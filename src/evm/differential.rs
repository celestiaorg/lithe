use super::*;

/// Every example and every program in `fuzz/`, with a path relative to the crate root.
pub(super) fn differential_targets() -> Vec<(std::path::PathBuf, String)> {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut found = Vec::new();
    lithe_files(&root.join("examples"), &mut found);
    lithe_files(&root.join("fuzz"), &mut found);
    found
        .into_iter()
        .filter_map(|path| {
            let rel = path
                .strip_prefix(&root)
                .expect("under the crate")
                .to_string_lossy()
                .replace('\\', "/");
            if rel.starts_with("examples/reject/") {
                return None;
            }
            let src = std::fs::read_to_string(&path).ok()?;
            // Builds of a factory embed different code, so their CREATE2 addresses differ.
            // Creation code that needs arguments cannot deploy without them.
            (is_program(&src) && contracts(&src) <= 1 && !needs_deploy_args(&src))
                .then_some((path, rel))
        })
        .collect()
}

pub(super) fn steps_from_env(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|n| n.parse().ok())
        .unwrap_or(default)
}

/// Replays one random call sequence against two runtimes of the same program.
pub(super) fn compare_builds(
    rel: &str,
    methods: &[(String, [u8; 4])],
    reference: &[u8],
    ours: &[u8],
    steps: usize,
    slots: bool,
) {
    let mut rng = Rng(rel.bytes().fold(0x9e37_79b9_7f4a_7c15u64, |h, b| {
        (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
    }));
    // Each build keeps its own storage: their layouts may differ.
    let mut theirs: HashMap<Word, Word> = HashMap::new();
    let mut mine: HashMap<Word, Word> = HashMap::new();
    // The ether the contract holds, as a chain keeps it from call to call.
    let mut held = Word::from_u64(10_000_000_000_000_000_000);
    let mut succeeded = 0;
    for step in 0..steps {
        let data = random_calldata(methods, &mut rng);
        let caller = match rng.below(6) {
            0 | 1 => Word::from_u64(0),
            2 => Word::from_u64(1),
            3 => Word::from_u64(0xcd),
            4 => Word::from_u64(0x1000),
            _ => Word::from_u64(rng.below(4)),
        };
        let value = match rng.below(8) {
            0 => Word::from_u64(1),
            1 => Word::from_u64(1_000_000_000_000_000_000),
            _ => Word::from_u64(0),
        };
        // The call's value is the account's as the call starts.
        let balance = held.wrapping_add(value);
        let run = |code: &[u8], storage: &HashMap<Word, Word>| {
            exec_state(
                code,
                &data,
                storage.clone(),
                caller,
                value,
                balance,
                HashMap::new(),
            )
        };
        // Both builds see the same world, so their `CREATE`s land at the same address.
        let nonce = NONCE.get();
        let want = run(reference, &theirs);
        NONCE.set(nonce);
        let got = run(ours, &mine);
        let ctx = format!("{rel} step {step}: calldata {}", hex(&data));
        let (want, got) = match (want, got) {
            (Err(a), Err(b)) => {
                assert_eq!(a, b, "{ctx}");
                continue;
            }
            (Ok(want), Ok(got)) => (want, got),
            (want, got) => panic!(
                "{ctx}: reference {:?} vs ours {:?}",
                want.map(|o| o.reverted),
                got.map(|o| o.reverted)
            ),
        };
        assert_eq!(want.reverted, got.reverted, "{ctx}: reverted");
        assert_eq!(
            hex(&want.returndata),
            hex(&got.returndata),
            "{ctx}: returndata"
        );
        // A delegated module's facet calls the contract's hooks back into its own code, which
        // the inline build runs in place; the facets themselves aren't recorded.
        let detail = |out: &Outcome| -> Vec<String> {
            out.detail
                .iter()
                .filter(|line| !line.starts_with("delegate "))
                .cloned()
                .collect()
        };
        assert_eq!(detail(&want), detail(&got), "{ctx}: effects");
        // When storage is written is not observable; what it ends up holding is.
        let effects = |trace: &[Ev]| {
            let kept: Vec<&Ev> = trace
                .iter()
                .filter(|ev| !matches!(ev, Ev::SStore))
                .collect();
            format!("{kept:?}")
        };
        assert_eq!(effects(&want.trace), effects(&got.trace), "{ctx}: trace");
        let sorted = |m: &HashMap<Word, Word>| {
            let mut v: Vec<(Word, Word)> = m
                .iter()
                .filter(|(_, v)| !v.is_zero())
                .map(|(k, v)| (*k, *v))
                .collect();
            v.sort_by_key(|(k, _)| k.to_be_bytes());
            format!("{v:?}")
        };
        if slots {
            assert_eq!(
                sorted(&want.storage),
                sorted(&got.storage),
                "{ctx}: storage"
            );
        }
        assert_eq!(
            sorted(&want.transient),
            sorted(&got.transient),
            "{ctx}: transient"
        );
        assert_eq!(
            sorted(&want.balances),
            sorted(&got.balances),
            "{ctx}: balances"
        );
        assert_eq!(
            want.self_balance, got.self_balance,
            "{ctx}: its own balance"
        );
        if !want.reverted {
            succeeded += 1;
            theirs = want.storage;
            mine = got.storage;
            held = want.self_balance;
        }
    }
    eprintln!("{rel}: {succeeded}/{steps} calls succeeded");
}

/// The optimizer must not change behavior. Each program runs a random call sequence
/// against its unoptimized build. `LITHE_FUZZ_STEPS` sets calls per program.
#[test]
fn optimizer_preserves_behavior() {
    let steps = steps_from_env("LITHE_FUZZ_STEPS", 200);
    for (path, rel) in differential_targets() {
        let plain = crate::compile_file_unoptimized(&path).unwrap_or_else(|e| panic!("{rel}: {e}"));
        let plain = deploy(&plain).unwrap_or_else(|e| panic!("{rel}: plain deploy: {e}"));
        differential(&path, &rel, &plain, steps, true);
    }
}

/// Builds that read stored constants as constants and place allocations where the heap's
/// top is known must behave as builds without them, for every program, whichever build is
/// smaller. `LITHE_FUZZ_STEPS` sets calls per program.
#[test]
fn static_heap_preserves_behavior() {
    let steps = steps_from_env("LITHE_FUZZ_STEPS", 200);
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut bench = Vec::new();
    lithe_files(&root.join("bench"), &mut bench);
    let bench = bench.into_iter().filter_map(|path| {
        let src = std::fs::read_to_string(&path).ok()?;
        let rel = path
            .strip_prefix(&root)
            .ok()?
            .to_string_lossy()
            .replace('\\', "/");
        (is_program(&src) && contracts(&src) <= 1 && !needs_deploy_args(&src))
            .then_some((path, rel))
    });
    let build = |path: &std::path::Path, rel: &str, on: bool| {
        crate::gen::FORCE_STATIC_HEAP.set(Some(on));
        let code = compile_file(path);
        crate::gen::FORCE_STATIC_HEAP.set(None);
        deploy(&code.unwrap_or_else(|e| panic!("{rel}: {e}")))
            .unwrap_or_else(|e| panic!("{rel}: deploy: {e}"))
    };
    let mut differ = 0;
    for (path, rel) in differential_targets().into_iter().chain(bench) {
        OPAQUE_CODE.set(true);
        install_mocks();
        let (off, on) = (build(&path, &rel, false), build(&path, &rel, true));
        if off == on {
            continue;
        }
        differ += 1;
        let checked = crate::check::check(
            crate::modules::load(&Sources::disk(), &path).expect("load"),
            Default::default(),
        )
        .expect("check");
        let mut methods = crate::route::method_ids(&checked).expect("methods");
        // Other characters than an alphabet's decode to whatever memory the lookups reach,
        // which the builds lay out differently.
        methods.retain(|(sig, _)| !sig.starts_with("decode("));
        compare_builds(&rel, &methods, &off, &on, steps, true);
    }
    assert!(differ > 20, "only {differ} programs placed an allocation");
}

/// Copies of outlined functions specialized to the constants their calls pass must behave as
/// the one copy every call shares. `LITHE_FUZZ_STEPS` sets calls per program.
#[test]
fn specialized_copies_preserve_behavior() {
    let steps = steps_from_env("LITHE_FUZZ_STEPS", 200);
    let build = |path: &std::path::Path, rel: &str, on: bool| {
        crate::gen::FORCE_SPECIALIZE.set(Some(on));
        let code = compile_file(path);
        crate::gen::FORCE_SPECIALIZE.set(None);
        deploy(&code.unwrap_or_else(|e| panic!("{rel}: {e}")))
            .unwrap_or_else(|e| panic!("{rel}: deploy: {e}"))
    };
    let mut differ = 0;
    for (path, rel) in differential_targets() {
        OPAQUE_CODE.set(true);
        install_mocks();
        let (off, on) = (build(&path, &rel, false), build(&path, &rel, true));
        if off == on {
            continue;
        }
        differ += 1;
        let checked = crate::check::check(
            crate::modules::load(&Sources::disk(), &path).expect("load"),
            Default::default(),
        )
        .expect("check");
        let methods = crate::route::method_ids(&checked).expect("methods");
        compare_builds(&rel, &methods, &off, &on, steps, true);
    }
    assert!(differ > 5, "only {differ} programs specialized a function");
}

/// Runs every program against creation code built by another compiler revision and demands
/// identical behavior. `LITHE_REF_DIR` holds `<path>.hex` for each `examples/` and `fuzz/`
/// program. Without it the test does nothing. `LITHE_REF_STEPS` sets calls per program.
/// `LITHE_REF_STORAGE=skip` compares everything but raw slots, for a reference with
/// another storage layout; views still expose storage through the ABI.
#[test]
fn optimized_code_matches_reference() {
    let Ok(dir) = std::env::var("LITHE_REF_DIR") else {
        return;
    };
    let steps = steps_from_env("LITHE_REF_STEPS", 600);
    let mut compared = 0;
    for (path, rel) in differential_targets() {
        let ref_path = std::path::Path::new(&dir).join(format!("{rel}.hex"));
        let Ok(text) = std::fs::read_to_string(&ref_path) else {
            continue;
        };
        let reference = deploy(&hex_decode(text.trim().trim_start_matches("0x")))
            .unwrap_or_else(|e| panic!("{rel}: reference deploy: {e}"));
        let slots = std::env::var("LITHE_REF_STORAGE").map_or(true, |v| v != "skip");
        differential(&path, &rel, &reference, steps, slots);
        compared += 1;
    }
    assert!(compared > 0, "no reference programs in {dir}");
}

/// Sends the same random calls, callers, and values to `reference` and to the current
/// optimized build, threading storage through successful calls, and compares everything.
fn differential(path: &std::path::Path, rel: &str, reference: &[u8], steps: usize, slots: bool) {
    OPAQUE_CODE.set(true);
    install_mocks();
    let ours = deploy(&compile_file(path).unwrap_or_else(|e| panic!("{rel}: {e}")))
        .unwrap_or_else(|e| panic!("{rel}: deploy: {e}"));
    let checked = crate::check::check(
        crate::modules::load(&Sources::disk(), path).expect("load"),
        Default::default(),
    )
    .expect("check");
    let methods = crate::route::method_ids(&checked).expect("methods");
    compare_builds(rel, &methods, reference, &ours, steps, slots);
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn word(&mut self) -> Word {
        Word([self.next(), self.next(), self.next(), self.next()])
    }
}

fn random_calldata(methods: &[(String, [u8; 4])], rng: &mut Rng) -> Vec<u8> {
    match rng.below(40) {
        0 => return Vec::new(),
        1 => return vec![0xab; rng.below(4) as usize],
        2 => return rng.word().to_be_bytes()[..4].to_vec(),
        _ => {}
    }
    if methods.is_empty() {
        return Vec::new();
    }
    let (sig, sel) = &methods[rng.below(methods.len() as u64) as usize];
    let open = sig.find('(').expect("signature");
    let types = split_types(&sig[open + 1..sig.len() - 1]);
    let mut data = sel.to_vec();
    data.extend(encode_tuple(&types, rng));
    match rng.below(30) {
        0 => data.truncate(data.len().saturating_sub(1 + rng.below(40) as usize)),
        1 => data.extend_from_slice(&[0x11; 7]),
        _ => {}
    }
    data
}

fn split_types(inner: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0;
    let mut cur = String::new();
    for c in inner.chars() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            _ => {}
        }
        if c == ',' && depth == 0 {
            out.push(std::mem::take(&mut cur));
        } else {
            cur.push(c);
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

fn is_dynamic_abi(ty: &str) -> bool {
    if ty == "string" || ty == "bytes" || ty.ends_with("[]") {
        return true;
    }
    if let Some(inner) = ty.strip_prefix('(') {
        let inner = &inner[..inner.rfind(')').expect("tuple")];
        return split_types(inner).iter().any(|t| is_dynamic_abi(t));
    }
    if let Some(open) = ty.rfind('[') {
        return is_dynamic_abi(&ty[..open]);
    }
    false
}

fn encode_tuple(types: &[String], rng: &mut Rng) -> Vec<u8> {
    let parts: Vec<(bool, Vec<u8>)> = types
        .iter()
        .map(|t| (is_dynamic_abi(t), encode_value(t, rng)))
        .collect();
    let head_len: usize = parts
        .iter()
        .map(|(dynamic, bytes)| if *dynamic { 32 } else { bytes.len() })
        .sum();
    let mut head = Vec::new();
    let mut tail = Vec::new();
    for (dynamic, bytes) in parts {
        if dynamic {
            head.extend(Word::from_u64((head_len + tail.len()) as u64).to_be_bytes());
            tail.extend(bytes);
        } else {
            head.extend(bytes);
        }
    }
    head.extend(tail);
    head
}

fn encode_value(ty: &str, rng: &mut Rng) -> Vec<u8> {
    if let Some(inner) = ty.strip_prefix('(') {
        let inner = &inner[..inner.rfind(')').expect("tuple")];
        return encode_tuple(&split_types(inner), rng);
    }
    if let Some(elem) = ty.strip_suffix("[]") {
        let n = rng.below(4) as usize;
        let mut out = Word::from_u64(n as u64).to_be_bytes().to_vec();
        out.extend(encode_tuple(&vec![elem.to_string(); n], rng));
        return out;
    }
    if let Some(open) = ty.rfind('[') {
        let n: usize = ty[open + 1..ty.len() - 1].parse().expect("array length");
        return encode_tuple(&vec![ty[..open].to_string(); n], rng);
    }
    if ty == "string" || ty == "bytes" {
        let n = match rng.below(4) {
            0 => 0,
            1 => rng.below(32) as usize,
            2 => 31 + rng.below(3) as usize,
            _ => rng.below(100) as usize,
        };
        let data: Vec<u8> = (0..n).map(|_| (rng.next() % 256) as u8).collect();
        let mut out = Word::from_u64(n as u64).to_be_bytes().to_vec();
        out.extend(&data);
        out.resize(32 + n.div_ceil(32) * 32, 0);
        return out;
    }
    random_word(ty, rng).to_be_bytes().to_vec()
}

fn random_word(ty: &str, rng: &mut Rng) -> Word {
    let ones = Word::from_u64(0).not();
    let pick = rng.below(10);
    if let Some(bits) = ty.strip_prefix("uint") {
        let bits: u32 = bits.parse().unwrap_or(256);
        let max = if bits == 256 {
            ones
        } else {
            ones.shr(256 - bits)
        };
        return match pick {
            0 => Word::from_u64(0),
            1 => Word::from_u64(1),
            2 => max,
            3 => max.wrapping_add(Word::from_u64(1)),
            4 => rng.word(),
            5 | 6 => Word::from_u64(rng.below(20)),
            _ => rng.word().bitand(max),
        };
    }
    if let Some(bits) = ty.strip_prefix("int") {
        let bits: u32 = bits.parse().unwrap_or(256);
        let raw = match pick {
            0 => Word::from_u64(0),
            1 => Word::from_u64(1),
            2 => ones,
            3 => Word::from_u64(1).shl(bits - 1),
            4 => Word::from_u64(1)
                .shl(bits - 1)
                .wrapping_sub(Word::from_u64(1)),
            5 => Word::from_u64(rng.below(20)),
            6 => Word::from_u64(0).wrapping_sub(Word::from_u64(rng.below(20))),
            7 => rng.word(),
            _ => rng.word(),
        };
        return if pick == 7 || bits == 256 {
            raw
        } else {
            raw.sign_extend(bits / 8 - 1)
        };
    }
    if ty == "address" {
        return match pick {
            0 | 1 => Word::from_u64(0),
            2 => Word::from_u64(1),
            3 => Word::from_u64(0xcd),
            4 => Word::from_u64(0x1000),
            5 => rng.word(),
            _ => rng.word().bitand(ones.shr(96)),
        };
    }
    if ty == "bool" {
        return Word::from_u64(if pick == 0 { 2 } else { pick % 2 });
    }
    if let Some(n) = ty.strip_prefix("bytes") {
        let n: u32 = n.parse().unwrap_or(32);
        let w = rng.word();
        return if pick == 0 || n == 32 {
            w
        } else {
            w.bitand(ones.shl(256 - 8 * n))
        };
    }
    rng.word()
}
