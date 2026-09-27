//! Every ABI type, in every place the ABI appears, against an encoder of the tests' own:
//! parameters and results, `Abi.encode` and `Abi.decode`, events and their topics, errors,
//! queries and continuations, `deploy`, and equality. Values are random, and every type is
//! checked both ways: what the contract returns must be the reference encoding, byte for byte.

use super::*;

/// An ABI type, as the reference encoder sees it.
#[derive(Clone, Debug)]
enum T {
    Uint(u16),
    Int(u16),
    Address,
    Bool,
    Fixed(u8),
    Bytes,
    Str,
    Array(Box<T>, Option<usize>),
    Tuple(Vec<T>),
}

/// A value of a `T`: a word, the bytes of `bytes` or `string`, or the members of an array or
/// tuple.
#[derive(Clone, Debug, PartialEq)]
enum V {
    W(Word),
    B(Vec<u8>),
    L(Vec<V>),
}

fn dynamic(t: &T) -> bool {
    match t {
        T::Bytes | T::Str => true,
        T::Array(_, None) => true,
        T::Array(e, Some(_)) => dynamic(e),
        T::Tuple(ts) => ts.iter().any(dynamic),
        _ => false,
    }
}

fn head_size(t: &T) -> usize {
    if dynamic(t) {
        return 32;
    }
    match t {
        T::Array(e, Some(n)) => n * head_size(e),
        T::Tuple(ts) => ts.iter().map(head_size).sum(),
        _ => 32,
    }
}

/// The standard encoding of values of a tuple of types.
fn encode(ts: &[T], vs: &[V]) -> Vec<u8> {
    let heads: usize = ts.iter().map(head_size).sum();
    let mut head = Vec::new();
    let mut tail = Vec::new();
    for (t, v) in ts.iter().zip(vs) {
        if dynamic(t) {
            head.extend(Word::from_u64((heads + tail.len()) as u64).to_be_bytes());
            tail.extend(encode_one(t, v));
        } else {
            head.extend(encode_one(t, v));
        }
    }
    head.extend(tail);
    head
}

fn encode_one(t: &T, v: &V) -> Vec<u8> {
    match (t, v) {
        (T::Bytes | T::Str, V::B(b)) => {
            let mut out = Word::from_u64(b.len() as u64).to_be_bytes().to_vec();
            out.extend(b);
            out.resize(32 + b.len().div_ceil(32) * 32, 0);
            out
        }
        (T::Fixed(n), V::W(w)) => {
            // Lithe holds `bytesN` in the low bytes; the ABI in the high ones.
            let bytes = w.to_be_bytes();
            let mut out = [0u8; 32];
            out[..*n as usize].copy_from_slice(&bytes[32 - *n as usize..]);
            out.to_vec()
        }
        (_, V::W(w)) => w.to_be_bytes().to_vec(),
        (T::Array(e, None), V::L(xs)) => {
            let mut out = Word::from_u64(xs.len() as u64).to_be_bytes().to_vec();
            let ts = vec![(**e).clone(); xs.len()];
            out.extend(encode(&ts, xs));
            out
        }
        (T::Array(e, Some(_)), V::L(xs)) => {
            let ts = vec![(**e).clone(); xs.len()];
            encode(&ts, xs)
        }
        (T::Tuple(ts), V::L(xs)) => encode(ts, xs),
        _ => panic!("value does not match its type: {t:?} {v:?}"),
    }
}

/// Solidity's in-place encoding of an indexed value, which its topic hashes.
fn in_place(t: &T, v: &V, top: bool) -> Vec<u8> {
    match (t, v) {
        (T::Bytes | T::Str, V::B(b)) => {
            let mut out = b.clone();
            if !top {
                out.resize(b.len().div_ceil(32) * 32, 0);
            }
            out
        }
        (T::Array(e, _), V::L(xs)) => xs.iter().flat_map(|x| in_place(e, x, false)).collect(),
        (T::Tuple(ts), V::L(xs)) => ts
            .iter()
            .zip(xs)
            .flat_map(|(t, x)| in_place(t, x, false))
            .collect(),
        _ => encode_one(t, v),
    }
}

/// The canonical ABI type, as a signature has it.
fn canon(t: &T) -> String {
    match t {
        T::Uint(bits) => format!("uint{bits}"),
        T::Int(bits) => format!("int{bits}"),
        T::Address => "address".into(),
        T::Bool => "bool".into(),
        T::Fixed(n) => format!("bytes{n}"),
        T::Bytes => "bytes".into(),
        T::Str => "string".into(),
        T::Array(e, None) => format!("{}[]", canon(e)),
        T::Array(e, Some(n)) => format!("{}[{n}]", canon(e)),
        T::Tuple(ts) => format!("({})", ts.iter().map(canon).collect::<Vec<_>>().join(",")),
    }
}

/// The same type in Lithe.
fn lithe(t: &T) -> String {
    match t {
        T::Uint(256) => "nat".into(),
        T::Uint(bits) => format!("uint{bits}"),
        T::Int(256) => "int".into(),
        T::Int(bits) => format!("int{bits}"),
        T::Address => "address".into(),
        T::Bool => "bool".into(),
        T::Fixed(n) => format!("bytes{n}"),
        T::Bytes => "bytes".into(),
        T::Str => "string".into(),
        T::Array(e, None) => format!("list({})", lithe(e)),
        T::Array(e, Some(n)) => format!("list({}, {n})", lithe(e)),
        T::Tuple(ts) => format!("({})", ts.iter().map(lithe).collect::<Vec<_>>().join(", ")),
    }
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
        let mut b = [0u8; 32];
        for chunk in b.chunks_mut(8) {
            chunk.copy_from_slice(&self.next().to_be_bytes());
        }
        Word::from_be_bytes(b)
    }
}

/// Keeps the low `bits` of a word.
fn low(w: Word, bits: u16) -> Word {
    if bits >= 256 {
        return w;
    }
    let mut b = w.to_be_bytes();
    let keep = usize::from(bits / 8);
    for byte in b.iter_mut().take(32 - keep) {
        *byte = 0;
    }
    Word::from_be_bytes(b)
}

fn value(t: &T, rng: &mut Rng) -> V {
    match t {
        T::Uint(bits) => V::W(low(rng.word(), *bits)),
        T::Int(bits) => {
            // A value in range, sign-extended to the whole word.
            let w = low(rng.word(), *bits);
            let negative = *bits < 256 && w.to_be_bytes()[32 - usize::from(bits / 8)] & 0x80 != 0;
            if negative {
                let mut b = w.to_be_bytes();
                for byte in b.iter_mut().take(32 - usize::from(bits / 8)) {
                    *byte = 0xff;
                }
                V::W(Word::from_be_bytes(b))
            } else {
                V::W(w)
            }
        }
        T::Address => V::W(low(rng.word(), 160)),
        T::Bool => V::W(Word::from_u64(rng.below(2))),
        T::Fixed(n) => V::W(low(rng.word(), u16::from(*n) * 8)),
        T::Bytes | T::Str => {
            let len = [0, 1, 5, 31, 32, 33, 64, 70][rng.below(8) as usize];
            V::B((0..len).map(|_| b'a' + rng.below(26) as u8).collect())
        }
        T::Array(e, None) => {
            let n = rng.below(4);
            V::L((0..n).map(|_| value(e, rng)).collect())
        }
        T::Array(e, Some(n)) => V::L((0..*n).map(|_| value(e, rng)).collect()),
        T::Tuple(ts) => V::L(ts.iter().map(|t| value(t, rng)).collect()),
    }
}

fn arr(e: T) -> T {
    T::Array(Box::new(e), None)
}

fn fixed(e: T, n: usize) -> T {
    T::Array(Box::new(e), Some(n))
}

/// The types under test: every elementary type, and lists, fixed lists, and tuples of them
/// nested every way the ABI allows.
fn shapes() -> Vec<T> {
    use T::*;
    vec![
        Uint(8),
        Uint(256),
        Int(16),
        Address,
        Bool,
        Fixed(4),
        Bytes,
        Str,
        fixed(Uint(256), 3),
        fixed(Fixed(2), 2),
        arr(Uint(64)),
        arr(Fixed(3)),
        arr(Str),
        arr(Bytes),
        fixed(Str, 2),
        arr(arr(Uint(256))),
        arr(fixed(Uint(8), 2)),
        fixed(arr(Uint(256)), 2),
        arr(arr(arr(Int(8)))),
        arr(arr(Str)),
        Tuple(vec![Uint(256), Address]),
        Tuple(vec![Uint(256), Bytes]),
        Tuple(vec![Str, arr(Uint(16)), Bool]),
        Tuple(vec![Tuple(vec![Uint(256), Bool]), Address]),
        Tuple(vec![Tuple(vec![Str, Fixed(1)]), arr(Bytes)]),
        arr(Tuple(vec![Uint(256), Address])),
        arr(Tuple(vec![Uint(256), Str])),
        arr(Tuple(vec![Bytes, arr(Uint(256))])),
        fixed(Tuple(vec![Str, Uint(256)]), 2),
        fixed(Tuple(vec![Uint(256), Int(256)]), 2),
        arr(arr(Tuple(vec![Str, Bool]))),
        Tuple(vec![arr(Tuple(vec![Str, arr(Str)])), Uint(256)]),
    ]
}

fn run_call(runtime: &[u8], data: &[u8]) -> Outcome {
    exec(
        runtime,
        data,
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("run")
}

fn log_data(out: &Outcome) -> Vec<u8> {
    let line = out.detail.iter().rev().find(|d| d.starts_with("log ")).expect("a log");
    hex_decode(line.rsplit(' ').next().unwrap_or(""))
}

fn with_sel(sig: &str, args: &[u8]) -> Vec<u8> {
    let mut out = selector(sig).to_vec();
    out.extend(args);
    out
}

/// A contract that takes, returns, encodes, decodes, logs, raises, queries, and compares
/// values of one type.
fn program(t: &T) -> String {
    let ty = lithe(t);
    format!(
        "\
type tt is {ty};
interface Echo is {{
  view function echo(x : {ty}) : {ty};
  function call(x : {ty}) : {ty};
}}
event Logged of record {{ x : {ty}; }}
event Topic of record {{ indexed x : {ty}; }}
error Bad of {ty};
storage is record {{ n : nat; }}
external pure function echo(const x : {ty}) : {ty} is x
external function kept(const x : {ty}) : {ty} is {{ storage.n := 1n; }} with x
external pure function enc(const x : {ty}) : bytes is Abi.encode(x)
external pure function enc_pair(const x : {ty}; const y : nat) : bytes is Abi.encode(y, x, y)
external pure function enc_call(const x : {ty}) : bytes is Abi.encode_call(Echo.call, x)
external pure function enc_sel(const x : {ty}) : bytes is Abi.encode_with_selector(0x12345678, x, 1n)
external pure function dec(const b : bytes) : tt is Abi.decode(b, tt)
external pure function dec_pair(const b : bytes) : (tt, nat) is Abi.decode(b, (tt, nat))
external function log(const x : {ty}) is {{ emit Logged {{ x = x; }}; }}
external function topic(const x : {ty}) is {{ emit Topic {{ x = x; }}; }}
external function bad(const x : {ty}) raises Bad is {{ fail Bad(x); }}
external view function ask(const e : Echo; const x : {ty}) : {ty} is query e.echo(x)
external view function ask_or(const e : Echo; const x : {ty}; const y : {ty}) : {ty} is
  case query e.echo(x) of {{ | Ok(r) -> r | Error(_) -> y }}
external nonreentrant function later(const e : Echo; const x : {ty}) is {{
  defer e.call(x) then (r : {ty}) {{ emit Logged {{ x = r; }}; }};
}}
external pure function same(const a : {ty}; const b : {ty}) : bool is a = b
external pure function local(const x : {ty}) : {ty} is {{
  const y : {ty} := x;
  const z : {ty} := y;
}} with z
"
    )
}

#[test]
fn every_abi_type_everywhere() {
    install_mocks();
    let mut rng = Rng(0x5eed_1234_abcd_ef01);
    for t in shapes() {
        let name = canon(&t);
        let src = program(&t);
        let runtime = deploy(&compile(&src).unwrap_or_else(|e| panic!("{name}: {e}\n{src}")))
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        for round in 0..6 {
            let v = value(&t, &mut rng);
            let w = value(&t, &mut rng);
            let enc = encode(std::slice::from_ref(&t), std::slice::from_ref(&v));
            let what = format!("{name} round {round}: {v:?}");
            // Parameters decode, and results encode, byte for byte.
            for f in ["echo", "kept", "local"] {
                let out = run_call(&runtime, &with_sel(&format!("{f}({name})"), &enc));
                assert!(!out.reverted, "{f} {what}: {}", pretty(&out.returndata));
                assert_eq!(hex(&out.returndata), hex(&enc), "{f} {what}");
            }
            // `Abi.encode` as a `bytes` result, and inside several values.
            let out = run_call(&runtime, &with_sel(&format!("enc({name})"), &enc));
            assert!(!out.reverted, "enc {what}: {}", pretty(&out.returndata));
            let want = encode(&[T::Bytes], &[V::B(enc.clone())]);
            assert_eq!(hex(&out.returndata), hex(&want), "enc {what}");
            let seven = V::W(Word::from_u64(7));
            let pair = encode(&[t.clone(), T::Uint(256)], &[v.clone(), seven.clone()]);
            let out = run_call(&runtime, &with_sel(&format!("enc_pair({name},uint256)"), &pair));
            let inner = encode(
                &[T::Uint(256), t.clone(), T::Uint(256)],
                &[seven.clone(), v.clone(), seven.clone()],
            );
            assert_eq!(hex(&out.returndata), hex(&encode(&[T::Bytes], &[V::B(inner)])), "enc_pair {what}");
            let out = run_call(&runtime, &with_sel(&format!("enc_call({name})"), &enc));
            let call = with_sel(&format!("call({name})"), &enc);
            assert_eq!(hex(&out.returndata), hex(&encode(&[T::Bytes], &[V::B(call)])), "enc_call {what}");
            let out = run_call(&runtime, &with_sel(&format!("enc_sel({name})"), &enc));
            let mut sel = vec![0x12, 0x34, 0x56, 0x78];
            sel.extend(encode(&[t.clone(), T::Uint(256)], &[v.clone(), V::W(Word::from_u64(1))]));
            assert_eq!(hex(&out.returndata), hex(&encode(&[T::Bytes], &[V::B(sel)])), "enc_sel {what}");
            // `Abi.decode` of one value, and of a list of types.
            let bytes_arg = encode(&[T::Bytes], &[V::B(enc.clone())]);
            let out = run_call(&runtime, &with_sel("dec(bytes)", &bytes_arg));
            assert!(!out.reverted, "dec {what}: {}", pretty(&out.returndata));
            assert_eq!(hex(&out.returndata), hex(&enc), "dec {what}");
            let two = encode(&[t.clone(), T::Uint(256)], &[v.clone(), seven.clone()]);
            let out = run_call(&runtime, &with_sel("dec_pair(bytes)", &encode(&[T::Bytes], &[V::B(two.clone())])));
            assert!(!out.reverted, "dec_pair {what}: {}", pretty(&out.returndata));
            let tuple = T::Tuple(vec![t.clone(), T::Uint(256)]);
            let want = encode(std::slice::from_ref(&tuple), &[V::L(vec![v.clone(), seven.clone()])]);
            assert_eq!(hex(&out.returndata), hex(&want), "dec_pair {what}");
            // An event's data, and an indexed value's topic.
            let out = run_call(&runtime, &with_sel(&format!("log({name})"), &enc));
            assert!(!out.reverted, "log {what}: {}", pretty(&out.returndata));
            assert_eq!(hex(&log_data(&out)), hex(&enc), "log {what}");
            let out = run_call(&runtime, &with_sel(&format!("topic({name})"), &enc));
            assert!(!out.reverted, "topic {what}: {}", pretty(&out.returndata));
            let topics = out
                .trace
                .iter()
                .find_map(|ev| match ev {
                    Ev::Log { topics } => Some(topics.clone()),
                    _ => None,
                })
                .expect("topics");
            let indexed = if dynamic(&t) || matches!(t, T::Array(..) | T::Tuple(..)) {
                Word::from_be_bytes(crate::keccak::keccak256(&in_place(&t, &v, true)))
            } else {
                Word::from_be_bytes(encode_one(&t, &v).try_into().expect("word"))
            };
            assert_eq!(topics[1], indexed, "topic {what}");
            // An error's payload.
            let out = run_call(&runtime, &with_sel(&format!("bad({name})"), &enc));
            assert!(out.reverted);
            assert_eq!(hex(&out.returndata), hex(&with_sel(&format!("Bad({name})"), &enc)), "bad {what}");
            // A query's arguments and result, through a contract that echoes its arguments.
            let echo = Word::from_u64(0xcd);
            let args = encode(&[T::Address, t.clone()], &[V::W(echo), v.clone()]);
            let out = run_call(&runtime, &with_sel(&format!("ask(address,{name})"), &args));
            assert!(!out.reverted, "ask {what}: {}", pretty(&out.returndata));
            assert_eq!(hex(&out.returndata), hex(&enc), "ask {what}");
            let args = encode(&[T::Address, t.clone(), t.clone()], &[V::W(echo), v.clone(), w.clone()]);
            let out = run_call(&runtime, &with_sel(&format!("ask_or(address,{name},{name})"), &args));
            assert_eq!(hex(&out.returndata), hex(&enc), "ask_or {what}");
            let refuse = Word::from_u64(0xef);
            let args = encode(&[T::Address, t.clone(), t.clone()], &[V::W(refuse), v.clone(), w.clone()]);
            let out = run_call(&runtime, &with_sel(&format!("ask_or(address,{name},{name})"), &args));
            let w_enc = encode(std::slice::from_ref(&t), std::slice::from_ref(&w));
            assert_eq!(hex(&out.returndata), hex(&w_enc), "ask_or failed {what}");
            // A deferred call's result, in its continuation.
            let args = encode(&[T::Address, t.clone()], &[V::W(echo), v.clone()]);
            let out = run_call(&runtime, &with_sel(&format!("later(address,{name})"), &args));
            assert!(!out.reverted, "later {what}: {}", pretty(&out.returndata));
            assert_eq!(hex(&log_data(&out)), hex(&enc), "later {what}");
            // Equality.
            let args = encode(&[t.clone(), t.clone()], &[v.clone(), v.clone()]);
            let out = run_call(&runtime, &with_sel(&format!("same({name},{name})"), &args));
            assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(1), "same {what}");
            let args = encode(&[t.clone(), t.clone()], &[v.clone(), w.clone()]);
            let out = run_call(&runtime, &with_sel(&format!("same({name},{name})"), &args));
            assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(u64::from(v == w)), "differ {what}");
        }
    }
}

/// `deploy` takes any ABI value from the arguments appended to the creation code.
#[test]
fn deploy_takes_every_abi_type() {
    let mut rng = Rng(0xdead_beef_0bad_f00d);
    for t in shapes() {
        let name = canon(&t);
        let ty = lithe(&t);
        let src = format!(
            "event Made of record {{ x : {ty}; }}\nstorage is record {{ n : nat; }}\ndeploy(const x : {ty}) is {{ emit Made {{ x = x; }}; }}\nexternal function f() is {{ skip }}\n"
        );
        let init = compile(&src).unwrap_or_else(|e| panic!("{name}: {e}"));
        for _ in 0..3 {
            let v = value(&t, &mut rng);
            let enc = encode(std::slice::from_ref(&t), std::slice::from_ref(&v));
            let mut code = init.clone();
            code.extend(&enc);
            let made = construct(&code, Word::from_u64(1), Word::from_u64(0)).expect("construct");
            assert!(!made.reverted, "{name}: {}", pretty(&made.returndata));
            assert_eq!(hex(&log_data(&made)), hex(&enc), "{name}");
        }
    }
}

/// Malformed arguments revert, as Solidity's decoder does: an offset or length past the data,
/// or out of 64 bits, and a word its type cannot hold.
#[test]
fn malformed_nested_arguments_revert() {
    let t = arr(T::Tuple(vec![T::Str, arr(T::Uint(8))]));
    let src = program(&t);
    let runtime = deploy(&compile(&src).expect("compile")).expect("deploy");
    let v = V::L(vec![
        V::L(vec![V::B(b"hello".to_vec()), V::L(vec![V::W(Word::from_u64(1)), V::W(Word::from_u64(2))])]),
        V::L(vec![V::B(Vec::new()), V::L(Vec::new())]),
    ]);
    let enc = encode(std::slice::from_ref(&t), std::slice::from_ref(&v));
    let sig = format!("echo({})", canon(&t));
    let good = run_call(&runtime, &with_sel(&sig, &enc));
    assert!(!good.reverted, "{}", pretty(&good.returndata));
    assert_eq!(good.returndata, enc);
    // Each word of the encoding, broken in several ways, must revert or decode to exactly
    // what re-encodes to the data given: no word is read unchecked.
    for at in (0..enc.len()).step_by(32) {
        for bad in [Word::from_u64(0x1000), Word::from_u64(u64::MAX), Word::from_u64(256), Word::from_u64(3)] {
            let mut data = enc.clone();
            data[at..at + 32].copy_from_slice(&bad.to_be_bytes());
            let out = run_call(&runtime, &with_sel(&sig, &data));
            if !out.reverted {
                // Whatever decodes must be a valid value, which encodes canonically.
                let back = run_call(&runtime, &with_sel(&sig, &out.returndata));
                assert!(!back.reverted, "word {at} = {bad:?}: re-encoding failed");
                assert_eq!(back.returndata, out.returndata, "word {at} = {bad:?}");
            }
        }
    }
    // Truncated data reverts.
    for cut in [4, 36, enc.len() / 2, enc.len() - 1] {
        let out = run_call(&runtime, &with_sel(&sig, &enc[..cut.min(enc.len())]));
        assert!(out.reverted, "cut at {cut}");
    }
    // A uint8 element past 255 reverts.
    let last = enc.len() - 32;
    let mut data = enc.clone();
    let find = enc.len() - 64;
    let _ = find;
    data[last..].copy_from_slice(&Word::from_u64(0).to_be_bytes());
    let _ = run_call(&runtime, &with_sel(&sig, &data));
    let mut wide = enc.clone();
    // The first list's second element, 2, is at the end of its tail.
    let two = Word::from_u64(2).to_be_bytes();
    let pos = wide.windows(32).position(|w| w == two).expect("the element");
    wide[pos..pos + 32].copy_from_slice(&Word::from_u64(300).to_be_bytes());
    assert!(run_call(&runtime, &with_sel(&sig, &wide)).reverted, "uint8 of 300");
    // `enc` passes its argument on without decoding it first: it reverts exactly when
    // `echo` does, and encodes what `echo` decodes.
    let sig_enc = format!("enc({})", canon(&t));
    let mut cases = vec![enc.clone(), wide];
    for at in (0..enc.len()).step_by(32) {
        for bad in [Word::from_u64(0x1000), Word::from_u64(u64::MAX), Word::from_u64(256), Word::from_u64(3)] {
            let mut data = enc.clone();
            data[at..at + 32].copy_from_slice(&bad.to_be_bytes());
            cases.push(data);
        }
    }
    cases.extend([36, enc.len() / 2, enc.len() - 1].map(|cut| enc[..cut].to_vec()));
    for (i, data) in cases.iter().enumerate() {
        let echoed = run_call(&runtime, &with_sel(&sig, data));
        let passed = run_call(&runtime, &with_sel(&sig_enc, data));
        assert_eq!(passed.reverted, echoed.reverted, "case {i}");
        if !echoed.reverted {
            assert_eq!(abi_string_value(&passed.returndata), echoed.returndata, "case {i}");
        }
    }
}

/// Nested values work as values: indexing, lengths, loops, literals, and fields.
#[test]
fn nested_values_index_and_loop() {
    let src = "\
type item is record { name : string; tags : list(nat); }
storage is record { n : nat; }
external pure function cell(const xs : list(list(nat)); const i : nat; const j : nat) : nat is xs[i][j]
external pure function row_len(const xs : list(list(nat)); const i : nat) : nat is xs[i].length
external pure function total(const xs : list(list(nat))) : nat is {
  var sum : nat := 0n;
  for row : list(nat) in xs do {
    for x : nat in row do {
      sum := sum + x;
    }
  }
} with sum
external pure function built(const a : nat) : list(list(nat)) is [[a, a + 1n], [], [a * 2n]]
external pure function names(const items : list(item)) : list(string) is {
  var out : list(string) := [];
  for it : item in items do {
    out[out.length] := it.name;
  }
} with out
external pure function tag(const items : list(item); const i : nat; const j : nat) : nat is items[i].tags[j]
external pure function make(const s : string; const t : nat) : list(item) is [{ name = s; tags = [t, t]; }]
external pure function swap(const p : (string, list(nat))) : (list(nat), string) is {
  const (s, xs) : (string, list(nat)) := p;
} with (xs, s)
";
    let runtime = deploy(&compile(src).unwrap_or_else(|e| panic!("{e}"))).expect("deploy");
    let grid = V::L(vec![
        V::L(vec![V::W(Word::from_u64(1)), V::W(Word::from_u64(2))]),
        V::L(vec![]),
        V::L(vec![V::W(Word::from_u64(3)), V::W(Word::from_u64(4)), V::W(Word::from_u64(5))]),
    ]);
    let gt = arr(arr(T::Uint(256)));
    let n = |x: u64| V::W(Word::from_u64(x));
    let call = |sig: &str, ts: &[T], vs: &[V]| {
        let out = run_call(&runtime, &with_sel(sig, &encode(ts, vs)));
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        out.returndata
    };
    let word = |data: Vec<u8>| load_bytes(&data, 0);
    assert_eq!(word(call("cell(uint256[][],uint256,uint256)", &[gt.clone(), T::Uint(256), T::Uint(256)], &[grid.clone(), n(2), n(1)])), Word::from_u64(4));
    assert_eq!(word(call("row_len(uint256[][],uint256)", &[gt.clone(), T::Uint(256)], &[grid.clone(), n(1)])), Word::from_u64(0));
    assert_eq!(word(call("total(uint256[][])", std::slice::from_ref(&gt), std::slice::from_ref(&grid))), Word::from_u64(15));
    let out = run_call(&runtime, &with_sel("cell(uint256[][],uint256,uint256)", &encode(&[gt.clone(), T::Uint(256), T::Uint(256)], &[grid.clone(), n(1), n(0)])));
    assert!(out.reverted, "an index past an inner list's end");
    let built = V::L(vec![V::L(vec![n(5), n(6)]), V::L(vec![]), V::L(vec![n(10)])]);
    assert_eq!(call("built(uint256)", &[T::Uint(256)], &[n(5)]), encode(std::slice::from_ref(&gt), &[built]));
    let it = T::Tuple(vec![T::Str, arr(T::Uint(256))]);
    let items = V::L(vec![
        V::L(vec![V::B(b"one".to_vec()), V::L(vec![n(1)])]),
        V::L(vec![V::B(b"a name longer than thirty-two bytes".to_vec()), V::L(vec![n(2), n(3)])]),
    ]);
    let names = V::L(vec![V::B(b"one".to_vec()), V::B(b"a name longer than thirty-two bytes".to_vec())]);
    assert_eq!(call("names((string,uint256[])[])", &[arr(it.clone())], std::slice::from_ref(&items)), encode(&[arr(T::Str)], &[names]));
    assert_eq!(word(call("tag((string,uint256[])[],uint256,uint256)", &[arr(it.clone()), T::Uint(256), T::Uint(256)], &[items.clone(), n(1), n(1)])), Word::from_u64(3));
    let made = V::L(vec![V::L(vec![V::B(b"x".to_vec()), V::L(vec![n(9), n(9)])])]);
    assert_eq!(call("make(string,uint256)", &[T::Str, T::Uint(256)], &[V::B(b"x".to_vec()), n(9)]), encode(&[arr(it.clone())], &[made]));
    let p = V::L(vec![V::B(b"s".to_vec()), V::L(vec![n(1), n(2)])]);
    let swapped = V::L(vec![V::L(vec![n(1), n(2)]), V::B(b"s".to_vec())]);
    assert_eq!(
        call("swap((string,uint256[]))", std::slice::from_ref(&it), &[p]),
        encode(&[T::Tuple(vec![arr(T::Uint(256)), T::Str])], &[swapped])
    );
}


/// `Abi.encode_packed` lays out what Solidity's `abi.encodePacked` does, fixed lists included:
/// each element padded to a word, `bytesN` in its high bytes. The expected bytes are solc's.
#[test]
fn packed_fixed_lists_match_solidity() {
    let src = "\
storage is record { n : nat; }
external pure function f(const a : list(bytes2, 2)) : bytes is Abi.encode_packed(a)
external pure function g(const a : list(uint8)) : bytes is Abi.encode_packed(a)
external pure function h(const a : list(bool, 2); const x : address) : bytes is Abi.encode_packed(a, x)
type status is
  | New
  | Pending
  | Complete
interface Target is {
  function foo(amount : nat);
}
external pure function k(const s : status; const t : Target; const x : int8; const b : bytes3; const ys : list(bytes2)) : bytes is
  Abi.encode_packed(s, t, x, b, ys)
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let packed = |data: Vec<u8>| {
        let out = run_call(&runtime, &data);
        assert!(!out.reverted, "{}", pretty(&out.returndata));
        hex(&abi_string_value(&out.returndata))
    };
    let two = encode(&[fixed(T::Fixed(2), 2)], &[V::L(vec![V::W(Word::from_u64(0x6162)), V::W(Word::from_u64(0x6364))])]);
    assert_eq!(
        packed(with_sel("f(bytes2[2])", &two)),
        "61620000000000000000000000000000000000000000000000000000000000006364000000000000000000000000000000000000000000000000000000000000"
    );
    let bytes = encode(&[arr(T::Uint(8))], &[V::L(vec![V::W(Word::from_u64(1)), V::W(Word::from_u64(2))])]);
    assert_eq!(
        packed(with_sel("g(uint8[])", &bytes)),
        "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"
    );
    let args = encode(
        &[fixed(T::Bool, 2), T::Address],
        &[V::L(vec![V::W(Word::from_u64(1)), V::W(Word::from_u64(0))]), V::W(Word::from_u64(0xab))],
    );
    assert_eq!(
        packed(with_sel("h(bool[2],address)", &args)),
        "0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ab"
    );
    let mut minus_two = [0xffu8; 32];
    minus_two[31] = 0xfe;
    let args = encode(
        &[T::Uint(8), T::Address, T::Int(8), T::Fixed(3), arr(T::Fixed(2))],
        &[
            V::W(Word::from_u64(2)),
            V::W(Word::from_u64(0xab)),
            V::W(Word::from_be_bytes(minus_two)),
            V::W(Word::from_u64(0x616263)),
            V::L(vec![V::W(Word::from_u64(0x6162)), V::W(Word::from_u64(0x6364))]),
        ],
    );
    assert_eq!(
        packed(with_sel("k(uint8,address,int8,bytes3,bytes2[])", &args)),
        "0200000000000000000000000000000000000000abfe616263\
         6162000000000000000000000000000000000000000000000000000000000000\
         6364000000000000000000000000000000000000000000000000000000000000"
    );
}
