//! Every precompile is a built-in. These tests stand a recording mock at each precompile's
//! address: the input must be laid out exactly as the precompile reads it, and its answer
//! must come back as the built-in's result. An answer of the wrong size, as a chain without
//! the precompile gives, must not read as zeros.

use super::*;

thread_local! {
    static SEEN: std::cell::RefCell<Vec<u8>> = const { std::cell::RefCell::new(Vec::new()) };
    static ANSWER: std::cell::RefCell<Result<Vec<u8>, Vec<u8>>> = const { std::cell::RefCell::new(Ok(Vec::new())) };
}

fn recorder(input: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
    SEEN.with(|s| *s.borrow_mut() = input.to_vec());
    ANSWER.with(|a| a.borrow().clone())
}

fn answer(a: Result<Vec<u8>, Vec<u8>>) {
    ANSWER.with(|slot| *slot.borrow_mut() = a);
}

fn seen() -> Vec<u8> {
    SEEN.with(|s| s.borrow().clone())
}

fn stand_at(addresses: &[u64]) {
    MOCKS.with(|m| {
        let mut m = m.borrow_mut();
        for &a in addresses {
            m.insert(Word::from_u64(a), recorder as Mock);
        }
    });
}

fn w(n: u64) -> Vec<u8> {
    Word::from_u64(n).to_be_bytes().to_vec()
}

fn words(ns: &[u64]) -> Vec<u8> {
    ns.iter().flat_map(|&n| w(n)).collect()
}

fn run(runtime: &[u8], data: &[u8]) -> Outcome {
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

fn bytes_args(sig: &str, parts: &[Vec<u8>]) -> Vec<u8> {
    let args: Vec<Arg> = parts.iter().map(|p| Arg::B(p.clone())).collect();
    encode_args(sig, &args)
}

const SRC: &str = "\
import \"std/crypto\"; import \"std/uint\"; storage is record { n : uint; }
external pure function add(const a : (uint, uint); const b : (uint, uint)) : (uint, uint) is Crypto.bn254Add(a, b)
external pure function mul(const p : (uint, uint); const s : uint) : (uint, uint) is Crypto.bn254Mul(p, s)
external pure function pair(const ps : list((uint, uint, uint, uint, uint, uint))) : bool is Crypto.bn254Pairing(ps)
external pure function blake(const r : uint32; const h : list(bytes32, 2); const m : list(bytes32, 4); const t : bytes16; const f : bool) : list(bytes32, 2) is
  Crypto.blake2f(r, h, m, t, f)
external pure function modexp(const b : bytes; const e : bytes; const m : bytes) : bytes is Crypto.modExp(b, e, m)
external pure function powmod(const b : uint; const e : uint; const m : uint) : uint is Uint.powMod(b, e, m)
external pure function kzg(const h : bytes32; const z : uint; const y : uint; const c : bytes; const p : bytes) : bool is
  Crypto.kzgPointEvaluation(h, z, y, c, p)
external pure function g1Add(const a : bytes; const b : bytes) : bytes is Crypto.bls12G1Add(a, b)
external pure function g1Msm(const pairs : bytes) : bytes is Crypto.bls12G1Msm(pairs)
external pure function g2Add(const a : bytes; const b : bytes) : bytes is Crypto.bls12G2Add(a, b)
external pure function g2Msm(const pairs : bytes) : bytes is Crypto.bls12G2Msm(pairs)
external pure function blsPair(const pairs : bytes) : bool is Crypto.bls12Pairing(pairs)
external pure function mapG1(const fp : bytes) : bytes is Crypto.bls12MapFpToG1(fp)
external pure function mapG2(const fp2 : bytes) : bytes is Crypto.bls12MapFp2ToG2(fp2)
external pure function p256(const h : bytes32; const r : bytes32; const s : bytes32; const x : bytes32; const y : bytes32) : bool is
  Crypto.p256Verify(h, r, s, x, y)
";

#[test]
fn bn254_calls_lay_out_their_input() {
    stand_at(&[6, 7, 8]);
    let runtime = deploy(&compile(SRC).expect("compile")).expect("deploy");
    answer(Ok(words(&[5, 6])));
    let out = run(
        &runtime,
        &[
            selector("add((uint256,uint256),(uint256,uint256))").to_vec(),
            words(&[1, 2, 3, 4]),
        ]
        .concat(),
    );
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(seen(), words(&[1, 2, 3, 4]));
    assert_eq!(out.returndata, words(&[5, 6]));
    let out = run(
        &runtime,
        &[
            selector("mul((uint256,uint256),uint256)").to_vec(),
            words(&[1, 2, 9]),
        ]
        .concat(),
    );
    assert_eq!(seen(), words(&[1, 2, 9]));
    assert_eq!(out.returndata, words(&[5, 6]));
    // A rejected point reverts.
    answer(Err(Vec::new()));
    assert!(
        run(
            &runtime,
            &[
                selector("add((uint256,uint256),(uint256,uint256))").to_vec(),
                words(&[1, 2, 3, 4])
            ]
            .concat()
        )
        .reverted
    );
    // The pairs are the input as the list holds them: six words each.
    let pairs: Vec<u64> = (1..=12).collect();
    let mut data = selector("pair((uint256,uint256,uint256,uint256,uint256,uint256)[])").to_vec();
    data.extend(words(&[32, 2]));
    data.extend(words(&pairs));
    answer(Ok(w(1)));
    let out = run(&runtime, &data);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(seen(), words(&pairs));
    assert_eq!(out.returndata, w(1));
    answer(Ok(w(0)));
    assert_eq!(run(&runtime, &data).returndata, w(0));
    // No answer, as from a chain without the precompile, is not `false`: it reverts.
    answer(Ok(Vec::new()));
    assert!(run(&runtime, &data).reverted);
}

#[test]
fn blake2f_lays_out_eip152_input() {
    stand_at(&[9]);
    let runtime = deploy(&compile(SRC).expect("compile")).expect("deploy");
    // EIP-152's fifth vector: BLAKE2b of "abc".
    let mut vector = vec![0, 0, 0, 12];
    vector.extend(hex_decode("48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b"));
    let mut m = b"abc".to_vec();
    m.resize(128, 0);
    vector.extend(m);
    let mut t = vec![3];
    t.resize(16, 0);
    vector.extend(t);
    vector.push(1);
    assert_eq!(vector.len(), 213);
    let expected = hex_decode("ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923");
    let mut data = selector("blake(uint32,bytes32[2],bytes32[4],bytes16,bool)").to_vec();
    data.extend(w(12));
    data.extend(&vector[4..68]);
    data.extend(&vector[68..196]);
    let mut t = vector[196..212].to_vec();
    t.resize(32, 0);
    data.extend(t);
    data.extend(w(1));
    answer(Ok(expected.clone()));
    let out = run(&runtime, &data);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(hex(&seen()), hex(&vector));
    assert_eq!(out.returndata, expected);
}

#[test]
fn modexp_lays_out_eip198_input() {
    stand_at(&[5]);
    let runtime = deploy(&compile(SRC).expect("compile")).expect("deploy");
    answer(Ok(vec![5]));
    let out = run(
        &runtime,
        &bytes_args("modexp(bytes,bytes,bytes)", &[vec![3], vec![5], vec![7]]),
    );
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(seen(), [words(&[1, 1, 1]), vec![3, 5, 7]].concat());
    assert_eq!(abi_string_value(&out.returndata), vec![5]);
    // A long modulus: the answer is as long as it.
    let modulus = vec![0xab; 40];
    answer(Ok(vec![0x11; 40]));
    let out = run(
        &runtime,
        &bytes_args(
            "modexp(bytes,bytes,bytes)",
            &[vec![2; 33], vec![], modulus.clone()],
        ),
    );
    assert_eq!(seen(), [words(&[33, 0, 40]), vec![2; 33], modulus].concat());
    assert_eq!(abi_string_value(&out.returndata), vec![0x11; 40]);
    answer(Ok(w(5)));
    let out = run(
        &runtime,
        &[
            selector("powmod(uint256,uint256,uint256)").to_vec(),
            words(&[3, 5, 7]),
        ]
        .concat(),
    );
    assert_eq!(seen(), words(&[32, 32, 32, 3, 5, 7]));
    assert_eq!(out.returndata, w(5));
    // A zero modulus divides by zero.
    let out = run(
        &runtime,
        &[
            selector("powmod(uint256,uint256,uint256)").to_vec(),
            words(&[3, 5, 0]),
        ]
        .concat(),
    );
    assert!(out.reverted);
    assert_eq!(
        out.returndata,
        [selector("Panic(uint256)").to_vec(), w(0x12)].concat()
    );
}

#[test]
fn point_evaluation_and_p256_answer_bools() {
    stand_at(&[0x0a, 0x100]);
    let runtime = deploy(&compile(SRC).expect("compile")).expect("deploy");
    let (commitment, proof) = (vec![0xc1; 48], vec![0xd2; 48]);
    let mut args = selector("kzg(bytes32,uint256,uint256,bytes,bytes)").to_vec();
    let mut vh = [0u8; 32];
    vh[0] = 1;
    args.extend(vh);
    args.extend(words(&[7, 8, 32 * 5, 32 * 8]));
    args.extend(w(48));
    args.extend([commitment.clone(), vec![0; 16]].concat());
    args.extend(w(48));
    args.extend([proof.clone(), vec![0; 16]].concat());
    answer(Ok(words(&[4096, 17])));
    let out = run(&runtime, &args);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(
        seen(),
        [vh.to_vec(), words(&[7, 8]), commitment, proof].concat()
    );
    assert_eq!(out.returndata, w(1));
    answer(Err(Vec::new()));
    assert_eq!(run(&runtime, &args).returndata, w(0));
    answer(Ok(Vec::new()));
    assert_eq!(
        run(&runtime, &args).returndata,
        w(0),
        "no precompile is no proof"
    );
    let sig: Vec<u8> = (1..=5).flat_map(|i| [i as u8; 32]).collect();
    let data = [
        selector("p256(bytes32,bytes32,bytes32,bytes32,bytes32)").to_vec(),
        sig.clone(),
    ]
    .concat();
    answer(Ok(w(1)));
    assert_eq!(run(&runtime, &data).returndata, w(1));
    assert_eq!(seen(), sig);
    answer(Ok(Vec::new()));
    assert_eq!(run(&runtime, &data).returndata, w(0));
}

#[test]
fn bls12_calls_concatenate_their_inputs() {
    stand_at(&[0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11]);
    let runtime = deploy(&compile(SRC).expect("compile")).expect("deploy");
    let (a, b) = (vec![0xaa; 128], vec![0xbb; 128]);
    answer(Ok(vec![0x11; 128]));
    let out = run(
        &runtime,
        &bytes_args("g1Add(bytes,bytes)", &[a.clone(), b.clone()]),
    );
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(seen(), [a.clone(), b.clone()].concat());
    assert_eq!(abi_string_value(&out.returndata), vec![0x11; 128]);
    let out = run(&runtime, &bytes_args("g1Msm(bytes)", &[vec![0xcc; 320]]));
    assert_eq!(seen(), vec![0xcc; 320]);
    assert_eq!(abi_string_value(&out.returndata), vec![0x11; 128]);
    let out = run(&runtime, &bytes_args("mapG1(bytes)", &[vec![0xdd; 64]]));
    assert_eq!(seen(), vec![0xdd; 64]);
    assert_eq!(abi_string_value(&out.returndata), vec![0x11; 128]);
    // A G2 point is 256 bytes; an answer of another size reverts.
    assert!(
        run(
            &runtime,
            &bytes_args("g2Add(bytes,bytes)", &[vec![1; 256], vec![2; 256]])
        )
        .reverted
    );
    answer(Ok(vec![0x22; 256]));
    let out = run(
        &runtime,
        &bytes_args("g2Add(bytes,bytes)", &[vec![1; 256], vec![2; 256]]),
    );
    assert_eq!(seen(), [vec![1; 256], vec![2; 256]].concat());
    assert_eq!(abi_string_value(&out.returndata), vec![0x22; 256]);
    let out = run(&runtime, &bytes_args("g2Msm(bytes)", &[vec![3; 288]]));
    assert_eq!(abi_string_value(&out.returndata), vec![0x22; 256]);
    let out = run(&runtime, &bytes_args("mapG2(bytes)", &[vec![4; 128]]));
    assert_eq!(seen(), vec![4; 128]);
    assert_eq!(abi_string_value(&out.returndata), vec![0x22; 256]);
    answer(Ok(w(1)));
    let out = run(&runtime, &bytes_args("blsPair(bytes)", &[vec![5; 384]]));
    assert_eq!(seen(), vec![5; 384]);
    assert_eq!(out.returndata, w(1));
    answer(Err(Vec::new()));
    assert!(run(&runtime, &bytes_args("blsPair(bytes)", &[vec![5; 384]])).reverted);
}

#[test]
fn precompile_arguments_are_typed() {
    for (body, want) in [
        (
            "Crypto.bn254Add((1, 2), true)",
            "`Crypto.bn254Add` takes `(uint256,uint256)` here",
        ),
        (
            "Crypto.p256Verify(0x01, 0x02, 0x03, 0x04)",
            "`Crypto.p256Verify` expects 5 arguments",
        ),
        (
            "Crypto.modExp(true, false, true)",
            "`Crypto.modExp` takes `bytes` here",
        ),
    ] {
        let src = format!("import \"std/crypto\"; storage is record {{ n : uint; }}\nexternal pure function f() : uint is {{ const x : bool := {body} = {body}; }} with 1\n");
        let err = compile(&src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}
