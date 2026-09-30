use super::*;

fn run(runtime: &[u8], data: &[u8], value: u64) -> Outcome {
    exec(
        runtime,
        data,
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(value),
        Word::from_u64(value),
    )
    .expect("run")
}

/// A name whose selector ends in a zero byte, which short calldata could also match.
fn zero_ending_name() -> String {
    (0..)
        .map(|i| format!("z{i}"))
        .find(|name| selector(&format!("{name}()"))[3] == 0)
        .expect("some name")
}

/// `plain` entrypoints `f{i}` and `payable` ones `p{i}`, each answering its own number,
/// and one whose selector ends in a zero byte answering 999.
fn entries(plain: usize, payable: usize, extra: &str) -> (String, Vec<(String, u64, bool)>) {
    let zero = zero_ending_name();
    let mut src = format!("import \"std/evm\"; storage is record {{ n : uint; }}\n{extra}\nexternal view function {zero}() : uint is 999\n");
    let mut sigs = vec![(format!("{zero}()"), 999, false)];
    for i in 0..plain {
        src += &format!("external view function f{i}() : uint is {i}\n");
        sigs.push((format!("f{i}()"), i as u64, false));
    }
    for i in 0..payable {
        src += &format!("external payable function p{i}() : uint is {{ skip }} with {i}\n");
        sigs.push((format!("p{i}()"), i as u64, true));
    }
    (src, sigs)
}

/// The bucket count of each table the dispatcher jumps through, in code order: the
/// index masked to a multiple of 16, then a push of two bytes per bucket.
fn tables(runtime: &[u8]) -> Vec<usize> {
    runtime
        .windows(4)
        .filter_map(|w| {
            [4, 8]
                .into_iter()
                .find(|&b| w == [0x60, ((b - 1) << 4) as u8, 0x16, 0x5f + 2 * b as u8])
        })
        .collect()
}

/// Every entrypoint answers, value only where payable, and every selector one bit away
/// from an entrypoint's, which shares its bucket for most bits, reaches `missed`.
fn check_dispatch(runtime: &[u8], sigs: &[(String, u64, bool)], missed: impl Fn(&[u8], Outcome)) {
    let sels: Vec<[u8; 4]> = sigs.iter().map(|(sig, _, _)| selector(sig)).collect();
    for (sig, n, payable) in sigs {
        let data = word_data(sig, &[]);
        let out = run(runtime, &data, 0);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        assert_eq!(out.returndata, Word::from_u64(*n).to_be_bytes(), "{sig}");
        let paid = run(runtime, &data, 1);
        assert_eq!(paid.reverted, !payable, "{sig} with value");
    }
    let mut misses: Vec<Vec<u8>> = vec![vec![0; 4], vec![0xff; 4], vec![0xde, 0xad, 0xbe, 0xef]];
    for sel in &sels {
        for bit in 0..32 {
            let mut other = *sel;
            other[bit / 8] ^= 0x80 >> (bit % 8);
            if !sels.contains(&other) {
                misses.push(other.to_vec());
            }
        }
    }
    for data in misses {
        assert!(!sels.iter().any(|s| s[..] == data[..]));
        missed(&data, run(runtime, &data, 0));
    }
}

#[test]
fn dispatch_shapes_hit_and_miss() {
    for (plain, shape) in [
        (4, vec![]),
        (12, vec![]),
        (13, vec![]),
        (16, vec![]),
        (17, vec![4]),
        (30, vec![4]),
        (31, vec![8]),
        (40, vec![8]),
    ] {
        let (src, sigs) = entries(plain, 0, "");
        let runtime = deploy(&compile(&src).expect("compile")).expect("deploy");
        assert_eq!(tables(&runtime), shape, "{plain} entrypoints");
        check_dispatch(&runtime, &sigs, |data, out| {
            assert!(out.reverted, "{data:?}")
        });
        // Short calldata never matches, even the selector it reads as.
        let zero = selector(&sigs[0].0);
        assert!(run(&runtime, &zero[..3], 0).reverted);
        assert!(run(&runtime, &[], 0).reverted);
    }
}

#[test]
fn dispatch_shapes_keep_fallback_and_receive() {
    let extra = "\
payable receive is { storage.n := 7; }
fallback : bytes is { skip } with Evm.calldata()";
    for (plain, shape) in [(4, vec![]), (13, vec![]), (19, vec![4]), (40, vec![8])] {
        let (src, sigs) = entries(plain, 0, extra);
        let runtime = deploy(&compile(&src).expect("compile")).expect("deploy");
        assert_eq!(tables(&runtime), shape, "{plain} entrypoints");
        check_dispatch(&runtime, &sigs, |data, out| {
            assert!(!out.reverted, "{data:?}: {}", pretty(&out.returndata));
            assert_eq!(out.returndata, data);
        });
        let zero = selector(&sigs[0].0);
        let short = run(&runtime, &zero[..3], 0);
        assert!(!short.reverted);
        assert_eq!(short.returndata, zero[..3]);
        // The fallback is not payable, on the short path too.
        assert!(run(&runtime, &zero[..3], 1).reverted);
        assert!(run(&runtime, &[0xde, 0xad, 0xbe, 0xef], 1).reverted);
        let plain_ether = run(&runtime, &[], 3);
        assert!(!plain_ether.reverted);
        assert_eq!(slot(&plain_ether.storage, 0), Word::from_u64(7));
    }
}

#[test]
fn dispatch_shapes_split_payable_entries() {
    // Payable entries dispatch first: a miss among them still reaches the others.
    for (plain, payable, shape) in [
        (3, 14, vec![]),
        (3, 20, vec![4]),
        (20, 3, vec![4]),
        (20, 20, vec![4, 4]),
        (18, 33, vec![8, 4]),
    ] {
        let (src, sigs) = entries(plain, payable, "");
        let runtime = deploy(&compile(&src).expect("compile")).expect("deploy");
        assert_eq!(tables(&runtime), shape, "{plain} and {payable} payable");
        check_dispatch(&runtime, &sigs, |data, out| {
            assert!(out.reverted, "{data:?}")
        });
        assert!(run(&runtime, &[0xde, 0xad, 0xbe, 0xef], 1).reverted);
    }
    // With a payable fallback, value to an entrypoint that is not payable is still refused.
    let (src, sigs) = entries(20, 20, "payable fallback is { storage.n := 5; }");
    let runtime = deploy(&compile(&src).expect("compile")).expect("deploy");
    check_dispatch(&runtime, &sigs, |data, out| {
        assert!(!out.reverted, "{data:?}");
        assert_eq!(slot(&out.storage, 0), Word::from_u64(5));
    });
    let paid = run(&runtime, &[0xde, 0xad, 0xbe, 0xef], 1);
    assert!(!paid.reverted);
}
