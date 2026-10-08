use super::*;

/// Every standard library file compiles inside a contract that imports it.
#[test]
fn every_stdlib_file_compiles() {
    for (path, _) in crate::modules::STD {
        if crate::is_spec_file(std::path::Path::new(path)) {
            continue;
        }
        let dir = std::env::temp_dir().join(format!("lithe-std-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let main = dir.join("main.lithe");
        let src = format!(
            "import \"{}\";\nstorage is record {{ n : uint; }}\nexternal function f() is {{ storage.n := 1; }}\n",
            path.trim_end_matches(".lithe")
        );
        std::fs::write(&main, src).unwrap();
        compile_file(&main).unwrap_or_else(|e| panic!("{path}: {e}"));
    }
}

fn w(n: u64) -> Arg {
    Arg::W(Word::from_u64(n))
}

/// `std/token`: an ERC-20 with burning, pausing, a cap, and ERC-2612 permits signed with
/// real keys against an independently computed EIP-712 domain.
#[test]
fn stdlib_erc20_and_permit() {
    let mut t = Session::new("examples/stdlib/token.lithe");
    assert_eq!(t.word("owner()", &[]), Word::from_u64(1));
    assert!(t.send(1, "mint(address,uint256)", &[w(2), w(100)]));
    assert!(!t.send(2, "mint(address,uint256)", &[w(2), w(1)]));
    t.reverted_with("OwnableUnauthorizedAccount(address)");
    assert!(t.send(2, "transfer(address,uint256)", &[w(3), w(40)]));
    assert_eq!(t.word("balanceOf(address)", &[w(2)]), Word::from_u64(60));
    assert!(!t.send(2, "transfer(address,uint256)", &[w(3), w(61)]));
    t.reverted_with("ERC20InsufficientBalance(address,uint256,uint256)");
    assert!(!t.send(2, "transfer(address,uint256)", &[w(0), w(1)]));
    t.reverted_with("ERC20InvalidReceiver(address)");
    assert!(t.send(2, "approve(address,uint256)", &[w(4), w(25)]));
    assert!(t.send(
        4,
        "transferFrom(address,address,uint256)",
        &[w(2), w(5), w(20)]
    ));
    assert_eq!(
        t.word("allowance(address,address)", &[w(2), w(4)]),
        Word::from_u64(5)
    );
    assert!(!t.send(
        4,
        "transferFrom(address,address,uint256)",
        &[w(2), w(5), w(6)]
    ));
    t.reverted_with("ERC20InsufficientAllowance(address,uint256,uint256)");
    assert!(t.send(3, "burn(uint256)", &[w(10)]));
    assert_eq!(t.word("totalSupply()", &[]), Word::from_u64(90));
    // `ERC20`'s `beforeTransfer` hook checks the pause, so it stops mints and burns too.
    assert!(t.send(1, "pause()", &[]));
    assert!(!t.send(2, "transfer(address,uint256)", &[w(3), w(1)]));
    t.reverted_with("EnforcedPause()");
    assert!(!t.send(1, "mint(address,uint256)", &[w(2), w(1)]));
    t.reverted_with("EnforcedPause()");
    assert!(!t.send(3, "burn(uint256)", &[w(1)]));
    t.reverted_with("EnforcedPause()");
    assert!(t.send(1, "unpause()", &[]));
    let cap = Word::from_hex("d3c21bcecceda1000000").unwrap();
    assert!(!t.send(1, "mint(address,uint256)", &[w(2), Arg::W(cap)]));
    t.reverted_with("ERC20ExceededCap(uint256,uint256)");

    // The domain, from its definition.
    let typehash = keccak_word(
        b"EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)",
    );
    let mut domain = Vec::new();
    for word in [
        typehash,
        keccak_word(b"Lithe Token"),
        keccak_word(b"1"),
        Word::from_u64(1),
        Word::from_u64(0x1000),
    ] {
        domain.extend_from_slice(&word.to_be_bytes());
    }
    let domain = keccak_word(&domain);
    assert_eq!(t.word("DOMAIN_SEPARATOR()", &[]), domain);

    let key = Word::from_u64(0xa11ce);
    let owner = crate::hash::address_of(key);
    assert!(t.send(1, "mint(address,uint256)", &[Arg::W(owner), w(1000)]));
    let permit_hash = |nonce: u64, deadline: u64| {
        let mut data = Vec::new();
        for word in [
            keccak_word(b"Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)"),
            owner,
            Word::from_u64(7),
            Word::from_u64(300),
            Word::from_u64(nonce),
            Word::from_u64(deadline),
        ] {
            data.extend_from_slice(&word.to_be_bytes());
        }
        let mut digest = vec![0x19, 0x01];
        digest.extend_from_slice(&domain.to_be_bytes());
        digest.extend_from_slice(&keccak_word(&data).to_be_bytes());
        keccak_word(&digest)
    };
    let deadline = 1_700_000_100;
    let (v, r, s) = crate::hash::sign(permit_hash(0, deadline), key, Word::from_u64(0x5eed));
    let permit = |v: u8, r: Word, s: Word, deadline: u64| {
        [
            Arg::W(owner),
            w(7),
            w(300),
            w(deadline),
            w(u64::from(v)),
            Arg::W(r),
            Arg::W(s),
        ]
    };
    let sig = "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)";
    assert!(
        t.send(9, sig, &permit(v, r, s, deadline)),
        "{}",
        pretty(&t.returned())
    );
    assert_eq!(
        t.word("allowance(address,address)", &[Arg::W(owner), w(7)]),
        Word::from_u64(300)
    );
    assert_eq!(
        t.word("nonces(address)", &[Arg::W(owner)]),
        Word::from_u64(1)
    );
    // The same signature again: the nonce has moved on, so it names another signer.
    assert!(!t.send(9, sig, &permit(v, r, s, deadline)));
    t.reverted_with("ERC2612InvalidSigner(address,address)");
    let late = 1_600_000_000;
    let (v, r, s) = crate::hash::sign(permit_hash(1, late), key, Word::from_u64(0x5eed));
    assert!(!t.send(9, sig, &permit(v, r, s, late)));
    t.reverted_with("ERC2612ExpiredSignature(uint256)");
}

/// `std/math`, `std/crypto`, `std/utils`, and `std/collections`, through one contract.
#[test]
fn stdlib_math_crypto_and_collections() {
    let mut u = Session::new("examples/stdlib/utils.lithe");
    let hexw = |s: &str| Word::from_hex(s).unwrap();
    // `sqrt` rounds down, at every scale.
    for (a, root) in [
        ("0", "0"),
        ("1", "1"),
        ("2", "1"),
        ("3", "1"),
        ("4", "2"),
        ("3f", "7"),
        ("40", "8"),
        ("fffffffffffffffe", "ffffffff"),
        ("10000000000000000", "100000000"),
        (
            "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            "ffffffffffffffffffffffffffffffff",
        ),
        (
            "fffffffffffffffffffffffffffffffe00000000000000000000000000000001",
            "ffffffffffffffffffffffffffffffff",
        ),
        (
            "fffffffffffffffffffffffffffffffe00000000000000000000000000000000",
            "fffffffffffffffffffffffffffffffe",
        ),
        ("123456789abcdef0123456789abcdef", "1111111111111109"),
    ] {
        assert_eq!(
            u.word("sqrt(uint256)", &[Arg::W(hexw(a))]),
            hexw(root),
            "sqrt({a})"
        );
    }
    let one = Word::from_u64(1);
    for (a, log) in [(0, 0), (1, 0), (2, 1), (3, 1), (4, 2), (255, 7), (256, 8)] {
        assert_eq!(
            u.word("log2(uint256)", &[w(a)]),
            Word::from_u64(log),
            "log2({a})"
        );
    }
    for k in [63, 64, 127, 128, 200, 255] {
        let p = one.shl(k);
        assert_eq!(
            u.word("log2(uint256)", &[Arg::W(p)]),
            Word::from_u64(k as u64)
        );
        assert_eq!(
            u.word("log2(uint256)", &[Arg::W(p.wrapping_sub(one))]),
            Word::from_u64(k as u64 - 1)
        );
    }
    assert_eq!(
        u.word("log2(uint256)", &[Arg::W(Word::from_u64(0).not())]),
        Word::from_u64(255)
    );
    // Around every power of two and at pseudo-random words, against bit-by-bit references.
    let isqrt = |a: Word| {
        let mut r = Word::from_u64(0);
        for bit in (0..128).rev() {
            let c = r.bitor(one.shl(bit));
            let (sq, over) = c.overflowing_mul(c);
            if !over && !a.lt(sq) {
                r = c;
            }
        }
        r
    };
    let bits = |a: Word| (0..256).rev().find(|&k| a.bit(k)).unwrap_or(0) as u64;
    let mut seed = 0x2545_f491_4f6c_dd1du64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let mut samples = vec![Word::from_u64(0).not()];
    let mut p = one;
    for _ in 0..=77 {
        samples.extend([p, p.wrapping_add(one)]);
        p = p.wrapping_mul(Word::from_u64(10));
    }
    for k in 0..256 {
        let p = one.shl(k);
        samples.extend([p, p.wrapping_sub(one), p.wrapping_add(one)]);
        samples.push(Word([next(), next(), next(), next()]).shr(k));
    }
    // Rounded up: one more where `a` is past the power of the base rounded down to.
    let up = |a: Word, log: u64, pow: Word| log + u64::from(pow.lt(a));
    let log10 = |a: Word| {
        let (mut k, mut p) = (0, Word::from_u64(10));
        while !a.lt(p) && k < 77 {
            (k, p) = (k + 1, p.wrapping_mul(Word::from_u64(10)));
        }
        k
    };
    for a in samples {
        assert_eq!(
            u.word("sqrt(uint256)", &[Arg::W(a)]),
            isqrt(a),
            "sqrt({a:?})"
        );
        assert_eq!(
            u.word("log2(uint256)", &[Arg::W(a)]),
            Word::from_u64(bits(a)),
            "log2({a:?})"
        );
        let (l10, l256) = (log10(a), bits(a) / 8);
        assert_eq!(
            u.word("log10(uint256)", &[Arg::W(a)]),
            Word::from_u64(l10),
            "log10({a:?})"
        );
        assert_eq!(
            u.word("log256(uint256)", &[Arg::W(a)]),
            Word::from_u64(l256),
            "log256({a:?})"
        );
        let ten_pow = (0..l10).fold(one, |p, _| p.wrapping_mul(Word::from_u64(10)));
        for (sig, want) in [
            ("log2Up(uint256)", up(a, bits(a), one.shl(bits(a) as u32))),
            ("log10Up(uint256)", up(a, l10, ten_pow)),
            ("log256Up(uint256)", up(a, l256, one.shl(8 * l256 as u32))),
        ] {
            assert_eq!(
                u.word(sig, &[Arg::W(a)]),
                Word::from_u64(want),
                "{sig} {a:?}"
            );
        }
    }
    let int = |n: i64| {
        let m = Word::from_u64(n.unsigned_abs());
        if n < 0 {
            Word::from_u64(0).wrapping_sub(m)
        } else {
            m
        }
    };
    let int_min = one.shl(255);
    let int_max = int_min.wrapping_sub(one);
    for (a, b, mean) in [
        (int(3), int(0), int(1)),
        (int(-3), int(0), int(-1)),
        (int(-4), int(1), int(-1)),
        (int(-1), int(-2), int(-1)),
        (int(-2), int(-4), int(-3)),
        (int_min, int_min, int_min),
        (int_max, int_max, int_max),
        (int_min, int_max, int(0)),
    ] {
        assert_eq!(
            u.word("averageInt(int256,int256)", &[Arg::W(a), Arg::W(b)]),
            mean
        );
    }
    assert_eq!(
        u.word("minInt(int256,int256)", &[Arg::W(int(-5)), w(2)]),
        int(-5)
    );
    assert_eq!(
        u.word("maxInt(int256,int256)", &[Arg::W(int(-5)), w(2)]),
        int(2)
    );
    assert_eq!(
        u.word("maxInt(int256,int256)", &[Arg::W(int_min), Arg::W(int(-1))]),
        int(-1)
    );
    let ten = Word::from_u64(10);
    let mut p = one;
    for k in 0..=77u64 {
        assert_eq!(
            u.word("log10(uint256)", &[Arg::W(p)]),
            Word::from_u64(k),
            "log10(10^{k})"
        );
        if k > 0 {
            let below = p.wrapping_sub(one);
            assert_eq!(
                u.word("log10(uint256)", &[Arg::W(below)]),
                Word::from_u64(k - 1)
            );
        }
        if k < 77 {
            p = p.wrapping_mul(ten);
        }
    }
    assert_eq!(u.word("log10(uint256)", &[w(0)]), Word::from_u64(0));
    assert_eq!(
        u.word("log10(uint256)", &[Arg::W(Word::from_u64(0).not())]),
        Word::from_u64(77)
    );
    let mut clamp_int = |x: i64, lo: i64, hi: i64| {
        u.word(
            "clampInt(int256,int256,int256)",
            &[Arg::W(int(x)), Arg::W(int(lo)), Arg::W(int(hi))],
        )
    };
    assert_eq!(clamp_int(-9, -5, 3), int(-5));
    assert_eq!(clamp_int(9, -5, 3), int(3));
    assert_eq!(clamp_int(-2, -5, 3), int(-2));
    assert_eq!(u.word("abs(int256)", &[w(7)]), Word::from_u64(7));
    assert_eq!(
        u.word("abs(int256)", &[Arg::W(Word::from_u64(6).not())]),
        Word::from_u64(7)
    );
    assert_eq!(u.word("abs(int256)", &[Arg::W(one.shl(255))]), one.shl(255));
    let max = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    assert_eq!(
        u.word(
            "average(uint256,uint256)",
            &[Arg::W(hexw(max)), Arg::W(hexw(max))]
        ),
        hexw(max)
    );
    assert_eq!(
        u.word("ceilDiv(uint256,uint256)", &[w(7), w(2)]),
        Word::from_u64(4)
    );
    assert_eq!(
        u.word("ceilDiv(uint256,uint256)", &[w(0), w(2)]),
        Word::from_u64(0)
    );
    assert_eq!(
        u.word("mulDivUp(uint256,uint256,uint256)", &[w(7), w(3), w(2)]),
        Word::from_u64(11)
    );
    assert_eq!(
        u.word("clamp(uint256,uint256,uint256)", &[w(9), w(2), w(5)]),
        Word::from_u64(5)
    );
    assert!(!u.send(0, "clamp(uint256,uint256,uint256)", &[w(1), w(5), w(2)]));
    u.reverted_with("MathInvalidRange(uint256,uint256)");
    assert!(!u.send(
        0,
        "clampInt(int256,int256,int256)",
        &[w(0), w(1), Arg::W(int(-1))]
    ));
    u.reverted_with("MathInvalidSignedRange(int256,int256)");
    assert!(!u.send(0, "toUint(int256)", &[Arg::W(Word::from_u64(3).not())]));
    u.reverted_with("SafeCastOverflowedIntToUint(int256)");
    assert!(!u.send(0, "toInt(uint256)", &[Arg::W(hexw(max))]));
    u.reverted_with("SafeCastOverflowedUintToInt(uint256)");
    let e18 = 1_000_000_000_000_000_000u64;
    assert_eq!(
        u.word("wadMul(uint256,uint256)", &[w(3 * e18 / 2), w(4 * e18)]),
        Word::from_u64(6 * e18)
    );
    assert_eq!(
        u.word("wadDiv(uint256,uint256)", &[w(3 * e18), w(2 * e18)]),
        Word::from_u64(3 * e18 / 2)
    );
    assert_eq!(
        u.word("applyBps(uint256,uint256)", &[w(20_000), w(25)]),
        Word::from_u64(50)
    );

    // A Merkle tree of five leaves, pairs hashed in sorted order.
    let pair = |a: Word, b: Word| {
        let (lo, hi) = if a.lt(b) { (a, b) } else { (b, a) };
        let mut data = lo.to_be_bytes().to_vec();
        data.extend_from_slice(&hi.to_be_bytes());
        keccak_word(&data)
    };
    let leaves: Vec<Word> = (0u8..5).map(|i| keccak_word(&[i])).collect();
    let l1 = [
        pair(leaves[0], leaves[1]),
        pair(leaves[2], leaves[3]),
        leaves[4],
    ];
    let l2 = [pair(l1[0], l1[1]), l1[2]];
    let root = pair(l2[0], l2[1]);
    let proof = |nodes: &[Word]| Arg::L(nodes.to_vec());
    let verify = "verify(bytes32[],bytes32,bytes32)";
    assert_eq!(
        u.word(
            verify,
            &[
                proof(&[leaves[3], l1[0], l1[2]]),
                Arg::W(root),
                Arg::W(leaves[2])
            ]
        ),
        Word::from_u64(1)
    );
    assert_eq!(
        u.word(verify, &[proof(&[l2[0]]), Arg::W(root), Arg::W(leaves[4])]),
        Word::from_u64(1)
    );
    assert_eq!(
        u.word(
            verify,
            &[
                proof(&[leaves[3], l1[0], l1[2]]),
                Arg::W(root),
                Arg::W(leaves[1])
            ]
        ),
        Word::from_u64(0)
    );
    assert_eq!(
        u.word(verify, &[proof(&[]), Arg::W(root), Arg::W(root)]),
        Word::from_u64(1)
    );

    // ECDSA: a wallet's signature recovers its signer; the malleable twin doesn't.
    let key = Word::from_u64(0xb0b);
    let hash = keccak_word(b"hello");
    let (v, r, s) = crate::hash::sign(hash, key, Word::from_u64(0x77));
    let mut sig = r.to_be_bytes().to_vec();
    sig.extend_from_slice(&s.to_be_bytes());
    sig.push(v);
    let signer = crate::hash::address_of(key);
    assert_eq!(
        u.word(
            "recover(bytes32,bytes)",
            &[Arg::W(hash), Arg::B(sig.clone())]
        ),
        signer
    );
    assert_eq!(
        u.word(
            "recoverVrs(bytes32,uint8,bytes32,bytes32)",
            &[Arg::W(hash), w(u64::from(v)), Arg::W(r), Arg::W(s)]
        ),
        signer
    );
    let n = hexw("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
    let high = n.wrapping_sub(s);
    let twin = if v == 27 { 28 } else { 27 };
    assert!(!u.send(
        0,
        "recoverVrs(bytes32,uint8,bytes32,bytes32)",
        &[Arg::W(hash), w(twin), Arg::W(r), Arg::W(high)]
    ));
    u.reverted_with("ECDSAInvalidSignatureS(bytes32)");
    assert!(!u.send(
        0,
        "recover(bytes32,bytes)",
        &[Arg::W(hash), Arg::B(sig[..64].to_vec())]
    ));
    u.reverted_with("ECDSAInvalidSignatureLength(uint256)");
    let mut prefixed = b"\x19Ethereum Signed Message:\n32".to_vec();
    prefixed.extend_from_slice(&hash.to_be_bytes());
    assert_eq!(
        u.word("ethMessage(bytes32)", &[Arg::W(hash)]),
        keccak_word(&prefixed)
    );

    // CREATE2: keccak256(0xff ++ deployer ++ salt ++ code hash), low 20 bytes.
    let (salt, code) = (keccak_word(b"salt"), keccak_word(b"code"));
    let mut data = vec![0xff];
    data.extend_from_slice(&Word::from_u64(0xdead).to_be_bytes()[12..]);
    data.extend_from_slice(&salt.to_be_bytes());
    data.extend_from_slice(&code.to_be_bytes());
    let mut addr = [0u8; 32];
    addr[12..].copy_from_slice(&crate::keccak::keccak256(&data)[12..]);
    assert_eq!(
        u.word(
            "create2Address(bytes32,bytes32,address)",
            &[Arg::W(salt), Arg::W(code), w(0xdead)]
        ),
        Word::from_be_bytes(addr)
    );

    // Nonces count up per account; each call here uses one.
    assert_eq!(u.word("useNonce(address)", &[w(5)]), Word::from_u64(0));
    assert_eq!(u.word("useNonce(address)", &[w(5)]), Word::from_u64(1));
    assert_eq!(u.word("useNonce(address)", &[w(6)]), Word::from_u64(0));

    // A bitmap packs 256 flags to a slot.
    for i in [0u64, 255, 256, 1000] {
        assert!(u.send(0, "claim(uint256)", &[w(i)]));
    }
    for (i, set) in [
        (0u64, true),
        (1, false),
        (255, true),
        (256, true),
        (257, false),
        (1000, true),
    ] {
        assert_eq!(
            u.word("isClaimed(uint256)", &[w(i)]),
            Word::from_u64(u64::from(set)),
            "{i}"
        );
    }
    assert!(u.send(0, "unclaim(uint256)", &[w(255)]));
    assert_eq!(u.word("isClaimed(uint256)", &[w(255)]), Word::from_u64(0));
    assert_eq!(u.word("isClaimed(uint256)", &[w(0)]), Word::from_u64(1));

    // A queue pops in push order.
    for caller in [11u64, 12, 13] {
        assert!(u.send(caller, "enqueue()", &[]));
    }
    assert_eq!(u.word("queued()", &[]), Word::from_u64(3));
    assert_eq!(u.word("dequeue()", &[]), Word::from_u64(11));
    assert_eq!(u.word("dequeue()", &[]), Word::from_u64(12));
    assert_eq!(u.word("dequeue()", &[]), Word::from_u64(13));
    assert!(!u.send(0, "dequeue()", &[]));
    u.reverted_with("QueueEmpty()");

    // Checkpoints at block 100: a second push at the same key replaces the value.
    assert!(u.send(0, "checkpointValue(uint256)", &[w(5)]));
    assert!(u.send(0, "checkpointValue(uint256)", &[w(8)]));
    assert_eq!(u.word("checkpoints()", &[]), Word::from_u64(1));
    assert_eq!(u.word("latest()", &[]), Word::from_u64(8));
    assert_eq!(u.word("valueAt(uint256)", &[w(100)]), Word::from_u64(8));
    assert_eq!(u.word("valueAt(uint256)", &[w(150)]), Word::from_u64(8));
    assert_eq!(u.word("valueAt(uint256)", &[w(99)]), Word::from_u64(0));

    // Sets.
    assert!(u.send(21, "join()", &[]));
    assert!(u.send(21, "join()", &[]));
    assert!(u.send(22, "join()", &[]));
    assert_eq!(u.word("member(address)", &[w(21)]), Word::from_u64(1));
    assert_eq!(u.word("member(address)", &[w(23)]), Word::from_u64(0));
    assert_eq!(u.word("listedCount()", &[]), Word::from_u64(2));
}

/// `std/token/erc20_votes.lithe` with roles, a pause, a cap, and permits: votes follow
/// delegation and every balance change, and the history answers as of past blocks.
#[test]
fn stdlib_governance_token() {
    let at = |block: u64| BLOCK.with(|b| b.set(block));
    at(100);
    let mut t = Session::new("examples/stdlib/governance_token.lithe");
    let votes = |t: &mut Session, who: u64| t.word("getVotes(address)", &[w(who)]);
    let past = |t: &mut Session, who: u64, block: u64| {
        t.word("getPastVotes(address,uint256)", &[w(who), w(block)])
    };
    assert!(t.send(1, "mint(address,uint256)", &[w(2), w(1000)]));
    assert!(!t.send(2, "mint(address,uint256)", &[w(2), w(1)]));
    t.reverted_with("AccessControlUnauthorizedAccount(address,bytes32)");
    // Votes count once delegated.
    assert_eq!(votes(&mut t, 2), Word::from_u64(0));
    assert!(t.send(2, "delegate(address)", &[w(2)]));
    assert_eq!(votes(&mut t, 2), Word::from_u64(1000));
    assert_eq!(t.word("delegates(address)", &[w(2)]), Word::from_u64(2));
    for block in 101..=108 {
        at(block);
        assert!(t.send(2, "transfer(address,uint256)", &[w(3), w(10)]));
    }
    assert_eq!(votes(&mut t, 2), Word::from_u64(920));
    assert_eq!(votes(&mut t, 3), Word::from_u64(0));
    assert_eq!(
        t.word("numCheckpoints(address)", &[w(2)]),
        Word::from_u64(9)
    );
    assert!(t.send(0, "checkpoints(address,uint32)", &[w(2), w(3)]));
    let point = t.returned();
    assert_eq!(
        (load_bytes(&point, 0), load_bytes(&point, 32)),
        (Word::from_u64(103), Word::from_u64(970))
    );
    assert!(!t.send(0, "checkpoints(address,uint32)", &[w(2), w(9)]));
    at(120);
    for (block, want) in [
        (99, 0),
        (100, 1000),
        (101, 990),
        (104, 960),
        (107, 930),
        (108, 920),
        (119, 920),
    ] {
        assert_eq!(
            past(&mut t, 2, block),
            Word::from_u64(want),
            "block {block}"
        );
    }
    assert!(!t.send(0, "getPastVotes(address,uint256)", &[w(2), w(120)]));
    t.reverted_with("ERC5805FutureLookup(uint256,uint48)");
    assert_eq!(
        t.word("getPastTotalSupply(uint256)", &[w(100)]),
        Word::from_u64(1000)
    );
    assert_eq!(t.word("clock()", &[]), Word::from_u64(120));

    // A delegate moves its votes; burning and minting move the total.
    assert!(t.send(3, "delegate(address)", &[w(2)]));
    assert_eq!(votes(&mut t, 2), Word::from_u64(1000));
    assert!(t.send(2, "burn(uint256)", &[w(100)]));
    assert_eq!(votes(&mut t, 2), Word::from_u64(900));
    at(121);
    assert_eq!(
        t.word("getPastTotalSupply(uint256)", &[w(120)]),
        Word::from_u64(900)
    );

    // The pause stops every balance change, delegation doesn't.
    assert!(t.send(1, "pause()", &[]));
    assert!(!t.send(2, "transfer(address,uint256)", &[w(3), w(1)]));
    t.reverted_with("EnforcedPause()");
    assert!(!t.send(1, "mint(address,uint256)", &[w(2), w(1)]));
    t.reverted_with("EnforcedPause()");
    assert!(t.send(2, "delegate(address)", &[w(3)]));
    assert!(t.send(1, "unpause()", &[]));
    let cap = Word::from_hex("084595161401484a000000").unwrap();
    assert!(!t.send(1, "mint(address,uint256)", &[w(2), Arg::W(cap)]));
    t.reverted_with("ERC20ExceededCap(uint256,uint256)");

    // Delegation by signature, against the domain.
    let mut domain = Vec::new();
    for word in [
        keccak_word(
            b"EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)",
        ),
        keccak_word(b"Lithe Governance"),
        keccak_word(b"1"),
        Word::from_u64(1),
        Word::from_u64(0x1000),
    ] {
        domain.extend_from_slice(&word.to_be_bytes());
    }
    let domain = keccak_word(&domain);
    assert_eq!(t.word("DOMAIN_SEPARATOR()", &[]), domain);
    let key = Word::from_u64(0xb0b);
    let signer = crate::hash::address_of(key);
    assert!(t.send(1, "mint(address,uint256)", &[Arg::W(signer), w(50)]));
    let delegation = |nonce: u64, expiry: u64| {
        let mut data = Vec::new();
        for word in [
            keccak_word(b"Delegation(address delegatee,uint256 nonce,uint256 expiry)"),
            Word::from_u64(5),
            Word::from_u64(nonce),
            Word::from_u64(expiry),
        ] {
            data.extend_from_slice(&word.to_be_bytes());
        }
        let mut digest = vec![0x19, 0x01];
        digest.extend_from_slice(&domain.to_be_bytes());
        digest.extend_from_slice(&keccak_word(&data).to_be_bytes());
        keccak_word(&digest)
    };
    let expiry = 1_700_000_100;
    let (v, r, s) = crate::hash::sign(delegation(0, expiry), key, Word::from_u64(0x5eed));
    let args = [w(5), w(0), w(expiry), w(u64::from(v)), Arg::W(r), Arg::W(s)];
    let sig = "delegateBySig(address,uint256,uint256,uint8,bytes32,bytes32)";
    assert!(t.send(9, sig, &args), "{}", pretty(&t.returned()));
    assert_eq!(
        t.word("delegates(address)", &[Arg::W(signer)]),
        Word::from_u64(5)
    );
    assert_eq!(votes(&mut t, 5), Word::from_u64(50));
    assert!(!t.send(9, sig, &args));
    t.reverted_with("InvalidAccountNonce(address,uint256)");
    at(100);
}

/// `std/access` and `std/security`: roles with admins, two-step ownership, and a pause
/// only a pauser may pull.
#[test]
fn stdlib_access_control() {
    let mut a = Session::new("examples/stdlib/roles.lithe");
    let minter = Arg::W(keccak_word(b"MINTER_ROLE"));
    let pauser = || Arg::W(keccak_word(b"PAUSER_ROLE"));
    let admin = Arg::W(Word::from_u64(0));
    assert!(a.send(1, "recordEntry(address,uint256)", &[w(5), w(3)]));
    assert!(!a.send(2, "recordEntry(address,uint256)", &[w(5), w(3)]));
    a.reverted_with("AccessControlUnauthorizedAccount(address,bytes32)");
    assert!(!a.send(
        2,
        "grantRole(bytes32,address)",
        &[Arg::W(keccak_word(b"MINTER_ROLE")), w(2)]
    ));
    assert!(a.send(1, "grantRole(bytes32,address)", &[minter, w(2)]));
    assert!(a.send(2, "recordEntry(address,uint256)", &[w(5), w(4)]));
    assert_eq!(a.word("entry(address)", &[w(5)]), Word::from_u64(7));
    assert!(!a.send(
        3,
        "renounceRole(bytes32,address)",
        &[Arg::W(keccak_word(b"MINTER_ROLE")), w(2)]
    ));
    a.reverted_with("AccessControlBadConfirmation()");
    assert!(a.send(
        2,
        "renounceRole(bytes32,address)",
        &[Arg::W(keccak_word(b"MINTER_ROLE")), w(2)]
    ));
    assert_eq!(
        a.word(
            "hasRole(bytes32,address)",
            &[Arg::W(keccak_word(b"MINTER_ROLE")), w(2)]
        ),
        Word::from_u64(0)
    );
    assert_eq!(
        a.word("hasRole(bytes32,address)", &[admin, w(1)]),
        Word::from_u64(1)
    );
    assert_eq!(
        a.word("getRoleAdmin(bytes32)", &[pauser()]),
        Word::from_u64(0)
    );

    assert!(!a.send(1, "pause()", &[]));
    a.reverted_with("AccessControlUnauthorizedAccount(address,bytes32)");
    assert!(a.send(1, "setPauser(address,bool)", &[w(4), w(1)]));
    assert!(a.send(4, "pause()", &[]));
    assert!(!a.send(1, "recordEntry(address,uint256)", &[w(5), w(1)]));
    a.reverted_with("EnforcedPause()");
    assert!(a.send(4, "unpause()", &[]));
    assert!(!a.send(4, "unpause()", &[]));
    a.reverted_with("ExpectedPause()");

    assert!(a.send(1, "transferOwnership(address)", &[w(9)]));
    assert_eq!(a.word("owner()", &[]), Word::from_u64(1));
    assert_eq!(a.word("pendingOwner()", &[]), Word::from_u64(9));
    assert!(!a.send(8, "acceptOwnership()", &[]));
    a.reverted_with("OwnableUnauthorizedAccount(address)");
    assert!(a.send(9, "acceptOwnership()", &[]));
    assert_eq!(a.word("owner()", &[]), Word::from_u64(9));
    assert_eq!(a.word("pendingOwner()", &[]), Word::from_u64(0));
    assert!(!a.send(1, "setPauser(address,bool)", &[w(4), w(0)]));
    assert!(a.send(9, "setPauser(address,bool)", &[w(4), w(0)]));
    assert!(!a.send(4, "pause()", &[]));
}

/// `std/token/erc721`: minting to accounts, approvals, transfers, and burning.
#[test]
fn stdlib_erc721() {
    let mut n = Session::new("examples/stdlib/nft.lithe");
    assert!(n.send(2, "mint()", &[]));
    assert_eq!(load_bytes(&n.returned(), 0), Word::from_u64(0));
    assert!(n.send(3, "mint()", &[]));
    assert_eq!(n.word("ownerOf(uint256)", &[w(1)]), Word::from_u64(3));
    assert!(!n.send(0, "ownerOf(uint256)", &[w(7)]));
    n.reverted_with("ERC721NonexistentToken(uint256)");
    assert!(!n.send(
        4,
        "transferFrom(address,address,uint256)",
        &[w(3), w(4), w(1)]
    ));
    n.reverted_with("ERC721InsufficientApproval(address,uint256)");
    assert!(n.send(3, "approve(address,uint256)", &[w(4), w(1)]));
    assert!(n.send(
        4,
        "transferFrom(address,address,uint256)",
        &[w(3), w(5), w(1)]
    ));
    assert_eq!(n.word("ownerOf(uint256)", &[w(1)]), Word::from_u64(5));
    assert_eq!(n.word("getApproved(uint256)", &[w(1)]), Word::from_u64(0));
    assert!(n.send(5, "setApprovalForAll(address,bool)", &[w(6), w(1)]));
    assert!(n.send(
        6,
        "safeTransferFrom(address,address,uint256)",
        &[w(5), w(7), w(1)]
    ));
    assert_eq!(n.word("balanceOf(address)", &[w(7)]), Word::from_u64(1));
    assert!(!n.send(6, "burn(uint256)", &[w(1)]));
    assert!(n.send(7, "burn(uint256)", &[w(1)]));
    assert!(!n.send(0, "ownerOf(uint256)", &[w(1)]));
    // A `bytes4` argument sits in the high bytes of its word.
    let id = |sel: u64| Arg::W(Word::from_u64(sel).shl(224));
    assert_eq!(
        n.word("supportsInterface(bytes4)", &[id(0x80ac58cd)]),
        Word::from_u64(1)
    );
    assert_eq!(
        n.word("supportsInterface(bytes4)", &[id(0xffffffff)]),
        Word::from_u64(0)
    );
}

/// `std/token/erc1155` with its supply extension: minting, approvals, transfers, burning,
/// and the totals they keep.
#[test]
fn stdlib_erc1155() {
    let mut t = Session::new("examples/stdlib/multi_token.lithe");
    let uri = t.send(0, "uri(uint256)", &[w(1)]);
    assert!(uri);
    assert_eq!(
        t.returned(),
        abi_string("f()", b"https://items.example/api/item/{id}.json")[4..]
    );
    let mint = "mint(address,uint256,uint256,bytes)";
    assert!(!t.send(2, mint, &[w(2), w(1), w(100), Arg::B(vec![])]));
    t.reverted_with("OwnableUnauthorizedAccount(address)");
    assert!(t.send(1, mint, &[w(2), w(1), w(100), Arg::B(vec![])]));
    assert_eq!(
        t.word("balanceOf(address,uint256)", &[w(2), w(1)]),
        Word::from_u64(100)
    );
    let transfer = "safeTransferFrom(address,address,uint256,uint256,bytes)";
    assert!(!t.send(4, transfer, &[w(2), w(3), w(1), w(30), Arg::B(vec![])]));
    t.reverted_with("ERC1155MissingApprovalForAll(address,address)");
    assert!(t.send(2, transfer, &[w(2), w(3), w(1), w(30), Arg::B(vec![])]));
    assert_eq!(
        t.word("balanceOf(address,uint256)", &[w(3), w(1)]),
        Word::from_u64(30)
    );
    assert!(t.send(3, "setApprovalForAll(address,bool)", &[w(4), w(1)]));
    let burn = "burn(address,uint256,uint256)";
    assert!(t.send(4, burn, &[w(3), w(1), w(10)]));
    assert!(!t.send(3, burn, &[w(3), w(1), w(100)]));
    t.reverted_with("ERC1155InsufficientBalance(address,uint256,uint256,uint256)");
    assert_eq!(t.word("totalSupply(uint256)", &[w(1)]), Word::from_u64(90));
    assert_eq!(t.word("totalSupply()", &[]), Word::from_u64(90));
    assert_eq!(t.word("exists(uint256)", &[w(1)]), Word::from_u64(1));
    assert_eq!(t.word("exists(uint256)", &[w(2)]), Word::from_u64(0));
    // `ERC1155`'s `afterTransfer` hook sees a batch whole: each id's supply, and the total.
    let ids = || Arg::L(vec![Word::from_u64(2), Word::from_u64(5)]);
    let mint_batch = "mintBatch(address,uint256[],uint256[],bytes)";
    let values = Arg::L(vec![Word::from_u64(7), Word::from_u64(11)]);
    assert!(t.send(1, mint_batch, &[w(3), ids(), values, Arg::B(vec![])]));
    let batch = "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)";
    let moved = Arg::L(vec![Word::from_u64(1), Word::from_u64(1)]);
    assert!(t.send(3, batch, &[w(3), w(2), ids(), moved, Arg::B(vec![])]));
    let burned = Arg::L(vec![Word::from_u64(2), Word::from_u64(3)]);
    assert!(t.send(
        3,
        "burnBatch(address,uint256[],uint256[])",
        &[w(3), ids(), burned]
    ));
    assert_eq!(t.word("totalSupply(uint256)", &[w(2)]), Word::from_u64(5));
    assert_eq!(t.word("totalSupply(uint256)", &[w(5)]), Word::from_u64(8));
    assert_eq!(t.word("totalSupply()", &[]), Word::from_u64(103));
    let id = |sel: u64| Arg::W(Word::from_u64(sel).shl(224));
    for (sel, want) in [(0xd9b67a26, 1), (0x0e89341c, 1), (0x80ac58cd, 0)] {
        assert_eq!(
            t.word("supportsInterface(bytes4)", &[id(sel)]),
            Word::from_u64(want)
        );
    }
}

/// `std/token/erc6909` with its extensions: operators move anything and spend no
/// allowance, allowances are per id and `Uint.max` is never spent, and every failure path
/// raises OpenZeppelin's error.
#[test]
fn stdlib_erc6909() {
    let mut t = Session::new("examples/stdlib/claims.lithe");
    let bal = |t: &mut Session, owner: u64, id: u64| {
        t.word("balanceOf(address,uint256)", &[w(owner), w(id)])
    };
    let allowance = |t: &mut Session, owner: u64, spender: u64, id: u64| {
        t.word(
            "allowance(address,address,uint256)",
            &[w(owner), w(spender), w(id)],
        )
    };
    let topics = |t: &Session| -> Vec<Vec<Word>> {
        let out = t.last.as_ref().unwrap();
        out.trace
            .iter()
            .filter_map(|e| match e {
                Ev::Log { topics } => Some(topics.clone()),
                _ => None,
            })
            .collect()
    };
    let mint = "mint(address,uint256,uint256)";
    let transfer = "transfer(address,uint256,uint256)";
    let from = "transferFrom(address,address,uint256,uint256)";
    let approve = "approve(address,uint256,uint256)";
    let operator = "setOperator(address,bool)";
    let burn = "burn(address,uint256,uint256)";

    assert!(!t.send(2, mint, &[w(2), w(1), w(100)]));
    t.reverted_with("OwnableUnauthorizedAccount(address)");
    assert!(!t.send(1, mint, &[w(0), w(1), w(100)]));
    t.reverted_with("ERC6909InvalidReceiver(address)");
    assert!(t.send(1, mint, &[w(2), w(1), w(100)]));
    let transfer_topic = keccak_word(b"Transfer(address,address,address,uint256,uint256)");
    assert_eq!(
        topics(&t),
        vec![vec![
            transfer_topic,
            Word::from_u64(0),
            Word::from_u64(2),
            Word::from_u64(1)
        ]]
    );
    assert!(t.send(1, mint, &[w(2), w(2), w(50)]));
    assert_eq!(bal(&mut t, 2, 1), Word::from_u64(100));

    // Plain transfers, and their failures in OpenZeppelin's order.
    assert!(t.send(2, transfer, &[w(3), w(1), w(10)]));
    assert_eq!(load_bytes(&t.returned(), 0), Word::from_u64(1));
    assert_eq!(bal(&mut t, 3, 1), Word::from_u64(10));
    assert!(!t.send(2, transfer, &[w(0), w(1), w(1)]));
    t.reverted_with("ERC6909InvalidReceiver(address)");
    assert!(!t.send(2, transfer, &[w(3), w(1), w(91)]));
    t.reverted_with("ERC6909InsufficientBalance(address,uint256,uint256,uint256)");
    assert!(!t.send(0, transfer, &[w(3), w(1), w(0)]));
    t.reverted_with("ERC6909InvalidSender(address)");

    // An allowance is per id, spent down without an `Approval`, and bounded.
    assert!(!t.send(4, from, &[w(2), w(5), w(1), w(1)]));
    t.reverted_with("ERC6909InsufficientAllowance(address,uint256,uint256,uint256)");
    assert!(t.send(2, approve, &[w(4), w(1), w(30)]));
    assert_eq!(allowance(&mut t, 2, 4, 1), Word::from_u64(30));
    assert_eq!(allowance(&mut t, 2, 4, 2), Word::from_u64(0));
    assert!(!t.send(4, from, &[w(2), w(5), w(2), w(1)]));
    t.reverted_with("ERC6909InsufficientAllowance(address,uint256,uint256,uint256)");
    assert!(t.send(4, from, &[w(2), w(5), w(1), w(20)]));
    assert_eq!(topics(&t).len(), 1);
    assert_eq!(topics(&t)[0][0], transfer_topic);
    assert_eq!(allowance(&mut t, 2, 4, 1), Word::from_u64(10));
    assert_eq!(bal(&mut t, 5, 1), Word::from_u64(20));
    assert!(!t.send(4, from, &[w(2), w(5), w(1), w(11)]));
    t.reverted_with("ERC6909InsufficientAllowance(address,uint256,uint256,uint256)");
    // The allowance is checked before the receiver.
    assert!(!t.send(4, from, &[w(2), w(0), w(1), w(11)]));
    t.reverted_with("ERC6909InsufficientAllowance(address,uint256,uint256,uint256)");
    assert!(!t.send(4, from, &[w(2), w(0), w(1), w(1)]));
    t.reverted_with("ERC6909InvalidReceiver(address)");
    assert!(!t.send(2, approve, &[w(0), w(1), w(1)]));
    t.reverted_with("ERC6909InvalidSpender(address)");
    assert!(!t.send(0, approve, &[w(4), w(1), w(1)]));
    t.reverted_with("ERC6909InvalidApprover(address)");

    // `Uint.max` is never spent.
    assert!(t.send(2, approve, &[w(6), w(2), Arg::W(Word::from_u64(0).not())]));
    assert!(t.send(6, from, &[w(2), w(6), w(2), w(5)]));
    assert_eq!(allowance(&mut t, 2, 6, 2), Word::from_u64(0).not());

    // The owner itself needs no allowance, and an operator spends none.
    assert!(t.send(2, from, &[w(2), w(3), w(2), w(5)]));
    assert!(t.send(2, operator, &[w(7), w(1)]));
    assert_eq!(
        t.word("isOperator(address,address)", &[w(2), w(7)]),
        Word::from_u64(1)
    );
    assert!(t.send(2, approve, &[w(7), w(1), w(3)]));
    assert!(t.send(7, from, &[w(2), w(7), w(1), w(50)]));
    assert_eq!(allowance(&mut t, 2, 7, 1), Word::from_u64(3));
    assert_eq!(bal(&mut t, 7, 1), Word::from_u64(50));
    assert!(!t.send(7, from, &[w(2), w(7), w(1), w(21)]));
    t.reverted_with("ERC6909InsufficientBalance(address,uint256,uint256,uint256)");
    assert!(!t.send(2, operator, &[w(0), w(1)]));
    t.reverted_with("ERC6909InvalidSpender(address)");
    assert!(t.send(2, operator, &[w(7), w(0)]));
    assert!(!t.send(7, from, &[w(2), w(7), w(1), w(4)]));
    t.reverted_with("ERC6909InsufficientAllowance(address,uint256,uint256,uint256)");

    // Supply follows mints and burns, not transfers.
    assert_eq!(t.word("totalSupply(uint256)", &[w(1)]), Word::from_u64(100));
    assert!(!t.send(4, burn, &[w(3), w(1), w(1)]));
    t.reverted_with("ERC6909InsufficientAllowance(address,uint256,uint256,uint256)");
    assert!(t.send(3, burn, &[w(3), w(1), w(10)]));
    assert!(!t.send(3, burn, &[w(3), w(1), w(1)]));
    t.reverted_with("ERC6909InsufficientBalance(address,uint256,uint256,uint256)");
    assert_eq!(t.word("totalSupply(uint256)", &[w(1)]), Word::from_u64(90));
    assert_eq!(t.word("totalSupply(uint256)", &[w(2)]), Word::from_u64(50));

    // Metadata and URIs.
    let string = |s: &str| Arg::B(s.as_bytes().to_vec());
    let text = |t: &mut Session, sig: &str, args: &[Arg]| {
        assert!(t.send(0, sig, args), "{sig}: {}", pretty(&t.returned()));
        abi_string_value(&t.returned())
    };
    let describe = "describe(uint256,string,string,uint8,string)";
    assert!(!t.send(
        2,
        describe,
        &[
            w(1),
            string("Claim"),
            string("CLM"),
            w(6),
            string("ipfs://1")
        ]
    ));
    t.reverted_with("OwnableUnauthorizedAccount(address)");
    assert!(t.send(
        1,
        describe,
        &[
            w(1),
            string("Claim"),
            string("CLM"),
            w(6),
            string("ipfs://1")
        ]
    ));
    assert_eq!(text(&mut t, "name(uint256)", &[w(1)]), b"Claim");
    assert_eq!(text(&mut t, "symbol(uint256)", &[w(1)]), b"CLM");
    assert_eq!(t.word("decimals(uint256)", &[w(1)]), Word::from_u64(6));
    assert_eq!(t.word("decimals(uint256)", &[w(2)]), Word::from_u64(0));
    assert_eq!(text(&mut t, "tokenURI(uint256)", &[w(1)]), b"ipfs://1");
    assert_eq!(text(&mut t, "tokenURI(uint256)", &[w(2)]), b"");
    assert_eq!(
        text(&mut t, "contractURI()", &[]),
        b"https://claims.example/contract.json"
    );

    let id = |sel: u64| Arg::W(Word::from_u64(sel).shl(224));
    let xor = |sigs: &[&str]| {
        sigs.iter().fold(0u64, |acc, s| {
            acc ^ u64::from(u32::from_be_bytes(selector(s)))
        })
    };
    let metadata = xor(&["name(uint256)", "symbol(uint256)", "decimals(uint256)"]);
    let content = xor(&["contractURI()", "tokenURI(uint256)"]);
    let supply = xor(&["totalSupply(uint256)"]);
    for (sel, want) in [
        (0x0f632fb3, 1),
        (0x01ffc9a7, 1),
        (metadata, 1),
        (content, 1),
        (supply, 1),
        (0xd9b67a26, 0),
        (0xffffffff, 0),
    ] {
        assert_eq!(
            t.word("supportsInterface(bytes4)", &[id(sel)]),
            Word::from_u64(want),
            "{sel:08x}"
        );
    }
}

/// `std/token`'s ERC-721 extensions together: enumerations through mints, transfers, and
/// burns, a URI per token under a base, royalties, the pause, and ERC-165 for all of them.
#[test]
fn stdlib_collectible() {
    let mut n = Session::new("examples/stdlib/collectible.lithe");
    trait Low {
        fn low(self) -> u64;
    }
    impl Low for Word {
        fn low(self) -> u64 {
            u64::from_be_bytes(self.to_be_bytes()[24..].try_into().unwrap())
        }
    }
    let string = |s: &str| Arg::B(s.as_bytes().to_vec());
    let text = |n: &mut Session, sig: &str, args: &[Arg]| {
        assert!(n.send(0, sig, args), "{sig}: {}", pretty(&n.returned()));
        abi_string_value(&n.returned())
    };
    assert!(!n.send(2, "safeMint(address,string)", &[w(2), string("x.json")]));
    n.reverted_with("OwnableUnauthorizedAccount(address)");
    for (to, uri) in [
        (2, "zero.json"),
        (3, ""),
        (2, "two.json"),
        (2, "three.json"),
    ] {
        assert!(n.send(1, "safeMint(address,string)", &[w(to), string(uri)]));
    }
    assert_eq!(load_bytes(&n.returned(), 0), Word::from_u64(3));
    assert_eq!(
        text(&mut n, "tokenURI(uint256)", &[w(0)]),
        b"ipfs://lithe-collectibles/zero.json"
    );
    assert_eq!(
        text(&mut n, "tokenURI(uint256)", &[w(1)]),
        b"ipfs://lithe-collectibles/1"
    );
    assert!(!n.send(0, "tokenURI(uint256)", &[w(9)]));
    n.reverted_with("ERC721NonexistentToken(uint256)");
    assert_eq!(n.word("totalSupply()", &[]), Word::from_u64(4));
    let owned = |n: &mut Session, who: u64| -> Vec<u64> {
        let count = n.word("balanceOf(address)", &[w(who)]).low();
        (0..count)
            .map(|i| {
                n.word("tokenOfOwnerByIndex(address,uint256)", &[w(who), w(i)])
                    .low()
            })
            .collect()
    };
    assert_eq!(owned(&mut n, 2), [0, 2, 3]);
    // The owner's last token takes the place of the one that leaves.
    assert!(n.send(
        2,
        "transferFrom(address,address,uint256)",
        &[w(2), w(3), w(0)]
    ));
    assert_eq!(owned(&mut n, 2), [3, 2]);
    assert_eq!(owned(&mut n, 3), [1, 0]);
    assert!(!n.send(0, "tokenOfOwnerByIndex(address,uint256)", &[w(3), w(2)]));
    n.reverted_with("ERC721OutOfBoundsIndex(address,uint256)");
    assert!(n.send(3, "burn(uint256)", &[w(1)]));
    let all: Vec<u64> = (0..3)
        .map(|i| n.word("tokenByIndex(uint256)", &[w(i)]).low())
        .collect();
    assert_eq!(all, [0, 3, 2]);
    assert!(!n.send(0, "tokenByIndex(uint256)", &[w(3)]));
    n.reverted_with("ERC721OutOfBoundsIndex(address,uint256)");
    // Royalties: the creator's default, then a token's own.
    let royalty = |n: &mut Session, id: u64| {
        assert!(n.send(0, "royaltyInfo(uint256,uint256)", &[w(id), w(10_000)]));
        (
            load_bytes(&n.returned(), 0).low(),
            load_bytes(&n.returned(), 32).low(),
        )
    };
    assert_eq!(royalty(&mut n, 2), (1, 500));
    assert!(n.send(
        1,
        "setTokenRoyalty(uint256,address,uint96)",
        &[w(2), w(9), w(1000)]
    ));
    assert_eq!(royalty(&mut n, 2), (9, 1000));
    assert!(!n.send(
        1,
        "setTokenRoyalty(uint256,address,uint96)",
        &[w(2), w(9), w(10_001)]
    ));
    n.reverted_with("ERC2981InvalidTokenRoyalty(uint256,uint256,uint256)");
    assert!(n.send(1, "resetTokenRoyalty(uint256)", &[w(2)]));
    assert_eq!(royalty(&mut n, 2), (1, 500));
    // The pause stops transfers, mints, and burns.
    assert!(n.send(1, "pause()", &[]));
    assert!(!n.send(
        2,
        "transferFrom(address,address,uint256)",
        &[w(2), w(3), w(2)]
    ));
    n.reverted_with("EnforcedPause()");
    assert!(!n.send(1, "safeMint(address,string)", &[w(2), string("")]));
    n.reverted_with("EnforcedPause()");
    assert!(n.send(1, "unpause()", &[]));
    assert!(n.send(
        2,
        "transferFrom(address,address,uint256)",
        &[w(2), w(3), w(2)]
    ));
    // A `bytes4` argument sits in the high bytes of its word.
    let id = |sel: u64| Arg::W(Word::from_u64(sel).shl(224));
    for (sel, want) in [
        (0x80ac58cd, 1),
        (0x5b5e139f, 1),
        (0x780e9d63, 1),
        (0x2a55205a, 1),
        (0x49064906, 1),
        (0x01ffc9a7, 1),
        (0xffffffff, 0),
    ] {
        assert_eq!(
            n.word("supportsInterface(bytes4)", &[id(sel)]),
            Word::from_u64(want),
            "{sel:#x}"
        );
    }
}

/// examples/uniswap_v2: the factory creates a pair where `pairFor` says it will be, and
/// the pair knows its tokens.
#[test]
fn uniswap_v2_example_creates_pairs() {
    let w = Word::from_u64;
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut init = compile_file(&root.join("examples/uniswap_v2/factory.lithe")).expect("factory");
    init.extend_from_slice(&w(1).to_be_bytes());
    let made = construct(&init, w(1), w(0)).expect("construct");
    assert!(!made.reverted, "{}", pretty(&made.returndata));
    let (runtime, mut storage) = (made.returndata, made.storage);
    let mut run = |sig: &str, args: &[Word], keep: bool| {
        let out = exec(
            &runtime,
            &word_data(sig, args),
            storage.clone(),
            w(1),
            w(0),
            w(0),
        )
        .expect(sig);
        if keep && !out.reverted {
            storage = out.storage.clone();
        }
        out
    };
    let (a, b) = (w(0x2222), w(0x1111));
    let predicted = load_bytes(
        &run("pairFor(address,address)", &[a, b], false).returndata,
        0,
    );
    let created = run("createPair(address,address)", &[a, b], true);
    assert!(!created.reverted, "{}", pretty(&created.returndata));
    assert_eq!(load_bytes(&created.returndata, 0), predicted);
    assert_eq!(
        load_bytes(
            &run("getPair(address,address)", &[b, a], false).returndata,
            0
        ),
        predicted
    );
    assert_eq!(
        load_bytes(&run("allPairsLength()", &[], false).returndata, 0),
        w(1)
    );
    let (code, pair) = DEPLOYED
        .with(|d| d.borrow().get(&predicted).cloned())
        .expect("pair");
    for (sig, want) in [("token0()", b), ("token1()", a), ("factory()", w(0x1000))] {
        let out = exec(&code, &word_data(sig, &[]), pair.clone(), w(1), w(0), w(0)).expect(sig);
        assert_eq!(load_bytes(&out.returndata, 0), want, "{sig}");
    }
    for (args, err) in [
        ([a, b], "PairExists()"),
        ([a, a], "IdenticalAddresses()"),
        ([a, w(0)], "ZeroAddress()"),
    ] {
        let out = run("createPair(address,address)", &args, false);
        assert!(out.reverted);
        assert_eq!(out.returndata, selector(err), "{err}");
    }
}

fn base64_reference(data: &[u8], file_safe: bool, no_padding: bool) -> Vec<u8> {
    let mut alphabet = *b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    if file_safe {
        alphabet[62] = b'-';
        alphabet[63] = b'_';
    }
    let mut out = Vec::new();
    for chunk in data.chunks(3) {
        let mut b = [0u8; 3];
        b[..chunk.len()].copy_from_slice(chunk);
        let n = u32::from(b[0]) << 16 | u32::from(b[1]) << 8 | u32::from(b[2]);
        for k in 0..4 {
            if k <= chunk.len() {
                out.push(alphabet[(n >> (18 - 6 * k) & 63) as usize]);
            } else if !no_padding {
                out.push(b'=');
            }
        }
    }
    out
}

/// `Base64` matches RFC 4648 at every length around the word boundaries,
/// in both alphabets, and its short results are ordinary short values.
#[test]
fn base64_encodes_and_decodes() {
    let src = r#"import "std/base64"; import "std/crypto"; import "std/string"; import "std/bytes";
contract T is {
  storage is record {
    last : string;
  }

  external pure function enc(const data : bytes; const fileSafe : bool; const noPadding : bool) : string is
    Base64.encodeWith(data, fileSafe, noPadding)

  external pure function dec(const data : string) : bytes is
    Base64.decode(data)

  external pure function same(const data : bytes) : bool is
    Crypto.keccak256(Base64.decode(Base64.encode(data))) = Crypto.keccak256(data)
    and Crypto.keccak256(Base64.encode(data)) = Crypto.keccak256(Base64.encodeWith(data, false, false))

  external pure function text(const s : string) : string is
    Base64.encodeUrl(s)

  external pure function escaped(const data : string) : bytes is {
    const html : string := String.escapeHtml(data);
  } with Bytes.concat(Base64.decode(data), bytes(html))

  external function keep(const data : bytes) is {
    storage.last := Base64.encode(data);
  }

  external view function last() : string is
    storage.last
}
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let with_flags = |sig: &str, data: &[u8], a: bool, b: bool| {
        let mut c = selector(sig).to_vec();
        for word in [96, u64::from(a), u64::from(b), data.len() as u64] {
            c.extend_from_slice(&Word::from_u64(word).to_be_bytes());
        }
        c.extend_from_slice(data);
        c.resize(c.len() + (32 - data.len() % 32) % 32, 0);
        c
    };
    let run = |calldata: &[u8]| {
        let out = exec(
            &runtime,
            calldata,
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect("exec");
        assert!(!out.reverted, "{}", pretty(&out.returndata));
        out
    };
    // A contract whose encodings all use one set of literal options gets a routine made
    // for them.
    let sets = [(false, false), (false, true), (true, false), (true, true)];
    let fixed: Vec<Vec<u8>> = sets
        .iter()
        .map(|(a, b)| {
            let src = format!(
                "import \"std/base64\";\ncontract F is {{\n  storage is record {{}}\n  external pure function f(const data : bytes) : string is\n    Base64.encodeWith(data, {a}, {b})\n}}\n"
            );
            deploy(&compile(&src).expect("compile")).expect("deploy")
        })
        .collect();
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    for len in 0..70 {
        let data: Vec<u8> = (0..len)
            .map(|_| {
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                seed as u8
            })
            .collect();
        for (file_safe, no_padding) in [(false, false), (false, true), (true, false), (true, true)]
        {
            let want = base64_reference(&data, file_safe, no_padding);
            let out = run(&with_flags(
                "enc(bytes,bool,bool)",
                &data,
                file_safe,
                no_padding,
            ));
            assert_eq!(
                abi_string_value(&out.returndata),
                want,
                "len {len} {file_safe} {no_padding}"
            );
            let back = run(&abi_string("dec(string)", &want));
            assert_eq!(abi_string_value(&back.returndata), data, "decode len {len}");
        }
        for (fixed, &(file_safe, no_padding)) in fixed.iter().zip(&sets) {
            let out = call_raw(fixed, &abi_string("f(bytes)", &data));
            assert!(!out.reverted);
            assert_eq!(
                abi_string_value(&out.returndata),
                base64_reference(&data, file_safe, no_padding),
                "fixed len {len} {file_safe} {no_padding}"
            );
        }
        let same = run(&abi_string("same(bytes)", &data));
        assert_eq!(
            load_bytes(&same.returndata, 0),
            Word::from_u64(1),
            "len {len}"
        );
        let kept = run(&abi_string("keep(bytes)", &data));
        let last = exec(
            &runtime,
            &selector("last()"),
            kept.storage,
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect("last");
        assert_eq!(
            abi_string_value(&last.returndata),
            base64_reference(&data, false, false)
        );
    }
    let out = run(&abi_string("text(string)", b"lithe?>"));
    assert_eq!(abi_string_value(&out.returndata), b"bGl0aGU_Pg");
    // Every character decodes as Solady's table has it, with zero bits where its stores
    // leave it undefined and bytes from 0x80 as their low seven bits, whatever the escape
    // tables left.
    let mut table = [0u8; 128];
    for (at, word) in [
        (0x1a, &b"\xf8\xfc\xf8\x00\xfc\xd0\xd4\xd8\xdc\xe0\xe4\xe8\xec\xf0\xf4"[..]),
        (0x3b, &b"\x04\x08\x0c\x10\x14\x18\x1c\x20\x24\x28\x2c\x30\x34\x38\x3c\x40\x44\x48\x4c\x50\x54\x58\x5c\x60\x64"[..]),
        (0x5b, &b"\xfc\x00\x00\x00\xfc\x00\x68\x6c\x70\x74\x78\x7c\x80\x84\x88\x8c\x90\x94\x98\x9c\xa0\xa4\xa8\xac\xb0\xb4\xb8\xbc\xc0\xc4\xc8\xcc"[..]),
    ] {
        let end = at + 32;
        table[end - word.len()..end].copy_from_slice(word);
    }
    for c in 0..=255u8 {
        let v = u32::from(table[usize::from(c & 0x7f)] >> 2);
        let n = v << 18 | v << 12 | v << 6 | v;
        let want = [(n >> 16) as u8, (n >> 8) as u8, n as u8];
        for sig in ["dec(string)", "escaped(string)"] {
            let out = run(&abi_string(sig, &[c; 4]));
            // `====` is padded down to one byte.
            let n = if c == b'=' { 1 } else { 3 };
            let got = abi_string_value(&out.returndata);
            assert_eq!(got[..n], want[..n], "{sig} {c:#x}");
            assert!(sig != "dec(string)" || got.len() == n);
        }
    }
}

/// `String.escapeJson` and `escapeHtml` with Solady's vectors and every byte,
/// `String.replace` against a naive replace, and `Bytes.join` / `String.join` of lists
/// built every way.
#[test]
fn string_escape_replace_and_join() {
    let src = r#"import "std/string"; import "std/bytes"; import "std/base64"; import "std/list";
type Blob is bytes;
storage is record { last : string; names : list(string); }

external pure function json(const s : string) : string is String.escapeJson(s)

external function add(const s : string) is {
  List.push(storage.names, s);
}

external view function names() : string is String.join(storage.names)
external pure function html(const s : string) : string is String.escapeHtml(s)

(* A slice escaped where it lies, quoted or not. *)
external pure function part(const s : bytes; const from : uint; const to : uint; const quoted : bool) : string is
  String.escapeJson(string(s[from:to]), quoted)

external pure function tail(const s : string; const from : uint) : string is
  String.concat(String.escapeJson(string(bytes(s)[from:]), true), "|", String.escapeHtml(bytes(s)[from:]))

(* Every helper that uses the table space at address 0, in one expression. *)
external pure function mixed(const s : bytes) : string is
  String.concat(String.escapeJson(string(s)), "|", Base64.encode(s), "|", String.escapeHtml(string(s)), "|", string(Base64.decode(Base64.encode(s))))

external function keep(const s : string) is {
  storage.last := String.escapeJson(s);
}

external view function kept() : string is storage.last

external pure function replace(const s : string; const n : string; const r : string) : string is String.replace(s, n, r)

external pure function join(const xs : list(string)) : string is String.join(xs)

(* `s` cut every `step` bytes, then joined back with `sep` after each piece. *)
external pure function rejoin(const s : bytes; const step : uint; const sep : bytes) : bytes is {
  var parts : list(Blob) := [];
  var pos : uint := 0;
  for _ : uint in 0 .. s.length + 1 until pos >= s.length do {
    const stop : uint := if pos + step > s.length then s.length else pos + step;
    List.push(parts, Blob(s[pos:stop]));
    List.push(parts, Blob(sep));
    pos := stop;
  }
} with Bytes.join(parts)

external pure function literal() : string is String.join(["a", "", "bc", String.escapeJson("\"")])
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let call = |sig: &str, args: &[Arg]| {
        let out = exec(
            &runtime,
            &encode_args(sig, args),
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect("exec");
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        abi_string_value(&out.returndata)
    };
    let run = |f: &str, s: &[u8]| call(&format!("{f}(string)"), &[Arg::B(s.to_vec())]);
    for (s, want) in [
        (&b""[..], &b""[..]),
        (b"abc", b"abc"),
        (b"abc\"_123", b"abc\\\"_123"),
        (b"abc\\_123", b"abc\\\\_123"),
        (b"abc\x08_123", b"abc\\b_123"),
        (b"abc\x0c_123", b"abc\\f_123"),
        (b"abc\n_123", b"abc\\n_123"),
        (b"abc\r_123", b"abc\\r_123"),
        (b"abc\t_123", b"abc\\t_123"),
        (b"\x00\x01\x1f\x7f", b"\\u0000\\u0001\\u001f\x7f"),
    ] {
        assert_eq!(run("json", s), want, "{s:?}");
    }
    for (s, want) in [
        (&b""[..], &b""[..]),
        (b"abc", b"abc"),
        (b"abc\"_123", b"abc&quot;_123"),
        (b"abc&_123", b"abc&amp;_123"),
        (b"abc'_123", b"abc&#39;_123"),
        (b"abc<_123", b"abc&lt;_123"),
        (b"abc>_123", b"abc&gt;_123"),
    ] {
        assert_eq!(run("html", s), want, "{s:?}");
    }
    // Every byte, ASCII and not, over lengths around a word.
    let all: Vec<u8> = (0..=255u8).collect();
    for len in [1, 31, 32, 33, 64, 100, 256] {
        let s: Vec<u8> = all
            .iter()
            .cycle()
            .skip(len * 7)
            .take(len)
            .copied()
            .collect();
        let mut json = Vec::new();
        let mut html = Vec::new();
        for &b in &s {
            match b {
                b'"' | b'\\' => json.extend([b'\\', b]),
                8 => json.extend(b"\\b"),
                9 => json.extend(b"\\t"),
                10 => json.extend(b"\\n"),
                12 => json.extend(b"\\f"),
                13 => json.extend(b"\\r"),
                0..=0x1f => json.extend(format!("\\u{b:04x}").as_bytes()),
                _ => json.push(b),
            }
            match b {
                b'"' => html.extend(b"&quot;"),
                b'&' => html.extend(b"&amp;"),
                b'\'' => html.extend(b"&#39;"),
                b'<' => html.extend(b"&lt;"),
                b'>' => html.extend(b"&gt;"),
                _ => html.push(b),
            }
        }
        assert_eq!(run("json", &s), json, "{len}");
        assert_eq!(run("html", &s), html, "{len}");
    }
    // Clean runs, whole words of them copied at once, around one byte that needs escaping.
    for len in 0..100usize {
        for at in [0, 1, 31, 32, 33, 63, 64, len.saturating_sub(1)] {
            for c in [b'"', b'\\', b'\n', 0x1f, b'&', b'<', 0x7f, 0x80] {
                let mut s: Vec<u8> = (0..len).map(|i| b'a' + (i % 26) as u8).collect();
                if at < len {
                    s[at] = c;
                }
                let (mut json, mut html) = (s.clone(), s.clone());
                if at < len {
                    let j: &[u8] = match c {
                        b'"' => b"\\\"",
                        b'\\' => b"\\\\",
                        b'\n' => b"\\n",
                        0x1f => b"\\u001f",
                        _ => &[c],
                    };
                    let h: &[u8] = match c {
                        b'"' => b"&quot;",
                        b'&' => b"&amp;",
                        b'<' => b"&lt;",
                        _ => &[c],
                    };
                    json.splice(at..=at, j.iter().copied());
                    html.splice(at..=at, h.iter().copied());
                }
                assert_eq!(run("json", &s), json, "{len} {at} {c}");
                assert_eq!(run("html", &s), html, "{len} {at} {c}");
            }
        }
    }
    let quote = |s: &[u8]| [&b"\""[..], &run("json", s), b"\""].concat();
    for len in [0usize, 5, 40, 70] {
        let s: Vec<u8> = (0..len).map(|i| b"ab\"\n<c"[i % 6]).collect();
        for (from, to) in [
            (0, len),
            (1, len),
            (0, len / 2),
            (len / 3, len / 3 + 32),
            (len, len),
        ] {
            if to > len || from > to {
                continue;
            }
            for quoted in [false, true] {
                let args = [
                    Arg::B(s.clone()),
                    Arg::W(Word::from_u64(from as u64)),
                    Arg::W(Word::from_u64(to as u64)),
                    Arg::W(Word::from_u64(u64::from(quoted))),
                ];
                let want = if quoted {
                    quote(&s[from..to])
                } else {
                    run("json", &s[from..to])
                };
                assert_eq!(
                    call("part(bytes,uint256,uint256,bool)", &args),
                    want,
                    "{len} {from} {to}"
                );
            }
        }
        let from = len / 2;
        let want = [quote(&s[from..]), b"|".to_vec(), run("html", &s[from..])].concat();
        assert_eq!(
            call(
                "tail(string,uint256)",
                &[Arg::B(s.clone()), Arg::W(Word::from_u64(from as u64))]
            ),
            want
        );
    }
    // Out of range, a slice still panics as it does anywhere.
    for (from, to) in [(3u64, 2u64), (0, 6)] {
        let out = exec(
            &runtime,
            &encode_args(
                "part(bytes,uint256,uint256,bool)",
                &[
                    Arg::B(b"abcde".to_vec()),
                    Arg::W(Word::from_u64(from)),
                    Arg::W(Word::from_u64(to)),
                    Arg::W(Word::from_u64(1)),
                ],
            ),
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect("exec");
        assert!(out.reverted);
        assert_eq!(out.returndata[..4], selector("Panic(uint256)"));
        assert_eq!(load_bytes(&out.returndata, 4), Word::from_u64(0x32));
    }
    assert_eq!(
        call("mixed(bytes)", &[Arg::B(b"<\"a\">\n".to_vec())]),
        b"<\\\"a\\\">\\n|PCJhIj4K|&lt;&quot;a&quot;&gt;\n|<\"a\">\n".to_vec()
    );
    let mut d = Session {
        runtime: runtime.clone(),
        storage: HashMap::new(),
        last: None,
    };
    assert!(d.send(1, "keep(string)", &[Arg::B(b"say \"hi\"".repeat(5))]));
    d.send(1, "kept()", &[]);
    assert_eq!(abi_string_value(&d.returned()), b"say \\\"hi\\\"".repeat(5));
    for name in [&b"ann"[..], b"", &[b'z'; 40]] {
        assert!(d.send(1, "add(string)", &[Arg::B(name.to_vec())]));
    }
    d.send(1, "names()", &[]);
    assert_eq!(
        abi_string_value(&d.returned()),
        [&b"ann"[..], &[b'z'; 40]].concat()
    );

    fn next(seed: &mut u64) -> u64 {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        *seed
    }
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    for round in 0..300 {
        let len = (next(&mut seed) % 80) as usize;
        let subject: Vec<u8> = (0..len)
            .map(|_| b"ab"[(next(&mut seed) % 2) as usize])
            .collect();
        let n = match round % 4 {
            0 => (next(&mut seed) % 4) as usize,
            1 => (next(&mut seed) % 40) as usize,
            _ => 30 + (next(&mut seed) % 5) as usize,
        };
        let needle: Vec<u8> = if n <= len && round % 3 > 0 {
            let at = (next(&mut seed) % (len - n + 1) as u64) as usize;
            subject[at..at + n].to_vec()
        } else {
            (0..n)
                .map(|_| b"ab"[(next(&mut seed) % 2) as usize])
                .collect()
        };
        let replacement: Vec<u8> = (0..next(&mut seed) % 40)
            .map(|k| b'x' + (k % 3) as u8)
            .collect();
        let mut expect = Vec::new();
        if needle.is_empty() {
            for &c in &subject {
                expect.extend(&replacement);
                expect.push(c);
            }
            expect.extend(&replacement);
        } else {
            let mut i = 0;
            while i < subject.len() {
                if subject[i..].starts_with(&needle) {
                    expect.extend(&replacement);
                    i += needle.len();
                } else {
                    expect.push(subject[i]);
                    i += 1;
                }
            }
        }
        let got = call(
            "replace(string,string,string)",
            &[Arg::B(subject.clone()), Arg::B(needle), Arg::B(replacement)],
        );
        assert_eq!(
            got,
            expect,
            "replace {:?}",
            String::from_utf8_lossy(&subject)
        );
    }
    assert_eq!(run("json", b""), b"");

    // A `string[]` argument, then lists pushed in a loop and written as a literal.
    let strings = |xs: &[&[u8]]| {
        let mut c = selector("join(string[])").to_vec();
        let mut heads = Vec::new();
        let mut tails = Vec::new();
        for x in xs {
            heads.extend_from_slice(
                &Word::from_u64((32 * xs.len() + tails.len()) as u64).to_be_bytes(),
            );
            tails.extend_from_slice(&Word::from_u64(x.len() as u64).to_be_bytes());
            tails.extend_from_slice(x);
            tails.resize(tails.len().div_ceil(32) * 32, 0);
        }
        c.extend_from_slice(&Word::from_u64(32).to_be_bytes());
        c.extend_from_slice(&Word::from_u64(xs.len() as u64).to_be_bytes());
        c.extend(heads);
        c.extend(tails);
        c
    };
    let long = [b'z'; 70];
    for xs in [
        &[][..],
        &[&b""[..]],
        &[b"a", b"", b"bcd"],
        &[&long[..], b"q", &long[..]],
    ] {
        let out = exec(
            &runtime,
            &strings(xs),
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect("exec");
        assert!(!out.reverted);
        assert_eq!(abi_string_value(&out.returndata), xs.concat());
    }
    for len in [0usize, 1, 31, 33, 100] {
        let s: Vec<u8> = (0..len).map(|i| b'a' + (i % 26) as u8).collect();
        for step in [1usize, 5, 32, 40] {
            let got = call(
                "rejoin(bytes,uint256,bytes)",
                &[
                    Arg::B(s.clone()),
                    Arg::W(Word::from_u64(step as u64)),
                    Arg::B(b",".to_vec()),
                ],
            );
            let want: Vec<u8> = s.chunks(step).flat_map(|c| [c, b","].concat()).collect();
            assert_eq!(got, want, "{len} {step}");
        }
    }
    assert_eq!(call("literal()", &[]), b"abc\\\"");
}

/// `std/utils`: ERC-1167 clones that delegate to a real implementation, clone arguments,
/// SSTORE2 data, and CREATE3 addresses.
#[test]
fn stdlib_deployers() {
    let unhex = |h: &str| {
        (0..h.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&h[i..i + 2], 16).unwrap())
            .collect::<Vec<u8>>()
    };
    let this = Word::from_u64(0x1000);
    let counter = "\
storage is record { n : uint; }
external function bump() is { storage.n := storage.n + 1; }
";
    let implementation = Word::from_u64(0x5301);
    let code = deploy(&compile(counter).expect("compile")).expect("deploy");
    DEPLOYED.with(|d| {
        d.borrow_mut()
            .insert(implementation, (code, HashMap::new()))
    });
    let mut d = Session::new("examples/stdlib/deployers.lithe");
    let clone_code = |args: &[u8]| {
        let mut code = unhex("363d3d373d3d3d363d73");
        code.extend(&implementation.to_be_bytes()[12..]);
        code.extend(unhex("5af43d82803e903d91602b57fd5bf3"));
        code.extend(args);
        code
    };

    // A clone runs the implementation's code on its own storage.
    assert!(d.send(1, "clone(address)", &[Arg::W(implementation)]));
    let instance = slot(&d.storage, 0);
    let (code, _) = DEPLOYED.with(|m| m.borrow()[&instance].clone());
    assert_eq!(code, clone_code(&[]));
    let bumped = exec(
        &code,
        &selector("bump()"),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("bump");
    assert!(!bumped.reverted, "{}", pretty(&bumped.returndata));
    assert_eq!(slot(&bumped.storage, 0), Word::from_u64(1));
    assert!(d.word("argsOf(address)", &[Arg::W(instance)]) == Word::from_u64(32));
    assert!(abi_string_value(&d.returned()).is_empty());

    // With a salt, the clone lands where `predictClone` says.
    let salt = Word::from_u64(0x5a17);
    let predicted = d.word(
        "predictClone(address,bytes32)",
        &[Arg::W(implementation), Arg::W(salt)],
    );
    let mut init = unhex("3d602d80600a3d3981f3");
    init.extend(clone_code(&[]));
    assert_eq!(predicted, created_address(this, Some(salt), &init));
    assert_eq!(
        d.word(
            "cloneDeterministic(address,bytes32)",
            &[Arg::W(implementation), Arg::W(salt)]
        ),
        predicted
    );
    assert_eq!(slot(&d.storage, 0), predicted);

    // Arguments ride after the clone's code.
    let args = b"immutable arguments, read back with EXTCODECOPY".to_vec();
    assert!(d.send(
        1,
        "cloneWithArgs(address,bytes)",
        &[Arg::W(implementation), Arg::B(args.clone())]
    ));
    let instance = slot(&d.storage, 0);
    assert_eq!(
        DEPLOYED.with(|m| m.borrow()[&instance].0.clone()),
        clone_code(&args)
    );
    d.word("argsOf(address)", &[Arg::W(instance)]);
    assert_eq!(abi_string_value(&d.returned()), args);
    assert!(!d.send(
        1,
        "cloneWithArgs(address,bytes)",
        &[Arg::W(implementation), Arg::B(vec![7; 24532])]
    ));
    d.reverted_with("CloneArgumentsTooLong()");

    // SSTORE2: data written as code reads back whole.
    let data = b"data kept as the code of a contract that stops at once".to_vec();
    assert!(d.send(1, "write(bytes)", &[Arg::B(data.clone())]));
    d.word("read()", &[]);
    assert_eq!(abi_string_value(&d.returned()), data);
    let pointer = d.word(
        "writeCounterfactual(bytes,bytes32)",
        &[Arg::B(data[..9].to_vec()), Arg::W(salt)],
    );
    let mut init = unhex("61000a80600a3d393df300");
    init.extend(&data[..9]);
    assert_eq!(pointer, created_address(this, Some(salt), &init));
    d.word("read()", &[]);
    assert_eq!(abi_string_value(&d.returned()), data[..9].to_vec());

    // CREATE3: the proxy's address, then its first creation's, from the salt alone.
    let proxy = created_address(this, Some(salt), &unhex("67363d3d37363d34f03d5260086018f3"));
    let mut rlp = vec![0xd6, 0x94];
    rlp.extend(&proxy.to_be_bytes()[12..]);
    rlp.push(0x01);
    let mut deployed = [0u8; 32];
    deployed[12..].copy_from_slice(&crate::keccak::keccak256(&rlp)[12..]);
    assert_eq!(
        d.word("predict3(bytes32)", &[Arg::W(salt)]),
        Word::from_be_bytes(deployed)
    );
    assert_eq!(
        Word::from_be_bytes(crate::keccak::keccak256(&unhex(
            "67363d3d37363d34f03d5260086018f3"
        ))),
        Word::from_hex("21c35dbe1b344a2488cf3321d6ce542f8e9f305544ff09e4993a62319a497c1f").unwrap()
    );
    // This interpreter's `CREATE` does not land at the nonce's address, so the check
    // that the contract exists fails, as it does when its creation code reverts.
    assert!(!d.send(
        1,
        "deploy3(bytes,bytes32)",
        &[Arg::B(unhex("6001600c60003960016000f3fe")), Arg::W(salt)]
    ));
    d.reverted_with("FailedDeployment()");
    let calls = &d.last.as_ref().unwrap().detail;
    assert!(
        calls
            .iter()
            .any(|c| c.contains("6001600c60003960016000f3fe")),
        "{calls:?}"
    );
}

/// The salted deployers take a value or not: without one, they send none.
#[test]
fn stdlib_deployers_with_and_without_value() {
    let src = "\
import \"std/evm\"; import \"std/utils/create2\";
import \"std/utils/clones\";
import \"std/utils/create3\";

contract Funded is {
  use Create2;
  use Clones;
  use Create3;

  storage is record { last : address; }

  external function plain(const target : address; const salt : bytes32) : address raises FailedDeployment is {
    storage.last := Clones.cloneDeterministic(target, salt);
  } with storage.last

  external payable function funded(const target : address; const salt : bytes32) : address raises FailedDeployment is {
    storage.last := Clones.cloneDeterministic(target, salt, uint(Evm.value()));
  } with storage.last

  external payable function fundedWithArgs(const target : address; const args : bytes; const salt : bytes32) : address
    raises CloneArgumentsTooLong | FailedDeployment
  is {
    storage.last := Clones.cloneDeterministicWithArgs(target, args, salt, uint(Evm.value()));
  } with storage.last

  external function plainWithArgs(const target : address; const args : bytes; const salt : bytes32) : address
    raises CloneArgumentsTooLong | FailedDeployment
  is {
    storage.last := Clones.cloneDeterministicWithArgs(target, args, salt);
  } with storage.last

  external function deploy3(const code : bytes; const salt : bytes32) : address raises FailedDeployment is {
    storage.last := Create3.deployDeterministic(code, salt);
  } with storage.last
}
";
    let dir = std::env::temp_dir().join(format!("lithe-funded-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let main = dir.join("main.lithe");
    std::fs::write(&main, src).unwrap();
    let init = compile_file(&main).expect("compile");
    let runtime = construct(&init, Word::from_u64(1), Word::from_u64(0))
        .expect("construct")
        .returndata;
    let target = Word::from_u64(0x5501);
    let run = |sig: &str, args: &[Arg], value: u64| {
        let out = exec(
            &runtime,
            &encode_args(sig, args),
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(value),
            Word::from_u64(value),
        )
        .expect(sig);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        let made = load_bytes(&out.returndata, 0);
        let sent = out.trace.iter().find_map(|ev| match ev {
            Ev::Call { to, value } if *to == made => Some(*value),
            _ => None,
        });
        (made, sent)
    };
    let salt = || Arg::W(Word::from_u64(0x77));
    let (plain, sent) = run("plain(address,bytes32)", &[Arg::W(target), salt()], 0);
    assert_eq!(sent, Some(Word::from_u64(0)));
    let (funded, sent) = run("funded(address,bytes32)", &[Arg::W(target), salt()], 5);
    assert_eq!(sent, Some(Word::from_u64(5)));
    assert_eq!(plain, funded, "the value does not move the address");
    let args = || Arg::B(b"config".to_vec());
    let (with_args, sent) = run(
        "plainWithArgs(address,bytes,bytes32)",
        &[Arg::W(target), args(), salt()],
        0,
    );
    assert_eq!(sent, Some(Word::from_u64(0)));
    let (funded_args, sent) = run(
        "fundedWithArgs(address,bytes,bytes32)",
        &[Arg::W(target), args(), salt()],
        3,
    );
    assert_eq!(sent, Some(Word::from_u64(3)));
    assert_eq!(with_args, funded_args);
    assert_ne!(with_args, plain);
    // The proxy is created with no value, and the call to it sends none.
    let out = exec(
        &runtime,
        &encode_args("deploy3(bytes,bytes32)", &[Arg::B(vec![0x00]), salt()]),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("deploy3");
    assert!(out
        .trace
        .iter()
        .all(|ev| !matches!(ev, Ev::Call { value, .. } if !value.is_zero())));
}

/// `std/accounts`: an ERC-7821 batch executor, as the account itself calls it, and a
/// contract that authorizes with `opData` from the module's pieces.
#[test]
fn stdlib_erc7821() {
    install_mocks();
    let word = |n: u64| Word::from_u64(n).to_be_bytes().to_vec();
    let padded = |data: &[u8]| {
        let mut out = word(data.len() as u64);
        out.extend(data);
        out.resize(32 + data.len().div_ceil(32) * 32, 0);
        out
    };
    // `abi.encode(calls)`, or `abi.encode(calls, opData)`.
    let batch = |calls: &[(u64, u64, &[u8])], op_data: Option<&[u8]>| {
        let mut list = word(calls.len() as u64);
        let mut tails = Vec::new();
        for (to, value, data) in calls {
            list.extend(word(32 * calls.len() as u64 + tails.len() as u64));
            tails.extend(word(*to));
            tails.extend(word(*value));
            tails.extend(word(96));
            tails.extend(padded(data));
        }
        list.extend(tails);
        let heads = if op_data.is_some() { 64 } else { 32 };
        let mut out = word(heads);
        if op_data.is_some() {
            out.extend(word(heads + list.len() as u64));
        }
        out.extend(list);
        if let Some(op_data) = op_data {
            out.extend(padded(op_data));
        }
        out
    };
    let mode = |m: &str| {
        let mut w = [0u8; 32];
        for (i, b) in w.iter_mut().enumerate().take(m.len() / 2) {
            *b = u8::from_str_radix(&m[2 * i..2 * i + 2], 16).unwrap();
        }
        Word::from_be_bytes(w)
    };
    let batch_mode = mode("01000000000000000000");
    let op_data_mode = mode("01000000000078210001");
    let this = 0x1000;
    let run = |runtime: &[u8], m: Word, data: Vec<u8>, caller: u64, value: u64, balance: u64| {
        exec(
            runtime,
            &encode_args("execute(bytes32,bytes)", &[Arg::W(m), Arg::B(data)]),
            HashMap::new(),
            Word::from_u64(caller),
            Word::from_u64(value),
            Word::from_u64(balance),
        )
        .expect("execute")
    };
    let calls_made = |out: &Outcome| {
        out.trace
            .iter()
            .filter_map(|ev| match ev {
                Ev::Call { to, value } => Some((*to, *value)),
                _ => None,
            })
            .collect::<Vec<_>>()
    };

    let wallet = deploy(
        &compile(
            "\
import \"std/accounts/erc7821\";
import \"std/interfaces/erc7821\";
contract Wallet is {
  use ERC7821 exposing IERC7821;
  storage is record {}
  payable receive is { skip }
}
",
        )
        .expect("compile"),
    )
    .expect("deploy");

    // The calls run in order, each with its value; `Address.zero` is the account itself.
    let calls: &[(u64, u64, &[u8])] = &[
        (0xcd, 3, b"\x01\x02\x03\x04hi"),
        (0, 4, b""),
        (0x7777, 0, b""),
    ];
    let out = run(&wallet, batch_mode, batch(calls, None), this, 7, 7);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    let w = Word::from_u64;
    assert_eq!(
        calls_made(&out),
        vec![(w(0xcd), w(3)), (w(this), w(4)), (w(0x7777), w(0))]
    );
    assert!(
        out.detail[0].ends_with(&hex(b"\x01\x02\x03\x04hi")),
        "{:?}",
        out.detail
    );
    assert_eq!(out.self_balance, w(0));
    // An empty batch does nothing.
    assert!(!run(&wallet, batch_mode, batch(&[], None), this, 0, 0).reverted);
    // With `opData` in its mode, a batch from the account runs too.
    let out = run(
        &wallet,
        op_data_mode,
        batch(calls, Some(b"signature")),
        this,
        7,
        7,
    );
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(calls_made(&out).len(), 3);

    // A failed call reverts the batch with its own revert data, or none.
    let out = run(
        &wallet,
        batch_mode,
        batch(&[(0xcd, 0, b""), (0xee, 0, b"\x01\x02\x03\x04why")], None),
        this,
        0,
        0,
    );
    assert!(out.reverted);
    assert_eq!(out.returndata, b"why".to_vec());
    let out = run(
        &wallet,
        batch_mode,
        batch(&[(0xef, 0, b"")], None),
        this,
        0,
        0,
    );
    assert!(out.reverted);
    assert!(out.returndata.is_empty());
    // So does a call the account cannot pay for.
    assert!(
        run(
            &wallet,
            batch_mode,
            batch(&[(0xcd, 5, b"")], None),
            this,
            0,
            4
        )
        .reverted
    );

    // Anyone else is refused.
    let out = run(&wallet, batch_mode, batch(calls, None), 1, 0, 7);
    assert!(out.reverted);
    assert_eq!(
        out.returndata[..4],
        selector("AccountUnauthorized(address)")
    );
    assert_eq!(load_bytes(&out.returndata, 4), w(1));

    // Other modes, batches of batches among them, are unsupported.
    let supports = |m: Word| {
        let out = call_raw(
            &wallet,
            &encode_args("supportsExecutionMode(bytes32)", &[Arg::W(m)]),
        );
        assert!(!out.reverted);
        load_bytes(&out.returndata, 0) == w(1)
    };
    assert!(supports(batch_mode));
    assert!(supports(op_data_mode));
    // The reserved bytes 2 to 5 and everything past byte 9 are free.
    assert!(supports(mode("0100ffffffff78210001ffff")));
    for other in [
        "01000000000078210002",
        "00000000000000000000",
        "01010000000000000000",
        "02000000000000000000",
        "01000000000078210003",
        "01000000000000000001",
    ] {
        assert!(!supports(mode(other)), "{other}");
        let out = run(&wallet, mode(other), batch(calls, None), this, 0, 7);
        assert!(out.reverted);
        assert_eq!(
            out.returndata,
            selector("UnsupportedExecutionMode()").to_vec(),
            "{other}"
        );
    }

    // Malformed data reverts before any call.
    let mut short = batch(calls, None);
    short.truncate(short.len() - 40);
    let mut far = batch(calls, None);
    far[31] = 0xff;
    for data in [short, far, vec![0; 16], Vec::new()] {
        let out = run(&wallet, batch_mode, data, this, 0, 7);
        assert!(out.reverted);
        assert!(calls_made(&out).is_empty());
    }

    // An account that authorizes with `opData` builds `execute` from the pieces.
    let keyed = deploy(
        &compile(
            "\
import \"std/abi\"; import \"std/accounts/erc7821\"; import \"std/interfaces/erc7821\";
contract Keyed is {
  error BadOpData;
  use ERC7821 exposing {
    view function supportsExecutionMode(mode : bytes32) : bool;
  }
  storage is record {}
  external payable function execute(const mode : bytes32; const executionData : bytes)
    raises UnsupportedExecutionMode | BadOpData | forwarded
  is {
    assert(ERC7821.executionModeId(mode) = 2, UnsupportedExecutionMode);
    const calls : ERC7821Calls := Abi.decode(executionData, ERC7821Calls);
    assert(
      ERC7821.opDataOf(2, executionData) = Abi.encode(calls.length),
      BadOpData
    );
    ERC7821.executeCalls(calls);
  }
}
",
        )
        .expect("compile"),
    )
    .expect("deploy");
    let three = word(3);
    let out = run(&keyed, op_data_mode, batch(calls, Some(&three)), 1, 7, 7);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(calls_made(&out).len(), 3);
    for data in [
        batch(calls, Some(&word(2))),
        batch(calls, Some(b"")),
        batch(calls, None),
    ] {
        let out = run(&keyed, op_data_mode, data, 1, 7, 7);
        assert!(out.reverted);
        assert_eq!(
            out.returndata,
            selector("BadOpData()").to_vec(),
            "{}",
            pretty(&out.returndata)
        );
    }
    let out = run(&keyed, batch_mode, batch(calls, Some(&three)), 1, 7, 7);
    assert_eq!(
        out.returndata,
        selector("UnsupportedExecutionMode()").to_vec()
    );

    // `ERC7821Batches` adds batches of batches, `abi.encode(bytes[])`.
    let batches = |items: &[Vec<u8>]| {
        let mut heads = word(items.len() as u64);
        let mut tails = Vec::new();
        for item in items {
            heads.extend(word(32 * items.len() as u64 + tails.len() as u64));
            tails.extend(padded(item));
        }
        let mut out = word(32);
        out.extend(heads);
        out.extend(tails);
        out
    };
    let batches_mode = mode("01000000000078210002");
    let nested = deploy(
        &compile(
            "\
import \"std/accounts/erc7821\";
import \"std/interfaces/erc7821\";
contract Wallet is {
  use ERC7821;
  use ERC7821Batches exposing IERC7821Batches;
  storage is record {}
  payable receive is { skip }
}
",
        )
        .expect("compile"),
    )
    .expect("deploy");
    let second: &[(u64, u64, &[u8])] = &[(0x7777, 1, b"x"), (0xcd, 0, b"\x01\x02\x03\x04")];
    let both = batches(&[batch(calls, None), batch(second, Some(b"sig"))]);
    let out = run(&nested, batches_mode, both.clone(), this, 8, 8);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(
        calls_made(&out),
        vec![
            (w(0xcd), w(3)),
            (w(this), w(4)),
            (w(0x7777), w(0)),
            (w(0x7777), w(1)),
            (w(0xcd), w(0))
        ]
    );
    // The single modes still run, and nothing, or an empty batch, is no call.
    assert_eq!(
        calls_made(&run(&nested, batch_mode, batch(calls, None), this, 7, 7)).len(),
        3
    );
    assert_eq!(
        calls_made(&run(
            &nested,
            op_data_mode,
            batch(calls, Some(b"s")),
            this,
            7,
            7
        ))
        .len(),
        3
    );
    for data in [batches(&[]), batches(&[batch(&[], None)])] {
        let out = run(&nested, batches_mode, data, this, 0, 0);
        assert!(!out.reverted && calls_made(&out).is_empty());
    }
    let supports_in = |m: Word| {
        let out = call_raw(
            &nested,
            &encode_args("supportsExecutionMode(bytes32)", &[Arg::W(m)]),
        );
        load_bytes(&out.returndata, 0) == w(1)
    };
    assert!(supports_in(batch_mode) && supports_in(op_data_mode) && supports_in(batches_mode));
    assert!(supports_in(mode("0100ffffffff78210002ffff")));
    assert!(!supports_in(mode("01000000000078210003")));
    // Anyone else is refused.
    let out = run(&nested, batches_mode, both.clone(), 1, 0, 8);
    assert_eq!(
        out.returndata[..4],
        selector("AccountUnauthorized(address)")
    );
    // A failed call in a later batch reverts the whole with its revert data.
    let failing: &[(u64, u64, &[u8])] = &[(0xee, 0, b"\x01\x02\x03\x04no")];
    let out = run(
        &nested,
        batches_mode,
        batches(&[batch(calls, None), batch(failing, None)]),
        this,
        7,
        7,
    );
    assert!(out.reverted);
    assert_eq!(out.returndata, b"no".to_vec());
    // Malformed batches revert before any call: the outer list with Solady's error.
    let decoding = selector("BatchOfBatchesDecodingError()").to_vec();
    let at = |mut data: Vec<u8>, i: usize, v: u64| {
        data[i..i + 32].copy_from_slice(&word(v));
        data
    };
    let mut truncated = both.clone();
    truncated.truncate(both.len() - 64);
    for (k, (data, reason)) in [
        (at(both.clone(), 0, 1 << 40), Some(&decoding)),
        (vec![0; 16], Some(&decoding)),
        (at(both.clone(), 32, 1 << 20), Some(&decoding)),
        (at(both.clone(), 96, 1 << 40), Some(&decoding)),
        (at(both.clone(), 96, both.len() as u64), Some(&decoding)),
        (truncated, Some(&decoding)),
        (batches(&[batch(calls, None), word(1 << 40)]), None),
    ]
    .into_iter()
    .enumerate()
    {
        let out = run(&nested, batches_mode, data, this, 7, 7);
        assert!(out.reverted, "{k}");
        assert!(calls_made(&out).is_empty());
        if let Some(reason) = reason {
            assert_eq!(&out.returndata, reason, "{}", pretty(&out.returndata));
        }
    }

    // Each batch authorized by its own `opData`, from the pieces.
    let signed = deploy(
        &compile(
            "\
import \"std/abi\"; import \"std/accounts/erc7821\"; import \"std/interfaces/erc7821\";
contract Signed is {
  error BadOpData;
  use ERC7821;
  use ERC7821Batches exposing {
    view function supportsExecutionMode(mode : bytes32) : bool;
  }
  storage is record {}
  external payable function execute(const mode : bytes32; const executionData : bytes)
    raises UnsupportedExecutionMode | BatchOfBatchesDecodingError | BadOpData | forwarded
  is {
    const id : uint := ERC7821Batches.executionModeId(mode);
    assert(id >= 2, UnsupportedExecutionMode);
    const n : uint := if id = 3 then ERC7821Batches.batchCount(executionData) else 1;
    for i : uint in 0 .. n do {
      var start : uint := 0;
      var finish : uint := executionData.length;
      if id = 3 then {
        (start, finish) := ERC7821Batches.batch(executionData, i);
      } else { skip };
      const calls : ERC7821Calls := Abi.decode(executionData[start : finish], ERC7821Calls);
      assert(
        ERC7821Batches.opDataIn(executionData, start, finish) = Abi.encode(calls.length),
        BadOpData
      );
      ERC7821.executeCalls(calls);
    }
  }
}
",
        )
        .expect("compile"),
    )
    .expect("deploy");
    let good = batches(&[batch(calls, Some(&three)), batch(second, Some(&word(2)))]);
    let out = run(&signed, batches_mode, good, 1, 8, 8);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(calls_made(&out).len(), 5);
    let out = run(&signed, op_data_mode, batch(calls, Some(&three)), 1, 7, 7);
    assert_eq!(calls_made(&out).len(), 3);
    for data in [
        batches(&[batch(calls, Some(&three)), batch(second, Some(&three))]),
        batches(&[batch(calls, Some(&three)), batch(second, None)]),
    ] {
        let out = run(&signed, batches_mode, data, 1, 8, 8);
        assert_eq!(out.returndata, selector("BadOpData()").to_vec());
        assert!(calls_made(&out).is_empty());
    }
}

/// `std/access/ownable_roles.lithe`: role masks the owner grants and revokes, renounced by
/// their holders, and the three kinds of check.
#[test]
fn stdlib_ownable_roles() {
    let mut r = Session::new("examples/stdlib/ownable_roles.lithe");
    let minter = Word::from_u64(1);
    let pauser = Word::from_u64(1).shl(255);
    let updated = |r: &Session| -> Vec<Word> {
        let out = r.last.as_ref().unwrap();
        let logs: Vec<&Vec<Word>> = out
            .trace
            .iter()
            .filter_map(|ev| match ev {
                Ev::Log { topics } => Some(topics),
                _ => None,
            })
            .collect();
        assert_eq!(logs.len(), 1);
        assert_eq!(logs[0][0], keccak_word(b"RolesUpdated(address,uint256)"));
        logs[0][1..].to_vec()
    };

    assert!(!r.send(2, "mint(address,uint256)", &[w(5), w(3)]));
    r.reverted_with("Unauthorized()");
    assert!(!r.send(2, "grantRoles(address,uint256)", &[w(2), Arg::W(minter)]));
    r.reverted_with("OwnableUnauthorizedAccount(address)");
    assert!(r.send(1, "grantRoles(address,uint256)", &[w(2), Arg::W(minter)]));
    assert_eq!(updated(&r), vec![Word::from_u64(2), minter]);
    assert!(r.send(1, "grantRoles(address,uint256)", &[w(2), Arg::W(pauser)]));
    assert_eq!(updated(&r), vec![Word::from_u64(2), minter.bitor(pauser)]);
    assert_eq!(r.word("rolesOf(address)", &[w(2)]), minter.bitor(pauser));
    assert_eq!(
        r.word("hasAnyRole(address,uint256)", &[w(2), w(3)]),
        Word::from_u64(1)
    );
    assert_eq!(
        r.word("hasAllRoles(address,uint256)", &[w(2), w(3)]),
        Word::from_u64(0)
    );
    assert_eq!(
        r.word(
            "hasAllRoles(address,uint256)",
            &[w(2), Arg::W(minter.bitor(pauser))]
        ),
        Word::from_u64(1)
    );
    assert_eq!(
        r.word("hasAnyRole(address,uint256)", &[w(3), w(1)]),
        Word::from_u64(0)
    );

    assert!(r.send(2, "mint(address,uint256)", &[w(5), w(3)]));
    assert_eq!(r.word("minted(address)", &[w(5)]), Word::from_u64(3));

    // The owner or a pauser pauses; a pauser or minter, or the owner, unpauses.
    assert!(!r.send(3, "pause()", &[]));
    r.reverted_with("Unauthorized()");
    assert!(r.send(1, "pause()", &[]));
    assert!(r.send(2, "unpause()", &[]));
    assert!(r.send(2, "pause()", &[]));
    assert!(!r.send(3, "unpause()", &[]));
    r.reverted_with("Unauthorized()");
    assert!(r.send(1, "unpause()", &[]));
    assert_eq!(r.word("paused()", &[]), Word::from_u64(0));

    // Renouncing and revoking clear only the named bits.
    assert!(r.send(2, "renounceRoles(uint256)", &[Arg::W(minter)]));
    assert_eq!(updated(&r), vec![Word::from_u64(2), pauser]);
    assert!(!r.send(2, "mint(address,uint256)", &[w(5), w(1)]));
    r.reverted_with("Unauthorized()");
    assert!(!r.send(3, "revokeRoles(address,uint256)", &[w(2), Arg::W(pauser)]));
    r.reverted_with("OwnableUnauthorizedAccount(address)");
    assert!(r.send(1, "revokeRoles(address,uint256)", &[w(2), Arg::W(pauser)]));
    assert_eq!(r.word("rolesOf(address)", &[w(2)]), Word::from_u64(0));
    assert!(!r.send(2, "pause()", &[]));

    // `setRoles` replaces the whole mask.
    assert!(r.send(1, "grantRoles(address,uint256)", &[w(4), w(7)]));
    assert!(!r.send(4, "resetRoles(address)", &[w(4)]));
    assert!(r.send(1, "resetRoles(address)", &[w(4)]));
    assert_eq!(updated(&r), vec![Word::from_u64(4), Word::from_u64(0)]);
    assert_eq!(r.word("rolesOf(address)", &[w(4)]), Word::from_u64(0));

    // The owner's transfer moves who may grant.
    assert!(r.send(1, "transferOwnership(address)", &[w(9)]));
    assert!(!r.send(1, "grantRoles(address,uint256)", &[w(2), Arg::W(minter)]));
    assert!(r.send(9, "grantRoles(address,uint256)", &[w(2), Arg::W(minter)]));
    assert!(!r.send(1, "pause()", &[]));

    // Masks to and from role ordinals, as Solady's helpers convert them.
    let conv = deploy(
        &compile(
            "\
import \"std/access/ownable_roles\"; import \"std/access/ownable\";
contract Conv is {
  use Ownable;
  use OwnableRoles;
  storage is record {}
  external pure function rolesFromOrdinals(const ordinals : list(uint8)) : Roles is
    OwnableRoles.rolesFromOrdinals(ordinals)
  external pure function ordinalsFromRoles(const r : Roles) : list(uint8) is
    OwnableRoles.ordinalsFromRoles(r)
}
",
        )
        .expect("compile"),
    )
    .expect("deploy");
    let one = Word::from_u64(1);
    for ordinals in [
        vec![],
        vec![0],
        vec![255],
        vec![0, 3, 3, 200, 255],
        vec![7, 1],
    ] {
        let list: Vec<Word> = ordinals.iter().map(|&o| Word::from_u64(o)).collect();
        let out = call_raw(
            &conv,
            &encode_args("rolesFromOrdinals(uint8[])", &[Arg::L(list)]),
        );
        let mask = ordinals
            .iter()
            .fold(Word::from_u64(0), |m, &o| m.bitor(one.shl(o as u32)));
        assert_eq!(load_bytes(&out.returndata, 0), mask, "{ordinals:?}");
        let out = call_raw(
            &conv,
            &encode_args("ordinalsFromRoles(uint256)", &[Arg::W(mask)]),
        );
        let mut sorted = ordinals.clone();
        sorted.sort();
        sorted.dedup();
        let want: Vec<Word> = sorted.iter().map(|&o| Word::from_u64(o)).collect();
        assert_eq!(
            load_bytes(&out.returndata, 32),
            Word::from_u64(want.len() as u64)
        );
        for (i, o) in want.iter().enumerate() {
            assert_eq!(load_bytes(&out.returndata, 64 + 32 * i), *o);
        }
    }
    let all = Word::from_u64(0).not();
    let out = call_raw(
        &conv,
        &encode_args("ordinalsFromRoles(uint256)", &[Arg::W(all)]),
    );
    assert_eq!(load_bytes(&out.returndata, 32), Word::from_u64(256));
    assert_eq!(
        load_bytes(&out.returndata, 64 + 32 * 255),
        Word::from_u64(255)
    );
    // An ordinal past 255 is not a `uint8`.
    let out = call_raw(
        &conv,
        &encode_args(
            "rolesFromOrdinals(uint8[])",
            &[Arg::L(vec![Word::from_u64(256)])],
        ),
    );
    assert!(out.reverted);
}

/// ERC-6492: a signature for a wallet not deployed yet deploys it through its factory,
/// deferred, and is checked in the continuation; the view answers at once.
#[test]
fn stdlib_erc6492() {
    install_mocks();
    let built = compile_contracts(
        "\
import \"std/abi\"; import \"std/crypto\"; import \"std/evm\"; import \"std/utils/create2\";
contract Factory is {
  use Create2;
  storage is record {}
  external function make(const salt : bytes32) is {
    defer create Wallet() with salt = salt;
  }
  external view function predict(const salt : bytes32) : address is
    Create2.computeAddressHere(salt, Crypto.keccak256(Evm.creationCode(Wallet)))
}
contract Wallet is {
  storage is record {}
  external view function isValidSignature(const hash : bytes32; const signature : bytes) : bytes4 is
    if signature = Abi.encode(hash) then 0x1626ba7e else 0xffffffff
}
",
    )
    .expect("compile");
    let factory_code =
        deploy(&built.iter().find(|(n, _)| n == "Factory").unwrap().1).expect("factory");
    let checker = deploy(
        &compile(
            "\
import \"std/crypto/signature_checker\"; import \"std/crypto/ecdsa\";
contract Checker is {
  use ECDSA;
  use SignatureChecker;
  storage is record { used : uint; }
  external function spend(const signer : address; const hash : bytes32; const signature : bytes)
    raises ERC6492InvalidSignature
  is {
    SignatureChecker.checkERC6492Signature(signer, hash, signature);
    storage.used := storage.used + 1;
  }
  external view function validNow(const signer : address; const hash : bytes32; const signature : bytes)
    : bool
  is
    SignatureChecker.isValidERC6492SignatureNow(signer, hash, signature)
}
",
        )
        .expect("compile checker"),
    )
    .expect("deploy checker");
    let w = Word::from_u64;
    let factory = w(0x6000);
    DEPLOYED.with(|d| {
        d.borrow_mut()
            .insert(factory, (factory_code.clone(), HashMap::new()))
    });
    let hash = keccak_word(b"message");
    let word = |x: Word| x.to_be_bytes().to_vec();
    let predict = |salt: u64| {
        // As the factory's own account, whose address its CREATE2 derives from.
        let out = super::elsewhere(factory, || {
            call(&factory_code, "predict(bytes32)", &[w(salt)])
        });
        load_bytes(&out.returndata, 0)
    };
    let wrap = |to: Word, salt: u64, inner: Vec<u8>| {
        let data = encode_args("make(bytes32)", &[Arg::W(w(salt))]);
        let mut out = encode_args("", &[Arg::W(to), Arg::B(data), Arg::B(inner)])[4..].to_vec();
        out.extend([0x64, 0x92].repeat(16));
        out
    };
    let run = |sig: &str, signer: Word, signature: &[u8]| {
        exec(
            &checker,
            &encode_args(
                sig,
                &[Arg::W(signer), Arg::W(hash), Arg::B(signature.to_vec())],
            ),
            HashMap::new(),
            w(1),
            w(0),
            w(0),
        )
        .expect(sig)
    };
    let valid_now = |signer: Word, signature: &[u8]| {
        load_bytes(
            &run("validNow(address,bytes32,bytes)", signer, signature).returndata,
            0,
        ) == w(1)
    };
    let spend = "spend(address,bytes32,bytes)";
    let invalid = |out: &Outcome, signer: Word| {
        assert!(out.reverted);
        assert_eq!(
            out.returndata[..4],
            selector("ERC6492InvalidSignature(address)")
        );
        assert_eq!(load_bytes(&out.returndata, 4), signer);
    };

    let wallet = predict(1);
    let signed = wrap(factory, 1, word(hash));
    // Not deployed: the view can't say yes, and the check deploys the wallet first.
    assert!(!valid_now(wallet, &signed));
    let out = run(spend, wallet, &signed);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert!(out
        .trace
        .iter()
        .any(|ev| matches!(ev, Ev::Call { to, .. } if *to == factory)));
    assert!(out.trace.iter().any(|ev| matches!(ev, Ev::SStore)));
    // Deployed now: the wrapped and the plain signature hold at once, with no factory call.
    assert!(valid_now(wallet, &signed));
    assert!(valid_now(wallet, &word(hash)));
    let out = run(spend, wallet, &signed);
    assert!(!out.reverted);
    assert!(!out.trace.iter().any(|ev| matches!(ev, Ev::Call { .. })));
    assert!(!valid_now(wallet, &wrap(factory, 1, word(w(5)))));

    // A wrong signature, a failing factory, or a plain bad signature raises, deploying
    // nothing.
    let other = predict(2);
    invalid(&run(spend, other, &wrap(factory, 2, word(w(5)))), other);
    assert!(!valid_now(other, &wrap(factory, 2, word(hash))));
    invalid(&run(spend, other, &wrap(w(0xee), 2, word(hash))), other);
    invalid(&run(spend, other, &word(hash)), other);
    invalid(&run(spend, w(0x4242), &[0; 65]), w(0x4242));
    // The wallet a factory call left undeployed is refused too.
    invalid(
        &run(spend, predict(3), &wrap(factory, 4, word(hash))),
        predict(3),
    );
}

/// `SetEnumerable.add`/`remove` and `MapEnumerable.set`/`remove` answer whether they
/// changed membership, as OpenZeppelin's do.
#[test]
fn enumerable_changes_answer_bool() {
    let runtime = deploy(
        &compile(
            "\
import \"std/collections/set_enumerable\"; import \"std/collections/map_enumerable\";
contract C is {
  storage is record {
    s : SetEnumerable(uint);
    m : MapEnumerable(uint, uint);
  }
  external function add(const v : uint) : bool is SetEnumerable.add(storage.s, v)
  external function remove(const v : uint) : bool is SetEnumerable.remove(storage.s, v)
  external function set(const k : uint; const v : uint) : bool is
    MapEnumerable.set(storage.m, k, v)
  external function unset(const k : uint) : bool is MapEnumerable.remove(storage.m, k)
  external view function get(const k : uint) : uint raises EnumerableMapNonexistentKey is
    MapEnumerable.get(storage.m, k)
}
",
        )
        .expect("compile"),
    )
    .expect("deploy");
    let mut storage = HashMap::new();
    let mut send = |sig: &str, args: &[u64]| {
        let args: Vec<Word> = args.iter().map(|&a| Word::from_u64(a)).collect();
        let data = encode_args(sig, &args.iter().map(|&a| Arg::W(a)).collect::<Vec<_>>());
        let out = exec(
            &runtime,
            &data,
            storage.clone(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect("exec");
        assert!(!out.reverted, "{sig}");
        storage = out.storage.clone();
        load_bytes(&out.returndata, 0)
    };
    let (yes, no) = (Word::from_u64(1), Word::from_u64(0));
    assert_eq!(send("add(uint256)", &[5]), yes);
    assert_eq!(send("add(uint256)", &[5]), no);
    assert_eq!(send("add(uint256)", &[6]), yes);
    assert_eq!(send("remove(uint256)", &[5]), yes);
    assert_eq!(send("remove(uint256)", &[5]), no);
    assert_eq!(send("remove(uint256)", &[7]), no);
    assert_eq!(send("set(uint256,uint256)", &[1, 10]), yes);
    assert_eq!(send("set(uint256,uint256)", &[1, 11]), no);
    assert_eq!(send("get(uint256)", &[1]), Word::from_u64(11));
    assert_eq!(send("unset(uint256)", &[1]), yes);
    assert_eq!(send("unset(uint256)", &[1]), no);
}

/// `std/collections/map_enumerable.lithe`: entries set, replaced, listed, and removed,
/// with OpenZeppelin's error for a missing key.
#[test]
fn stdlib_map_enumerable() {
    let mut u = Session::new("examples/stdlib/utils.lithe");
    let pair = |u: &Session| {
        let out = u.returned();
        (load_bytes(&out, 0), load_bytes(&out, 32))
    };
    assert_eq!(u.word("mapLength()", &[]), Word::from_u64(0));
    assert!(!u.send(0, "mapGet(address)", &[w(7)]));
    u.reverted_with("EnumerableMapNonexistentKey(bytes32)");
    assert_eq!(load_bytes(&u.returned()[4..], 0), Word::from_u64(7));
    assert!(u.send(0, "mapTryGet(address)", &[w(7)]));
    assert_eq!(pair(&u), (Word::from_u64(0), Word::from_u64(0)));
    assert!(!u.send(0, "mapAt(uint256)", &[w(0)]));
    u.reverted_with("OutOfBounds()");

    for (key, value) in [(7u64, 70u64), (8, 0), (9, 90), (7, 71)] {
        assert!(u.send(0, "mapSet(address,uint256)", &[w(key), w(value)]));
    }
    assert_eq!(u.word("mapLength()", &[]), Word::from_u64(3));
    assert_eq!(u.word("mapGet(address)", &[w(7)]), Word::from_u64(71));
    // A key set to zero is still present.
    assert_eq!(u.word("mapContains(address)", &[w(8)]), Word::from_u64(1));
    assert!(u.send(0, "mapTryGet(address)", &[w(8)]));
    assert_eq!(pair(&u), (Word::from_u64(1), Word::from_u64(0)));
    assert!(u.send(0, "mapAt(uint256)", &[w(2)]));
    assert_eq!(pair(&u), (Word::from_u64(9), Word::from_u64(90)));

    // Removing moves the last entry into the gap.
    assert!(u.send(0, "mapRemove(address)", &[w(7)]));
    assert!(u.send(0, "mapRemove(address)", &[w(7)]));
    assert_eq!(u.word("mapLength()", &[]), Word::from_u64(2));
    assert_eq!(u.word("mapContains(address)", &[w(7)]), Word::from_u64(0));
    assert!(!u.send(0, "mapGet(address)", &[w(7)]));
    u.reverted_with("EnumerableMapNonexistentKey(bytes32)");
    assert!(u.send(0, "mapAt(uint256)", &[w(0)]));
    assert_eq!(pair(&u), (Word::from_u64(9), Word::from_u64(90)));
    assert!(u.send(0, "mapAt(uint256)", &[w(1)]));
    assert_eq!(pair(&u), (Word::from_u64(8), Word::from_u64(0)));
    assert!(!u.send(0, "mapAt(uint256)", &[w(2)]));
    u.reverted_with("OutOfBounds()");
    assert!(u.send(0, "mapSet(address,uint256)", &[w(7), w(5)]));
    assert_eq!(u.word("mapGet(address)", &[w(7)]), Word::from_u64(5));

    // A `bytes4` key's error payload is left-aligned, as OpenZeppelin's `bytes32` is.
    let selector = Word::from_u64(0xdead_beef).shl(224);
    assert!(!u.send(0, "tagged(bytes4)", &[Arg::W(selector)]));
    u.reverted_with("EnumerableMapNonexistentKey(bytes32)");
    assert_eq!(load_bytes(&u.returned()[4..], 0), selector);
    assert!(u.send(0, "tag(bytes4,address)", &[Arg::W(selector), w(3)]));
    assert_eq!(
        u.word("tagged(bytes4)", &[Arg::W(selector)]),
        Word::from_u64(3)
    );
}

/// `Bitmap.setBatch`, `unsetBatch`, and `popCount` over runs inside one slot, across
/// slot edges, and over whole slots, against a model of the flags.
#[test]
fn stdlib_bitmap_batches() {
    let mut u = Session::new("examples/stdlib/utils.lithe");
    let mut model = vec![false; 1300];
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = |bound: u64| {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed % bound
    };
    let edges = [
        (0u64, 0u64),
        (0, 256),
        (0, 1),
        (255, 1),
        (255, 2),
        (256, 256),
        (1, 255),
        (3, 700),
        (512, 0),
        (100, 512),
    ];
    for step in 0..60 {
        let (start, amount) = match edges.get(step / 2) {
            Some(&edge) => edge,
            None => (next(800), next(500)),
        };
        let on = step % 3 != 2;
        let sig = if on {
            "flag(uint256,uint256)"
        } else {
            "unflag(uint256,uint256)"
        };
        assert!(
            u.send(0, sig, &[w(start), w(amount)]),
            "{sig} {start} {amount}"
        );
        for i in start..start + amount {
            model[i as usize] = on;
        }
        let (a, b) = (next(1300), next(600));
        let want = model[a as usize..(a + b).min(1300) as usize]
            .iter()
            .filter(|f| **f)
            .count();
        assert_eq!(
            u.word("flagged(uint256,uint256)", &[w(a), w(b)]),
            Word::from_u64(want as u64),
            "popCount({a}, {b}) after {sig} {start} {amount}"
        );
        for i in [
            start.saturating_sub(1),
            start,
            start + amount.saturating_sub(1),
            start + amount,
        ] {
            assert_eq!(
                u.word("isFlagged(uint256)", &[w(i)]),
                Word::from_u64(u64::from(model[i as usize])),
                "flag {i} after {sig} {start} {amount}"
            );
        }
    }
    assert!(u.send(0, "flag(uint256,uint256)", &[w(0), w(1300)]));
    assert_eq!(
        u.word("flagged(uint256,uint256)", &[w(0), w(1300)]),
        Word::from_u64(1300)
    );
    assert_eq!(
        u.word("flagged(uint256,uint256)", &[w(256), w(256)]),
        Word::from_u64(256)
    );
    // Overflowing the index range reverts.
    assert!(!u.send(
        0,
        "flag(uint256,uint256)",
        &[w(1), Arg::W(Word::from_u64(0).not())]
    ));
}

const PASSKEYS: &str = r#"
import "std/crypto/webauthn";
import "std/abi";
import "std/bytes";

contract Passkeys is {
  storage is record {}

  use WebAuthn;

  external view function verify(
    const challenge : bytes;
    const requireUserVerification : bool;
    const auth : WebauthnAuth;
    const x : bytes32;
    const y : bytes32
  ) : bool is
    WebAuthn.verify(challenge, requireUserVerification, auth, x, y)

  external pure function decode(const encoded : bytes) : bytes is
    case WebAuthn.tryDecodeAuth(encoded) of { Some(auth) -> Abi.encode(auth) | None -> Bytes.concat() }

  external pure function encodeCompact(const auth : WebauthnAuth) : bytes is
    WebAuthn.tryEncodeAuthCompact(auth)

  external pure function decodeCompact(const encoded : bytes) : bytes is
    case WebAuthn.tryDecodeAuthCompact(encoded) of { Some(auth) -> Abi.encode(auth) | None -> Bytes.concat() }
}
"#;

fn passkeys(evm: crate::EvmVersion) -> Vec<u8> {
    let opts = Options {
        evm,
        ..Options::default()
    };
    let out = crate::compile(&memory(PASSKEYS), Path::new(ENTRY), &opts)
        .and_then(crate::Output::single)
        .map_err(first)
        .expect("compile");
    deploy(&out.bytecode).expect("deploy")
}

struct Assertion {
    authenticator_data: Vec<u8>,
    client_data_json: Vec<u8>,
    challenge_index: Word,
    type_index: Word,
    r: Word,
    s: Word,
}

/// `verify(challenge, uv, auth, x, y)` on the `Passkeys` runtime, or `None` if it reverted.
fn passkey_verify(
    runtime: &[u8],
    challenge: &[u8],
    uv: bool,
    a: &Assertion,
    x: Word,
    y: Word,
) -> Option<bool> {
    let auth = encode_args(
        "",
        &[
            Arg::B(a.authenticator_data.clone()),
            Arg::B(a.client_data_json.clone()),
            Arg::W(a.challenge_index),
            Arg::W(a.type_index),
            Arg::W(a.r),
            Arg::W(a.s),
        ],
    );
    let challenge = encode_args("", &[Arg::B(challenge.to_vec())]);
    let challenge = &challenge[4 + 32..];
    let mut data = selector(
        "verify(bytes,bool,(bytes,string,uint256,uint256,bytes32,bytes32),bytes32,bytes32)",
    )
    .to_vec();
    for word in [
        Word::from_u64(5 * 32),
        Word::from_u64(u64::from(uv)),
        Word::from_u64((5 * 32 + challenge.len()) as u64),
        x,
        y,
    ] {
        data.extend(word.to_be_bytes());
    }
    data.extend(challenge);
    data.extend(&auth[4..]);
    let out = call_raw(runtime, &data);
    (!out.reverted).then(|| out.returndata == Word::from_u64(1).to_be_bytes())
}

/// Solady's `WebAuthn.t.sol` passkey assertions from Safari and Chrome, and its key and
/// challenge.
fn solady_passkeys() -> (Word, Word, Vec<u8>, [Assertion; 2]) {
    let hexw = |s: &str| Word::from_hex(s).unwrap();
    let x = hexw("3f2be075ef57d6c8374ef412fe54fdd980050f70f4f3a00b5b1b32d2def7d28d");
    let y = hexw("57095a365acc2590ade3583fabfe8fbd64a9ed3ec07520da00636fb21f0176c1");
    let challenge = hexw("f631058a3ba1116acce12396fad0a125b5041c43f8e15723709f81aa8d5f4ccf")
        .to_be_bytes()
        .to_vec();
    let json = |tail: &str| {
        [
            br#"{"type":"webauthn.get","challenge":""#.to_vec(),
            base64_reference(&challenge, true, true),
            tail.as_bytes().to_vec(),
        ]
        .concat()
    };
    let safari = Assertion {
        authenticator_data: hex_decode(
            "49960de5880e8c687434170f6476605b8fe4aeb9a28632c7995cf3ba831d97630500000101",
        ),
        client_data_json: json(r#"","origin":"http://localhost:3005"}"#),
        challenge_index: Word::from_u64(23),
        type_index: Word::from_u64(1),
        r: hexw("60946081650523acad13c8eff94996a409b1ed60e923c90f9e366aad619adffa"),
        s: hexw("3216a237b73765d01b839e0832d73474bc7e63f4c86ef05fbbbfbeb34b35602b"),
    };
    let chrome = Assertion {
        authenticator_data: hex_decode(
            "49960de5880e8c687434170f6476605b8fe4aeb9a28632c7995cf3ba831d9763050000010a",
        ),
        client_data_json: json(r#"","origin":"http://localhost:3005","crossOrigin":false}"#),
        challenge_index: Word::from_u64(23),
        type_index: Word::from_u64(1),
        r: hexw("41c01ca5ecdfeb23ef70d6cc216fd491ac3aa3d40c480751f3618a3a9ef67b41"),
        s: hexw("6595569abf76c2777e832a9252bae14efdb77febd0fa3b919aa16f6208469e86"),
    };
    (x, y, challenge, [safari, chrome])
}

/// The P-256 order.
fn p256_order() -> Word {
    Word::from_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551").unwrap()
}

/// Solady's `WebAuthn.t.sol` passkey signatures from Safari and Chrome verify on the
/// EIP-7951 precompile, and every part of the assertion is checked.
#[test]
fn webauthn_verifies_passkey_assertions() {
    let runtime = deploy(&compile(PASSKEYS).expect("compile")).expect("deploy");
    let (x, y, challenge, assertions) = solady_passkeys();
    let n = p256_order();
    let max = Word::from_u64(0).not();
    let verify = |c: &[u8], uv: bool, a: &Assertion| passkey_verify(&runtime, c, uv, a, x, y);
    for mut a in assertions {
        assert_eq!(verify(&challenge, false, &a), Some(true));
        // Both authenticators set the user-verified flag.
        assert_eq!(verify(&challenge, true, &a), Some(true));
        assert_eq!(
            passkey_verify(&runtime, &challenge, false, &a, y, x),
            Some(false)
        );
        let mut other = challenge.clone();
        other[31] ^= 1;
        assert_eq!(verify(&other, false, &a), Some(false));
        // `(r, n - s)` signs the same hash: the precompile accepts it, and `verify` does not.
        let high = n.wrapping_sub(a.s);
        let hash = crate::hash::sha256(
            &[
                a.authenticator_data.clone(),
                crate::hash::sha256(&a.client_data_json).to_vec(),
            ]
            .concat(),
        );
        let input = [
            hash,
            a.r.to_be_bytes(),
            high.to_be_bytes(),
            x.to_be_bytes(),
            y.to_be_bytes(),
        ];
        assert!(crate::hash::p256_verify(&input.concat()));
        let s = std::mem::replace(&mut a.s, high);
        assert_eq!(verify(&challenge, false, &a), Some(false));
        a.s = s;
        let r = a.r;
        a.r = r.wrapping_add(Word::from_u64(1));
        assert_eq!(verify(&challenge, false, &a), Some(false));
        a.r = r;
        let (c, t) = (a.challenge_index, a.type_index);
        for (c2, t2) in [
            (Word::from_u64(24), t),
            (c, Word::from_u64(0)),
            (max, t),
            (c, max),
            (max.wrapping_sub(Word::from_u64(12)), t),
        ] {
            (a.challenge_index, a.type_index) = (c2, t2);
            assert_eq!(verify(&challenge, false, &a), Some(false));
        }
        (a.challenge_index, a.type_index) = (c, t);
        a.authenticator_data.truncate(32);
        assert_eq!(verify(&challenge, false, &a), Some(false));
    }
}

/// Built for Prague, `verify` asks Solady's P256 verifier when the precompile answers
/// nothing and Solady's canary has no code, and takes only a word 1 from it. An Osaka
/// build trusts the precompile alone.
#[test]
fn webauthn_falls_back_to_solady_verifier() {
    fn absent(_: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
        Ok(Vec::new())
    }
    fn verifier(input: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
        Ok(Word::from_u64(u64::from(crate::hash::p256_verify(input)))
            .to_be_bytes()
            .to_vec())
    }
    fn short(input: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
        Ok(vec![u8::from(crate::hash::p256_verify(input)); 31])
    }
    fn failing(_: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
        Err(Word::from_u64(1).to_be_bytes().to_vec())
    }
    fn canary(_: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
        Ok(Vec::new())
    }
    let at = |s: &str| Word::from_hex(s).unwrap();
    let (verifier_at, canary_at) = (
        at("000000000000D01eA45F9eFD5c54f037Fa57Ea1a"),
        at("0000000000001Ab2e8006Fd8B71907bf06a5BDEE"),
    );
    let set = |addr: Word, mock: Option<Mock>| {
        MOCKS.with(|m| {
            let mut m = m.borrow_mut();
            match mock {
                Some(f) => m.insert(addr, f),
                None => m.remove(&addr),
            }
        });
    };
    let (prague, osaka) = (
        passkeys(crate::EvmVersion::Prague),
        passkeys(crate::EvmVersion::Osaka),
    );
    let (x, y, challenge, assertions) = solady_passkeys();
    let precompile = Word::from_u64(0x100);
    for mut a in assertions {
        let s = a.s;
        let high = p256_order().wrapping_sub(s);
        let mut check = |precompile_mock: Option<Mock>,
                         verifier_mock: Option<Mock>,
                         canary_mock: Option<Mock>,
                         want: [bool; 2]| {
            set(precompile, precompile_mock);
            set(verifier_at, verifier_mock);
            set(canary_at, canary_mock);
            a.s = s;
            let got = [&prague, &osaka].map(|r| passkey_verify(r, &challenge, false, &a, x, y));
            assert_eq!(got, want.map(Some));
            // The verifier accepts the high twin; `verify` does not ask.
            a.s = high;
            let got = [&prague, &osaka].map(|r| passkey_verify(r, &challenge, false, &a, x, y));
            assert_eq!(got, [Some(false); 2]);
            a.s = s;
            let got = passkey_verify(&prague, &challenge, false, &a, y, x);
            assert_eq!(got, Some(false));
        };
        check(None, Some(verifier), None, [true, true]);
        check(Some(absent), Some(verifier), None, [true, false]);
        check(Some(absent), Some(verifier), Some(canary), [false, false]);
        check(Some(absent), None, None, [false, false]);
        check(Some(absent), Some(short), None, [false, false]);
        check(Some(absent), Some(failing), None, [false, false]);
    }
}

/// An `Abi.encode`d auth by Solady's `tryDecodeAuth` rules: the fields, or `None`.
fn solady_try_decode_auth(e: &[u8]) -> Option<(Vec<u8>, Vec<u8>, [Word; 4])> {
    let word = |at: usize| {
        e.get(at..at + 32)
            .map(|b| Word::from_be_bytes(b.try_into().unwrap()))
    };
    let small = |w: Word| word_usize(w).ok().filter(|&v| v < 1 << 40);
    let n = e.len();
    if n < 0xc0 {
        return None;
    }
    let p = small(word(0)?)?;
    if p + 0xc0 > n {
        return None;
    }
    let field = |k: usize| -> Option<Vec<u8>> {
        let at = p + small(word(p + k)?)?;
        let len = small(word(at)?)?;
        (at + 32 + len <= n).then(|| e[at + 32..at + 32 + len].to_vec())
    };
    let (a, j) = (field(0)?, field(32)?);
    Some((a, j, [0x40, 0x60, 0x80, 0xa0].map(|k| word(p + k).unwrap())))
}

/// `tryDecodeAuth` reads what `Abi.encode` wrote, and with any word or length broken
/// answers as Solady's `tryDecodeAuth` does; `tryEncodeAuthCompact` packs as Solady's
/// test expects, and `tryDecodeAuthCompact` reads it back or refuses as Solady does.
#[test]
fn webauthn_decodes_auths_as_solady() {
    let runtime = passkeys(crate::EvmVersion::Osaka);
    let seed = std::cell::Cell::new(0x9e37_79b9_7f4a_7c15u64);
    let next = || {
        let mut v = seed.get();
        v ^= v << 13;
        v ^= v >> 7;
        v ^= v << 17;
        seed.set(v);
        v
    };
    let bytes_out = |sig: &str, data: &[u8]| {
        let out = call_raw(&runtime, &abi_string(sig, data));
        assert!(!out.reverted, "{sig}");
        abi_string_value(&out.returndata)
    };
    let encode = |a: &[u8], j: &[u8], w: [Word; 4]| {
        let args = [
            Arg::B(a.to_vec()),
            Arg::B(j.to_vec()),
            Arg::W(w[0]),
            Arg::W(w[1]),
            Arg::W(w[2]),
            Arg::W(w[3]),
        ];
        let mut out = Word::from_u64(32).to_be_bytes().to_vec();
        out.extend(&encode_args("", &args)[4..]);
        out
    };
    let (mut accepted, mut refused, mut compact) = (0, 0, 0);
    for round in 0..300 {
        let short = |max: u64| -> Vec<u8> { (0..next() % max).map(|_| next() as u8).collect() };
        let (a, j) = (short(80), short(80));
        let mut w = [0; 4].map(|_| Word::from_u64(next()));
        if round % 2 == 0 {
            w[0] = Word::from_u64(next() & 0xffff);
            w[1] = Word::from_u64(next() & 0xffff);
        }
        let encoded = encode(&a, &j, w);
        assert_eq!(bytes_out("decode(bytes)", &encoded), encoded);
        // Broken copies: a word replaced, or the data cut short.
        let mut broken = encoded.clone();
        match next() % 3 {
            0 => {
                let at = (next() as usize % (broken.len() / 32)) * 32;
                let v = match next() % 3 {
                    0 => Word::from_u64(next() % 0x200),
                    1 => Word::from_u64(0).not(),
                    _ => Word::from_u64(next()),
                };
                broken[at..at + 32].copy_from_slice(&v.to_be_bytes());
            }
            1 => broken.truncate(next() as usize % broken.len()),
            _ => broken.extend(short(40)),
        }
        let want =
            solady_try_decode_auth(&broken).map_or(Vec::new(), |(a, j, w)| encode(&a, &j, w));
        if want.is_empty() {
            refused += 1;
        } else {
            accepted += 1;
        }
        assert_eq!(bytes_out("decode(bytes)", &broken), want);

        let fits = a.len() < 1 << 16
            && j.len() < 1 << 16
            && w[..2]
                .iter()
                .all(|&v| word_usize(v).is_ok_and(|v| v < 1 << 16));
        let args = encode(&a, &j, w);
        let mut call =
            selector("encodeCompact((bytes,string,uint256,uint256,bytes32,bytes32))").to_vec();
        call.extend(&args);
        let out = call_raw(&runtime, &call);
        assert!(!out.reverted);
        let packed = abi_string_value(&out.returndata);
        let want: Vec<u8> = if fits {
            [
                (a.len() as u16).to_be_bytes().to_vec(),
                a.clone(),
                j.clone(),
                (word_usize(w[0]).unwrap() as u16).to_be_bytes().to_vec(),
                (word_usize(w[1]).unwrap() as u16).to_be_bytes().to_vec(),
                w[2].to_be_bytes().to_vec(),
                w[3].to_be_bytes().to_vec(),
            ]
            .concat()
        } else {
            Vec::new()
        };
        assert_eq!(packed, want);
        if fits {
            compact += 1;
            assert_eq!(bytes_out("decodeCompact(bytes)", &packed), encoded);
        }
        // Solady's rules for any bytes: at least 0x46 of them, and the authenticator data
        // before the last 0x44.
        let raw = if fits && next() % 2 == 0 {
            packed[..next() as usize % packed.len()].to_vec()
        } else {
            short(120)
        };
        let n = raw.len();
        let want = if n >= 0x46 && 2 + (usize::from(raw[0]) << 8 | usize::from(raw[1])) <= n - 0x44
        {
            let c = 2 + (usize::from(raw[0]) << 8 | usize::from(raw[1]));
            let j = n - 0x44;
            let word = |at: usize| Word::from_be_bytes(raw[at..at + 32].try_into().unwrap());
            encode(
                &raw[2..c],
                &raw[c..j],
                [
                    Word::from_u64(u64::from(raw[j]) << 8 | u64::from(raw[j + 1])),
                    Word::from_u64(u64::from(raw[j + 2]) << 8 | u64::from(raw[j + 3])),
                    word(j + 4),
                    word(j + 36),
                ],
            )
        } else {
            Vec::new()
        };
        assert_eq!(bytes_out("decodeCompact(bytes)", &raw), want);
    }
    assert!(
        accepted > 30 && refused > 30 && compact > 100,
        "{accepted} {refused} {compact}"
    );
}

/// With a precompile that accepts every signature, `verify` answers as Solady's reference
/// checks of the client data and flags do, over sampled JSON, indexes, and flags.
#[test]
fn webauthn_checks_match_solady_reference() {
    fn accept(_: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
        Ok(Word::from_u64(1).to_be_bytes().to_vec())
    }
    fn next(seed: &mut u64) -> u64 {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        *seed
    }
    fn short(seed: &mut u64, max: u64) -> Vec<u8> {
        let len = next(seed) % max;
        (0..len).map(|_| next(seed) as u8).collect()
    }
    fn maybe(seed: &mut u64, s: &[u8]) -> Vec<u8> {
        if next(seed).is_multiple_of(4) {
            Vec::new()
        } else {
            s.to_vec()
        }
    }
    MOCKS.with(|m| m.borrow_mut().insert(Word::from_u64(0x100), accept as Mock));
    let runtime = deploy(&compile(PASSKEYS).expect("compile")).expect("deploy");
    let mut seed = 0x2545_f491_4f6c_dd1du64;
    let (mut accepted, mut rejected) = (0, 0);
    for _ in 0..600 {
        let challenge = short(&mut seed, 40);
        let encoded = base64_reference(&challenge, true, true);
        let close = [b"\"".to_vec(), short(&mut seed, 4), b"}".to_vec()].concat();
        let json = [
            b"{".to_vec(),
            short(&mut seed, 4),
            maybe(&mut seed, br#""type":"webauthn.get""#),
            short(&mut seed, 4),
            maybe(&mut seed, br#","challenge":""#),
            encoded.clone(),
            maybe(&mut seed, &close),
        ]
        .concat();
        let mut index = |needle: &[u8]| match json.windows(needle.len()).position(|w| w == needle) {
            Some(i) if !next(&mut seed).is_multiple_of(4) => i as u64,
            _ => next(&mut seed) % (json.len() as u64 + 36),
        };
        let c = index(br#""challenge":""#);
        let t = index(br#""type":"webauthn.get""#);
        let len = if next(&mut seed).is_multiple_of(4) {
            next(&mut seed) % 40
        } else {
            33 + next(&mut seed) % 8
        };
        let mut data: Vec<u8> = (0..len).map(|_| next(&mut seed) as u8).collect();
        if data.len() > 32 && !next(&mut seed).is_multiple_of(4) {
            data[32] |= 1;
        }
        let uv = next(&mut seed).is_multiple_of(2);
        let expected = [br#""challenge":""#.to_vec(), encoded, b"\"".to_vec()].concat();
        let (cu, tu) = (c as usize, t as usize);
        let want = json.get(tu..tu + 21) == Some(br#""type":"webauthn.get""#.as_slice())
            && json.get(cu..cu + expected.len()) == Some(expected.as_slice())
            && data.len() > 32
            && data[32] & 1 == 1
            && (!uv || data[32] & 4 == 4);
        let a = Assertion {
            authenticator_data: data,
            client_data_json: json.clone(),
            challenge_index: Word::from_u64(c),
            type_index: Word::from_u64(t),
            r: Word::from_u64(0),
            s: Word::from_u64(0),
        };
        let zero = Word::from_u64(0);
        let got = passkey_verify(&runtime, &challenge, uv, &a, zero, zero);
        assert_eq!(got, Some(want), "{}", String::from_utf8_lossy(&json));
        if want {
            accepted += 1;
        } else {
            rejected += 1;
        }
    }
    assert!(
        accepted > 20 && rejected > 20,
        "{accepted} accepted, {rejected} rejected"
    );
}

/// `std/token/safe_erc20.lithe` against a token that answers `true`, one that answers
/// `false`, one that reverts, a USDT that answers nothing and refuses to change an
/// allowance that isn't zero, and an account with no code.
#[test]
fn stdlib_safe_erc20() {
    install_mocks();
    let usdt = deploy(&compile(
        "\
error Nope;
storage is record { allowed : map(address, uint); moved : uint; }
external function transfer(const to : address; const value : uint) is { storage.moved := storage.moved + value; }
external function transferFrom(const from : address; const to : address; const value : uint) is { storage.moved := storage.moved + value; }
external function approve(const spender : address; const value : uint) raises Nope is {
  assert(value = 0 or storage.allowed[spender] = 0, Nope);
  storage.allowed[spender] := value;
}
external view function allowance(const owner : address; const spender : address) : uint is storage.allowed[spender]
",
    )
    .expect("usdt"))
    .expect("deploy usdt");
    // Answers `answer = 1`, or reverts with `Nope(value)` when `refuse` is set; its
    // `approve` answers `false` to change an allowance that isn't zero.
    let flagged = deploy(&compile(
        "\
error Nope of uint;
storage is record { allowed : map(address, uint); moved : uint; answer : uint; refuse : uint; }
external function transfer(const to : address; const value : uint) : bool raises Nope is {
  assert(storage.refuse = 0, Nope(value));
  storage.moved := storage.moved + value;
} with storage.answer = 1
external function transferFrom(const from : address; const to : address; const value : uint) : bool raises Nope is {
  assert(storage.refuse = 0, Nope(value));
  storage.moved := storage.moved + value;
} with storage.answer = 1
external function approve(const spender : address; const value : uint) : bool raises Nope is {
  assert(storage.refuse = 0, Nope(value));
  const ok : bool := value = 0 or storage.allowed[spender] = 0;
  if ok then {
    storage.allowed[spender] := value;
  }
} with ok
external view function allowance(const owner : address; const spender : address) : uint is storage.allowed[spender]
",
    )
    .expect("flagged"))
    .expect("deploy flagged");
    // Answers 2 to everything.
    let two = deploy(&compile(
        "\
storage is record { n : uint; }
external function transfer(const to : address; const value : uint) : uint is 2
external function transferFrom(const from : address; const to : address; const value : uint) : uint is 2
external function approve(const spender : address; const value : uint) : uint is 2
",
    )
    .expect("two"))
    .expect("deploy two");
    let vault = deploy(
        &compile(
            "\
import \"std/token/safe_erc20\"; import \"std/evm\"; import \"std/interfaces/erc20\";
use SafeERC20;
storage is record { n : uint; }
external nonreentrant function pay(const token : IERC20; const to : address; const value : uint)
  raises SafeERC20FailedOperation | forwarded
is {
  SafeERC20.safeTransfer(token, to, value);
}
external nonreentrant function pull(const token : IERC20; const from : address; const value : uint)
  raises SafeERC20FailedOperation | forwarded
is {
  SafeERC20.safeTransferFrom(token, from, Evm.self(), value);
}
external nonreentrant function allow(const token : IERC20; const spender : address; const value : uint)
  raises SafeERC20FailedOperation | forwarded
is {
  SafeERC20.forceApprove(token, spender, value);
}
external nonreentrant function raise(const token : IERC20; const spender : address; const value : uint)
  raises SafeERC20FailedOperation | forwarded
is {
  SafeERC20.safeIncreaseAllowance(token, spender, value);
}
external nonreentrant function lower(const token : IERC20; const spender : address; const value : uint)
  raises SafeERC20FailedOperation | SafeERC20FailedDecreaseAllowance | forwarded
is {
  SafeERC20.safeDecreaseAllowance(token, spender, value);
}
",
        )
        .expect("vault"),
    )
    .expect("deploy");
    let w = Word::from_u64;
    let (token, spender) = (w(0x7000), w(0x5e));
    let allowed = map_key(spender, w(0));
    // Puts `code` at `token` with `allowance` for `spender` and the other slots given,
    // then calls the vault.
    let run = |code: &[u8], allowance: u64, slots: &[(u64, u64)], sig: &str, args: &[Word]| {
        let mut storage = HashMap::from([(allowed, w(allowance))]);
        storage.extend(slots.iter().map(|&(k, v)| (w(k), w(v))));
        DEPLOYED.with(|d| d.borrow_mut().insert(token, (code.to_vec(), storage)));
        let mut data = vec![token];
        data.extend(args);
        let out = call(&vault, sig, &data);
        let state = DEPLOYED.with(|d| d.borrow()[&token].1.clone());
        (out, state)
    };
    let failed = |out: &Outcome, sig: &str| {
        assert!(out.reverted, "expected {sig}");
        assert_eq!(
            out.returndata[..4],
            selector(sig),
            "{}",
            pretty(&out.returndata)
        );
    };
    let calls = |out: &Outcome| {
        out.trace
            .iter()
            .filter(|ev| matches!(ev, Ev::Call { .. }))
            .count()
    };

    for sig in [
        "pay(address,address,uint256)",
        "pull(address,address,uint256)",
    ] {
        let (out, state) = run(&flagged, 0, &[(2, 1)], sig, &[w(3), w(40)]);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        assert_eq!(slot(&state, 1), w(40), "{sig}");
        let (out, state) = run(&usdt, 0, &[], sig, &[w(3), w(40)]);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        assert_eq!(slot(&state, 1), w(40), "{sig}");
        let (out, _) = run(&flagged, 0, &[], sig, &[w(3), w(40)]);
        failed(&out, "SafeERC20FailedOperation(address)");
        assert_eq!(out.returndata[4..], token.to_be_bytes(), "{sig}");
        let (out, _) = run(&flagged, 0, &[(2, 1), (3, 1)], sig, &[w(3), w(40)]);
        failed(&out, "Nope(uint256)");
        assert_eq!(out.returndata[4..], w(40).to_be_bytes(), "{sig}");
        // An answer that isn't a `bool` reverts with no data.
        let (out, _) = run(&two, 0, &[], sig, &[w(3), w(40)]);
        assert!(out.reverted && out.returndata.is_empty(), "{sig}");
        for nobody in [w(0x4242), w(1)] {
            let out = call(&vault, sig, &[nobody, w(3), w(40)]);
            assert!(
                out.reverted && out.returndata.is_empty(),
                "{sig} {nobody:?}"
            );
        }
    }

    let allow = "allow(address,address,uint256)";
    let (out, state) = run(&usdt, 0, &[], allow, &[spender, w(9)]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!((state[&allowed], calls(&out)), (w(9), 1));
    // USDT refuses to change 5 to 9, so the allowance goes through zero.
    let (out, state) = run(&usdt, 5, &[], allow, &[spender, w(9)]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!((state[&allowed], calls(&out)), (w(9), 3));
    let (out, state) = run(&flagged, 5, &[(2, 1)], allow, &[spender, w(9)]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!((state[&allowed], calls(&out)), (w(9), 3));
    // The retry's own revert passes through.
    let (out, _) = run(&flagged, 5, &[(2, 1), (3, 1)], allow, &[spender, w(9)]);
    failed(&out, "Nope(uint256)");
    assert_eq!(out.returndata[4..], w(0).to_be_bytes());
    let out = call(&vault, allow, &[w(0x4242), spender, w(9)]);
    assert!(out.reverted && out.returndata.is_empty());
    // An approval answered with 2 reverts with no data.
    let (out, _) = run(&two, 5, &[], allow, &[spender, w(9)]);
    assert!(out.reverted && out.returndata.is_empty());

    let (out, state) = run(
        &usdt,
        5,
        &[],
        "raise(address,address,uint256)",
        &[spender, w(3)],
    );
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(state[&allowed], w(8));
    let lower = "lower(address,address,uint256)";
    let (out, state) = run(&usdt, 5, &[], lower, &[spender, w(3)]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(state[&allowed], w(2));
    let (out, _) = run(&usdt, 5, &[], lower, &[spender, w(6)]);
    failed(
        &out,
        "SafeERC20FailedDecreaseAllowance(address,uint256,uint256)",
    );
    assert_eq!(
        out.returndata[4..],
        [spender, w(5), w(6)].map(|x| x.to_be_bytes()).concat()
    );
}

/// `std/token/erc4626`: a vault over a real asset contract, through deposits, mints,
/// withdrawals, and redemptions, OpenZeppelin's rounding, the first-depositor inflation
/// attack with and without a decimals offset, the `max*` limits, a capped vault built from
/// the internals, and assets that return nothing or `false`.
#[test]
fn stdlib_erc4626() {
    const ASSET: &str = r#"
import "std/token/erc20"; import "std/interfaces/erc20";

contract Asset is {
  use ERC20 exposing IERC20, IERC20Metadata; hook ERC20.beforeTransfer is skip; hook ERC20.afterTransfer is skip;

  external function mint(const to : address; const value : uint)
    raises ERC20InvalidReceiver | ERC20InsufficientBalance
  is {
    ERC20.mint(to, value);
  }
}
"#;
    // Transfers that return nothing, like USDT's, and six decimals.
    const QUIET: &str = r#"
import "std/evm"; storage is record {
  balances : map(address, uint);
  allowances : map(address, map(address, uint));
}

external pure function decimals() : uint8 is 6

external view function balanceOf(const account : address) : uint is
  storage.balances[account]

external function mint(const to : address; const value : uint) is {
  storage.balances[to] := storage.balances[to] + value;
}

external function approve(const spender : address; const value : uint) : bool is {
  storage.allowances[Evm.sender()][spender] := value;
} with true

external function transfer(const to : address; const value : uint) is {
  storage.balances[Evm.sender()] := storage.balances[Evm.sender()] - value;
  storage.balances[to] := storage.balances[to] + value;
}

external function transferFrom(const from : address; const to : address; const value : uint) is {
  storage.allowances[from][Evm.sender()] := storage.allowances[from][Evm.sender()] - value;
  storage.balances[from] := storage.balances[from] - value;
  storage.balances[to] := storage.balances[to] + value;
}
"#;
    // Transfers that answer `false`, and no `decimals`.
    const REFUSING: &str = r#"
storage is record {
  n : uint;
}

external view function balanceOf(const account : address) : uint is
  storage.n

external function transfer(const to : address; const value : uint) : bool is {
  storage.n := storage.n;
} with false

external function transferFrom(const from : address; const to : address; const value : uint) : bool is {
  storage.n := storage.n;
} with false
"#;
    let vault_src = |asset: u64, offset: u8, extra: &str| {
        format!(
            r#"
import "std/evm";
import "std/token/erc20";
import "std/token/safe_erc20";
import "std/token/erc4626";
import "std/interfaces/erc20";
import "std/interfaces/erc4626";

contract Vault is {{
  use SafeERC20;
  use ERC20 exposing IERC20, IERC20Name; hook ERC20.beforeTransfer is skip; hook ERC20.afterTransfer is skip;
  use ERC4626 exposing IERC4626, {{
    view function decimals() : uint8;
  }}
  supports IERC20, IERC20Metadata, IERC4626;

  deploy() is {{
    const asset : address := address(0x{asset:040x});
    ERC20.init("Vault", "vTKN");
    ERC4626.init(asset, ERC4626.assetDecimals(asset), {offset});
  }}
  {extra}
}}
"#
        )
    };
    let n = |v: u128| Arg::W(Word::from_dec(&v.to_string()).unwrap());
    let top = Word::from_u64(0).wrapping_sub(Word::from_u64(1));
    let low = |w: Word| u128::from_be_bytes(w.to_be_bytes()[16..].try_into().unwrap());
    let vault_addr = Word::from_u64(0x1000);
    let place = |at: u64, src: &str| {
        let runtime = deploy(&compile(src).unwrap_or_else(|e| panic!("{e}"))).unwrap();
        DEPLOYED.with(|d| {
            d.borrow_mut()
                .insert(Word::from_u64(at), (runtime, HashMap::new()))
        });
    };
    // A direct call to a placed asset, keeping its storage when it succeeds.
    let asset_send = |at: u64, caller: u64, sig: &str, args: &[Arg]| -> Word {
        let (code, storage) = DEPLOYED.with(|d| d.borrow()[&Word::from_u64(at)].clone());
        let out = exec(
            &code,
            &encode_args(sig, args),
            storage,
            Word::from_u64(caller),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .unwrap();
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        DEPLOYED.with(|d| d.borrow_mut().get_mut(&Word::from_u64(at)).unwrap().1 = out.storage);
        load_bytes(&out.returndata, 0)
    };
    let open = |src: &str| {
        let made = construct(
            &compile(src).unwrap_or_else(|e| panic!("{e}")),
            Word::from_u64(1),
            Word::from_u64(0),
        )
        .unwrap();
        assert!(!made.reverted, "{}", pretty(&made.returndata));
        Session {
            runtime: made.returndata,
            storage: made.storage,
            last: None,
        }
    };
    let (a, b, attacker) = (2u64, 3u64, 4u64);
    let deposit = "deposit(uint256,address)";
    let mint = "mint(uint256,address)";
    let withdraw = "withdraw(uint256,address,address)";
    let redeem = "redeem(uint256,address,address)";

    // Metadata, and the ERC-165 ids.
    place(0xa55e7, ASSET);
    let mut v = open(&vault_src(0xa55e7, 0, ""));
    assert_eq!(v.word("asset()", &[]), Word::from_u64(0xa55e7));
    assert_eq!(v.word("decimals()", &[]), Word::from_u64(18));
    assert_eq!(v.word("totalAssets()", &[]), Word::from_u64(0));
    assert_eq!(v.word("maxDeposit(address)", &[w(a)]), top);
    assert_eq!(v.word("maxMint(address)", &[w(a)]), top);
    let erc4626_id = [
        "asset()",
        "totalAssets()",
        "convertToShares(uint256)",
        "convertToAssets(uint256)",
        "maxDeposit(address)",
        "previewDeposit(uint256)",
        "maxMint(address)",
        "previewMint(uint256)",
        "maxWithdraw(address)",
        "previewWithdraw(uint256)",
        "maxRedeem(address)",
        "previewRedeem(uint256)",
        deposit,
        mint,
        withdraw,
        redeem,
    ]
    .iter()
    .fold([0u8; 4], |id, sig| {
        let s = selector(sig);
        [id[0] ^ s[0], id[1] ^ s[1], id[2] ^ s[2], id[3] ^ s[3]]
    });
    let mut id = Word::from_u64(0).to_be_bytes();
    id[..4].copy_from_slice(&erc4626_id);
    assert_eq!(
        v.word(
            "supportsInterface(bytes4)",
            &[Arg::W(Word::from_be_bytes(id))]
        ),
        Word::from_u64(1)
    );

    // Deposit and mint: the asset moves before the shares are minted, so the vault writes
    // nothing until its `transferFrom` has run.
    asset_send(0xa55e7, 1, "mint(address,uint256)", &[w(a), w(10_000)]);
    asset_send(0xa55e7, 1, "mint(address,uint256)", &[w(b), w(10_000)]);
    asset_send(
        0xa55e7,
        a,
        "approve(address,uint256)",
        &[Arg::W(vault_addr), Arg::W(top)],
    );
    assert!(!v.send(a, deposit, &[w(1000), w(0)]));
    v.reverted_with("ERC20InvalidReceiver(address)");
    // The revert undoes the asset's `transferFrom` too.
    assert_eq!(
        asset_send(0xa55e7, 0, "balanceOf(address)", &[Arg::W(vault_addr)]),
        Word::from_u64(0)
    );
    assert!(v.send(a, deposit, &[w(1000), w(a)]));
    assert_eq!(low(load_bytes(&v.returned(), 0)), 1000);
    let out = v.last.as_ref().unwrap();
    let kinds = trace_kinds(&out.trace);
    let call = kinds.iter().position(|k| *k == "call").unwrap();
    assert!(
        kinds[..call].iter().all(|k| *k != "sstore" && *k != "log"),
        "{kinds:?}"
    );
    let deposit_topic = keccak_word(b"Deposit(address,address,uint256,uint256)");
    assert!(out.trace.iter().any(
        |e| matches!(e, Ev::Log { topics } if topics[0] == deposit_topic
        && topics[1] == Word::from_u64(a) && topics[2] == Word::from_u64(a))
    ));
    assert_eq!(v.word("balanceOf(address)", &[w(a)]), Word::from_u64(1000));
    assert_eq!(v.word("totalAssets()", &[]), Word::from_u64(1000));
    // Without an allowance the asset's own error comes back.
    assert!(!v.send(b, deposit, &[w(1), w(b)]));
    v.reverted_with("ERC20InsufficientAllowance(address,uint256,uint256)");

    // A donation makes the rate uneven: 1007 assets for 1000 shares, and one virtual
    // share and asset. Each preview rounds against the caller.
    asset_send(
        0xa55e7,
        b,
        "transfer(address,uint256)",
        &[Arg::W(vault_addr), w(7)],
    );
    let (assets, supply) = (1007u128, 1000u128);
    let to_shares =
        |x: u128, up: bool| (x * (supply + 1) + if up { assets } else { 0 }) / (assets + 1);
    let to_assets =
        |x: u128, up: bool| (x * (assets + 1) + if up { supply } else { 0 }) / (supply + 1);
    for x in [0u128, 1, 10, 999, 12_345] {
        assert_eq!(
            low(v.word("convertToShares(uint256)", &[n(x)])),
            to_shares(x, false),
            "{x}"
        );
        assert_eq!(
            low(v.word("previewDeposit(uint256)", &[n(x)])),
            to_shares(x, false),
            "{x}"
        );
        assert_eq!(
            low(v.word("previewWithdraw(uint256)", &[n(x)])),
            to_shares(x, true),
            "{x}"
        );
        assert_eq!(
            low(v.word("convertToAssets(uint256)", &[n(x)])),
            to_assets(x, false),
            "{x}"
        );
        assert_eq!(
            low(v.word("previewRedeem(uint256)", &[n(x)])),
            to_assets(x, false),
            "{x}"
        );
        assert_eq!(
            low(v.word("previewMint(uint256)", &[n(x)])),
            to_assets(x, true),
            "{x}"
        );
    }
    assert_eq!(low(v.word("previewWithdraw(uint256)", &[w(10)])), 10);
    assert_eq!(low(v.word("previewMint(uint256)", &[w(10)])), 11);
    // A mint takes the rounded-up assets.
    assert!(v.send(a, mint, &[w(10), w(b)]));
    assert_eq!(low(load_bytes(&v.returned(), 0)), 11);
    assert_eq!(v.word("balanceOf(address)", &[w(b)]), Word::from_u64(10));
    assert_eq!(v.word("totalAssets()", &[]), Word::from_u64(1018));

    // Withdraw and redeem, up to `maxWithdraw` and `maxRedeem`.
    let (assets, supply) = (1018u128, 1010u128);
    let most = (1000 * (assets + 1)) / (supply + 1);
    assert_eq!(low(v.word("maxWithdraw(address)", &[w(a)])), most);
    assert_eq!(low(v.word("maxRedeem(address)", &[w(a)])), 1000);
    assert!(!v.send(a, withdraw, &[n(most + 1), w(a), w(a)]));
    v.reverted_with("ERC4626ExceededMaxWithdraw(address,uint256,uint256)");
    assert_eq!(
        &v.returned()[4..],
        &encode_args("", &[w(a), n(most + 1), n(most)])[4..]
    );
    assert!(!v.send(a, redeem, &[w(1001), w(a), w(a)]));
    v.reverted_with("ERC4626ExceededMaxRedeem(address,uint256,uint256)");
    assert_eq!(
        &v.returned()[4..],
        &encode_args("", &[w(a), w(1001), w(1000)])[4..]
    );
    let shares = (100 * (supply + 1) + assets) / (assets + 1);
    assert!(v.send(a, withdraw, &[w(100), w(5), w(a)]));
    assert_eq!(low(load_bytes(&v.returned(), 0)), shares);
    let withdraw_topic = keccak_word(b"Withdraw(address,address,address,uint256,uint256)");
    let out = v.last.as_ref().unwrap();
    assert!(out.trace.iter().any(|e| matches!(e, Ev::Log { topics } if topics[0] == withdraw_topic
        && topics[1] == Word::from_u64(a) && topics[2] == Word::from_u64(5) && topics[3] == Word::from_u64(a))));
    assert_eq!(
        asset_send(0xa55e7, 0, "balanceOf(address)", &[w(5)]),
        Word::from_u64(100)
    );
    assert_eq!(low(v.word("balanceOf(address)", &[w(a)])), 1000 - shares);
    // Someone else's shares need their allowance, which a redemption spends.
    assert!(!v.send(b, redeem, &[w(5), w(b), w(a)]));
    v.reverted_with("ERC20InsufficientAllowance(address,uint256,uint256)");
    assert!(v.send(a, "approve(address,uint256)", &[w(b), w(8)]));
    assert!(v.send(b, redeem, &[w(5), w(b), w(a)]));
    assert_eq!(
        v.word("allowance(address,address)", &[w(a), w(b)]),
        Word::from_u64(3)
    );
    assert!(!v.send(b, redeem, &[w(5), w(b), w(a)]));
    v.reverted_with("ERC20InsufficientAllowance(address,uint256,uint256)");
    assert!(!v.send(a, withdraw, &[w(1), w(0), w(a)]));

    // The first-depositor attack: deposit 1 wei, donate a fortune, and round the next
    // deposit down. The virtual share and asset make it cost the attacker more than the
    // victim loses, and an offset of 6 leaves the victim's loss negligible.
    for (at, offset) in [(0xa1u64, 0u8), (0xa2, 6)] {
        place(at, ASSET);
        let mut v = open(&vault_src(at, offset, ""));
        let vs = 10u128.pow(u32::from(offset));
        assert_eq!(low(v.word("decimals()", &[])), 18 + u128::from(offset));
        let (fortune, stake) = (10u128.pow(18), 10u128.pow(18));
        asset_send(
            at,
            1,
            "mint(address,uint256)",
            &[w(attacker), n(fortune + 1)],
        );
        asset_send(at, 1, "mint(address,uint256)", &[w(b), n(stake)]);
        asset_send(
            at,
            attacker,
            "approve(address,uint256)",
            &[Arg::W(vault_addr), Arg::W(top)],
        );
        asset_send(
            at,
            b,
            "approve(address,uint256)",
            &[Arg::W(vault_addr), Arg::W(top)],
        );
        assert!(v.send(attacker, deposit, &[w(1), w(attacker)]));
        assert_eq!(low(load_bytes(&v.returned(), 0)), vs);
        asset_send(
            at,
            attacker,
            "transfer(address,uint256)",
            &[Arg::W(vault_addr), n(fortune)],
        );
        assert!(v.send(b, deposit, &[n(stake), w(b)]));
        let victim = low(load_bytes(&v.returned(), 0));
        assert_eq!(victim, stake * (vs + vs) / (fortune + 1 + 1));
        assert!(victim > 0);
        let theirs = low(v.word("balanceOf(address)", &[w(attacker)]));
        assert!(v.send(attacker, redeem, &[n(theirs), w(attacker), w(attacker)]));
        let back = low(load_bytes(&v.returned(), 0));
        let kept = low(v.word("previewRedeem(uint256)", &[n(victim)]));
        let (attacker_loss, victim_loss) = (fortune + 1 - back, stake - kept);
        assert!(attacker_loss > victim_loss, "{attacker_loss} {victim_loss}");
        if offset == 6 {
            assert!(victim_loss * 1_000_000 < stake, "{victim_loss}");
        }
    }

    // A cap written around the internals, as the docs show.
    place(0xa3, ASSET);
    let capped = r#"
  error Cap of uint;

  view function depositLimit() : uint is {
    var room : uint := 0;
    if ERC4626.heldAssets() < 500 then {
      room := 500 - ERC4626.heldAssets();
    }
  } with room

  external view function maxDeposit(const receiver : address) : uint is
    depositLimit()

  external function deposit(const assets : uint; const receiver : address) : uint
    raises ERC4626ExceededMaxDeposit | SafeERC20FailedOperation | ERC20InvalidReceiver
      | ERC20InsufficientBalance | forwarded
  is {
    const most : uint := depositLimit();
    assert(assets <= most, ERC4626ExceededMaxDeposit { receiver = receiver; assets = assets; max = most; });
    const shares : uint := ERC4626.sharesFor(assets, false);
    ERC4626.depositAs(Evm.sender(), receiver, assets, shares);
  } with shares
"#;
    let src = vault_src(0xa3, 0, capped)
        .replace("use ERC4626 exposing IERC4626, {", "use ERC4626 exposing {\n    view function asset() : address;\n    view function totalAssets() : uint;\n    view function convertToShares(assets : uint) : uint;\n    view function convertToAssets(shares : uint) : uint;\n    view function previewDeposit(assets : uint) : uint;\n    view function maxMint(receiver : address) : uint;\n    view function previewMint(shares : uint) : uint;\n    view function maxWithdraw(owner : address) : uint;\n    view function previewWithdraw(assets : uint) : uint;\n    view function maxRedeem(owner : address) : uint;\n    view function previewRedeem(shares : uint) : uint;\n    function mint(shares : uint; receiver : address) : uint\n      raises ERC4626ExceededMaxMint | SafeERC20FailedOperation | ERC20InvalidReceiver | ERC20InsufficientBalance | forwarded;\n    function withdraw(assets : uint; receiver : address; owner : address) : uint\n      raises ERC4626ExceededMaxWithdraw | ERC20InsufficientAllowance | ERC20InvalidApprover | ERC20InvalidSpender | ERC20InvalidSender | ERC20InsufficientBalance | SafeERC20FailedOperation | forwarded;\n    function redeem(shares : uint; receiver : address; owner : address) : uint\n      raises ERC4626ExceededMaxRedeem | ERC20InsufficientAllowance | ERC20InvalidApprover | ERC20InvalidSpender | ERC20InvalidSender | ERC20InsufficientBalance | SafeERC20FailedOperation | forwarded;");
    let mut v = open(&src);
    asset_send(0xa3, 1, "mint(address,uint256)", &[w(a), w(1000)]);
    asset_send(
        0xa3,
        a,
        "approve(address,uint256)",
        &[Arg::W(vault_addr), Arg::W(top)],
    );
    assert!(v.send(a, deposit, &[w(300), w(a)]));
    assert_eq!(v.word("maxDeposit(address)", &[w(a)]), Word::from_u64(200));
    assert!(!v.send(a, deposit, &[w(201), w(a)]));
    v.reverted_with("ERC4626ExceededMaxDeposit(address,uint256,uint256)");
    assert_eq!(
        &v.returned()[4..],
        &encode_args("", &[w(a), w(201), w(200)])[4..]
    );
    assert!(v.send(a, deposit, &[w(200), w(a)]));
    assert_eq!(v.word("maxDeposit(address)", &[w(a)]), Word::from_u64(0));

    // An asset whose transfers return nothing, with six decimals.
    place(0xa4, QUIET);
    let mut v = open(&vault_src(0xa4, 0, ""));
    assert_eq!(v.word("decimals()", &[]), Word::from_u64(6));
    asset_send(0xa4, 1, "mint(address,uint256)", &[w(a), w(50)]);
    asset_send(
        0xa4,
        a,
        "approve(address,uint256)",
        &[Arg::W(vault_addr), w(50)],
    );
    assert!(v.send(a, deposit, &[w(50), w(a)]));
    assert_eq!(v.word("totalAssets()", &[]), Word::from_u64(50));
    assert!(v.send(a, redeem, &[w(20), w(b), w(a)]));
    assert_eq!(
        asset_send(0xa4, 0, "balanceOf(address)", &[w(b)]),
        Word::from_u64(20)
    );

    // An asset whose transfers answer `false` fails either way, and one without
    // `decimals` counts 18.
    place(0xa5, REFUSING);
    let mut v = open(&vault_src(0xa5, 0, ""));
    assert_eq!(v.word("decimals()", &[]), Word::from_u64(18));
    assert!(!v.send(a, deposit, &[w(1), w(a)]));
    v.reverted_with("SafeERC20FailedOperation(address)");
    assert_eq!(&v.returned()[4..], &encode_args("", &[w(0xa5)])[4..]);
    assert!(!v.send(a, mint, &[w(1), w(a)]));
    v.reverted_with("SafeERC20FailedOperation(address)");
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// Calls `sig` on `runtime` with ABI-encoded `args`, failing on a revert.
fn ok_call(runtime: &[u8], sig: &str, args: &[Arg]) -> Vec<u8> {
    let out = exec(
        runtime,
        &encode_args(sig, args),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect(sig);
    assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
    out.returndata
}

fn words_of(data: &[u8]) -> Vec<u64> {
    data.chunks(32)
        .map(|w| word_usize(Word::from_be_bytes(w.try_into().unwrap())).unwrap() as u64)
        .collect()
}

/// `Create.computeAddress`, built for Prague and for Osaka, against `cast compute-address`
/// and an RLP encoder of its own.
#[test]
fn stdlib_create_addresses() {
    for evm in [crate::EvmVersion::Prague, crate::EvmVersion::Osaka] {
        create_addresses(evm);
    }
}

fn create_addresses(evm: crate::EvmVersion) {
    let src = r#"
import "std/utils/create";

contract T is {
  use Create;
  storage is record { n : uint; }
  external pure function compute(const deployer : address; const nonce : uint) : address is
    Create.computeAddress(deployer, nonce)
}
"#;
    let opts = Options {
        evm,
        ..Options::default()
    };
    let out = crate::compile(&memory(src), Path::new(ENTRY), &opts)
        .and_then(crate::Output::single)
        .map_err(first)
        .expect("compile");
    let runtime = deploy(&out.bytecode).expect("deploy");
    let deployer = Word::from_hex("6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0").unwrap();
    let compute = |deployer: Word, nonce: Word| {
        load_bytes(
            &call(&runtime, "compute(address,uint256)", &[deployer, nonce]).returndata,
            0,
        )
    };
    for (nonce, want) in [
        (0u64, "cd234a471b72ba2f1ccf0a70fcaba648a5eecd8d"),
        (1, "343c43a37d37dff08ae8c4a11544c718abb4fcf8"),
        (127, "06d9a77f5e4b311bae8d559db9cdb4df94104aa0"),
        (128, "08e190dcb7b73f5fcdabb43e102215c83659a76d"),
        (255, "3ef7c1a519e4b4431e317d7839340e3139b03c65"),
        (256, "3837c1ae70354f670550c746580199ac6a73cb0a"),
        (65535, "65260eecff4edebabe134f76f1f39a91defde56c"),
        (4294967295, "4c9958390a81acc68a5f19aa8e6188bebbbeefd7"),
        (u64::MAX, "9bc924993b60399df164c3763a964301d3db95ca"),
    ] {
        assert_eq!(
            compute(deployer, Word::from_u64(nonce)),
            Word::from_hex(want).unwrap(),
            "nonce {nonce}"
        );
    }
    // RLP([deployer, nonce]) for nonces of every length, up to 32 bytes.
    let reference = |deployer: Word, nonce: Word| {
        let bytes = nonce.to_be_bytes();
        let digits: Vec<u8> = bytes.iter().copied().skip_while(|&b| b == 0).collect();
        let item = match digits.as_slice() {
            [] => vec![0x80],
            [b] if *b < 0x80 => vec![*b],
            d => [vec![0x80 + d.len() as u8], d.to_vec()].concat(),
        };
        let mut rlp = vec![0xc0 + 21 + item.len() as u8, 0x94];
        rlp.extend(&deployer.to_be_bytes()[12..]);
        rlp.extend(item);
        let mut out = [0u8; 32];
        out[12..].copy_from_slice(&crate::keccak::keccak256(&rlp)[12..]);
        Word::from_be_bytes(out)
    };
    for bits in (0..=256).step_by(7).chain([8, 64, 255, 256]) {
        let nonce = if bits == 0 {
            Word::from_u64(0)
        } else {
            Word::from_u64(0).not().shr(256 - bits)
        };
        for nonce in [nonce, nonce.shr(1).bitxor(Word::from_u64(0x5a))] {
            assert_eq!(
                compute(deployer, nonce),
                reference(deployer, nonce),
                "{nonce:?}"
            );
        }
    }
}

/// `BlockHash.blockHash` reads `BLOCKHASH` in its window, and the EIP-2935 contract
/// before it, with zero where neither knows the block.
#[test]
fn stdlib_block_hash() {
    fn history(input: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
        let n = Word::from_be_bytes(input.try_into().map_err(|_| Vec::new())?);
        if n.lt(Word::from_u64(500)) {
            return Err(Vec::new());
        }
        Ok(n.not().to_be_bytes().to_vec())
    }
    let contract = Word::from_hex("0000F90827F1C53a10cb7A02335B175320002935").unwrap();
    MOCKS.with(|m| m.borrow_mut().insert(contract, history as Mock));
    let src = r#"
import "std/utils/block_hash";

contract T is {
  use BlockHash;
  storage is record { n : uint; }
  external view function hash(const n : uint) : bytes32 is
    BlockHash.blockHash(n)
}
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    BLOCK.with(|b| b.set(1000));
    let hash = |n: Word| load_bytes(&call(&runtime, "hash(uint256)", &[n]).returndata, 0);
    let recent =
        |n: u64| Word::from_be_bytes(crate::keccak::keccak256(&Word::from_u64(n).to_be_bytes()));
    assert_eq!(hash(Word::from_u64(999)), recent(999));
    assert_eq!(hash(Word::from_u64(744)), recent(744));
    assert_eq!(hash(Word::from_u64(1000)), Word::from_u64(0));
    assert_eq!(hash(Word::from_u64(5000)), Word::from_u64(0));
    assert_eq!(hash(Word::from_u64(743)), Word::from_u64(743).not());
    assert_eq!(hash(Word::from_u64(500)), Word::from_u64(500).not());
    // The history contract reverts before its window: zero, as Solady answers.
    assert_eq!(hash(Word::from_u64(499)), Word::from_u64(0));
    // `n + 256` wraps, so the history contract is asked, as in Solady.
    assert_eq!(hash(Word::from_u64(0).not()), Word::from_u64(0));
    let out = call(&runtime, "hash(uint256)", &[Word::from_u64(743)]);
    assert!(
        out.detail.iter().any(|d| d.starts_with("static")),
        "{:?}",
        out.detail
    );
    BLOCK.with(|b| b.set(100));
}

/// `String.lower`, `upper`, `escapeJson`, and `escapeHtml`, with Solady's vectors.
#[test]
fn string_builtins() {
    let src = r#"import "std/string"; import "std/base64"; 
storage is record { last : string; }

external pure function lower(const s : string) : string is String.lower(s)
external pure function upper(const s : string) : string is String.upper(s)
external pure function json(const s : string) : string is String.escapeJson(s)
external pure function html(const s : string) : string is String.escapeHtml(s)

(* Every helper that uses the table space at address 0, in one expression. *)
external pure function mixed(const s : bytes) : string is
  String.concat(String.escapeJson(string(s)), "|", Base64.encode(s), "|", String.escapeHtml(string(s)), "|", String.upper(string(s)))

external function keep(const s : string) is {
  storage.last := String.escapeJson(s);
}

external view function kept() : string is storage.last
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let run = |f: &str, s: &[u8]| {
        abi_string_value(&ok_call(
            &runtime,
            &format!("{f}(string)"),
            &[Arg::B(s.to_vec())],
        ))
    };
    for (s, want) in [
        (&b""[..], &b""[..]),
        (b"abc", b"abc"),
        (b"abc\"_123", b"abc\\\"_123"),
        (b"abc\\_123", b"abc\\\\_123"),
        (b"abc\x08_123", b"abc\\b_123"),
        (b"abc\x0c_123", b"abc\\f_123"),
        (b"abc\n_123", b"abc\\n_123"),
        (b"abc\r_123", b"abc\\r_123"),
        (b"abc\t_123", b"abc\\t_123"),
        (b"\x00\x01\x1f\x7f", b"\\u0000\\u0001\\u001f\x7f"),
    ] {
        assert_eq!(run("json", s), want, "{s:?}");
    }
    for (s, want) in [
        (&b""[..], &b""[..]),
        (b"abc", b"abc"),
        (b"abc\"_123", b"abc&quot;_123"),
        (b"abc&_123", b"abc&amp;_123"),
        (b"abc'_123", b"abc&#39;_123"),
        (b"abc<_123", b"abc&lt;_123"),
        (b"abc>_123", b"abc&gt;_123"),
    ] {
        assert_eq!(run("html", s), want, "{s:?}");
    }
    assert_eq!(run("lower", b"@AZ["), b"@az[");
    // Every byte, ASCII and not, over lengths around a word.
    let all: Vec<u8> = (0..=255u8).collect();
    for len in [1, 31, 32, 33, 64, 100, 256] {
        let s: Vec<u8> = all
            .iter()
            .cycle()
            .skip(len * 7)
            .take(len)
            .copied()
            .collect();
        let lower: Vec<u8> = s
            .iter()
            .map(|&b| if b.is_ascii_uppercase() { b + 32 } else { b })
            .collect();
        let upper: Vec<u8> = s
            .iter()
            .map(|&b| if b.is_ascii_lowercase() { b - 32 } else { b })
            .collect();
        assert_eq!(run("lower", &s), lower);
        assert_eq!(run("upper", &s), upper);
        let mut json = Vec::new();
        let mut html = Vec::new();
        for &b in &s {
            match b {
                b'"' | b'\\' => json.extend([b'\\', b]),
                8 => json.extend(b"\\b"),
                9 => json.extend(b"\\t"),
                10 => json.extend(b"\\n"),
                12 => json.extend(b"\\f"),
                13 => json.extend(b"\\r"),
                0..=0x1f => json.extend(format!("\\u{b:04x}").as_bytes()),
                _ => json.push(b),
            }
            match b {
                b'"' => html.extend(b"&quot;"),
                b'&' => html.extend(b"&amp;"),
                b'\'' => html.extend(b"&#39;"),
                b'<' => html.extend(b"&lt;"),
                b'>' => html.extend(b"&gt;"),
                _ => html.push(b),
            }
        }
        assert_eq!(run("json", &s), json, "{len}");
        assert_eq!(run("html", &s), html, "{len}");
    }
    let mixed = abi_string_value(&ok_call(
        &runtime,
        "mixed(bytes)",
        &[Arg::B(b"<\"a\">\n".to_vec())],
    ));
    assert_eq!(
        mixed,
        b"<\\\"a\\\">\\n|PCJhIj4K|&lt;&quot;a&quot;&gt;\n|<\"A\">\n".to_vec()
    );
    let mut d = Session {
        runtime,
        storage: HashMap::new(),
        last: None,
    };
    assert!(d.send(1, "keep(string)", &[Arg::B(b"say \"hi\"".repeat(5))]));
    d.send(1, "kept()", &[]);
    assert_eq!(abi_string_value(&d.returned()), b"say \\\"hi\\\"".repeat(5));
}

/// `Strings`, with Solady's vectors.
/// `String.indexOf` and `Strings.replace` answer as a byte-by-byte search does, over
/// subjects and needles on both sides of a word, from every offset.
#[test]
fn string_search_matches_a_naive_search() {
    let src = r#"
import "std/utils/strings";
import "std/string";

contract T is {
  use Strings;
  storage is record { n : uint; }
  external pure function indexOf(const s : bytes; const n : bytes; const from : uint) : uint is String.indexOf(s, n, from)
  external pure function replace(const s : string; const n : string; const r : string) : string is Strings.replace(s, n, r)
  external pure function indexIn(const s : bytes; const a : uint; const b : uint; const n : bytes; const from : uint) : uint is
    String.indexOf(s[a:b], n, from)
  external pure function replaceIn(const s : bytes; const a : uint; const b : uint; const n : string; const r : string) : string is
    String.replace(string(s[a:b]), n, r)
}
"#;
    fn next(seed: &mut u64) -> u64 {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        *seed
    }
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    for round in 0..400 {
        let len = (next(&mut seed) % 80) as usize;
        let subject: Vec<u8> = (0..len)
            .map(|_| b"ab"[(next(&mut seed) % 2) as usize])
            .collect();
        let n = match round % 4 {
            0 => (next(&mut seed) % 4) as usize,
            1 => (next(&mut seed) % 40) as usize,
            _ => 30 + (next(&mut seed) % 5) as usize,
        };
        let needle: Vec<u8> = if n <= len && round % 3 > 0 {
            let at = (next(&mut seed) % (len - n + 1) as u64) as usize;
            subject[at..at + n].to_vec()
        } else {
            (0..n)
                .map(|_| b"ab"[(next(&mut seed) % 2) as usize])
                .collect()
        };
        let from = next(&mut seed) % (len as u64 + 3);
        let want = if needle.is_empty() {
            Some(from.min(len as u64))
        } else {
            (from as usize..(len + 1).saturating_sub(needle.len()))
                .find(|&i| subject[i..i + needle.len()] == needle[..])
                .map(|i| i as u64)
        };
        let got = load_bytes(
            &ok_call(
                &runtime,
                "indexOf(bytes,bytes,uint256)",
                &[
                    Arg::B(subject.clone()),
                    Arg::B(needle.clone()),
                    Arg::W(Word::from_u64(from)),
                ],
            ),
            0,
        );
        assert_eq!(
            got,
            want.map_or(Word::from_u64(0).not(), Word::from_u64),
            "{:?} {:?} {from}",
            String::from_utf8_lossy(&subject),
            String::from_utf8_lossy(&needle)
        );
        // The same subject as a slice, between bytes the search must not see.
        let pad = round % 3 * 17;
        let framed = [&b"z".repeat(pad)[..], &subject, &b"zz"[..]].concat();
        let (a, b) = (
            Word::from_u64(pad as u64),
            Word::from_u64((pad + len) as u64),
        );
        let got = load_bytes(
            &ok_call(
                &runtime,
                "indexIn(bytes,uint256,uint256,bytes,uint256)",
                &[
                    Arg::B(framed.clone()),
                    Arg::W(a),
                    Arg::W(b),
                    Arg::B(needle.clone()),
                    Arg::W(Word::from_u64(from)),
                ],
            ),
            0,
        );
        assert_eq!(
            got,
            want.map_or(Word::from_u64(0).not(), Word::from_u64),
            "sliced {from}"
        );
        let replacement: Vec<u8> = (0..next(&mut seed) % 40)
            .map(|k| b'x' + (k % 3) as u8)
            .collect();
        let mut expect = Vec::new();
        if needle.is_empty() {
            for &c in &subject {
                expect.extend(&replacement);
                expect.push(c);
            }
            expect.extend(&replacement);
        } else {
            let mut i = 0;
            while i < subject.len() {
                if subject[i..].starts_with(&needle) {
                    expect.extend(&replacement);
                    i += needle.len();
                } else {
                    expect.push(subject[i]);
                    i += 1;
                }
            }
        }
        let out = ok_call(
            &runtime,
            "replace(string,string,string)",
            &[
                Arg::B(subject.clone()),
                Arg::B(needle.clone()),
                Arg::B(replacement.clone()),
            ],
        );
        assert_eq!(
            abi_string_value(&out),
            expect,
            "replace {:?}",
            String::from_utf8_lossy(&subject)
        );
        let out = ok_call(
            &runtime,
            "replaceIn(bytes,uint256,uint256,string,string)",
            &[
                Arg::B(framed),
                Arg::W(a),
                Arg::W(b),
                Arg::B(needle.clone()),
                Arg::B(replacement),
            ],
        );
        assert_eq!(abi_string_value(&out), expect, "sliced replace");
    }
}

/// `out := Bytes.concat(out, ...)` grows `out` in place when it ends at the heap top, and
/// copies it when something was allocated since or another value shares its blob.
#[test]
fn appends_grow_in_place_or_copy() {
    let src = r#"
import "std/bytes";

contract T is {
  storage is record { n : uint; }
  external pure function build(const src : bytes; const n : uint; const every : uint) : bytes is {
    var out : bytes := "";
    for i : uint in 0 .. n do {
      const k : uint := i % src.length;
      if every > 0 and i % every = 0 then {
        out := Bytes.concat(out, Bytes.concat(src[k:], "!"));
      } else {
        out := Bytes.concat(out, src[:k], bytes1(uint8(i)));
      }
    }
  } with out
  external pure function shared(const p : bytes) : bytes is {
    var a : bytes := Bytes.concat("x", p);
    const b : bytes := a;
    a := Bytes.concat(a, "z");
  } with Bytes.concat(b, "|", a)
}
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let text = b"abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ".to_vec();
    for (n, every) in [
        (0u64, 0u64),
        (1, 0),
        (5, 0),
        (40, 0),
        (40, 3),
        (40, 1),
        (70, 7),
    ] {
        let mut want = Vec::new();
        for i in 0..n as usize {
            let k = i % text.len();
            if every > 0 && i % every as usize == 0 {
                want.extend(&text[k..]);
                want.push(b'!');
            } else {
                want.extend(&text[..k]);
                want.push(i as u8);
            }
        }
        let out = ok_call(
            &runtime,
            "build(bytes,uint256,uint256)",
            &[
                Arg::B(text.clone()),
                Arg::W(Word::from_u64(n)),
                Arg::W(Word::from_u64(every)),
            ],
        );
        assert_eq!(abi_string_value(&out), want, "{n} {every}");
    }
    let out = ok_call(&runtime, "shared(bytes)", &[Arg::B(b"yy".to_vec())]);
    assert_eq!(abi_string_value(&out), b"xyy|xyyz");
}

#[test]
fn stdlib_strings() {
    let src = r#"
import "std/utils/strings";

contract T is {
  use Strings;
  storage is record { n : uint; }
  external pure function indexOf(const s : string; const n : string; const from : uint) : uint is Strings.indexOf(s, n, from)
  external pure function indexOf(const s : string; const n : string) : uint is Strings.indexOf(s, n)
  external pure function contains(const s : string; const n : string) : bool is Strings.contains(s, n)
  external pure function startsWith(const s : string; const n : string) : bool is Strings.startsWith(s, n)
  external pure function endsWith(const s : string; const n : string) : bool is Strings.endsWith(s, n)
  external pure function replace(const s : string; const n : string; const r : string) : string is Strings.replace(s, n, r)
}
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let b = |s: &str| Arg::B(s.as_bytes().to_vec());
    let word = |sig: &str, args: &[Arg]| load_bytes(&ok_call(&runtime, sig, args), 0);
    let not_found = Word::from_u64(0).not();
    let subject = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
    for (needle, from, want) in [
        ("", 16, Some(16)),
        ("", 17, Some(17)),
        ("", 52, Some(52)),
        ("", 53, Some(52)),
        ("", 555, Some(52)),
        ("abc", 0, Some(0)),
        ("abc", 1, None),
        ("qrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ", 16, Some(16)),
        ("qrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ", 17, None),
    ] {
        assert_eq!(
            word(
                "indexOf(string,string,uint256)",
                &[b(subject), b(needle), w(from)]
            ),
            want.map_or(not_found, Word::from_u64),
            "{needle} {from}"
        );
    }
    for (s, needle, want) in [
        (subject, "", Some(0)),
        (subject, "bcd", Some(1)),
        (subject, "XYZ", Some(49)),
        (subject, "qrstuvwxyzABCDEFGHIJKLMNOPQRSTUVW", Some(16)),
        (subject, "qrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ", Some(16)),
        ("abcabcabc", "abc", Some(0)),
        ("a", "bcd", None),
        ("accd", "bcd", None),
        ("", "bcd", None),
    ] {
        assert_eq!(
            word("indexOf(string,string)", &[b(s), b(needle)]),
            want.map_or(not_found, Word::from_u64),
            "{s} {needle}"
        );
        assert_eq!(
            word("contains(string,string)", &[b(s), b(needle)]),
            Word::from_u64(u64::from(want.is_some()))
        );
    }
    assert_eq!(
        word(
            "indexOf(string,string,uint256)",
            &[b("abcabcabc"), b("abc"), w(1)]
        ),
        Word::from_u64(3)
    );
    for (s, needle, starts, ends) in [
        (subject, "abc", true, false),
        (subject, "abcdefghijklmnopqrstuvwxyzABCDEFG", true, false),
        (subject, "bcd", false, false),
        (subject, "XYZ", false, true),
        (
            subject,
            "pqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ",
            false,
            true,
        ),
        (
            subject,
            "opqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXY",
            false,
            false,
        ),
        ("", "", true, true),
        ("bc", "", true, true),
        ("bc", "bc", true, true),
        ("bc", "abc", false, false),
        ("", "abc", false, false),
    ] {
        assert_eq!(
            word("startsWith(string,string)", &[b(s), b(needle)]),
            Word::from_u64(u64::from(starts)),
            "{s} {needle}"
        );
        assert_eq!(
            word("endsWith(string,string)", &[b(s), b(needle)]),
            Word::from_u64(u64::from(ends)),
            "{s} {needle}"
        );
    }
    let replace = |s: &str, n: &str, r: &str| {
        String::from_utf8(abi_string_value(&ok_call(
            &runtime,
            "replace(string,string,string)",
            &[b(s), b(n), b(r)],
        )))
        .unwrap()
    };
    for (s, n, r, want) in [
        ("abc", "", "_@", "_@a_@b_@c_@"),
        ("abc", "a", "_", "_bc"),
        ("abc", "b", "_", "a_c"),
        ("abc", "c", "_", "ab_"),
        ("abc", "ab", "_", "_c"),
        ("abc", "bc", "_", "a_"),
        ("abc", "ac", "_", "abc"),
        ("abc", "a", "", "bc"),
        ("abc", "", "", "abc"),
        ("abc", "d", "x", "abc"),
        ("aaaa", "aa", "b", "bb"),
        (
            "70708741044725766535585242414884609539555049888764130733849700923779599488691391677696419266840",
            "46095395550498887641307338497009",
            "320807383223517906783031356692334377159141",
            "707087410447257665355852424148832080738322351790678303135669233437715914123779599488691391677696419266840",
        ),
        (
            "01234567890123456789012345678901_search_search_search_search_search_search_23456789012345678901234567890123456789_search_search_search_search_search_search",
            "search_search_search_search_search_search",
            "REPLACEMENT_REPLACEMENT_REPLACEMENT_REPLACEMENT_REPLACEMENT",
            "01234567890123456789012345678901_REPLACEMENT_REPLACEMENT_REPLACEMENT_REPLACEMENT_REPLACEMENT_23456789012345678901234567890123456789_REPLACEMENT_REPLACEMENT_REPLACEMENT_REPLACEMENT_REPLACEMENT",
        ),
    ] {
        assert_eq!(replace(s, n, r), want, "{s} {n} {r}");
    }
    // Needles past a word whose first 32 bytes match where the rest doesn't, against a
    // plain search.
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = |n: u64| {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed % n
    };
    for _ in 0..40 {
        let text = |len: u64, next: &mut dyn FnMut(u64) -> u64| -> String {
            (0..len)
                .map(|_| if next(8) == 0 { 'b' } else { 'a' })
                .collect()
        };
        let s = text(next(80), &mut next);
        let needle = text(next(40), &mut next);
        let from = next(8);
        let want = if needle.is_empty() {
            Some(from.min(s.len() as u64))
        } else {
            (from as usize..s.len())
                .find(|&i| s[i..].starts_with(&needle))
                .map(|i| i as u64)
        };
        assert_eq!(
            word(
                "indexOf(string,string,uint256)",
                &[b(&s), b(&needle), w(from)]
            ),
            want.map_or(not_found, Word::from_u64),
            "{s} {needle} {from}"
        );
        if !needle.is_empty() {
            assert_eq!(
                replace(&s, &needle, "_"),
                s.replace(&needle, "_"),
                "{s} {needle}"
            );
        }
    }
}

/// `DateTime`, with Solady's vectors.
#[test]
fn stdlib_date_time() {
    let src = r#"
import "std/utils/date_time";

contract T is {
  use DateTime;
  storage is record { n : uint; }
  external pure function dateToEpochDay(const y : uint; const m : uint; const d : uint) : uint is DateTime.dateToEpochDay(y, m, d)
  external pure function epochDayToDate(const e : uint) : (uint, uint, uint) is DateTime.epochDayToDate(e)
  external pure function dateToTimestamp(const y : uint; const m : uint; const d : uint) : timestamp is DateTime.dateToTimestamp(y, m, d)
  external pure function timestampToDate(const t : timestamp) : (uint, uint, uint) is DateTime.timestampToDate(t)
  external pure function dateTimeToTimestamp(const y : uint; const m : uint; const d : uint; const h : uint; const mi : uint; const s : uint) : timestamp is DateTime.dateTimeToTimestamp(y, m, d, h, mi, s)
  external pure function timestampToDateTime(const t : timestamp) : (uint, uint, uint, uint, uint, uint) is DateTime.timestampToDateTime(t)
  external pure function isLeapYear(const y : uint) : bool is DateTime.isLeapYear(y)
  external pure function daysInMonth(const y : uint; const m : uint) : uint is DateTime.daysInMonth(y, m)
  external pure function weekday(const t : timestamp) : uint is DateTime.weekday(t)
  external pure function isSupportedDate(const y : uint; const m : uint; const d : uint) : bool is DateTime.isSupportedDate(y, m, d)
  external pure function addYears(const t : timestamp; const n : uint) : timestamp is DateTime.addYears(t, n)
  external pure function subYears(const t : timestamp; const n : uint) : timestamp is DateTime.subYears(t, n)
  external pure function addMonths(const t : timestamp; const n : uint) : timestamp is DateTime.addMonths(t, n)
  external pure function subMonths(const t : timestamp; const n : uint) : timestamp is DateTime.subMonths(t, n)
  external pure function diffYears(const a : timestamp; const b : timestamp) : uint is DateTime.diffYears(a, b)
  external pure function diffMonths(const a : timestamp; const b : timestamp) : uint is DateTime.diffMonths(a, b)
}
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let words = |sig: &str, args: &[u64]| {
        let args: Vec<Word> = args.iter().map(|&a| Word::from_u64(a)).collect();
        let out = call(&runtime, sig, &args);
        assert!(!out.reverted, "{sig} {args:?}");
        words_of(&out.returndata)
    };
    for (y, m, d, day) in [
        (1970, 1, 1, 0),
        (1970, 1, 2, 1),
        (1970, 2, 1, 31),
        (1970, 3, 1, 59),
        (1970, 4, 1, 90),
        (1970, 5, 1, 120),
        (1970, 6, 1, 151),
        (1970, 7, 1, 181),
        (1970, 8, 1, 212),
        (1970, 9, 1, 243),
        (1970, 10, 1, 273),
        (1970, 11, 1, 304),
        (1970, 12, 1, 334),
        (1970, 12, 31, 364),
        (1971, 1, 1, 365),
        (1980, 11, 3, 3959),
        (2000, 3, 1, 11017),
        (2355, 12, 31, 140982),
        (99999, 12, 31, 35804721),
        (100000, 12, 31, 35805087),
        (604800, 2, 29, 220179195),
        (1667347200, 2, 29, 608985340227),
        (1667952000, 2, 29, 609206238891),
        (0xffffffff, 12, 31, 0x16d3e098039),
    ] {
        assert_eq!(
            words("dateToEpochDay(uint256,uint256,uint256)", &[y, m, d]),
            [day],
            "{y}-{m}-{d}"
        );
        assert_eq!(words("epochDayToDate(uint256)", &[day]), [y, m, d], "{day}");
        assert_eq!(
            words("dateToTimestamp(uint256,uint256,uint256)", &[y, m, d]),
            [day * 86400]
        );
    }
    for (day, y, m, d) in [
        (10987, 2000, 1, 31),
        (18321, 2020, 2, 29),
        (156468, 2398, 5, 25),
    ] {
        assert_eq!(words("epochDayToDate(uint256)", &[day]), [y, m, d]);
    }
    // The last supported timestamp, and the first past it.
    assert_eq!(
        words("timestampToDate(uint256)", &[0x1e18549868c76ff]),
        [0xffffffff, 12, 31]
    );
    assert_ne!(
        words("timestampToDate(uint256)", &[0x1e18549868c76ff + 1]),
        [0xffffffff, 12, 31]
    );
    assert_eq!(
        words("timestampToDateTime(uint256)", &[1709251199]),
        [2024, 2, 29, 23, 59, 59]
    );
    assert_eq!(
        words(
            "dateTimeToTimestamp(uint256,uint256,uint256,uint256,uint256,uint256)",
            &[2024, 2, 29, 23, 59, 59]
        ),
        [1709251199]
    );
    for y in [
        2000, 2024, 2048, 2072, 2104, 2128, 10032, 10124, 10296, 10400, 10916,
    ] {
        assert_eq!(words("isLeapYear(uint256)", &[y]), [1], "{y}");
    }
    for y in [1900, 2100, 2023, 1] {
        assert_eq!(words("isLeapYear(uint256)", &[y]), [0], "{y}");
    }
    for (m, d) in [
        (1, 31),
        (2, 28),
        (3, 31),
        (4, 30),
        (5, 31),
        (6, 30),
        (7, 31),
        (8, 31),
        (9, 30),
        (10, 31),
        (11, 30),
        (12, 31),
    ] {
        assert_eq!(words("daysInMonth(uint256,uint256)", &[2022, m]), [d]);
    }
    assert_eq!(words("daysInMonth(uint256,uint256)", &[2024, 2]), [29]);
    assert_eq!(words("daysInMonth(uint256,uint256)", &[1900, 2]), [28]);
    for (t, day) in [
        (1, 4),
        (86400, 5),
        (86401, 5),
        (172800, 6),
        (259200, 7),
        (345600, 1),
        (432000, 2),
        (518400, 3),
    ] {
        assert_eq!(words("weekday(uint256)", &[t]), [day]);
    }
    for (y, m, d) in [
        (1970, 1, 1),
        (1971, 5, 31),
        (1971, 6, 30),
        (1971, 12, 31),
        (1972, 2, 28),
        (1972, 4, 30),
        (1972, 5, 31),
        (2000, 2, 29),
        (0xffffffff, 5, 31),
    ] {
        assert_eq!(
            words("isSupportedDate(uint256,uint256,uint256)", &[y, m, d]),
            [1],
            "{y}-{m}-{d}"
        );
    }
    for (y, m, d) in [
        (0, 0, 0),
        (1970, 0, 0),
        (1970, 1, 0),
        (1969, 1, 1),
        (1800, 1, 1),
        (1970, 13, 1),
        (1700, 13, 1),
        (1970, 15, 32),
        (1970, 1, 32),
        (1879, 1, 1),
        (1970, 4, 31),
        (1970, 6, 31),
        (1970, 7, 32),
        (2000, 2, 30),
        (0x1_0000_0000, 5, 31),
        (u64::MAX, 5, 31),
    ] {
        assert_eq!(
            words("isSupportedDate(uint256,uint256,uint256)", &[y, m, d]),
            [0],
            "{y}-{m}-{d}"
        );
    }
    // 29 February 2024, 12:34:56: a year on is 28 February, a month on 29 March.
    let t = 1709210096;
    let at = |y, m, d| (words("dateToTimestamp(uint256,uint256,uint256)", &[y, m, d])[0]) + 45296;
    assert_eq!(
        words("addYears(uint256,uint256)", &[t, 1]),
        [at(2025, 2, 28)]
    );
    assert_eq!(
        words("addYears(uint256,uint256)", &[t, 4]),
        [at(2028, 2, 29)]
    );
    assert_eq!(
        words("subYears(uint256,uint256)", &[t, 1]),
        [at(2023, 2, 28)]
    );
    assert_eq!(
        words("addMonths(uint256,uint256)", &[t, 1]),
        [at(2024, 3, 29)]
    );
    assert_eq!(
        words("addMonths(uint256,uint256)", &[t, 23]),
        [at(2026, 1, 29)]
    );
    assert_eq!(
        words("subMonths(uint256,uint256)", &[t, 3]),
        [at(2023, 11, 29)]
    );
    assert_eq!(
        words("subMonths(uint256,uint256)", &[at(2024, 3, 31), 1]),
        [at(2024, 2, 29)]
    );
    assert_eq!(
        words(
            "diffYears(uint256,uint256)",
            &[at(2023, 12, 31), at(2024, 1, 1)]
        ),
        [1]
    );
    assert_eq!(
        words(
            "diffMonths(uint256,uint256)",
            &[at(2023, 12, 31), at(2025, 2, 1)]
        ),
        [14]
    );
    // Solady's `testDateTimeArithmeticReverts`: each panics with an arithmetic error.
    let big = Word::from_u64(0).not().shr(128);
    let half = Word::from_u64(0).not().shr(1);
    for (sig, a, b) in [
        ("addYears(uint256,uint256)", big, half),
        ("subYears(uint256,uint256)", big, half),
        ("diffYears(uint256,uint256)", big, big.shr(1)),
        ("addMonths(uint256,uint256)", big, half),
        ("subMonths(uint256,uint256)", big, half),
        ("diffMonths(uint256,uint256)", big, big.shr(1)),
    ] {
        let out = call(&runtime, sig, &[a, b]);
        assert!(out.reverted, "{sig}");
        assert_eq!(
            load_bytes(&out.returndata, 4),
            Word::from_u64(0x11),
            "{sig}"
        );
    }
}

fn small(w: Word) -> usize {
    let b = w.to_be_bytes();
    usize::from(u16::from_be_bytes([b[30], b[31]]))
}

/// The `bytes` or `string` whose offset is at head word `i` of ABI-encoded results.
fn dynamic_at(ret: &[u8], i: usize) -> Vec<u8> {
    let at = small(load_bytes(ret, 32 * i));
    let len = small(load_bytes(ret, at));
    ret[at + 32..at + 32 + len].to_vec()
}

/// ECDSA's non-reverting recovery, signature checks against accounts and an ERC-1271
/// wallet, multiproofs from `@openzeppelin/merkle-tree`, and ERC-5267.
#[test]
fn stdlib_signatures_and_multiproofs() {
    install_mocks();
    let mut u = Session::new("examples/stdlib/utils.lithe");
    let hexw = |s: &str| Word::from_hex(s).unwrap();
    let zero = Word::from_u64(0);

    let key = Word::from_u64(0xb0b);
    let signer = crate::hash::address_of(key);
    let hash = keccak_word(b"hello");
    let (v, r, s) = crate::hash::sign(hash, key, Word::from_u64(0x77));
    let mut sig = r.to_be_bytes().to_vec();
    sig.extend_from_slice(&s.to_be_bytes());
    sig.push(v);
    let n = hexw("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
    let twin = (if v == 27 { 28 } else { 27 }, n.wrapping_sub(s));
    let mut malleable = r.to_be_bytes().to_vec();
    malleable.extend_from_slice(&twin.1.to_be_bytes());
    malleable.push(twin.0);

    // `tryRecover` answers where `recover` would raise, with zero for `None` here.
    let try_bytes = "tryRecover(bytes32,bytes)";
    assert_eq!(
        u.word(try_bytes, &[Arg::W(hash), Arg::B(sig.clone())]),
        signer
    );
    assert_eq!(
        u.word(try_bytes, &[Arg::W(hash), Arg::B(malleable.clone())]),
        zero
    );
    assert_eq!(
        u.word(try_bytes, &[Arg::W(hash), Arg::B(sig[..64].to_vec())]),
        zero
    );
    assert_eq!(u.word(try_bytes, &[Arg::W(hash), Arg::B(vec![])]), zero);
    let try_vrs = "tryRecoverVrs(bytes32,uint8,bytes32,bytes32)";
    assert_eq!(
        u.word(
            try_vrs,
            &[Arg::W(hash), w(u64::from(v)), Arg::W(r), Arg::W(s)]
        ),
        signer
    );
    assert_eq!(
        u.word(
            try_vrs,
            &[
                Arg::W(hash),
                w(u64::from(twin.0)),
                Arg::W(r),
                Arg::W(twin.1)
            ]
        ),
        zero
    );
    // A `v` the precompile rejects recovers no one.
    assert_eq!(
        u.word(try_vrs, &[Arg::W(hash), w(29), Arg::W(r), Arg::W(s)]),
        zero
    );
    assert!(!u.send(
        0,
        "recoverVrs(bytes32,uint8,bytes32,bytes32)",
        &[Arg::W(hash), w(29), Arg::W(r), Arg::W(s)]
    ));
    u.reverted_with("ECDSAInvalidSignature()");
    // EIP-2098: `v - 27` in the top bit of `s`.
    let vs = if v == 28 {
        s.bitor(Word::from_u64(1).shl(255))
    } else {
        s
    };
    assert_eq!(
        u.word(
            "tryRecoverCompact(bytes32,bytes32,bytes32)",
            &[Arg::W(hash), Arg::W(r), Arg::W(vs)]
        ),
        signer
    );
    assert_eq!(
        u.word(
            "recoverCompact(bytes32,bytes32,bytes32)",
            &[Arg::W(hash), Arg::W(r), Arg::W(vs)]
        ),
        signer
    );
    // The other `v` recovers someone else.
    let flipped = vs.bitxor(Word::from_u64(1).shl(255));
    assert_ne!(
        u.word(
            "tryRecoverCompact(bytes32,bytes32,bytes32)",
            &[Arg::W(hash), Arg::W(r), Arg::W(flipped)]
        ),
        signer
    );

    // An account without code signs with ECDSA; a contract answers ERC-1271.
    let now = "isValidSignatureNow(address,bytes32,bytes)";
    let erc1271 = "isValidERC1271SignatureNow(address,bytes32,bytes)";
    let check = |u: &mut Session, sig: &str, who: Word, data: &[u8]| {
        u.word(sig, &[Arg::W(who), Arg::W(hash), Arg::B(data.to_vec())]) == Word::from_u64(1)
    };
    assert!(check(&mut u, now, signer, &sig));
    assert!(!check(&mut u, now, Word::from_u64(0xabc), &sig));
    assert!(!check(&mut u, now, signer, &malleable));
    assert!(!check(&mut u, now, signer, &sig[..64]));
    assert!(!check(&mut u, now, zero, &[0; 65]));
    // An account's ECDSA signature is not one to ERC-1271.
    assert!(!check(&mut u, erc1271, signer, &sig));
    let wallet = Word::from_u64(0x1271);
    let hash_bytes = hash.to_be_bytes();
    assert!(check(&mut u, now, wallet, &hash_bytes));
    assert!(check(&mut u, erc1271, wallet, &hash_bytes));
    assert!(!check(&mut u, now, wallet, &sig));
    // A contract is never checked with ECDSA, even for a signature its address made.
    assert!(!check(&mut u, now, wallet, b"wrong"));
    // The selector must fill a whole word.
    assert!(!check(&mut u, now, wallet, b"short"));
    assert!(!check(&mut u, now, wallet, b"dirty"));
    // Reverting, silent, and echoing contracts all answer false without reverting.
    for callee in [0xee, 0xef, 0xce, 0xcd, 2] {
        assert!(
            !check(&mut u, now, Word::from_u64(callee), &hash_bytes),
            "{callee:#x}"
        );
    }

    // Multiproofs from `@openzeppelin/merkle-tree`'s `SimpleMerkleTree.of` over
    // keccak256 of the bytes 0 to 6, a tree that isn't perfect.
    let root = hexw("710426d6c25ffa16bd4a78dc6ea868f4b17858c4bc0741ca38181e98b14ddd86");
    let words = |xs: &[&str]| Arg::L(xs.iter().map(|x| hexw(x)).collect());
    let flags = |xs: &[bool]| Arg::L(xs.iter().map(|&b| Word::from_u64(u64::from(b))).collect());
    let vectors: [(&[&str], &[&str], &[bool]); 5] = [
        (
            &[
                "69c322e3248a5dfc29d73c5b0553b0185a35cd5bb6386747517ef7e53b15e287",
                "bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a",
                "dbb8d0f4c497851a5043c6363657698cb1387682cac2f786c731f8936109d795",
            ],
            &[
                "5fe7f977e71dba2ea1a68e21057beebb9be2ac30c6410aa38d4f3fbe41dcffd2",
                "d0591206d9e81e07f4defc5327957173572bcd1bca7838caa7be39b0c12b1873",
                "f2ee15ea639b73fa3db9b34a245bdfa015c260c598b211bf05a1ecc4b3e3b4f2",
                "f343681465b9efe82c933c3e8748c70cb8aa06539c361de20f72eac04e766393",
            ],
            &[false, false, false, false, true, true],
        ),
        (
            &[
                "5fe7f977e71dba2ea1a68e21057beebb9be2ac30c6410aa38d4f3fbe41dcffd2",
                "f2ee15ea639b73fa3db9b34a245bdfa015c260c598b211bf05a1ecc4b3e3b4f2",
            ],
            &[
                "69c322e3248a5dfc29d73c5b0553b0185a35cd5bb6386747517ef7e53b15e287",
                "dbb8d0f4c497851a5043c6363657698cb1387682cac2f786c731f8936109d795",
                "f343681465b9efe82c933c3e8748c70cb8aa06539c361de20f72eac04e766393",
                "4d317a495479673fbf9eff21a78cc0d4c4d67210196299508f6214d5e12f2a70",
            ],
            &[false, false, false, false, true],
        ),
        (
            &["d0591206d9e81e07f4defc5327957173572bcd1bca7838caa7be39b0c12b1873"],
            &[
                "bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a",
                "82142e1c0ddd298cd66ef6caeaffb602a56f7379941f173a60d5d604cd34c9e3",
                "460705b2c816a244a5bbc3d1e82564c20ef556b8c7677c4c6160ec8cea0d3deb",
            ],
            &[false, false, false],
        ),
        (
            &[
                "5fe7f977e71dba2ea1a68e21057beebb9be2ac30c6410aa38d4f3fbe41dcffd2",
                "69c322e3248a5dfc29d73c5b0553b0185a35cd5bb6386747517ef7e53b15e287",
                "bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a",
                "d0591206d9e81e07f4defc5327957173572bcd1bca7838caa7be39b0c12b1873",
                "dbb8d0f4c497851a5043c6363657698cb1387682cac2f786c731f8936109d795",
                "f2ee15ea639b73fa3db9b34a245bdfa015c260c598b211bf05a1ecc4b3e3b4f2",
                "f343681465b9efe82c933c3e8748c70cb8aa06539c361de20f72eac04e766393",
            ],
            &[],
            &[true, true, true, true, true, true],
        ),
        (
            &["f343681465b9efe82c933c3e8748c70cb8aa06539c361de20f72eac04e766393"],
            &[
                "a6245e634fd8b37fd223f8c238ee488a9fd3408cf3fbe70bbf64f337166de1c9",
                "f7710c1230ccc1b2374848eb088c944b26a3e2ff42a3da990a699bdca5e46cc5",
            ],
            &[false, false],
        ),
    ];
    let verify = "verifyMulti(bytes32[],bool[],bytes32,bytes32[])";
    let multi_root = "multiRoot(bytes32[],bool[],bytes32[])";
    for (leaves, proof, fl) in vectors {
        let args = [words(proof), flags(fl), Arg::W(root), words(leaves)];
        assert_eq!(u.word(verify, &args), Word::from_u64(1), "{leaves:?}");
        assert_eq!(
            u.word(multi_root, &[words(proof), flags(fl), words(leaves)]),
            root
        );
        // A leaf that isn't in the tree fails.
        let mut wrong: Vec<&str> = leaves.to_vec();
        wrong[0] = "0000000000000000000000000000000000000000000000000000000000000001";
        let args = [words(proof), flags(fl), Arg::W(root), words(&wrong)];
        assert_eq!(u.word(verify, &args), zero);
    }
    let (leaves, proof, fl) = vectors[0];
    // Too few flags for the nodes given.
    assert!(!u.send(
        0,
        verify,
        &[words(proof), flags(&fl[1..]), Arg::W(root), words(leaves)]
    ));
    u.reverted_with("MerkleProofInvalidMultiproof()");
    // The flags leave a proof node unused, taking a node from the queue instead: the
    // multiproof OpenZeppelin 4.9.2 stopped accepting.
    let leaf = [leaves[0]];
    let two = [proof[0], proof[1]];
    assert!(!u.send(
        0,
        verify,
        &[
            words(&two),
            flags(&[true, false]),
            Arg::W(root),
            words(&leaf)
        ]
    ));
    u.reverted_with("MerkleProofInvalidMultiproof()");
    // No leaves: a one-node proof proves that node, and anything more is invalid.
    let only = ["710426d6c25ffa16bd4a78dc6ea868f4b17858c4bc0741ca38181e98b14ddd86"];
    assert_eq!(
        u.word(
            verify,
            &[words(&only), flags(&[]), Arg::W(root), words(&[])]
        ),
        Word::from_u64(1)
    );
    assert!(!u.send(
        0,
        verify,
        &[words(&two), flags(&[false]), Arg::W(root), words(&[])]
    ));
    u.reverted_with("MerkleProofInvalidMultiproof()");
    // One leaf is its own root.
    assert_eq!(
        u.word(
            verify,
            &[words(&[]), flags(&[]), Arg::W(root), words(&only)]
        ),
        Word::from_u64(1)
    );

    // ERC-5267: the fields bitmap, name, version, chain id, and this contract.
    assert!(u.send(0, "eip712Domain()", &[]));
    let ret = u.returned();
    assert_eq!(
        load_bytes(&ret, 0),
        hexw("0f00000000000000000000000000000000000000000000000000000000000000")
    );
    assert_eq!(dynamic_at(&ret, 1), b"Utils");
    assert_eq!(dynamic_at(&ret, 2), b"1");
    assert_eq!(load_bytes(&ret, 96), Word::from_u64(1));
    assert_eq!(load_bytes(&ret, 128), Word::from_u64(0x1000));
    assert_eq!(load_bytes(&ret, 160), zero);
    assert_eq!(load_bytes(&ret, small(load_bytes(&ret, 192))), zero);

    // A name or version of 32 bytes or more is stored instead.
    for (name, version) in [
        ("A name that is longer than one word", "1"),
        ("Short", "version 1.0.0 of a longer protocol"),
        ("Thirty-one bytes, just a word.", "2"),
        ("", ""),
    ] {
        let mut d = Session::source(&format!(
            "import \"std/crypto/eip712\"; import \"std/interfaces/erc5267\";\ncontract D is {{\n  use EIP712 exposing IERC5267;\n  storage is record {{ n : uint; }}\n  deploy() is {{ EIP712.init(\"{name}\", \"{version}\"); }}\n  external view function domain() : bytes32 is EIP712.domainSeparator()\n}}\n"
        ));
        assert!(d.send(0, "eip712Domain()", &[]));
        let ret = d.returned();
        assert_eq!(dynamic_at(&ret, 1), name.as_bytes());
        assert_eq!(dynamic_at(&ret, 2), version.as_bytes());
        let mut domain = Vec::new();
        for word in [
            keccak_word(b"EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
            keccak_word(name.as_bytes()),
            keccak_word(version.as_bytes()),
            Word::from_u64(1),
            Word::from_u64(0x1000),
        ] {
            domain.extend_from_slice(&word.to_be_bytes());
        }
        assert_eq!(d.word("domain()", &[]), keccak_word(&domain));
    }
}

/// Multiproofs with random leaves, proofs, and flags, well formed or not, rebuild what
/// OpenZeppelin's `processMultiProof` does: the same root, the same
/// `MerkleProofInvalidMultiproof`, and a panic where a proof node runs out or a read goes
/// past the hashes.
#[test]
fn multiproofs_match_openzeppelin() {
    #[derive(Debug, PartialEq)]
    enum Want {
        Root(Word),
        Invalid,
        Panic,
    }
    fn pair(a: Word, b: Word) -> Word {
        let (lo, hi) = if a.lt(b) || a == b { (a, b) } else { (b, a) };
        keccak_word(&[lo.to_be_bytes(), hi.to_be_bytes()].concat())
    }
    fn oz(proof: &[Word], flags: &[bool], leaves: &[Word]) -> Want {
        let (n, count) = (leaves.len(), flags.len());
        if n + proof.len() != count + 1 {
            return Want::Invalid;
        }
        let mut hashes = vec![Word::from_u64(0); count];
        let (mut lp, mut hp, mut pp) = (0, 0, 0);
        for i in 0..count {
            let mut take = || {
                if lp < n {
                    lp += 1;
                    Some(leaves[lp - 1])
                } else {
                    hp += 1;
                    hashes.get(hp - 1).copied()
                }
            };
            let Some(a) = take() else { return Want::Panic };
            let b = if flags[i] {
                match take() {
                    Some(b) => b,
                    None => return Want::Panic,
                }
            } else {
                pp += 1;
                match proof.get(pp - 1) {
                    Some(&b) => b,
                    None => return Want::Panic,
                }
            };
            hashes[i] = pair(a, b);
        }
        if count > 0 {
            if pp != proof.len() {
                return Want::Invalid;
            }
            Want::Root(hashes[count - 1])
        } else if n > 0 {
            Want::Root(leaves[0])
        } else {
            Want::Root(proof[0])
        }
    }
    let mut u = Session::new("examples/stdlib/utils.lithe");
    let mut seed = 0x51f1_5eedu64;
    let mut next = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let (mut roots, mut invalid, mut panics) = (0, 0, 0);
    for _ in 0..400 {
        let n = (next() % 5) as usize;
        let count = (next() % 6) as usize;
        let mut plen = (count + 1).saturating_sub(n);
        if next() % 5 == 0 {
            plen = (next() % 4) as usize;
        }
        let word = |x: u64| keccak_word(&x.to_be_bytes());
        let leaves: Vec<Word> = (0..n).map(|_| word(next())).collect();
        let proof: Vec<Word> = (0..plen).map(|_| word(next())).collect();
        let flags: Vec<bool> = (0..count).map(|_| next() % 2 == 0).collect();
        let want = oz(&proof, &flags, &leaves);
        let args = [
            Arg::L(proof.clone()),
            Arg::L(
                flags
                    .iter()
                    .map(|&f| Word::from_u64(u64::from(f)))
                    .collect(),
            ),
            Arg::L(leaves.clone()),
        ];
        let ok = u.send(0, "multiRoot(bytes32[],bool[],bytes32[])", &args);
        let got = if ok {
            Want::Root(load_bytes(&u.returned(), 0))
        } else if u.returned().get(..4) == Some(&selector("MerkleProofInvalidMultiproof()")[..]) {
            Want::Invalid
        } else {
            Want::Panic
        };
        match &want {
            Want::Root(_) => roots += 1,
            Want::Invalid => invalid += 1,
            Want::Panic => panics += 1,
        }
        assert_eq!(got, want, "{proof:?} {flags:?} {leaves:?}");
    }
    assert!(
        roots > 50 && invalid > 50 && panics > 50,
        "{roots} roots, {invalid} invalid, {panics} panics"
    );
}

/// `Math`'s bit-length functions built for Prague (halving ladders) and for Osaka (`CLZ`)
/// agree with bit-by-bit references at every power of two, and only Osaka's uses `CLZ`.
#[test]
fn math_bit_lengths_on_both_forks() {
    let src = r#"import "std/uint"; 
import "std/math/math";

contract M is {
  use Math;
  storage is record { n : uint; }
  external pure function sqrt(const a : uint) : uint is Math.sqrt(a)
  external pure function cbrt(const a : uint) : uint is Math.cbrt(a)
  external pure function log2(const a : uint) : uint is Math.log2(a)
  external pure function log256(const a : uint) : uint is Math.log256(a)
  external pure function clz(const a : uint) : uint is Uint.clz(a)
}
"#;
    let build = |evm| {
        let opts = Options {
            evm,
            ..Options::default()
        };
        let out = crate::compile(&memory(src), Path::new(ENTRY), &opts)
            .and_then(crate::Output::single)
            .map_err(first)
            .expect("compile");
        deploy(&out.bytecode).expect("deploy")
    };
    let has_clz = |code: &[u8]| {
        let mut i = 0;
        while i < code.len() {
            if code[i] == 0x1e {
                return true;
            }
            i += 1 + if (0x60..=0x7f).contains(&code[i]) {
                usize::from(code[i] - 0x5f)
            } else {
                0
            };
        }
        false
    };
    let (prague, osaka) = (
        build(crate::EvmVersion::Prague),
        build(crate::EvmVersion::Osaka),
    );
    assert!(!has_clz(&prague) && has_clz(&osaka));
    assert!(
        osaka.len() < prague.len(),
        "{} vs {}",
        osaka.len(),
        prague.len()
    );
    let one = Word::from_u64(1);
    let root = |a: Word, n: u32, top: u32| {
        let mut r = Word::from_u64(0);
        for bit in (0..top).rev() {
            let c = r.bitor(one.shl(bit));
            let (mut p, mut over) = (one, false);
            for _ in 0..n {
                let (q, o) = p.overflowing_mul(c);
                (p, over) = (q, over || o);
            }
            if !over && !a.lt(p) {
                r = c;
            }
        }
        r
    };
    let mut samples = vec![Word::from_u64(0), Word::from_u64(0).not()];
    for k in 0..256 {
        let p = one.shl(k);
        samples.extend([p, p.wrapping_sub(one), p.wrapping_add(one)]);
    }
    for a in samples {
        let bits = u64::from(a.bits());
        let want = [
            ("sqrt(uint256)", root(a, 2, 128)),
            ("cbrt(uint256)", root(a, 3, 86)),
            ("log2(uint256)", Word::from_u64(bits.saturating_sub(1))),
            (
                "log256(uint256)",
                Word::from_u64(bits.saturating_sub(1) / 8),
            ),
            ("clz(uint256)", Word::from_u64(256 - bits)),
        ];
        for runtime in [&prague, &osaka] {
            for (sig, want) in want {
                let out = call(runtime, sig, &[a]);
                assert_eq!(load_bytes(&out.returndata, 0), want, "{sig} {a:?}");
            }
        }
    }
}
