use super::*;

/// Every standard library file compiles inside a contract that imports it.
#[test]
fn every_stdlib_file_compiles() {
    for (path, _) in crate::modules::STD {
        let dir = std::env::temp_dir().join(format!("lithe-std-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let main = dir.join("main.lithe");
        let src = format!(
            "import \"{path}\";\nstorage is record {{ n : nat; }}\nexternal function f() is {{ storage.n := 1n; }}\n"
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
    assert!(t.send(1, "pause()", &[]));
    assert!(!t.send(2, "transfer(address,uint256)", &[w(3), w(1)]));
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
    let max = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    assert_eq!(
        u.word(
            "average(uint256,uint256)",
            &[Arg::W(hexw(max)), Arg::W(hexw(max))]
        ),
        hexw(max)
    );
    assert_eq!(
        u.word("ceil_div(uint256,uint256)", &[w(7), w(2)]),
        Word::from_u64(4)
    );
    assert_eq!(
        u.word("ceil_div(uint256,uint256)", &[w(0), w(2)]),
        Word::from_u64(0)
    );
    assert_eq!(
        u.word("mul_div_up(uint256,uint256,uint256)", &[w(7), w(3), w(2)]),
        Word::from_u64(11)
    );
    assert_eq!(
        u.word("clamp(uint256,uint256,uint256)", &[w(9), w(2), w(5)]),
        Word::from_u64(5)
    );
    assert!(!u.send(0, "clamp(uint256,uint256,uint256)", &[w(1), w(5), w(2)]));
    u.reverted_with("MathInvalidRange(uint256,uint256)");
    assert!(!u.send(0, "to_nat(int256)", &[Arg::W(Word::from_u64(3).not())]));
    u.reverted_with("SafeCastOverflowedIntToUint(int256)");
    assert!(!u.send(0, "to_int(uint256)", &[Arg::W(hexw(max))]));
    u.reverted_with("SafeCastOverflowedUintToInt(uint256)");
    let e18 = 1_000_000_000_000_000_000u64;
    assert_eq!(
        u.word("wad_mul(uint256,uint256)", &[w(3 * e18 / 2), w(4 * e18)]),
        Word::from_u64(6 * e18)
    );
    assert_eq!(
        u.word("wad_div(uint256,uint256)", &[w(3 * e18), w(2 * e18)]),
        Word::from_u64(3 * e18 / 2)
    );
    assert_eq!(
        u.word("apply_bps(uint256,uint256)", &[w(20_000), w(25)]),
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
    let proof = |nodes: &[Word]| Arg::B(nodes.iter().flat_map(|n| n.to_be_bytes()).collect());
    let verify = "verify(bytes,bytes32,bytes32)";
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
    assert!(!u.send(
        0,
        verify,
        &[Arg::B(vec![1; 33]), Arg::W(root), Arg::W(root)]
    ));
    u.reverted_with("MerkleProofInvalidLength(uint256)");

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
            "recover_vrs(bytes32,uint8,bytes32,bytes32)",
            &[Arg::W(hash), w(u64::from(v)), Arg::W(r), Arg::W(s)]
        ),
        signer
    );
    let n = hexw("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
    let high = n.wrapping_sub(s);
    let twin = if v == 27 { 28 } else { 27 };
    assert!(!u.send(
        0,
        "recover_vrs(bytes32,uint8,bytes32,bytes32)",
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
        u.word("eth_message(bytes32)", &[Arg::W(hash)]),
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
            "create2_address(bytes32,bytes32,address)",
            &[Arg::W(salt), Arg::W(code), w(0xdead)]
        ),
        Word::from_be_bytes(addr)
    );

    // Nonces count up per account; each call here uses one.
    assert_eq!(u.word("use_nonce(address)", &[w(5)]), Word::from_u64(0));
    assert_eq!(u.word("use_nonce(address)", &[w(5)]), Word::from_u64(1));
    assert_eq!(u.word("use_nonce(address)", &[w(6)]), Word::from_u64(0));

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
            u.word("is_claimed(uint256)", &[w(i)]),
            Word::from_u64(u64::from(set)),
            "{i}"
        );
    }
    assert!(u.send(0, "unclaim(uint256)", &[w(255)]));
    assert_eq!(u.word("is_claimed(uint256)", &[w(255)]), Word::from_u64(0));
    assert_eq!(u.word("is_claimed(uint256)", &[w(0)]), Word::from_u64(1));

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
    assert!(u.send(0, "checkpoint_value(uint256)", &[w(5)]));
    assert!(u.send(0, "checkpoint_value(uint256)", &[w(8)]));
    assert_eq!(u.word("checkpoints()", &[]), Word::from_u64(1));
    assert_eq!(u.word("latest()", &[]), Word::from_u64(8));
    assert_eq!(u.word("value_at(uint256)", &[w(100)]), Word::from_u64(8));
    assert_eq!(u.word("value_at(uint256)", &[w(150)]), Word::from_u64(8));
    assert_eq!(u.word("value_at(uint256)", &[w(99)]), Word::from_u64(0));

    // Sets.
    assert!(u.send(21, "join()", &[]));
    assert!(u.send(21, "join()", &[]));
    assert!(u.send(22, "join()", &[]));
    assert_eq!(u.word("member(address)", &[w(21)]), Word::from_u64(1));
    assert_eq!(u.word("member(address)", &[w(23)]), Word::from_u64(0));
    assert_eq!(u.word("listed_count()", &[]), Word::from_u64(2));
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
    assert!(a.send(1, "record_entry(address,uint256)", &[w(5), w(3)]));
    assert!(!a.send(2, "record_entry(address,uint256)", &[w(5), w(3)]));
    a.reverted_with("AccessControlUnauthorizedAccount(address,bytes32)");
    assert!(!a.send(
        2,
        "grantRole(bytes32,address)",
        &[Arg::W(keccak_word(b"MINTER_ROLE")), w(2)]
    ));
    assert!(a.send(1, "grantRole(bytes32,address)", &[minter, w(2)]));
    assert!(a.send(2, "record_entry(address,uint256)", &[w(5), w(4)]));
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
    assert!(a.send(1, "set_pauser(address,bool)", &[w(4), w(1)]));
    assert!(a.send(4, "pause()", &[]));
    assert!(!a.send(1, "record_entry(address,uint256)", &[w(5), w(1)]));
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
    assert!(!a.send(1, "set_pauser(address,bool)", &[w(4), w(0)]));
    assert!(a.send(9, "set_pauser(address,bool)", &[w(4), w(0)]));
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
    let id = |sel: u64| Arg::W(Word::from_u64(sel).shl(224));
    for (sel, want) in [(0xd9b67a26, 1), (0x0e89341c, 1), (0x80ac58cd, 0)] {
        assert_eq!(
            t.word("supportsInterface(bytes4)", &[id(sel)]),
            Word::from_u64(want)
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
    let src = r#"
contract T is {
  storage is record {
    last : string;
  }

  external pure function enc(const data : bytes; const file_safe : bool; const no_padding : bool) : string is
    Base64.encode_with(data, file_safe, no_padding)

  external pure function dec(const data : string) : bytes is
    Base64.decode(data)

  external pure function same(const data : bytes) : bool is
    Crypto.keccak256(Base64.decode(Base64.encode(data))) = Crypto.keccak256(data)
    and Crypto.keccak256(Base64.encode(data)) = Crypto.keccak256(Base64.encode_with(data, false, false))

  external pure function text(const s : string) : string is
    Base64.encode_url(s)

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
storage is record { n : nat; }
external function bump() is { storage.n := storage.n + 1n; }
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
    assert!(d.word("args_of(address)", &[Arg::W(instance)]) == Word::from_u64(32));
    assert!(abi_string_value(&d.returned()).is_empty());

    // With a salt, the clone lands where `predict_clone` says.
    let salt = Word::from_u64(0x5a17);
    let predicted = d.word(
        "predict_clone(address,bytes32)",
        &[Arg::W(implementation), Arg::W(salt)],
    );
    let mut init = unhex("3d602d80600a3d3981f3");
    init.extend(clone_code(&[]));
    assert_eq!(predicted, created_address(this, Some(salt), &init));
    assert_eq!(
        d.word(
            "clone_deterministic(address,bytes32)",
            &[Arg::W(implementation), Arg::W(salt)]
        ),
        predicted
    );
    assert_eq!(slot(&d.storage, 0), predicted);

    // Arguments ride after the clone's code.
    let args = b"immutable arguments, read back with EXTCODECOPY".to_vec();
    assert!(d.send(
        1,
        "clone_with_args(address,bytes)",
        &[Arg::W(implementation), Arg::B(args.clone())]
    ));
    let instance = slot(&d.storage, 0);
    assert_eq!(
        DEPLOYED.with(|m| m.borrow()[&instance].0.clone()),
        clone_code(&args)
    );
    d.word("args_of(address)", &[Arg::W(instance)]);
    assert_eq!(abi_string_value(&d.returned()), args);
    assert!(!d.send(
        1,
        "clone_with_args(address,bytes)",
        &[Arg::W(implementation), Arg::B(vec![7; 24532])]
    ));
    d.reverted_with("CloneArgumentsTooLong()");

    // SSTORE2: data written as code reads back whole.
    let data = b"data kept as the code of a contract that stops at once".to_vec();
    assert!(d.send(1, "write(bytes)", &[Arg::B(data.clone())]));
    d.word("read()", &[]);
    assert_eq!(abi_string_value(&d.returned()), data);
    let pointer = d.word(
        "write_counterfactual(bytes,bytes32)",
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
import \"std/utils/create2.lithe\";
import \"std/utils/clones.lithe\";
import \"std/utils/create3.lithe\";

contract Funded is {
  use Create2;
  use Clones;
  use Create3;

  storage is record { last : address; }

  external function plain(const target : address; const salt : bytes32) : address raises FailedDeployment is {
    storage.last := Clones.clone_deterministic(target, salt);
  } with storage.last

  external payable function funded(const target : address; const salt : bytes32) : address raises FailedDeployment is {
    storage.last := Clones.clone_deterministic(target, salt, nat(Evm.value()));
  } with storage.last

  external payable function funded_with_args(const target : address; const args : bytes; const salt : bytes32) : address
    raises CloneArgumentsTooLong | FailedDeployment
  is {
    storage.last := Clones.clone_deterministic_with_args(target, args, salt, nat(Evm.value()));
  } with storage.last

  external function plain_with_args(const target : address; const args : bytes; const salt : bytes32) : address
    raises CloneArgumentsTooLong | FailedDeployment
  is {
    storage.last := Clones.clone_deterministic_with_args(target, args, salt);
  } with storage.last

  external function deploy3(const code : bytes; const salt : bytes32) : address raises FailedDeployment is {
    storage.last := Create3.deploy_deterministic(code, salt);
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
        "plain_with_args(address,bytes,bytes32)",
        &[Arg::W(target), args(), salt()],
        0,
    );
    assert_eq!(sent, Some(Word::from_u64(0)));
    let (funded_args, sent) = run(
        "funded_with_args(address,bytes,bytes32)",
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
