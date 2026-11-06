//! Benchmark gas without solc or a node: replays `bench/run.py` scenarios through the
//! interpreter with a gas meter on, and writes each contract's runtime size and gas to
//! `$LITHE_BENCH_OUT` as JSON when it is set.
//!
//! The ported scenarios are the ones of single contracts whose calls need only flat ABI
//! arguments; steps with hand-built calldata are left out.
//!
//! simplify: the meter prices Osaka's opcodes, memory expansion, and EIP-2929/2200
//! warm/cold storage and account access, without refunds, the calldata floor, or call
//! stipends, so its totals track codegen changes rather than match a node's receipts.
//! Port more of `run.py` or price those when a number needs to match anvil's.

use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use super::{compile_file, construct, encode_args, exec, hex_decode, word_usize, Arg, SELF};
use crate::word::Word;

struct Meter {
    gas: u64,
    /// Each storage slot touched, by account, with the value it held when first touched.
    slots: HashMap<(Word, Word), Word>,
    accounts: HashSet<Word>,
}

impl Meter {
    /// The access cost of `slot` in `at`, and the value it held when first touched.
    fn touch(&mut self, at: Word, slot: Word, current: Word) -> (u64, Word) {
        match self.slots.entry((at, slot)) {
            Entry::Occupied(e) => (100, *e.get()),
            Entry::Vacant(e) => (2_100, *e.insert(current)),
        }
    }
}

thread_local! {
    static METER: RefCell<Option<Meter>> = const { RefCell::new(None) };
}

pub(super) fn metering() -> bool {
    METER.with(|m| m.borrow().is_some())
}

/// Charges the gas of running `op` with `stack`, in the account `at` whose storage is `storage`.
pub(super) fn charge(op: u8, stack: &[Word], storage: &HashMap<Word, Word>, at: Word) {
    let arg = |i: usize| {
        stack
            .len()
            .checked_sub(i + 1)
            .map_or(Word::from_u64(0), |j| stack[j])
    };
    let words = |i: usize| (word_usize(arg(i)).unwrap_or(0) as u64).div_ceil(32);
    let current = |slot: Word| storage.get(&slot).copied().unwrap_or(Word::from_u64(0));
    METER.with(|m| {
        let mut m = m.borrow_mut();
        let Some(m) = m.as_mut() else { return };
        let cost = match op {
            0x01 | 0x03 | 0x10..=0x1d | 0x35 | 0x51..=0x53 | 0x60..=0x9f => 3,
            0x02 | 0x04..=0x07 | 0x0b | 0x1e | 0x47 => 5,
            0x08 | 0x09 | 0x56 => 8,
            0x0a => 10 + 50 * u64::from(arg(1).bits()).div_ceil(8),
            0x20 => 30 + 6 * words(1),
            0x30 | 0x32..=0x34 | 0x36 | 0x38 | 0x3a | 0x3d | 0x41..=0x46 | 0x48 | 0x4a => 2,
            0x50 | 0x58..=0x5a | 0x5f => 2,
            0x37 | 0x39 | 0x3e | 0x5e => 3 + 3 * words(2),
            0x3c => 100 + 3 * words(3),
            0x31 | 0x3b | 0x3f | 0x5c | 0x5d => 100,
            0x40 => 20,
            0x49 => 3,
            0x57 => 10,
            0x5b => 1,
            0x54 => m.touch(at, arg(0), current(arg(0))).0,
            0x55 => {
                let (access, original) = m.touch(at, arg(0), current(arg(0)));
                let (now, new) = (current(arg(0)), arg(1));
                let write = if now == new || original != now {
                    100
                } else if original.is_zero() {
                    20_000
                } else {
                    2_900
                };
                let cold = if access == 100 { 0 } else { 2_100 };
                cold + write
            }
            0xa0..=0xa4 => 375 * u64::from(op - 0x9f) + 8 * word_usize(arg(1)).unwrap_or(0) as u64,
            0xf0 | 0xf5 => 32_000 + 2 * words(2),
            0xf1 | 0xf2 | 0xf4 | 0xfa => {
                let cold = if m.accounts.insert(arg(1)) {
                    2_600
                } else {
                    100
                };
                let value = matches!(op, 0xf1 | 0xf2) && !arg(2).is_zero();
                cold + if value { 9_000 } else { 0 }
            }
            _ => 0,
        };
        m.gas += cost;
    });
}

/// Charges for a frame's memory, by its size when the frame ends.
pub(super) fn charge_memory(len: usize) {
    let w = len.div_ceil(32) as u64;
    METER.with(|m| {
        if let Some(m) = m.borrow_mut().as_mut() {
            m.gas += 3 * w + w * w / 512;
        }
    });
}

/// Runs `f` as one transaction from `from`, returning its execution gas.
fn metered<T>(from: Word, f: impl FnOnce() -> T) -> (T, u64) {
    let accounts = [from, SELF.get()]
        .into_iter()
        .chain((1..=0x11).map(Word::from_u64))
        .collect();
    METER.with(|m| {
        *m.borrow_mut() = Some(Meter {
            gas: 0,
            slots: HashMap::new(),
            accounts,
        })
    });
    let out = f();
    let gas = METER.with(|m| m.borrow_mut().take().map_or(0, |m| m.gas));
    (out, gas)
}

fn intrinsic(data: &[u8]) -> u64 {
    21_000
        + data
            .iter()
            .map(|&b| if b == 0 { 4 } else { 16 })
            .sum::<u64>()
}

const A: &str = "0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266";
const B: &str = "0x70997970C51812dC3A010C7d01b50e0d17dc79C8";
const ZERO: &str = "0x0000000000000000000000000000000000000000";
const LONG: &str = "a string that is well past thirty one bytes long";

struct Step {
    send: bool,
    from: &'static str,
    sig: &'static str,
    args: Vec<String>,
    value: &'static str,
}

fn step(send: bool, from: &'static str, sig: &'static str, args: &[&str]) -> Step {
    let args = args.iter().map(|a| a.to_string()).collect();
    Step {
        send,
        from,
        sig,
        args,
        value: "0",
    }
}

fn send(from: &'static str, sig: &'static str, args: &[&str]) -> Step {
    step(true, from, sig, args)
}

fn call(from: &'static str, sig: &'static str, args: &[&str]) -> Step {
    step(false, from, sig, args)
}

fn pay(from: &'static str, sig: &'static str, args: &[&str], value: &'static str) -> Step {
    Step {
        value,
        ..send(from, sig, args)
    }
}

fn e18(n: u64) -> String {
    format!("{n}000000000000000000")
}

fn word(text: &str) -> Word {
    let parsed = match text {
        "true" => Some(Word::from_u64(1)),
        "false" => Some(Word::from_u64(0)),
        _ if text.starts_with("0x") => Word::from_hex(&text[2..]),
        _ if text.starts_with('-') => Word::from_dec(&text[1..]).map(Word::wrapping_neg),
        _ => Word::from_dec(text),
    };
    parsed.unwrap_or_else(|| panic!("not a word: {text}"))
}

fn value(text: &str) -> Word {
    match text.strip_suffix("ether") {
        Some(n) => word(&e18(n.parse().expect("whole ether"))),
        None => word(text),
    }
}

/// Encodes `args` for `sig`'s flat parameter list, as `cast` takes them.
fn calldata(sig: &str, args: &[String]) -> Vec<u8> {
    let params = &sig[sig.find('(').expect("signature") + 1..sig.len() - 1];
    let types = params.split(',').filter(|t| !t.is_empty());
    let args: Vec<Arg> = types
        .zip(args)
        .map(|(ty, text)| match ty {
            "string" => Arg::B(text.as_bytes().to_vec()),
            "bytes" => Arg::B(hex_decode(&text[2..])),
            _ if ty.ends_with("[]") => Arg::L(
                text[1..text.len() - 1]
                    .split(',')
                    .filter(|t| !t.is_empty())
                    .map(word)
                    .collect(),
            ),
            _ => Arg::W(word(text)),
        })
        .collect();
    encode_args(sig, &args)
}

struct Measured {
    runtime_bytes: usize,
    deploy_gas: u64,
    gas: u64,
}

/// Deploys `bench/<name>.lithe` from A with `ctor` appended, then runs `steps`, keeping
/// storage and balance after each send that succeeds.
fn replay(name: &str, ctor: &[&str], steps: &[Step]) -> Measured {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut init = compile_file(&root.join(format!("bench/{name}.lithe")))
        .unwrap_or_else(|e| panic!("{name}: {e}"));
    init.extend(ctor.iter().flat_map(|a| word(a).to_be_bytes()));
    let deployer = word(A);
    let (made, gas) = metered(deployer, || construct(&init, deployer, Word::from_u64(0)));
    let made = made.unwrap_or_else(|e| panic!("{name}: {e}"));
    assert!(!made.reverted, "{name}: deploy reverted");
    let runtime = made.returndata;
    let deploy_gas = intrinsic(&init)
        + 32_000
        + 2 * (init.len() as u64).div_ceil(32)
        + 200 * runtime.len() as u64
        + gas;
    let mut storage = made.storage;
    let mut balance = Word::from_u64(0);
    let mut total = 0;
    for s in steps {
        let data = calldata(s.sig, &s.args);
        let (from, value) = (word(s.from), value(s.value));
        let (out, gas) = metered(from, || {
            exec(
                &runtime,
                &data,
                storage.clone(),
                from,
                value,
                balance.wrapping_add(value),
            )
        });
        let out = out.unwrap_or_else(|e| panic!("{name} {}: {e}", s.sig));
        if s.send && !out.reverted {
            storage = out.storage;
            balance = out.self_balance;
        }
        total += intrinsic(&data) + gas;
    }
    Measured {
        runtime_bytes: runtime.len(),
        deploy_gas,
        gas: total,
    }
}

fn scenarios() -> Vec<(&'static str, Vec<&'static str>, Vec<Step>)> {
    let (n101, d201, x41) = ("n".repeat(101), "d".repeat(201), "x".repeat(41));
    let (a31, b32, ab65) = (
        "a".repeat(31),
        "b".repeat(32),
        format!("0x{}", "ab".repeat(65)),
    );
    let (v1, v2, v3) = (
        format!("0x{}", "01".repeat(32)),
        format!("0x{}", "02".repeat(32)),
        format!("0x{}", "03".repeat(32)),
    );
    let max = format!("0x{}", "f".repeat(64));
    let huge = format!("1{}", "0".repeat(30));
    let (e1000, e100, e500, e200, e400, e10, e5) = (
        e18(1000),
        e18(100),
        e18(500),
        e18(200),
        e18(400),
        e18(10),
        e18(5),
    );
    let hash = format!("0x{}", "11".repeat(32));
    let airdrop = format!("[{A},{B},{A}]");
    let payout = format!("[{B},0x0000000000000000000000000000000000000003]");
    vec![
        (
            "counter",
            vec![],
            vec![
                send(A, "increment(uint256)", &["5"]),
                send(B, "increment(uint256)", &["0"]),
                send(B, "increment(uint256)", &["7"]),
                send(B, "reset()", &[]),
                call(A, "getCount()", &[]),
                send(A, "reset()", &[]),
                call(A, "getCount()", &[]),
            ],
        ),
        (
            "token",
            vec![],
            vec![
                send(A, "mint(address,uint256)", &[A, "1000"]),
                send(A, "mint(address,uint256)", &[B, "50"]),
                send(A, "transfer(address,uint256)", &[B, "100"]),
                send(B, "transfer(address,uint256)", &[A, "999"]),
                send(B, "mint(address,uint256)", &[B, "1"]),
                send(B, "transfer(address,uint256)", &[A, "150"]),
                call(A, "balanceOf(address)", &[A]),
                call(A, "totalSupply()", &[]),
            ],
        ),
        (
            "shapes",
            vec![],
            vec![
                send(A, "add(uint256)", &["0"]),
                call(A, "add(uint256)", &["0"]),
                send(B, "add(uint256)", &["3"]),
                call(B, "add(uint256)", &["3"]),
                send(A, "add(uint256)", &["5"]),
                send(A, "buy(uint256,string)", &["2", "Widget"]),
                send(A, "buy(uint256,string)", &["9", "Widget"]),
                call(A, "buy(uint256,string)", &["9", "Widget"]),
                call(A, "buy(uint256,string)", &["9", LONG]),
                call(A, "buy(uint256,string)", &["1", ""]),
                call(A, "buy(uint256,string)", &["1", &x41]),
                call(A, "buyAll(uint256[],string)", &["[]", "nothing to buy"]),
                call(A, "buyAll(uint256[],string)", &["[1,2,3,4,5]", LONG]),
                send(A, "buyAll(uint256[],string)", &["[1,9]", "n"]),
                call(A, "buyAll(uint256[],string)", &["[1,9]", "n"]),
                call(A, "buyAll(uint256[],string)", &["[0,1]", LONG]),
                send(A, "buyAll(uint256[],string)", &["[1,2]", "ok"]),
                call(A, "load(bytes)", &["0x"]),
                send(A, "load(bytes)", &["0xdeadbeef"]),
                call(B, "load(bytes)", &["0xdeadbeef"]),
                call(A, "load(bytes)", &[&ab65]),
                call(A, "compare(string,string)", &["abc", "abc"]),
                call(A, "compare(string,string)", &["abc", "abd"]),
                call(A, "compare(string,string)", &[LONG, "x"]),
                call(A, "compare(string,string)", &["", ""]),
            ],
        ),
        (
            "reasons",
            vec![],
            vec![
                send(A, "deposit(uint256)", &["100"]),
                send(A, "deposit(uint256)", &["0"]),
                call(A, "deposit(uint256)", &["0"]),
                call(A, "deposit(uint256)", &["5000"]),
                send(A, "withdraw(uint256)", &["500"]),
                call(A, "withdraw(uint256)", &["500"]),
                send(A, "withdraw(uint256)", &["50"]),
                call(A, "transfer(address,uint256)", &[ZERO, "1"]),
                call(A, "transfer(address,uint256)", &[A, "1"]),
                send(A, "transfer(address,uint256)", &[B, "10"]),
                send(B, "setLimit(uint256)", &["5"]),
                call(B, "setLimit(uint256)", &["5"]),
                call(A, "setLimit(uint256)", &["0"]),
                call(A, "setLimit(uint256)", &["2000000"]),
                send(A, "setLimit(uint256)", &["2000"]),
                call(A, "pause(bool)", &["false"]),
                send(A, "pause(bool)", &["true"]),
                send(A, "deposit(uint256)", &["1"]),
                call(A, "deposit(uint256)", &["1"]),
                call(A, "balanceOf(address)", &[ZERO]),
                call(A, "balanceOf(address)", &[A]),
            ],
        ),
        (
            "strings",
            vec![],
            vec![
                send(A, "rename(string)", &["Short"]),
                send(A, "rename(string)", &["Short"]),
                call(A, "rename(string)", &["Short"]),
                send(A, "rename(string)", &[LONG]),
                call(A, "rename(string)", &[LONG]),
                send(B, "rename(string)", &["Other"]),
                call(B, "rename(string)", &["Other"]),
                call(A, "rename(string)", &[&n101]),
                send(
                    A,
                    "describe(string)",
                    &["a description that is well past one word in length"],
                ),
                call(B, "describe(string)", &["x"]),
                call(A, "describe(string)", &[&d201]),
                call(A, "description()", &[]),
                call(A, "name()", &[]),
                call(A, "title(string)", &["Dr."]),
                call(A, "title(string)", &[LONG]),
                call(A, "requireName(string)", &["nope"]),
                call(A, "requireName(string)", &[LONG]),
                send(A, "rename(string)", &[&a31]),
                call(A, "name()", &[]),
                send(A, "describe(string)", &["short"]),
                call(A, "description()", &[]),
                send(A, "rename(string)", &[&b32]),
                call(A, "name()", &[]),
                send(A, "rename(string)", &[""]),
                call(A, "name()", &[]),
                call(B, "describe(string)", &["x"]),
            ],
        ),
        (
            "logs",
            vec![],
            vec![
                send(A, "move(address,uint256)", &[B, "1"]),
                send(B, "move(address,uint256)", &[A, "1"]),
                send(A, "note(uint256,string)", &["1", "hi"]),
                send(A, "note(uint256,string)", &["2", LONG]),
                send(A, "tick()", &[]),
                send(B, "tick()", &[]),
            ],
        ),
        (
            "math",
            vec![],
            vec![
                call(A, "mulDiv(uint256,uint256,uint256)", &["10", "20", "3"]),
                call(A, "mulDiv(uint256,uint256,uint256)", &["1", "2", "0"]),
                call(A, "average(uint256,uint256)", &["7", "9"]),
                call(A, "distance(int256,int256)", &["-5", "3"]),
                call(A, "narrow(uint256)", &["255"]),
                call(A, "narrow(uint256)", &["256"]),
                call(A, "mix(uint32,uint32)", &["10", "20"]),
                call(A, "mix(uint32,uint32)", &["4000000000", "4000000000"]),
                send(A, "store(uint256,uint256)", &["12", "5"]),
            ],
        ),
        (
            "loops",
            vec![],
            vec![
                call(A, "sum(uint256[])", &["[1,2,3,4,5]"]),
                call(A, "sum(uint256[])", &["[]"]),
                send(A, "airdrop(address[],uint256)", &[&airdrop, "7"]),
                call(A, "balanceOf(address)", &[A]),
                send(A, "join(address)", &[A]),
                send(A, "join(address)", &[B]),
                send(
                    A,
                    "join(address)",
                    &["0x0000000000000000000000000000000000000003"],
                ),
                send(A, "markAll()", &[]),
                call(A, "isOwner(address)", &[B]),
                call(A, "find(address)", &[B]),
                call(
                    A,
                    "find(address)",
                    &["0x0000000000000000000000000000000000000009"],
                ),
                call(A, "gcd(uint256,uint256)", &["1071", "462"]),
                call(A, "gcd(uint256,uint256)", &["7", "0"]),
                call(A, "hashChain(bytes32,uint256)", &[&hash, "20"]),
                pay(A, "payout(address[])", &[&payout], "1ether"),
                pay(A, "payout(address[])", &["[]"], "1"),
            ],
        ),
        (
            "tally",
            vec![],
            vec![
                send(A, "vote(bytes32,uint256)", &[&v1, "3"]),
                send(B, "vote(bytes32,uint256)", &[&v1, "5"]),
                send(A, "vote(bytes32,uint256)", &[&v2, "7"]),
                send(B, "vote(bytes32,uint256)", &[&v2, "0"]),
                send(B, "vote(bytes32,uint256)", &[&v3, &max]),
                call(A, "votesOf(address)", &[A]),
                call(A, "votesOf(address)", &[B]),
                call(A, "votesFor(bytes32)", &[&v1]),
                call(A, "votesFor(bytes32)", &[&v3]),
                call(A, "totalVotes()", &[]),
            ],
        ),
        (
            "erc20",
            vec![A],
            vec![
                call(A, "name()", &[]),
                call(A, "symbol()", &[]),
                call(A, "decimals()", &[]),
                call(A, "owner()", &[]),
                send(A, "mint(address,uint256)", &[A, &e1000]),
                send(B, "mint(address,uint256)", &[B, "5"]),
                send(A, "mint(address,uint256)", &[ZERO, "1"]),
                send(A, "transfer(address,uint256)", &[B, &e100]),
                call(A, "transfer(address,uint256)", &[B, "1"]),
                send(A, "transfer(address,uint256)", &[ZERO, "1"]),
                send(B, "transfer(address,uint256)", &[A, &huge]),
                send(A, "approve(address,uint256)", &[B, &e500]),
                send(A, "approve(address,uint256)", &[ZERO, "1"]),
                call(A, "allowance(address,address)", &[A, B]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, &e200]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, &e400]),
                send(B, "transferFrom(address,address,uint256)", &[A, ZERO, "1"]),
                send(A, "approve(address,uint256)", &[B, &max]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "1"]),
                call(A, "allowance(address,address)", &[A, B]),
                send(B, "burn(uint256)", &[&e10]),
                send(B, "burn(uint256)", &[&huge]),
                send(B, "burnFrom(address,uint256)", &[A, &e5]),
                send(A, "burnFrom(address,uint256)", &[B, "1"]),
                send(B, "pause()", &[]),
                send(A, "pause()", &[]),
                send(A, "pause()", &[]),
                call(A, "paused()", &[]),
                send(A, "transfer(address,uint256)", &[B, "1"]),
                send(A, "transfer(address,uint256)", &[ZERO, "1"]),
                send(A, "mint(address,uint256)", &[A, "1"]),
                send(A, "approve(address,uint256)", &[B, "7"]),
                send(A, "unpause()", &[]),
                send(A, "unpause()", &[]),
                send(A, "transferOwnership(address)", &[ZERO]),
                send(A, "transferOwnership(address)", &[B]),
                send(A, "mint(address,uint256)", &[A, "1"]),
                send(B, "renounceOwnership()", &[]),
                call(A, "owner()", &[]),
                call(A, "totalSupply()", &[]),
                call(A, "balanceOf(address)", &[A]),
                call(A, "balanceOf(address)", &[B]),
            ],
        ),
    ]
}

#[test]
fn bench_gas() {
    let rows: Vec<String> = scenarios()
        .iter()
        .map(|(name, ctor, steps)| {
            let r = replay(name, ctor, steps);
            assert!(r.runtime_bytes > 0 && r.gas > 0, "{name}");
            format!(
                "  \"{name}\": {{\"runtime_bytes\": {}, \"deploy_gas\": {}, \"gas\": {}}}",
                r.runtime_bytes, r.deploy_gas, r.gas
            )
        })
        .collect();
    if let Some(path) = std::env::var_os("LITHE_BENCH_OUT") {
        std::fs::write(&path, format!("{{\n{}\n}}\n", rows.join(",\n")))
            .unwrap_or_else(|e| panic!("{}: {e}", path.to_string_lossy()));
    }
}

#[test]
fn meter_prices_storage_by_access() {
    let at = SELF.get();
    let (zero, one) = (Word::from_u64(0), Word::from_u64(1));
    let storage = HashMap::new();
    let ((), cold_set) = metered(one, || charge(0x55, &[one, zero], &storage, at));
    let ((), warm) = metered(one, || {
        charge(0x54, &[zero], &storage, at);
        charge(0x54, &[zero], &storage, at);
    });
    assert_eq!((cold_set, warm), (2_100 + 20_000, 2_100 + 100));
    assert!(!metering());
}
