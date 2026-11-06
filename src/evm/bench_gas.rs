//! Benchmark gas without solc or a node: replays `bench/run.py`'s scenarios and suites
//! through the interpreter with a gas meter on, and writes each one's runtime size, deploy
//! gas, transaction gas, and ordered step outcomes (status and Keccak-256 returndata hash)
//! to `$LITHE_BENCH_OUT` as JSON when it is set. A suite's runtime size sums every contract
//! it deploys.
//!
//! Each suite deploys its contracts from account A into one shared world, at the addresses
//! anvil gives A's first deployments, so they call each other, then replays its steps; block
//! numbers advance one per deployment and send, as anvil mines them. The steps are `run.py`'s,
//! generated from it: calldata it builds by hand, or with tuples or nested lists, is literal
//! hex here, and permits and delegations are signed here over the domain the target reports.
//!
//! Plain `cargo test` replays only `SMOKE`; `LITHE_BENCH_OUT` or `LITHE_BENCH_GAS` replays all.
//!
//! simplify: the meter prices Osaka's opcodes, memory expansion, EIP-2929/2200 warm and cold
//! storage and calls, the intrinsic and calldata cost, and deployment's code deposit. Its
//! totals track codegen changes between builds and do not match a node's receipts, because:
//! - there are no refunds, no EIP-7623 calldata floor, and no transaction access lists;
//! - nothing limits gas: no 63/64 rule, no call stipend, and `GAS` answers a constant;
//! - a value call to a new account costs no 25 000, and precompiles cost nothing;
//! - `BALANCE`, `EXTCODESIZE`, `EXTCODECOPY`, and `EXTCODEHASH` always cost the warm 100;
//! - accounts and slots stay warm when the frame that touched them reverts;
//! - a creation during a transaction costs no `CREATE2` hashing and no code deposit;
//! - a zero-length memory access past the end still grows memory, and is charged for it;
//! - `TIMESTAMP` is the interpreter's constant, so `run.py`'s waits are dropped: Uniswap's
//!   price accumulators and the staking rewards never grow;
//! - only the contract a transaction targets holds a balance; contracts it calls hold none.
//!
//! Price those when a number has to match anvil's.

use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use super::{
    compile_file, construct, elsewhere, exec, hex_bytes, hex_decode, load_bytes, word_usize,
    Outcome, BLOCK, DEPLOYED, FACETS, NONCE, SELF,
};
use crate::keccak::{keccak256, selector};
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

/// Runs `f` as one transaction from `from` to `to`, returning its execution gas.
fn metered<T>(from: Word, to: Word, f: impl FnOnce() -> T) -> (T, u64) {
    let accounts = [from, to]
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
/// anvil's keys for A and B.
const KEY_A: &str = "0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80";
const KEY_B: &str = "0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d";
const ZERO: &str = "0x0000000000000000000000000000000000000000";
const LONG: &str = "a string that is well past thirty one bytes long";
const MAX: &str = "115792089237316195423570985008687907853269984665640564039457584007913129639935";
const PERMIT: &str =
    "Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)";
const DELEGATION: &str = "Delegation(address delegatee,uint256 nonce,uint256 expiry)";

/// The suites plain `cargo test` replays: single contracts and a shared world, cheap to build.
const SMOKE: &[&str] = &["counter", "token", "swap"];

enum Kind {
    Send,
    Call,
    /// A call whose answer becomes the named role, as an address or a word.
    Bind(&'static str),
}

/// A transaction, or a call, to a suite's role. `sig` is a signature, or whole calldata in
/// hex; `$role` arguments name a role's address. A signed step appends the `v`, `r`, and
/// `s` of `key`'s EIP-712 signature over the target's domain of the struct `ty` with `fields`.
struct Step {
    kind: Kind,
    from: &'static str,
    to: &'static str,
    sig: String,
    args: Vec<String>,
    value: &'static str,
    must_succeed: bool,
    sign: Option<(&'static str, Vec<String>, &'static str)>,
}

impl Step {
    fn succeeds(self) -> Step {
        Step {
            must_succeed: true,
            ..self
        }
    }

    fn on(self, to: &'static str) -> Step {
        Step { to, ..self }
    }

    fn paying(self, value: &'static str) -> Step {
        Step { value, ..self }
    }

    fn signed(self, ty: &'static str, fields: &[&str], key: &'static str) -> Step {
        let fields = fields.iter().map(|f| f.to_string()).collect();
        Step {
            sign: Some((ty, fields, key)),
            ..self
        }
    }
}

fn step(kind: Kind, from: &'static str, sig: &str, args: &[&str]) -> Step {
    Step {
        kind,
        from,
        to: "",
        sig: sig.to_string(),
        args: args.iter().map(|a| a.to_string()).collect(),
        value: "0",
        sign: None,
        must_succeed: false,
    }
}

fn send(from: &'static str, sig: &str, args: &[&str]) -> Step {
    step(Kind::Send, from, sig, args)
}

fn call(from: &'static str, sig: &str, args: &[&str]) -> Step {
    step(Kind::Call, from, sig, args)
}

fn bind(role: &'static str, to: &'static str, sig: &str, args: &[&str]) -> Step {
    step(Kind::Bind(role), A, sig, args).on(to)
}

/// A role, the `bench/` contract deployed for it, and its constructor's parameter types
/// and arguments.
struct Deploy(&'static str, &'static str, &'static str, Vec<String>);

fn deploy(role: &'static str, pair: &'static str, types: &'static str, args: &[&str]) -> Deploy {
    Deploy(
        role,
        pair,
        types,
        args.iter().map(|a| a.to_string()).collect(),
    )
}

struct Suite {
    name: &'static str,
    deploy: Vec<Deploy>,
    steps: Vec<Step>,
}

fn suite(name: &'static str, deploy: Vec<Deploy>, steps: Vec<Step>) -> Suite {
    Suite {
        name,
        deploy,
        steps,
    }
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

/// The ABI encoding of one value of `ty`, as `cast` takes it, and whether it is dynamic.
fn value(ty: &str, text: &str) -> (bool, Vec<u8>) {
    let padded = |mut data: Vec<u8>| {
        let mut out = Word::from_u64(data.len() as u64).to_be_bytes().to_vec();
        data.resize(data.len().div_ceil(32) * 32, 0);
        out.extend(data);
        out
    };
    if let Some(item) = ty.strip_suffix("[]") {
        let inner = &text[1..text.len() - 1];
        let items: Vec<&str> = if inner.is_empty() {
            Vec::new()
        } else {
            inner.split(',').collect()
        };
        let mut out = Word::from_u64(items.len() as u64).to_be_bytes().to_vec();
        out.extend(tuple(items.iter().map(|t| value(item, t)).collect()));
        return (true, out);
    }
    match ty {
        "string" => (true, padded(text.as_bytes().to_vec())),
        "bytes" => (true, padded(hex_decode(&text[2..]))),
        _ if ty.starts_with("bytes") => {
            let mut data = hex_decode(&text[2..]);
            data.resize(32, 0);
            (false, data)
        }
        _ => (false, word(text).to_be_bytes().to_vec()),
    }
}

/// Heads, then the tails of the dynamic values.
fn tuple(values: Vec<(bool, Vec<u8>)>) -> Vec<u8> {
    let (mut head, mut tail) = (Vec::new(), Vec::new());
    let size = 32 * values.len();
    for (dynamic, data) in values {
        if dynamic {
            head.extend(Word::from_u64((size + tail.len()) as u64).to_be_bytes());
            tail.extend(data);
        } else {
            head.extend(data);
        }
    }
    head.extend(tail);
    head
}

/// Encodes `args` for the flat parameter list `types`.
fn encode(types: &str, args: &[String]) -> Vec<u8> {
    let types = types.split(',').filter(|t| !t.is_empty());
    tuple(types.zip(args).map(|(ty, a)| value(ty, a)).collect())
}

fn calldata(sig: &str, args: &[String]) -> Vec<u8> {
    if let Some(data) = sig.strip_prefix("0x") {
        return hex_decode(data);
    }
    let params = &sig[sig.find('(').expect("signature") + 1..sig.len() - 1];
    let mut out = selector(sig).to_vec();
    out.extend(encode(params, args));
    out
}

/// Where `CREATE` from `creator` with `nonce`, below 128, puts a contract, as a node does.
fn created(creator: Word, nonce: u8) -> Word {
    let mut rlp = vec![0xd6, 0x94];
    rlp.extend(&creator.to_be_bytes()[12..]);
    rlp.push(if nonce == 0 { 0x80 } else { nonce });
    let mut at = keccak256(&rlp);
    at[..12].fill(0);
    Word::from_be_bytes(at)
}

fn hex_word(w: Word) -> String {
    format!("0x{}", hex_bytes(&w.to_be_bytes()))
}

/// `key`'s signature of the EIP-712 `digest` of the struct `ty` with `fields` in `domain`:
/// `v`, `r`, and `s`.
fn sign(domain: Word, ty: &str, fields: &[String], key: &str) -> [String; 3] {
    let mut data = keccak256(ty.as_bytes()).to_vec();
    data.extend(fields.iter().flat_map(|f| word(f).to_be_bytes()));
    let mut message = vec![0x19, 0x01];
    message.extend(domain.to_be_bytes());
    message.extend(keccak256(&data));
    let digest = Word::from_be_bytes(keccak256(&message));
    let key = word(key);
    let nonce = [key.to_be_bytes(), digest.to_be_bytes()].concat();
    let (v, r, s) = crate::hash::sign(digest, key, Word::from_be_bytes(keccak256(&nonce)));
    [v.to_string(), hex_word(r), hex_word(s)]
}

struct Measured {
    runtime_bytes: usize,
    deploy_gas: u64,
    gas: u64,
    outcomes: Vec<String>,
}

/// One transaction from `from` to the contract at `to`, with its gas, kept only when
/// `keep` and it succeeds.
fn transact(
    from: Word,
    to: Word,
    data: &[u8],
    value: Word,
    keep: bool,
    balances: &mut HashMap<Word, Word>,
) -> (Outcome, u64) {
    let world = (DEPLOYED.with(|d| d.borrow().clone()), NONCE.get());
    let (code, storage) = world.0[&to].clone();
    let balance = balances.get(&to).copied().unwrap_or(Word::from_u64(0));
    let (out, gas) = metered(from, to, || {
        elsewhere(to, || {
            exec(
                &code,
                data,
                storage,
                from,
                value,
                balance.wrapping_add(value),
            )
        })
    });
    let out = out.unwrap_or_else(|e| panic!("{}: {e}", hex_bytes(data)));
    if keep && !out.reverted {
        DEPLOYED.with(|d| d.borrow_mut().get_mut(&to).expect("target").1 = out.storage.clone());
        balances.insert(to, out.self_balance);
    } else {
        DEPLOYED.with(|d| *d.borrow_mut() = world.0);
        NONCE.set(world.1);
    }
    (out, intrinsic(data) + gas)
}

/// Deploys `suite`'s contracts from A into a fresh world, then runs its steps, counting the
/// gas of each send and call.
fn replay(suite: &Suite) -> Measured {
    let name = suite.name;
    DEPLOYED.with(|d| d.borrow_mut().clear());
    FACETS.with(|f| f.borrow_mut().clear());
    NONCE.set(1);
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let deployer = word(A);
    let mut built: HashMap<&str, Vec<u8>> = HashMap::new();
    let mut roles: HashMap<&str, Word> = HashMap::new();
    let fill = |args: &[String], roles: &HashMap<&str, Word>| -> Vec<String> {
        let role = |a: &String| a.strip_prefix('$').map(|r| hex_word(roles[r]));
        args.iter()
            .map(|a| role(a).unwrap_or_else(|| a.clone()))
            .collect()
    };
    let (mut block, mut runtime_bytes, mut deploy_gas) = (0, 0, 0);
    for (n, Deploy(role, pair, types, args)) in suite.deploy.iter().enumerate() {
        let mut init = built
            .entry(pair)
            .or_insert_with(|| {
                compile_file(&root.join(format!("bench/{pair}.lithe")))
                    .unwrap_or_else(|e| panic!("{pair}: {e}"))
            })
            .clone();
        init.extend(encode(types, &fill(args, &roles)));
        let at = created(deployer, n as u8);
        block += 1;
        BLOCK.set(block);
        let (made, gas) = metered(deployer, at, || {
            elsewhere(at, || construct(&init, deployer, Word::from_u64(0)))
        });
        let made = made.unwrap_or_else(|e| panic!("{name} {role}: {e}"));
        assert!(!made.reverted, "{name}: {role} reverted");
        let runtime = made.returndata;
        runtime_bytes += runtime.len();
        deploy_gas += intrinsic(&init)
            + 32_000
            + 2 * (init.len() as u64).div_ceil(32)
            + 200 * runtime.len() as u64
            + gas;
        DEPLOYED.with(|d| d.borrow_mut().insert(at, (runtime, made.storage)));
        roles.insert(role, at);
    }
    let main = suite.deploy[0].0;
    let mut balances = HashMap::new();
    let (mut total, mut succeeded) = (0, false);
    let mut outcomes = Vec::new();
    for s in &suite.steps {
        let to = roles[if s.to.is_empty() { main } else { s.to }];
        let mut args = fill(&s.args, &roles);
        if let Some((ty, fields, key)) = &s.sign {
            let data = selector("DOMAIN_SEPARATOR()");
            let (out, _) = transact(deployer, to, &data, Word::from_u64(0), false, &mut balances);
            let domain = load_bytes(&out.returndata, 0);
            args.extend(sign(domain, ty, &fill(fields, &roles), key));
        }
        let data = calldata(&s.sig, &args);
        let (from, value) = (word(s.from), word(s.value));
        if let Kind::Send = s.kind {
            block += 1;
            BLOCK.set(block);
        }
        let keep = matches!(s.kind, Kind::Send);
        let (out, gas) = transact(from, to, &data, value, keep, &mut balances);
        assert!(
            !s.must_succeed || !out.reverted,
            "{name}: {} reverted: {}",
            s.sig,
            hex_bytes(&out.returndata)
        );
        outcomes.push(format!(
            "{{\"status\":\"{}\",\"returndata_hash\":\"{}\"}}",
            if out.reverted { "revert" } else { "ok" },
            hex_bytes(&keccak256(&out.returndata)),
        ));
        if let Kind::Bind(role) = s.kind {
            roles.insert(role, load_bytes(&out.returndata, 0));
        } else {
            total += gas;
            succeeded |= !out.reverted;
        }
    }
    DEPLOYED.with(|d| d.borrow_mut().clear());
    FACETS.with(|f| f.borrow_mut().clear());
    assert!(succeeded, "{name}: every step reverted");
    Measured {
        runtime_bytes,
        deploy_gas,
        gas: total,
        outcomes,
    }
}

fn suites() -> Vec<Suite> {
    vec![
        suite(
            "codec",
            vec![deploy("codec", "codec", "", &[])],
            vec![
                call(A, "encFlat(address,uint256,string)", &[B, "7", LONG]),
                call(A, "decFlat(bytes)", &["0x00000000000000000000000070997970c51812dc3a010c7d01b50e0d17dc79c80000000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000306120737472696e6720746861742069732077656c6c207061737420746869727479206f6e65206279746573206c6f6e6700000000000000000000000000000000"]),
                call(A, "decFlat(bytes)", &["0x0000000000000000000000000000000000000000000000000000000000000001"]),
                call(A, "0xb027a467000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000016000000000000000000000000000000000000000000000000000000000000002400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000566697273740000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000306120737472696e6720746861742069732077656c6c207061737420746869727479206f6e65206279746573206c6f6e67000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000007", &[]),
                call(A, "0xb027a46700000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000", &[]),
                call(A, "decOrders(bytes)", &["0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000016000000000000000000000000000000000000000000000000000000000000002400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000566697273740000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000306120737472696e6720746861742069732077656c6c207061737420746869727479206f6e65206279746573206c6f6e67000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000007"]),
                call(A, "decOrders(bytes)", &["0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000001000"]),
                call(A, "decOrders(bytes)", &["0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000010000000000000000"]),
                call(A, "0x4157ec9500000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000005", &[]),
                call(A, "decGrid(bytes)", &["0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000005"]),
                call(A, "packed(address,uint96,string)", &[A, "5", LONG]),
                call(A, "0x5039d96f000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000016000000000000000000000000000000000000000000000000000000000000002400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000566697273740000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000306120737472696e6720746861742069732077656c6c207061737420746869727479206f6e65206279746573206c6f6e67000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000007", &[]),
                send(A, "keep(bytes)", &["0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000016000000000000000000000000000000000000000000000000000000000000002400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000566697273740000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000306120737472696e6720746861742069732077656c6c207061737420746869727479206f6e65206279746573206c6f6e67000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000007"]),
                call(A, "seen()", &[]),
                call(A, "digest()", &[]),
            ],
        ),
        suite(
            "counter",
            vec![deploy("counter", "counter", "", &[])],
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
        suite(
            "token",
            vec![deploy("token", "token", "", &[])],
            vec![
                send(A, "mint(address,uint256)", &[A, "1000"]),
                send(A, "mint(address,uint256)", &[B, "50"]),
                send(A, "transfer(address,uint256)", &[B, "100"]),
                send(B, "transfer(address,uint256)", &[A, "999"]),
                send(B, "mint(address,uint256)", &[B, "1"]),
                send(B, "transfer(address,uint256)", &[A, "150"]),
                send(A, "0xa9059cbb00000000000000000000000070997970c51812dc3a010c7d01b50e0d17dc79c8", &[]),
                send(A, "0xa9059cbb00000000000000000000000070997970c51812dc3a010c7d01b50e0d17dc79c800000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000009", &[]),
                send(A, "0x40c10f1900000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001", &[]),
                call(A, "balanceOf(address)", &[A]),
                call(A, "totalSupply()", &[]),
            ],
        ),
        suite(
            "traits",
            vec![deploy("traits", "traits", "", &[])],
            vec![
                send(A, "mint(uint256)", &["3"]),
                send(A, "tag(uint256,string)", &["1", "Background"]),
                send(A, "tag(uint256,string)", &["1", ""]),
                call(A, "tag(uint256,string)", &["1", ""]),
                send(A, "tag(uint256,string)", &["9", "Background"]),
                call(A, "tag(uint256,string)", &["9", "Background"]),
                call(A, "tag(uint256,string)", &["9", LONG]),
                call(A, "background(uint256)", &["2"]),
                call(A, "background(uint256)", &["3"]),
                call(A, "check(uint256[])", &["[0,1,2]"]),
                call(A, "check(uint256[])", &["[0,5,1]"]),
                call(A, "check(uint256[])", &["[]"]),
            ],
        ),
        suite(
            "shapes",
            vec![deploy("shapes", "shapes", "", &[])],
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
                call(A, "buy(uint256,string)", &["1", "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"]),
                call(A, "buyAll(uint256[],string)", &["[]", "nothing to buy"]),
                call(A, "buyAll(uint256[],string)", &["[1,2,3,4,5]", LONG]),
                send(A, "buyAll(uint256[],string)", &["[1,9]", "n"]),
                call(A, "buyAll(uint256[],string)", &["[1,9]", "n"]),
                call(A, "buyAll(uint256[],string)", &["[0,1]", LONG]),
                send(A, "buyAll(uint256[],string)", &["[1,2]", "ok"]),
                call(A, "load(bytes)", &["0x"]),
                send(A, "load(bytes)", &["0xdeadbeef"]),
                call(B, "load(bytes)", &["0xdeadbeef"]),
                call(A, "load(bytes)", &["0xababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababab"]),
                call(A, "compare(string,string)", &["abc", "abc"]),
                call(A, "compare(string,string)", &["abc", "abd"]),
                call(A, "compare(string,string)", &[LONG, "x"]),
                call(A, "compare(string,string)", &["", ""]),
            ],
        ),
        suite(
            "reasons",
            vec![deploy("reasons", "reasons", "", &[])],
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
        suite(
            "strings",
            vec![deploy("strings", "strings", "", &[])],
            vec![
                send(A, "rename(string)", &["Short"]),
                send(A, "rename(string)", &["Short"]),
                call(A, "rename(string)", &["Short"]),
                send(A, "rename(string)", &[LONG]),
                call(A, "rename(string)", &[LONG]),
                send(B, "rename(string)", &["Other"]),
                call(B, "rename(string)", &["Other"]),
                call(A, "rename(string)", &["nnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnn"]),
                send(A, "describe(string)", &["a description that is well past one word in length"]),
                call(B, "describe(string)", &["x"]),
                call(A, "describe(string)", &[&"d".repeat(201)]),
                call(A, "description()", &[]),
                call(A, "name()", &[]),
                call(A, "title(string)", &["Dr."]),
                call(A, "title(string)", &[LONG]),
                call(A, "requireName(string)", &["nope"]),
                call(A, "requireName(string)", &[LONG]),
                send(A, "rename(string)", &["aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"]),
                call(A, "name()", &[]),
                send(A, "describe(string)", &["short"]),
                call(A, "description()", &[]),
                send(A, "rename(string)", &["bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"]),
                call(A, "name()", &[]),
                send(A, "rename(string)", &[""]),
                call(A, "name()", &[]),
                call(B, "describe(string)", &["x"]),
            ],
        ),
        suite(
            "vault",
            vec![deploy("vault", "vault", "", &[])],
            vec![
                send(A, "deposit()", &[]).paying("1000000000000000000"),
                send(B, "deposit()", &[]).paying("500000000000000000"),
                send(A, "withdraw(uint256)", &["300000000000000000"]),
                send(B, "withdraw(uint256)", &["5000000000000000000"]),
                send(B, "setPaused(bool)", &["true"]),
                send(A, "setPaused(bool)", &["true"]),
                send(A, "deposit()", &[]).paying("1"),
                send(A, "setPaused(bool)", &["false"]),
                send(A, "withdraw(uint256)", &["100"]).paying("1"),
                call(A, "depositOf(address)", &[A]),
            ],
        ),
        suite(
            "selectors",
            vec![deploy("selectors", "selectors", "", &[])],
            vec![
                send(A, "handle(bytes4)", &["0xb6b55f25"]),
                send(B, "handle(bytes4)", &["0xb6b55f25"]),
                send(A, "handle(bytes4)", &["0x00f714ce"]),
                send(A, "handle(bytes4)", &["0xa9059cbb"]),
                send(A, "handle(bytes4)", &["0x70a08231"]),
                call(A, "handle(bytes4)", &["0xdeadbeef"]),
                call(A, "handled(bytes4)", &["0xb6b55f25"]),
                call(A, "transferCall(address,uint256)", &[B, "7"]),
                call(A, "ids()", &[]),
            ],
        ),
        suite(
            "logs",
            vec![deploy("logs", "logs", "", &[])],
            vec![
                send(A, "move(address,uint256)", &[B, "1"]),
                send(B, "move(address,uint256)", &[A, "1"]),
                send(A, "note(uint256,string)", &["1", "hi"]),
                send(A, "note(uint256,string)", &["2", LONG]),
                send(A, "tick()", &[]),
                send(B, "tick()", &[]),
            ],
        ),
        suite(
            "env",
            vec![deploy("env", "env", "", &[])],
            vec![
                send(A, "deposit()", &[]).paying("1000000000000000000"),
                send(B, "deposit()", &[]).paying("500000000000000000"),
                call(A, "deposit()", &[]),
                call(A, "blobFee()", &[]),
            ],
        ),
        suite(
            "date_time",
            vec![deploy("date_time", "date_time", "", &[])],
            vec![
                send(A, "startOn(uint256,uint256,uint256)", &["2024", "1", "31"]),
                send(A, "renew(uint256)", &["1"]),
                send(A, "renew(uint256)", &["13"]),
                send(A, "extend(uint256)", &["4"]),
                call(A, "renewalDate()", &[]),
                call(A, "monthsActive(uint256)", &["1727600000"]),
                call(A, "yearsActive(uint256)", &["1727600000"]),
                call(A, "monthsActive(uint256)", &["1000"]),
                call(A, "stamp(uint256,uint256,uint256,uint256,uint256,uint256)", &["2024", "9", "29", "10", "20", "30"]),
                call(A, "parts(uint256)", &["1727600000"]),
                call(A, "weekdayOf(uint256)", &["1727600000"]),
                call(A, "valid(uint256,uint256,uint256)", &["2023", "2", "29"]),
                call(A, "valid(uint256,uint256,uint256)", &["2024", "2", "29"]),
                call(A, "daysIn(uint256,uint256)", &["2024", "2"]),
                call(A, "daysIn(uint256,uint256)", &["2023", "13"]),
            ],
        ),
        suite(
            "math",
            vec![deploy("math", "math", "", &[])],
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
        suite(
            "numerics",
            vec![deploy("numerics", "numerics", "", &[])],
            vec![
                call(A, "pow(uint256,uint256)", &["3", "5"]),
                call(A, "pow(uint256,uint256)", &["0", "0"]),
                call(A, "pow(uint256,uint256)", &["1", MAX]),
                call(A, "pow(uint256,uint256)", &[MAX, "1"]),
                call(A, "pow(uint256,uint256)", &["10", "77"]),
                call(A, "pow(uint256,uint256)", &["10", "78"]),
                call(A, "pow(uint256,uint256)", &["2", "256"]),
                call(A, "units(uint8)", &["0"]),
                call(A, "units(uint8)", &["18"]),
                call(A, "units(uint8)", &["77"]),
                call(A, "units(uint8)", &["78"]),
                call(A, "units(uint8)", &["255"]),
                call(A, "powSigned(int256,uint256)", &["-3", "5"]),
                call(A, "powSigned(int256,uint256)", &["-2", "255"]),
                call(A, "powSigned(int256,uint256)", &["-2", "256"]),
                call(A, "powSigned(int256,uint256)", &["2", "255"]),
                call(A, "powSigned(int256,uint256)", &["-1", MAX]),
                call(A, "powSigned(int256,uint256)", &["-57896044618658097711785492504343953926634992332820282019728792003956564819968", "1"]),
                call(A, "powSigned(int256,uint256)", &["-57896044618658097711785492504343953926634992332820282019728792003956564819968", "2"]),
                call(A, "pow2(uint256)", &["0"]),
                call(A, "pow2(uint256)", &["255"]),
                call(A, "pow2(uint256)", &["256"]),
                call(A, "sqrt(uint256)", &["0"]),
                call(A, "sqrt(uint256)", &["1"]),
                call(A, "sqrt(uint256)", &["2"]),
                call(A, "sqrt(uint256)", &["1000000000000000000"]),
                call(A, "sqrt(uint256)", &[MAX]),
                call(A, "log2(uint256)", &["0"]),
                call(A, "log2(uint256)", &["1"]),
                call(A, "log2(uint256)", &["340282366920938463463374607431768211456"]),
                call(A, "log2(uint256)", &[MAX]),
                call(A, "log10(uint256)", &["0"]),
                call(A, "log10(uint256)", &["9"]),
                call(A, "log10(uint256)", &["10"]),
                call(A, "log10(uint256)", &["10000000000000000000000000000000000000000000000000000000000000000"]),
                call(A, "log10(uint256)", &[MAX]),
                call(A, "log256(uint256)", &["0"]),
                call(A, "log256(uint256)", &["1"]),
                call(A, "log256(uint256)", &["2"]),
                call(A, "log256(uint256)", &["1000000000000000000"]),
                call(A, "log256(uint256)", &["340282366920938463463374607431768211456"]),
                call(A, "log256(uint256)", &["340282366920938463463374607431768211457"]),
                call(A, "log256(uint256)", &[MAX]),
                call(A, "log2Up(uint256)", &["0"]),
                call(A, "log2Up(uint256)", &["1"]),
                call(A, "log2Up(uint256)", &["2"]),
                call(A, "log2Up(uint256)", &["1000000000000000000"]),
                call(A, "log2Up(uint256)", &["340282366920938463463374607431768211456"]),
                call(A, "log2Up(uint256)", &["340282366920938463463374607431768211457"]),
                call(A, "log2Up(uint256)", &[MAX]),
                call(A, "log10Up(uint256)", &["0"]),
                call(A, "log10Up(uint256)", &["1"]),
                call(A, "log10Up(uint256)", &["2"]),
                call(A, "log10Up(uint256)", &["1000000000000000000"]),
                call(A, "log10Up(uint256)", &["340282366920938463463374607431768211456"]),
                call(A, "log10Up(uint256)", &["340282366920938463463374607431768211457"]),
                call(A, "log10Up(uint256)", &[MAX]),
                call(A, "log256Up(uint256)", &["0"]),
                call(A, "log256Up(uint256)", &["1"]),
                call(A, "log256Up(uint256)", &["2"]),
                call(A, "log256Up(uint256)", &["1000000000000000000"]),
                call(A, "log256Up(uint256)", &["340282366920938463463374607431768211456"]),
                call(A, "log256Up(uint256)", &["340282366920938463463374607431768211457"]),
                call(A, "log256Up(uint256)", &[MAX]),
                call(A, "clz(uint256)", &["0"]),
                call(A, "clz(uint256)", &["1"]),
                call(A, "clz(uint256)", &["2"]),
                call(A, "clz(uint256)", &["1000000000000000000"]),
                call(A, "clz(uint256)", &["340282366920938463463374607431768211456"]),
                call(A, "clz(uint256)", &["340282366920938463463374607431768211457"]),
                call(A, "clz(uint256)", &[MAX]),
                call(A, "abs(int256)", &["0"]),
                call(A, "abs(int256)", &["-1"]),
                call(A, "abs(int256)", &["57896044618658097711785492504343953926634992332820282019728792003956564819967"]),
                call(A, "abs(int256)", &["-57896044618658097711785492504343953926634992332820282019728792003956564819968"]),
                call(A, "min(int256,int256)", &["-5", "3"]),
                call(A, "min(int256,int256)", &["57896044618658097711785492504343953926634992332820282019728792003956564819967", "-57896044618658097711785492504343953926634992332820282019728792003956564819968"]),
                call(A, "max(int256,int256)", &["-5", "3"]),
                call(A, "max(int256,int256)", &["57896044618658097711785492504343953926634992332820282019728792003956564819967", "-57896044618658097711785492504343953926634992332820282019728792003956564819968"]),
                call(A, "average(int256,int256)", &["-7", "2"]),
                call(A, "average(int256,int256)", &["-3", "-4"]),
                call(A, "average(int256,int256)", &["-57896044618658097711785492504343953926634992332820282019728792003956564819968", "57896044618658097711785492504343953926634992332820282019728792003956564819967"]),
                call(A, "average(int256,int256)", &["57896044618658097711785492504343953926634992332820282019728792003956564819967", "57896044618658097711785492504343953926634992332820282019728792003956564819967"]),
                call(A, "average(int256,int256)", &["-57896044618658097711785492504343953926634992332820282019728792003956564819968", "-57896044618658097711785492504343953926634992332820282019728792003956564819968"]),
                call(A, "clamp(int256,int256,int256)", &["5", "-1", "3"]),
                call(A, "clamp(int256,int256,int256)", &["-9", "-1", "3"]),
                call(A, "clamp(int256,int256,int256)", &["0", "-1", "3"]),
                call(A, "clamp(int256,int256,int256)", &["-57896044618658097711785492504343953926634992332820282019728792003956564819968", "-57896044618658097711785492504343953926634992332820282019728792003956564819968", "57896044618658097711785492504343953926634992332820282019728792003956564819967"]),
                call(A, "clamp(int256,int256,int256)", &["0", "3", "-1"]),
                call(A, "hexNat(uint256)", &["0"]),
                call(A, "hexNat(uint256)", &["255"]),
                call(A, "hexNat(uint256)", &["256"]),
                call(A, "hexNat(uint256)", &[MAX]),
                call(A, "hexFixed(uint256,uint256)", &["0", "0"]),
                call(A, "hexFixed(uint256,uint256)", &["255", "1"]),
                call(A, "hexFixed(uint256,uint256)", &["4660", "4"]),
                call(A, "hexFixed(uint256,uint256)", &["1", "32"]),
                call(A, "hexFixed(uint256,uint256)", &[MAX, "32"]),
                call(A, "hexAddress(address)", &[A]),
                call(A, "hexAddress(address)", &[ZERO]),
                call(A, "checksum(address)", &[A]),
                call(A, "checksum(address)", &[B]),
                call(A, "checksum(address)", &[ZERO]),
                send(A, "setScale(uint8)", &["18"]),
                send(A, "setScale(uint8)", &["78"]),
                send(A, "setScale(uint8)", &["6"]),
            ],
        ),
        suite(
            "fixed_point",
            vec![deploy("fixed_point", "fixed_point", "", &[])],
            vec![
                call(A, "wadMulUp(uint256,uint256)", &["3", "333333333333333333"]),
                call(A, "wadMulUp(uint256,uint256)", &["1000000000000000000", "1000000000000000000"]),
                call(A, "wadMulUp(uint256,uint256)", &["0", "5"]),
                call(A, "wadMulUp(uint256,uint256)", &["1606938044258990275541962092341162602522202993782792835301376", "100000000000000000000"]),
                call(A, "wadDivUp(uint256,uint256)", &["1", "3"]),
                call(A, "wadDivUp(uint256,uint256)", &["1000000000000000000", "3"]),
                call(A, "wadDivUp(uint256,uint256)", &["1532495540865888858358347027150309183618739122183602176", "7"]),
                call(A, "divWad(uint256,uint256)", &["5", "3"]),
                call(A, "divWad(uint256,uint256)", &["1569275433846670190958947355801916604025588861116008628224", "1000000000000000000"]),
                call(A, "sMulWad(int256,int256)", &["-3", "333333333333333333"]),
                call(A, "sMulWad(int256,int256)", &["-100000000000000000000", "2000000000000000000"]),
                call(A, "sDivWad(int256,int256)", &["-1", "3"]),
                call(A, "sDivWad(int256,int256)", &["100000000000000000000", "-7000000000000000000"]),
                call(A, "expWad(int256)", &["0"]),
                call(A, "expWad(int256)", &["1000000000000000000"]),
                call(A, "expWad(int256)", &["-41446531673892822313"]),
                call(A, "expWad(int256)", &["-41446531673892822312"]),
                call(A, "expWad(int256)", &["135305999368893231588"]),
                call(A, "expWad(int256)", &["135305999368893231589"]),
                call(A, "expWad(int256)", &["-3000000000000000000"]),
                call(A, "lnWad(int256)", &["1"]),
                call(A, "lnWad(int256)", &["1000000000000000000"]),
                call(A, "lnWad(int256)", &["2718281828459045235"]),
                call(A, "lnWad(int256)", &["57896044618658097711785492504343953926634992332820282019728792003956564819967"]),
                call(A, "lnWad(int256)", &["0"]),
                call(A, "lnWad(int256)", &["-5"]),
                call(A, "powWad(int256,int256)", &["2000000000000000000", "500000000000000000"]),
                call(A, "powWad(int256,int256)", &["300000000000000000", "-2000000000000000000"]),
                call(A, "powWad(int256,int256)", &["0", "1000000000000000000"]),
                call(A, "sqrtWad(uint256)", &["0"]),
                call(A, "sqrtWad(uint256)", &["2"]),
                call(A, "sqrtWad(uint256)", &["2000000000000000000"]),
                call(A, "sqrtWad(uint256)", &[MAX]),
                call(A, "cbrtWad(uint256)", &["0"]),
                call(A, "cbrtWad(uint256)", &["2000000000000000000"]),
                call(A, "cbrtWad(uint256)", &["1393796574908163946345982392040522594123776"]),
                call(A, "cbrtWad(uint256)", &["1725436586697640946858688965569256363112777243042596638790631055949824"]),
                call(A, "cbrtWad(uint256)", &[MAX]),
                call(A, "rpow(uint256,uint256,uint256)", &["1000000001000000000", "31536000", "1000000000000000000000000000"]),
                call(A, "rpow(uint256,uint256,uint256)", &["0", "0", "1000000000000000000"]),
                call(A, "rpow(uint256,uint256,uint256)", &["0", "3", "1000000000000000000"]),
                call(A, "rpow(uint256,uint256,uint256)", &["2000000000000000000", "10", "1000000000000000000"]),
                call(A, "rpow(uint256,uint256,uint256)", &["3000000000000000000000000000", "5", "1000000000000000000000000000"]),
                call(A, "cbrt(uint256)", &["0"]),
                call(A, "cbrt(uint256)", &["7"]),
                call(A, "cbrt(uint256)", &["8"]),
                call(A, "cbrt(uint256)", &[MAX]),
                call(A, "dist(uint256,uint256)", &["3", "10"]),
                call(A, "dist(uint256,uint256)", &["10", "3"]),
                call(A, "dist(uint256,uint256)", &["0", MAX]),
                call(A, "distInt(int256,int256)", &["-3", "10"]),
                call(A, "distInt(int256,int256)", &["57896044618658097711785492504343953926634992332820282019728792003956564819967", "-57896044618658097711785492504343953926634992332820282019728792003956564819968"]),
                call(A, "gcd(uint256,uint256)", &["12", "18"]),
                call(A, "gcd(uint256,uint256)", &["0", "0"]),
                call(A, "gcd(uint256,uint256)", &["0", "7"]),
                call(A, "gcd(uint256,uint256)", &["1606938044258990275541962092341162602522202993782792835301376", "3802951800684688204490109616128"]),
                call(A, "saturatingAdd(uint256,uint256)", &["1", "2"]),
                call(A, "saturatingAdd(uint256,uint256)", &[MAX, "1"]),
                call(A, "saturatingSub(uint256,uint256)", &["5", "2"]),
                call(A, "saturatingSub(uint256,uint256)", &["2", "5"]),
                call(A, "saturatingMul(uint256,uint256)", &["0", MAX]),
                call(A, "saturatingMul(uint256,uint256)", &["340282366920938463463374607431768211456", "340282366920938463463374607431768211456"]),
                call(A, "saturatingMul(uint256,uint256)", &["3", "5"]),
                call(A, "lerp(uint256,uint256,uint256,uint256,uint256)", &["100", "200", "5", "0", "10"]),
                call(A, "lerp(uint256,uint256,uint256,uint256,uint256)", &["200", "100", "5", "0", "10"]),
                call(A, "lerp(uint256,uint256,uint256,uint256,uint256)", &["100", "200", "5", "10", "0"]),
                call(A, "lerp(uint256,uint256,uint256,uint256,uint256)", &["1", "2", "7", "7", "7"]),
                call(A, "lerp(uint256,uint256,uint256,uint256,uint256)", &["1", "2", "8", "7", "7"]),
                call(A, "lerpInt(int256,int256,int256,int256,int256)", &["-100", "200", "5", "0", "10"]),
                call(A, "lerpInt(int256,int256,int256,int256,int256)", &["200", "-100", "-5", "0", "-10"]),
                call(A, "lerpInt(int256,int256,int256,int256,int256)", &["1", "2", "-3", "-7", "5"]),
                send(A, "setLast(int256)", &["1000000000000000000"]),
                send(A, "setLast(int256)", &["-50000000000000000000"]),
                send(A, "setLast(int256)", &["135305999368893231589"]),
            ],
        ),
        suite(
            "layout",
            vec![deploy("layout", "layout", "", &[])],
            vec![
                send(A, "setLevel(uint256,uint8)", &["0", "11"]),
                send(A, "setLevel(uint256,uint8)", &["31", "22"]),
                send(A, "setLevel(uint256,uint8)", &["32", "33"]),
                send(A, "setLevel(uint256,uint8)", &["39", "255"]),
                send(A, "setLevel(uint256,uint8)", &["40", "1"]),
                call(A, "level(uint256)", &["31"]),
                call(A, "level(uint256)", &["32"]),
                send(A, "setFlag(uint256,bool)", &["4", "true"]),
                send(A, "setFlag(uint256,bool)", &["0", "true"]),
                call(A, "flag(uint256)", &["4"]),
                send(A, "setDelta(uint256,int16)", &["1", "-300"]),
                send(A, "setDelta(uint256,int16)", &["2", "7"]),
                call(A, "delta(uint256)", &["1"]),
                call(A, "delta(uint256)", &["0"]),
                send(A, "place(uint16,uint16)", &["65535", "3"]),
                call(A, "spot()", &[]),
                send(A, "setPair(uint32,address)", &["4000000000", B]),
                call(A, "pair()", &[]),
                send(A, "bump(uint64)", &["18000000000000000000"]),
                send(A, "bump(uint64)", &["5"]),
                call(A, "small()", &[]),
            ],
        ),
        suite(
            "records",
            vec![deploy("records", "records", "", &[])],
            vec![
                send(A, "place(uint256,uint256,uint32,int16)", &["1", "1000", "4000000000", "-300"]),
                send(B, "place(uint256,uint256,uint32,int16)", &["2", "57896044618658097711785492504343953926634992332820282019728792003956564819968", "5", "32767"]),
                call(A, "orderOf(uint256)", &["1"]),
                send(A, "bump(uint256,uint256)", &["1", "5"]),
                send(A, "bump(uint256,uint256)", &["9", "5"]),
                send(A, "bump(uint256,uint256)", &["2", "57896044618658097711785492504343953926634992332820282019728792003956564819968"]),
                send(A, "place(uint256,uint256,uint32,int16)", &["3", "1", "1", "-32768"]),
                send(A, "bump(uint256,uint256)", &["3", "1"]),
                send(A, "copy(uint256,uint256)", &["1", "4"]),
                send(A, "copy(uint256,uint256)", &["4", "4"]),
                call(A, "orderOf(uint256)", &["4"]),
                call(A, "statusOf(uint256)", &["1"]),
                call(A, "deltaOf(uint256)", &["1"]),
                send(A, "pairSet(uint256,uint128,uint128)", &["7", "340282366920938463463374607431768211455", "3"]),
                send(B, "pairSet(uint256,uint128,uint128)", &["7", "1", "170141183460469231731687303715884105728"]),
                send(A, "pairSet(uint256,uint128,uint128)", &["8", "2", "9"]),
                call(A, "pairOf(address,uint256)", &[A, "8"]),
                call(A, "pairOf(address,uint256)", &[B, "8"]),
                send(A, "headSet(uint128)", &["7"]),
                send(B, "headSet(uint128)", &["340282366920938463463374607431768211455"]),
                send(B, "headSet(uint128)", &["9"]),
                send(A, "headSwap()", &[]),
                call(A, "headPair()", &[]),
                call(A, "pairOf(address,uint256)", &[B, "0"]),
                call(A, "pairOf(address,uint256)", &[A, "0"]),
                call(A, "oddOf(uint128)", &["7"]),
                call(A, "oddOf(uint128)", &["8"]),
                send(A, "promote(uint256)", &["1"]),
                call(A, "topOrder()", &[]),
                send(B, "resetTop(uint256,int16)", &["77", "-5"]),
                call(A, "topOrder()", &[]),
                send(A, "resetTop(uint256,int16)", &["3", "32767"]),
                send(A, "promote(uint256)", &["9"]),
                call(A, "topOrder()", &[]),
            ],
        ),
        suite(
            "lists",
            vec![deploy("lists", "lists", "", &[])],
            vec![
                send(A, "save(uint256[])", &["[1,2,3]"]),
                call(A, "saved()", &[]),
                send(A, "push(uint256)", &["4"]),
                send(A, "save(uint256[])", &["[9]"]),
                call(A, "saved()", &[]),
                send(A, "save(uint256[])", &["[]"]),
                send(A, "setOwners(address[])", &["[0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266,0x70997970C51812dC3A010C7d01b50e0d17dc79C8]"]),
                call(A, "owners()", &[]),
                call(A, "ownerAt(uint256)", &["1"]),
                call(A, "ownerAt(uint256)", &["2"]),
                call(A, "first(uint256[])", &["[7,8]"]),
                call(A, "first(uint256[])", &["[]"]),
                call(A, "echo(bytes4[])", &["[0xdeadbeef,0x01020304]"]),
                call(A, "pair(uint256,uint256)", &["5", "6"]),
                send(A, "announce(uint256[],string)", &["[1,2]", LONG]),
                send(A, "tag(bytes4[])", &["[0xdeadbeef,0x01020304]"]),
                call(A, "same(uint256[],uint256[])", &["[1,2]", "[1,2]"]),
                call(A, "same(uint256[],uint256[])", &["[1,2]", "[1,3]"]),
                call(A, "encoded(uint256[],bytes4)", &["[1,2]", "0xcafebabe"]),
                send(A, "0x717a8a0c0000000000000000000000000000000000000000000000000000000000001000", &[]),
                send(A, "0x717a8a0c000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000001", &[]),
                send(A, "0xfa4d3698000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000010000000000000000000000000000000000000000", &[]),
            ],
        ),
        suite(
            "texts",
            vec![deploy("texts", "texts", "", &[])],
            vec![
                send(A, "save(bytes[])", &["[0x0102,0xcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd,0x]"]),
                call(A, "saved()", &[]),
                call(A, "savedAt(uint256)", &["1"]),
                call(A, "savedAt(uint256)", &["3"]),
                send(A, "push(bytes)", &["0xefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefef"]),
                send(A, "setAt(uint256,bytes)", &["1", "0x09"]),
                call(A, "joined()", &[]),
                send(A, "save(bytes[])", &["[0xababababababababababababababababababababababababababababababab]"]),
                call(A, "saved()", &[]),
                send(A, "save(bytes[])", &["[]"]),
                send(A, "setNames(string[])", &["[a string that is well past thirty one bytes long,hi,]"]),
                call(A, "names()", &[]),
                send(A, "setNames(string[])", &["[x]"]),
                send(A, "label(uint256,string)", &["7", LONG]),
                call(A, "labelOf(uint256)", &["7"]),
                send(A, "label(uint256,string)", &["7", "short"]),
                call(A, "labelOf(uint256)", &["7"]),
                call(A, "labelOf(uint256)", &["8"]),
                call(A, "first(bytes[])", &["[0x0102,0x030405]"]),
                call(A, "concatAll(bytes[])", &["[0x0102,0x030405,0xcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd]"]),
                call(A, "echo(string[])", &["[a string that is well past thirty one bytes long,ab,]"]),
                call(A, "pair(bytes,bytes)", &["0x0102", "0xcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd"]),
                call(A, "left(bytes,bytes)", &["0x", "0x010203"]),
                call(A, "same(bytes[],bytes[])", &["[0x0102,0x]", "[0x0102,0x]"]),
                call(A, "same(bytes[],bytes[])", &["[0x0102,0x]", "[0x0102,0x00]"]),
                call(A, "encoded(uint256,string[])", &["7", "[a string that is well past thirty one bytes long,hi]"]),
                call(A, "decoded(bytes)", &["0x0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000201020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"]),
                send(A, "0xc3ef1311000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000001000", &[]),
                send(A, "0xc3ef13110000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000040", &[]),
                call(A, "decoded(bytes)", &["0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000001000"]),
                call(A, "smallOf(bytes)", &["0x0000000000000000000000000000000000000000000000000000000000000007"]),
                call(A, "smallOf(bytes)", &["0x0000000000000000000000000000000000000000000000000000000000000100"]),
                call(A, "smallOf(bytes)", &["0x07"]),
                call(A, "textOf(bytes)", &["0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000026869000000000000000000000000000000000000000000000000000000000000"]),
                call(A, "textOf(bytes)", &["0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000028abababababababababababababababababababababababababababababababababababababababab000000000000000000000000000000000000000000000000"]),
                call(A, "textOf(bytes)", &["0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000003e8"]),
                call(A, "textOf(bytes)", &["0x0000000000000000000000000000000000000000000000000000000000001000"]),
                call(A, "addrMem(bytes)", &["0x0000000000000000000000000000000000000000000000000000000000000abc"]),
                call(A, "addrMem(bytes)", &["0x0000000000000000000000010000000000000000000000000000000000000000"]),
                call(A, "addrMem(bytes)", &["0x"]),
                call(A, "textMem(bytes)", &["0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000028abababababababababababababababababababababababababababababababababababababababab000000000000000000000000000000000000000000000000"]),
                call(A, "textMem(bytes)", &["0x0000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000036162630000000000000000000000000000000000000000000000000000000000"]),
                call(A, "textMem(bytes)", &["0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000021abababababababababababababababababababababababababababababababab"]),
                call(A, "namesMem(bytes)", &["0x0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000268690000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"]),
                call(A, "namesMem(bytes)", &["0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000040"]),
                call(A, "sameText(string,bytes)", &["hi", "0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000026869000000000000000000000000000000000000000000000000000000000000"]),
                call(A, "sameText(string,bytes)", &[LONG, "0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000306120737472696e6720746861742069732077656c6c207061737420746869727479206f6e65206279746573206c6f6e6700000000000000000000000000000000"]),
                call(A, "sameText(string,bytes)", &["ho", "0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000026869000000000000000000000000000000000000000000000000000000000000"]),
                call(A, "emptyText(bytes)", &["0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000"]),
                send(A, "keepText(uint256,bytes)", &["9", "0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000028abababababababababababababababababababababababababababababababababababababababab000000000000000000000000000000000000000000000000"]),
                send(A, "keepText(uint256,bytes)", &["9", "0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000026869000000000000000000000000000000000000000000000000000000000000"]),
                call(A, "labelOf(uint256)", &["9"]),
                call(A, "note()", &[]),
                call(A, "selectorOnly()", &[]),
            ],
        ),
        suite(
            "loops",
            vec![deploy("loops", "loops", "", &[])],
            vec![
                call(A, "sum(uint256[])", &["[1,2,3,4,5]"]),
                call(A, "sum(uint256[])", &["[]"]),
                send(A, "airdrop(address[],uint256)", &["[0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266,0x70997970C51812dC3A010C7d01b50e0d17dc79C8,0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266]", "7"]),
                call(A, "balanceOf(address)", &[A]),
                send(A, "join(address)", &[A]),
                send(A, "join(address)", &[B]),
                send(A, "join(address)", &["0x0000000000000000000000000000000000000003"]),
                send(A, "markAll()", &[]),
                call(A, "isOwner(address)", &[B]),
                call(A, "find(address)", &[B]),
                call(A, "find(address)", &["0x0000000000000000000000000000000000000009"]),
                call(A, "gcd(uint256,uint256)", &["1071", "462"]),
                call(A, "gcd(uint256,uint256)", &["7", "0"]),
                call(A, "hashChain(bytes32,uint256)", &["0x1111111111111111111111111111111111111111111111111111111111111111", "20"]),
                send(A, "payout(address[])", &["[0x70997970C51812dC3A010C7d01b50e0d17dc79C8,0x0000000000000000000000000000000000000003]"]).paying("1000000000000000000"),
                send(A, "payout(address[])", &["[]"]).paying("1"),
            ],
        ),
        suite(
            "names",
            vec![deploy("names", "names", "", &[])],
            vec![
                send(A, "setName(uint256,string)", &["1", "hello"]),
                call(A, "name(uint256)", &["1"]),
                send(A, "setName(uint256,string)", &["1", LONG]),
                call(A, "name(uint256)", &["1"]),
                send(A, "setName(uint256,string)", &["1", &LONG.repeat(3)]),
                send(A, "setName(uint256,string)", &["1", LONG]),
                call(A, "name(uint256)", &["1"]),
                send(A, "setName(uint256,string)", &["1", "hi"]),
                call(A, "name(uint256)", &["1"]),
                call(A, "name(uint256)", &["2"]),
                send(A, "setBlob(bytes32,bytes)", &["0x1111111111111111111111111111111111111111111111111111111111111111", "0xabababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababab"]),
                call(A, "blob(bytes32)", &["0x1111111111111111111111111111111111111111111111111111111111111111"]),
                send(A, "setBlob(bytes32,bytes)", &["0x1111111111111111111111111111111111111111111111111111111111111111", "0xcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd"]),
                send(A, "setBlob(bytes32,bytes)", &["0x1111111111111111111111111111111111111111111111111111111111111111", "0xefefefefef"]),
                call(A, "blob(bytes32)", &["0x1111111111111111111111111111111111111111111111111111111111111111"]),
                send(A, "setLabel(uint256,string)", &["3", LONG]),
                send(B, "setLabel(uint256,string)", &["3", "bee"]),
                call(A, "label(address,uint256)", &[A, "3"]),
                call(A, "label(address,uint256)", &[B, "3"]),
                send(A, "addNote(string)", &["short"]),
                send(A, "addNote(string)", &[LONG]),
                send(A, "addNote(string)", &["a string that is well past thirty one bytes longa string that is well past thirty one bytes long"]),
                call(A, "note(uint256)", &["1"]),
                call(A, "noteCopy(uint256)", &["2"]),
                call(A, "notesLength()", &[]),
                send(A, "setNote(uint256,string)", &["2", "x"]),
                send(A, "setNote(uint256,string)", &["0", &LONG.repeat(3)]),
                call(A, "note(uint256)", &["0"]),
                call(A, "note(uint256)", &["2"]),
                send(A, "setNote(uint256,string)", &["5", "y"]),
                call(A, "note(uint256)", &["9"]),
                send(A, "setNotes(string,string)", &["b", LONG]),
                call(A, "noteCopy(uint256)", &["1"]),
                call(A, "notesLength()", &[]),
            ],
        ),
        suite(
            "base64",
            vec![deploy("base64", "base64", "", &[])],
            vec![
                call(A, "encode(bytes)", &["0x"]),
                call(A, "encode(bytes)", &["0x66"]),
                call(A, "encode(bytes)", &["0xabababababababababababababababababababab"]),
                call(A, "encode(bytes)", &["0xabababababababababababababababababababababababababababababababab"]),
                call(A, "encode(bytes)", &[&["0x", &"5a".repeat(100)].concat()]),
                call(A, "encode(bytes)", &[&["0x", &"c3".repeat(1000)].concat()]),
                call(A, "encodeWith(bytes,bool,bool)", &["0xfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfb", "true", "true"]),
                call(A, "encodeWith(bytes,bool,bool)", &["0xfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfbfb", "false", "true"]),
                call(A, "decode(string)", &["Zm9vYmFy"]),
                call(A, "decode(string)", &["Zm9vYg=="]),
                call(A, "decode(string)", &["Pz8_-,A"]),
                call(A, "decode(string)", &["AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8gISIjJCUmJygpKissLS4vMDEyMzQ1Njc4OTo7PD0+P0BBQkNERUZHSElKS0xNTk9QUVJTVFVWV1hZWltcXV5fYGFiY2RlZmdoaWprbG1ub3BxcnN0dXZ3eHl6e3x9fn+AgYKDhIWGh4iJiouMjY6PkJGSk5SVlpeYmZqbnJ2en6ChoqOkpaanqKmqq6ytrq+wsbKztLW2t7i5uru8vb6/wMHCw8TFxsfIycrLzM3Oz9DR0tPU1dbX2Nna29zd3t/g4eLj5OXm5+jp6uvs7e7v8PHy8/T19vf4+fr7/P3+/wABAgMEBQYHCAkKCwwNDg8QERITFBUWFxgZGhscHR4fICEiIyQlJicoKSorLC0uLzAxMjM0NTY3ODk6Ozw9Pj9AQUJDREVGR0hJSktMTU5PUFFSU1RVVldYWVpbXF1eX2BhYmNkZWZnaGlqa2xtbm9wcXJzdHV2d3h5ent8fX5/gIGCg4SFhoeIiYqLjI2Oj5CRkpOUlZaXmJmam5ydnp+goaKjpKWmp6ipqqusra6vsLGys7S1tre4ubq7vL2+v8DBwsPExcbHyMnKy8zNzs/Q0dLT1NXW19jZ2tvc3d7f4OHi4+Tl5ufo6err7O3u7/Dx8vP09fb3+Pn6+/z9/v8AAQIDBAUGBwgJCgsMDQ4PEBESExQVFhcYGRobHB0eHyAhIiMkJSYnKCkqKywtLi8wMTIzNDU2Nzg5Ojs8PT4/QEFCQ0RFRkdISUpLTE1OT1BRUlNUVVZXWFlaW1xdXl9gYWJjZGVmZ2hpamtsbW5vcHFyc3R1dnd4eXp7fH1+f4CBgoOEhYaHiImKi4yNjo+QkZKTlJWWl5iZmpucnZ6foKGio6SlpqeoqaqrrK2ur7CxsrO0tba3uLm6u7y9vr/AwcLDxMXGx8jJysvMzc7P0NHS09TV1tfY2drb3N3e3+Dh4uPk5ebn6Onq6+zt7u/w8fLz9PX29/j5+vv8/f7/AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8gISIjJCUmJygpKissLS4vMDEyMzQ1Njc4OTo7PD0+P0BBQkNERUZHSElKS0xNTk9QUVJTVFVWV1hZWltcXV5fYGFiY2RlZmdoaWprbG1ub3BxcnN0dXZ3eHl6e3x9fn+AgYKDhIWGh4iJiouMjY6PkJGSk5SVlpeYmZqbnJ2en6ChoqOkpaanqKmqq6ytrq+wsbKztLW2t7i5uru8vb6/wMHCw8TFxsfIycrLzM3Oz9DR0tPU1dbX2Nna29zd3t/g4eLj5OXm5+jp6uvs7e7v8PHy8/T19vf4+fr7/P3+/w=="]),
            ],
        ),
        suite(
            "overloads",
            vec![deploy("overloads", "overloads", "", &[])],
            vec![
                send(A, "deposit(uint256)", &["10000"]),
                send(B, "deposit(uint256,uint256)", &["10000", "100"]),
                send(A, "deposit(uint256,uint256)", &["10000", "10001"]),
                send(A, "stake(uint256)", &["500"]),
                send(A, "transfer(address,uint256)", &[B, "70"]),
                send(B, "transfer(address,uint256)", &[A, "99999"]),
                send(A, "transferStaked(address,uint256)", &[B, "200"]),
                send(B, "transferStaked(address,uint256)", &[A, "201"]),
                call(A, "balanceOf(address)", &[A]),
                call(A, "balanceOf(address)", &[B]),
                call(A, "stakedOf(address)", &[B]),
                call(A, "total()", &[]),
            ],
        ),
        suite(
            "tally",
            vec![deploy("tally", "tally", "", &[])],
            vec![
                send(A, "vote(bytes32,uint256)", &["0x0101010101010101010101010101010101010101010101010101010101010101", "3"]),
                send(B, "vote(bytes32,uint256)", &["0x0101010101010101010101010101010101010101010101010101010101010101", "5"]),
                send(A, "vote(bytes32,uint256)", &["0x0202020202020202020202020202020202020202020202020202020202020202", "7"]),
                send(B, "vote(bytes32,uint256)", &["0x0202020202020202020202020202020202020202020202020202020202020202", "0"]),
                send(B, "vote(bytes32,uint256)", &["0x0303030303030303030303030303030303030303030303030303030303030303", MAX]),
                call(A, "votesOf(address)", &[A]),
                call(A, "votesOf(address)", &[B]),
                call(A, "votesFor(bytes32)", &["0x0101010101010101010101010101010101010101010101010101010101010101"]),
                call(A, "votesFor(bytes32)", &["0x0303030303030303030303030303030303030303030303030303030303030303"]),
                call(A, "totalVotes()", &[]),
            ],
        ),
        suite(
            "collections",
            vec![deploy("collections", "collections", "", &[])],
            vec![
                send(A, "enqueue(address)", &[A]),
                send(A, "enqueue(address)", &[B]),
                send(B, "enqueue(address)", &[A]),
                call(A, "queued()", &[]),
                send(A, "dequeue()", &[]),
                send(B, "dequeue()", &[]),
                call(A, "queued()", &[]),
                send(A, "dequeue()", &[]),
                send(A, "dequeue()", &[]),
                send(A, "set(address,uint256)", &[A, "5"]),
                send(A, "set(address,uint256)", &[B, "7"]),
                send(B, "set(address,uint256)", &[ZERO, "9"]),
                send(A, "set(address,uint256)", &[A, "6"]),
                call(A, "length()", &[]),
                call(A, "at(uint256)", &["1"]),
                call(A, "get(address)", &[B]),
                send(A, "remove(address)", &[A]),
                send(A, "remove(address)", &[A]),
                call(A, "get(address)", &[A]),
                call(A, "at(uint256)", &["0"]),
                send(B, "remove(address)", &[ZERO]),
                send(B, "remove(address)", &[B]),
                call(A, "length()", &[]),
                send(A, "set(address,uint256)", &[A, "8"]),
                call(A, "get(address)", &[A]),
                call(A, "at(uint256)", &["0"]),
            ],
        ),
        suite(
            "registry",
            vec![deploy("registry", "registry", "string", &["registry"])],
            vec![
                send(A, "rename(string)", &["hello"]),
                call(A, "name()", &[]),
                send(A, "rename(string)", &[LONG]),
                call(A, "name()", &[]),
                send(A, "setBlob(bytes)", &["0xabababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababab"]),
                call(A, "blob()", &[]),
                call(A, "digest()", &[]),
                send(A, "setTag(bytes4,uint8)", &["0xdeadbeef", "7"]),
                call(A, "tag()", &[]),
                call(A, "level()", &[]),
                send(B, "setTag(bytes4,uint8)", &["0x01020304", "255"]),
                call(A, "tag()", &[]),
                send(A, "0x66605ba40000000000000000000000000000000000000000000000000000000000001000", &[]),
                send(A, "0x66605ba40000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000004068656c6c6f000000000000000000000000000000000000000000000000000000", &[]),
                send(A, "0x66605ba40000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000568656c6c6f000000000000000000000000000000000000000000000000000000", &[]),
                send(A, "rename(string)", &[&LONG.repeat(3)]),
                send(A, "rename(string)", &[LONG]),
                call(A, "name()", &[]),
                send(A, "rename(string)", &["hi"]),
                call(A, "name()", &[]),
                send(A, "setBlob(bytes)", &["0xcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd"]),
                send(A, "setBlob(bytes)", &["0xefefefefef"]),
                call(A, "blob()", &[]),
                send(A, "setBoth(string,bytes)", &["", "0x0102"]),
                call(A, "name()", &[]),
                call(A, "blob()", &[]),
                send(A, "setBoth(string,bytes)", &["hi", "0x"]),
                send(A, "setBoth(string,bytes)", &["xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx", "0xabababababababababababababababababababababababababababababababab"]),
                send(A, "setBoth(string,bytes)", &[LONG, "0xcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd"]),
                call(A, "name()", &[]),
                call(A, "blob()", &[]),
                send(A, "0x4ca510440000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000026869ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000001abffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", &[]),
                call(A, "name()", &[]),
                call(A, "blob()", &[]),
            ],
        ),
        suite(
            "relay",
            vec![deploy("texts", "texts", "", &[]), deploy("relay", "relay", "", &[])],
            vec![
                send(A, "ask(address,string[])", &["$texts", "[a string that is well past thirty one bytes long,hi,]"]).on("relay"),
                call(A, "names()", &[]).on("relay"),
                send(A, "send(address,string[])", &["$texts", "[x,a string that is well past thirty one bytes long]"]).on("relay"),
                call(A, "kept()", &[]).on("relay"),
                send(A, "unpack(address,bytes)", &["$texts", &["0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000008600000000000000000000000000000000000000000000000000000000000000800", &"ab".repeat(2048), "0000000000000000000000000000000000000000000000000000000000000800", &"cd".repeat(2048)].concat()]).on("relay"),
                send(A, "unpack(address,bytes)", &["$texts", &["0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000040600000000000000000000000000000000000000000000000000000000000004000", &"ab".repeat(16384), "0000000000000000000000000000000000000000000000000000000000004000", &"cd".repeat(16384)].concat()]).on("relay"),
                call(A, "count()", &[]).on("relay"),
                send(A, "unpack(address,bytes)", &["$texts", "0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000001000"]).on("relay"),
            ],
        ),
        suite(
            "dial",
            vec![deploy("book", "book", "", &[]), deploy("dialer", "dialer", "", &[])],
            vec![
                send(A, "0x0cee60200000000000000000000000005fbdb2315678afecb367f032d93f642f64180aa300000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000001400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000566697273740000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000306120737472696e6720746861742069732077656c6c207061737420746869727479206f6e65206279746573206c6f6e670000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000005", &[]).on("dialer"),
                call(A, "ids()", &[]).on("dialer"),
                call(A, "note(address,uint256)", &["$book", "2"]).on("dialer"),
                call(A, "note(address,uint256)", &["$book", "9"]).on("dialer"),
                send(A, "0x0cee60200000000000000000000000005fbdb2315678afecb367f032d93f642f64180aa300000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000001200000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000017800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000179000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000", &[]).on("dialer"),
                call(A, "refused()", &[]).on("dialer"),
                call(A, "ids()", &[]).on("dialer"),
                call(A, "0x0cee602000000000000000000000000070997970c51812dc3a010c7d01b50e0d17dc79c80000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000005000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000017a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001", &[]).on("dialer"),
            ],
        ),
        suite(
            "profile",
            vec![deploy("profile", "profile", "string,bytes", &["", "0x0102"]), deploy("short", "profile", "string,bytes", &["alice", "0x"]), deploy("long", "profile", "string,bytes", &[LONG, "0xabababababababababababababababababababababababababababababababababababababababab"])],
            vec![
                call(A, "name()", &[]),
                call(A, "avatar()", &[]),
                call(A, "name()", &[]).on("short"),
                call(A, "avatar()", &[]).on("short"),
                call(A, "name()", &[]).on("long"),
                call(A, "avatar()", &[]).on("long"),
                send(A, "setBio(string)", &[""]),
                send(A, "setBio(string)", &["hi"]),
                send(A, "setBio(string)", &["xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"]),
                send(A, "setBio(string)", &["xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"]),
                send(A, "setBio(string)", &[LONG]),
                call(A, "bio()", &[]),
                send(A, "0xfb7e06d8000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000026869ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", &[]),
                call(A, "bio()", &[]),
            ],
        ),
        suite(
            "erc20",
            vec![deploy("token", "erc20", "address", &[A])],
            vec![
                call(A, "name()", &[]),
                call(A, "symbol()", &[]),
                call(A, "decimals()", &[]),
                call(A, "owner()", &[]),
                send(A, "mint(address,uint256)", &[A, "1000000000000000000000"]),
                send(B, "mint(address,uint256)", &[B, "5"]),
                send(A, "mint(address,uint256)", &[ZERO, "1"]),
                send(A, "transfer(address,uint256)", &[B, "100000000000000000000"]),
                call(A, "transfer(address,uint256)", &[B, "1"]),
                send(A, "transfer(address,uint256)", &[ZERO, "1"]),
                send(B, "transfer(address,uint256)", &[A, "1000000000000000000000000000000"]),
                send(A, "approve(address,uint256)", &[B, "500000000000000000000"]),
                send(A, "approve(address,uint256)", &[ZERO, "1"]),
                call(A, "allowance(address,address)", &[A, B]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "200000000000000000000"]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "400000000000000000000"]),
                send(B, "transferFrom(address,address,uint256)", &[A, ZERO, "1"]),
                send(A, "approve(address,uint256)", &[B, MAX]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "1"]),
                call(A, "allowance(address,address)", &[A, B]),
                send(B, "burn(uint256)", &["10000000000000000000"]),
                send(B, "burn(uint256)", &["1000000000000000000000000000000"]),
                send(B, "burnFrom(address,uint256)", &[A, "5000000000000000000"]),
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
                send(A, "0xa9059cbb00000000000000000000000070997970c51812dc3a010c7d01b50e0d17dc79c8", &[]),
            ],
        ),
        suite(
            "erc721",
            vec![deploy("nft", "erc721", "address", &[A]), deploy("receiver", "receiver", "", &[])],
            vec![
                call(A, "name()", &[]),
                call(A, "symbol()", &[]),
                call(A, "owner()", &[]),
                call(A, "supportsInterface(bytes4)", &["0x80ac58cd"]),
                call(A, "supportsInterface(bytes4)", &["0x5b5e139f"]),
                call(A, "supportsInterface(bytes4)", &["0x01ffc9a7"]),
                call(A, "supportsInterface(bytes4)", &["0xffffffff"]),
                send(A, "safeMint(address,uint256)", &[A, "1"]),
                send(A, "safeMint(address,uint256)", &[B, "2"]),
                send(B, "safeMint(address,uint256)", &[B, "9"]),
                send(A, "safeMint(address,uint256)", &[ZERO, "3"]),
                send(A, "safeMint(address,uint256)", &[B, "1"]),
                send(A, "safeMint(address,uint256)", &["$receiver", "3"]),
                send(A, "safeMint(address,uint256)", &[A, "4"]),
                send(A, "safeMint(address,uint256)", &[A, "5"]),
                send(A, "safeMint(address,uint256)", &[A, "6"]),
                call(A, "balanceOf(address)", &[A]),
                call(A, "balanceOf(address)", &[ZERO]),
                call(A, "ownerOf(uint256)", &["1"]),
                call(A, "ownerOf(uint256)", &["99"]),
                call(A, "tokenURI(uint256)", &["1"]),
                call(A, "tokenURI(uint256)", &["99"]),
                send(A, "approve(address,uint256)", &[B, "1"]),
                call(A, "getApproved(uint256)", &["1"]),
                call(A, "getApproved(uint256)", &["99"]),
                send(B, "approve(address,uint256)", &[B, "4"]),
                send(A, "approve(address,uint256)", &[B, "99"]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "1"]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "1"]),
                send(B, "transferFrom(address,address,uint256)", &[B, ZERO, "1"]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "4"]),
                send(A, "transferFrom(address,address,uint256)", &[A, B, "99"]),
                send(B, "setApprovalForAll(address,bool)", &[A, "true"]),
                send(B, "setApprovalForAll(address,bool)", &[ZERO, "true"]),
                call(A, "isApprovedForAll(address,address)", &[B, A]),
                send(A, "transferFrom(address,address,uint256)", &[B, A, "2"]),
                send(A, "approve(address,uint256)", &[A, "1"]),
                send(A, "safeTransferFrom(address,address,uint256)", &[A, B, "2"]),
                send(A, "safeTransferFrom(address,address,uint256,bytes)", &[A, "$receiver", "4", "0xabababababababababababababababababababababababababababababababababababababababab"]),
                send(A, "safeTransferFrom(address,address,uint256,bytes)", &[A, "$receiver", "5", "0x1234"]),
                send(A, "setMode(uint256)", &["1"]).on("receiver"),
                send(A, "safeTransferFrom(address,address,uint256)", &[A, "$receiver", "6"]),
                send(A, "setMode(uint256)", &["2"]).on("receiver"),
                call(A, "safeTransferFrom(address,address,uint256)", &[A, "$receiver", "6"]),
                send(A, "safeTransferFrom(address,address,uint256)", &[A, "$receiver", "6"]),
                send(A, "setMode(uint256)", &["0"]).on("receiver"),
                call(A, "safeTransferFrom(address,address,uint256)", &[A, "$nft", "6"]),
                send(A, "safeTransferFrom(address,address,uint256)", &[A, "$nft", "6"]),
                send(A, "burn(uint256)", &["1"]),
                send(B, "burn(uint256)", &["1"]),
                send(B, "burn(uint256)", &["1"]),
                call(A, "getApproved(uint256)", &["1"]),
                send(B, "pause()", &[]),
                send(A, "pause()", &[]),
                call(A, "paused()", &[]),
                send(A, "transferFrom(address,address,uint256)", &[A, B, "6"]),
                send(A, "safeMint(address,uint256)", &[A, "7"]),
                send(A, "approve(address,uint256)", &[B, "6"]),
                send(A, "unpause()", &[]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "6"]),
                call(A, "balanceOf(address)", &[A]),
                call(A, "balanceOf(address)", &[B]),
                call(A, "balanceOf(address)", &["$receiver"]),
                send(A, "transferOwnership(address)", &[B]),
                send(B, "renounceOwnership()", &[]),
                call(A, "owner()", &[]),
            ],
        ),
        suite(
            "erc1155",
            vec![deploy("mt", "erc1155", "address", &[A]), deploy("r1155", "receiver1155", "", &[]), deploy("plain", "receiver", "", &[])],
            vec![
                call(A, "uri(uint256)", &["1"]),
                call(A, "owner()", &[]),
                call(A, "supportsInterface(bytes4)", &["0xd9b67a26"]),
                call(A, "supportsInterface(bytes4)", &["0x0e89341c"]),
                call(A, "supportsInterface(bytes4)", &["0x01ffc9a7"]),
                call(A, "supportsInterface(bytes4)", &["0x80ac58cd"]),
                call(A, "supportsInterface(bytes4)", &["0xffffffff"]),
                send(A, "mint(address,uint256,uint256,bytes)", &[A, "1", "100", "0x"]),
                send(A, "mint(address,uint256,uint256,bytes)", &[B, "2", "50", "0x1234"]),
                send(B, "mint(address,uint256,uint256,bytes)", &[B, "2", "1", "0x"]),
                send(A, "mint(address,uint256,uint256,bytes)", &[ZERO, "1", "1", "0x"]),
                send(A, "mint(address,uint256,uint256,bytes)", &["$r1155", "3", "10", &["0x", &"ab".repeat(100)].concat()]),
                send(A, "mint(address,uint256,uint256,bytes)", &["$plain", "3", "1", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &[A, "[1,2,3]", "[10,20,30]", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &["$r1155", "[4,5,4]", "[1,2,3]", &["0x", &"ab".repeat(100)].concat()]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &["$r1155", "[7]", "[1]", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &[A, "[]", "[]", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &[A, "[1,2]", "[1]", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &[ZERO, "[1]", "[1]", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &["$plain", "[1,2]", "[1,1]", "0x"]),
                send(A, "setMode(uint256)", &["1"]).on("r1155"),
                send(A, "mint(address,uint256,uint256,bytes)", &["$r1155", "3", "1", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &["$r1155", "[3,4]", "[1,1]", "0x"]),
                send(A, "setMode(uint256)", &["2"]).on("r1155"),
                call(A, "mint(address,uint256,uint256,bytes)", &["$r1155", "3", "1", "0x"]),
                call(A, "mintBatch(address,uint256[],uint256[],bytes)", &["$r1155", "[3,4]", "[1,1]", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &["$r1155", "[3,4]", "[1,1]", "0x"]),
                send(A, "setMode(uint256)", &["3"]).on("r1155"),
                call(A, "mint(address,uint256,uint256,bytes)", &["$r1155", "3", "1", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &["$r1155", "[3,4]", "[1,1]", "0x"]),
                send(A, "setMode(uint256)", &["0"]).on("r1155"),
                call(A, "balanceOf(address,uint256)", &[A, "1"]),
                call(A, "balanceOf(address,uint256)", &["$r1155", "4"]),
                call(A, "balanceOfBatch(address[],uint256[])", &["[0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266,0x70997970C51812dC3A010C7d01b50e0d17dc79C8,0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266,0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266]", "[1,2,3,99]"]),
                call(A, "balanceOfBatch(address[],uint256[])", &["[0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266,0x70997970C51812dC3A010C7d01b50e0d17dc79C8]", "[1]"]),
                call(A, "balanceOfBatch(address[],uint256[])", &["[]", "[]"]),
                send(A, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, B, "1", "5", "0x"]),
                send(B, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, B, "1", "5", "0x"]),
                send(A, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, B, "1", "1000", "0x"]),
                send(A, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, ZERO, "1", "1", "0x"]),
                send(A, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[ZERO, B, "1", "1", "0x"]),
                send(A, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, "$r1155", "1", "5", &["0x", &"ab".repeat(100)].concat()]),
                send(A, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, "$plain", "1", "5", "0x"]),
                send(A, "setApprovalForAll(address,bool)", &[B, "true"]),
                send(A, "setApprovalForAll(address,bool)", &[ZERO, "true"]),
                call(A, "isApprovedForAll(address,address)", &[A, B]),
                send(B, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, B, "1", "5", "0x"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, B, "[1,2,3]", "[1,2,3]", "0x"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, B, "[1,1,2]", "[1,2,3]", "0x1234"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, B, "[1,2]", "[1]", "0x"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, B, "[1,2]", "[1,1000]", "0x"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, B, "[3,3]", "[20,20]", "0x"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, ZERO, "[1]", "[1]", "0x"]),
                send(B, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[B, A, "[2]", "[1]", "0x"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[B, A, "[2]", "[1]", "0x"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, "$r1155", "[1,3,1]", "[1,1,1]", &["0x", &"ab".repeat(100)].concat()]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, "$plain", "[1,3]", "[1,1]", "0x"]),
                send(A, "burn(address,uint256,uint256)", &[A, "1", "1"]),
                send(B, "burn(address,uint256,uint256)", &[A, "1", "1"]),
                send(A, "setApprovalForAll(address,bool)", &[B, "false"]),
                send(B, "burn(address,uint256,uint256)", &[A, "1", "1"]),
                send(A, "burn(address,uint256,uint256)", &[A, "1", "1000"]),
                send(A, "burn(address,uint256,uint256)", &[ZERO, "1", "1"]),
                send(A, "burnBatch(address,uint256[],uint256[])", &[A, "[1,2,3]", "[1,1,1]"]),
                send(A, "burnBatch(address,uint256[],uint256[])", &[A, "[1,1]", "[1,1]"]),
                send(A, "burnBatch(address,uint256[],uint256[])", &[A, "[1,2]", "[1]"]),
                send(A, "burnBatch(address,uint256[],uint256[])", &[A, "[1,2]", "[1,1000]"]),
                send(B, "burnBatch(address,uint256[],uint256[])", &[A, "[1]", "[1]"]),
                call(A, "totalSupply(uint256)", &["1"]),
                call(A, "totalSupply(uint256)", &["4"]),
                call(A, "totalSupply()", &[]),
                call(A, "exists(uint256)", &["1"]),
                call(A, "exists(uint256)", &["99"]),
                send(A, "mint(address,uint256,uint256,bytes)", &[A, "9", MAX, "0x"]),
                send(B, "setURI(string)", &["ipfs://x/{id}"]),
                send(A, "setURI(string)", &["ipfs://x/{id}"]),
                call(A, "uri(uint256)", &["1"]),
                send(A, "setURI(string)", &["a string that is well past thirty one bytes long/{id}.json"]),
                call(A, "uri(uint256)", &["7"]),
                send(B, "pause()", &[]),
                send(A, "pause()", &[]),
                send(A, "pause()", &[]),
                call(A, "paused()", &[]),
                send(A, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, B, "1", "1", "0x"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, B, "[1]", "[1]", "0x"]),
                send(A, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, ZERO, "1", "1", "0x"]),
                send(A, "mint(address,uint256,uint256,bytes)", &[A, "1", "1", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &[A, "[1]", "[1]", "0x"]),
                send(A, "burn(address,uint256,uint256)", &[A, "1", "1"]),
                send(A, "burnBatch(address,uint256[],uint256[])", &[A, "[1]", "[1]"]),
                send(A, "setApprovalForAll(address,bool)", &[B, "true"]),
                send(A, "unpause()", &[]),
                send(A, "unpause()", &[]),
                send(B, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, B, "1", "1", "0x"]),
                send(A, "transferOwnership(address)", &[ZERO]),
                send(A, "transferOwnership(address)", &[B]),
                send(A, "mint(address,uint256,uint256,bytes)", &[A, "1", "1", "0x"]),
                send(B, "mintBatch(address,uint256[],uint256[],bytes)", &[A, "[1,8]", "[1,1]", "0x"]),
                send(B, "renounceOwnership()", &[]),
                call(A, "owner()", &[]),
                call(A, "balanceOfBatch(address[],uint256[])", &["[0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266,0x70997970C51812dC3A010C7d01b50e0d17dc79C8,0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266,0x70997970C51812dC3A010C7d01b50e0d17dc79C8]", "[1,1,8,8]"]),
                call(A, "balanceOf(address,uint256)", &["$r1155", "1"]),
                call(A, "totalSupply()", &[]),
                send(A, "0x4e1273f4000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000001", &[]),
            ],
        ),
        suite(
            "erc6909",
            vec![deploy("mt", "erc6909", "address", &[A])],
            vec![
                call(A, "owner()", &[]),
                call(A, "contractURI()", &[]),
                call(A, "supportsInterface(bytes4)", &["0x0f632fb3"]),
                call(A, "supportsInterface(bytes4)", &["0x01ffc9a7"]),
                call(A, "supportsInterface(bytes4)", &["0xbd85b039"]),
                call(A, "supportsInterface(bytes4)", &["0x71abc795"]),
                call(A, "supportsInterface(bytes4)", &["0x20d88258"]),
                call(A, "supportsInterface(bytes4)", &["0xd9b67a26"]),
                call(A, "supportsInterface(bytes4)", &["0xffffffff"]),
                send(A, "mint(address,uint256,uint256)", &[A, "1", "100"]),
                send(A, "mint(address,uint256,uint256)", &[A, "2", "50"]),
                send(B, "mint(address,uint256,uint256)", &[B, "1", "1"]),
                send(A, "mint(address,uint256,uint256)", &[ZERO, "1", "1"]),
                send(A, "mint(address,uint256,uint256)", &[B, "3", MAX]),
                send(A, "mint(address,uint256,uint256)", &[B, "3", "1"]),
                send(A, "transfer(address,uint256,uint256)", &[B, "1", "10"]),
                send(A, "transfer(address,uint256,uint256)", &[B, "1", "0"]),
                send(A, "transfer(address,uint256,uint256)", &[ZERO, "1", "1"]),
                send(A, "transfer(address,uint256,uint256)", &[B, "1", "1000"]),
                send(A, "transfer(address,uint256,uint256)", &[A, "1", "5"]),
                send(B, "transferFrom(address,address,uint256,uint256)", &[A, "0x000000000000000000000000000000000000c0de", "1", "1"]),
                send(A, "approve(address,uint256,uint256)", &[B, "1", "30"]),
                send(A, "approve(address,uint256,uint256)", &[ZERO, "1", "30"]),
                call(A, "allowance(address,address,uint256)", &[A, B, "1"]),
                send(B, "transferFrom(address,address,uint256,uint256)", &[A, "0x000000000000000000000000000000000000c0de", "2", "1"]),
                send(B, "transferFrom(address,address,uint256,uint256)", &[A, "0x000000000000000000000000000000000000c0de", "1", "20"]),
                send(B, "transferFrom(address,address,uint256,uint256)", &[A, "0x000000000000000000000000000000000000c0de", "1", "11"]),
                send(B, "transferFrom(address,address,uint256,uint256)", &[A, ZERO, "1", "11"]),
                send(B, "transferFrom(address,address,uint256,uint256)", &[A, ZERO, "1", "1"]),
                call(A, "allowance(address,address,uint256)", &[A, B, "1"]),
                send(A, "transferFrom(address,address,uint256,uint256)", &[A, "0x000000000000000000000000000000000000c0de", "2", "5"]),
                send(A, "approve(address,uint256,uint256)", &[B, "2", MAX]),
                send(B, "transferFrom(address,address,uint256,uint256)", &[A, "0x000000000000000000000000000000000000c0de", "2", "5"]),
                call(A, "allowance(address,address,uint256)", &[A, B, "2"]),
                send(A, "setOperator(address,bool)", &[B, "true"]),
                send(A, "setOperator(address,bool)", &[ZERO, "true"]),
                call(A, "isOperator(address,address)", &[A, B]),
                send(B, "transferFrom(address,address,uint256,uint256)", &[A, B, "1", "50"]),
                send(B, "transferFrom(address,address,uint256,uint256)", &[A, B, "1", "1000"]),
                call(A, "allowance(address,address,uint256)", &[A, B, "1"]),
                send(A, "setOperator(address,bool)", &[B, "false"]),
                send(B, "transferFrom(address,address,uint256,uint256)", &[A, B, "1", "20"]),
                send(B, "burn(address,uint256,uint256)", &[B, "1", "10"]),
                send(B, "burn(address,uint256,uint256)", &[A, "1", "5"]),
                send(B, "burn(address,uint256,uint256)", &[A, "2", "5"]),
                send(A, "burn(address,uint256,uint256)", &[A, "1", "1000"]),
                send(A, "burn(address,uint256,uint256)", &[ZERO, "1", "0"]),
                send(A, "setOperator(address,bool)", &[B, "true"]),
                send(B, "burn(address,uint256,uint256)", &[A, "2", "10"]),
                call(A, "totalSupply(uint256)", &["1"]),
                call(A, "totalSupply(uint256)", &["2"]),
                call(A, "totalSupply(uint256)", &["3"]),
                call(A, "totalSupply(uint256)", &["9"]),
                call(A, "balanceOf(address,uint256)", &[A, "1"]),
                call(A, "balanceOf(address,uint256)", &[A, "2"]),
                call(A, "balanceOf(address,uint256)", &[B, "1"]),
                call(A, "balanceOf(address,uint256)", &[B, "2"]),
                call(A, "balanceOf(address,uint256)", &["0x000000000000000000000000000000000000c0de", "1"]),
                call(A, "balanceOf(address,uint256)", &["0x000000000000000000000000000000000000c0de", "2"]),
                send(B, "describe(uint256,string,string,uint8,string)", &["1", "Claim", "CLM", "6", "ipfs://claim/1"]),
                send(A, "describe(uint256,string,string,uint8,string)", &["1", "Claim", "CLM", "6", "ipfs://claim/1"]),
                send(A, "describe(uint256,string,string,uint8,string)", &["2", LONG, "", "18", LONG]),
                call(A, "name(uint256)", &["1"]),
                call(A, "name(uint256)", &["2"]),
                call(A, "name(uint256)", &["3"]),
                call(A, "symbol(uint256)", &["1"]),
                call(A, "symbol(uint256)", &["2"]),
                call(A, "symbol(uint256)", &["3"]),
                call(A, "decimals(uint256)", &["1"]),
                call(A, "decimals(uint256)", &["2"]),
                call(A, "decimals(uint256)", &["3"]),
                call(A, "tokenURI(uint256)", &["1"]),
                call(A, "tokenURI(uint256)", &["2"]),
                call(A, "tokenURI(uint256)", &["3"]),
            ],
        ),
        suite(
            "erc721_full",
            vec![deploy("nft", "erc721_full", "address", &[A]), deploy("receiver", "receiver", "", &[])],
            vec![
                call(A, "name()", &[]),
                call(A, "symbol()", &[]),
                call(A, "owner()", &[]),
                call(A, "supportsInterface(bytes4)", &["0x80ac58cd"]),
                call(A, "supportsInterface(bytes4)", &["0x5b5e139f"]),
                call(A, "supportsInterface(bytes4)", &["0x780e9d63"]),
                call(A, "supportsInterface(bytes4)", &["0x49064906"]),
                call(A, "supportsInterface(bytes4)", &["0x2a55205a"]),
                call(A, "supportsInterface(bytes4)", &["0x01ffc9a7"]),
                call(A, "supportsInterface(bytes4)", &["0xffffffff"]),
                call(A, "supportsInterface(bytes4)", &["0x00000000"]),
                call(A, "totalSupply()", &[]),
                call(A, "tokenByIndex(uint256)", &["0"]),
                call(A, "royaltyInfo(uint256,uint256)", &["0", "1000000000000000000"]),
                call(A, "safeMint(address,string)", &[A, "a.json"]),
                send(A, "safeMint(address,string)", &[A, "a.json"]),
                send(A, "safeMint(address,string)", &[B, ""]),
                send(B, "safeMint(address,string)", &[B, "b.json"]),
                send(A, "safeMint(address,string)", &[ZERO, "z.json"]),
                send(A, "safeMint(address,string)", &["$receiver", LONG]),
                send(A, "safeMint(address,string)", &[A, "d.json"]),
                send(A, "safeMint(address,string)", &[A, "e.json"]),
                send(A, "safeMint(address,string)", &[B, "f.json"]),
                call(A, "safeMint(address,string)", &[B, "g.json"]),
                call(A, "totalSupply()", &[]),
                call(A, "tokenByIndex(uint256)", &["0"]),
                call(A, "tokenByIndex(uint256)", &["1"]),
                call(A, "tokenByIndex(uint256)", &["2"]),
                call(A, "tokenByIndex(uint256)", &["3"]),
                call(A, "tokenByIndex(uint256)", &["4"]),
                call(A, "tokenByIndex(uint256)", &["5"]),
                call(A, "tokenByIndex(uint256)", &["6"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "0"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "1"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "2"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "3"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "0"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "1"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "2"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "3"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "0"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "1"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "2"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "3"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[ZERO, "0"]),
                call(A, "balanceOf(address)", &[A]),
                call(A, "balanceOf(address)", &[ZERO]),
                call(A, "ownerOf(uint256)", &["2"]),
                call(A, "ownerOf(uint256)", &["99"]),
                call(A, "tokenURI(uint256)", &["0"]),
                call(A, "tokenURI(uint256)", &["1"]),
                call(A, "tokenURI(uint256)", &["2"]),
                call(A, "tokenURI(uint256)", &["5"]),
                call(A, "tokenURI(uint256)", &["99"]),
                send(A, "approve(address,uint256)", &[B, "0"]),
                call(A, "getApproved(uint256)", &["0"]),
                call(A, "getApproved(uint256)", &["99"]),
                send(B, "approve(address,uint256)", &[B, "3"]),
                send(A, "approve(address,uint256)", &[B, "99"]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "0"]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "0"]),
                send(B, "transferFrom(address,address,uint256)", &[B, ZERO, "0"]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "3"]),
                send(A, "transferFrom(address,address,uint256)", &[A, B, "99"]),
                send(B, "setApprovalForAll(address,bool)", &[A, "true"]),
                send(B, "setApprovalForAll(address,bool)", &[ZERO, "true"]),
                call(A, "isApprovedForAll(address,address)", &[B, A]),
                send(A, "transferFrom(address,address,uint256)", &[B, A, "1"]),
                send(A, "transferFrom(address,address,uint256)", &[A, A, "1"]),
                call(A, "totalSupply()", &[]),
                call(A, "tokenByIndex(uint256)", &["0"]),
                call(A, "tokenByIndex(uint256)", &["1"]),
                call(A, "tokenByIndex(uint256)", &["2"]),
                call(A, "tokenByIndex(uint256)", &["3"]),
                call(A, "tokenByIndex(uint256)", &["4"]),
                call(A, "tokenByIndex(uint256)", &["5"]),
                call(A, "tokenByIndex(uint256)", &["6"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "0"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "1"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "2"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "3"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "0"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "1"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "2"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "3"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "0"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "1"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "2"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "3"]),
                send(A, "safeTransferFrom(address,address,uint256)", &[A, B, "3"]),
                send(A, "safeTransferFrom(address,address,uint256,bytes)", &[A, "$receiver", "4", "0xabababababababababababababababababababababababababababababababababababababababab"]),
                send(A, "setMode(uint256)", &["1"]).on("receiver"),
                send(A, "safeTransferFrom(address,address,uint256)", &[A, "$receiver", "1"]),
                send(A, "safeMint(address,string)", &["$receiver", "r.json"]),
                send(A, "setMode(uint256)", &["2"]).on("receiver"),
                call(A, "safeTransferFrom(address,address,uint256)", &[A, "$receiver", "1"]),
                send(A, "safeTransferFrom(address,address,uint256)", &[A, "$receiver", "1"]),
                send(A, "setMode(uint256)", &["0"]).on("receiver"),
                call(A, "safeTransferFrom(address,address,uint256)", &[A, "$nft", "1"]),
                send(A, "safeTransferFrom(address,address,uint256)", &[A, "$nft", "1"]),
                send(A, "safeTransferFrom(address,address,uint256)", &[B, A, "1"]),
                call(A, "totalSupply()", &[]),
                call(A, "tokenByIndex(uint256)", &["0"]),
                call(A, "tokenByIndex(uint256)", &["1"]),
                call(A, "tokenByIndex(uint256)", &["2"]),
                call(A, "tokenByIndex(uint256)", &["3"]),
                call(A, "tokenByIndex(uint256)", &["4"]),
                call(A, "tokenByIndex(uint256)", &["5"]),
                call(A, "tokenByIndex(uint256)", &["6"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "0"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "1"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "2"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "3"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "0"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "1"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "2"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "3"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "0"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "1"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "2"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "3"]),
                send(A, "burn(uint256)", &["5"]),
                send(B, "burn(uint256)", &["0"]),
                send(B, "burn(uint256)", &["0"]),
                call(A, "tokenURI(uint256)", &["0"]),
                call(A, "getApproved(uint256)", &["0"]),
                call(A, "totalSupply()", &[]),
                call(A, "tokenByIndex(uint256)", &["0"]),
                call(A, "tokenByIndex(uint256)", &["1"]),
                call(A, "tokenByIndex(uint256)", &["2"]),
                call(A, "tokenByIndex(uint256)", &["3"]),
                call(A, "tokenByIndex(uint256)", &["4"]),
                call(A, "tokenByIndex(uint256)", &["5"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "0"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "1"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "2"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "3"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "0"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "1"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "2"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "3"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "0"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "1"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "2"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "3"]),
                call(A, "royaltyInfo(uint256,uint256)", &["1", "1000000000000000000"]),
                send(A, "setTokenRoyalty(uint256,address,uint96)", &["1", B, "1000"]),
                call(A, "royaltyInfo(uint256,uint256)", &["1", "1000000000000000000"]),
                call(A, "royaltyInfo(uint256,uint256)", &["2", "1000000000000000000"]),
                call(A, "royaltyInfo(uint256,uint256)", &["1", MAX]),
                send(A, "setTokenRoyalty(uint256,address,uint96)", &["1", B, "10001"]),
                send(A, "setTokenRoyalty(uint256,address,uint96)", &["1", ZERO, "100"]),
                send(A, "setTokenRoyalty(uint256,address,uint96)", &["2", "$receiver", "10000"]),
                call(A, "royaltyInfo(uint256,uint256)", &["2", "12345"]),
                send(B, "setTokenRoyalty(uint256,address,uint96)", &["1", B, "1"]),
                send(A, "setDefaultRoyalty(address,uint96)", &[B, "10001"]),
                send(A, "setDefaultRoyalty(address,uint96)", &[ZERO, "1"]),
                send(A, "setDefaultRoyalty(address,uint96)", &[B, "250"]),
                send(B, "setDefaultRoyalty(address,uint96)", &[B, "250"]),
                call(A, "royaltyInfo(uint256,uint256)", &["4", "999"]),
                send(A, "resetTokenRoyalty(uint256)", &["1"]),
                send(B, "resetTokenRoyalty(uint256)", &["1"]),
                call(A, "royaltyInfo(uint256,uint256)", &["1", "1000000000000000000"]),
                send(A, "deleteDefaultRoyalty()", &[]),
                send(B, "deleteDefaultRoyalty()", &[]),
                call(A, "royaltyInfo(uint256,uint256)", &["1", "1000000000000000000"]),
                call(A, "royaltyInfo(uint256,uint256)", &["2", "1000000000000000000"]),
                send(B, "pause()", &[]),
                send(A, "pause()", &[]),
                send(A, "pause()", &[]),
                call(A, "paused()", &[]),
                send(A, "transferFrom(address,address,uint256)", &[A, B, "1"]),
                send(A, "transferFrom(address,address,uint256)", &[A, ZERO, "1"]),
                send(A, "safeMint(address,string)", &[A, "p.json"]),
                send(A, "burn(uint256)", &["1"]),
                send(A, "approve(address,uint256)", &[B, "1"]),
                send(A, "unpause()", &[]),
                send(A, "unpause()", &[]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "1"]),
                send(A, "safeMint(address,string)", &[A, "after.json"]),
                call(A, "tokenURI(uint256)", &["6"]),
                send(A, "transferOwnership(address)", &[ZERO]),
                send(A, "transferOwnership(address)", &[B]),
                send(A, "safeMint(address,string)", &[A, "old.json"]),
                send(B, "safeMint(address,string)", &[A, ""]),
                call(A, "tokenURI(uint256)", &["7"]),
                send(B, "renounceOwnership()", &[]),
                call(A, "owner()", &[]),
                send(B, "setDefaultRoyalty(address,uint96)", &[B, "1"]),
                call(A, "totalSupply()", &[]),
                call(A, "tokenByIndex(uint256)", &["0"]),
                call(A, "tokenByIndex(uint256)", &["1"]),
                call(A, "tokenByIndex(uint256)", &["2"]),
                call(A, "tokenByIndex(uint256)", &["3"]),
                call(A, "tokenByIndex(uint256)", &["4"]),
                call(A, "tokenByIndex(uint256)", &["5"]),
                call(A, "tokenByIndex(uint256)", &["6"]),
                call(A, "tokenByIndex(uint256)", &["7"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "0"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "1"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "2"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[A, "3"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "0"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "1"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "2"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &[B, "3"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "0"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "1"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "2"]),
                call(A, "tokenOfOwnerByIndex(address,uint256)", &["$receiver", "3"]),
                call(A, "balanceOf(address)", &[A]),
                call(A, "balanceOf(address)", &[B]),
                call(A, "balanceOf(address)", &["$receiver"]),
                send(A, "0x04634d8d000000000000000000000000f39fd6e51aad88f6f4ce6ab8827279cfffb922660000000000000000000000000000000000000001000000000000000000000000", &[]),
            ],
        ),
        suite(
            "erc4626",
            vec![deploy("asset", "erc20", "address", &[A]), deploy("vault", "erc4626", "address", &["$asset"])],
            vec![
                call(A, "name()", &[]).on("vault"),
                call(A, "symbol()", &[]).on("vault"),
                call(A, "decimals()", &[]).on("vault"),
                call(A, "asset()", &[]).on("vault"),
                call(A, "totalAssets()", &[]).on("vault"),
                call(A, "totalSupply()", &[]).on("vault"),
                call(A, "maxDeposit(address)", &[A]).on("vault"),
                call(A, "maxMint(address)", &[A]).on("vault"),
                send(A, "mint(address,uint256)", &[A, "1000000000000000000000"]),
                send(A, "mint(address,uint256)", &[B, "1000000000000000000000"]),
                send(A, "deposit(uint256,address)", &["1000000000000000000", A]).on("vault"),
                send(A, "approve(address,uint256)", &["$vault", MAX]),
                send(B, "approve(address,uint256)", &["$vault", "500000000000000000000"]),
                send(A, "deposit(uint256,address)", &["1000000000000000000", ZERO]).on("vault"),
                send(A, "deposit(uint256,address)", &["100000000000000000000", A]).on("vault"),
                send(A, "deposit(uint256,address)", &["0", A]).on("vault"),
                send(B, "mint(uint256,address)", &["50000000000000000000", B]).on("vault"),
                send(B, "mint(uint256,address)", &["1000000000000000000000000000000", B]).on("vault"),
                send(A, "transfer(address,uint256)", &["$vault", "7"]),
                call(A, "convertToShares(uint256)", &["0"]).on("vault"),
                call(A, "convertToShares(uint256)", &["1"]).on("vault"),
                call(A, "convertToShares(uint256)", &["999"]).on("vault"),
                call(A, "convertToShares(uint256)", &["1000000000000000000"]).on("vault"),
                call(A, "convertToAssets(uint256)", &["0"]).on("vault"),
                call(A, "convertToAssets(uint256)", &["1"]).on("vault"),
                call(A, "convertToAssets(uint256)", &["999"]).on("vault"),
                call(A, "convertToAssets(uint256)", &["1000000000000000000"]).on("vault"),
                call(A, "previewDeposit(uint256)", &["0"]).on("vault"),
                call(A, "previewDeposit(uint256)", &["1"]).on("vault"),
                call(A, "previewDeposit(uint256)", &["999"]).on("vault"),
                call(A, "previewDeposit(uint256)", &["1000000000000000000"]).on("vault"),
                call(A, "previewMint(uint256)", &["0"]).on("vault"),
                call(A, "previewMint(uint256)", &["1"]).on("vault"),
                call(A, "previewMint(uint256)", &["999"]).on("vault"),
                call(A, "previewMint(uint256)", &["1000000000000000000"]).on("vault"),
                call(A, "previewWithdraw(uint256)", &["0"]).on("vault"),
                call(A, "previewWithdraw(uint256)", &["1"]).on("vault"),
                call(A, "previewWithdraw(uint256)", &["999"]).on("vault"),
                call(A, "previewWithdraw(uint256)", &["1000000000000000000"]).on("vault"),
                call(A, "previewRedeem(uint256)", &["0"]).on("vault"),
                call(A, "previewRedeem(uint256)", &["1"]).on("vault"),
                call(A, "previewRedeem(uint256)", &["999"]).on("vault"),
                call(A, "previewRedeem(uint256)", &["1000000000000000000"]).on("vault"),
                call(A, "maxWithdraw(address)", &[A]).on("vault"),
                call(A, "maxRedeem(address)", &[A]).on("vault"),
                send(A, "withdraw(uint256,address,address)", &["200000000000000000000", A, A]).on("vault"),
                send(A, "redeem(uint256,address,address)", &["200000000000000000000", A, A]).on("vault"),
                send(A, "withdraw(uint256,address,address)", &["10000000000000000000", B, A]).on("vault"),
                send(A, "redeem(uint256,address,address)", &["10000000000000000000", B, A]).on("vault"),
                send(B, "redeem(uint256,address,address)", &["1000000000000000000", B, A]).on("vault"),
                send(A, "approve(address,uint256)", &[B, "5000000000000000000"]).on("vault"),
                send(B, "redeem(uint256,address,address)", &["2000000000000000000", B, A]).on("vault"),
                send(B, "withdraw(uint256,address,address)", &["1000000000000000000", B, A]).on("vault"),
                send(B, "withdraw(uint256,address,address)", &["10000000000000000000", B, A]).on("vault"),
                send(A, "withdraw(uint256,address,address)", &["1", ZERO, A]).on("vault"),
                send(B, "redeem(uint256,address,address)", &["50000000000000000000", B, B]).on("vault"),
                call(A, "maxWithdraw(address)", &[B]).on("vault"),
                call(A, "totalAssets()", &[]).on("vault"),
                call(A, "totalSupply()", &[]).on("vault"),
                call(A, "balanceOf(address)", &[A]).on("vault"),
                call(A, "balanceOf(address)", &[B]).on("vault"),
                call(A, "balanceOf(address)", &["$vault"]),
            ],
        ),
        suite(
            "safe_erc20",
            vec![deploy("token", "erc20", "address", &[A]), deploy("payer", "safe_erc20", "", &[])],
            vec![
                send(A, "mint(address,uint256)", &["$payer", "1000000"]),
                send(A, "mint(address,uint256)", &[B, "1000000"]),
                send(A, "pay(address,address,uint256)", &["$token", B, "1000"]).on("payer"),
                send(A, "pay(address,address,uint256)", &["$token", B, "1000"]).on("payer"),
                send(A, "pay(address,address,uint256)", &["$token", A, "5000000"]).on("payer"),
                send(B, "approve(address,uint256)", &["$payer", "5000"]),
                send(A, "pull(address,address,uint256)", &["$token", B, "2000"]).on("payer"),
                send(A, "pull(address,address,uint256)", &["$token", B, "2000"]).on("payer"),
                send(A, "pull(address,address,uint256)", &["$token", B, "2000"]).on("payer"),
                send(A, "allow(address,address,uint256)", &["$token", B, "5"]).on("payer"),
                send(A, "allow(address,address,uint256)", &["$token", B, "7"]).on("payer"),
                call(A, "allowance(address,address)", &["$payer", B]),
            ],
        ),
        suite(
            "ownable_roles",
            vec![deploy("roles", "ownable_roles", "", &[])],
            vec![
                send(A, "grantRoles(address,uint256)", &[B, "1"]),
                send(A, "grantRoles(address,uint256)", &[B, "2"]),
                send(B, "grantRoles(address,uint256)", &[B, "4"]),
                send(B, "mint(address,uint256)", &[A, "10"]),
                send(B, "mint(address,uint256)", &[A, "10"]),
                send(A, "mint(address,uint256)", &[A, "10"]),
                send(A, "pause()", &[]),
                send(B, "unpause()", &[]),
                send(B, "pause()", &[]),
                send(A, "unpause()", &[]),
                call(A, "hasAnyRole(address,uint256)", &[B, "1"]),
                call(A, "hasAllRoles(address,uint256)", &[B, "7"]),
                call(A, "rolesOf(address)", &[B]),
                call(A, "minted(address)", &[A]),
                send(A, "revokeRoles(address,uint256)", &[B, "1"]),
                send(B, "renounceRoles(uint256)", &["2"]),
                send(B, "mint(address,uint256)", &[A, "10"]),
                send(B, "pause()", &[]),
            ],
        ),
        suite(
            "erc20_full",
            vec![deploy("token", "erc20_full", "address,address,address", &[A, A, A]), deploy("borrower", "flash_borrower", "", &[])],
            vec![
                call(A, "name()", &[]),
                call(A, "symbol()", &[]),
                call(A, "decimals()", &[]),
                call(A, "totalSupply()", &[]),
                call(A, "cap()", &[]),
                call(A, "paused()", &[]),
                call(A, "DEFAULT_ADMIN_ROLE()", &[]),
                call(A, "MINTER_ROLE()", &[]),
                call(A, "PAUSER_ROLE()", &[]),
                call(A, "clock()", &[]),
                call(A, "CLOCK_MODE()", &[]),
                call(A, "DOMAIN_SEPARATOR()", &[]),
                call(A, "eip712Domain()", &[]),
                call(A, "supportsInterface(bytes4)", &["0x7965db0b"]),
                call(A, "supportsInterface(bytes4)", &["0x01ffc9a7"]),
                call(A, "supportsInterface(bytes4)", &["0x36372b07"]),
                call(A, "supportsInterface(bytes4)", &["0xffffffff"]),
                call(A, "hasRole(bytes32,address)", &["0x9f2df0fed2c77648de5860a4cc508cd0818c85b8b8a1ab4ceeef8d981c8956a6", A]),
                call(A, "hasRole(bytes32,address)", &["0x9f2df0fed2c77648de5860a4cc508cd0818c85b8b8a1ab4ceeef8d981c8956a6", B]),
                call(A, "getRoleAdmin(bytes32)", &["0x9f2df0fed2c77648de5860a4cc508cd0818c85b8b8a1ab4ceeef8d981c8956a6"]),
                call(A, "maxFlashLoan(address)", &["$token"]),
                call(A, "maxFlashLoan(address)", &[B]),
                call(A, "flashFee(address,uint256)", &["$token", "1000000000000000000"]),
                call(A, "flashFee(address,uint256)", &[B, "1"]),
                send(A, "mint(address,uint256)", &[A, "1000000000000000000000"]),
                send(B, "mint(address,uint256)", &[B, "5"]),
                send(A, "mint(address,uint256)", &[ZERO, "1"]),
                send(A, "mint(address,uint256)", &[B, "1000000000000000000000000"]),
                call(A, "getVotes(address)", &[A]),
                send(A, "delegate(address)", &[A]),
                send(A, "transfer(address,uint256)", &[B, "100000000000000000000"]),
                send(B, "delegate(address)", &[B]),
                send(B, "transfer(address,uint256)", &[A, "10000000000000000000"]),
                send(A, "transfer(address,uint256)", &[ZERO, "1"]),
                send(B, "transfer(address,uint256)", &[A, "1000000000000000000000000000000"]),
                send(A, "transfer(address,uint256)", &[B, "1000000000000000000"]),
                send(A, "transfer(address,uint256)", &[B, "1000000000000000000"]),
                send(A, "transfer(address,uint256)", &[B, "1000000000000000000"]),
                send(A, "transfer(address,uint256)", &[B, "1000000000000000000"]),
                send(A, "transfer(address,uint256)", &[B, "1000000000000000000"]),
                send(A, "transfer(address,uint256)", &[B, "1000000000000000000"]),
                send(A, "mint(address,uint256)", &[B, "50000000000000000000"]),
                send(B, "burn(uint256)", &["5000000000000000000"]),
                send(B, "burn(uint256)", &["1000000000000000000000000000000"]),
                send(A, "approve(address,uint256)", &[B, "20000000000000000000"]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "5000000000000000000"]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "100000000000000000000"]),
                send(B, "burnFrom(address,uint256)", &[A, "5000000000000000000"]),
                send(A, "burnFrom(address,uint256)", &[B, "1"]),
                send(A, "delegate(address)", &[B]),
                send(A, "delegate(address)", &[ZERO]),
                send(A, "delegate(address)", &[A]),
                call(A, "getVotes(address)", &[A]),
                call(A, "delegates(address)", &[A]),
                call(A, "numCheckpoints(address)", &[A]),
                call(A, "checkpoints(address,uint32)", &[A, "0"]),
                call(A, "checkpoints(address,uint32)", &[A, "1"]),
                call(A, "checkpoints(address,uint32)", &[A, "7"]),
                call(A, "checkpoints(address,uint32)", &[A, "99"]),
                call(A, "getPastVotes(address,uint256)", &[A, "1"]),
                call(A, "getPastVotes(address,uint256)", &[A, "6"]),
                call(A, "getPastVotes(address,uint256)", &[A, "7"]),
                call(A, "getPastVotes(address,uint256)", &[A, "10"]),
                call(A, "getPastVotes(address,uint256)", &[A, "16"]),
                call(A, "getPastVotes(address,uint256)", &[A, "18"]),
                call(A, "getPastVotes(address,uint256)", &[A, "19"]),
                call(A, "getPastVotes(address,uint256)", &[A, "28"]),
                call(A, "getPastVotes(address,uint256)", &[A, "34"]),
                call(A, "getVotes(address)", &[B]),
                call(A, "delegates(address)", &[B]),
                call(A, "numCheckpoints(address)", &[B]),
                call(A, "checkpoints(address,uint32)", &[B, "0"]),
                call(A, "checkpoints(address,uint32)", &[B, "1"]),
                call(A, "checkpoints(address,uint32)", &[B, "7"]),
                call(A, "checkpoints(address,uint32)", &[B, "99"]),
                call(A, "getPastVotes(address,uint256)", &[B, "1"]),
                call(A, "getPastVotes(address,uint256)", &[B, "6"]),
                call(A, "getPastVotes(address,uint256)", &[B, "7"]),
                call(A, "getPastVotes(address,uint256)", &[B, "10"]),
                call(A, "getPastVotes(address,uint256)", &[B, "16"]),
                call(A, "getPastVotes(address,uint256)", &[B, "18"]),
                call(A, "getPastVotes(address,uint256)", &[B, "19"]),
                call(A, "getPastVotes(address,uint256)", &[B, "28"]),
                call(A, "getPastVotes(address,uint256)", &[B, "34"]),
                call(A, "getPastTotalSupply(uint256)", &["1"]),
                call(A, "getPastTotalSupply(uint256)", &["7"]),
                call(A, "getPastTotalSupply(uint256)", &["19"]),
                call(A, "getPastTotalSupply(uint256)", &["28"]),
                call(A, "getPastTotalSupply(uint256)", &["34"]),
                send(B, "pause()", &[]),
                send(B, "grantRole(bytes32,address)", &["0x65d7a28e3265b37a6474929f336521b332c1681b933f6cb9f3376673440d862a", B]),
                send(A, "grantRole(bytes32,address)", &["0x65d7a28e3265b37a6474929f336521b332c1681b933f6cb9f3376673440d862a", B]),
                send(A, "grantRole(bytes32,address)", &["0x65d7a28e3265b37a6474929f336521b332c1681b933f6cb9f3376673440d862a", B]),
                send(B, "pause()", &[]),
                send(B, "pause()", &[]),
                call(A, "paused()", &[]),
                send(A, "transfer(address,uint256)", &[B, "1"]),
                send(A, "mint(address,uint256)", &[A, "1"]),
                send(A, "flashLoan(address,address,uint256,bytes)", &["$borrower", "$token", "1000000000000000000", "0x"]),
                send(A, "approve(address,uint256)", &[B, "7"]),
                send(B, "delegate(address)", &[A]),
                send(A, "unpause()", &[]),
                send(B, "unpause()", &[]),
                send(B, "unpause()", &[]),
                send(A, "revokeRole(bytes32,address)", &["0x65d7a28e3265b37a6474929f336521b332c1681b933f6cb9f3376673440d862a", B]),
                send(B, "renounceRole(bytes32,address)", &["0x9f2df0fed2c77648de5860a4cc508cd0818c85b8b8a1ab4ceeef8d981c8956a6", A]),
                send(B, "pause()", &[]),
                send(A, "flashLoan(address,address,uint256,bytes)", &["$borrower", "$token", "1000000000000000000000", "0xabababababababababababababababababababababababababababababababababababababababab"]),
                call(A, "totalSupply()", &[]),
                call(A, "balanceOf(address)", &["$borrower"]),
                call(A, "allowance(address,address)", &["$borrower", "$token"]),
                send(A, "flashLoan(address,address,uint256,bytes)", &["$borrower", "$token", MAX, "0x"]),
                send(A, "flashLoan(address,address,uint256,bytes)", &["$borrower", B, "0", "0x"]),
                send(A, "flashLoan(address,address,uint256,bytes)", &["$borrower", B, "1", "0x"]),
                send(A, "flashLoan(address,address,uint256,bytes)", &["$borrower", "$token", "1000000000000000000000000", "0x"]),
                send(A, "flashLoan(address,address,uint256,bytes)", &[ZERO, "$token", "1", "0x"]),
                send(A, "flashLoan(address,address,uint256,bytes)", &[B, "$token", "1", "0x"]),
                send(A, "setMode(uint256)", &["1"]).on("borrower"),
                call(A, "flashLoan(address,address,uint256,bytes)", &["$borrower", "$token", "7", "0x"]),
                send(A, "flashLoan(address,address,uint256,bytes)", &["$borrower", "$token", "7", "0x"]),
                send(A, "setMode(uint256)", &["2"]).on("borrower"),
                call(A, "flashLoan(address,address,uint256,bytes)", &["$borrower", "$token", "7", "0x"]),
                send(A, "flashLoan(address,address,uint256,bytes)", &["$borrower", "$token", "7", "0x"]),
                send(A, "setMode(uint256)", &["3"]).on("borrower"),
                call(A, "flashLoan(address,address,uint256,bytes)", &["$borrower", "$token", "7", "0x"]),
                send(A, "flashLoan(address,address,uint256,bytes)", &["$borrower", "$token", "7", "0x"]),
                send(A, "setMode(uint256)", &["0"]).on("borrower"),
                send(B, "flashLoan(address,address,uint256,bytes)", &["$borrower", "$token", "7", "0x1234"]),
                send(A, "flashLoan(address,address,uint256,bytes)", &["$borrower", "$token", "7", "0x"]).succeeds(),
                send(B, "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", &[A, B, "123", "3000000000"]).signed(PERMIT, &[A, B, "123", "0", "3000000000"], KEY_A),
                call(A, "allowance(address,address)", &[A, B]),
                call(A, "nonces(address)", &[A]),
                send(B, "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", &[A, B, "123", "3000000000"]).signed(PERMIT, &[A, B, "123", "0", "3000000000"], KEY_A),
                send(B, "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", &[A, B, "5", "1"]).signed(PERMIT, &[A, B, "5", "1", "1"], KEY_A),
                send(B, "delegateBySig(address,uint256,uint256,uint8,bytes32,bytes32)", &[B, "1", "3000000000"]).signed(DELEGATION, &[B, "1", "3000000000"], KEY_A),
                call(A, "delegates(address)", &[A]),
                send(B, "delegateBySig(address,uint256,uint256,uint8,bytes32,bytes32)", &[B, "1", "3000000000"]).signed(DELEGATION, &[B, "1", "3000000000"], KEY_A),
                send(B, "delegateBySig(address,uint256,uint256,uint8,bytes32,bytes32)", &[B, "2", "1"]).signed(DELEGATION, &[B, "2", "1"], KEY_A),
                call(A, "nonces(address)", &[A]),
                send(A, "renounceRole(bytes32,address)", &["0x9f2df0fed2c77648de5860a4cc508cd0818c85b8b8a1ab4ceeef8d981c8956a6", A]),
                send(A, "mint(address,uint256)", &[A, "1"]),
                call(A, "totalSupply()", &[]),
                call(A, "totalSupply()", &[]),
                call(A, "getVotes(address)", &[A]),
                call(A, "getVotes(address)", &[B]),
                call(A, "balanceOf(address)", &[A]),
                call(A, "balanceOf(address)", &[B]),
                send(A, "0xa9059cbb00000000000000000000000070997970c51812dc3a010c7d01b50e0d17dc79c8", &[]),
            ],
        ),
        suite(
            "solady_erc20",
            vec![deploy("token", "solady_erc20", "", &[])],
            vec![
                call(A, "name()", &[]),
                call(A, "symbol()", &[]),
                call(A, "decimals()", &[]),
                call(A, "totalSupply()", &[]),
                call(A, "DOMAIN_SEPARATOR()", &[]),
                send(A, "mint(address,uint256)", &[A, "1000000000000000000000"]),
                send(B, "mint(address,uint256)", &[B, "5"]),
                send(A, "mint(address,uint256)", &[ZERO, "1"]),
                send(A, "mint(address,uint256)", &[A, MAX]),
                send(A, "transfer(address,uint256)", &[B, "100000000000000000000"]),
                call(A, "transfer(address,uint256)", &[B, "1"]),
                send(A, "transfer(address,uint256)", &[ZERO, "1"]),
                send(A, "transfer(address,uint256)", &[A, "7"]),
                send(A, "transfer(address,uint256)", &[B, "0"]),
                send(B, "transfer(address,uint256)", &[A, "1000000000000000000000000000000"]),
                send(A, "approve(address,uint256)", &[B, "500000000000000000000"]),
                send(A, "approve(address,uint256)", &[ZERO, "1"]),
                call(A, "allowance(address,address)", &[A, B]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "200000000000000000000"]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "400000000000000000000"]),
                send(B, "transferFrom(address,address,uint256)", &[A, ZERO, "1"]),
                send(A, "approve(address,uint256)", &[B, MAX]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "1"]),
                call(A, "allowance(address,address)", &[A, B]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "1000000000000000000000000000000"]),
                call(A, "allowance(address,address)", &[A, "0x000000000022D473030F116dDEE9F6B43aC78BA3"]),
                send(A, "approve(address,uint256)", &["0x000000000022D473030F116dDEE9F6B43aC78BA3", "5"]),
                send(A, "approve(address,uint256)", &["0x000000000022D473030F116dDEE9F6B43aC78BA3", MAX]),
                send(B, "burn(uint256)", &["10000000000000000000"]),
                send(B, "burn(uint256)", &["1000000000000000000000000000000"]),
                send(B, "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", &[A, B, "123", "3000000000"]).signed(PERMIT, &[A, B, "123", "0", "3000000000"], KEY_A),
                call(A, "allowance(address,address)", &[A, B]),
                call(A, "nonces(address)", &[A]),
                send(B, "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", &[A, B, "123", "3000000000"]).signed(PERMIT, &[A, B, "123", "0", "3000000000"], KEY_A),
                send(B, "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", &[A, B, "5", "1"]).signed(PERMIT, &[A, B, "5", "1", "1"], KEY_A),
                send(B, "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", &[A, "0x000000000022D473030F116dDEE9F6B43aC78BA3", "5", "3000000000"]).signed(PERMIT, &[A, "0x000000000022D473030F116dDEE9F6B43aC78BA3", "5", "1", "3000000000"], KEY_A),
                send(B, "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", &[B, B, "5", "3000000000"]).signed(PERMIT, &[A, B, "5", "1", "3000000000"], KEY_A),
                send(B, "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", &[ZERO, B, "5", "3000000000", "27", "0x1111111111111111111111111111111111111111111111111111111111111111", "0x2222222222222222222222222222222222222222222222222222222222222222"]),
                send(B, "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", &[A, B, "9", "3000000000"]).signed(PERMIT, &[A, B, "9", "1", "3000000000"], KEY_A),
                call(A, "nonces(address)", &[A]),
                call(A, "totalSupply()", &[]),
                call(A, "balanceOf(address)", &[A]),
                call(A, "balanceOf(address)", &[B]),
                call(A, "balanceOf(address)", &[ZERO]),
                send(A, "0xa9059cbb00000000000000000000000070997970c51812dc3a010c7d01b50e0d17dc79c8", &[]),
            ],
        ),
        suite(
            "solady_erc721",
            vec![deploy("nft", "solady_erc721", "", &[]), deploy("receiver", "receiver", "", &[])],
            vec![
                call(A, "name()", &[]),
                call(A, "symbol()", &[]),
                call(A, "supportsInterface(bytes4)", &["0x80ac58cd"]),
                call(A, "supportsInterface(bytes4)", &["0x5b5e139f"]),
                call(A, "supportsInterface(bytes4)", &["0x01ffc9a7"]),
                call(A, "supportsInterface(bytes4)", &["0xffffffff"]),
                send(A, "mint(address,uint256)", &[A, "1"]),
                send(B, "mint(address,uint256)", &[B, "2"]),
                send(A, "mint(address,uint256)", &[ZERO, "3"]),
                send(A, "mint(address,uint256)", &[B, "1"]),
                send(A, "safeMint(address,uint256,bytes)", &["$receiver", "3", "0xabababababababababababababababababababababababababababababababababababababababab"]),
                send(A, "safeMint(address,uint256,bytes)", &[A, "4", "0x"]),
                send(A, "safeMint(address,uint256,bytes)", &[A, "5", "0x1234"]),
                send(A, "mint(address,uint256)", &[A, "6"]),
                send(A, "safeMint(address,uint256,bytes)", &["$nft", "7", "0x"]),
                call(A, "balanceOf(address)", &[A]),
                call(A, "balanceOf(address)", &[ZERO]),
                call(A, "ownerOf(uint256)", &["1"]),
                call(A, "ownerOf(uint256)", &["99"]),
                call(A, "tokenURI(uint256)", &["1"]),
                call(A, "tokenURI(uint256)", &["4"]),
                call(A, "tokenURI(uint256)", &["99"]),
                send(A, "approve(address,uint256)", &[B, "1"]),
                call(A, "getApproved(uint256)", &["1"]),
                call(A, "getApproved(uint256)", &["99"]),
                send(B, "approve(address,uint256)", &[B, "4"]),
                send(A, "approve(address,uint256)", &[B, "99"]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "1"]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "1"]),
                send(B, "transferFrom(address,address,uint256)", &[B, ZERO, "1"]),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "4"]),
                send(A, "transferFrom(address,address,uint256)", &[A, B, "99"]),
                send(B, "setApprovalForAll(address,bool)", &[A, "true"]),
                send(B, "setApprovalForAll(address,bool)", &[ZERO, "true"]),
                call(A, "isApprovedForAll(address,address)", &[B, A]),
                send(A, "transferFrom(address,address,uint256)", &[B, A, "2"]).paying("1"),
                send(A, "approve(address,uint256)", &[A, "1"]),
                send(A, "safeTransferFrom(address,address,uint256)", &[A, B, "2"]),
                send(A, "safeTransferFrom(address,address,uint256,bytes)", &[A, "$receiver", "4", "0xabababababababababababababababababababababababababababababababababababababababab"]),
                send(A, "safeTransferFrom(address,address,uint256,bytes)", &[A, "$receiver", "5", "0x1234"]),
                send(A, "setMode(uint256)", &["1"]).on("receiver"),
                send(A, "safeTransferFrom(address,address,uint256)", &[A, "$receiver", "6"]),
                send(A, "setMode(uint256)", &["2"]).on("receiver"),
                call(A, "safeTransferFrom(address,address,uint256)", &[A, "$receiver", "6"]),
                send(A, "safeTransferFrom(address,address,uint256)", &[A, "$receiver", "6"]),
                send(A, "setMode(uint256)", &["0"]).on("receiver"),
                call(A, "safeTransferFrom(address,address,uint256)", &[A, "$nft", "6"]),
                send(A, "safeTransferFrom(address,address,uint256)", &[A, "$nft", "6"]),
                send(A, "burn(uint256)", &["1"]),
                send(B, "burn(uint256)", &["1"]),
                send(B, "burn(uint256)", &["6"]),
                send(A, "burn(uint256)", &["6"]),
                call(A, "getApproved(uint256)", &["1"]),
                send(A, "mint(address,uint256)", &[A, "1"]),
                call(A, "balanceOf(address)", &[A]),
                call(A, "balanceOf(address)", &[B]),
                call(A, "balanceOf(address)", &["$receiver"]),
            ],
        ),
        suite(
            "solady_erc1155",
            vec![deploy("mt", "solady_erc1155", "", &[]), deploy("r1155", "receiver1155", "", &[]), deploy("plain", "receiver", "", &[])],
            vec![
                call(A, "uri(uint256)", &["1"]),
                call(A, "supportsInterface(bytes4)", &["0xd9b67a26"]),
                call(A, "supportsInterface(bytes4)", &["0x0e89341c"]),
                call(A, "supportsInterface(bytes4)", &["0x01ffc9a7"]),
                call(A, "supportsInterface(bytes4)", &["0x80ac58cd"]),
                call(A, "supportsInterface(bytes4)", &["0xffffffff"]),
                send(A, "mint(address,uint256,uint256,bytes)", &[A, "1", "100", "0x"]),
                send(B, "mint(address,uint256,uint256,bytes)", &[B, "2", "50", "0x1234"]),
                send(A, "mint(address,uint256,uint256,bytes)", &[ZERO, "1", "1", "0x"]),
                send(A, "mint(address,uint256,uint256,bytes)", &["$r1155", "3", "10", &["0x", &"ab".repeat(100)].concat()]),
                send(A, "mint(address,uint256,uint256,bytes)", &["$plain", "3", "1", "0x"]),
                send(A, "mint(address,uint256,uint256,bytes)", &[A, "9", MAX, "0x"]),
                send(A, "mint(address,uint256,uint256,bytes)", &[A, "9", "1", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &[A, "[1,2,3]", "[10,20,30]", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &["$r1155", "[4,5,4]", "[1,2,3]", &["0x", &"ab".repeat(100)].concat()]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &["$r1155", "[7]", "[1]", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &[A, "[]", "[]", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &[A, "[1,2]", "[1]", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &[ZERO, "[1]", "[1]", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &[A, "[9,8,9]", "[1,1,1]", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &["$plain", "[1,2]", "[1,1]", "0x"]),
                send(A, "setMode(uint256)", &["1"]).on("r1155"),
                send(A, "mint(address,uint256,uint256,bytes)", &["$r1155", "3", "1", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &["$r1155", "[3,4]", "[1,1]", "0x"]),
                send(A, "setMode(uint256)", &["2"]).on("r1155"),
                call(A, "mint(address,uint256,uint256,bytes)", &["$r1155", "3", "1", "0x"]),
                call(A, "mintBatch(address,uint256[],uint256[],bytes)", &["$r1155", "[3,4]", "[1,1]", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &["$r1155", "[3,4]", "[1,1]", "0x"]),
                send(A, "setMode(uint256)", &["3"]).on("r1155"),
                call(A, "mint(address,uint256,uint256,bytes)", &["$r1155", "3", "1", "0x"]),
                send(A, "mintBatch(address,uint256[],uint256[],bytes)", &["$r1155", "[3,4]", "[1,1]", "0x"]),
                send(A, "setMode(uint256)", &["0"]).on("r1155"),
                call(A, "balanceOf(address,uint256)", &[A, "1"]),
                call(A, "balanceOf(address,uint256)", &["$r1155", "4"]),
                call(A, "balanceOfBatch(address[],uint256[])", &["[0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266,0x70997970C51812dC3A010C7d01b50e0d17dc79C8,0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266,0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266]", "[1,2,3,99]"]),
                call(A, "balanceOfBatch(address[],uint256[])", &["[0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266,0x70997970C51812dC3A010C7d01b50e0d17dc79C8]", "[1]"]),
                call(A, "balanceOfBatch(address[],uint256[])", &["[]", "[]"]),
                send(A, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, B, "1", "5", "0x"]),
                send(B, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, B, "1", "5", "0x"]),
                send(A, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, B, "1", "1000", "0x"]),
                send(A, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, ZERO, "1", "1", "0x"]),
                send(A, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[ZERO, B, "1", "1", "0x"]),
                send(A, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, A, "1", "1", "0x"]),
                send(A, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, "$r1155", "1", "5", &["0x", &"ab".repeat(100)].concat()]),
                send(A, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, "$plain", "1", "5", "0x"]),
                send(A, "setApprovalForAll(address,bool)", &[B, "true"]),
                send(A, "setApprovalForAll(address,bool)", &[ZERO, "true"]),
                call(A, "isApprovedForAll(address,address)", &[A, B]),
                send(B, "safeTransferFrom(address,address,uint256,uint256,bytes)", &[A, B, "1", "5", "0x"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, B, "[1,2,3]", "[1,2,3]", "0x"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, B, "[1,1,2]", "[1,2,3]", "0x1234"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, B, "[1,2]", "[1]", "0x"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, B, "[1,2]", "[1000,1000]", "0x"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, B, "[3,3]", "[20,20]", "0x"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, ZERO, "[1]", "[1]", "0x"]),
                send(B, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[B, A, "[2]", "[1]", "0x"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[B, A, "[2]", "[1]", "0x"]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, "$r1155", "[1,3,1]", "[1,1,1]", &["0x", &"ab".repeat(100)].concat()]),
                send(A, "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", &[A, "$plain", "[1,3]", "[1,1]", "0x"]),
                send(A, "burn(address,uint256,uint256)", &[A, "1", "1"]),
                send(B, "burn(address,uint256,uint256)", &[A, "1", "1"]),
                send(A, "setApprovalForAll(address,bool)", &[B, "false"]),
                send(B, "burn(address,uint256,uint256)", &[A, "1", "1"]),
                send(A, "burn(address,uint256,uint256)", &[A, "1", "1000"]),
                send(A, "burn(address,uint256,uint256)", &[ZERO, "1", "0"]),
                send(A, "burnBatch(address,uint256[],uint256[])", &[A, "[1,2,3]", "[1,1,1]"]),
                send(A, "burnBatch(address,uint256[],uint256[])", &[A, "[1,1]", "[1,1]"]),
                send(A, "burnBatch(address,uint256[],uint256[])", &[A, "[1,2]", "[1]"]),
                send(A, "burnBatch(address,uint256[],uint256[])", &[A, "[1,2]", "[1000,1000]"]),
                send(B, "burnBatch(address,uint256[],uint256[])", &[A, "[1]", "[1]"]),
                call(A, "balanceOfBatch(address[],uint256[])", &["[0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266,0x70997970C51812dC3A010C7d01b50e0d17dc79C8,0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266,0x70997970C51812dC3A010C7d01b50e0d17dc79C8,0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266]", "[1,1,2,2,9]"]),
                call(A, "balanceOf(address,uint256)", &["$r1155", "1"]),
                send(A, "0x4e1273f4000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000001", &[]),
            ],
        ),
        suite(
            "deployers",
            vec![deploy("counter", "counter", "", &[]), deploy("deployers", "deployers", "", &[])],
            vec![
                send(A, "clone(address)", &["$counter"]).on("deployers"),
                bind("clone", "deployers", "last()", &[]),
                send(A, "increment(uint256)", &["3"]).on("clone"),
                call(A, "getCount()", &[]).on("clone"),
                call(A, "predictClone(address,bytes32)", &["$counter", "0x0000000000000000000000000000000000000000000000000000000000000007"]).on("deployers"),
                send(A, "cloneDeterministic(address,bytes32)", &["$counter", "0x0000000000000000000000000000000000000000000000000000000000000007"]).on("deployers"),
                bind("salted", "deployers", "last()", &[]),
                send(A, "increment(uint256)", &["2"]).on("salted"),
                send(A, "cloneDeterministic(address,bytes32)", &["$counter", "0x0000000000000000000000000000000000000000000000000000000000000007"]).on("deployers"),
                send(A, "cloneWithArgs(address,bytes)", &["$counter", &["0x", &"ab".repeat(100)].concat()]).on("deployers"),
                bind("with_args", "deployers", "last()", &[]),
                call(A, "argsOf(address)", &["$with_args"]).on("deployers"),
                call(A, "argsOf(address)", &["$clone"]).on("deployers"),
                send(A, "increment(uint256)", &["1"]).on("with_args"),
                send(A, "write(bytes)", &[&["0x", &"cd".repeat(1000)].concat()]).on("deployers"),
                call(A, "read()", &[]).on("deployers"),
                send(A, "writeCounterfactual(bytes,bytes32)", &["0xefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefef", "0x0000000000000000000000000000000000000000000000000000000000000009"]).on("deployers"),
                call(A, "read()", &[]).on("deployers"),
                send(A, "writeCounterfactual(bytes,bytes32)", &["0xefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefef", "0x0000000000000000000000000000000000000000000000000000000000000009"]).on("deployers"),
                call(A, "predict3(bytes32)", &["0x0000000000000000000000000000000000000000000000000000000000000003"]).on("deployers"),
                send(A, "deploy3(bytes,bytes32)", &["0x6001600c60003960016000f3fe", "0x0000000000000000000000000000000000000000000000000000000000000003"]).on("deployers"),
                call(A, "last()", &[]).on("deployers"),
                send(A, "deploy3(bytes,bytes32)", &["0x6001600c60003960016000f3fe", "0x0000000000000000000000000000000000000000000000000000000000000003"]).on("deployers"),
                send(A, "deploy3(bytes,bytes32)", &["0x60006000fd", "0x0000000000000000000000000000000000000000000000000000000000000004"]).on("deployers"),
                send(A, "deploy3(bytes,bytes32)", &["0x6001600c60003960016000f3fe", "0x0000000000000000000000000000000000000000000000000000000000000005"]).on("deployers").paying("7"),
            ],
        ),
        suite(
            "swap",
            vec![deploy("exchange", "exchange", "", &[]), deploy("executor", "executor", "address,uint256", &["$exchange", "100"])],
            vec![
                call(A, "swap(uint256,uint256)", &["1000", "0"]),
                send(B, "swap(uint256,uint256)", &["5000", "1"]),
                send(A, "execute(uint256,uint256,uint256)", &["1", "1000", "1990"]).on("executor"),
                send(A, "execute(uint256,uint256,uint256)", &["1", "1000", "0"]).on("executor"),
                send(A, "execute(uint256,uint256,uint256)", &["2", "1000", "5000"]).on("executor"),
                send(A, "execute(uint256,uint256,uint256)", &["3", "10", "0"]).on("executor"),
                send(B, "execute(uint256,uint256,uint256)", &["5", "1000000000000000000000000", "0"]).on("executor"),
                send(A, "executeAndDeposit(uint256,uint256)", &["4", "500"]).on("executor"),
                send(A, "executeAndDeposit(uint256,uint256)", &["4", "500"]).on("executor"),
                send(A, "unwind(uint256)", &["4"]).on("executor"),
                send(A, "unwind(uint256)", &["4"]).on("executor"),
                send(A, "unwind(uint256)", &["9"]).on("executor"),
                call(A, "orderOf(uint256)", &["1"]).on("executor"),
                call(A, "orderOf(uint256)", &["2"]).on("executor"),
                call(A, "orderOf(uint256)", &["4"]).on("executor"),
                call(A, "sharesOf(address)", &["$executor"]),
            ],
        ),
        suite(
            "uniswap_v2",
            vec![deploy("tka", "erc20", "address", &[A]), deploy("tkb", "erc20", "address", &[A]), deploy("factory", "uniswap_v2_factory", "address", &[A])],
            vec![
                send(A, "mint(address,uint256)", &[A, "10000000000000000000000"]),
                send(A, "mint(address,uint256)", &[B, "10000000000000000000000"]),
                send(A, "mint(address,uint256)", &[A, "10000000000000000000000"]).on("tkb"),
                send(A, "mint(address,uint256)", &[B, "10000000000000000000000"]).on("tkb"),
                call(A, "feeTo()", &[]).on("factory"),
                call(A, "feeToSetter()", &[]).on("factory"),
                call(A, "allPairsLength()", &[]).on("factory"),
                call(A, "createPair(address,address)", &["$tka", "$tka"]).on("factory"),
                send(A, "createPair(address,address)", &["$tka", "$tka"]).on("factory"),
                call(A, "createPair(address,address)", &["$tka", ZERO]).on("factory"),
                send(A, "createPair(address,address)", &["$tka", ZERO]).on("factory"),
                call(A, "createPair(address,address)", &[ZERO, "$tkb"]).on("factory"),
                bind("pair", "factory", "createPair(address,address)", &["$tka", "$tkb"]),
                send(B, "createPair(address,address)", &["$tka", "$tkb"]).on("factory"),
                call(A, "createPair(address,address)", &["$tkb", "$tka"]).on("factory"),
                send(A, "createPair(address,address)", &["$tkb", "$tka"]).on("factory"),
                call(A, "getPair(address,address)", &["$tka", "$tkb"]).on("factory"),
                call(A, "getPair(address,address)", &["$tkb", "$tka"]).on("factory"),
                call(A, "allPairs(uint256)", &["0"]).on("factory"),
                send(A, "allPairs(uint256)", &["1"]).on("factory"),
                call(A, "allPairsLength()", &[]).on("factory"),
                bind("domain", "pair", "DOMAIN_SEPARATOR()", &[]),
                bind("t0", "pair", "token0()", &[]),
                bind("t1", "pair", "token1()", &[]),
                call(A, "name()", &[]).on("pair"),
                call(A, "symbol()", &[]).on("pair"),
                call(A, "decimals()", &[]).on("pair"),
                call(A, "factory()", &[]).on("pair"),
                call(A, "MINIMUM_LIQUIDITY()", &[]).on("pair"),
                call(A, "PERMIT_TYPEHASH()", &[]).on("pair"),
                call(A, "DOMAIN_SEPARATOR()", &[]).on("pair"),
                call(A, "getReserves()", &[]).on("pair"),
                call(A, "totalSupply()", &[]).on("pair"),
                call(B, "initialize(address,address)", &["$t0", "$t1"]).on("pair"),
                send(B, "initialize(address,address)", &["$t0", "$t1"]).on("pair"),
                call(A, "mint(address)", &[A]).on("pair"),
                send(A, "transfer(address,uint256)", &["$pair", "1000000000000000000000"]).on("t0"),
                send(A, "transfer(address,uint256)", &["$pair", "4000000000000000000000"]).on("t1"),
                send(A, "mint(address)", &[A]).on("pair"),
                call(A, "getReserves()", &[]).on("pair"),
                call(A, "totalSupply()", &[]).on("pair"),
                call(A, "balanceOf(address)", &[A]).on("pair"),
                call(A, "balanceOf(address)", &[ZERO]).on("pair"),
                call(A, "mint(address)", &[A]).on("pair"),
                send(A, "mint(address)", &[A]).on("pair"),
                call(B, "swap(uint256,uint256,address,bytes)", &["0", "0", B, "0x"]).on("pair"),
                call(B, "swap(uint256,uint256,address,bytes)", &["0", "4000000000000000000000", B, "0x"]).on("pair"),
                call(B, "swap(uint256,uint256,address,bytes)", &["0", "1", "$t0", "0x"]).on("pair"),
                call(B, "swap(uint256,uint256,address,bytes)", &["0", "1", "$t1", "0x"]).on("pair"),
                call(B, "swap(uint256,uint256,address,bytes)", &["1", "0", B, "0x"]).on("pair"),
                call(B, "swap(uint256,uint256,address,bytes)", &["0", "1", B, "0x01"]).on("pair"),
                send(B, "transfer(address,uint256)", &["$pair", "10000000000000000000"]).on("t0"),
                call(B, "swap(uint256,uint256,address,bytes)", &["0", "39486321375882451955", B, "0x"]).on("pair"),
                send(B, "swap(uint256,uint256,address,bytes)", &["0", "39486321375882451955", B, "0x"]).on("pair"),
                send(B, "swap(uint256,uint256,address,bytes)", &["0", "39486321375882451954", B, "0x"]).on("pair"),
                call(A, "getReserves()", &[]).on("pair"),
                call(A, "price0CumulativeLast()", &[]).on("pair"),
                send(A, "transfer(address,uint256)", &["$pair", "100000000000000000000"]).on("t1"),
                send(A, "swap(uint256,uint256,address,bytes)", &["20000000000000000000", "0", A, "0x"]).on("pair"),
                send(B, "transfer(address,uint256)", &["$pair", "40000000000000000000"]).on("t0"),
                send(B, "swap(uint256,uint256,address,bytes)", &["1000000000000000000", "100000000000000000000", B, "0x"]).on("pair"),
                call(A, "getReserves()", &[]).on("pair"),
                call(A, "price0CumulativeLast()", &[]).on("pair"),
                call(A, "price1CumulativeLast()", &[]).on("pair"),
                send(A, "approve(address,uint256)", &[B, "100000000000000000000"]).on("pair"),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "30000000000000000000"]).on("pair"),
                call(A, "allowance(address,address)", &[A, B]).on("pair"),
                call(B, "transferFrom(address,address,uint256)", &[A, B, "100000000000000000000"]).on("pair"),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "100000000000000000000"]).on("pair"),
                send(A, "approve(address,uint256)", &[B, MAX]).on("pair"),
                send(B, "transferFrom(address,address,uint256)", &[A, B, "1000000000000000000"]).on("pair"),
                call(A, "allowance(address,address)", &[A, B]).on("pair"),
                send(A, "transfer(address,uint256)", &[B, "1000000000000000000"]).on("pair"),
                call(A, "nonces(address)", &[A]).on("pair"),
                send(B, "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", &[A, B, "5000000000000000000", "1099511627776"]).on("pair").signed(PERMIT, &[A, B, "5000000000000000000", "0", "1099511627776"], KEY_A),
                call(A, "nonces(address)", &[A]).on("pair"),
                call(A, "allowance(address,address)", &[A, B]).on("pair"),
                call(B, "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", &[A, B, "5000000000000000000", "1099511627776"]).on("pair").signed(PERMIT, &[A, B, "5000000000000000000", "0", "1099511627776"], KEY_A),
                call(B, "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", &[A, B, "5000000000000000000", "1"]).on("pair").signed(PERMIT, &[A, B, "5000000000000000000", "1", "1"], KEY_A),
                call(B, "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", &[A, B, "5000000000000000000", "1099511627776"]).on("pair").signed(PERMIT, &[A, B, "5000000000000000000", "1", "1099511627776"], KEY_B),
                send(B, "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", &[A, B, "5000000000000000000", "1099511627776"]).on("pair").signed(PERMIT, &[A, B, "5000000000000000000", "1", "1099511627776"], KEY_B),
                send(A, "transfer(address,uint256)", &["$pair", "100000000000000000000"]).on("pair"),
                send(A, "burn(address)", &[A]).on("pair"),
                call(A, "burn(address)", &[A]).on("pair"),
                send(A, "burn(address)", &[A]).on("pair"),
                call(A, "getReserves()", &[]).on("pair"),
                send(A, "transfer(address,uint256)", &["$pair", "5000000000000000000"]).on("t0"),
                send(B, "skim(address)", &[B]).on("pair"),
                send(A, "transfer(address,uint256)", &["$pair", "3000000000000000000"]).on("t1"),
                send(B, "sync()", &[]).on("pair"),
                call(A, "getReserves()", &[]).on("pair"),
                call(B, "setFeeTo(address)", &[B]).on("factory"),
                send(B, "setFeeTo(address)", &[B]).on("factory"),
                send(A, "setFeeTo(address)", &[B]).on("factory"),
                call(A, "feeTo()", &[]).on("factory"),
                send(A, "transfer(address,uint256)", &["$pair", "100000000000000000000"]).on("t0"),
                send(A, "transfer(address,uint256)", &["$pair", "400000000000000000000"]).on("t1"),
                send(A, "mint(address)", &[A]).on("pair"),
                call(A, "kLast()", &[]).on("pair"),
                send(B, "transfer(address,uint256)", &["$pair", "200000000000000000000"]).on("t1"),
                send(B, "swap(uint256,uint256,address,bytes)", &["40000000000000000000", "0", B, "0x"]).on("pair"),
                send(A, "transfer(address,uint256)", &["$pair", "10000000000000000000"]).on("t0"),
                send(A, "transfer(address,uint256)", &["$pair", "40000000000000000000"]).on("t1"),
                send(A, "mint(address)", &[A]).on("pair"),
                call(A, "balanceOf(address)", &[B]).on("pair"),
                call(A, "kLast()", &[]).on("pair"),
                send(A, "setFeeTo(address)", &[ZERO]).on("factory"),
                send(A, "transfer(address,uint256)", &["$pair", "10000000000000000000"]).on("t0"),
                send(A, "transfer(address,uint256)", &["$pair", "40000000000000000000"]).on("t1"),
                send(A, "mint(address)", &[A]).on("pair"),
                call(A, "kLast()", &[]).on("pair"),
                call(B, "setFeeToSetter(address)", &[B]).on("factory"),
                send(B, "setFeeToSetter(address)", &[B]).on("factory"),
                send(A, "setFeeToSetter(address)", &[B]).on("factory"),
                call(A, "setFeeTo(address)", &[A]).on("factory"),
                send(A, "setFeeTo(address)", &[A]).on("factory"),
                send(B, "setFeeTo(address)", &[A]).on("factory"),
                call(A, "feeToSetter()", &[]).on("factory"),
                send(A, "pause()", &[]),
                send(A, "transfer(address,uint256)", &["$pair", "10000000000000000000"]).on("pair"),
                call(A, "burn(address)", &[A]).on("pair"),
                send(A, "burn(address)", &[A]).on("pair"),
                call(A, "skim(address)", &[A]).on("pair"),
                send(A, "skim(address)", &[A]).on("pair"),
                send(A, "unpause()", &[]),
                send(A, "burn(address)", &[A]).on("pair"),
                bind("pair2", "factory", "createPair(address,address)", &["$tkb", "$factory"]),
                send(A, "createPair(address,address)", &["$tkb", "$factory"]).on("factory"),
                bind("domain2", "pair2", "DOMAIN_SEPARATOR()", &[]),
                call(A, "allPairs(uint256)", &["1"]).on("factory"),
                call(A, "allPairsLength()", &[]).on("factory"),
                call(A, "getPair(address,address)", &["$factory", "$tkb"]).on("factory"),
                call(A, "getReserves()", &[]).on("pair2"),
                call(A, "getReserves()", &[]).on("pair"),
                call(A, "price0CumulativeLast()", &[]).on("pair"),
                call(A, "price1CumulativeLast()", &[]).on("pair"),
                call(A, "totalSupply()", &[]).on("pair"),
                call(A, "balanceOf(address)", &["$pair"]).on("t0"),
                call(A, "balanceOf(address)", &["$pair"]).on("t1"),
            ],
        ),
        suite(
            "staking",
            vec![deploy("stake", "erc20", "address", &[A]), deploy("reward", "erc20", "address", &[A]), deploy("staking", "staking", "address,address,address", &[A, "$reward", "$stake"])],
            vec![
                send(A, "mint(address,uint256)", &[A, "1000000000000000000000"]),
                send(A, "mint(address,uint256)", &[B, "1000000000000000000000"]),
                send(A, "mint(address,uint256)", &[A, "2000000000000000000000000"]).on("reward"),
                send(A, "transfer(address,uint256)", &["$staking", "700000000000000000000000"]).on("reward"),
                send(B, "notifyRewardAmount(uint256)", &["604800000000000000000000"]).on("staking"),
                send(A, "notifyRewardAmount(uint256)", &["1000000000000000000000000000000"]).on("staking"),
                send(A, "notifyRewardAmount(uint256)", &["604800000000000000000000"]).on("staking"),
                send(A, "approve(address,uint256)", &["$staking", MAX]),
                send(B, "approve(address,uint256)", &["$staking", MAX]),
                send(A, "stake(uint256)", &["0"]).on("staking"),
                send(A, "stake(uint256)", &["100000000000000000000"]).on("staking"),
                send(B, "stake(uint256)", &["300000000000000000000"]).on("staking"),
                call(A, "earned(address)", &[A]).on("staking"),
                call(A, "earned(address)", &[B]).on("staking"),
                call(A, "rewardPerToken()", &[]).on("staking"),
                send(A, "getReward()", &[]).on("staking"),
                send(A, "withdraw(uint256)", &["50000000000000000000"]).on("staking"),
                send(A, "withdraw(uint256)", &["0"]).on("staking"),
                send(A, "withdraw(uint256)", &["1000000000000000000000000000000"]).on("staking"),
                send(B, "exit()", &[]).on("staking"),
                send(B, "exit()", &[]).on("staking"),
                send(A, "setRewardsDuration(uint256)", &["100"]).on("staking"),
                call(A, "earned(address)", &[A]).on("staking"),
                call(A, "lastTimeRewardApplicable()", &[]).on("staking"),
                send(A, "getReward()", &[]).on("staking"),
                send(B, "setRewardsDuration(uint256)", &["86400"]).on("staking"),
                send(A, "setRewardsDuration(uint256)", &["86400"]).on("staking"),
                send(A, "notifyRewardAmount(uint256)", &["1000000000000000000000"]).on("staking"),
                call(A, "getRewardForDuration()", &[]).on("staking"),
                call(A, "rewardRate()", &[]).on("staking"),
                call(A, "totalSupply()", &[]).on("staking"),
                call(A, "balanceOf(address)", &["$staking"]),
                call(A, "balanceOf(address)", &[A]).on("reward"),
                call(A, "balanceOf(address)", &[B]).on("reward"),
                call(A, "rewardsToken()", &[]).on("staking"),
            ],
        ),
    ]
}

#[test]
fn bench_gas() {
    let all = ["LITHE_BENCH_OUT", "LITHE_BENCH_GAS"]
        .iter()
        .any(|v| std::env::var_os(v).is_some());
    let rows: Vec<String> = suites()
        .iter()
        .filter(|s| all || SMOKE.contains(&s.name))
        .map(|s| {
            let r = replay(s);
            let name = s.name;
            assert!(r.runtime_bytes > 0 && r.gas > 0, "{name}");
            format!(
                "  \"{name}\": {{\"runtime_bytes\": {}, \"deploy_gas\": {}, \"gas\": {}, \"outcomes\": [{}]}}",
                r.runtime_bytes, r.deploy_gas, r.gas, r.outcomes.join(",")
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
    let ((), cold_set) = metered(one, at, || charge(0x55, &[one, zero], &storage, at));
    let ((), warm) = metered(one, at, || {
        charge(0x54, &[zero], &storage, at);
        charge(0x54, &[zero], &storage, at);
    });
    assert_eq!((cold_set, warm), (2_100 + 20_000, 2_100 + 100));
    assert!(!metering());
}
