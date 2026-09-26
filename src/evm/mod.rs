use std::collections::HashMap;

use crate::compile;
use crate::keccak::{keccak256, selector};
use crate::word::Word;

#[derive(Clone, Debug)]
enum Ev {
    SStore,
    Call { to: Word, value: Word },
    Static,
    Log { topics: Vec<Word> },
}

/// A stand-in external contract: its return data for some calldata, or its revert data.
type Mock = fn(&[u8]) -> Result<Vec<u8>, Vec<u8>>;

thread_local! {
    /// External contracts the interpreter can call, by address. Other addresses succeed
    /// with no return data.
    static MOCKS: std::cell::RefCell<HashMap<Word, Mock>> = std::cell::RefCell::new(HashMap::new());
    /// Hides the running code's own size and hash, which differ between builds.
    static OPAQUE_CODE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Whether the running code is creation code: its account has no code yet.
    static CONSTRUCTING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Contracts created while running, by address: their code and their own storage.
    static DEPLOYED: std::cell::RefCell<HashMap<Word, (Vec<u8>, HashMap<Word, Word>)>> =
        std::cell::RefCell::new(HashMap::new());
    static NONCE: std::cell::Cell<u64> = const { std::cell::Cell::new(1) };
    /// The block number `NUMBER` answers, for tests of a history by block.
    static BLOCK: std::cell::Cell<u64> = const { std::cell::Cell::new(100) };
    /// The code of the account each enclosing `delegatecall` into a created contract runs
    /// in, innermost last. That code, not the running code, is what the account's size,
    /// hash, and calls to itself see.
    /// A call or creation into another account pushes `None`: that account runs its own code.
    static ACCOUNT_CODE: std::cell::RefCell<Vec<Option<Vec<u8>>>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// The code of the account running `code`: its own, unless it runs by `delegatecall`.
fn account_code(code: &[u8]) -> Vec<u8> {
    ACCOUNT_CODE.with(|a| a.borrow().last().cloned().flatten().unwrap_or_else(|| code.to_vec()))
}

/// Runs `f` as another account, which runs its own code.
fn elsewhere<T>(f: impl FnOnce() -> T) -> T {
    ACCOUNT_CODE.with(|a| a.borrow_mut().push(None));
    let out = f();
    ACCOUNT_CODE.with(|a| a.borrow_mut().pop());
    out
}

/// Where `CREATE` puts a contract: from the creator and a running count, standing in for
/// the account nonce. `CREATE2` uses the real rule: `keccak(0xff . creator . salt . keccak(code))`.
fn created_address(creator: Word, salt: Option<Word>, init: &[u8]) -> Word {
    let hash = match salt {
        Some(salt) => {
            let mut buf = vec![0xff];
            buf.extend_from_slice(&creator.to_be_bytes()[12..]);
            buf.extend_from_slice(&salt.to_be_bytes());
            buf.extend_from_slice(&crate::keccak::keccak256(init));
            crate::keccak::keccak256(&buf)
        }
        None => {
            let nonce = NONCE.get();
            NONCE.set(nonce + 1);
            let mut buf = creator.to_be_bytes().to_vec();
            buf.extend_from_slice(&Word::from_u64(nonce).to_be_bytes());
            crate::keccak::keccak256(&buf)
        }
    };
    let mut word = [0u8; 32];
    word[12..].copy_from_slice(&hash[12..]);
    Word::from_be_bytes(word)
}

/// The mocks the continuation tests and the differential runs share:
/// `0xcd` returns its arguments; `0x2` returns them ABI-encoded as `bytes`;
/// `0x1` returns one byte, which is never a valid result; `0xee` reverts with its
/// arguments as the revert data, and `0xef` with none. Queries reach the mocks away
/// from the precompiles.
fn install_mocks() {
    fn echo(input: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
        Ok(input.get(4..).unwrap_or_default().to_vec())
    }
    fn refuse(input: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
        Err(input.get(4..).unwrap_or_default().to_vec())
    }
    fn silent(_: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
        Err(Vec::new())
    }
    fn as_bytes(input: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
        let data = input.get(4..).unwrap_or_default();
        let mut out = Word::from_u64(32).to_be_bytes().to_vec();
        out.extend(Word::from_u64(data.len() as u64).to_be_bytes());
        out.extend(data);
        out.resize(64 + data.len().div_ceil(32) * 32, 0);
        Ok(out)
    }
    fn malformed(_: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
        Ok(vec![1])
    }
    fn quiet(_: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
        Ok(Vec::new())
    }
    MOCKS.with(|m| {
        let mut m = m.borrow_mut();
        m.insert(Word::from_u64(0xcd), echo as Mock);
        m.insert(Word::from_u64(2), as_bytes as Mock);
        m.insert(Word::from_u64(1), malformed as Mock);
        m.insert(Word::from_u64(0xee), refuse as Mock);
        m.insert(Word::from_u64(0xef), silent as Mock);
        m.insert(Word::from_u64(0xce), quiet as Mock);
    });
}

struct Outcome {
    storage: HashMap<Word, Word>,
    balances: HashMap<Word, Word>,
    reverted: bool,
    returndata: Vec<u8>,
    trace: Vec<Ev>,
    transient: HashMap<Word, Word>,
    /// Every external effect with its payload, for comparing two builds of one program.
    detail: Vec<String>,
    /// The account's balance when the call ended.
    self_balance: Word,
}

/// Deploys as account 1, one of the callers the differential tests use, so a contract
/// that makes its deployer the owner can be exercised as that owner.
fn deploy(init: &[u8]) -> Result<Vec<u8>, String> {
    let out = construct(init, Word::from_u64(1), Word::from_u64(0))?;
    if out.reverted {
        return Err(format!("init reverted: {}", pretty(&out.returndata)));
    }
    if out.returndata.is_empty() {
        return Err("init returned no code".into());
    }
    Ok(out.returndata)
}

/// Runs creation code, with any arguments already appended, as `caller` sending `value`.
fn construct(init: &[u8], caller: Word, value: Word) -> Result<Outcome, String> {
    let was = CONSTRUCTING.replace(true);
    let out = exec(init, &[], HashMap::new(), caller, value, value);
    CONSTRUCTING.set(was);
    out
}

fn exec(
    code: &[u8],
    calldata: &[u8],
    storage: HashMap<Word, Word>,
    caller: Word,
    value: Word,
    balance: Word,
) -> Result<Outcome, String> {
    exec_state(
        code,
        calldata,
        storage,
        caller,
        value,
        balance,
        HashMap::new(),
    )
}

fn exec_state(
    code: &[u8],
    calldata: &[u8],
    storage: HashMap<Word, Word>,
    caller: Word,
    value: Word,
    balance: Word,
    mut transient: HashMap<Word, Word>,
) -> Result<Outcome, String> {
    let snap_storage = storage.clone();
    let snap_transient = transient.clone();
    let mut balances = HashMap::new();
    let mut mem = Vec::new();
    let mut stack: Vec<Word> = Vec::new();
    let mut pc = 0usize;
    let mut reverted = false;
    let mut returndata = Vec::new();
    let mut trace = Vec::new();
    let mut detail: Vec<String> = Vec::new();
    let mut stopped = false;
    let self_addr = Word::from_u64(0x1000);
    let mut self_balance = balance;
    let storage0 = storage;
    let mut storage = storage0;
    for _ in 0..200_000 {
        if pc >= code.len() {
            stopped = true;
            break;
        }
        let op = code[pc];
        if (0x60..=0x7f).contains(&op) {
            let n = (op - 0x5f) as usize;
            if pc + 1 + n > code.len() {
                return Err("truncated push".into());
            }
            let mut b = [0u8; 32];
            b[32 - n..].copy_from_slice(&code[pc + 1..pc + 1 + n]);
            stack.push(Word::from_be_bytes(b));
            pc += 1 + n;
            continue;
        }
        pc += 1;
        let pop = |stack: &mut Vec<Word>| stack.pop().ok_or_else(|| "stack underflow".to_string());
        match op {
            0x00 => {
                stopped = true;
                break;
            }
            0x5f => stack.push(Word::from_u64(0)),
            0x20 => {
                let off = word_usize(pop(&mut stack)?)?;
                let len = word_usize(pop(&mut stack)?)?;
                if mem.len() < off.saturating_add(len) {
                    mem.resize(off + len, 0);
                }
                let hash = crate::keccak::keccak256(&mem[off..off + len]);
                stack.push(Word::from_be_bytes(hash));
            }
            0x01 => {
                let a = pop(&mut stack)?;
                let b = pop(&mut stack)?;
                stack.push(a.wrapping_add(b));
            }
            0x02 => {
                let a = pop(&mut stack)?;
                let b = pop(&mut stack)?;
                stack.push(a.wrapping_mul(b));
            }
            0x03 => {
                let a = pop(&mut stack)?;
                let b = pop(&mut stack)?;
                stack.push(a.wrapping_sub(b));
            }
            0x04 | 0x05 | 0x06 | 0x07 => {
                let a = pop(&mut stack)?;
                let b = pop(&mut stack)?;
                let q = match op {
                    0x05 => a.sdiv(b),
                    0x06 => a.rem(b),
                    0x07 => a.smod(b),
                    _ => a.div(b),
                };
                stack.push(q);
            }
            0x08 | 0x09 => {
                let a = pop(&mut stack)?;
                let b = pop(&mut stack)?;
                let m = pop(&mut stack)?;
                let zero = Word::from_u64(0);
                stack.push(if m == zero {
                    zero
                } else if op == 0x08 {
                    crate::hash::addmod(a.rem(m), b.rem(m), m)
                } else {
                    crate::hash::mulmod(a.rem(m), b.rem(m), m)
                });
            }
            0x0b => {
                let k = pop(&mut stack)?;
                let v = pop(&mut stack)?;
                let byte = if k.0[1] | k.0[2] | k.0[3] != 0 || k.0[0] > 31 {
                    31
                } else {
                    k.0[0] as u32
                };
                stack.push(v.sign_extend(byte));
            }
            0x10 | 0x11 | 0x12 | 0x13 => {
                let a = pop(&mut stack)?;
                let b = pop(&mut stack)?;
                let bit = match op {
                    0x10 => a.lt(b),
                    0x11 => b.lt(a),
                    0x12 => a.slt(b),
                    _ => b.slt(a),
                };
                stack.push(Word::from_u64(u64::from(bit)));
            }
            0x14 => {
                let a = pop(&mut stack)?;
                let b = pop(&mut stack)?;
                stack.push(Word::from_u64(u64::from(a == b)));
            }
            0x15 => {
                let a = pop(&mut stack)?;
                stack.push(Word::from_u64(u64::from(a.is_zero())));
            }
            0x16 => {
                let a = pop(&mut stack)?;
                let b = pop(&mut stack)?;
                stack.push(a.bitand(b));
            }
            0x17 => {
                let a = pop(&mut stack)?;
                let b = pop(&mut stack)?;
                stack.push(a.bitor(b));
            }
            0x18 => {
                let a = pop(&mut stack)?;
                let b = pop(&mut stack)?;
                stack.push(a.bitxor(b));
            }
            0x19 => {
                let a = pop(&mut stack)?;
                stack.push(a.not());
            }
            0x1a => {
                let i = pop(&mut stack)?;
                let x = pop(&mut stack)?;
                let small = i.0[1] | i.0[2] | i.0[3] == 0 && i.0[0] < 32;
                let b = if small { x.to_be_bytes()[i.0[0] as usize] } else { 0 };
                stack.push(Word::from_u64(u64::from(b)));
            }
            0x1b | 0x1c | 0x1d => {
                let sh = pop(&mut stack)?;
                let v = pop(&mut stack)?;
                let n = if sh.0[1] | sh.0[2] | sh.0[3] != 0 || sh.0[0] >= 256 {
                    256
                } else {
                    sh.0[0] as u32
                };
                stack.push(match op {
                    0x1b => v.shl(n),
                    0x1d => v.sar(n),
                    _ => v.shr(n),
                });
            }
            0x30 => stack.push(self_addr),
            0x31 => {
                let addr = pop(&mut stack)?;
                let bal = if addr == self_addr {
                    self_balance
                } else {
                    balances
                        .get(&addr)
                        .copied()
                        .unwrap_or_else(|| Word::from_u64(0))
                };
                stack.push(bal);
            }
            0x32 => stack.push(Word::from_u64(0x0a)),
            0x33 => stack.push(caller),
            0x34 => stack.push(value),
            0x35 => {
                let off = word_usize(pop(&mut stack)?)?;
                stack.push(load_bytes(calldata, off));
            }
            0x36 => stack.push(Word::from_u64(calldata.len() as u64)),
            0x37 => {
                let dest = word_usize(pop(&mut stack)?)?;
                let off = word_usize(pop(&mut stack)?)?;
                let len = word_usize(pop(&mut stack)?)?;
                let data = slice_pad(calldata, off, len);
                write_mem(&mut mem, dest, &data);
            }
            0x3a => stack.push(Word::from_u64(1_000_000_000)),
            0x3b => {
                let addr = pop(&mut stack)?;
                let size = if addr == self_addr {
                    if CONSTRUCTING.get() {
                        0
                    } else if OPAQUE_CODE.get() {
                        1
                    } else {
                        account_code(code).len() as u64
                    }
                } else if MOCKS.with(|m| m.borrow().contains_key(&addr)) {
                    // A mock stands in for a contract.
                    1
                } else {
                    DEPLOYED.with(|d| d.borrow().get(&addr).map_or(0, |(c, _)| c.len() as u64))
                };
                stack.push(Word::from_u64(size));
            }
            0x3f => {
                let addr = pop(&mut stack)?;
                if addr == self_addr && OPAQUE_CODE.get() {
                    stack.push(Word::from_u64(1));
                } else if addr == self_addr {
                    stack.push(Word::from_be_bytes(crate::keccak::keccak256(
                        &account_code(code),
                    )));
                } else {
                    stack.push(Word::from_u64(0));
                }
            }
            0x40 => {
                let n = pop(&mut stack)?;
                let block = Word::from_u64(100);
                let recent = n.lt(block) && block.wrapping_sub(n).lt(Word::from_u64(257));
                if recent {
                    stack.push(Word::from_be_bytes(crate::keccak::keccak256(
                        &n.to_be_bytes(),
                    )));
                } else {
                    stack.push(Word::from_u64(0));
                }
            }
            0x41 => stack.push(Word::from_u64(0x0b)),
            0x38 => stack.push(Word::from_u64(code.len() as u64)),
            0x39 => {
                let dest = word_usize(pop(&mut stack)?)?;
                let off = word_usize(pop(&mut stack)?)?;
                let len = word_usize(pop(&mut stack)?)?;
                let data = slice_pad(code, off, len);
                write_mem(&mut mem, dest, &data);
            }
            0x3d => stack.push(Word::from_u64(returndata.len() as u64)),
            0x3e => {
                let dest = word_usize(pop(&mut stack)?)?;
                let off = word_usize(pop(&mut stack)?)?;
                let len = word_usize(pop(&mut stack)?)?;
                // The EVM halts on a copy past the end; generated code must check first.
                if off
                    .checked_add(len)
                    .is_none_or(|end| end > returndata.len())
                {
                    return Err(format!(
                        "returndata copy past the end at {}: {off}+{len} > {}",
                        pc - 1,
                        returndata.len()
                    ));
                }
                let data = slice_pad(&returndata, off, len);
                write_mem(&mut mem, dest, &data);
            }
            0x42 => stack.push(Word::from_u64(1_700_000_000)),
            0x43 => stack.push(Word::from_u64(BLOCK.with(|b| b.get()))),
            0x44 => stack.push(Word::from_u64(0x1234)),
            0x45 => stack.push(Word::from_u64(30_000_000)),
            0x46 => stack.push(Word::from_u64(1)),
            0x48 => stack.push(Word::from_u64(1_000_000_000)),
            0x49 => {
                let index = pop(&mut stack)?;
                if index.is_zero() {
                    stack.push(Word::from_be_bytes(crate::keccak::keccak256(b"blob")));
                } else {
                    stack.push(Word::from_u64(0));
                }
            }
            0x47 => stack.push(self_balance),
            0x50 => {
                pop(&mut stack)?;
            }
            0x51 => {
                let off = word_usize(pop(&mut stack)?)?;
                stack.push(read_word(&mut mem, off));
            }
            0x52 => {
                let off = word_usize(pop(&mut stack)?)?;
                let val = pop(&mut stack)?;
                write_mem(&mut mem, off, &val.to_be_bytes());
            }
            0x53 => {
                let off = word_usize(pop(&mut stack)?)?;
                let val = pop(&mut stack)?;
                write_mem(&mut mem, off, &val.to_be_bytes()[31..]);
            }
            0x54 => {
                let slot = pop(&mut stack)?;
                stack.push(
                    storage
                        .get(&slot)
                        .copied()
                        .unwrap_or_else(|| Word::from_u64(0)),
                );
            }
            0x55 => {
                let slot = pop(&mut stack)?;
                let val = pop(&mut stack)?;
                trace.push(Ev::SStore);
                storage.insert(slot, val);
            }
            0x5c => {
                let slot = pop(&mut stack)?;
                stack.push(
                    transient
                        .get(&slot)
                        .copied()
                        .unwrap_or_else(|| Word::from_u64(0)),
                );
            }
            0x5d => {
                let slot = pop(&mut stack)?;
                let val = pop(&mut stack)?;
                transient.insert(slot, val);
            }
            0x56 => {
                let dest = word_usize(pop(&mut stack)?)?;
                need_dest(code, dest)?;
                pc = dest;
            }
            0x57 => {
                let dest = word_usize(pop(&mut stack)?)?;
                let cond = pop(&mut stack)?;
                if !cond.is_zero() {
                    need_dest(code, dest)?;
                    pc = dest;
                }
            }
            0x59 => stack.push(Word::from_u64(mem.len().div_ceil(32) as u64 * 32)),
            0x5a => stack.push(Word::from_u64(1_000_000)),
            0x5b => {}
            0x5e => {
                let dest = word_usize(pop(&mut stack)?)?;
                let src = word_usize(pop(&mut stack)?)?;
                let len = word_usize(pop(&mut stack)?)?;
                let data = read_slice(&mut mem, src, len);
                write_mem(&mut mem, dest, &data);
            }
            0x80..=0x8f => {
                let n = (op - 0x7f) as usize;
                if stack.len() < n {
                    return Err("dup underflow".into());
                }
                let v = stack[stack.len() - n];
                stack.push(v);
            }
            0x90..=0x9f => {
                let n = (op - 0x8f) as usize;
                let len = stack.len();
                if len <= n {
                    return Err("swap underflow".into());
                }
                stack.swap(len - 1, len - 1 - n);
            }
            0xf0 | 0xf5 => {
                let val = pop(&mut stack)?;
                let off = word_usize(pop(&mut stack)?)?;
                let size = word_usize(pop(&mut stack)?)?;
                let salt = if op == 0xf5 {
                    Some(pop(&mut stack)?)
                } else {
                    None
                };
                let init = read_slice(&mut mem, off, size);
                if self_balance.lt(val) {
                    returndata.clear();
                    stack.push(Word::from_u64(0));
                    continue;
                }
                let was = CONSTRUCTING.replace(true);
                let born = elsewhere(|| {
                    exec_state(
                        &init,
                        &[],
                        HashMap::new(),
                        self_addr,
                        val,
                        val,
                        HashMap::new(),
                    )
                });
                CONSTRUCTING.set(was);
                let born = born?;
                if born.reverted {
                    returndata = born.returndata;
                    stack.push(Word::from_u64(0));
                    continue;
                }
                let at = created_address(self_addr, salt, &init);
                DEPLOYED.with(|d| d.borrow_mut().insert(at, (born.returndata, born.storage)));
                self_balance = self_balance.wrapping_sub(val);
                trace.push(Ev::Call { to: at, value: val });
                returndata.clear();
                stack.push(at);
            }
            0xf1 => {
                let _gas = pop(&mut stack)?;
                let to = pop(&mut stack)?;
                let val = pop(&mut stack)?;
                let in_off = word_usize(pop(&mut stack)?)?;
                let in_size = word_usize(pop(&mut stack)?)?;
                let ret_off = word_usize(pop(&mut stack)?)?;
                let ret_size = word_usize(pop(&mut stack)?)?;
                detail.push(format!(
                    "call {to:?} {val:?} {}",
                    hex(&read_slice(&mut mem, in_off, in_size))
                ));
                if self_balance.lt(val) {
                    stack.push(Word::from_u64(0));
                } else if let Some((child, child_storage)) =
                    DEPLOYED.with(|d| d.borrow().get(&to).cloned())
                {
                    // A contract this run created runs its own code on its own storage.
                    let input = read_slice(&mut mem, in_off, in_size);
                    let nested = elsewhere(|| {
                        exec_state(
                            &child,
                            &input,
                            child_storage,
                            self_addr,
                            val,
                            Word::from_u64(0),
                            transient.clone(),
                        )
                    })?;
                    trace.push(Ev::Call { to, value: val });
                    returndata = nested.returndata.clone();
                    if nested.reverted {
                        stack.push(Word::from_u64(0));
                    } else {
                        DEPLOYED.with(|d| {
                            if let Some(entry) = d.borrow_mut().get_mut(&to) {
                                entry.1 = nested.storage.clone();
                            }
                        });
                        self_balance = self_balance.wrapping_sub(val);
                        if ret_size > 0 {
                            let n = ret_size.min(returndata.len());
                            write_mem(&mut mem, ret_off, &returndata[..n]);
                        }
                        stack.push(Word::from_u64(1));
                    }
                } else if to == self_addr && in_size > 0 {
                    let input = read_slice(&mut mem, in_off, in_size);
                    let nested = exec_state(
                        &account_code(code),
                        &input,
                        storage.clone(),
                        self_addr,
                        val,
                        self_balance,
                        transient.clone(),
                    )?;
                    trace.push(Ev::Call { to, value: val });
                    if nested.reverted {
                        returndata = nested.returndata;
                        stack.push(Word::from_u64(0));
                    } else {
                        storage = nested.storage;
                        transient = nested.transient;
                        returndata = nested.returndata.clone();
                        if ret_size > 0 && !nested.returndata.is_empty() {
                            let n = ret_size.min(nested.returndata.len());
                            write_mem(&mut mem, ret_off, &nested.returndata[..n]);
                        }
                        trace.extend(nested.trace);
                        detail.extend(nested.detail);
                        stack.push(Word::from_u64(1));
                    }
                } else {
                    let input = read_slice(&mut mem, in_off, in_size);
                    let answer = MOCKS.with(|m| m.borrow().get(&to).map(|mock| mock(&input)));
                    match answer {
                        Some(Err(data)) => {
                            trace.push(Ev::Call { to, value: val });
                            returndata = data;
                            stack.push(Word::from_u64(0));
                        }
                        answer => {
                            self_balance = self_balance.wrapping_sub(val);
                            let entry = balances.entry(to).or_insert_with(|| Word::from_u64(0));
                            *entry = entry.wrapping_add(val);
                            trace.push(Ev::Call { to, value: val });
                            returndata = answer.and_then(Result::ok).unwrap_or_default();
                            if ret_size > 0 {
                                let n = ret_size.min(returndata.len());
                                write_mem(&mut mem, ret_off, &returndata[..n]);
                            }
                            stack.push(Word::from_u64(1));
                        }
                    }
                }
            }
            0xfa => {
                let _gas = pop(&mut stack)?;
                let to = pop(&mut stack)?;
                let in_off = word_usize(pop(&mut stack)?)?;
                let in_size = word_usize(pop(&mut stack)?)?;
                let ret_off = word_usize(pop(&mut stack)?)?;
                let ret_size = word_usize(pop(&mut stack)?)?;
                let input = read_slice(&mut mem, in_off, in_size);
                detail.push(format!("static {to:?} {}", hex(&input)));
                if let Some((child, child_storage)) =
                    DEPLOYED.with(|d| d.borrow().get(&to).cloned())
                {
                    let nested = elsewhere(|| {
                        exec_state(
                            &child,
                            &input,
                            child_storage,
                            self_addr,
                            Word::from_u64(0),
                            Word::from_u64(0),
                            transient.clone(),
                        )
                    })?;
                    returndata = nested.returndata;
                    if ret_size > 0 {
                        let n = ret_size.min(returndata.len());
                        write_mem(&mut mem, ret_off, &returndata[..n]);
                    }
                    trace.push(Ev::Static);
                    stack.push(Word::from_u64(u64::from(!nested.reverted)));
                    continue;
                }
                if to == self_addr && in_size > 0 {
                    // A read-only call back into this contract sees its storage as it is now.
                    let nested = exec_state(
                        &account_code(code),
                        &input,
                        storage.clone(),
                        self_addr,
                        Word::from_u64(0),
                        self_balance,
                        transient.clone(),
                    )?;
                    let wrote = nested
                        .trace
                        .iter()
                        .any(|ev| matches!(ev, Ev::SStore));
                    returndata = nested.returndata;
                    if ret_size > 0 {
                        let n = ret_size.min(returndata.len());
                        write_mem(&mut mem, ret_off, &returndata[..n]);
                    }
                    trace.push(Ev::Static);
                    stack.push(Word::from_u64(u64::from(!nested.reverted && !wrote)));
                    continue;
                }
                let precompiled = to.0[1] | to.0[2] | to.0[3] == 0 && (1..=3).contains(&to.0[0]);
                let mocked = if precompiled {
                    None
                } else {
                    MOCKS.with(|m| m.borrow().get(&to).map(|mock| mock(&input)))
                };
                if let Some(answer) = mocked {
                    let ok = answer.is_ok();
                    returndata = answer.unwrap_or_else(|data| data);
                    if ok && ret_size > 0 {
                        let n = ret_size.min(returndata.len());
                        write_mem(&mut mem, ret_off, &returndata[..n]);
                    }
                    trace.push(Ev::Static);
                    stack.push(Word::from_u64(u64::from(ok)));
                    continue;
                }
                let precompile = if to == Word::from_u64(1) && in_size == 128 {
                    crate::hash::ecrecover(&input).unwrap_or_else(|| Word::from_u64(0))
                } else if to == Word::from_u64(2) {
                    Word::from_be_bytes(crate::hash::sha256(&input))
                } else if to == Word::from_u64(3) {
                    let digest = crate::hash::ripemd160(&input);
                    let mut word = [0u8; 32];
                    word[12..].copy_from_slice(&digest);
                    Word::from_be_bytes(word)
                } else if to == Word::from_u64(1) {
                    Word::from_u64(7)
                } else {
                    returndata.clear();
                    stack.push(Word::from_u64(0));
                    continue;
                };
                let word = precompile.to_be_bytes();
                returndata = word.to_vec();
                if ret_size > 0 {
                    let n = ret_size.min(32);
                    write_mem(&mut mem, ret_off, &word[..n]);
                }
                trace.push(Ev::Static);
                stack.push(Word::from_u64(1));
            }
            0xf4 => {
                let _gas = pop(&mut stack)?;
                let to = pop(&mut stack)?;
                let in_off = word_usize(pop(&mut stack)?)?;
                let in_size = word_usize(pop(&mut stack)?)?;
                let ret_off = word_usize(pop(&mut stack)?)?;
                let ret_size = word_usize(pop(&mut stack)?)?;
                if let Some((child, _)) = DEPLOYED.with(|d| d.borrow().get(&to).cloned()) {
                    // A created contract's code runs in this account: its storage, balance,
                    // and transient storage. A router reaching its parts is not an effect.
                    let input = read_slice(&mut mem, in_off, in_size);
                    let account = account_code(code);
                    ACCOUNT_CODE.with(|a| a.borrow_mut().push(Some(account)));
                    let nested = exec_state(
                        &child,
                        &input,
                        storage.clone(),
                        caller,
                        value,
                        self_balance,
                        transient.clone(),
                    );
                    ACCOUNT_CODE.with(|a| a.borrow_mut().pop());
                    let nested = nested?;
                    returndata = nested.returndata.clone();
                    // Effects are recorded as they happen, reverted or not, as in one frame.
                    trace.extend(nested.trace);
                    detail.extend(nested.detail);
                    if nested.reverted {
                        stack.push(Word::from_u64(0));
                    } else {
                        storage = nested.storage;
                        transient = nested.transient;
                        self_balance = nested.self_balance;
                        for (to, sent) in nested.balances {
                            let entry = balances.entry(to).or_insert_with(|| Word::from_u64(0));
                            *entry = entry.wrapping_add(sent);
                        }
                        if ret_size > 0 {
                            let n = ret_size.min(returndata.len());
                            write_mem(&mut mem, ret_off, &returndata[..n]);
                        }
                        stack.push(Word::from_u64(1));
                    }
                    continue;
                }
                detail.push(format!(
                    "delegate {to:?} {}",
                    hex(&read_slice(&mut mem, in_off, in_size))
                ));
                if to != self_addr {
                    stack.push(Word::from_u64(0));
                } else {
                    let input = read_slice(&mut mem, in_off, in_size);
                    let nested = exec_state(
                        &account_code(code),
                        &input,
                        storage.clone(),
                        caller,
                        value,
                        self_balance,
                        transient.clone(),
                    )?;
                    if nested.reverted {
                        returndata = nested.returndata;
                        reverted = true;
                        stopped = true;
                        break;
                    }
                    storage = nested.storage;
                    transient = nested.transient;
                    stack.push(Word::from_u64(1));
                }
            }
            0xa1 | 0xa2 | 0xa3 | 0xa4 => {
                let n = (op - 0xa0) as usize;
                let off = word_usize(pop(&mut stack)?)?;
                let size = word_usize(pop(&mut stack)?)?;
                let mut topics = Vec::with_capacity(n);
                for _ in 0..n {
                    topics.push(pop(&mut stack)?);
                }
                detail.push(format!(
                    "log {topics:?} {}",
                    hex(&read_slice(&mut mem, off, size))
                ));
                trace.push(Ev::Log { topics });
            }
            0xf3 | 0xfd => {
                let off = word_usize(pop(&mut stack)?)?;
                let len = word_usize(pop(&mut stack)?)?;
                returndata = read_slice(&mut mem, off, len);
                reverted = op == 0xfd;
                stopped = true;
                break;
            }
            other => return Err(format!("opcode {other:#x} at {}", pc - 1)),
        }
        if stack.len() > 1024 {
            return Err("stack too deep".into());
        }
    }
    if !stopped {
        return Err("step limit".into());
    }
    if reverted {
        storage = snap_storage;
        transient = snap_transient;
        balances.clear();
        self_balance = balance;
    }
    Ok(Outcome {
        storage,
        balances,
        reverted,
        returndata,
        trace,
        transient,
        detail,
        self_balance,
    })
}

fn need_dest(code: &[u8], dest: usize) -> Result<(), String> {
    if code.get(dest) == Some(&0x5b) {
        Ok(())
    } else {
        Err(format!("jump to {dest} is not a jumpdest"))
    }
}

fn word_usize(w: Word) -> Result<usize, String> {
    if w.0[1] | w.0[2] | w.0[3] != 0 {
        return Err("offset too large".into());
    }
    Ok(w.0[0] as usize)
}

fn load_bytes(src: &[u8], off: usize) -> Word {
    let mut b = [0u8; 32];
    for i in 0..32 {
        if let Some(byte) = src.get(off + i) {
            b[i] = *byte;
        }
    }
    Word::from_be_bytes(b)
}

fn slice_pad(src: &[u8], off: usize, len: usize) -> Vec<u8> {
    let mut out = vec![0u8; len];
    for i in 0..len {
        if let Some(b) = src.get(off + i) {
            out[i] = *b;
        }
    }
    out
}

fn expand(mem: &mut Vec<u8>, end: usize) {
    if mem.len() < end {
        mem.resize(end, 0);
    }
}

fn read_word(mem: &mut Vec<u8>, off: usize) -> Word {
    expand(mem, off + 32);
    let mut b = [0u8; 32];
    b.copy_from_slice(&mem[off..off + 32]);
    Word::from_be_bytes(b)
}

fn read_slice(mem: &mut Vec<u8>, off: usize, len: usize) -> Vec<u8> {
    expand(mem, off + len);
    mem[off..off + len].to_vec()
}

fn write_mem(mem: &mut Vec<u8>, off: usize, data: &[u8]) {
    expand(mem, off + data.len());
    mem[off..off + data.len()].copy_from_slice(data);
}

fn word_data(sig: &str, words: &[Word]) -> Vec<u8> {
    let mut c = selector(sig).to_vec();
    for w in words {
        c.extend_from_slice(&w.to_be_bytes());
    }
    c
}

fn pretty(data: &[u8]) -> String {
    let text = String::from_utf8_lossy(data);
    format!("{text} ({})", hex(data))
}

fn hex(bytes: &[u8]) -> String {
    const H: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push(H[(b >> 4) as usize] as char);
        s.push(H[(b & 0xf) as usize] as char);
    }
    s
}

fn slot(map: &HashMap<Word, Word>, n: u64) -> Word {
    map.get(&Word::from_u64(n))
        .copied()
        .unwrap_or_else(|| Word::from_u64(0))
}

/// A program's storage leaves, so tests can name a field by leaf index whatever slot it packs into.
struct Leaves {
    keys: Vec<Word>,
    packs: Vec<crate::check::Pack>,
}

fn leaves(src: &str) -> Leaves {
    let checked = crate::check::check(crate::parse::parse(src).expect("parse")).expect("check");
    Leaves {
        keys: checked.leaf_keys,
        packs: checked.leaf_pack,
    }
}

impl Leaves {
    fn get(&self, storage: &HashMap<Word, Word>, leaf: usize) -> Word {
        let raw = storage
            .get(&self.keys[leaf])
            .copied()
            .unwrap_or_else(|| Word::from_u64(0));
        let pack = self.packs[leaf];
        if pack.is_full() {
            return raw;
        }
        let bits = u32::from(pack.width) * 8;
        let value = raw
            .shr(u32::from(pack.offset) * 8)
            .bitand(Word::from_u64(0).not().shr(256 - bits));
        if pack.signed {
            value.sign_extend(u32::from(pack.width) - 1)
        } else {
            value
        }
    }

    fn put(&self, storage: &mut HashMap<Word, Word>, leaf: usize, value: Word) {
        let pack = self.packs[leaf];
        let key = self.keys[leaf];
        if pack.is_full() {
            storage.insert(key, value);
            return;
        }
        let shift = u32::from(pack.offset) * 8;
        let mask = Word::from_u64(0).not().shr(256 - u32::from(pack.width) * 8);
        let old = storage
            .get(&key)
            .copied()
            .unwrap_or_else(|| Word::from_u64(0));
        let kept = old.bitand(mask.shl(shift).not());
        storage.insert(key, kept.bitor(value.bitand(mask).shl(shift)));
    }
}

const COUNTER: &str = include_str!("../../examples/counter.lithe");
const PAY: &str = include_str!("../../examples/pay.lithe");
const GRAB: &str = include_str!("../../examples/grab.lithe");
const TOUCH: &str = include_str!("../../examples/touch.lithe");
const GATE: &str = include_str!("../../examples/gate.lithe");
const BANK: &str = include_str!("../../examples/bank.lithe");
const DISPATCH_ERRORS: &str = include_str!("../../examples/dispatch_errors.lithe");
const BARE_STORAGE: &str = include_str!("../../examples/reject/bare_storage.lithe");
const UNDECLARED_ERROR: &str = include_str!("../../examples/reject/undeclared_error.lithe");
const ERROR_MISMATCH: &str = include_str!("../../examples/reject/error_mismatch.lithe");
const ERROR_COLLISION: &str = include_str!("../../examples/reject/error_collision.lithe");
const STRING_ERROR: &str = include_str!("../../examples/reject/string_error.lithe");
const UNTYPED_BINDING: &str = include_str!("../../examples/reject/untyped_binding.lithe");
const VIEW_WRITES: &str = include_str!("../../examples/reject/view_writes_storage.lithe");
const FUNCTION_WRITES: &str = include_str!("../../examples/reject/function_writes_storage.lithe");
const CREATE: &str = include_str!("../../examples/reject/create.lithe");
const TYPES: &str = include_str!("../../examples/types.lithe");

fn call(runtime: &[u8], sig: &str, args: &[Word]) -> Outcome {
    exec(
        runtime,
        &word_data(sig, args),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .unwrap_or_else(|err| panic!("{sig}: {err}"))
}

fn trace_kinds(trace: &[Ev]) -> Vec<&str> {
    trace
        .iter()
        .map(|e| match e {
            Ev::Static => "static",
            Ev::SStore => "sstore",
            Ev::Call { .. } => "call",
            Ev::Log { .. } => "log",
        })
        .collect()
}

fn lithe_files(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .map(|e| e.expect("read examples"))
        .map(|e| e.path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            lithe_files(&path, out);
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("lithe") {
            out.push(path);
        }
    }
}

fn abi_string_value(data: &[u8]) -> Vec<u8> {
    let len = word_usize(load_bytes(data, 32)).expect("length");
    data[64..64 + len].to_vec()
}

fn hex_decode(text: &str) -> Vec<u8> {
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).expect("hex"))
        .collect()
}

fn hex_bytes(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0xf) as usize] as char);
    }
    out
}

fn is_program(src: &str) -> bool {
    src.lines().any(|line| {
        // A module's own externals are indented; only the contract's make a program.
        line.starts_with("external ")
            || (line.trim_start().starts_with("use ") && line.contains(" exposing"))
            || line.starts_with("upgradeable")
            || line.starts_with("contract ")
            || line.starts_with("migrate ")
    })
}

fn contracts(src: &str) -> usize {
    src.lines()
        .filter(|line| line.starts_with("contract "))
        .count()
}

fn needs_deploy_args(src: &str) -> bool {
    !src.lines().any(|line| line.trim() == "upgradeable")
        && src.lines().any(|line| {
            let line = line.trim_start().trim_start_matches("payable ");
            line.starts_with("deploy(") && !line.starts_with("deploy()")
        })
}

fn route_text<'a>(tree: &'a str, name: &str) -> &'a str {
    let mut rest = tree;
    loop {
        if rest.starts_with(name) && rest.as_bytes().get(name.len()) == Some(&b'\n') {
            let body = &rest[name.len() + 1..];
            let next = body
                .lines()
                .position(|line| !line.is_empty() && !line.starts_with(' '))
                .map(|index| {
                    body.lines()
                        .take(index)
                        .map(|line| line.len() + 1)
                        .sum::<usize>()
                })
                .unwrap_or(body.len());
            return &rest[..name.len() + 1 + next];
        }
        let Some(newline) = rest.find('\n') else {
            panic!("missing route {name}\n{tree}");
        };
        rest = &rest[newline + 1..];
    }
}

fn call_raw(runtime: &[u8], data: &[u8]) -> Outcome {
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

/// One deployed contract whose storage carries from call to call, for the standard
/// library's tests.
struct Session {
    runtime: Vec<u8>,
    storage: HashMap<Word, Word>,
    last: Option<Outcome>,
}

/// An ABI argument: a static word, or `bytes` / `string` data.
enum Arg {
    W(Word),
    B(Vec<u8>),
}

fn encode_args(sig: &str, args: &[Arg]) -> Vec<u8> {
    let mut head = Vec::new();
    let mut tail = Vec::new();
    for arg in args {
        match arg {
            Arg::W(w) => head.extend_from_slice(&w.to_be_bytes()),
            Arg::B(data) => {
                let offset = 32 * args.len() + tail.len();
                head.extend_from_slice(&Word::from_u64(offset as u64).to_be_bytes());
                tail.extend_from_slice(&Word::from_u64(data.len() as u64).to_be_bytes());
                tail.extend_from_slice(data);
                tail.resize(tail.len().div_ceil(32) * 32, 0);
            }
        }
    }
    let mut out = selector(sig).to_vec();
    out.extend(head);
    out.extend(tail);
    out
}

impl Session {
    fn new(path: &str) -> Session {
        let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let init = crate::compile_file(&root.join(path)).unwrap_or_else(|e| panic!("{path}: {e}"));
        let made = construct(&init, Word::from_u64(1), Word::from_u64(0)).expect("construct");
        assert!(!made.reverted, "{path}: {}", pretty(&made.returndata));
        Session {
            runtime: made.returndata.clone(),
            storage: made.storage,
            last: None,
        }
    }

    /// Calls as `caller`, keeping storage when the call succeeds. Returns whether it did.
    fn send(&mut self, caller: u64, sig: &str, args: &[Arg]) -> bool {
        let out = exec(
            &self.runtime,
            &encode_args(sig, args),
            self.storage.clone(),
            Word::from_u64(caller),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect(sig);
        let ok = !out.reverted;
        if ok {
            self.storage = out.storage.clone();
        }
        self.last = Some(out);
        ok
    }

    fn word(&mut self, sig: &str, args: &[Arg]) -> Word {
        assert!(
            self.send(0, sig, args),
            "{sig}: {}",
            pretty(&self.returned())
        );
        load_bytes(&self.returned(), 0)
    }

    fn returned(&self) -> Vec<u8> {
        self.last
            .as_ref()
            .map(|o| o.returndata.clone())
            .unwrap_or_default()
    }

    /// Asserts the last call reverted with the error `sig`.
    fn reverted_with(&self, sig: &str) {
        let out = self.last.as_ref().expect("a call");
        assert!(out.reverted, "expected {sig}");
        assert_eq!(
            out.returndata[..4],
            selector(sig),
            "expected {sig}, got {}",
            pretty(&out.returndata)
        );
    }
}

fn keccak_word(data: &[u8]) -> Word {
    Word::from_be_bytes(crate::keccak::keccak256(data))
}

fn map_key(key: Word, slot: Word) -> Word {
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(&key.to_be_bytes());
    buf[32..].copy_from_slice(&slot.to_be_bytes());
    Word::from_be_bytes(crate::keccak::keccak256(&buf))
}

/// Runs a view or stateful call on `runtime` with `storage`, failing on a revert.
fn run_ok(runtime: &[u8], storage: &HashMap<Word, Word>, sig: &str, args: &[Word]) -> Outcome {
    let out = exec(
        runtime,
        &word_data(sig, args),
        storage.clone(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .unwrap_or_else(|err| panic!("{sig}: {err}"));
    assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
    out
}

fn read_ok(runtime: &[u8], storage: &HashMap<Word, Word>, sig: &str, args: &[Word]) -> Word {
    load_bytes(&run_ok(runtime, storage, sig, args).returndata, 0)
}

fn abi_string(sig: &str, data: &[u8]) -> Vec<u8> {
    let mut c = selector(sig).to_vec();
    c.extend_from_slice(&Word::from_u64(32).to_be_bytes());
    c.extend_from_slice(&Word::from_u64(data.len() as u64).to_be_bytes());
    c.extend_from_slice(data);
    c.resize(
        c.len() + (32 - data.len() % 32) % 32 + usize::from(data.is_empty()) * 32,
        0,
    );
    c
}

mod abi;
mod basics;
mod calls;
mod differential;
mod examples;
mod interfaces;
mod language;
mod split;
mod stdlib;
mod storage;
mod values;
