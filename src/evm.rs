use std::collections::HashMap;

use crate::compile;
use crate::keccak::{keccak256, selector};
use crate::word::Word;

#[derive(Clone, Debug)]
enum Ev {
    SStore { slot: Word, val: Word },
    Call { to: Word, value: Word },
    Static { to: Word },
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
    MOCKS.with(|m| {
        let mut m = m.borrow_mut();
        m.insert(Word::from_u64(0xcd), echo as Mock);
        m.insert(Word::from_u64(2), as_bytes as Mock);
        m.insert(Word::from_u64(1), malformed as Mock);
        m.insert(Word::from_u64(0xee), refuse as Mock);
        m.insert(Word::from_u64(0xef), silent as Mock);
    });
}

struct Outcome {
    storage: HashMap<Word, Word>,
    balances: HashMap<Word, Word>,
    reverted: bool,
    returndata: Vec<u8>,
    trace: Vec<Ev>,
    err: Option<String>,
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
            0x43 => stack.push(Word::from_u64(100)),
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
                trace.push(Ev::SStore { slot, val });
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
                    trace.push(Ev::Static { to });
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
                        .any(|ev| matches!(ev, Ev::SStore { .. }));
                    returndata = nested.returndata;
                    if ret_size > 0 {
                        let n = ret_size.min(returndata.len());
                        write_mem(&mut mem, ret_off, &returndata[..n]);
                    }
                    trace.push(Ev::Static { to });
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
                    trace.push(Ev::Static { to });
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
                trace.push(Ev::Static { to });
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
        err: None,
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

const COUNTER: &str = include_str!("../examples/counter.lithe");
const PAY: &str = include_str!("../examples/pay.lithe");
const GRAB: &str = include_str!("../examples/grab.lithe");
const TOUCH: &str = include_str!("../examples/touch.lithe");
const GATE: &str = include_str!("../examples/gate.lithe");
const BANK: &str = include_str!("../examples/bank.lithe");
const DISPATCH_ERRORS: &str = include_str!("../examples/dispatch_errors.lithe");
const BARE_STORAGE: &str = include_str!("../examples/reject/bare_storage.lithe");
const UNDECLARED_ERROR: &str = include_str!("../examples/reject/undeclared_error.lithe");
const ERROR_MISMATCH: &str = include_str!("../examples/reject/error_mismatch.lithe");
const ERROR_COLLISION: &str = include_str!("../examples/reject/error_collision.lithe");
const STRING_ERROR: &str = include_str!("../examples/reject/string_error.lithe");
const UNTYPED_BINDING: &str = include_str!("../examples/reject/untyped_binding.lithe");
const VIEW_WRITES: &str = include_str!("../examples/reject/view_writes_storage.lithe");
const FUNCTION_WRITES: &str = include_str!("../examples/reject/function_writes_storage.lithe");
const CREATE: &str = include_str!("../examples/reject/create.lithe");
const TYPES: &str = include_str!("../examples/types.lithe");
const UPGRADE: &str = include_str!("../examples/upgrade.lithe");

#[test]
fn keccak_matches_ethereum() {
    let empty = keccak256(b"");
    assert_eq!(
        hex(&empty),
        "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    );
    assert_eq!(hex(&selector("transfer(address,uint256)")), "a9059cbb");
}

#[test]
fn counter_enforces_storage_and_sender() {
    let init = compile(COUNTER).expect("compile");
    let runtime = deploy(&init).expect("deploy");
    let owner = Word::from_u64(0xab);
    let mut storage = HashMap::new();
    storage.insert(Word::from_u64(1), owner);

    let inc = exec(
        &runtime,
        &word_data("increment(uint256)", &[Word::from_u64(5)]),
        storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("inc");
    assert!(!inc.reverted, "{}", pretty(&inc.returndata));
    assert_eq!(slot(&inc.storage, 0), Word::from_u64(5));
    assert_eq!(trace_kinds(&inc.trace), ["sstore", "log"]);

    let zero = exec(
        &runtime,
        &word_data("increment(uint256)", &[Word::from_u64(0)]),
        storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("zero");
    assert!(!zero.reverted, "{}", pretty(&zero.returndata));
    assert!(zero.trace.is_empty());

    let mut full = storage.clone();
    full.insert(Word::from_u64(0), Word::from_u64(0).not());
    let overflow = exec(
        &runtime,
        &word_data("increment(uint256)", &[Word::from_u64(1)]),
        full.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("overflow");
    assert!(overflow.reverted);
    assert_eq!(slot(&overflow.storage, 0), Word::from_u64(0).not());
    assert!(overflow.returndata.starts_with(&selector("Panic(uint256)")));
    assert_eq!(load_bytes(&overflow.returndata, 4), Word::from_u64(0x11));

    let denied = exec(
        &runtime,
        &word_data("reset()", &[]),
        storage.clone(),
        Word::from_u64(0xcd),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("denied");
    assert!(denied.reverted);
    assert_eq!(denied.returndata, selector("InvalidOwnerAccess()").to_vec());
    assert_eq!(slot(&denied.storage, 0), Word::from_u64(0));

    let mut seeded = storage;
    seeded.insert(Word::from_u64(0), Word::from_u64(9));
    let reset = exec(
        &runtime,
        &word_data("reset()", &[]),
        seeded,
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("reset");
    assert!(!reset.reverted, "{}", pretty(&reset.returndata));
    assert_eq!(slot(&reset.storage, 0), Word::from_u64(0));

    let view = exec(
        &runtime,
        &word_data("get_count()", &[]),
        {
            let mut s = HashMap::new();
            s.insert(Word::from_u64(0), Word::from_u64(42));
            s
        },
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("view");
    assert!(!view.reverted, "{}", pretty(&view.returndata));
    assert_eq!(load_bytes(&view.returndata, 0), Word::from_u64(42));
    assert!(view.trace.is_empty());
}

#[test]
fn rejected_programs_name_the_rule() {
    let err = compile(BARE_STORAGE).expect_err("bare storage");
    assert!(
        err.to_string()
            .contains("storage field `paid` must be qualified as `storage.paid`"),
        "{err}"
    );
    let err = compile(VIEW_WRITES).expect_err("view");
    assert!(
        err.to_string().contains("declared effect is weaker than the body's: external view function `bad` writes storage"),
        "{err}"
    );

    let err = compile(FUNCTION_WRITES).expect_err("function");
    assert!(
        err.to_string().contains(
            "declared effect is weaker than the body's: view function `bad` writes storage"
        ),
        "{err}"
    );
    let err = crate::compile_contracts(CREATE).expect_err("create");
    assert!(
        err.to_string()
            .contains("`Vault` has no `deploy` parameters, so it takes no arguments"),
        "{err}"
    );
    let err = compile(UNDECLARED_ERROR).expect_err("undeclared");
    assert!(
        err.to_string()
            .contains("external function `go` must declare its errors"),
        "{err}"
    );
    assert!(err.to_string().contains("Not_owner"), "{err}");
    let err = compile(ERROR_MISMATCH).expect_err("mismatch");
    assert!(
        err.to_string()
            .contains("external function `go` may raise `Closed`"),
        "{err}"
    );
    assert!(err.to_string().contains("declared:"), "{err}");
    assert!(err.to_string().contains("inferred:"), "{err}");
    let err = compile(STRING_ERROR).expect_err("string");
    assert!(err.to_string().contains("errors must be typed"), "{err}");
    let err = compile(UNTYPED_BINDING).expect_err("untyped");
    assert!(
        err.to_string().contains("local bindings require a type"),
        "{err}"
    );
    let err = compile(ERROR_COLLISION).expect_err("collision");
    assert!(
        err.to_string()
            .contains("error selector `NotOwner()` collides with `NotOwner()`"),
        "{err}"
    );
}

#[test]
fn storage_is_written_before_calls() {
    let runtime = deploy(&compile(PAY).expect("compile")).expect("deploy");
    let to = Word::from_u64(2);
    let out = exec(
        &runtime,
        &word_data("pay(address)", &[to]),
        HashMap::new(),
        Word::from_u64(0xab),
        Word::from_u64(10),
        Word::from_u64(10),
    )
    .expect("pay");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(slot(&out.storage, 0), Word::from_u64(10));
    assert_eq!(out.balances.get(&to).copied(), Some(Word::from_u64(10)));
    let sstore_at = out
        .trace
        .iter()
        .position(|e| matches!(e, Ev::SStore { .. }));
    let call_at = out.trace.iter().position(|e| matches!(e, Ev::Call { .. }));
    assert!(sstore_at < call_at, "{:?}", out.trace);
}

#[test]
fn static_call_runs_before_storage_is_written() {
    let runtime = deploy(&compile(GRAB).expect("compile")).expect("deploy");
    assert!(runtime.contains(&0xfa), "missing STATICCALL");
    let to = Word::from_u64(1);
    let out = exec(
        &runtime,
        &word_data("grab(address)", &[to]),
        HashMap::new(),
        Word::from_u64(0xab),
        Word::from_u64(0),
        Word::from_u64(1),
    )
    .expect("grab");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(slot(&out.storage, 0), Word::from_u64(8));
    assert_eq!(trace_kinds(&out.trace), ["static", "sstore", "call"]);
}

#[test]
fn touch_records_time_for_the_guard() {
    let runtime = deploy(&compile(TOUCH).expect("compile")).expect("deploy");
    let guard = Word::from_u64(0xab);
    let mut storage = HashMap::new();
    storage.insert(Word::from_u64(1), guard);

    let denied = exec(
        &runtime,
        &word_data("touch()", &[]),
        storage.clone(),
        Word::from_u64(0xcd),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("denied");
    assert!(denied.reverted);
    assert_eq!(denied.returndata, selector("NotGuard()").to_vec());
    assert!(denied.storage.get(&Word::from_u64(0)).is_none());

    let touched = exec(
        &runtime,
        &word_data("touch()", &[]),
        storage.clone(),
        guard,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("touch");
    assert!(!touched.reverted, "{}", pretty(&touched.returndata));
    assert_eq!(slot(&touched.storage, 0), Word::from_u64(1_700_000_000));
    assert!(touched.trace.iter().all(|e| !matches!(e, Ev::Call { .. })));

    let next = Word::from_u64(0xcd);
    let moved = exec(
        &runtime,
        &word_data("set_guard(address)", &[next]),
        storage,
        guard,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("set guard");
    assert!(!moved.reverted, "{}", pretty(&moved.returndata));
    assert_eq!(slot(&moved.storage, 1), next);

    let view = exec(
        &runtime,
        &word_data("updated()", &[]),
        touched.storage,
        guard,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("view");
    assert_eq!(
        load_bytes(&view.returndata, 0),
        Word::from_u64(1_700_000_000)
    );
    assert!(view.trace.is_empty());
}

#[test]
fn gate_pays_out_only_when_open() {
    let layout = leaves(GATE);
    let runtime = deploy(&compile(GATE).expect("compile")).expect("deploy");
    let owner = Word::from_u64(0xab);
    let to = Word::from_u64(2);
    let mut storage = HashMap::new();
    layout.put(&mut storage, 1, owner);

    let closed = exec(
        &runtime,
        &word_data("withdraw(address)", &[to]),
        storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(10),
    )
    .expect("closed");
    assert!(closed.reverted);
    assert_eq!(closed.returndata, selector("Closed()").to_vec());
    assert!(closed.trace.iter().all(|e| !matches!(e, Ev::Call { .. })));
    assert!(closed.balances.get(&to).is_none());

    let denied = exec(
        &runtime,
        &word_data("set_open(bool)", &[Word::from_u64(1)]),
        storage.clone(),
        Word::from_u64(0xcd),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("denied");
    assert!(denied.reverted);
    assert_eq!(denied.returndata, selector("NotOwner()").to_vec());

    let opened = exec(
        &runtime,
        &word_data("set_open(bool)", &[Word::from_u64(1)]),
        storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("open");
    assert!(!opened.reverted, "{}", pretty(&opened.returndata));
    assert_eq!(layout.get(&opened.storage, 0), Word::from_u64(1));

    let paid = exec(
        &runtime,
        &word_data("withdraw(address)", &[to]),
        opened.storage,
        owner,
        Word::from_u64(0),
        Word::from_u64(10),
    )
    .expect("withdraw");
    assert!(!paid.reverted, "{}", pretty(&paid.returndata));
    assert_eq!(paid.balances.get(&to).copied(), Some(Word::from_u64(10)));
    assert!(paid.trace.iter().any(|e| matches!(e, Ev::Call { .. })));
}

#[test]
fn typed_errors_revert_with_custom_error_data() {
    let layout = leaves(BANK);
    let runtime = deploy(&compile(BANK).expect("compile")).expect("deploy");
    let owner = Word::from_u64(0xab);
    let mut storage = HashMap::new();
    layout.put(&mut storage, 0, owner);
    layout.put(&mut storage, 2, Word::from_u64(3));

    let paused = {
        let mut s = storage.clone();
        layout.put(&mut s, 1, Word::from_u64(1));
        s
    };
    let denied = exec(
        &runtime,
        &word_data("withdraw(uint256)", &[Word::from_u64(1)]),
        paused,
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("paused");
    assert!(denied.reverted);
    assert_eq!(denied.returndata, selector("Paused()").to_vec());
    assert!(denied.trace.is_empty());

    let zero = exec(
        &runtime,
        &word_data("withdraw(uint256)", &[Word::from_u64(0)]),
        storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("zero");
    assert!(zero.reverted);
    assert!(zero
        .returndata
        .starts_with(&selector("InvalidAmount(uint256)")));
    assert_eq!(load_bytes(&zero.returndata, 4), Word::from_u64(0));

    let short = exec(
        &runtime,
        &word_data("withdraw(uint256)", &[Word::from_u64(5)]),
        storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("short");
    assert!(short.reverted);
    assert!(short
        .returndata
        .starts_with(&selector("InsufficientBalance(uint256,uint256)")));
    assert_eq!(load_bytes(&short.returndata, 4), Word::from_u64(3));
    assert_eq!(load_bytes(&short.returndata, 36), Word::from_u64(5));
    assert_eq!(layout.get(&short.storage, 2), Word::from_u64(3));

    let paid = exec(
        &runtime,
        &word_data("withdraw(uint256)", &[Word::from_u64(2)]),
        storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("paid");
    assert!(!paid.reverted, "{}", pretty(&paid.returndata));
    assert_eq!(layout.get(&paid.storage, 2), Word::from_u64(1));
    assert_eq!(trace_kinds(&paid.trace), ["sstore", "log"]);

    let stranger = exec(
        &runtime,
        &word_data("set_pause(bool)", &[Word::from_u64(1)]),
        storage.clone(),
        Word::from_u64(0xcd),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("stranger");
    assert!(stranger.reverted);
    assert_eq!(stranger.returndata, selector("NotOwner()").to_vec());
    assert_eq!(layout.get(&stranger.storage, 1), Word::from_u64(0));

    let closed = exec(
        &runtime,
        &word_data("set_pause(bool)", &[Word::from_u64(1)]),
        storage,
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("close");
    assert!(!closed.reverted, "{}", pretty(&closed.returndata));
    assert_eq!(layout.get(&closed.storage, 1), Word::from_u64(1));
}

#[test]
fn division_by_zero_is_a_panic() {
    let src = "\
storage is record {
  count : nat;
}

external function boom(const n : nat) is {
  storage.count := n / 0n;
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let out = exec(
        &runtime,
        &word_data("boom(uint256)", &[Word::from_u64(1)]),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("boom");
    assert!(out.reverted);
    assert!(out.returndata.starts_with(&selector("Panic(uint256)")));
    assert_eq!(load_bytes(&out.returndata, 4), Word::from_u64(0x12));
}

#[test]
fn dispatch_errors_follow_the_path() {
    let tree = crate::abi_tree(DISPATCH_ERRORS).expect("abi-tree");
    assert_eq!(
        tree,
        "\
reset
  path:
    main -> owner_main -> reset

  calls:
    none

  guards:
    - Evm.sender() = storage.owner

  storage reads:
    - storage.owner

  storage writes:
    - storage.count

  queries:
    none

  events:
    none

  operations:
    none

  raises:
    - NotOwner()

increment
  path:
    main -> public_main -> increment

  calls:
    none

  guards:
    none

  storage reads:
    - storage.count

  storage writes:
    - storage.count

  queries:
    none

  events:
    none

  operations:
    none

  raises:
    none
"
    );

    let report = crate::errors(BANK).expect("errors");
    assert!(
        report.contains(
            "\
withdraw(uint256)

  Paused()
  InvalidAmount(uint256)
  InsufficientBalance(uint256,uint256)
"
        ),
        "{report}"
    );
    assert!(
        report.contains(
            "\
set_pause(bool)

  NotOwner()
"
        ),
        "{report}"
    );
    let sel = hex(&selector("InsufficientBalance(uint256,uint256)"));
    assert!(
        report.contains(&format!("selector:\n  0x{sel}\n")),
        "{report}"
    );
    assert!(
        report.contains(
            "\
fields:
  available : uint256
  required : uint256

raised by:
  withdraw(uint256)
"
        ),
        "{report}"
    );
    assert!(
        report.contains("raised by:\n  set_pause(bool)\n"),
        "{report}"
    );
}

#[test]
fn every_example_file_is_compiled() {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut found = Vec::new();
    lithe_files(&root, &mut found);
    let mut rejects = Vec::new();
    for path in &found {
        let rel = path
            .strip_prefix(&root)
            .expect("under examples")
            .to_string_lossy()
            .replace('\\', "/");
        let src = std::fs::read_to_string(path).unwrap_or_else(|err| panic!("{rel}: {err}"));
        if rel.starts_with("reject/") {
            if reject_root(&rel) {
                rejects.push(rel);
            }
            continue;
        }
        if !is_program(&src) {
            continue;
        }
        let result = if has_imports(&src) {
            crate::compile_file(path).map(|_| ())
        } else if contracts(&src) > 1 {
            crate::compile_contracts(&src).map(|_| ())
        } else {
            compile(&src).map(|_| ())
        };
        result.unwrap_or_else(|err| panic!("{rel} failed to compile: {err}"));
    }
    rejects.sort();
    let mut expected: Vec<&str> = REJECT_RULES.iter().map(|(path, _)| *path).collect();
    expected.sort();
    assert_eq!(rejects, expected, "every reject example needs a rule");
    for (rel, rule) in REJECT_RULES {
        let path = root.join(rel);
        let src = std::fs::read_to_string(&path).unwrap_or_else(|err| panic!("{rel}: {err}"));
        let err = if has_imports(&src) {
            crate::compile_file(&path).expect_err(rel)
        } else if contracts(&src) > 1 {
            crate::compile_contracts(&src).expect_err(rel)
        } else {
            compile(&src).expect_err(rel)
        };
        assert!(
            err.to_string().contains(rule),
            "{rel}: expected `{rule}` in {err}"
        );
    }
}

const REJECT_RULES: &[(&str, &str)] = &[
    (
        "reject/bare_storage.lithe",
        "storage field `paid` must be qualified as `storage.paid`",
    ),
    (
        "reject/create.lithe",
        "`Vault` has no `deploy` parameters, so it takes no arguments",
    ),
    (
        "reject/error_collision.lithe",
        "error selector `NotOwner()` collides",
    ),
    (
        "reject/event_indexed_emit.lithe",
        "`indexed` belongs on the event declaration",
    ),
    (
        "reject/event_indexed_storage.lithe",
        "`indexed` is only valid on an event field",
    ),
    (
        "reject/event_topics.lithe",
        "event `Foo` declares 4 indexed fields",
    ),
    (
        "reject/error_mismatch.lithe",
        "external function `go` may raise `Closed`",
    ),
    (
        "reject/function_writes_storage.lithe",
        "declared effect is weaker than the body's: view function `bad` writes storage",
    ),
    ("reject/string_error.lithe", "errors must be typed"),
    (
        "reject/undeclared_error.lithe",
        "external function `go` must declare its errors",
    ),
    (
        "reject/untyped_binding.lithe",
        "local bindings require a type",
    ),
    (
        "reject/view_writes_storage.lithe",
        "declared effect is weaker than the body's: external view function `bad` writes storage",
    ),
    (
        "reject/loop_map.lithe",
        "a map cannot be iterated; keep an enumerable set",
    ),
    ("reject/loop_bound.lithe", "`bound` must be a number"),
    (
        "reject/type_storage.lithe",
        "declare contract storage as `storage is record`",
    ),
    ("reject/literal_range.lithe", "does not fit type `tiny`"),
    (
        "reject/nominal_assign.lithe",
        "initializer type does not match",
    ),
    ("reject/nat_suffix.lithe", "initializer type does not match"),
    (
        "reject/value_nonpayable.lithe",
        "`deposit` is not payable; declare it `payable function deposit` in its interface to send value",
    ),
    (
        "reject/value_payable.lithe",
        "external function `go` reads `Evm.value()`; write `external payable function`",
    ),
    (
        "reject/payable_procedure.lithe",
        "payable functions must be external; write `external payable function`",
    ),
    (
        "reject/payable_order.lithe",
        "payable functions must be stateful",
    ),
    (
        "reject/keyword_order.lithe",
        "keywords out of order; write `external view function`",
    ),
    (
        "reject/nonreentrant_named.lithe",
        "named nonreentrant domains are not supported",
    ),
    (
        "reject/nonreentrant_readonly.lithe",
        "nonreentrant functions must be external; write `external nonreentrant function`",
    ),
    (
        "reject/nonreentrant_pure.lithe",
        "a pure function reads no state, so it cannot be nonreentrant",
    ),
    (
        "reject/upgrade_guard.lithe",
        "upgradeable contract requires an upgrade guard",
    ),
    (
        "reject/guard_alone.lithe",
        "upgrade guard requires `upgradeable`",
    ),
    (
        "reject/migrate_defer.lithe",
        "migrate cannot defer an operation",
    ),
    ("reject/migrate_query.lithe", "migrate cannot query"),
    (
        "reject/cycle/main.lithe",
        "cyclic module dependency detected",
    ),
    (
        "reject/clash/main.lithe",
        "ambiguous symbol `calculate_fee`",
    ),
    (
        "reject/private_call/main.lithe",
        "unknown function `hidden`",
    ),
    (
        "reject/aliased_entry/main.lithe",
        "an imported file cannot declare external function `go`",
    ),
    (
        "reject/readonly_calls.lithe",
        "declared effect is weaker than the body's: view function `mid` calls `bump`, which is stateful",
    ),
    (
        "reject/view_list_writer.lithe",
        "declared effect is weaker than the body's: external view function `get` calls `bump`, which is stateful",
    ),
    (
        "reject/pure_storage.lithe",
        "declared effect is weaker than the body's: pure function `balance` reads contract storage",
    ),
    (
        "reject/pure_call.lithe",
        "declared effect is weaker than the body's: pure function `wrapped` calls `peek`, which is not pure",
    ),
    (
        "reject/pure_env.lithe",
        "declared effect is weaker than the body's: pure function `who` reads `Evm.sender`",
    ),
    (
        "reject/generic_key.lithe",
        "type `string` does not satisfy `map_key`",
    ),
    ("reject/view_defers.lithe", "declared effect is weaker than the body's: external view function `balance` cannot defer an operation"),
    (
        "reject/then_var.lithe",
        "`remaining` is a `var` of an earlier phase; mutable locals do not cross an external call",
    ),
    (
        "reject/declare_mismatch.lithe",
        "module `Ledger` does not have the contract's inline interface: `balance` is stateful in the inline interface and `view` in `Ledger`",
    ),
    (
        "reject/declare_body.lithe",
        "an interface's methods have no body",
    ),
    (
        "reject/declare_clash.lithe",
        "duplicate entrypoint `transfer(uint256)`",
    ),
    (
        "reject/missing_requires.lithe",
        "module `Guarded` requires `Ledger`",
    ),
    (
        "reject/storage_id.lithe",
        "storage id `lithe.std.foo` conflicts between `Alpha` and `Beta`",
    ),
    (
        "reject/module_storage.lithe",
        "module `Ledger` uses `Pausable.settings` but does not require `Pausable`",
    ),
    (
        "reject/storage_qualify.lithe",
        "storage `ledger` belongs to `Ledger`; write `Ledger.ledger`",
    ),
    (
        "reject/mixed_contract.lithe",
        "explicit `contract Foo` cannot share a file with top-level contract declarations",
    ),
    (
        "reject/module_contract_call.lithe",
        "module `Ledger` cannot call `hook`, which belongs to no module",
    ),
    (
        "reject/duplicate_use.lithe",
        "module `Ledger` is already used",
    ),
    ("reject/unknown_module.lithe", "unknown module `Missing`"),
    (
        "reject/require_call.lithe",
        "module `Guarded` calls `Pausable` but does not require it",
    ),
];

fn reject_root(rel: &str) -> bool {
    let rest = rel.trim_start_matches("reject/");
    !rest.contains('/') || rest.ends_with("/main.lithe")
}

fn is_program(src: &str) -> bool {
    src.lines().any(|line| {
        // A module's own externals are indented; only the contract's make a program.
        line.starts_with("external ")
            || line.starts_with("  external use ")
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

fn has_imports(src: &str) -> bool {
    src.lines()
        .any(|line| line.trim_start().starts_with("import \""))
}

#[test]
fn added_examples_match_runtime_results() {
    let widths_layout = leaves(include_str!("../examples/widths.lithe"));
    let widths = deploy(&compile(include_str!("../examples/widths.lithe")).expect("widths"))
        .expect("deploy");
    let filled = call(&widths, "fill()", &[]);
    assert!(!filled.reverted, "{}", pretty(&filled.returndata));
    assert_eq!(widths_layout.get(&filled.storage, 0), Word::from_u64(11));
    assert_eq!(widths_layout.get(&filled.storage, 1), Word::from_u64(1000));
    assert_eq!(
        widths_layout.get(&filled.storage, 2),
        Word::from_u64(0).wrapping_sub(Word::from_u64(5))
    );
    let clipped = call(&widths, "clip(uint256)", &[Word::from_u64(7)]);
    assert!(!clipped.reverted, "{}", pretty(&clipped.returndata));
    assert_eq!(widths_layout.get(&clipped.storage, 0), Word::from_u64(7));
    let too_wide = call(&widths, "clip(uint256)", &[Word::from_u64(300)]);
    assert!(too_wide.reverted);
    assert_eq!(load_bytes(&too_wide.returndata, 4), Word::from_u64(0x11));
    let overflow = call(
        &widths,
        "overflow(uint8,uint8)",
        &[Word::from_u64(200), Word::from_u64(200)],
    );
    assert!(overflow.reverted);
    assert_eq!(load_bytes(&overflow.returndata, 4), Word::from_u64(0x11));

    let units_layout = leaves(include_str!("../examples/units.lithe"));
    let units =
        deploy(&compile(include_str!("../examples/units.lithe")).expect("units")).expect("deploy");
    let priced = call(&units, "set()", &[]);
    assert!(!priced.reverted, "{}", pretty(&priced.returndata));
    assert_eq!(
        units_layout.get(&priced.storage, 0),
        Word::from_u64(20_000_000_001)
    );
    assert_eq!(
        units_layout.get(&priced.storage, 1),
        Word::from_u64(3_600 + 1_800 + 15)
    );
    assert_eq!(
        units_layout.get(&priced.storage, 2),
        Word::from_u64(1_700_000_000 + 2 * 86_400)
    );
    assert_eq!(
        units_layout.get(&priced.storage, 3),
        Word::from_u64(2 * 86_400)
    );

    let bytes_layout = leaves(include_str!("../examples/bytes.lithe"));
    let bytes =
        deploy(&compile(include_str!("../examples/bytes.lithe")).expect("bytes")).expect("deploy");
    let tagged = call(&bytes, "set()", &[]);
    assert!(!tagged.reverted, "{}", pretty(&tagged.returndata));
    assert_eq!(
        bytes_layout.get(&tagged.storage, 0),
        Word::from_u64(0xa9059cbb)
    );
    assert_eq!(bytes_layout.get(&tagged.storage, 1), Word::from_u64(0x11));
    assert_eq!(bytes_layout.get(&tagged.storage, 2), Word::from_u64(0xab));

    let named =
        deploy(&compile(include_str!("../examples/named.lithe")).expect("named")).expect("deploy");
    let who = Word::from_u64(0xcd);
    let configured = call(
        &named,
        "configure(uint256,address)",
        &[Word::from_u64(30), who],
    );
    assert!(!configured.reverted, "{}", pretty(&configured.returndata));
    let settings = crate::keccak::erc7201("example.settings");
    let treasury = crate::keccak::erc7201("example.treasury");
    assert_eq!(
        configured.storage.get(&settings).copied(),
        Some(Word::from_u64(30))
    );
    assert_eq!(
        configured
            .storage
            .get(&settings.wrapping_add(Word::from_u64(1)))
            .copied(),
        Some(Word::from_u64(1))
    );
    assert_eq!(configured.storage.get(&treasury).copied(), Some(who));
    assert_eq!(
        configured
            .storage
            .get(&treasury.wrapping_add(Word::from_u64(1)))
            .copied(),
        Some(Word::from_u64(2_000_000_000_000_000_000))
    );
    let viewed = exec(
        &named,
        &word_data("fee()", &[]),
        configured.storage,
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("fee");
    assert!(!viewed.reverted, "{}", pretty(&viewed.returndata));
    assert_eq!(load_bytes(&viewed.returndata, 0), Word::from_u64(30));
}

#[test]
fn decorators_split_visibility_and_effects() {
    let src = include_str!("../examples/decorators.lithe");
    let abi = crate::abi(src).expect("abi");
    for name in ["set", "add", "deposit", "count"] {
        assert!(abi.contains(&format!("\"name\": \"{name}\"")), "{abi}");
    }
    for hidden in ["bump", "doubled", "stamp"] {
        assert!(!abi.contains(&format!("\"name\": \"{hidden}\"")), "{abi}");
    }
    assert!(abi.contains("\"stateMutability\": \"payable\""), "{abi}");
    assert!(abi.contains("\"stateMutability\": \"view\""), "{abi}");

    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let set = call(&runtime, "set(uint256)", &[Word::from_u64(4)]);
    assert!(!set.reverted, "{}", pretty(&set.returndata));
    assert_eq!(slot(&set.storage, 0), Word::from_u64(4));
    let added = call(&runtime, "add(uint256)", &[Word::from_u64(3)]);
    assert!(!added.reverted, "{}", pretty(&added.returndata));
    assert_eq!(slot(&added.storage, 0), Word::from_u64(6));
    let counted = exec(
        &runtime,
        &word_data("count()", &[]),
        set.storage.clone(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("count");
    assert!(!counted.reverted, "{}", pretty(&counted.returndata));
    assert_eq!(load_bytes(&counted.returndata, 0), Word::from_u64(4));
    let paid = exec(
        &runtime,
        &word_data("deposit()", &[]),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(9),
        Word::from_u64(9),
    )
    .expect("deposit");
    assert!(!paid.reverted, "{}", pretty(&paid.returndata));
    assert_eq!(slot(&paid.storage, 1), Word::from_u64(9));
    let rejected = exec(
        &runtime,
        &word_data("add(uint256)", &[Word::from_u64(1)]),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(1),
        Word::from_u64(1),
    )
    .expect("value");
    assert!(rejected.reverted, "a plain entry rejects value");
}

#[test]
fn pure_functions_depend_only_on_arguments() {
    let src = include_str!("../examples/pure.lithe");
    let abi = crate::abi(src).expect("abi");
    for hidden in ["calculate_fee", "fee_of"] {
        assert!(!abi.contains(&format!("\"name\": \"{hidden}\"")), "{abi}");
    }
    assert!(abi.contains("\"name\": \"preview\""), "{abi}");
    assert!(abi.contains("\"name\": \"quote\""), "{abi}");

    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let preview = call(&runtime, "preview(uint256)", &[Word::from_u64(10_000)]);
    assert!(!preview.reverted, "{}", pretty(&preview.returndata));
    assert_eq!(load_bytes(&preview.returndata, 0), Word::from_u64(25));
    let quoted = call(&runtime, "quote(uint256)", &[Word::from_u64(10_000)]);
    assert!(!quoted.reverted, "{}", pretty(&quoted.returndata));
    assert_eq!(slot(&quoted.storage, 0), Word::from_u64(25));

    let raised = r#"
error Too_small;

storage is record { n : nat; }

pure function need(const n : nat) : nat
  raises Too_small
is {
  assert(n > 0n, Too_small);
} with n

external function go(const n : nat)
  raises Too_small
is {
  storage.n := need(n);
}
"#;
    compile(raised).expect("pure function raises a typed error");

    let hashed = r#"
storage is record { digest : bytes32; }

pure function digest(const data : bytes) : bytes32 is
  Crypto.keccak256(data)

external function store(const data : bytes) is {
  storage.digest := digest(data);
}
"#;
    compile(hashed).expect("a hash of an argument is pure");

    let module = r#"
module Fees is {
  pure function calculate_fee(const amount : nat; const fee_bps : nat) : nat is
    amount * fee_bps / 10_000n
}

use Fees;

storage is record { rate : nat; }

external function quote(const amount : nat) is {
  storage.rate := Fees.calculate_fee(amount, 25n);
}
"#;
    compile(module).expect("a module can define a pure function");

    let declared = r#"
module Math is {
  external pure function double(const n : nat) : nat is
    n + n
}

storage is record { n : nat; }

external use Math is {
  view function double(n : nat) : nat;
}
"#;
    let err = compile(declared).expect_err("pure is not a view");
    assert!(
        err.to_string()
            .contains("module `Math` does not have the contract's inline interface: `double` is `view` in the inline interface and `pure` in `Math`"),
        "{err}"
    );

    let wrote = r#"
storage is record { n : nat; }

pure function set() is {
  storage.n := 1n;
}
"#;
    let err = compile(wrote).expect_err("write");
    assert!(
        err.to_string().contains(
            "declared effect is weaker than the body's: pure function `set` writes storage"
        ),
        "{err}"
    );

    let emitted = r#"
event Ping of record { n : nat; }

pure function ping() is {
  emit Ping { n = 1n };
}
"#;
    let err = compile(emitted).expect_err("emit");
    assert!(
        err.to_string().contains(
            "declared effect is weaker than the body's: pure function `ping` cannot emit"
        ),
        "{err}"
    );

    let queried = r#"
interface Source is {
  view function read() : nat;
}

pure function pulled(const source : Source) : nat is
  query source.read()
"#;
    let err = compile(queried).expect_err("query");
    assert!(
        err.to_string()
            .contains("declared effect is weaker than the body's: pure function `pulled` queries another contract"),
        "{err}"
    );

    let deferred = r#"
interface Token is {
  function transfer(to : address; amount : nat);
}

pure function send(const token : Token; const to : address) is {
  defer token.transfer(to, 1n);
}
"#;
    let err = compile(deferred).expect_err("defer");
    assert!(
        err.to_string()
            .contains("declared effect is weaker than the body's: pure function `send` cannot defer an operation"),
        "{err}"
    );

    // All six combinations of visibility and effect are expressible.
    let external_pure = "\
storage is record { n : nat; }
pure function twice(const n : nat) : nat is n + n
external pure function double(const n : nat) : nat is twice(n)
external function set(const n : nat) is { storage.n := twice(n); }
";
    let runtime = deploy(&compile(external_pure).expect("external pure")).expect("deploy");
    let out = call(&runtime, "double(uint256)", &[Word::from_u64(21)]);
    assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(42));
    let abi = crate::abi(external_pure).expect("abi");
    assert!(abi.contains("\"stateMutability\": \"pure\""), "{abi}");
    let reads = "storage is record { n : nat; }\nexternal pure function get() : nat is storage.n\n";
    let err = compile(reads).expect_err("external pure reads");
    assert!(
        err.to_string().contains(
            "declared effect is weaker than the body's: external pure function `get` reads contract storage"
        ),
        "{err}"
    );
    // External functions are never called from inside the contract.
    for (callee, call_site) in [
        (
            "external view function get() : nat is storage.n",
            "storage.n := get();",
        ),
        ("external function get() is { storage.n := 1n; }", "get();"),
    ] {
        let src = format!(
            "storage is record {{ n : nat; }}\n{callee}\nexternal function go() is {{ {call_site} }}\n"
        );
        let err = compile(&src).expect_err("internal call to an external function");
        assert!(
            err.to_string()
                .contains("`get` cannot be called from inside the contract"),
            "{err}"
        );
    }
}

#[test]
fn generics_specialize_sets() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/generics.lithe");
    let abi = crate::abi_file(&path).expect("abi");
    assert!(abi.contains("\"name\": \"is_admin\""), "{abi}");
    assert!(abi.contains("\"name\": \"grant\""), "{abi}");
    assert!(!abi.contains("\"name\": \"contains\""), "{abi}");
    assert!(!abi.contains("\"name\": \"identity\""), "{abi}");
    let tree = crate::abi_tree_file(&path).expect("tree");
    assert!(
        tree.contains("storage.admins"),
        "analysis should see the concrete write\n{tree}"
    );

    let runtime = deploy(&crate::compile_file(&path).expect("compile")).expect("deploy");
    let alice = Word::from_u64(2);
    let bob = Word::from_u64(3);
    let caller = Word::from_u64(1);
    let granted = call(&runtime, "grant(address)", &[alice]);
    assert!(!granted.reverted, "{}", pretty(&granted.returndata));
    let admin = exec(
        &runtime,
        &word_data("is_admin(address)", &[alice]),
        granted.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("admin");
    assert!(!admin.reverted, "{}", pretty(&admin.returndata));
    assert_eq!(load_bytes(&admin.returndata, 0), Word::from_u64(1));
    let revoked = exec(
        &runtime,
        &word_data("revoke(address)", &[alice]),
        granted.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("revoke");
    assert!(!revoked.reverted, "{}", pretty(&revoked.returndata));
    let gone = exec(
        &runtime,
        &word_data("is_admin(address)", &[alice]),
        revoked.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("gone");
    assert_eq!(load_bytes(&gone.returndata, 0), Word::from_u64(0));

    let first = call(&runtime, "add_validator(address)", &[alice]);
    assert!(!first.reverted, "{}", pretty(&first.returndata));
    let second = exec(
        &runtime,
        &word_data("add_validator(address)", &[bob]),
        first.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("second");
    assert!(!second.reverted, "{}", pretty(&second.returndata));
    let again = exec(
        &runtime,
        &word_data("add_validator(address)", &[alice]),
        second.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("duplicate");
    assert!(!again.reverted, "{}", pretty(&again.returndata));
    let count = exec(
        &runtime,
        &word_data("validator_count()", &[]),
        again.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("count");
    assert_eq!(load_bytes(&count.returndata, 0), Word::from_u64(2));
    let at0 = exec(
        &runtime,
        &word_data("validator_at(uint256)", &[Word::from_u64(0)]),
        again.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("at0");
    assert!(!at0.reverted, "{}", pretty(&at0.returndata));
    assert_eq!(load_bytes(&at0.returndata, 0), alice);
    let at1 = exec(
        &runtime,
        &word_data("validator_at(uint256)", &[Word::from_u64(1)]),
        again.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("at1");
    assert_eq!(load_bytes(&at1.returndata, 0), bob);
    let dropped = exec(
        &runtime,
        &word_data("drop_validator(address)", &[alice]),
        again.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("drop");
    assert!(!dropped.reverted, "{}", pretty(&dropped.returndata));
    let left = exec(
        &runtime,
        &word_data("validator_count()", &[]),
        dropped.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("left");
    assert_eq!(load_bytes(&left.returndata, 0), Word::from_u64(1));
    let now0 = exec(
        &runtime,
        &word_data("validator_at(uint256)", &[Word::from_u64(0)]),
        dropped.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("now0");
    assert_eq!(load_bytes(&now0.returndata, 0), bob);
    let bounds = exec(
        &runtime,
        &word_data("validator_at(uint256)", &[Word::from_u64(1)]),
        dropped.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("bounds");
    assert!(bounds.reverted, "index past count reverts");

    let tracked = call(&runtime, "track(bytes32)", &[Word::from_u64(9)]);
    assert!(!tracked.reverted, "{}", pretty(&tracked.returndata));

    let mixed = r#"
module Set(T : map_key) is {
  type self is map(T, bool);
  function add(const set : self; const value : T) is {
    set[value] := true;
  }
}
type order_id is bytes32;
storage is record { orders : Set(order_id); }
external function bad(const id : bytes32) is {
  Set.add(storage.orders, id);
}
"#;
    let err = compile(mixed).expect_err("nominal");
    assert!(
        err.to_string()
            .contains("type parameter `T` is both `order_id` and `bytes32`"),
        "{err}"
    );

    let used = r#"
module Set(T : map_key) is {
  type self is map(T, bool);
}
use Set;
storage is record { n : nat; }
external function go() is { skip }
"#;
    let err = compile(used).expect_err("use");
    assert!(
        err.to_string()
            .contains("module `Set` is generic; instantiate it as `Set(...)`"),
        "{err}"
    );
}

fn map_key(key: Word, slot: Word) -> Word {
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(&key.to_be_bytes());
    buf[32..].copy_from_slice(&slot.to_be_bytes());
    Word::from_be_bytes(crate::keccak::keccak256(&buf))
}

#[test]
fn records_in_maps_lay_out_like_solidity_structs() {
    let src = include_str!("../fuzz/records.lithe");
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let neg = |n: u64| w(0).wrapping_sub(w(n));
    let run = |storage: &HashMap<Word, Word>, sig: &str, args: &[Word]| {
        exec(
            &runtime,
            &word_data(sig, args),
            storage.clone(),
            w(7),
            w(0),
            w(0),
        )
        .unwrap_or_else(|err| panic!("{sig}: {err}"))
    };
    let at = |storage: &HashMap<Word, Word>, slot: Word| {
        storage.get(&slot).copied().unwrap_or_else(|| w(0))
    };
    let placed = run(
        &HashMap::new(),
        "place(uint256,uint256,uint32,int16)",
        &[w(1), w(1000), w(5), neg(300)],
    );
    assert!(!placed.reverted, "{}", pretty(&placed.returndata));
    // `status` and `owner` share the first slot; `inner` and `last` each start a new one.
    let base = map_key(w(1), w(1));
    let slot = |i: u64| base.wrapping_add(w(i));
    assert_eq!(at(&placed.storage, slot(0)), w(0x701));
    assert_eq!(at(&placed.storage, slot(1)), w(1000));
    assert_eq!(at(&placed.storage, slot(2)), w(5));
    assert_eq!(at(&placed.storage, slot(3)), w(0xfed401));
    assert_eq!(at(&placed.storage, slot(4)), w(7));

    let bumped = run(&placed.storage, "bump(uint256,uint256)", &[w(1), w(5)]);
    assert!(!bumped.reverted, "{}", pretty(&bumped.returndata));
    assert_eq!(at(&bumped.storage, slot(0)), w(0x702));
    assert_eq!(at(&bumped.storage, slot(1)), w(1005));
    assert_eq!(at(&bumped.storage, slot(3)), w(0xfed301));
    assert_eq!(at(&bumped.storage, slot(4)), w(8));
    assert_eq!(at(&bumped.storage, w(3)), w(2));
    let delta = run(&bumped.storage, "delta_of(uint256)", &[w(1)]);
    assert_eq!(load_bytes(&delta.returndata, 0), neg(301));
    assert!(run(&placed.storage, "bump(uint256,uint256)", &[w(2), w(1)]).reverted);
    let low = run(
        &HashMap::new(),
        "place(uint256,uint256,uint32,int16)",
        &[w(3), w(1), w(1), neg(32768)],
    );
    assert!(
        run(&low.storage, "bump(uint256,uint256)", &[w(3), w(1)]).reverted,
        "int16 underflow"
    );

    let copied = run(&bumped.storage, "copy(uint256,uint256)", &[w(1), w(4)]);
    let copy = |i: u64| map_key(w(4), w(1)).wrapping_add(w(i));
    assert_eq!(at(&copied.storage, copy(0)), w(0x702));
    assert_eq!(at(&copied.storage, copy(3)), w(0xfed300));
    let order = run(&copied.storage, "order_of(uint256)", &[w(4)]);
    let words: Vec<Word> = (0..7)
        .map(|i| load_bytes(&order.returndata, i * 32))
        .collect();
    assert_eq!(words, [w(2), w(7), w(1005), w(5), w(0), neg(301), w(8)]);

    // Through the journal and directly, the same writes leave the same slots.
    let price = run(&bumped.storage, "probe(address,uint256)", &[w(2), w(1)]);
    let price = load_bytes(&price.returndata, 0);
    let queried = run(&bumped.storage, "priced(address,uint256)", &[w(2), w(1)]);
    let direct = run(
        &bumped.storage,
        "set_price(uint256,uint256)",
        &[w(1), price],
    );
    assert!(!queried.reverted && !direct.reverted);
    assert_eq!(queried.storage, direct.storage);
    assert_ne!(queried.storage, bumped.storage);

    let paired = run(
        &HashMap::new(),
        "pair_set(uint256,uint128,uint128)",
        &[w(7), w(1), w(2)],
    );
    let inner = map_key(w(7), w(2));
    assert_eq!(
        at(&paired.storage, map_key(w(7), inner)),
        w(2).shl(128).wrapping_add(w(1))
    );
    assert_eq!(at(&paired.storage, map_key(w(8), inner)), w(2).shl(128));

    let program = |body: &str| {
        format!("type r is record {{ a : uint8; b : nat; }}\nstorage is record {{ m : map(nat, r); n : map(nat, nat); }}\nexternal function f(const k : nat) is {{\n  {body}\n}}\n")
    };
    for (body, want) in [
        ("storage.m[k].c := 1n;", "no field `c`"),
        (
            "storage.n[k].a := 1n;",
            "only a record in a map has fields here",
        ),
        (
            "storage.m[k].a := 1n;",
            "assignment type does not match the field",
        ),
    ] {
        let err = compile(&program(body)).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    let dynamic = "type r is record { a : string; }\nstorage is record { m : map(nat, r); }\nexternal function f() is { skip; }\n";
    let err = compile(dynamic).expect_err("string in a map value");
    assert!(err.to_string().contains("a fixed-size record"), "{err}");
}

#[test]
fn queries_see_storage_as_the_transition_found_it() {
    let src = "\
error Bad;
interface Me is {
  view function peek() : nat;
  view function peek_plus(k : nat) : nat;
}
storage is record { n : nat; seen : nat; }
external view function peek() : nat is storage.n
external view function peek_plus(const k : nat) : nat is storage.n + k
external function early(const me : Me; const k : nat)
  raises Bad
is {
  storage.n := storage.n + 1n;
  assert(k > 0n, Bad);
  const before : nat := query me.peek();
  storage.seen := before;
}
external function late(const me : Me) is {
  storage.n := storage.n + 1n;
  const before : nat := query me.peek_plus(storage.n);
  storage.seen := before;
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let me = w(0x1000);
    let run = |storage: &HashMap<Word, Word>, sig: &str, args: &[Word]| {
        exec(
            &runtime,
            &word_data(sig, args),
            storage.clone(),
            w(7),
            w(0),
            w(0),
        )
        .unwrap_or_else(|err| panic!("{sig}: {err}"))
    };
    let mut storage = HashMap::from([(w(0), w(5))]);
    // Issued before the write, the query still answers with the old count.
    let early = run(&storage, "early(address,uint256)", &[me, w(1)]);
    assert!(!early.reverted, "{}", pretty(&early.returndata));
    assert_eq!(
        (slot(&early.storage, 0), slot(&early.storage, 1)),
        (w(6), w(5))
    );
    storage = early.storage;
    // Its argument reads the new count, so it runs in place, and the view still sees the old one.
    let late = run(&storage, "late(address)", &[me]);
    assert!(!late.reverted, "{}", pretty(&late.returndata));
    assert_eq!(
        (slot(&late.storage, 0), slot(&late.storage, 1)),
        (w(7), w(13))
    );
    // An earlier failure keeps its error; the query's own failure comes where it was written.
    let bad = run(
        &HashMap::new(),
        "early(address,uint256)",
        &[w(0x2000), w(0)],
    );
    assert!(bad.reverted);
    assert_eq!(bad.returndata, selector("Bad()").to_vec());
    let failed = run(
        &HashMap::new(),
        "early(address,uint256)",
        &[w(0x2000), w(1)],
    );
    assert!(failed.reverted && failed.returndata.is_empty());
}

/// Each compile seeds its hash maps afresh, so repeating one shows whether any pass
/// leans on their iteration order.
#[test]
fn declarations_restate_the_module_external() {
    let program = |exposed: &str| {
        format!(
            "\
module Vault_ops is {{
  storage vault at \"vault.ops\" is record {{ deposits : map(address, wei); }}
  error Too_much of wei;
  function take(const amount : wei) raises Too_much is {{
    assert(amount <= vault.deposits[Evm.sender()], Too_much(amount));
    vault.deposits[Evm.sender()] := vault.deposits[Evm.sender()] - amount;
  }}
  external function withdraw(const amount : wei) raises Too_much is take(amount)
  external payable function deposit() is {{
    vault.deposits[Evm.sender()] := vault.deposits[Evm.sender()] + Evm.value();
  }}
  external view function deposit_of(const who : address) : wei is vault.deposits[who]
  external pure function fee(const amount : wei) : wei is amount / 100wei
  external view function hidden() : wei is 0wei
}}
external use Vault_ops is {{
{exposed}
}}
"
        )
    };
    let all = "\
  function withdraw(amount : wei) raises Too_much;
  payable function deposit();
  view function deposit_of(who : address) : wei;
  pure function fee(amount : wei) : wei;";
    let good = program(all);
    let abi = crate::abi(&good).expect("declarations");
    for name in ["withdraw", "deposit", "deposit_of", "fee"] {
        assert!(
            abi.contains(&format!("\"name\": \"{name}\"")),
            "{name}: {abi}"
        );
    }
    // What the contract does not declare is not part of its interface.
    assert!(!abi.contains("\"name\": \"hidden\""), "{abi}");
    assert!(abi.contains("\"stateMutability\": \"payable\""), "{abi}");
    assert!(abi.contains("\"stateMutability\": \"pure\""), "{abi}");
    let footprint = crate::footprint(&good).expect("footprint");
    assert!(
        footprint.contains("writes: Vault_ops.vault.deposits"),
        "{footprint}"
    );
    let runtime = deploy(&compile(&good).expect("compile")).expect("deploy");
    let out = call(&runtime, "fee(uint256)", &[Word::from_u64(500)]);
    assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(5));
    for (exposed, want) in [
        (
            "  view function withdraw(amount : wei) : wei raises Too_much;",
            "`withdraw` returns `wei` in the inline interface and nothing in `Vault_ops`",
        ),
        (
            "  function deposit();",
            "module `Vault_ops` does not have the contract's inline interface: `deposit` is `payable` in `Vault_ops` but not in the inline interface\n\n  interface:  function deposit()\n  module:     payable function deposit()",
        ),
        (
            "  view function fee(amount : wei) : wei;",
            "`fee` is `view` in the inline interface and `pure` in `Vault_ops`",
        ),
        (
            "  view function deposit_of(account : address) : wei;",
            "parameter 1 of `deposit_of` is `account` in the inline interface and `who` in `Vault_ops`",
        ),
        (
            "  view function deposit_of(who : address) : nat;",
            "`deposit_of` returns `nat` in the inline interface and `wei` in `Vault_ops`",
        ),
        (
            "  function withdraw(amount : wei);",
            "`withdraw` raises `Too_much` in `Vault_ops`, and the inline interface lists no errors",
        ),
        (
            "  function withdraw(amount : wei) raises Too_much | Other;",
            "unknown error `Other`",
        ),
        (
            "  function take(amount : wei) raises Too_much;",
            "`Vault_ops.take` is an internal function; declare it `external` in `Vault_ops` to offer it",
        ),
        (
            "  function missing();",
            "module `Vault_ops` does not have the contract's inline interface: it has no external `missing`",
        ),
        (
            "  external function withdraw(amount : wei) raises Too_much;",
            "an interface's methods are external; drop `external`",
        ),
        (
            "  function withdraw(const amount : wei) raises Too_much;",
            "an interface's parameters are `name : type`, without `const`",
        ),
        (
            "  nonreentrant function withdraw(amount : wei) raises Too_much;",
            "`nonreentrant` is not part of an interface",
        ),
    ] {
        let err = compile(&program(exposed)).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    // A module's external is not a function the contract can call.
    let src = good.replace(
        "external use Vault_ops is {",
        "external function again(const amount : wei) raises Too_much is Vault_ops.withdraw(amount)\nexternal use Vault_ops is {",
    );
    let err = compile(&src).expect_err("an external is not callable");
    assert!(
        err.to_string()
            .contains("external function `Vault_ops.withdraw` cannot be called from inside the contract"),
        "{err}"
    );
}

#[test]
fn compiling_is_deterministic() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    for rel in [
        "examples/named.lithe",
        "examples/upgrade.lithe",
        "bench/erc20.lithe",
        "bench/staking.lithe",
    ] {
        let path = root.join(rel);
        let first = crate::compile_file(&path).unwrap_or_else(|e| panic!("{rel}: {e}"));
        for _ in 0..4 {
            assert_eq!(crate::compile_file(&path).expect("again"), first, "{rel}");
        }
    }
}

#[test]
fn type_constants_take_their_width_from_context() {
    let src = "\
storage is record { small : uint8; delta : int16; big : nat; low : int; who : address; }
function lowest(T)(const value : T) : T is Int.min
external function set() is {
  storage.small := Nat.max;
  storage.delta := Int.min;
  storage.big := Nat.max;
  storage.low := lowest(Int.max);
  storage.who := Address.zero;
}
external view function capped(const n : nat) : bool is n < Nat.max
external view function top16() : int16 is Int.max
";
    let layout = leaves(src);
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let ones = Word::from_u64(0).not();
    let set = call(&runtime, "set()", &[]);
    assert!(!set.reverted, "{}", pretty(&set.returndata));
    assert_eq!(layout.get(&set.storage, 0), Word::from_u64(255));
    assert_eq!(layout.get(&set.storage, 1), Word::from_u64(0x7fff).not());
    assert_eq!(layout.get(&set.storage, 2), ones);
    assert_eq!(layout.get(&set.storage, 3), ones.shr(1).not());
    assert_eq!(layout.get(&set.storage, 4), Word::from_u64(0));
    let capped = call(&runtime, "capped(uint256)", &[ones]);
    assert_eq!(load_bytes(&capped.returndata, 0), Word::from_u64(0));
    let top = call(&runtime, "top16()", &[]);
    assert_eq!(load_bytes(&top.returndata, 0), Word::from_u64(0x7fff));
    let err = compile(
        "storage is record { n : nat; }\nexternal function f() is { storage.n := Nat.min; }\n",
    )
    .expect_err("no Nat.min");
    assert!(
        err.to_string().contains("unknown constant `Nat.min`"),
        "{err}"
    );
}

/// An option with a payload narrower than a word is one slot: zero is `None`, and `Some`
/// flips its payload so that even `Some(0)` or a maximal value never reads as `None`.
#[test]
fn narrow_options_take_one_slot() {
    let src = r#"
type inner is record {
  small : option(uint8);
  n : nat;
}

storage is record {
  who : option(address);
  small : option(uint8);
  tiny : option(int8);
  flag : option(bool);
  tag : option(bytes4);
  wide : option(nat);
  nested : inner;
}

pure function wrap(const k : uint8) : option(uint8) is
  Some(k)

pure function or_seven(const o : option(uint8)) : nat is
  case o of { | Some(v) -> nat(v) | None -> 7 }

external function set_who() is { storage.who := Some(Evm.sender()); }
external view function who_or() : address is
  case storage.who of { | Some(w) -> w | None -> Evm.self() }

external function set_small(const v : uint8) is { storage.small := Some(v); }
external function clear_small() is { storage.small := None; }
external view function small_or() : nat is
  case storage.small of { | Some(v) -> nat(v) | None -> 1000 }
external view function has_small() : bool is
  case storage.small of { | Some(v) -> true | None -> false }

external function set_tiny(const v : int8) is { storage.tiny := Some(v); }
external view function tiny_or() : int is
  case storage.tiny of { | Some(v) -> int(v) | None -> 1000 }

external function set_flag(const v : bool) is { storage.flag := Some(v); }
external view function flag_or(const d : bool) : bool is
  case storage.flag of { | Some(b) -> b | None -> d }

external function set_tag(const v : bytes4) is { storage.tag := Some(v); }
external view function tag_or(const d : bytes4) : bytes4 is
  case storage.tag of { | Some(t) -> t | None -> d }

external function set_wide(const v : nat) is { storage.wide := Some(v); }
external view function wide_or() : nat is
  case storage.wide of { | Some(v) -> v | None -> 1000 }

external function set_nested(const v : uint8) is { storage.nested.small := Some(v); }
external function copy_small() is {
  const held : option(uint8) := storage.small;
  storage.nested.small := held;
}
external view function nested_or() : nat is
  case storage.nested.small of { | Some(v) -> nat(v) | None -> 1000 }

external view function through(const k : uint8) : nat is {
  const o : option(uint8) := wrap(k);
} with case o of { | Some(v) -> nat(v) + or_seven(None) | None -> 0 }
external view function direct(const k : uint8) : nat is
  case wrap(k) of { | Some(v) -> or_seven(Some(v)) | None -> 0 }
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let caller = Word::from_u64(1);
    let run = |storage: &HashMap<Word, Word>, sig: &str, args: &[Word]| {
        let out = exec(
            &runtime,
            &word_data(sig, args),
            storage.clone(),
            caller,
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .unwrap_or_else(|err| panic!("{sig}: {err}"));
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        out
    };
    let read = |storage: &HashMap<Word, Word>, sig: &str, args: &[Word]| {
        load_bytes(&run(storage, sig, args).returndata, 0)
    };
    let empty = HashMap::new();
    let n = Word::from_u64;
    let neg = |v: u64| n(v - 1).not();

    // Unset storage is `None`.
    assert_eq!(read(&empty, "who_or()", &[]), n(0x1000));
    assert_eq!(read(&empty, "small_or()", &[]), n(1000));
    assert_eq!(read(&empty, "has_small()", &[]), n(0));
    assert_eq!(read(&empty, "tiny_or()", &[]), n(1000));
    assert_eq!(read(&empty, "wide_or()", &[]), n(1000));

    let who = run(&empty, "set_who()", &[]).storage;
    assert_eq!(slot(&who, 0), caller.not());
    assert_eq!(read(&who, "who_or()", &[]), caller);

    // `Some(0)` and `Some(255)` both stay distinct from `None`.
    for v in [0, 1, 255] {
        let set = run(&empty, "set_small(uint8)", &[n(v)]).storage;
        assert_eq!(slot(&set, 1), n(v).not());
        assert_eq!(slot(&set, 2), n(0));
        assert_eq!(read(&set, "small_or()", &[]), n(v));
        assert_eq!(read(&set, "has_small()", &[]), n(1));
        let cleared = run(&set, "clear_small()", &[]).storage;
        assert_eq!(slot(&cleared, 1), n(0));
        assert_eq!(read(&cleared, "small_or()", &[]), n(1000));
    }

    // A signed payload is flipped at its sign's next bit, so -1 is not `None` either.
    for v in [n(0), n(1), n(127), neg(1), neg(128)] {
        let set = run(&empty, "set_tiny(int8)", &[v]).storage;
        assert_eq!(slot(&set, 2), v.bitxor(n(0x80)));
        assert_ne!(slot(&set, 2), n(0));
        assert_eq!(read(&set, "tiny_or()", &[]), v);
    }

    for v in [0, 1] {
        let set = run(&empty, "set_flag(bool)", &[n(v)]).storage;
        assert_eq!(slot(&set, 3), n(v).not());
        assert_eq!(read(&set, "flag_or(bool)", &[n(1 - v)]), n(v));
    }
    assert_eq!(read(&empty, "flag_or(bool)", &[n(1)]), n(1));

    let ones = n(0xffff_ffff).shl(224);
    let tagged = run(&empty, "set_tag(bytes4)", &[ones]).storage;
    assert_ne!(slot(&tagged, 4), n(0));
    assert_eq!(read(&tagged, "tag_or(bytes4)", &[n(0)]), ones);
    let zero_tag = run(&empty, "set_tag(bytes4)", &[n(0)]).storage;
    assert_eq!(read(&zero_tag, "tag_or(bytes4)", &[ones]), n(0));

    // A full-width payload has no spare bit: a tag word, then the payload.
    let wide = run(&empty, "set_wide(uint256)", &[n(0)]).storage;
    assert_eq!(slot(&wide, 5), n(1));
    assert_eq!(slot(&wide, 6), n(0));
    assert_eq!(read(&wide, "wide_or()", &[]), n(0));

    let nested = run(&empty, "set_nested(uint8)", &[n(0)]).storage;
    assert_eq!(slot(&nested, 7), n(0).not());
    assert_eq!(read(&nested, "nested_or()", &[]), n(0));
    let small = run(&empty, "set_small(uint8)", &[n(42)]).storage;
    let copied = run(&small, "copy_small()", &[]).storage;
    assert_eq!(read(&copied, "nested_or()", &[]), n(42));
    let unset = run(&nested, "copy_small()", &[]).storage;
    assert_eq!(read(&unset, "nested_or()", &[]), n(1000));

    assert_eq!(read(&empty, "through(uint8)", &[n(0)]), n(7));
    assert_eq!(read(&empty, "through(uint8)", &[n(200)]), n(207));
    assert_eq!(read(&empty, "direct(uint8)", &[n(0)]), n(0));
    assert_eq!(read(&empty, "direct(uint8)", &[n(9)]), n(9));
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

/// Options as vars, results, arguments, tuple and record members, payloads of records,
/// tuples, and other options, and operands of `=`.
#[test]
fn options_work_as_values() {
    let src = include_str!("../examples/options.lithe");
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let empty = HashMap::new();
    let read = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| read_ok(&rt, st, sig, args);

    let none = run_ok(&rt, &empty, "pick(uint256)", &[n(0)]).storage;
    assert_eq!(read(&none, "last_or()", &[]), n(0));
    assert_eq!(slot(&none, 13), n(0));
    let some = run_ok(&rt, &empty, "pick(uint256)", &[n(5)]).storage;
    assert_eq!(slot(&some, 11), n(1));
    assert_eq!(slot(&some, 12), n(6));
    assert_eq!(read(&some, "last_or()", &[]), n(6));
    assert_eq!(slot(&some, 13), n(1));

    assert_eq!(read(&empty, "via_case(uint256)", &[n(41)]), n(42));
    assert_eq!(read(&empty, "direct_args(uint256)", &[n(9)]), n(10));
    assert_eq!(read(&empty, "eqs(uint256)", &[n(5)]), n(101_111));
    assert_eq!(read(&empty, "eqs(uint256)", &[n(4)]), n(101_110));
    assert_eq!(read(&empty, "inferred(uint256)", &[n(7)]), n(8));
    assert_eq!(read(&empty, "tuples(uint256)", &[n(10)]), n(35));
    assert_eq!(read(&empty, "records(uint256)", &[n(10)]), n(14));

    assert_eq!(read(&empty, "pos_sum()", &[]), n(0));
    let pos = run_ok(&rt, &empty, "set_pos(uint256,uint256)", &[n(3), n(4)]).storage;
    assert_eq!(
        (slot(&pos, 0), slot(&pos, 1), slot(&pos, 2)),
        (n(1), n(3), n(4))
    );
    assert_eq!(read(&pos, "pos_sum()", &[]), n(7));

    assert_eq!(read(&empty, "deep_or()", &[]), n(2));
    assert_eq!(read(&empty, "deep8_or()", &[]), n(2));
    let deep = run_ok(&rt, &empty, "set_deep(uint256)", &[n(9)]).storage;
    assert_eq!(
        (slot(&deep, 3), slot(&deep, 4), slot(&deep, 5)),
        (n(1), n(1), n(9))
    );
    // `Some(None)` of a one-word inner option: a tag, then the inner `None` as zero.
    assert_eq!((slot(&deep, 6), slot(&deep, 7)), (n(1), n(0)));
    assert_eq!(read(&deep, "deep_or()", &[]), n(9));
    assert_eq!(read(&deep, "deep8_or()", &[]), n(1));

    assert_eq!(read(&empty, "pair_or()", &[]), n(0));
    let pair = run_ok(&rt, &empty, "set_pair(uint256)", &[n(8)]).storage;
    assert_eq!((slot(&pair, 8), slot(&pair, 9)), (n(1), n(8)));
    assert_eq!(slot(&pair, 10), n(1).not());
    assert_eq!(read(&pair, "pair_or()", &[]), n(1008));
}

/// A function's record result binds to a name, has its fields read, and is stored whole.
#[test]
fn record_results_are_values() {
    let src = include_str!("../examples/records.lithe");
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let empty = HashMap::new();
    let read = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| read_ok(&rt, st, sig, args);
    assert_eq!(read(&empty, "spread(uint256)", &[n(5)]), n(5 + 7 + 105));
    assert_eq!(read(&empty, "low_plus(uint256)", &[n(5)]), n(6 + 15));
    assert_eq!(read(&empty, "span_high(uint256)", &[n(4)]), n(8));
    let quote = run_ok(&rt, &empty, "quote_of(uint256)", &[n(3)]).returndata;
    let words: Vec<Word> = (0..4).map(|i| load_bytes(&quote, i * 32)).collect();
    assert_eq!(words, [n(1), n(3), n(4), n(5)]);
    let saved = run_ok(&rt, &empty, "save(uint256)", &[n(7)]).storage;
    assert_eq!(read(&saved, "last()", &[]), n(7008));
    assert_eq!(read(&saved, "high_of(uint256)", &[n(7)]), n(9));
    let flipped = run_ok(&rt, &saved, "flip()", &[]).storage;
    assert_eq!(read(&flipped, "last()", &[]), n(8007));
}

/// Record results in transient storage, in a body whose writes wait for a query, as
/// arguments, and through calls that return another call's record.
#[test]
fn record_results_everywhere() {
    install_mocks();
    let src = r#"
interface Echo is {
  view function echo(n : nat) : nat;
}

type inner is record { a : nat; b : int16; }
type v is record { ok : bool; d : int16; i : inner; }

storage is record { r : v; k : nat; }

transient storage t is record { r : v; }

pure function mk(const n : nat; const d : int16) : v is {
  ok = true;
  d = d;
  i = { a = n; b = d - int16(1); };
}

pure function wrap(const n : nat) : v is mk(n + 1n, int16(-3))

pure function total(const x : v) : nat is x.i.a

external function later(const e : Echo; const n : nat) is {
  storage.r := mk(n, int16(-2));
  storage.k := query e.echo(storage.r.i.a);
}

external function flash(const n : nat) : int16 is {
  t.r := mk(n, int16(-7));
} with t.r.d + t.r.i.b

external view function chain(const n : nat) : nat is
  wrap(n).i.a + total(mk(n, int16(0))) + total({ ok = false; d = int16(0); i = { a = 5n; b = int16(0); }; })

external view function neg() : int16 is wrap(1n).i.b

external view function r_d() : int16 is storage.r.d

external view function r_b() : int16 is storage.r.i.b

external view function k() : nat is storage.k

pure function once(const n : nat) : v is {
  ok = false;
  d = int16(-9);
  i = { a = n * 2n; b = int16(4); };
}

external view function once_d(const n : nat) : int16 is int16(1) + once(n).d
"#;
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let neg = |v: u64| n(v).wrapping_neg();
    let empty = HashMap::new();
    let read = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| read_ok(&rt, st, sig, args);
    assert_eq!(read(&empty, "chain(uint256)", &[n(4)]), n(5 + 4 + 5));
    assert_eq!(read(&empty, "neg()", &[]), neg(4));
    assert_eq!(read(&empty, "flash(uint256)", &[n(1)]), neg(15));
    let later = run_ok(&rt, &empty, "later(address,uint256)", &[n(0xcd), n(6)]).storage;
    assert_eq!(read(&later, "k()", &[]), n(6));
    assert_eq!(read(&later, "r_d()", &[]), neg(2));
    assert_eq!(read(&later, "r_b()", &[]), neg(3));
    assert_eq!(read(&empty, "once_d(uint256)", &[n(2)]), neg(8));
    let overflow = exec(
        &rt,
        &word_data("once_d(uint256)", &[n(0).not()]),
        empty.clone(),
        n(1),
        n(0),
        n(0),
    );
    assert!(
        overflow.expect("once_d").reverted,
        "an unread field still fails"
    );
}

/// A missing map key reads as `None`, so a map of options tells "never set" from zero.
/// Options also sit in records held by maps, and in transient storage and its maps.
#[test]
fn options_live_in_maps_and_transient_storage() {
    let src = include_str!("../examples/option_maps.lithe");
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let empty = HashMap::new();
    let read = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| read_ok(&rt, st, sig, args);
    let run =
        |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| run_ok(&rt, st, sig, args).storage;
    let at = |st: &HashMap<Word, Word>, key: Word| st.get(&key).copied().unwrap_or(n(0));

    assert_eq!(read(&empty, "small_or(address)", &[n(1)]), n(1000));
    let small = run(&empty, "set_small(uint64)", &[n(0)]);
    assert_eq!(at(&small, map_key(n(1), n(0))), n(0).not());
    assert_eq!(read(&small, "small_or(address)", &[n(1)]), n(0));
    assert_eq!(read(&small, "small_or(address)", &[n(2)]), n(1000));
    let cleared = run(&small, "clear_small()", &[]);
    assert_eq!(at(&cleared, map_key(n(1), n(0))), n(0));
    assert_eq!(read(&cleared, "small_or(address)", &[n(1)]), n(1000));

    // A two-word option takes two slots from its key's slot on, like a record.
    let wide = run(&empty, "set_wide(uint256,uint256)", &[n(7), n(0)]);
    let base = map_key(n(7), n(1));
    assert_eq!(at(&wide, base), n(1));
    assert_eq!(at(&wide, base.wrapping_add(n(1))), n(0));
    assert_eq!(read(&wide, "wide_or(uint256)", &[n(7)]), n(0));
    assert_eq!(read(&wide, "wide_or(uint256)", &[n(8)]), n(1000));
    assert_eq!(read(&wide, "wide_passed(uint256)", &[n(7)]), n(0));
    assert_eq!(read(&wide, "wide_is_none(uint256)", &[n(7)]), n(0));
    assert_eq!(read(&wide, "wide_is_none(uint256)", &[n(8)]), n(1));
    assert_eq!(read(&wide, "wide_is(uint256,uint256)", &[n(7), n(0)]), n(1));
    assert_eq!(read(&wide, "wide_is(uint256,uint256)", &[n(7), n(1)]), n(0));
    assert_eq!(read(&wide, "wide_is(uint256,uint256)", &[n(8), n(0)]), n(0));
    let copied = run(&wide, "copy_wide(uint256,uint256)", &[n(7), n(9)]);
    assert_eq!(read(&copied, "wide_or(uint256)", &[n(9)]), n(0));
    let wiped = run(&copied, "copy_wide(uint256,uint256)", &[n(8), n(7)]);
    assert_eq!(at(&wiped, base), n(0));
    assert_eq!(read(&wiped, "wide_or(uint256)", &[n(7)]), n(1000));
    let wide = run(&wide, "set_wide(uint256,uint256)", &[n(7), n(5)]);
    let gone = run(&wide, "clear_wide(uint256)", &[n(7)]);
    assert_eq!(
        (at(&gone, base), at(&gone, base.wrapping_add(n(1)))),
        (n(0), n(0))
    );

    let nested = run(&empty, "set_nested(uint256,uint256)", &[n(3), n(4)]);
    assert_eq!(
        read(&nested, "nested_or(address,uint256)", &[n(1), n(3)]),
        n(4)
    );
    assert_eq!(
        read(&nested, "nested_or(address,uint256)", &[n(1), n(4)]),
        n(1000)
    );
    assert_eq!(
        read(&nested, "nested_or(address,uint256)", &[n(2), n(3)]),
        n(1000)
    );

    assert_eq!(read(&empty, "entry_sum(uint256)", &[n(1)]), n(0));
    let entry = run(&empty, "set_entry(uint256,uint256)", &[n(1), n(2)]);
    assert_eq!(read(&entry, "entry_sum(uint256)", &[n(1)]), n(52));
    let noted = run(&entry, "set_note(uint256,uint256)", &[n(1), n(3)]);
    assert_eq!(read(&noted, "entry_sum(uint256)", &[n(1)]), n(352));
    let expired = run(&noted, "clear_expiry(uint256)", &[n(1)]);
    assert_eq!(read(&expired, "entry_sum(uint256)", &[n(1)]), n(302));

    let pt = run(
        &empty,
        "set_pt(uint256,uint256,uint256)",
        &[n(1), n(2), n(3)],
    );
    assert_eq!(read(&pt, "pt_sum(uint256)", &[n(1)]), n(32));
    assert_eq!(read(&pt, "pt_sum(uint256)", &[n(2)]), n(1000));

    // Transient options start each transaction as `None`, and every slot is transient.
    let used = run_ok(&rt, &empty, "use_transient(uint256)", &[n(4)]);
    assert_eq!(slot(&used.storage, 5), n(3441));
    assert_eq!(used.storage.len(), 1);
    assert_eq!(read(&used.storage, "fresh_t()", &[]), n(0));
}

/// Lists of options: a two-word option takes two slots per element, in stored and local
/// lists alike, and a stored fixed list works through the storage image too.
#[test]
fn options_live_in_lists() {
    let src = include_str!("../examples/option_lists.lithe");
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let empty = HashMap::new();
    let read = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| read_ok(&rt, st, sig, args);
    let run =
        |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| run_ok(&rt, st, sig, args).storage;
    let reverts = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| {
        exec(&rt, &word_data(sig, args), st.clone(), n(1), n(0), n(0))
            .expect("exec")
            .reverted
    };
    let at = |st: &HashMap<Word, Word>, key: Word| st.get(&key).copied().unwrap_or(n(0));
    let elems = |slot: u64| Word::from_be_bytes(keccak256(&n(slot).to_be_bytes()));

    let small = run(&empty, "put_small(uint256,uint8)", &[n(0), n(0)]);
    assert_eq!(slot(&small, 0), n(1));
    assert_eq!(at(&small, elems(0)), n(0).not());
    assert_eq!(read(&small, "small_at(uint256)", &[n(0)]), n(0));
    assert!(reverts(&small, "small_at(uint256)", &[n(1)]));

    let wide = run(&empty, "put_wide(uint256,uint256)", &[n(0), n(5)]);
    let wide = run(&wide, "put_wide(uint256,uint256)", &[n(1), n(0)]);
    assert_eq!(slot(&wide, 1), n(2));
    let base = elems(1);
    assert_eq!(
        (at(&wide, base), at(&wide, base.wrapping_add(n(1)))),
        (n(1), n(5))
    );
    assert_eq!(at(&wide, base.wrapping_add(n(2))), n(1));
    assert_eq!(at(&wide, base.wrapping_add(n(3))), n(0));
    assert_eq!(read(&wide, "wide_at(uint256)", &[n(0)]), n(5));
    assert_eq!(read(&wide, "wide_at(uint256)", &[n(1)]), n(0));
    assert!(reverts(&wide, "put_wide(uint256,uint256)", &[n(3), n(1)]));
    let cleared = run(&wide, "clear_wide(uint256)", &[n(0)]);
    assert_eq!(read(&cleared, "wide_at(uint256)", &[n(0)]), n(1000));
    assert_eq!(read(&cleared, "wide_len()", &[]), n(2));

    let fixed = run(&empty, "put_fixed(uint256,uint256)", &[n(1), n(7)]);
    assert_eq!((slot(&fixed, 7), slot(&fixed, 8)), (n(1), n(7)));
    assert_eq!(slot(&fixed, 3), n(1).not());
    assert_eq!(slot(&fixed, 11), n(1));
    assert_eq!(read(&fixed, "fixed_at(uint256)", &[n(1)]), n(7));
    assert_eq!(read(&fixed, "fixed_at(uint256)", &[n(0)]), n(1000));
    assert!(reverts(&fixed, "fixed_at(uint256)", &[n(3)]));
    assert_eq!(read(&fixed, "fixed8_at(uint256)", &[n(1)]), n(1));
    assert_eq!(read(&fixed, "fixed8_at(uint256)", &[n(0)]), n(1000));
    assert_eq!(read(&fixed, "fixed_passed(uint256)", &[n(1)]), n(7));
    assert_eq!(read(&fixed, "fixed_is_none(uint256)", &[n(1)]), n(0));
    assert_eq!(read(&fixed, "fixed_is_none(uint256)", &[n(2)]), n(1));
    let moved = run(&fixed, "move_fixed(uint256,uint256)", &[n(1), n(2)]);
    assert_eq!(read(&moved, "fixed_at(uint256)", &[n(2)]), n(7));
    let wiped = run(&moved, "move_fixed(uint256,uint256)", &[n(0), n(1)]);
    assert_eq!((slot(&wiped, 7), slot(&wiped, 8)), (n(0), n(0)));
    let cleared = run(&wiped, "clear_fixed(uint256)", &[n(2)]);
    assert_eq!(read(&cleared, "fixed_at(uint256)", &[n(2)]), n(1000));

    // Through the storage image: written, read back after a query, and flushed.
    let image = run(
        &empty,
        "put_fixed_image(address,uint256,uint256)",
        &[n(2), n(2), n(9)],
    );
    assert_eq!((slot(&image, 9), slot(&image, 10)), (n(1), n(9)));
    assert_eq!(slot(&image, 11), n(9));
    let image = run(
        &image,
        "move_fixed_image(address,uint256,uint256)",
        &[n(2), n(2), n(0)],
    );
    assert_eq!((slot(&image, 5), slot(&image, 6)), (n(1), n(9)));
    assert_eq!(slot(&image, 11), n(2));

    assert_eq!(
        read(&empty, "locals(uint256,uint256)", &[n(0), n(5)]),
        n(5074)
    );
    assert_eq!(
        read(&empty, "locals(uint256,uint256)", &[n(1), n(5)]),
        n(109)
    );
    assert!(reverts(&empty, "locals(uint256,uint256)", &[n(2), n(5)]));
}

#[test]
fn collections_live_in_storage() {
    let src = include_str!("../examples/collections.lithe");
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let caller = Word::from_u64(1);
    let first = call(&runtime, "deposit(uint256)", &[Word::from_u64(5)]);
    assert!(!first.reverted, "{}", pretty(&first.returndata));
    assert_eq!(slot(&first.storage, 1), Word::from_u64(5));
    assert_eq!(
        first.storage.get(&map_key(caller, Word::from_u64(0))),
        Some(&Word::from_u64(5))
    );
    let second = exec(
        &runtime,
        &word_data("deposit(uint256)", &[Word::from_u64(2)]),
        first.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("deposit");
    assert!(!second.reverted, "{}", pretty(&second.returndata));
    assert_eq!(slot(&second.storage, 1), Word::from_u64(7));

    let noted = call(&runtime, "note()", &[]);
    assert!(!noted.reverted, "{}", pretty(&noted.returndata));
    assert_eq!(slot(&noted.storage, 2), Word::from_u64(1));
    let head = exec(
        &runtime,
        &word_data("first()", &[]),
        noted.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("first");
    assert!(!head.reverted, "{}", pretty(&head.returndata));
    assert_eq!(load_bytes(&head.returndata, 0), caller);

    let filled = call(&runtime, "fill()", &[]);
    assert!(!filled.reverted, "{}", pretty(&filled.returndata));
    assert_eq!(slot(&filled.storage, 4), Word::from_u64(7));
    let read = call(&runtime, "slot1()", &[]);
    assert!(!read.reverted, "{}", pretty(&read.returndata));
    assert_eq!(load_bytes(&read.returndata, 0), Word::from_u64(0));
    let kept = exec(
        &runtime,
        &word_data("slot1()", &[]),
        filled.storage,
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("slot");
    assert_eq!(load_bytes(&kept.returndata, 0), Word::from_u64(7));

    let fresh = call(&runtime, "admin_or_sender()", &[]);
    assert_eq!(load_bytes(&fresh.returndata, 0), caller);
    let appointed = call(&runtime, "appoint()", &[]);
    assert!(!appointed.reverted, "{}", pretty(&appointed.returndata));
    // A narrow payload shares its option's one slot: `Some(x)` is stored as `NOT x`.
    assert_eq!(slot(&appointed.storage, 7), caller.not());
    assert_eq!(slot(&appointed.storage, 8), Word::from_u64(0));
    let admin = exec(
        &runtime,
        &word_data("admin_or_sender()", &[]),
        appointed.storage,
        Word::from_u64(9),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("admin");
    assert_eq!(load_bytes(&admin.returndata, 0), caller);

    let missed = call(&runtime, "miss()", &[]);
    assert!(missed.reverted);
    assert_eq!(load_bytes(&missed.returndata, 4), Word::from_u64(0x32));
    let ctx = call(&runtime, "context()", &[]);
    assert!(!ctx.reverted, "{}", pretty(&ctx.returndata));
    assert_eq!(load_bytes(&ctx.returndata, 0), Word::from_u64(101));
}

#[test]
fn loops_run_bounded_work() {
    let src = include_str!("../examples/loops.lithe");
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;

    let tri = call(&runtime, "triangle(uint256)", &[w(5)]);
    assert!(!tri.reverted, "{}", pretty(&tri.returndata));
    assert_eq!(slot(&tri.storage, 0), w(10));
    let none = call(&runtime, "triangle(uint256)", &[w(0)]);
    assert!(!none.reverted);
    assert_eq!(slot(&none.storage, 0), w(0));

    let weighted = call(&runtime, "weighted(uint256[3])", &[w(1), w(2), w(3)]);
    assert!(!weighted.reverted, "{}", pretty(&weighted.returndata));
    assert_eq!(slot(&weighted.storage, 0), w(14));

    let grid = call(&runtime, "grid(uint256)", &[w(3)]);
    assert!(!grid.reverted, "{}", pretty(&grid.returndata));
    assert_eq!(slot(&grid.storage, 0), w(9));

    let gcd = call(&runtime, "euclid(uint256,uint256)", &[w(48), w(18)]);
    assert!(!gcd.reverted, "{}", pretty(&gcd.returndata));
    assert_eq!(slot(&gcd.storage, 1), w(6));
    let zero_steps = call(&runtime, "euclid(uint256,uint256)", &[w(7), w(0)]);
    assert_eq!(slot(&zero_steps.storage, 1), w(7));

    // A storage list: three members marked, and a search that stops early.
    let mut storage = HashMap::new();
    for who in [w(0xa1), w(0xa2), w(0xa3)] {
        let joined = exec(&runtime, &word_data("join(address)", &[who]), storage, w(1), w(0), w(0))
            .expect("join");
        assert!(!joined.reverted, "{}", pretty(&joined.returndata));
        storage = joined.storage;
    }
    let marked = exec(&runtime, &word_data("mark_all()", &[]), storage.clone(), w(1), w(0), w(0))
        .expect("mark");
    assert!(!marked.reverted, "{}", pretty(&marked.returndata));
    for who in [w(0xa1), w(0xa2), w(0xa3)] {
        assert_eq!(marked.storage.get(&map_key(who, w(4))), Some(&w(1)), "{who:?}");
    }
    let found = exec(&runtime, &word_data("find(address)", &[w(0xa2)]), storage.clone(), w(1), w(0), w(0))
        .expect("find");
    assert!(!found.reverted, "{}", pretty(&found.returndata));
    assert_eq!(slot(&found.storage, 2), w(2));
    let missing = exec(&runtime, &word_data("find(address)", &[w(0xa9)]), storage.clone(), w(1), w(0), w(0))
        .expect("find");
    assert_eq!(slot(&missing.storage, 2), w(0));

    // Past the bound, the loop panics before it starts.
    for who in [w(0xa4), w(0xa5)] {
        let joined = exec(&runtime, &word_data("join(address)", &[who]), storage, w(1), w(0), w(0))
            .expect("join");
        storage = joined.storage;
    }
    let too_many = exec(&runtime, &word_data("mark_all()", &[]), storage, w(1), w(0), w(0))
        .expect("mark");
    assert!(too_many.reverted);
    assert_eq!(load_bytes(&too_many.returndata, 4), w(0x01));

    // One event and one transfer per recipient, in order, after the storage write.
    let paid = exec(
        &runtime,
        &word_data("pay(address[2],uint256[2])", &[w(0xb1), w(0xb2), w(5), w(7)]),
        HashMap::new(),
        w(1),
        w(0),
        w(100),
    )
    .expect("pay");
    assert!(!paid.reverted, "{}", pretty(&paid.returndata));
    assert_eq!(slot(&paid.storage, 7), w(12));
    let logs = paid.trace.iter().filter(|ev| matches!(ev, Ev::Log { .. })).count();
    assert_eq!(logs, 2, "{:?}", paid.trace);
    let calls: Vec<(Word, Word)> = paid
        .trace
        .iter()
        .filter_map(|ev| match ev {
            Ev::Call { to, value } => Some((*to, *value)),
            _ => None,
        })
        .collect();
    assert_eq!(calls, vec![(w(0xb1), w(5)), (w(0xb2), w(7))], "{:?}", paid.trace);
    let store_then_call = paid
        .trace
        .iter()
        .position(|ev| matches!(ev, Ev::Call { .. }))
        .expect("call");
    assert!(
        paid.trace[..store_then_call]
            .iter()
            .any(|ev| matches!(ev, Ev::SStore { .. })),
        "{:?}",
        paid.trace
    );

    // Each continuation sees its own iteration's index. The echo mock returns its argument.
    install_mocks();
    let set = call(&runtime, "set_exchange(address)", &[w(0xcd)]);
    assert!(!set.reverted, "{}", pretty(&set.returndata));
    let swapped = exec(
        &runtime,
        &word_data("swap_all(uint256[2])", &[w(11), w(22)]),
        set.storage,
        w(1),
        w(0),
        w(0),
    )
    .expect("swap_all");
    assert!(!swapped.reverted, "{}", pretty(&swapped.returndata));
    assert_eq!(swapped.storage.get(&map_key(w(0), w(6))), Some(&w(11)));
    assert_eq!(swapped.storage.get(&map_key(w(1), w(6))), Some(&w(22)));
    let swaps = swapped
        .trace
        .iter()
        .filter(|ev| matches!(ev, Ev::Call { to, .. } if *to == w(0xcd)))
        .count();
    assert_eq!(swaps, 2, "{:?}", swapped.trace);
}

#[test]
fn braces_group_records_blocks_and_cases() {
    let src = include_str!("../examples/brackets.lithe");
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let first = call(&runtime, "first_admin()", &[]);
    assert!(!first.reverted, "{}", pretty(&first.returndata));
    assert_eq!(load_bytes(&first.returndata, 0), Word::from_u64(1));
    let count = call(&runtime, "admin_count()", &[]);
    assert!(!count.reverted, "{}", pretty(&count.returndata));
    assert_eq!(load_bytes(&count.returndata, 0), Word::from_u64(2));
    let second = call(&runtime, "second()", &[]);
    assert!(!second.reverted, "{}", pretty(&second.returndata));
    assert_eq!(load_bytes(&second.returndata, 0), Word::from_u64(2));
    let owed = call(&runtime, "owed()", &[]);
    assert!(!owed.reverted, "{}", pretty(&owed.returndata));
    assert_eq!(load_bytes(&owed.returndata, 0), Word::from_u64(9));

    let paid = call(&runtime, "pay(uint256)", &[Word::from_u64(5)]);
    assert!(!paid.reverted, "{}", pretty(&paid.returndata));
    assert_eq!(slot(&paid.storage, 0), Word::from_u64(5));
    assert!(paid.trace.iter().any(|ev| matches!(ev, Ev::Log { .. })));

    let old = compile("storage is record [ n : nat; ]\nexternal function go() is { skip }\n");
    let err = old.expect_err("square record").to_string();
    assert!(err.contains("`{`"), "{err}");

    let bare_case = compile(
        "storage is record { n : nat; }\nexternal function go() is\n  case storage.n of\n  | _ -> skip\n  end\n",
    );
    let err = bare_case.expect_err("bare case").to_string();
    assert!(err.contains("`{`"), "{err}");

    let short = "\
storage is record { n : nat; }
external view function go() : nat is {
  const nums : list(nat, 2) := [1n];
} with nums[0]
";
    let err = compile(short).expect_err("short list").to_string();
    assert!(
        err.contains("list has 1 element and the type has 2"),
        "{err}"
    );

    let past = "\
storage is record { n : nat; }
external view function go() : address is {
  const alice : address := 0x01;
  const admins : list(address) := [alice];
} with admins[1]
";
    let runtime = deploy(&compile(past).expect("compile")).expect("deploy");
    let missed = call(&runtime, "go()", &[]);
    assert!(missed.reverted);
    assert_eq!(load_bytes(&missed.returndata, 4), Word::from_u64(0x32));
}

#[test]
fn indexed_events_split_topics_and_data() {
    let src = include_str!("../examples/events.lithe");
    let abi = crate::abi(src).expect("abi");
    assert!(
        abi.contains("\"name\": \"from\"") && abi.contains("\"indexed\": true"),
        "{abi}"
    );
    assert!(abi.contains("\"name\": \"amount\""), "{abi}");
    assert!(abi.contains("\"indexed\": false"), "{abi}");
    let tree = crate::abi_tree(src).expect("tree");
    assert!(
        tree.contains("Transfer(indexed from, indexed to, amount)"),
        "{tree}"
    );
    assert!(tree.contains("Note(indexed hash memo, amount)"), "{tree}");
    assert!(
        tree.contains("Tagged(indexed flag, indexed hash ids, amount)"),
        "{tree}"
    );

    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let to = Word::from_u64(2);
    let paid = call(&runtime, "pay(address,uint256)", &[to, Word::from_u64(5)]);
    assert!(!paid.reverted, "{}", pretty(&paid.returndata));
    assert_eq!(slot(&paid.storage, 0), Word::from_u64(5));
    let logs: Vec<&[Word]> = paid
        .trace
        .iter()
        .filter_map(|ev| match ev {
            Ev::Log { topics } => Some(topics.as_slice()),
            _ => None,
        })
        .collect();
    assert_eq!(logs.len(), 3, "{:?}", paid.trace);
    let transfer = crate::keccak::keccak256(b"Transfer(address,address,uint256)");
    assert_eq!(logs[0][0], Word::from_be_bytes(transfer));
    assert_eq!(logs[0][1], Word::from_u64(1));
    assert_eq!(logs[0][2], to);
    let note = crate::keccak::keccak256(b"Note(string,uint256)");
    assert_eq!(logs[1][0], Word::from_be_bytes(note));
    assert_eq!(
        logs[1][1],
        Word::from_be_bytes(crate::keccak::keccak256(b"hi"))
    );
    let tagged = crate::keccak::keccak256(b"Tagged(bool,uint256[2],uint256)");
    assert_eq!(logs[2][0], Word::from_be_bytes(tagged));
    assert_eq!(logs[2][1], Word::from_u64(1));
    let mut preimage = [0u8; 64];
    preimage[..32].copy_from_slice(&Word::from_u64(7).to_be_bytes());
    preimage[32..].copy_from_slice(&Word::from_u64(8).to_be_bytes());
    assert_eq!(
        logs[2][2],
        Word::from_be_bytes(crate::keccak::keccak256(&preimage))
    );
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

#[test]
fn strings_and_dynamic_bytes_use_short_slots() {
    let src = include_str!("../examples/text.lithe");
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let remembered = call(&runtime, "remember()", &[]);
    assert!(!remembered.reverted, "{}", pretty(&remembered.returndata));
    assert_eq!(slot(&remembered.storage, 0), Word::short_dyn(b"Lithe"));
    assert_eq!(
        slot(&remembered.storage, 1),
        Word::short_dyn(&[0x61, 0x62, 0x63])
    );
    let shown = exec(
        &runtime,
        &word_data("name()", &[]),
        remembered.storage.clone(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("name");
    assert!(!shown.reverted, "{}", pretty(&shown.returndata));
    assert_eq!(load_bytes(&shown.returndata, 0), Word::from_u64(32));
    assert_eq!(load_bytes(&shown.returndata, 32), Word::from_u64(5));
    let mut lithe = [0u8; 32];
    lithe[..5].copy_from_slice(b"Lithe");
    assert_eq!(
        load_bytes(&shown.returndata, 64),
        Word::from_be_bytes(lithe)
    );

    let labeled = exec(
        &runtime,
        &abi_string("label(string)", b"Hi"),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("label");
    assert!(!labeled.reverted, "{}", pretty(&labeled.returndata));
    assert_eq!(slot(&labeled.storage, 0), Word::short_dyn(b"Hi"));

    let long = "storage is record { x : nat; }\nexternal function f() is {\n  const s : string := \"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\";\n}\n";
    let err = compile(long).expect_err("long string");
    assert!(
        err.to_string()
            .contains("a string must be at most 31 bytes"),
        "{err}"
    );
}

/// Sending ether is `Evm.transfer`, like every other built-in reached through its module.
/// A bare `transfer` is an ordinary name, free for a contract's own function.
/// `Nat.mul_div` keeps the full 512-bit product, as OpenZeppelin's `Math.mulDiv` does;
/// `Nat.mul_mod` and `Nat.add_mod` are the EVM's modular operations.
#[test]
fn full_precision_arithmetic() {
    let src = "\
storage is record { n : nat; }
external pure function mul_div(const a : nat; const b : nat; const d : nat) : nat is Nat.mul_div(a, b, d)
external pure function mul_mod(const a : nat; const b : nat; const d : nat) : nat is Nat.mul_mod(a, b, d)
external pure function add_mod(const a : nat; const b : nat; const d : nat) : nat is Nat.add_mod(a, b, d)
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let hexw = |s: &str| {
        let s = s.trim_start_matches("0x");
        let mut bytes = [0u8; 32];
        let padded = format!("{s:0>64}");
        for (i, b) in bytes.iter_mut().enumerate() {
            *b = u8::from_str_radix(&padded[2 * i..2 * i + 2], 16).unwrap();
        }
        Word::from_be_bytes(bytes)
    };
    let max = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    let max1 = "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe";
    // (a, b, d, a * b / d or None when it overflows, a * b % d, (a + b) % d)
    let cases: &[(&str, &str, &str, Option<&str>, &str, &str)] = &[
        ("a", "14", "3", Some("42"), "2", "0"),
        (max, max, max, Some(max), "0", "0"),
        (max, max1, max, Some(max1), "0", max1),
        (
            "100000000000000000000000000000000000000000000000000",
            "10000000000000000000000000",
            "1000000000000000",
            Some("1000000000000000000000000000000000000000000000000000000000000"),
            "0",
            "0",
        ),
        (
            max,
            "3",
            "7",
            Some("6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6"),
            "3",
            "4",
        ),
        (
            "8000000000000000000000000000000000000000000000000000000000000000",
            "2",
            "8000000000000000000000000000000000000000000000000000000000000001",
            Some("1"),
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            "1",
        ),
        (max, "2", "1", None, "0", "0"),
    ];
    let run = |sig: &str, args: &[Word]| {
        exec(
            &runtime,
            &word_data(sig, args),
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect(sig)
    };
    for &(a, b, d, q, m, s) in cases {
        let args = [hexw(a), hexw(b), hexw(d)];
        let out = run("mul_div(uint256,uint256,uint256)", &args);
        match q {
            Some(q) => {
                assert!(!out.reverted, "{a} {b} {d}: {}", pretty(&out.returndata));
                assert_eq!(load_bytes(&out.returndata, 0), hexw(q), "{a} * {b} / {d}");
            }
            None => {
                assert!(out.reverted);
                assert_eq!(load_bytes(&out.returndata, 4), Word::from_u64(0x11));
            }
        }
        assert_eq!(
            load_bytes(
                &run("mul_mod(uint256,uint256,uint256)", &args).returndata,
                0
            ),
            hexw(m)
        );
        assert_eq!(
            load_bytes(
                &run("add_mod(uint256,uint256,uint256)", &args).returndata,
                0
            ),
            hexw(s)
        );
    }
    for sig in [
        "mul_div(uint256,uint256,uint256)",
        "mul_mod(uint256,uint256,uint256)",
        "add_mod(uint256,uint256,uint256)",
    ] {
        for a in ["5", max] {
            let out = run(sig, &[hexw(a), hexw(a), hexw("0")]);
            assert!(out.reverted, "{sig} by zero");
            assert_eq!(
                load_bytes(&out.returndata, 4),
                Word::from_u64(0x12),
                "{sig}"
            );
        }
    }
}

/// `Bytes.word` reads 32 bytes at any offset; `bytesN` and `address` convert exactly to and
/// from the unsigned integer of their width.
#[test]
fn byte_words_and_width_conversions() {
    let src = "\
storage is record { n : nat; }
external pure function word(const b : bytes; const offset : nat) : bytes32 is Bytes.word(b, offset)
external pure function widths(const h : bytes32; const s : bytes4) : (nat, address, uint32, bytes32) is
  (nat(h), address(uint160(nat(h) & ((1n << 160n) - 1n))), uint32(s), bytes32(nat(h) + 1n))
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let data: Vec<u8> = (0u8..70).collect();
    let call = |at: u64, data: &[u8]| {
        let mut c = selector("word(bytes,uint256)").to_vec();
        for word in [w(64), w(at), w(data.len() as u64)] {
            c.extend_from_slice(&word.to_be_bytes());
        }
        c.extend_from_slice(data);
        c.resize(4 + (c.len() - 4).div_ceil(32) * 32, 0);
        exec(&runtime, &c, HashMap::new(), w(1), w(0), w(0)).expect("word")
    };
    for at in [0u64, 1, 33, 38] {
        let out = call(at, &data);
        assert!(!out.reverted, "{at}");
        assert_eq!(
            &out.returndata[..32],
            &data[at as usize..at as usize + 32],
            "{at}"
        );
    }
    for (at, data) in [(39u64, &data[..]), (0, &data[..31]), (u64::MAX, &data[..])] {
        let out = call(at, data);
        assert!(out.reverted, "{at} of {}", data.len());
        assert_eq!(load_bytes(&out.returndata, 4), w(0x32));
    }
    let mut h = [0u8; 32];
    h[0] = 0xaa;
    h[12..].copy_from_slice(&[0x11; 20]);
    let mut c = selector("widths(bytes32,bytes4)").to_vec();
    c.extend_from_slice(&h);
    let mut s4 = [0u8; 32];
    s4[..4].copy_from_slice(&[0xde, 0xad, 0xbe, 0xef]);
    c.extend_from_slice(&s4);
    let out = exec(&runtime, &c, HashMap::new(), w(1), w(0), w(0)).expect("widths");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(load_bytes(&out.returndata, 0), Word::from_be_bytes(h));
    let mut addr = [0u8; 32];
    addr[12..].copy_from_slice(&[0x11; 20]);
    assert_eq!(load_bytes(&out.returndata, 32), Word::from_be_bytes(addr));
    assert_eq!(load_bytes(&out.returndata, 64), w(0xdeadbeef));
    h[31] += 1;
    assert_eq!(load_bytes(&out.returndata, 96), Word::from_be_bytes(h));
}

#[test]
fn transfer_lives_in_evm() {
    for (body, want) in [
        (
            "defer transfer(Evm.sender(), 1wei);",
            "unknown function `transfer`",
        ),
        (
            "defer Evm.transfer(Evm.sender());",
            "`Evm.transfer` expects 2 arguments",
        ),
        (
            "defer Evm.transfer(Evm.sender(), 1n);",
            "argument has the wrong type",
        ),
    ] {
        let src =
            format!("storage is record {{ n : nat; }}\nexternal function f() is {{ {body} }}\n");
        let err = compile(&src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    let view = "storage is record { n : nat; }\nexternal view function f() : nat is {\n  defer Evm.transfer(Evm.sender(), 1wei);\n} with 1n\n";
    let err = compile(view).expect_err("view");
    assert!(err.to_string().contains("weaker"), "{err}");

    let own = "\
storage is record { balances : map(address, nat); }
external function transfer(const to : address; const amount : nat) is {
  storage.balances[to] := storage.balances[to] + amount;
}
external view function balance_of(const who : address) : nat is storage.balances[who]
";
    let runtime = deploy(&compile(own).expect("own transfer")).expect("deploy");
    let w = Word::from_u64;
    let out = exec(
        &runtime,
        &word_data("transfer(address,uint256)", &[w(0xb0b), w(3)]),
        HashMap::new(),
        w(7),
        w(0),
        w(0),
    )
    .expect("transfer");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
}

#[test]
fn builtins_are_explicit_modules() {
    let layout = leaves(include_str!("../examples/builtins.lithe"));
    let src = include_str!("../examples/builtins.lithe");
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let caller = Word::from_u64(1);
    let out = exec(
        &runtime,
        &word_data("take()", &[]),
        HashMap::new(),
        caller,
        Word::from_u64(5),
        Word::from_u64(9),
    )
    .expect("take");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(layout.get(&out.storage, 0), caller);
    assert_eq!(layout.get(&out.storage, 1), Word::from_u64(5));
    assert_eq!(layout.get(&out.storage, 2), Word::from_u64(1_700_000_000));
    assert_eq!(layout.get(&out.storage, 3), Word::from_u64(100));
    assert_eq!(layout.get(&out.storage, 4), Word::from_u64(1));
    assert_eq!(layout.get(&out.storage, 5), Word::from_u64(0x1000));
    assert_eq!(layout.get(&out.storage, 6), Word::from_u64(9));
    let mut sel = [0u8; 32];
    sel[28..].copy_from_slice(&selector("take()"));
    assert_eq!(layout.get(&out.storage, 7), Word::from_be_bytes(sel));
    assert_eq!(layout.get(&out.storage, 8), Word::from_u64(0x0a));
    assert_eq!(layout.get(&out.storage, 9), Word::from_u64(1_000_000_000));
    assert_eq!(layout.get(&out.storage, 10), Word::from_u64(0x0b));
    assert_eq!(layout.get(&out.storage, 11), Word::from_u64(1_000_000_000));
    assert_eq!(layout.get(&out.storage, 12), Word::from_u64(0x1234));
    assert_eq!(layout.get(&out.storage, 13), Word::from_u64(30_000_000));
    assert!(layout.get(&out.storage, 14).0[0] > 0);
    assert_eq!(
        layout.get(&out.storage, 19),
        Word::from_be_bytes(crate::keccak::keccak256(b"abc"))
    );
    assert_eq!(
        layout.get(&out.storage, 20),
        Word::from_be_bytes(crate::hash::sha256(b"abc"))
    );
    let ripe = crate::hash::ripemd160(b"abc");
    let mut ripe_word = [0u8; 32];
    ripe_word[12..].copy_from_slice(&ripe);
    assert_eq!(layout.get(&out.storage, 21), Word::from_be_bytes(ripe_word));
    assert_eq!(layout.get(&out.storage, 22), Word::from_u64(7));
    assert_eq!(
        layout.get(&out.storage, 15),
        Word::from_be_bytes(crate::keccak::keccak256(&runtime))
    );
    assert_eq!(layout.get(&out.storage, 18), Word::from_u64(1_000_000));
    assert_eq!(
        layout.get(&out.storage, 16),
        Word::from_be_bytes(crate::keccak::keccak256(&Word::from_u64(1).to_be_bytes()))
    );
    assert_eq!(
        layout.get(&out.storage, 17),
        Word::from_be_bytes(crate::keccak::keccak256(b"blob"))
    );
    let mut packed = [0u8; 32];
    packed[19] = 1;
    packed[31] = 40;
    assert_eq!(layout.get(&out.storage, 23), Word::from_be_bytes(packed));
    let data = call(&runtime, "payload()", &[]);
    assert!(!data.reverted, "{}", pretty(&data.returndata));
    assert_eq!(load_bytes(&data.returndata, 32), Word::from_u64(4));
    let framed = call(&runtime, "framed()", &[]);
    assert!(!framed.reverted, "{}", pretty(&framed.returndata));
    assert_eq!(load_bytes(&framed.returndata, 32), Word::from_u64(36));
    assert_eq!(&framed.returndata[64..68], &[0xaa, 0xbb, 0xcc, 0xdd]);
    assert_eq!(load_bytes(&framed.returndata, 68), Word::from_u64(7));
    let sig = crate::keccak::keccak256(b"foo(uint256)");
    let signed = call(&runtime, "signed()", &[]);
    assert!(!signed.reverted, "{}", pretty(&signed.returndata));
    assert_eq!(&signed.returndata[64..68], &sig[..4]);
    assert_eq!(load_bytes(&signed.returndata, 68), Word::from_u64(7));
    let called = call(&runtime, "called()", &[]);
    assert_eq!(called.returndata, signed.returndata);
    let who = call(&runtime, "recovered()", &[]);
    assert!(!who.reverted, "{}", pretty(&who.returndata));
    assert_eq!(load_bytes(&who.returndata, 0), Word::from_u64(0));
    let bare = "storage is record { x : nat; }\nexternal function f() is { const a : address := sender; }\n";
    let err = compile(bare).expect_err("bare sender");
    assert!(err.to_string().contains("use `Evm.sender()`"), "{err}");
}

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

#[test]
fn counter_abi_tree_matches_the_dispatch() {
    let tree = crate::abi_tree(COUNTER).expect("abi-tree");
    assert_eq!(
        tree,
        "\
reset
  path:
    main -> owner_main -> reset

  calls:
    none

  guards:
    - Evm.sender() = storage.owner

  storage reads:
    - storage.owner
    - storage.count

  storage writes:
    - storage.count

  queries:
    none

  events:
    - Count_changed

  operations:
    none

  raises:
    - InvalidOwnerAccess()

increment
  path:
    main -> public_main -> increment

  calls:
    - add

  guards:
    none

  storage reads:
    - storage.count

  storage writes:
    - storage.count

  queries:
    none

  events:
    - Count_changed

  operations:
    none

  raises:
    none
"
    );
}

fn trace_kinds(trace: &[Ev]) -> Vec<&str> {
    trace
        .iter()
        .map(|e| match e {
            Ev::Static { .. } => "static",
            Ev::SStore { .. } => "sstore",
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

#[test]
fn bank_abi_is_solidity_json() {
    let abi = crate::abi(BANK).expect("abi");
    assert_eq!(abi, BANK_ABI);
}

const BANK_ABI: &str = r#"[
  {
    "inputs": [
      {
        "internalType": "uint256",
        "name": "amount",
        "type": "uint256"
      }
    ],
    "name": "withdraw",
    "outputs": [],
    "stateMutability": "nonpayable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "internalType": "bool",
        "name": "value",
        "type": "bool"
      }
    ],
    "name": "set_pause",
    "outputs": [],
    "stateMutability": "nonpayable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "internalType": "bytes4",
        "name": "interfaceId",
        "type": "bytes4"
      }
    ],
    "name": "supportsInterface",
    "outputs": [
      {
        "internalType": "bool",
        "name": "",
        "type": "bool"
      }
    ],
    "stateMutability": "pure",
    "type": "function"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "account",
        "type": "address"
      },
      {
        "indexed": false,
        "internalType": "uint256",
        "name": "amount",
        "type": "uint256"
      }
    ],
    "name": "Withdrawal",
    "type": "event"
  },
  {
    "inputs": [],
    "name": "NotOwner",
    "type": "error"
  },
  {
    "inputs": [],
    "name": "Paused",
    "type": "error"
  },
  {
    "inputs": [
      {
        "internalType": "uint256",
        "name": "available",
        "type": "uint256"
      },
      {
        "internalType": "uint256",
        "name": "required",
        "type": "uint256"
      }
    ],
    "name": "InsufficientBalance",
    "type": "error"
  },
  {
    "inputs": [
      {
        "internalType": "uint256",
        "name": "",
        "type": "uint256"
      }
    ],
    "name": "InvalidAmount",
    "type": "error"
  }
]
"#;

#[test]
fn counter_abi_flattens_dispatch_and_views() {
    let abi = crate::abi(COUNTER).expect("abi");
    assert!(abi.contains("\"name\": \"reset\""), "{abi}");
    assert!(abi.contains("\"name\": \"increment\""), "{abi}");
    assert!(abi.contains("\"name\": \"n\""), "{abi}");
    assert!(abi.contains("\"name\": \"get_count\""), "{abi}");
    assert!(abi.contains("\"stateMutability\": \"view\""), "{abi}");
    assert!(abi.contains("\"stateMutability\": \"nonpayable\""), "{abi}");
    assert!(!abi.contains("\"stateMutability\": \"payable\""), "{abi}");
    assert!(abi.contains("\"name\": \"Count_changed\""), "{abi}");
    assert!(abi.contains("\"name\": \"InvalidOwnerAccess\""), "{abi}");
    assert!(abi.contains("\"indexed\": false"), "{abi}");
}

#[test]
fn directory_compile_writes_bytecode_and_abi() {
    let dir = std::env::temp_dir().join(format!("lithe-compile-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("temp");
    let nested = dir.join("nested");
    std::fs::create_dir_all(&nested).expect("nested");
    std::fs::write(nested.join("skip.lithe"), PAY).expect("skip");
    std::fs::write(dir.join("pay.lithe"), PAY).expect("pay");
    std::fs::write(dir.join("bad.lithe"), "nope\n").expect("bad");

    let out_dir = dir.join("out");
    let out = crate::compile_dir(&dir, &out_dir).expect("compile dir");
    let msgs: Vec<_> = out.failed.iter().map(ToString::to_string).collect();
    assert_eq!(msgs.len(), 1, "{msgs:?}");
    assert!(msgs[0].contains("bad.lithe"), "{msgs:?}");
    let code = compile(PAY).expect("pay code");
    let artifact =
        std::fs::read_to_string(out_dir.join("pay.lithe").join("Pay.json")).expect("artifact");
    assert!(artifact.contains("\"contractName\": \"Pay\""), "{artifact}");
    let creation = hex_bytes(&code);
    let runtime = hex_bytes(&code[crate::gen::INIT_BYTES..]);
    assert!(
        artifact.contains(&format!(
            "\"bytecode\": {{\n    \"object\": \"0x{creation}\""
        )),
        "{artifact}"
    );
    assert!(
        artifact.contains(&format!(
            "\"deployedBytecode\": {{\n    \"object\": \"0x{runtime}\""
        )),
        "{artifact}"
    );
    let sel = selector("pay(address)");
    assert!(
        artifact.contains(&format!(
            "\"pay(address)\": \"{:02x}{:02x}{:02x}{:02x}\"",
            sel[0], sel[1], sel[2], sel[3]
        )),
        "{artifact}"
    );
    assert!(!dir.join("pay.bin").exists());
    assert!(!dir.join("pay.json").exists());
    assert!(!dir.join("pay.abi.json").exists());
    assert!(!out_dir.join("skip.lithe").exists());

    let abi_only = dir.join("abi-only");
    std::fs::create_dir_all(&abi_only).expect("abi-only");
    std::fs::write(abi_only.join("pay.lithe"), PAY).expect("pay");
    let abi_out = dir.join("abi-out");
    let out = crate::abi_dir(&abi_only, &abi_out).expect("abi dir");
    assert!(out.failed.is_empty());
    let abi = std::fs::read_to_string(abi_out.join("pay.lithe").join("Pay.abi.json")).expect("abi");
    assert_eq!(abi, crate::abi(PAY).expect("pay abi"));
    assert!(!abi_only.join("pay.abi.json").exists());
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn explicit_contracts_are_braced_and_separate() {
    let braced = "\
module Counter is {
  function step(const n : nat) : nat is
    n + 1n
}

contract Vault is {
  use Counter;

  storage is record { n : nat; }

  external function go() is {
    storage.n := Counter.step(1n);
  }
}

contract Factory is {
  use Counter;

  storage is record { n : nat; }

  external function make() is {
    storage.n := Counter.step(2n);
  }
}
";
    let err = compile(braced).expect_err("two contracts");
    assert!(
        err.to_string()
            .contains("this file defines `Vault`, `Factory`"),
        "{err}"
    );
    assert!(
        err.to_string()
            .contains("one bytecode needs a single contract"),
        "{err}"
    );
    let old = compile("module M is\nend\n").expect_err("old module");
    assert!(old.to_string().contains("`{`"), "{old}");
    let stray = compile(
        "contract Foo is {\n  storage is record { n : nat; }\n}\nexternal function go() is { skip }\n",
    )
    .expect_err("stray");
    assert!(
        stray
            .to_string()
            .contains("move this declaration inside a contract"),
        "{stray}"
    );

    let dir = std::env::temp_dir().join(format!("lithe-contracts-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("temp");
    std::fs::write(dir.join("shops.lithe"), braced).expect("shops");
    let one = "\
contract Vault is {
  storage is record { n : nat; }
  external function claim() is { storage.n := 1n; }
}
";
    std::fs::write(dir.join("named.lithe"), one).expect("named");
    let out_dir = dir.join("out");
    let out = crate::compile_dir(&dir, &out_dir).expect("dir");
    let failed: Vec<_> = out.failed.iter().map(ToString::to_string).collect();
    assert!(failed.is_empty(), "{failed:?}");
    let vault =
        std::fs::read_to_string(out_dir.join("shops.lithe").join("Vault.json")).expect("vault");
    let factory =
        std::fs::read_to_string(out_dir.join("shops.lithe").join("Factory.json")).expect("factory");
    assert!(vault.contains("\"contractName\": \"Vault\""), "{vault}");
    assert!(
        factory.contains("\"contractName\": \"Factory\""),
        "{factory}"
    );
    assert!(vault.contains("\"name\": \"go\""), "{vault}");
    assert!(!vault.contains("\"name\": \"make\""), "{vault}");
    assert!(factory.contains("\"name\": \"make\""), "{factory}");
    assert!(!factory.contains("\"name\": \"go\""), "{factory}");
    let named =
        std::fs::read_to_string(out_dir.join("named.lithe").join("Vault.json")).expect("named");
    assert!(named.contains("\"contractName\": \"Vault\""), "{named}");
    assert!(!out_dir.join("named.lithe").join("Named.json").exists());
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn payable_is_explicit_on_entries() {
    let err = compile(
        "storage is record { n : nat; }\nexternal function go() is { const x : wei := Evm.value(); }\n",
    )
    .expect_err("value");
    assert!(
        err.to_string().contains(
            "external function `go` reads `Evm.value()`; write `external payable function`"
        ),
        "{err}"
    );
    for (src, want) in [
        (
            "payable function go() is { skip }\n",
            "payable functions must be external; write `external payable function`",
        ),
        (
            "external payable view function go() : nat is 0n\n",
            "payable functions must be stateful",
        ),
        (
            "view external function go() : nat is 0n\n",
            "keywords out of order; write `external view function`",
        ),
        (
            "payable external function go() is { skip }\n",
            "keywords out of order; write `external payable function`",
        ),
    ] {
        let err = compile(src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    let runtime = deploy(&compile(COUNTER).expect("counter")).expect("deploy");
    let mut storage = HashMap::new();
    storage.insert(Word::from_u64(1), Word::from_u64(0xab));
    let rejected = exec(
        &runtime,
        &word_data("increment(uint256)", &[Word::from_u64(1)]),
        storage,
        Word::from_u64(0xab),
        Word::from_u64(1),
        Word::from_u64(1),
    )
    .expect("value");
    assert!(rejected.reverted, "nonzero value must revert");
    let abi = crate::abi(PAY).expect("pay abi");
    assert!(abi.contains("\"stateMutability\": \"payable\""), "{abi}");
}

#[test]
fn types_reject_implicit_conversions() {
    let err = compile("type storage is record { n : nat; }\nexternal function go() is { skip }\n")
        .expect_err("syntax");
    assert!(
        err.to_string()
            .contains("declare contract storage as `storage is record`"),
        "{err}"
    );
    let err = compile(
        "type tiny is uint8;\nstorage is record { n : nat; }\nexternal function go() is { const x : tiny := 300; skip }\n",
    )
    .expect_err("range");
    assert!(
        err.to_string().contains("does not fit type `tiny`"),
        "{err}"
    );
    assert!(err.to_string().contains("uint8"), "{err}");
    let err = compile(
        "type basis_points is uint16;\ntype discount_rate is uint16;\nstorage is record { n : nat; }\nexternal function go() is { const fee : basis_points := 500; const discount : discount_rate := fee; skip }\n",
    )
    .expect_err("nominal");
    assert!(
        err.to_string().contains("initializer type does not match"),
        "{err}"
    );
    let err = compile(
        "type basis_points is uint16;\nstorage is record { n : nat; }\nexternal function go() is { const fee : basis_points := 500n; skip }\n",
    )
    .expect_err("suffix");
    assert!(
        err.to_string().contains("initializer type does not match"),
        "{err}"
    );
    compile(TYPES).expect("casts");
    let runtime = deploy(&compile(TYPES).expect("units")).expect("deploy");
    let out = exec(
        &runtime,
        &word_data("quote(uint16)", &[Word::from_u64(500)]),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("go");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(
        slot(&out.storage, 0),
        Word::from_u64(1_000_000_000_000_000_000)
    );
    assert_eq!(
        slot(&out.storage, 1),
        Word::from_u64(1_700_000_000 + 86_400)
    );
}

#[test]
fn imports_are_typed_declarations() {
    let examples = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/imports");
    let err = compile("import \"./fee.lithe\";\n").expect_err("string");
    assert!(
        err.to_string()
            .contains("`import` requires compiling a file"),
        "{err}"
    );
    let runtime = deploy(&crate::compile_file(&examples.join("vault.lithe")).expect("vault"))
        .expect("deploy");
    let out = exec(
        &runtime,
        &word_data("go(uint256)", &[Word::from_u64(4)]),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("go");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(slot(&out.storage, 0), Word::from_u64(5));
    let dir = std::env::temp_dir().join(format!("lithe-uses-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("dir");
    std::fs::copy(examples.join("fee.lithe"), dir.join("fee.lithe")).expect("fee");
    std::fs::write(
        dir.join("other.lithe"),
        "function calculate_fee(const amount : nat) : nat is amount\n",
    )
    .expect("other");
    std::fs::write(
        dir.join("clash.lithe"),
        "import \"./fee.lithe\";\nimport \"./other.lithe\";\nstorage is record { n : nat; }\nexternal function go() is { skip }\n",
    )
    .expect("clash");
    let err = crate::compile_file(&dir.join("clash.lithe")).expect_err("clash");
    assert!(
        err.to_string().contains("ambiguous symbol `calculate_fee`"),
        "{err}"
    );
    std::fs::write(dir.join("a.lithe"), "import \"./b.lithe\";\n").expect("a");
    std::fs::write(dir.join("b.lithe"), "import \"./a.lithe\";\n").expect("b");
    let err = crate::compile_file(&dir.join("a.lithe")).expect_err("cycle");
    assert!(
        err.to_string()
            .contains("cyclic module dependency detected"),
        "{err}"
    );
    assert!(err.to_string().contains("a.lithe"), "{err}");
    assert!(err.to_string().contains("b.lithe"), "{err}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn named_storage_and_upgrade_migrate_once() {
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/upgrade.lithe");
    let dir = std::env::temp_dir().join(format!("lithe-upgrade-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("dir");
    let src = std::fs::read_to_string(&path).expect("upgrade example");
    let abi = crate::abi_file(&path).expect("abi");
    assert!(abi.contains("upgradeToAndCall"), "{abi}");
    assert!(abi.contains("proxiableUUID"), "{abi}");
    assert!(!abi.contains("\"name\": \"init\""), "{abi}");
    let layout = crate::storage_layout(&path).expect("layout");
    assert!(layout.contains("vault.settings"), "{layout}");
    assert!(
        layout.contains(&hex_bytes(
            &crate::keccak::erc7201("vault.settings").to_be_bytes()
        )),
        "{layout}"
    );
    let runtime = deploy(&crate::compile_file(&path).expect("compile")).expect("deploy");
    let owner = Word::from_u64(0xab);
    let claimed = exec(
        &runtime,
        &word_data("claim()", &[]),
        HashMap::new(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("claim");
    assert!(!claimed.reverted, "{}", pretty(&claimed.returndata));
    let data =
        crate::upgrade_calldata(&path, "init", "0x1000", &["9".to_string()]).expect("calldata");
    let raw = hex_decode(data.strip_prefix("0x").unwrap());
    let upgraded = exec(
        &runtime,
        &raw,
        claimed.storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("upgrade");
    assert!(!upgraded.reverted, "{}", pretty(&upgraded.returndata));
    let root = crate::keccak::erc7201("vault.settings");
    assert_eq!(
        upgraded.storage.get(&root).copied(),
        Some(Word::from_u64(9))
    );
    let denied = exec(
        &runtime,
        &raw,
        claimed.storage,
        Word::from_u64(0xcd),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("stranger");
    assert!(denied.reverted, "stranger upgrade must revert");
    let direct = exec(
        &runtime,
        &word_data("init(uint256)", &[Word::from_u64(9)]),
        HashMap::new(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("direct");
    assert!(direct.reverted, "migrate is not a public entry");
    let uuid = exec(
        &runtime,
        &selector("proxiableUUID()").to_vec(),
        HashMap::new(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("uuid");
    assert!(!uuid.reverted, "{}", pretty(&uuid.returndata));
    assert_eq!(
        uuid.returndata,
        crate::keccak::erc1967_implementation()
            .to_be_bytes()
            .to_vec()
    );
    let next = dir.join("next.lithe");
    std::fs::write(
        &next,
        src.replace("paused : bool;", "paused : bool;\n  extra : nat;"),
    )
    .expect("next");
    let diff = crate::storage_diff(&path, &next).expect("diff");
    assert!(diff.contains("extra added"), "{diff}");
    assert!(diff.contains("compatible"), "{diff}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn operators_divide_shift_and_return_tuples() {
    let layout = leaves(include_str!("../examples/operators.lithe"));
    let src = include_str!("../examples/operators.lithe");
    let abi = crate::abi(src).expect("abi");
    assert!(abi.contains("(uint256,uint256)"), "{abi}");
    assert!(abi.contains("(uint256,address)"), "{abi}");
    assert!(abi.contains("(uint256,(address,bool))"), "{abi}");
    assert!(abi.contains("\"type\": \"tuple\""), "{abi}");
    assert!(abi.contains("\"components\":"), "{abi}");

    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let out = call(&runtime, "run(uint256)", &[Word::from_u64(11)]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(layout.get(&out.storage, 0), Word::from_u64(2));
    assert_eq!(layout.get(&out.storage, 1), Word::from_u64(1));
    assert_eq!(
        layout.get(&out.storage, 2),
        Word::from_u64(2).wrapping_neg()
    );
    assert_eq!(
        layout.get(&out.storage, 3),
        Word::from_u64(1).wrapping_neg()
    );
    assert_eq!(layout.get(&out.storage, 4), Word::from_u64(1));
    assert_eq!(
        layout.get(&out.storage, 5),
        Word::from_u64(2).wrapping_neg()
    );
    assert_eq!(
        layout.get(&out.storage, 6),
        Word::from_u64(1).wrapping_neg()
    );
    assert_eq!(layout.get(&out.storage, 7), Word::from_u64(0x0f));
    assert_eq!(layout.get(&out.storage, 8), Word::from_u64(3));
    assert_eq!(layout.get(&out.storage, 9), Word::from_u64(252));
    assert_eq!(layout.get(&out.storage, 10), Word::from_u64(0).not());
    assert_eq!(layout.get(&out.storage, 11), Word::from_u64(256));
    assert_eq!(layout.get(&out.storage, 12), Word::from_u64(1));
    assert_eq!(layout.get(&out.storage, 13), Word::from_u64(3));
    assert_eq!(layout.get(&out.storage, 14), Word::from_u64(1));
    assert_eq!(layout.get(&out.storage, 15), Word::from_u64(0));
    assert_eq!(layout.get(&out.storage, 16), Word::from_u64(255));
    assert_eq!(
        layout.get(&out.storage, 17),
        Word::from_u64(4).wrapping_neg()
    );
    assert_eq!(layout.get(&out.storage, 18), Word::from_u64(5));
    assert_eq!(layout.get(&out.storage, 19), Word::from_u64(1));
    assert_eq!(layout.get(&out.storage, 20), Word::from_u64(11));
    assert_eq!(layout.get(&out.storage, 21), Word::from_u64(1));
    assert_eq!(layout.get(&out.storage, 22), Word::from_u64(1));
    assert_eq!(layout.get(&out.storage, 23), Word::from_u64(11));

    let quote = call(&runtime, "quote()", &[]);
    assert!(!quote.reverted, "{}", pretty(&quote.returndata));
    assert_eq!(load_bytes(&quote.returndata, 0), Word::from_u64(2));
    assert_eq!(load_bytes(&quote.returndata, 32), Word::from_u64(1));

    let payee = call(&runtime, "payee()", &[]);
    assert!(!payee.reverted, "{}", pretty(&payee.returndata));
    assert_eq!(load_bytes(&payee.returndata, 0), Word::from_u64(7));
    assert_eq!(load_bytes(&payee.returndata, 32), Word::from_u64(1));

    let nested = call(&runtime, "nested_quote()", &[]);
    assert!(!nested.reverted, "{}", pretty(&nested.returndata));
    assert_eq!(load_bytes(&nested.returndata, 0), Word::from_u64(1));
    assert_eq!(load_bytes(&nested.returndata, 32), Word::from_u64(0x1000));
    assert_eq!(load_bytes(&nested.returndata, 64), Word::from_u64(1));

    let summed = call(&runtime, "sum_some()", &[]);
    assert!(!summed.reverted, "{}", pretty(&summed.returndata));
    assert_eq!(load_bytes(&summed.returndata, 0), Word::from_u64(9));

    let masked = call(&runtime, "mask_some()", &[]);
    assert!(!masked.reverted, "{}", pretty(&masked.returndata));
    assert_eq!(load_bytes(&masked.returndata, 0), Word::from_u64(0x0f));

    let zero = call(&runtime, "mod_zero()", &[]);
    assert!(zero.reverted);
    assert!(zero.returndata.starts_with(&selector("Panic(uint256)")));
    assert_eq!(load_bytes(&zero.returndata, 4), Word::from_u64(0x12));

    let min_div = call(&runtime, "min_div()", &[]);
    assert!(min_div.reverted);
    assert_eq!(load_bytes(&min_div.returndata, 4), Word::from_u64(0x11));
    let min_mod = call(&runtime, "min_mod()", &[]);
    assert!(min_mod.reverted);
    assert_eq!(load_bytes(&min_mod.returndata, 4), Word::from_u64(0x11));
}

#[test]
fn nonreentrant_lock_covers_deferred_calls() {
    let src = include_str!("../examples/nonreentrant.lithe");
    let tree = crate::abi_tree(src).expect("tree");
    let settle = route_text(&tree, "settle");
    assert!(
        settle.contains("protected by nonreentrant domain"),
        "{settle}"
    );
    assert!(settle.contains("hook.cancel"), "{settle}");
    let notify = route_text(&tree, "notify");
    assert!(
        notify.contains("protected by nonreentrant domain"),
        "{notify}"
    );
    assert!(
        !route_text(&tree, "ping").contains("nonreentrant"),
        "{tree}"
    );
    assert!(crate::warnings(src).expect("warnings").is_empty());

    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let hook = Word::from_u64(0x1000);
    let blocked = call(&runtime, "settle(address)", &[hook]);
    assert!(blocked.reverted, "cancel reentered a locked entry");
    assert_eq!(slot(&blocked.storage, 0), Word::from_u64(0));

    let noted = call(&runtime, "notify(address)", &[hook]);
    assert!(!noted.reverted, "{}", pretty(&noted.returndata));
    assert_eq!(slot(&noted.storage, 0), Word::from_u64(1));
    assert_eq!(slot(&noted.storage, 1), Word::from_u64(3));
    assert_eq!(
        noted
            .transient
            .get(&Word::from_u64(1))
            .copied()
            .unwrap_or_else(|| Word::from_u64(0)),
        Word::from_u64(0)
    );
    let canceled = exec_state(
        &runtime,
        &word_data("cancel()", &[]),
        noted.storage.clone(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
        noted.transient.clone(),
    )
    .expect("cancel");
    assert!(!canceled.reverted, "{}", pretty(&canceled.returndata));
    assert_eq!(slot(&canceled.storage, 1), Word::from_u64(2));

    let open = include_str!("../examples/reentry.lithe");
    let notes = crate::warnings(open).expect("reentry warnings");
    assert!(
        notes.contains(
            "warning: `settle` performs deferred external operations and may\nbe re-entered through `cancel`"
        ),
        "{notes}"
    );
    assert!(
        notes.contains(
            "consider `nonreentrant` if the protocol requires serialized\nexternal-effect execution"
        ),
        "{notes}"
    );
    let unlocked = deploy(&compile(open).expect("compile")).expect("deploy");
    let entered = call(&unlocked, "settle(address)", &[hook]);
    assert!(!entered.reverted, "{}", pretty(&entered.returndata));
    assert_eq!(slot(&entered.storage, 0), Word::from_u64(1));
    assert_eq!(slot(&entered.storage, 1), Word::from_u64(2));

    let alone = "\
storage is record { n : nat; }
external function pay(const to : address) is {
  storage.n := 1n;
  defer Evm.transfer(to, 1wei);
}
";
    let alone_notes = crate::warnings(alone).expect("alone");
    assert!(
        alone_notes.contains("be re-entered through `pay`"),
        "{alone_notes}"
    );
    let guarded = "\
storage is record { n : nat; }
external nonreentrant function pay(const to : address) is {
  storage.n := 1n;
  defer Evm.transfer(to, 1wei);
}
";
    assert!(crate::warnings(guarded).expect("guarded").is_empty());
    compile(guarded).expect("decorator order");
}

#[test]
fn continuations_run_as_new_phases() {
    install_mocks();
    let src = include_str!("../fuzz/then.lithe");
    let layout = leaves(src);
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let run = |storage: &HashMap<Word, Word>, sig: &str, args: &[u64]| {
        let args: Vec<Word> = args.iter().map(|&a| Word::from_u64(a)).collect();
        exec(
            &runtime,
            &word_data(sig, &args),
            storage.clone(),
            Word::from_u64(7),
            Word::from_u64(0),
            Word::from_u64(10),
        )
        .unwrap_or_else(|err| panic!("{sig}: {err}"))
    };
    let ok = |out: &Outcome| assert!(!out.reverted, "{}", pretty(&out.returndata));
    let empty = HashMap::new();

    // Phase 1 commits before the call; phase 2 re-reads `status` and logs after it.
    let done = run(&empty, "execute(address,uint256)", &[0xcd, 1005]);
    ok(&done);
    assert_eq!(layout.get(&done.storage, 0), Word::from_u64(2));
    assert_eq!(layout.get(&done.storage, 1), Word::from_u64(5));
    assert_eq!(layout.get(&done.storage, 6), Word::from_u64(1));
    let kinds = trace_kinds(&done.trace);
    let first_call = kinds.iter().position(|k| *k == "call").expect("call");
    assert!(kinds[..first_call].contains(&"sstore"), "{kinds:?}");
    assert_eq!(kinds.last(), Some(&"log"), "{kinds:?}");
    let too_small = run(&done.storage, "execute(address,uint256)", &[0xcd, 3]);
    assert!(too_small.reverted, "5 % 7 > 3");
    for bad in [1, 0x2000] {
        let out = run(&empty, "execute(address,uint256)", &[bad, 5]);
        assert!(out.reverted, "malformed return data from {bad:#x}");
        assert!(out.storage.is_empty());
    }

    let narrow = run(&empty, "narrow(address,uint256)", &[0xcd, 200]);
    ok(&narrow);
    assert_eq!(layout.get(&narrow.storage, 2), Word::from_u64(200));
    assert!(run(&empty, "narrow(address,uint256)", &[0xcd, 256]).reverted);

    let split = run(&empty, "split(address,uint256,uint256)", &[0xcd, 3, 4]);
    ok(&split);
    assert_eq!(layout.get(&split.storage, 3), Word::from_u64(3));
    assert_eq!(layout.get(&split.storage, 4), Word::from_u64(4));

    // Depth-first: the nested calls and their continuations finish before the last call's.
    let chain = run(&empty, "chain(address,uint256)", &[0xcd, 107]);
    ok(&chain);
    assert_eq!(layout.get(&chain.storage, 1), Word::from_u64(7));
    assert_eq!(layout.get(&chain.storage, 3), Word::from_u64(15));
    assert_eq!(layout.get(&chain.storage, 4), Word::from_u64(15));
    assert_eq!(layout.get(&chain.storage, 6), Word::from_u64(10));
    assert_eq!(kinds_of(&chain.trace, "call"), 5);

    let data = u64::from_be_bytes(*b"hi there");
    let short = run(&empty, "rename(address,uint256,uint256)", &[0xcd, 8, data]);
    ok(&short);
    let name = run(&short.storage, "name()", &[]);
    ok(&name);
    assert_eq!(abi_string_value(&name.returndata), b"\0\0\0\0\0\0\0\0");
    assert!(run(&empty, "rename(address,uint256,uint256)", &[0xcd, 33, data]).reverted);
    let full = run(&empty, "rename(address,uint256,uint256)", &[0xcd, 32, data]);
    ok(&full);
    let name = run(&full.storage, "name()", &[]);
    assert_eq!(
        abi_string_value(&name.returndata),
        Word::from_u64(data).to_be_bytes()
    );

    let hashed = run(&empty, "hashed(address,uint256)", &[2, 9]);
    ok(&hashed);
    let name = run(&hashed.storage, "name()", &[]);
    assert_eq!(
        abi_string_value(&name.returndata),
        Word::from_u64(9).to_be_bytes()
    );
    assert!(run(&empty, "hashed(address,uint256)", &[0xcd, 9]).reverted);

    let fund = run(&empty, "fund(address,uint256)", &[0xcd, 8]);
    ok(&fund);
    assert_eq!(layout.get(&fund.storage, 7), Word::from_u64(3));
    assert!(fund
        .trace
        .iter()
        .any(|ev| matches!(ev, Ev::Call { value, .. } if *value == Word::from_u64(3))));

    let tree = crate::abi_tree(src).expect("tree");
    let chain = route_text(&tree, "chain");
    assert!(
        chain.contains("  phase 2 (after op):\n    input:\n      - first : nat\n"),
        "{chain}"
    );
    assert!(chain.contains("  phase 5 (after ex.poke):"), "{chain}");
    let split = route_text(&tree, "split");
    assert!(
        split.contains("      - x : nat\n      - y : nat\n"),
        "{split}"
    );
    assert!(!split.contains("phase 3"), "{split}");
    assert!(!route_text(&tree, "narrow").contains("phase 3"), "{tree}");

    let notes = crate::warnings(src).expect("warnings");
    assert!(
        notes.contains(
            "warning: captured value `before` was derived from storage before\nan external state-changing call and may be stale in this continuation\n\nconsider re-reading storage inside the continuation"
        ),
        "{notes}"
    );

    // The lock holds through the continuation and the calls it defers.
    let locked = "\
interface Hook is {
  function cancel();
  function ping();
}
storage is record { status : nat; pinged : nat; }
external nonreentrant function settle(const hook : Hook) is {
  defer hook.ping()
    then {
      storage.status := storage.pinged;
      defer hook.cancel();
    };
}
external nonreentrant function cancel() is {
  storage.pinged := 2n;
}
external function ping() is {
  storage.pinged := 3n;
}
";
    let runtime = deploy(&compile(locked).expect("compile")).expect("deploy");
    let blocked = call(&runtime, "settle(address)", &[Word::from_u64(0x1000)]);
    assert!(blocked.reverted, "cancel reentered from a continuation");
    let unlocked = locked.replacen(
        "external nonreentrant function cancel",
        "external function cancel",
        1,
    );
    let runtime = deploy(&compile(&unlocked).expect("compile")).expect("deploy");
    let passed = call(&runtime, "settle(address)", &[Word::from_u64(0x1000)]);
    assert!(!passed.reverted, "{}", pretty(&passed.returndata));
    assert_eq!(slot(&passed.storage, 0), Word::from_u64(3));
    assert_eq!(slot(&passed.storage, 1), Word::from_u64(2));
}

#[test]
fn continuations_reject_what_cannot_cross_a_call() {
    let program = |body: &str| {
        format!(
            "\
interface Ex is {{
  function swap(amount : nat) : nat;
  function pair() : (nat, nat);
  function poke();
}}
storage is record {{ n : nat; }}
{body}"
        )
    };
    let cases = [
        (
            "external function f(const ex : Ex) is {\n  var left : nat := 1n;\n  defer ex.swap(1n) then (r : nat) { storage.n := left + r; };\n}\n",
            "`left` is a `var` of an earlier phase; mutable locals do not cross an external call",
        ),
        (
            "external function f(const ex : Ex) is {\n  defer ex.swap(1n) then (r : bool) { skip; };\n}\n",
            "the result type does not match what the call returns",
        ),
        (
            "external function f(const ex : Ex) is {\n  defer ex.poke() then (r : nat) { skip; };\n}\n",
            "this call returns nothing; write `then { ... }` without a result",
        ),
        (
            "external function f(const ex : Ex) is {\n  defer ex.pair() then ((a, b, c) : (nat, nat)) { skip; };\n}\n",
            "tuple pattern has 3 names and the type has 2 elements",
        ),
        (
            "external function f(const ex : Ex) is {\n  defer ex.swap(1n) then (r) { skip; };\n}\n",
            "a continuation result needs a type",
        ),
        (
            "external view function f(const ex : Ex) : nat is {\n  defer ex.swap(1n) then (r : nat) { skip; };\n} with 1n\n",
            "cannot defer an operation",
        ),
        (
            "view function g(const ex : Ex) is {\n  defer ex.swap(1n) then (r : nat) { skip; };\n}\n",
            "cannot defer an operation",
        ),
        (
            "pure function g(const ex : Ex) is {\n  defer ex.swap(1n) then (r : nat) { skip; };\n}\n",
            "cannot defer an operation",
        ),
    ];
    for (body, want) in cases {
        let err = compile(&program(body)).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    let captured = program(
        "external function f(const ex : Ex; const k : nat) is {\n  const seen : nat := storage.n;\n  const fresh : nat := k + 1n;\n  defer ex.swap(k) then (r : nat) { storage.n := r + fresh + seen + k; };\n}\n",
    );
    let notes = crate::warnings(&captured).expect("warnings");
    assert!(notes.contains("captured value `seen`"), "{notes}");
    assert!(
        !notes.contains("`fresh`") && !notes.contains("`k`"),
        "{notes}"
    );
}

fn kinds_of(trace: &[Ev], kind: &str) -> usize {
    trace_kinds(trace).iter().filter(|k| **k == kind).count()
}

fn abi_string_value(data: &[u8]) -> Vec<u8> {
    let len = word_usize(load_bytes(data, 32)).expect("length");
    data[64..64 + len].to_vec()
}

/// A `nonreentrant` function reverts if called while any transition of this contract is
/// still running its deferred calls: its own, a `nonreentrant` one's, or a plain one's.
#[test]
fn nonreentrant_rejects_calls_during_any_defer_window() {
    let src = "\
interface Me is {
  function guarded();
  function plain();
  function relay(me : Me);
  function price() : nat;
  function open_price() : nat;
}
storage is record { n : nat; seen : nat; }
external nonreentrant function guarded() is { storage.n := storage.n + 1n; }
external function plain() is { storage.n := storage.n + 10n; }
external function relay(const me : Me) is { defer me.plain(); }
external nonreentrant view function price() : nat is storage.n
external view function open_price() : nat is storage.n
external function plain_then_guarded(const me : Me) is { defer me.guarded(); }
external function plain_then_price(const me : Me) is {
  defer me.price() then (p : nat) { storage.seen := p; };
}
external function plain_then_open(const me : Me) is {
  storage.n := 5n;
  defer me.open_price() then (p : nat) { storage.seen := p; };
}
external function plain_then_plain(const me : Me) is { defer me.plain(); }
external nonreentrant function locked_then_plain(const me : Me) is { defer me.plain(); }
external nonreentrant function locked_then_guarded(const me : Me) is { defer me.guarded(); }
external function after_nested(const me : Me) is {
  defer me.relay(me);
  defer me.guarded();
}
external function continuation_then_guarded(const me : Me) is {
  defer me.plain() then { defer me.guarded(); };
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let me = Word::from_u64(0x1000);
    let run = |sig: &str, args: &[Word]| call(&runtime, sig, args);
    // Outside any window, both kinds run.
    assert!(!run("guarded()", &[]).reverted);
    let price = run("price()", &[]);
    assert!(!price.reverted, "{}", pretty(&price.returndata));
    for (sig, rejected) in [
        ("plain_then_guarded(address)", true),
        ("plain_then_price(address)", true),
        ("plain_then_open(address)", false),
        ("plain_then_plain(address)", false),
        ("locked_then_plain(address)", false),
        ("locked_then_guarded(address)", true),
        // The inner window ends with the lock still held for the outer one.
        ("after_nested(address)", true),
        ("continuation_then_guarded(address)", true),
    ] {
        let out = run(sig, &[me]);
        assert_eq!(out.reverted, rejected, "{sig}: {}", pretty(&out.returndata));
        // The lock never outlives the transition.
        assert_eq!(
            out.transient
                .get(&Word::from_u64(1))
                .copied()
                .unwrap_or_else(|| Word::from_u64(0)),
            Word::from_u64(0),
            "{sig}"
        );
    }
    let open = run("plain_then_open(address)", &[me]);
    assert_eq!(slot(&open.storage, 1), Word::from_u64(5));

    let footprint = crate::footprint(src).expect("footprint");
    let line = |name: &str| {
        footprint
            .lines()
            .find(|l| l.starts_with(&format!("{name} ")))
            .unwrap_or_else(|| panic!("{name} in {footprint}"))
            .to_string()
    };
    assert!(
        line("guarded").ends_with("during defers: rejected"),
        "{footprint}"
    );
    assert!(
        line("price").ends_with("during defers: rejected"),
        "{footprint}"
    );
    assert!(
        line("plain").ends_with("during defers: callable"),
        "{footprint}"
    );
    assert!(
        line("open_price").ends_with("during defers: callable"),
        "{footprint}"
    );

    // Without a `nonreentrant` function nothing checks the lock, so nothing sets it.
    let unguarded = "\
interface Me is { function plain(); }
storage is record { n : nat; }
external function plain() is { storage.n := storage.n + 1n; }
external function relay(const me : Me) is { defer me.plain(); }
";
    let code = compile(unguarded).expect("unguarded");
    assert!(
        !code.contains(&0x5d),
        "no TSTORE without a nonreentrant function"
    );

    for (src, want) in [
        (
            "nonreentrant function helper() is { skip }\n",
            "nonreentrant functions must be external; write `external nonreentrant function`",
        ),
        (
            "pure nonreentrant function calc() : nat is 1n\n",
            "nonreentrant functions must be external",
        ),
        (
            "view nonreentrant function peek() : nat is 1n\n",
            "nonreentrant functions must be external",
        ),
        (
            "external view nonreentrant function peek() : nat is 1n\n",
            "keywords out of order; write `external nonreentrant view function`",
        ),
        (
            "external nonreentrant payable function pay() is { skip }\n",
            "keywords out of order; write `external payable nonreentrant function`",
        ),
    ] {
        let err = compile(src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    compile("storage is record { n : wei; }\nexternal payable nonreentrant function pay() is { storage.n := Evm.value(); }\n")
        .expect("payable nonreentrant");
}

/// Transient storage is shared by every call in a transaction and gone after it.
#[test]
fn transient_storage_lasts_for_the_transaction() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/transient.lithe");
    let runtime = deploy(&crate::compile_file(&path).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let me = w(0x1000);
    let run =
        |sig: &str, args: &[Word], transient: HashMap<Word, Word>, storage: HashMap<Word, Word>| {
            exec_state(
                &runtime,
                &word_data(sig, args),
                storage,
                w(7),
                w(0),
                w(0),
                transient,
            )
            .unwrap_or_else(|err| panic!("{sig}: {err}"))
        };
    // The deferred call back into `confirm` sees the scratch state `process` left.
    let first = run(
        "process(address,uint256)",
        &[me, w(9)],
        HashMap::new(),
        HashMap::new(),
    );
    assert!(!first.reverted, "{}", pretty(&first.returndata));
    assert_eq!(slot(&first.storage, 0), w(9));
    assert_eq!(slot(&first.storage, 1), w(9));
    // Persistent storage holds only its own two slots.
    assert_eq!(first.storage.len(), 2, "{:?}", first.storage);
    assert_eq!(first.transient.get(&w(2)), Some(&w(1)));
    assert_eq!(first.transient.get(&w(3)), Some(&w(9)));
    assert_eq!(first.transient.get(&w(5)), Some(&w(1)));
    assert_eq!(first.transient.get(&map_key(w(7), w(4))), Some(&w(9)));
    // A module's record sits at a slot derived from its name, the same in every contract.
    let execution = crate::check::module_transient_slot("Settlement.execution");
    assert_eq!(first.transient.get(&w(execution)), Some(&w(1)));
    assert_eq!(first.transient.get(&w(execution + 1)), Some(&w(1)));
    // Later in the same transaction the flag is still set.
    let again = run(
        "process(address,uint256)",
        &[me, w(1)],
        first.transient.clone(),
        first.storage.clone(),
    );
    assert!(again.reverted);
    assert_eq!(again.returndata, selector("AlreadyProcessing()").to_vec());
    assert_eq!(
        again.transient, first.transient,
        "a revert undoes transient writes"
    );
    let seen = run(
        "processing()",
        &[],
        first.transient.clone(),
        first.storage.clone(),
    );
    assert_eq!(load_bytes(&seen.returndata, 0), w(1));
    // A new transaction starts clear.
    let next = run(
        "process(address,uint256)",
        &[me, w(1)],
        HashMap::new(),
        first.storage.clone(),
    );
    assert!(!next.reverted, "{}", pretty(&next.returndata));
    assert_eq!(slot(&next.storage, 0), w(10));
    let outside = run("confirm()", &[], HashMap::new(), first.storage.clone());
    assert!(outside.reverted);
    assert_eq!(outside.returndata, selector("NotSettling()").to_vec());
    let clear = run("processing()", &[], HashMap::new(), first.storage.clone());
    assert_eq!(load_bytes(&clear.returndata, 0), w(0));

    // A query sees transient writes made before it, so it is never moved ahead of one.
    let src = "\
interface Me is { view function pending() : nat; }
transient storage scratch is record { pending : nat; }
storage is record { first : nat; seen : nat; }
external view function pending() : nat is scratch.pending
external function probe(const me : Me) is {
  storage.first := 1n;
  scratch.pending := 9n;
  const seen : nat := query me.pending();
  storage.seen := seen;
}
";
    let runtime = deploy(&compile(src).expect("probe")).expect("deploy");
    let out = call(&runtime, "probe(address)", &[me]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(slot(&out.storage, 1), w(9));

    let file = std::env::temp_dir().join(format!("lithe-transient-{}.lithe", std::process::id()));
    std::fs::write(&file, src).expect("write");
    let layout = crate::storage_layout(&file).expect("layout");
    std::fs::remove_file(&file).ok();
    assert!(
        layout.contains("transient scratch\n  pending: uint256  transient slot 2"),
        "{layout}"
    );
    let analysis = crate::analysis(src).expect("analysis");
    assert!(
        analysis.contains("{ \"space\": \"transient\", \"path\": \"scratch.pending\" }"),
        "{analysis}"
    );
    assert!(
        analysis.contains("{ \"space\": \"storage\", \"path\": \"seen\" }"),
        "{analysis}"
    );
    assert!(!crate::abi(src).expect("abi").contains("scratch"));

    for (body, want) in [
        (
            "transient storage t is record { s : string; }\nexternal function f() is { skip }\n",
            "transient storage field `s` must hold a word, an option, or a map of them",
        ),
        (
            "transient storage t is record { n : nat; }\nexternal view function f() : nat is { t.n := 1n; } with 1n\n",
            "declared effect is weaker than the body's: external view function `f` writes storage",
        ),
        (
            "transient storage t is record { n : nat; }\npure function f() : nat is t.n\nexternal function g() is { skip }\n",
            "declared effect is weaker than the body's: pure function `f` reads contract storage",
        ),
        (
            "transient storage t is record { n : nat; }\nstorage t at \"x\" is record { n : nat; }\nexternal function f() is { skip }\n",
            "duplicate storage domain `t`",
        ),
    ] {
        let err = compile(body).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}

/// `Ok` and `Error` recover from a failed external call: a deferred call's arm runs as
/// a new phase, a query's arm within the transition. Malformed success still reverts.
#[test]
fn recoverable_calls_branch_on_the_outcome() {
    install_mocks();
    let src = include_str!("../fuzz/recover.lithe");
    let layout = leaves(src);
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let (ok, refuse, malformed, missing) = (w(0xcd), w(0xee), w(1), w(0x2000));
    let run = |sig: &str, args: &[Word]| call(&runtime, sig, args);
    let reason = |out: &Outcome| {
        let view = exec(
            &runtime,
            &word_data("reason()", &[]),
            out.storage.clone(),
            w(7),
            w(0),
            w(0),
        )
        .expect("reason");
        abi_string_value(&view.returndata)
    };

    let done = run("execute(address,uint256)", &[ok, w(5)]);
    assert!(!done.reverted, "{}", pretty(&done.returndata));
    assert_eq!(
        (layout.get(&done.storage, 0), layout.get(&done.storage, 1)),
        (w(2), w(5))
    );
    // The callee reverts: the phase before the call stays, and `Error` records why.
    let failed = run("execute(address,uint256)", &[refuse, w(5)]);
    assert!(!failed.reverted, "{}", pretty(&failed.returndata));
    assert_eq!(layout.get(&failed.storage, 0), w(3));
    assert_eq!(layout.get(&failed.storage, 2), w(1));
    assert_eq!(reason(&failed), w(5).to_be_bytes());
    // Revert data longer than a word lands in a blob.
    let long = run("execute(address,uint256)", &[refuse, w(0).not()]);
    assert_eq!(reason(&long), w(0).not().to_be_bytes());
    // A successful call with bad return data is not an `Error`: it reverts everything.
    assert!(run("execute(address,uint256)", &[malformed, w(5)]).reverted);
    assert!(run("execute(address,uint256)", &[missing, w(5)]).reverted);

    let pinged = run("ping(address,uint256)", &[ok, w(3)]);
    assert_eq!(layout.get(&pinged.storage, 3), w(1));
    let unpinged = run("ping(address,uint256)", &[refuse, w(3)]);
    assert!(!unpinged.reverted);
    assert_eq!(layout.get(&unpinged.storage, 3), w(0));

    let read = run("read(address,uint256)", &[ok, w(42)]);
    assert_eq!(layout.get(&read.storage, 4), w(42));
    let unavailable = run("read(address,uint256)", &[missing, w(42)]);
    assert!(unavailable.reverted);
    assert_eq!(unavailable.returndata, selector("Unavailable()").to_vec());
    let small = run("read_small(address,uint256)", &[ok, w(200)]);
    assert_eq!(layout.get(&small.storage, 5), w(200));
    // A dirty word is malformed, not an `Error`.
    assert!(run("read_small(address,uint256)", &[ok, w(300)]).reverted);
    for sig in ["read_plain(address,uint256)", "read_early(address,uint256)"] {
        let fits = run(sig, &[ok, w(200)]);
        assert!(!fits.reverted, "{sig}: {}", pretty(&fits.returndata));
        assert_eq!(layout.get(&fits.storage, 5), w(200), "{sig}");
        assert!(run(sig, &[ok, w(300)]).reverted, "{sig}: a dirty uint8");
        assert!(run(sig, &[refuse, w(1)]).reverted, "{sig}: a failed query");
    }
    let noted = run("read_small(address,uint256)", &[refuse, w(9)]);
    assert!(!noted.reverted);
    assert_eq!(reason(&noted), w(9).to_be_bytes());

    let program = |body: &str| {
        format!(
            "interface Ext is {{ function swap(n : nat) : nat; function poke(); view function price(n : nat) : nat; }}\nstorage is record {{ n : nat; r : bytes; }}\n{body}"
        )
    };
    for (body, want) in [
        (
            "external function f(const e : Ext) is { defer e.swap(1n) then { | Ok(r : nat) -> { skip } }; }\n",
            "a recoverable call needs both `Ok` and `Error` arms",
        ),
        (
            "external function f(const e : Ext) is { defer e.swap(1n) then { | Ok(r : nat) -> { skip } | Fail(r : bytes) -> { skip } }; }\n",
            "a call's outcome is `Ok` or `Error`, not `Fail`",
        ),
        (
            "external function f(const e : Ext) is { defer e.swap(1n) then { | Ok(r : bool) -> { skip } | Error(_) -> { skip } }; }\n",
            "the result type does not match what the call returns",
        ),
        (
            "external function f(const e : Ext) is { defer e.swap(1n) then { | Ok(r : nat) -> { skip } | Error(x : string) -> { skip } }; }\n",
            "the result type does not match what the call returns",
        ),
        (
            "external function f(const e : Ext) is { defer e.poke() then { | Ok(r : nat) -> { skip } | Error(_) -> { skip } }; }\n",
            "this call returns nothing",
        ),
        (
            "external function f(const e : Ext) is { case query e.price(1n) of { | Ok(p) -> { skip } }; }\n",
            "missing case arm `Error`",
        ),
    ] {
        let err = compile(&program(body)).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    let tree = crate::abi_tree(src).expect("tree");
    assert!(
        route_text(&tree, "execute")
            .contains("phase 3 (after ex.swap fails):\n    input:\n      - reason : bytes"),
        "{tree}"
    );
}

/// A deferred call may send `bytes` and `string`: its calldata is sized when it is deferred.
#[test]
fn deferred_calls_send_dynamic_values() {
    install_mocks();
    let src = "\
interface Echo is {
  function same(data : bytes) : bytes;
  function around(n : nat; data : bytes; m : nat) : (nat, nat);
  function text(label : string) : string;
}
storage is record { back : bytes; first : nat; offset : nat; label : string; }
external function send(const e : Echo; const data : bytes) is {
  defer e.same(data) then (back : bytes) { storage.back := back; };
}
external function head(const e : Echo; const n : nat; const data : bytes) is {
  defer e.around(n, data, 7n) then ((a, b) : (nat, nat)) {
    storage.first := a;
    storage.offset := b;
  };
}
external function name(const e : Echo; const label : string) is {
  defer e.text(label) then (back : string) { storage.label := back; };
}
external view function back() : bytes is storage.back
external view function label() : string is storage.label
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let echo = Word::from_u64(0xcd).to_be_bytes();
    let bytes_call = |sig: &str, data: &[u8]| {
        let mut input = selector(sig).to_vec();
        input.extend_from_slice(&echo);
        input.extend_from_slice(&Word::from_u64(64).to_be_bytes());
        input.extend_from_slice(&Word::from_u64(data.len() as u64).to_be_bytes());
        input.extend_from_slice(data);
        input.resize(input.len() + (32 - data.len() % 32) % 32, 0);
        input
    };
    for data in [&b""[..], b"hello", &[0xab; 70][..]] {
        for (sig, view) in [
            ("send(address,bytes)", "back()"),
            ("name(address,string)", "label()"),
        ] {
            let out = exec(
                &runtime,
                &bytes_call(sig, data),
                HashMap::new(),
                Word::from_u64(7),
                Word::from_u64(0),
                Word::from_u64(0),
            )
            .expect(sig);
            assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
            let read = exec(
                &runtime,
                &word_data(view, &[]),
                out.storage,
                Word::from_u64(7),
                Word::from_u64(0),
                Word::from_u64(0),
            )
            .expect(view);
            assert_eq!(
                abi_string_value(&read.returndata),
                data,
                "{sig} {}",
                data.len()
            );
        }
    }
    let mut input = selector("head(address,uint256,bytes)").to_vec();
    input.extend_from_slice(&echo);
    input.extend_from_slice(&Word::from_u64(5).to_be_bytes());
    input.extend_from_slice(&Word::from_u64(96).to_be_bytes());
    input.extend_from_slice(&Word::from_u64(3).to_be_bytes());
    input.extend_from_slice(&[1, 2, 3]);
    input.resize(input.len() + 29, 0);
    let out = exec(
        &runtime,
        &input,
        HashMap::new(),
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("head");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    // The echoed head: `n`, then the offset of `data` past the three head words.
    assert_eq!(
        (slot(&out.storage, 1), slot(&out.storage, 2)),
        (Word::from_u64(5), Word::from_u64(96))
    );
}

/// An empty string or bytes value is its offset and a zero length, with no data word.
#[test]
fn empty_dynamic_returns_have_no_data_word() {
    let src = "\
storage is record { s : string; }
external function set(const s : string) is { storage.s := s; }
external view function empty() : string is \"\"
external view function stored() : string is storage.s
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let empty = call(&runtime, "empty()", &[]);
    assert_eq!(empty.returndata.len(), 64, "{}", hex(&empty.returndata));
    assert_eq!(load_bytes(&empty.returndata, 0), Word::from_u64(32));
    let short = exec(
        &runtime,
        &abi_string("set(string)", b"hi"),
        HashMap::new(),
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("set");
    let stored = exec(
        &runtime,
        &word_data("stored()", &[]),
        short.storage,
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("stored");
    assert_eq!(stored.returndata.len(), 96);
    assert_eq!(abi_string_value(&stored.returndata), b"hi");
}

/// `fail reason` re-raises raw revert data unchanged, whether it stays in the return data
/// or was copied into a value first.
#[test]
fn raw_revert_data_passes_through() {
    install_mocks();
    let src = "\
error Silent;
interface Ext is { function swap(n : nat) : nat; }
storage is record { out : nat; kept : bytes; size : nat; }
external function relay(const ex : Ext; const n : nat)
  raises Silent
is {
  defer ex.swap(n) then {
    | Ok(r : nat) -> { storage.out := r; }
    | Error(reason : bytes) -> {
        if reason.length = 0n then { fail Silent; }
        fail reason;
      }
  };
}
external function keep(const ex : Ext; const n : nat) is {
  defer ex.swap(n) then {
    | Ok(r : nat) -> { storage.out := r; }
    | Error(reason : bytes) -> {
        storage.kept := reason;
        storage.size := reason.length;
        if reason.length > 20n then { fail reason; }
      }
  };
}
external function measure(const s : string) is { storage.size := s.length; }
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let run = |sig: &str, args: &[Word]| call(&runtime, sig, args);
    let ok = run("relay(address,uint256)", &[w(0xcd), w(4)]);
    assert!(!ok.reverted);
    assert_eq!(slot(&ok.storage, 0), w(4));
    let passed = run("relay(address,uint256)", &[w(0xee), w(4)]);
    assert!(passed.reverted);
    assert_eq!(
        passed.returndata,
        w(4).to_be_bytes().to_vec(),
        "the callee's own revert data"
    );
    let silent = run("relay(address,uint256)", &[w(0xef), w(4)]);
    assert!(silent.reverted);
    assert_eq!(silent.returndata, selector("Silent()").to_vec());
    // Copied into a value, then stored and measured; 32 bytes is long, so it is raised again.
    let kept = run("keep(address,uint256)", &[w(0xee), w(9)]);
    assert!(kept.reverted);
    assert_eq!(kept.returndata, w(9).to_be_bytes().to_vec());
    let quiet = run("keep(address,uint256)", &[w(0xef), w(9)]);
    assert!(!quiet.reverted, "{}", pretty(&quiet.returndata));
    assert_eq!(slot(&quiet.storage, 2), w(0));
    for text in [&b""[..], b"hello", &[0x61; 40][..]] {
        let out = exec(
            &runtime,
            &abi_string("measure(string)", text),
            HashMap::new(),
            w(7),
            w(0),
            w(0),
        )
        .expect("measure");
        assert_eq!(slot(&out.storage, 2), w(text.len() as u64));
    }
}

/// `defer create` deploys another contract of the same file after the transition; its
/// continuation receives the new address. With a salt it uses `CREATE2`.
#[test]
fn deferred_creation_deploys_a_peer_contract() {
    let src = "\
interface Child is {
  function init(owner : address);
  view function owner() : address;
}

contract Factory is {
  storage is record { last : address; count : nat; seeded : address; }

  external function make() is {
    defer create Vault() then (vault : address) {
      storage.last := vault;
      storage.count := storage.count + 1n;
      defer Child(vault).init(Evm.sender());
    };
  }

  external function make_at(const salt : bytes32) is {
    defer create Vault() with salt = salt then (vault : address) {
      storage.seeded := vault;
    };
  }

  external function fund(const amount : nat) is {
    defer create Vault() with value = amount then {
      | Ok(vault : address) -> { storage.last := vault; }
      | Error(_) -> { storage.count := 99n; }
    };
  }

  external function fund_at(const amount : nat; const salt : bytes32) is {
    defer create Vault() with { value = amount; salt = salt; } then (vault : address) {
      storage.seeded := vault;
    };
  }

  external function owner_of_last() : address is {
    const owner : address := query Child(storage.last).owner();
  } with owner
}

contract Vault is {
  storage is record { owner : address; }
  external function init(const owner : address) is { storage.owner := owner; }
  external view function owner() : address is storage.owner
}
";
    let contracts = crate::compile_contracts(src).expect("compile");
    let code = |name: &str| {
        contracts
            .iter()
            .find(|(n, _)| n.as_deref() == Some(name))
            .map(|(_, c)| c.clone())
            .expect(name)
    };
    let factory = deploy(&code("Factory")).expect("deploy");
    let vault = deploy(&code("Vault")).expect("deploy vault");
    // The factory carries the vault's whole creation code after its own.
    let creation = code("Vault");
    assert!(factory
        .windows(creation.len())
        .any(|w| w == creation.as_slice()));
    let w = Word::from_u64;
    let caller = w(0xabc);
    let made = exec(
        &factory,
        &word_data("make()", &[]),
        HashMap::new(),
        caller,
        w(0),
        w(0),
    )
    .expect("make");
    assert!(!made.reverted, "{}", pretty(&made.returndata));
    let child = slot(&made.storage, 0);
    assert_ne!(child, w(0));
    assert_eq!(slot(&made.storage, 1), w(1));
    // The continuation's deferred call initialized the new contract.
    let (child_code, child_storage) = DEPLOYED
        .with(|d| d.borrow().get(&child).cloned())
        .expect("deployed");
    assert_eq!(child_code, vault);
    assert_eq!(
        slot(&child_storage, 0),
        caller,
        "`init` got the factory's caller"
    );
    let asked = exec(
        &factory,
        &word_data("owner_of_last()", &[]),
        made.storage.clone(),
        caller,
        w(0),
        w(0),
    )
    .expect("owner_of_last");
    assert_eq!(load_bytes(&asked.returndata, 0), caller);

    let salt = w(0x5a17);
    let seeded = exec(
        &factory,
        &word_data("make_at(bytes32)", &[salt]),
        HashMap::new(),
        caller,
        w(0),
        w(0),
    )
    .expect("make_at");
    assert!(!seeded.reverted, "{}", pretty(&seeded.returndata));
    let mut buf = vec![0xff];
    buf.extend_from_slice(&w(0x1000).to_be_bytes()[12..]);
    buf.extend_from_slice(&salt.to_be_bytes());
    buf.extend_from_slice(&crate::keccak::keccak256(&creation));
    let mut expected = [0u8; 32];
    expected[12..].copy_from_slice(&crate::keccak::keccak256(&buf)[12..]);
    assert_eq!(slot(&seeded.storage, 2), Word::from_be_bytes(expected));

    // More value than the factory holds: the creation fails and `Error` runs.
    let broke = exec(
        &factory,
        &word_data("fund(uint256)", &[w(5)]),
        HashMap::new(),
        caller,
        w(0),
        w(1),
    )
    .expect("fund");
    assert!(!broke.reverted, "{}", pretty(&broke.returndata));
    assert_eq!(slot(&broke.storage, 1), w(99));
    let funded = exec(
        &factory,
        &word_data("fund(uint256)", &[w(5)]),
        HashMap::new(),
        caller,
        w(0),
        w(10),
    )
    .expect("fund");
    assert_ne!(slot(&funded.storage, 0), w(0));

    // Both options: CREATE2 at the salted address, sending the value along.
    let both = exec(
        &factory,
        &word_data("fund_at(uint256,bytes32)", &[w(5), salt]),
        HashMap::new(),
        caller,
        w(0),
        w(10),
    )
    .expect("fund_at");
    assert!(!both.reverted, "{}", pretty(&both.returndata));
    let at = Word::from_be_bytes(expected);
    assert_eq!(slot(&both.storage, 2), at);
    assert!(both
        .trace
        .iter()
        .any(|ev| matches!(ev, Ev::Call { to, value } if *to == at && *value == w(5))));

    for (body, want) in [
        (
            "defer create Missing();",
            "`Missing` is not another contract of this file",
        ),
        (
            "defer create Other(1n);",
            "`Other` has no `deploy` parameters, so it takes no arguments",
        ),
        (
            "defer Evm.transfer(Evm.sender(), 1wei) with salt = 0x01;",
            "`salt` is only for `create`",
        ),
    ] {
        let src = format!(
            "contract One is {{\n  storage is record {{ n : nat; }}\n  external function f() is {{ {body} }}\n}}\ncontract Other is {{\n  storage is record {{ n : nat; }}\n  external function g() is {{ skip }}\n}}\n"
        );
        let err = crate::compile_contracts(&src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}

/// An encoding with a dynamic tail grows after it is allocated; later allocations must
/// not land on that tail while the encoding is still in use.
#[test]
fn encoded_blobs_keep_their_tails() {
    let src = "\
storage is record { a : bytes; b : bytes; name : string; }
external function both(const x : string; const y : string) is {
  const a : bytes := Abi.encode(1n, x);
  const b : bytes := Abi.encode_packed(y, 2n);
  const c : bytes := Abi.encode(y, storage.name);
  storage.a := a;
  storage.b := b;
}
external view function a() : bytes is storage.a
external view function b() : bytes is storage.b
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let (x, y) = ([0x78u8; 40], [0x79u8; 50]);
    let mut data = selector("both(string,string)").to_vec();
    for word in [w(64), w(160), w(x.len() as u64)] {
        data.extend_from_slice(&word.to_be_bytes());
    }
    data.extend_from_slice(&x);
    data.resize(4 + (data.len() - 4).div_ceil(32) * 32, 0);
    data.extend_from_slice(&w(y.len() as u64).to_be_bytes());
    data.extend_from_slice(&y);
    data.resize(4 + (data.len() - 4).div_ceil(32) * 32, 0);
    let out = exec(&runtime, &data, HashMap::new(), w(7), w(0), w(0)).expect("both");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    let view = |sig: &str| {
        let got = exec(
            &runtime,
            &word_data(sig, &[]),
            out.storage.clone(),
            w(7),
            w(0),
            w(0),
        )
        .expect(sig);
        abi_string_value(&got.returndata)
    };
    let mut a = Vec::new();
    for word in [w(1), w(64), w(x.len() as u64)] {
        a.extend_from_slice(&word.to_be_bytes());
    }
    a.extend_from_slice(&x);
    a.resize(a.len().div_ceil(32) * 32, 0);
    assert_eq!(view("a()"), a);
    let mut b = y.to_vec();
    b.extend_from_slice(&w(2).to_be_bytes());
    assert_eq!(view("b()"), b);
}

/// ABI words for `(address, uint256, string)`, as appended to creation code.
fn deploy_args(owner: Word, fee: u64, name: &[u8]) -> Vec<u8> {
    let w = Word::from_u64;
    let mut out = Vec::new();
    for word in [owner, w(fee), w(96), w(name.len() as u64)] {
        out.extend_from_slice(&word.to_be_bytes());
    }
    out.extend_from_slice(name);
    out.resize(out.len().div_ceil(32) * 32, 0);
    out
}

/// `deploy` runs once in the creation code, on the ABI-encoded arguments appended to it,
/// like a Solidity constructor.
#[test]
fn deploy_runs_in_creation_code() {
    let src = "\
error Too_high of nat;
storage is record { owner : address; fee : nat; name : string; }
event Deployed of record { indexed owner : address; fee : nat; }
deploy(const owner : address; const fee : nat; const name : string)
  raises Too_high
is {
  assert(fee <= 100n, Too_high(fee));
  storage.owner := owner;
  storage.fee := fee;
  storage.name := name;
  emit Deployed { owner = owner; fee = fee; };
}
external view function owner() : address is storage.owner
external view function fee() : nat is storage.fee
external view function name() : string is storage.name
";
    let init = compile(src).expect("compile");
    let w = Word::from_u64;
    let with_args = |args: &[u8]| [init.as_slice(), args].concat();
    for name in [&b"vault"[..], &[0x61; 45][..]] {
        let made =
            construct(&with_args(&deploy_args(w(0xabc), 30, name)), w(7), w(0)).expect("construct");
        assert!(!made.reverted, "{}", pretty(&made.returndata));
        assert!(made.trace.iter().any(|ev| matches!(ev, Ev::Log { .. })));
        let runtime = made.returndata.clone();
        let view = |sig: &str| {
            exec(
                &runtime,
                &word_data(sig, &[]),
                made.storage.clone(),
                w(1),
                w(0),
                w(0),
            )
            .expect(sig)
            .returndata
        };
        assert_eq!(load_bytes(&view("owner()"), 0), w(0xabc));
        assert_eq!(load_bytes(&view("fee()"), 0), w(30));
        assert_eq!(abi_string_value(&view("name()")), name);
    }
    // The body's checks, a value it cannot take, and arguments cut short all revert.
    let high = construct(&with_args(&deploy_args(w(1), 101, b"")), w(7), w(0)).expect("high");
    assert!(high.reverted);
    assert_eq!(high.returndata[..4], selector("TooHigh(uint256)"));
    let paid = construct(&with_args(&deploy_args(w(1), 1, b"")), w(7), w(1)).expect("paid");
    assert!(paid.reverted);
    let short = construct(&with_args(&deploy_args(w(1), 1, b"")[..64]), w(7), w(0)).expect("short");
    assert!(short.reverted);
    let abi = crate::abi(src).expect("abi");
    assert!(abi.contains("\"type\": \"constructor\""), "{abi}");

    let payable = "\
storage is record { paid : wei; }
payable deploy() is { storage.paid := Evm.value(); }
external view function paid() : wei is storage.paid
";
    let made = construct(&compile(payable).expect("payable"), w(7), w(5)).expect("construct");
    assert!(!made.reverted);
    assert_eq!(slot(&made.storage, 0), w(5));

    for (body, want) in [
        ("deploy() is { skip }\ndeploy() is { skip }", "a contract has at most one `deploy`"),
        ("deploy() : nat is { skip }", "`deploy` does not declare a return type"),
        ("external deploy() is { skip }", "`deploy` takes only `payable`"),
        ("deploy() is { storage.n := nat(Evm.value()); }", "`deploy` reads `Evm.value()`; write `payable deploy`"),
        ("deploy() is { defer Evm.transfer(Evm.sender(), 1wei); }", "deploy cannot defer an operation"),
        (
            "interface I is { view function n() : nat; }\ndeploy() is { storage.n := query I(Evm.sender()).n(); }",
            "deploy cannot query",
        ),
    ] {
        let src = format!(
            "storage is record {{ n : nat; }}\n{body}\nexternal view function n() : nat is storage.n\n"
        );
        let err = compile(&src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}

/// Behind a proxy, `deploy` is an entrypoint that runs only while its caller has no code:
/// from the proxy's constructor, on the proxy's storage.
#[test]
fn upgradeable_deploy_runs_only_during_construction() {
    let src = "\
upgradeable
error Not_owner;
storage is record { owner : address; }
upgrade guard is { assert(Evm.sender() = storage.owner, Not_owner); }
deploy(const owner : address) is { storage.owner := owner; }
external view function owner() : address is storage.owner
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let data = word_data("deploy(address)", &[w(0xabc)]);
    let later = exec(&runtime, &data, HashMap::new(), w(7), w(0), w(0)).expect("later");
    assert!(later.reverted, "a deployed proxy cannot run `deploy` again");
    let was = CONSTRUCTING.replace(true);
    let during = exec(&runtime, &data, HashMap::new(), w(7), w(0), w(0));
    CONSTRUCTING.set(was);
    let during = during.expect("during");
    assert!(!during.reverted, "{}", pretty(&during.returndata));
    assert_eq!(slot(&during.storage, 0), w(0xabc));
    let abi = crate::abi(src).expect("abi");
    assert!(abi.contains("\"name\": \"deploy\""), "{abi}");
    assert!(!abi.contains("constructor"), "{abi}");
}

/// `defer create Vault(args)` appends the encoded arguments to the creation code, so they
/// reach `deploy` and take part in the `CREATE2` address.
#[test]
fn created_contracts_receive_deploy_arguments() {
    let src = "\
contract Factory is {
  storage is record { last : address; }
  external function open(const fee : nat; const name : string) is {
    defer create Vault(Evm.sender(), fee, name) then (vault : address) {
      storage.last := vault;
    };
  }
  external function open_at(const salt : bytes32; const fee : nat) is {
    defer create Vault(Evm.sender(), fee, \"salted\") with salt = salt then (vault : address) {
      storage.last := vault;
    };
  }
}

contract Vault is {
  storage is record { owner : address; fee : nat; name : string; }
  deploy(const owner : address; const fee : nat; const name : string) is {
    storage.owner := owner;
    storage.fee := fee;
    storage.name := name;
  }
  external view function fee() : nat is storage.fee
}
";
    let contracts = crate::compile_contracts(src).expect("compile");
    let code = |name: &str| {
        contracts
            .iter()
            .find(|(n, _)| n.as_deref() == Some(name))
            .map(|(_, c)| c.clone())
            .expect(name)
    };
    let factory = deploy(&code("Factory")).expect("deploy");
    let w = Word::from_u64;
    let caller = w(0xabc);
    let name = [0x62u8; 40];
    let mut data = selector("open(uint256,string)").to_vec();
    for word in [w(30), w(64), w(name.len() as u64)] {
        data.extend_from_slice(&word.to_be_bytes());
    }
    data.extend_from_slice(&name);
    data.resize(4 + (data.len() - 4).div_ceil(32) * 32, 0);
    let opened = exec(&factory, &data, HashMap::new(), caller, w(0), w(0)).expect("open");
    assert!(!opened.reverted, "{}", pretty(&opened.returndata));
    let vault = slot(&opened.storage, 0);
    let (_, storage) = DEPLOYED
        .with(|d| d.borrow().get(&vault).cloned())
        .expect("deployed");
    assert_eq!(slot(&storage, 0), caller);
    assert_eq!(slot(&storage, 1), w(30));

    let salt = w(0x5a17);
    let at = exec(
        &factory,
        &word_data("open_at(bytes32,uint256)", &[salt, w(7)]),
        HashMap::new(),
        caller,
        w(0),
        w(0),
    )
    .expect("open_at");
    assert!(!at.reverted, "{}", pretty(&at.returndata));
    let init = [code("Vault"), deploy_args(caller, 7, b"salted")].concat();
    let mut buf = vec![0xff];
    buf.extend_from_slice(&w(0x1000).to_be_bytes()[12..]);
    buf.extend_from_slice(&salt.to_be_bytes());
    buf.extend_from_slice(&crate::keccak::keccak256(&init));
    let mut expected = [0u8; 32];
    expected[12..].copy_from_slice(&crate::keccak::keccak256(&buf)[12..]);
    assert_eq!(slot(&at.storage, 0), Word::from_be_bytes(expected));

    for (args, want) in [
        ("Evm.sender(), 1n", "`Vault` expects 3 arguments"),
        ("Evm.sender(), \"no\", \"x\"", "argument has the wrong type"),
    ] {
        let bad = src.replace("Vault(Evm.sender(), fee, name)", &format!("Vault({args})"));
        let err = crate::compile_contracts(&bad).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}

/// `Bytes.concat` and `String.concat` join values in order; `Abi.encode_call` checks its
/// arguments against an interface method and encodes like Solidity's `abi.encodeCall`.
#[test]
fn concatenation_and_typed_call_encoding() {
    let src = "\
interface Token is { function transfer(to : address; amount : nat) : bool; }
storage is record { joined : bytes; text : string; call_data : bytes; }
external function join(const a : bytes; const b : bytes) is {
  storage.joined := Bytes.concat(a, 0xdeadbeef, b);
}
external function greet(const name : string) is {
  storage.text := String.concat(\"hello, \", name, \"!\");
}
external function encode(const to : address; const amount : nat) is {
  storage.call_data := Abi.encode_call(Token.transfer, to, amount);
}
external pure function same(const to : address; const amount : nat) : bool is
  Crypto.keccak256(Abi.encode_call(Token.transfer, to, amount))
    = Crypto.keccak256(Abi.encode_with_signature(\"transfer(address,uint256)\", to, amount))
external view function joined() : bytes is storage.joined
external view function text() : string is storage.text
external view function call_data() : bytes is storage.call_data
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let run = |data: Vec<u8>, storage: HashMap<Word, Word>| {
        exec(&runtime, &data, storage, w(7), w(0), w(0)).expect("run")
    };
    let view = |sig: &str, storage: &HashMap<Word, Word>| {
        abi_string_value(&run(word_data(sig, &[]), storage.clone()).returndata)
    };
    let two = |sig: &str, a: &[u8], b: &[u8]| {
        let mut c = selector(sig).to_vec();
        let pad = |n: usize| n.div_ceil(32) * 32;
        c.extend_from_slice(&w(64).to_be_bytes());
        c.extend_from_slice(&w(96 + pad(a.len()) as u64).to_be_bytes());
        for part in [a, b] {
            c.extend_from_slice(&w(part.len() as u64).to_be_bytes());
            c.extend_from_slice(part);
            c.resize(c.len() + pad(part.len()) - part.len(), 0);
        }
        c
    };
    // Short and long results, around a fixed `bytes4`.
    for (a, b) in [
        (&b"ab"[..], &b"cd"[..]),
        (&[1u8; 20][..], &[2u8; 30][..]),
        (&b""[..], &b""[..]),
    ] {
        let out = run(two("join(bytes,bytes)", a, b), HashMap::new());
        assert!(!out.reverted, "{}", pretty(&out.returndata));
        let mut want = a.to_vec();
        want.extend_from_slice(&[0xde, 0xad, 0xbe, 0xef]);
        want.extend_from_slice(b);
        assert_eq!(view("joined()", &out.storage), want);
    }
    for name in [&b"lithe"[..], &[0x61; 40][..]] {
        let out = run(abi_string("greet(string)", name), HashMap::new());
        let mut want = b"hello, ".to_vec();
        want.extend_from_slice(name);
        want.push(b'!');
        assert_eq!(view("text()", &out.storage), want);
    }
    let encoded = run(
        word_data("encode(address,uint256)", &[w(0xbeef), w(5)]),
        HashMap::new(),
    );
    let mut want = selector("transfer(address,uint256)").to_vec();
    want.extend_from_slice(&w(0xbeef).to_be_bytes());
    want.extend_from_slice(&w(5).to_be_bytes());
    assert_eq!(view("call_data()", &encoded.storage), want);
    let same = run(
        word_data("same(address,uint256)", &[w(1), w(2)]),
        HashMap::new(),
    );
    assert_eq!(load_bytes(&same.returndata, 0), w(1));

    for (body, want) in [
        (
            "Abi.encode_call(Token.transfer, Evm.sender())",
            "`Token.transfer` expects 2 arguments",
        ),
        (
            "Abi.encode_call(Token.mint, Evm.sender(), 1n)",
            "unknown interface method `Token.mint`",
        ),
        (
            "Abi.encode_call(\"transfer(address,uint256)\", Evm.sender(), 1n)",
            "expects an interface method",
        ),
        (
            "Bytes.concat(1n)",
            "`Bytes.concat` joins `bytes` and `bytesN` values",
        ),
    ] {
        let src = format!(
            "interface Token is {{ function transfer(to : address; amount : nat) : bool; }}\nstorage is record {{ b : bytes; }}\nexternal function f() is {{ storage.b := {body}; }}\n"
        );
        let err = compile(&src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
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

#[test]
fn modules_compose_without_inheritance() {
    let src = include_str!("../examples/compose.lithe");
    let abi = crate::abi(src).expect("abi");
    assert!(abi.contains("\"name\": \"transfer\""), "{abi}");
    assert!(abi.contains("\"name\": \"balance_of\""), "{abi}");
    assert!(!abi.contains("Ledger.transfer"), "{abi}");
    assert!(abi.contains("InsufficientBalance"), "{abi}");
    assert!(abi.contains("Paused"), "{abi}");
    assert!(abi.contains("Transfer"), "{abi}");

    let tree = crate::abi_tree(src).expect("abi-tree");
    let transfer_route = route_text(&tree, "transfer");
    assert!(transfer_route.contains("  - Ledger.transfer\n"), "{tree}");
    assert!(
        transfer_route.contains("Ledger.ledger.balances"),
        "{transfer_route}"
    );
    assert!(transfer_route.contains("Transfer"), "{tree}");
    assert!(transfer_route.contains("InsufficientBalance"), "{tree}");
    assert!(
        !transfer_route.contains("settings"),
        "raw transfer must not see the pause flag\n{transfer_route}"
    );
    assert!(tree.contains("Guarded.transfer"), "{tree}");

    let report = crate::errors(src).expect("errors");
    assert!(
        report.contains("transfer(address,uint256)") && report.contains("InsufficientBalance"),
        "{report}"
    );
    assert!(
        report.contains("guarded_transfer(address,uint256)") && report.contains("Paused()"),
        "{report}"
    );

    let hidden = "\
module Ledger is {
  storage ledger at \"lithe.ledger\" is record {
    n : nat;
  }

  function set(const n : nat) is {
    ledger.n := n;
  }
}

contract Token is {
  use Ledger;

  external function go(const n : nat) is {
    Ledger.set(n);
  }
}
";
    let hidden_abi = crate::abi(hidden).expect("hidden");
    assert!(hidden_abi.contains("\"name\": \"go\""), "{hidden_abi}");
    assert!(!hidden_abi.contains("\"name\": \"set\""), "{hidden_abi}");

    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let caller = Word::from_u64(1);
    let other = Word::from_u64(2);
    let minted = call(
        &runtime,
        "mint(address,uint256)",
        &[caller, Word::from_u64(100)],
    );
    assert!(!minted.reverted, "{}", pretty(&minted.returndata));
    let mut storage = minted.storage.clone();

    let owed = exec(
        &runtime,
        &word_data("balance_of(address)", &[caller]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("balance");
    assert!(!owed.reverted, "{}", pretty(&owed.returndata));
    assert_eq!(load_bytes(&owed.returndata, 0), Word::from_u64(100));

    let open = exec(
        &runtime,
        &word_data("is_paused()", &[]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("open");
    assert!(!open.reverted, "{}", pretty(&open.returndata));
    assert_eq!(load_bytes(&open.returndata, 0), Word::from_u64(0));
    let qualified = exec(
        &runtime,
        &word_data("flag()", &[]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("flag view");
    assert!(!qualified.reverted, "{}", pretty(&qualified.returndata));
    assert_eq!(load_bytes(&qualified.returndata, 0), Word::from_u64(0));

    let sent = exec(
        &runtime,
        &word_data("transfer(address,uint256)", &[other, Word::from_u64(40)]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("transfer");
    assert!(!sent.reverted, "{}", pretty(&sent.returndata));
    assert!(sent.trace.iter().any(|ev| matches!(ev, Ev::Log { .. })));
    storage = sent.storage.clone();

    let left = exec(
        &runtime,
        &word_data("balance_of(address)", &[caller]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("left");
    assert_eq!(load_bytes(&left.returndata, 0), Word::from_u64(60));
    let gained = exec(
        &runtime,
        &word_data("balance_of(address)", &[other]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("gained");
    assert_eq!(load_bytes(&gained.returndata, 0), Word::from_u64(40));

    let broke = exec(
        &runtime,
        &word_data("transfer(address,uint256)", &[other, Word::from_u64(61)]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("broke");
    assert!(broke.reverted);
    assert!(broke
        .returndata
        .starts_with(&selector("InsufficientBalance(uint256,uint256)")));

    let paused = exec(
        &runtime,
        &word_data("pause()", &[]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("pause");
    assert!(!paused.reverted, "{}", pretty(&paused.returndata));
    storage = paused.storage.clone();
    let flag = exec(
        &runtime,
        &word_data("is_paused()", &[]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("flag");
    assert_eq!(load_bytes(&flag.returndata, 0), Word::from_u64(1));
    let qualified = exec(
        &runtime,
        &word_data("flag()", &[]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("flagged");
    assert_eq!(load_bytes(&qualified.returndata, 0), Word::from_u64(1));

    let still = exec(
        &runtime,
        &word_data("transfer(address,uint256)", &[other, Word::from_u64(10)]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("still");
    assert!(!still.reverted, "{}", pretty(&still.returndata));
    let after = exec(
        &runtime,
        &word_data("balance_of(address)", &[caller]),
        still.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("after");
    assert_eq!(load_bytes(&after.returndata, 0), Word::from_u64(50));

    let blocked = exec(
        &runtime,
        &word_data(
            "guarded_transfer(address,uint256)",
            &[other, Word::from_u64(1)],
        ),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("blocked");
    assert!(blocked.reverted);
    assert!(blocked.returndata.starts_with(&selector("Paused()")));
    let safer = exec(
        &runtime,
        &word_data(
            "safe_transfer(address,uint256)",
            &[other, Word::from_u64(1)],
        ),
        storage,
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("safer");
    assert!(safer.reverted);
    assert!(safer.returndata.starts_with(&selector("Paused()")));

    let path =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/compose/token.lithe");
    let imported = deploy(&crate::compile_file(&path).expect("import")).expect("deploy");
    let ping = call(&imported, "ping(uint256)", &[Word::from_u64(7)]);
    assert!(!ping.reverted, "{}", pretty(&ping.returndata));
    let root = crate::keccak::erc7201("lithe.compose");
    assert_eq!(
        ping.storage
            .get(&root)
            .copied()
            .unwrap_or(Word::from_u64(0)),
        Word::from_u64(7)
    );
    let pinged = exec(
        &imported,
        &word_data("pinged()", &[]),
        ping.storage.clone(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("pinged");
    assert_eq!(load_bytes(&pinged.returndata, 0), Word::from_u64(7));
    // `Token` has `ILedger`, so it answers for its ERC-165 id.
    let ledger_id = u32::from_be_bytes(selector("ping(uint256)")) ^ u32::from_be_bytes(selector("pinged()"));
    let supports = call(
        &imported,
        "supportsInterface(bytes4)",
        &[Word::from_u64(u64::from(ledger_id)).shl(224)],
    );
    assert_eq!(load_bytes(&supports.returndata, 0), Word::from_u64(1));
    let pinger_path =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/compose/pinger.lithe");
    install_mocks();
    let pinger = deploy(&crate::compile_file(&pinger_path).expect("pinger")).expect("deploy");
    let relay = exec(
        &pinger,
        &word_data("relay(address,uint256)", &[Word::from_u64(0xcd), Word::from_u64(9)]),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("relay");
    assert!(!relay.reverted, "{}", pretty(&relay.returndata));
    assert!(relay.detail.join("\n").contains(&hex(&selector("ping(uint256)"))));

    let votes_path =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/votes.lithe");
    let layout = crate::storage_layout(&votes_path).expect("layout");
    assert!(
        layout.contains("ERC20.erc20 \"lithe.std.erc20\""),
        "{layout}"
    );
    assert!(
        layout.contains("ERC20Votes.votes \"lithe.std.erc20.votes\""),
        "{layout}"
    );
    let votes = deploy(&crate::compile_file(&votes_path).expect("votes")).expect("deploy");
    let minted = call(
        &votes,
        "mint(address,uint256)",
        &[caller, Word::from_u64(5)],
    );
    assert!(!minted.reverted, "{}", pretty(&minted.returndata));
    let supply = exec(
        &votes,
        &word_data("total_supply()", &[]),
        minted.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("supply");
    assert_eq!(load_bytes(&supply.returndata, 0), Word::from_u64(5));
    let tree = crate::abi_tree_file(&votes_path).expect("votes tree");
    assert!(tree.contains("ERC20.erc20.balances"), "{tree}");
    assert!(tree.contains("ERC20Votes.votes.delegates"), "{tree}");
    let delegated = exec(
        &votes,
        &word_data("delegate(address,address)", &[caller, other]),
        minted.storage,
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("delegate");
    assert!(!delegated.reverted, "{}", pretty(&delegated.returndata));
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

/// Every example and every program in `fuzz/`, with a path relative to the crate root.
fn differential_targets() -> Vec<(std::path::PathBuf, String)> {
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

fn steps_from_env(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|n| n.parse().ok())
        .unwrap_or(default)
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
    let ours = deploy(&crate::compile_file(path).unwrap_or_else(|e| panic!("{rel}: {e}")))
        .unwrap_or_else(|e| panic!("{rel}: deploy: {e}"));
    let checked = crate::check::check(crate::modules::load(path).expect("load")).expect("check");
    let methods = crate::route::method_ids(&checked).expect("methods");
    compare_builds(rel, &methods, reference, &ours, steps, slots);
}

/// Replays one random call sequence against two runtimes of the same program.
fn compare_builds(
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
        let balance = Word::from_u64(10_000_000_000_000_000_000);
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
        let (want, got) = (run(reference, &theirs), run(ours, &mine));
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
        assert_eq!(want.detail, got.detail, "{ctx}: effects");
        // When storage is written is not observable; what it ends up holding is.
        let effects = |trace: &[Ev]| {
            let kept: Vec<&Ev> = trace
                .iter()
                .filter(|ev| !matches!(ev, Ev::SStore { .. }))
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
        if !want.reverted {
            succeeded += 1;
            theirs = want.storage;
            mine = got.storage;
        }
    }
    eprintln!("{rel}: {succeeded}/{steps} calls succeeded");
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

/// ABI words for a dynamic array argument or result: length, then elements.
fn abi_array(words: &[Word]) -> Vec<u8> {
    let mut out = Word::from_u64(words.len() as u64).to_be_bytes().to_vec();
    for w in words {
        out.extend_from_slice(&w.to_be_bytes());
    }
    out
}

/// Dynamic lists cross the ABI both ways, live in `var`s and `const`s, go to and from
/// storage, and are logged, encoded, and compared, as Solidity's `T[]` values are.
#[test]
fn dynamic_lists_cross_the_abi() {
    let mut l = Session::new("examples/lists.lithe");
    let w = Word::from_u64;
    let list = |sig: &str, items: &[Word]| {
        let mut data = selector(sig).to_vec();
        data.extend_from_slice(&w(32).to_be_bytes());
        data.extend(abi_array(items));
        data
    };
    let run = |l: &mut Session, data: Vec<u8>| {
        let out = exec(&l.runtime, &data, l.storage.clone(), w(7), w(0), w(0)).expect("call");
        if !out.reverted {
            l.storage = out.storage.clone();
        }
        out
    };
    // Decoding, with Solidity's bounds and element checks.
    let out = run(&mut l, list("first(uint256[])", &[w(9), w(8)]));
    assert_eq!(load_bytes(&out.returndata, 0), w(9));
    let out = run(&mut l, list("first(uint256[])", &[]));
    assert!(out.reverted);
    assert_eq!(load_bytes(&out.returndata, 4), w(0x32));
    let out = run(&mut l, list("count(address[])", &[w(1), w(2), w(3)]));
    assert_eq!(load_bytes(&out.returndata, 0), w(3));
    assert!(
        run(
            &mut l,
            list("count(address[])", &[Word::from_u64(1).shl(160)])
        )
        .reverted
    );
    let mut short = list("count(address[])", &[w(1), w(2)]);
    short.truncate(short.len() - 1);
    assert!(run(&mut l, short).reverted);
    let mut far = selector("count(address[])").to_vec();
    far.extend_from_slice(&w(0x1000).to_be_bytes());
    assert!(run(&mut l, far).reverted);

    // `bytes4` elements sit in the high bytes on the wire, and come back the same way.
    let tags = [
        Word::from_u64(0xdeadbeef).shl(224),
        Word::from_u64(0x01020304).shl(224),
    ];
    let out = run(&mut l, list("echo(bytes4[])", &tags));
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    let mut want = w(32).to_be_bytes().to_vec();
    want.extend(abi_array(&tags));
    assert_eq!(out.returndata, want);

    // To storage and back, shrinking clears what the shorter list no longer uses.
    assert!(!run(&mut l, list("save(uint256[])", &[w(1), w(2), w(3)])).reverted);
    let out = run(&mut l, word_data("saved()", &[]));
    let mut want = w(32).to_be_bytes().to_vec();
    want.extend(abi_array(&[w(1), w(2), w(3)]));
    assert_eq!(out.returndata, want);
    assert!(!run(&mut l, list("save(uint256[])", &[w(5)])).reverted);
    let base = keccak_word(&w(0).to_be_bytes());
    assert_eq!(l.storage.get(&base).copied(), Some(w(5)));
    for i in 1..3u64 {
        assert!(
            l.storage
                .get(&base.wrapping_add(w(i)))
                .is_none_or(|v| v.is_zero()),
            "slot {i}"
        );
    }
    assert_eq!(slot(&l.storage, 0), w(1));

    // A `var` grows by writing at its length.
    let out = run(&mut l, word_data("build(uint256,uint256)", &[w(4), w(6)]));
    let mut want = w(32).to_be_bytes().to_vec();
    want.extend(abi_array(&[w(10), w(6)]));
    assert_eq!(out.returndata, want);

    // An event's list is ABI-encoded in its data.
    let out = run(&mut l, list("log_batch(uint256[])", &[w(3), w(4)]));
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    let logs: Vec<&Ev> = out
        .trace
        .iter()
        .filter(|e| matches!(e, Ev::Log { .. }))
        .collect();
    assert_eq!(logs.len(), 1);
    let data = out
        .detail
        .iter()
        .find(|d| d.starts_with("log"))
        .expect("log detail");
    let mut want = w(32).to_be_bytes().to_vec();
    want.extend(abi_array(&[w(3), w(4)]));
    assert!(data.contains(&hex(&want)), "{data}");

    // `Abi.encode`, equality, and passing a list to a function.
    let out = run(&mut l, list("enc(uint256[])", &[w(3), w(4)]));
    let mut inner = w(32).to_be_bytes().to_vec();
    inner.extend(abi_array(&[w(3), w(4)]));
    assert_eq!(abi_string_value(&out.returndata), inner);
    let mut data = selector("same(uint256[],uint256[])").to_vec();
    data.extend_from_slice(&w(64).to_be_bytes());
    data.extend_from_slice(&w(160).to_be_bytes());
    data.extend(abi_array(&[w(1), w(2)]));
    data.extend(abi_array(&[w(1), w(2)]));
    assert_eq!(load_bytes(&run(&mut l, data.clone()).returndata, 0), w(1));
    let n = data.len();
    data[n - 1] = 3;
    assert_eq!(load_bytes(&run(&mut l, data).returndata, 0), w(0));
    let out = run(&mut l, list("sum2(uint256[])", &[w(20), w(22)]));
    assert_eq!(load_bytes(&out.returndata, 0), w(42));
}

/// Lists and strings as query arguments and answers, as deferred-call arguments and
/// results, and from `Abi.decode`, against a contract that answers with its arguments.
#[test]
fn lists_and_strings_through_calls() {
    install_mocks();
    let mut c = Session::new("examples/list_calls.lithe");
    let w = Word::from_u64;
    let echo = w(0xcd);
    let with_list = |sig: &str, items: &[Word]| {
        let mut data = selector(sig).to_vec();
        data.extend_from_slice(&echo.to_be_bytes());
        data.extend_from_slice(&w(64).to_be_bytes());
        data.extend(abi_array(items));
        data
    };
    let send = |c: &mut Session, data: Vec<u8>| {
        let out = exec(&c.runtime, &data, c.storage.clone(), w(7), w(0), w(0)).expect("call");
        assert!(!out.reverted, "{}", pretty(&out.returndata));
        c.storage = out.storage.clone();
        out
    };
    let list_result = |items: &[Word]| {
        let mut want = w(32).to_be_bytes().to_vec();
        want.extend(abi_array(items));
        want
    };
    send(
        &mut c,
        with_list("ask(address,uint256[])", &[w(5), w(6), w(7)]),
    );
    assert_eq!(
        send(&mut c, word_data("got()", &[])).returndata,
        list_result(&[w(5), w(6), w(7)])
    );
    send(
        &mut c,
        with_list("send(address,address[])", &[w(0xa), w(0xb)]),
    );
    assert_eq!(
        send(&mut c, word_data("kept()", &[])).returndata,
        list_result(&[w(0xa), w(0xb)])
    );
    send(
        &mut c,
        with_list("ask_case(address,uint256[])", &[w(1), w(2), w(3), w(4)]),
    );
    assert_eq!(
        load_bytes(&send(&mut c, word_data("total()", &[])).returndata, 0),
        w(4)
    );
    let name = b"a name long enough to need a blob of its own";
    let mut data = selector("ask_name(address,string)").to_vec();
    data.extend_from_slice(&echo.to_be_bytes());
    data.extend_from_slice(&w(64).to_be_bytes());
    data.extend_from_slice(&w(name.len() as u64).to_be_bytes());
    data.extend_from_slice(name);
    data.resize(4 + (data.len() - 4).div_ceil(32) * 32, 0);
    send(&mut c, data);
    assert_eq!(
        abi_string_value(&send(&mut c, word_data("label()", &[])).returndata),
        name
    );
    let encoded = list_result(&[w(1), w(2)]);
    let out = send(
        &mut c,
        encode_args("decoded_length(bytes)", &[Arg::B(encoded)]),
    );
    assert_eq!(load_bytes(&out.returndata, 0), w(2));
    let out = exec(
        &c.runtime,
        &encode_args("decoded_length(bytes)", &[Arg::B(vec![0; 40])]),
        HashMap::new(),
        w(7),
        w(0),
        w(0),
    )
    .unwrap();
    assert!(
        !out.reverted,
        "a zero offset and zero length decode as an empty list"
    );
    let out = exec(
        &c.runtime,
        &encode_args("decoded_length(bytes)", &[Arg::B(vec![0xff; 64])]),
        HashMap::new(),
        w(7),
        w(0),
        w(0),
    )
    .unwrap();
    assert!(out.reverted);
    let out = send(&mut c, word_data("counted(uint256)", &[w(8)]));
    assert_eq!(out.returndata, list_result(&[w(8), w(9)]));
}

/// A topic stays on the stack while the data after it is encoded; no stored word the
/// optimizer keeps on the stack may end up in its place.
#[test]
fn topics_survive_encoded_event_data() {
    let src = "\
storage is record { n : nat; }
event E of record { indexed who : address; note : string; tail : string; ids : list(nat); }
external function f(const note : string; const ids : list(nat)) is {
  emit E { who = Evm.sender(); note = note; tail = note; ids = ids; };
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let mut data = selector("f(string,uint256[])").to_vec();
    for word in [64u64, 128, 2] {
        data.extend_from_slice(&w(word).to_be_bytes());
    }
    data.extend_from_slice(b"hi");
    data.resize(4 + 4 * 32, 0);
    data.extend(abi_array(&[w(7)]));
    let out = exec(&runtime, &data, HashMap::new(), w(0xabc), w(0), w(0)).expect("f");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    let topics = out
        .trace
        .iter()
        .find_map(|e| {
            if let Ev::Log { topics } = e {
                Some(topics.clone())
            } else {
                None
            }
        })
        .expect("a log");
    assert_eq!(topics[1], w(0xabc));
    let mut want = Vec::new();
    for word in [96u64, 160, 224, 2] {
        want.extend_from_slice(&w(word).to_be_bytes());
    }
    let mut hi = [0u8; 32];
    hi[..2].copy_from_slice(b"hi");
    want.extend_from_slice(&hi);
    want.extend_from_slice(&w(2).to_be_bytes());
    want.extend_from_slice(&hi);
    want.extend(abi_array(&[w(7)]));
    let log = out
        .detail
        .iter()
        .find(|d| d.starts_with("log"))
        .expect("log detail");
    assert!(log.ends_with(&hex(&want)), "{log}");
}

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
        crate::compile_file(&main).unwrap_or_else(|e| panic!("{path}: {e}"));
    }
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

fn w(n: u64) -> Arg {
    Arg::W(Word::from_u64(n))
}

fn keccak_word(data: &[u8]) -> Word {
    Word::from_be_bytes(crate::keccak::keccak256(data))
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

/// Deploys a split build: each prerequisite facet at its `CREATE2` address, then the router.
/// Returns the router's runtime.
fn deploy_split(split: &crate::split::Split) -> Vec<u8> {
    deploy_facets(split);
    deploy(&split.creation).unwrap_or_else(|e| panic!("router: {e}"))
}

fn deploy_facets(split: &crate::split::Split) {
    for facet in split.prerequisites() {
        let runtime = deploy(&facet.init).unwrap_or_else(|e| panic!("{}: {e}", facet.name));
        DEPLOYED.with(|d| {
            d.borrow_mut().insert(
                crate::split::address_word(facet.address),
                (runtime, HashMap::new()),
            )
        });
    }
}

fn split_opts(limit: usize) -> crate::Options {
    crate::Options {
        size_limit: limit,
        ..crate::Options::default()
    }
}

fn all_facets() -> crate::Options {
    crate::Options {
        split: crate::SplitMode::All,
        ..crate::Options::default()
    }
}

fn checked_src(src: &str) -> crate::check::Checked {
    crate::check::check(crate::parse::parse(src).expect("parse")).expect("check")
}

fn whole_build(checked: &crate::check::Checked) -> crate::gen::Built {
    crate::gen::codegen(checked, &crate::split::Shape::default()).expect("whole")
}

fn facet_names(split: &crate::split::Split) -> Vec<&str> {
    split.facets.iter().map(|facet| facet.name.as_str()).collect()
}

/// Every program that exposes a module, with every exposed module in its facet, behaves
/// exactly like its unsplit build: the same return data, reverts, effects, and storage, slot
/// for slot. `LITHE_SPLIT_STEPS` sets calls per program.
#[test]
fn split_preserves_behavior() {
    let steps = steps_from_env("LITHE_SPLIT_STEPS", 200);
    let mut compared = 0;
    for (path, rel) in differential_targets() {
        let checked =
            crate::check::check(crate::modules::load(&path).expect("load")).expect("check");
        let split = crate::split::build(&checked, "Test", &all_facets())
            .unwrap_or_else(|e| panic!("{rel}: {e}"));
        if split.facets.is_empty() {
            continue;
        }
        let whole = whole_build(&checked);
        OPAQUE_CODE.set(true);
        install_mocks();
        let reference = deploy(&whole.code).unwrap_or_else(|e| panic!("{rel}: {e}"));
        let ours = deploy_split(&split);
        let methods = crate::route::method_ids(&checked).expect("methods");
        eprintln!("{rel}: router and {} facets", split.facets.len());
        compare_builds(&rel, &methods, &reference, &ours, steps, true);
        compared += 1;
    }
    assert!(compared >= 5, "only {compared} programs split");
}

const SPLIT_VAULT: &str = r#"
upgradeable

error Not_owner;

module Counter is {
  storage counter at "split.counter" is record {
    count : nat;
  }

  external function bump(const by : nat) is {
    counter.count := counter.count + by;
  }

  external view function count() : nat is
    counter.count
}

storage is record {
  owner : address;
}

storage settings at "split.settings" is record {
  fee : nat;
}

upgrade guard is {
  assert(Evm.sender() = storage.owner, Not_owner);
}

deploy(const owner : address) is {
  storage.owner := owner;
}

migrate init(const fee : nat) is {
  settings.fee := fee;
}

external use Counter is {
  function bump(by : nat);
  view function count() : nat;
}

external view function fee() : nat is
  settings.fee
"#;

/// A standard ERC-1967 proxy's runtime: `delegatecall` the implementation in the slot with
/// the whole calldata, then return or revert with what it did.
fn proxy_runtime() -> Vec<u8> {
    let mut code = vec![0x36, 0x5f, 0x5f, 0x37, 0x5f, 0x5f, 0x36, 0x5f, 0x7f];
    code.extend_from_slice(&crate::keccak::erc1967_implementation().to_be_bytes());
    code.extend_from_slice(&[0x54, 0x5a, 0xf4, 0x3d, 0x5f, 0x5f, 0x3e, 0x60, 0x36, 0x57]);
    code.extend_from_slice(&[0x3d, 0x5f, 0xfd, 0x5b, 0x3d, 0x5f, 0xf3]);
    assert_eq!(code[0x36], 0x5b);
    code
}

fn upgrade_to_and_call(implementation: Word, data: &[u8]) -> Vec<u8> {
    let mut out = selector("upgradeToAndCall(address,bytes)").to_vec();
    out.extend_from_slice(&implementation.to_be_bytes());
    out.extend_from_slice(&Word::from_u64(64).to_be_bytes());
    out.extend_from_slice(&Word::from_u64(data.len() as u64).to_be_bytes());
    out.extend_from_slice(data);
    out.resize(out.len() + (32 - data.len() % 32) % 32, 0);
    out
}

/// One proxy moves from a whole implementation to one that runs `Counter` from its facet,
/// and back. Storage stays where it is, and the migration runs in the router, inside the
/// upgrade.
#[test]
fn upgrades_move_between_whole_and_split() {
    let checked = checked_src(SPLIT_VAULT);
    let slot = crate::keccak::erc1967_implementation();
    let whole = deploy(&whole_build(&checked).code).expect("whole");
    let split = crate::split::build(&checked, "Vault", &all_facets()).expect("split");
    assert_eq!(facet_names(&split), ["Counter"]);
    assert!(split.entries.iter().any(|e| e.name == "init (migrate)"));
    let router = deploy_split(&split);
    let (a, b) = (Word::from_u64(0xa11), Word::from_u64(0xb22));
    DEPLOYED.with(|d| {
        let mut d = d.borrow_mut();
        d.insert(a, (whole, HashMap::new()));
        d.insert(b, (router, HashMap::new()));
    });
    let proxy = proxy_runtime();
    let owner = Word::from_u64(1);
    // The proxy's storage as `deploy` would have left it: the owner in slot 0.
    let storage: std::cell::RefCell<HashMap<Word, Word>> =
        std::cell::RefCell::new([(slot, a), (Word::from_u64(0), owner)].into_iter().collect());
    let send = |data: Vec<u8>| {
        let now = storage.borrow().clone();
        let out = exec(&proxy, &data, now, owner, Word::from_u64(0), Word::from_u64(0))
            .expect("run");
        if !out.reverted {
            *storage.borrow_mut() = out.storage.clone();
        }
        out
    };
    let word = |n: u64| Word::from_u64(n).to_be_bytes().to_vec();
    assert!(!send(word_data("bump(uint256)", &[Word::from_u64(5)])).reverted);
    let init = word_data("init(uint256)", &[Word::from_u64(30)]);
    let out = send(upgrade_to_and_call(b, &init));
    assert!(!out.reverted, "upgrade into the split build: {}", pretty(&out.returndata));
    assert_eq!(storage.borrow()[&slot], b);
    assert_eq!(send(word_data("count()", &[])).returndata, word(5));
    assert_eq!(send(word_data("fee()", &[])).returndata, word(30));
    assert!(!send(word_data("bump(uint256)", &[Word::from_u64(2)])).reverted);
    // Outside an upgrade, a migration reverts.
    assert!(send(init.clone()).reverted);
    let out = send(upgrade_to_and_call(a, &[]));
    assert!(!out.reverted, "back to the whole build");
    assert_eq!(storage.borrow()[&slot], a);
    assert_eq!(send(word_data("count()", &[])).returndata, word(7));
    assert_eq!(send(word_data("fee()", &[])).returndata, word(30));
}

/// A facet runs its module's externals and nothing else: no `deploy`, no migration, and no
/// upgrade machinery. Called directly, it only touches its own empty storage.
#[test]
fn facets_run_only_their_module() {
    let checked = checked_src(SPLIT_VAULT);
    let split = crate::split::build(&checked, "Vault", &all_facets()).expect("split");
    let facet = &split.facets[0];
    let names: Vec<&str> = facet.entries.iter().map(|e| e.name.as_str()).collect();
    assert_eq!(names, ["bump", "count"]);
    let runtime = deploy(&facet.init).expect("facet");
    for sig in ["deploy(address)", "init(uint256)", "proxiableUUID()", "fee()"] {
        assert!(call_raw(&runtime, &word_data(sig, &[Word::from_u64(1)])).reverted, "{sig}");
    }
    let out = call_raw(&runtime, &word_data("bump(uint256)", &[Word::from_u64(3)]));
    assert!(!out.reverted);
    assert_eq!(out.storage.len(), 1, "only the counter's own slot");
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

/// A router refuses to deploy while one of its facets has no code, with or without `deploy`.
#[test]
fn routers_need_their_facets() {
    let plain = "module M is {\n\
          storage m at \"t.m\" is record { a : nat; b : nat; }\n\
          external function set_a(const v : nat) is { m.a := v * 3n + m.b; }\n\
          external view function sum() : nat is m.a + m.b\n\
        }\n\
        storage is record { n : nat; }\n\
        external use M is {\n\
          function set_a(v : nat);\n\
          view function sum() : nat;\n\
        }\n";
    let constructed = format!("{plain}deploy(const a : nat) is {{ storage.n := a; }}\n");
    for src in [plain.to_string(), constructed] {
        let split = crate::split::build(&checked_src(&src), "T", &all_facets()).expect("split");
        let mut init = split.creation.clone();
        init.extend_from_slice(&Word::from_u64(4).to_be_bytes());
        let out = construct(&init, Word::from_u64(1), Word::from_u64(0)).expect("run");
        assert!(out.reverted, "{src}");
        deploy_facets(&split);
        let out = construct(&init, Word::from_u64(1), Word::from_u64(0)).expect("run");
        assert!(!out.reverted, "{src}: {}", pretty(&out.returndata));
        DEPLOYED.with(|d| d.borrow_mut().clear());
    }
}

const SPLIT_MODULES: &str = r#"
module Alpha is {
  storage alpha_state at "split.alpha" is record {
    n : nat;
  }

  error Alpha_zero;

  function add(const a : nat; const b : nat) is {
    alpha_state.n := alpha_state.n + a * b + a / (b + 1n);
  }

  external function alpha_add(const a : nat; const b : nat) is
    add(a, b)

  external function alpha_mix(const a : nat; const b : nat; const c : nat)
    raises Alpha_zero
  is {
    assert(c > 0n, Alpha_zero);
    alpha_state.n := alpha_state.n * 3n + a * b * c + (a + b) / c + (a * c) % (b + 5n);
    add(a % 7n, c);
  }

  external view function alpha() : nat is
    alpha_state.n
}

module Beta is {
  storage beta_state at "split.beta" is record {
    m : nat;
  }

  external function beta_add(const a : nat; const b : nat) is {
    beta_state.m := beta_state.m * 2n + a % (b + 3n) + b;
  }

  external view function beta() : nat is
    beta_state.m
}
"#;

fn pair_src(extra: &str) -> String {
    format!(
        "{SPLIT_MODULES}
contract Pair is {{
  storage is record {{
    total : nat;
  }}

  external use Alpha is {{
    function alpha_add(a : nat; b : nat);
    function alpha_mix(a : nat; b : nat; c : nat)
      raises Alpha_zero;
    view function alpha() : nat;
  }}

  external use Beta is {{
    function beta_add(a : nat; b : nat);
    view function beta() : nat;
  }}

  external function mix(const a : nat; const b : nat; const c : nat) is {{
    storage.total := storage.total * 5n + a * b * c + (a + b) / (c + 5n) + (a * c) % (b + 10n);
    storage.total := storage.total + (a * a + b * b) / (c * c + 1n) + (a + c) % (b + 3n);
  }}
{extra}
}}
"
    )
}

/// A facet is built from its module alone. Contracts that expose the module in different
/// ways, use other modules, or write their own code share one facet at one address, and
/// every build of the same source gives the same router and facets.
#[test]
fn facets_are_shared() {
    let pair = checked_src(&pair_src(""));
    let one = crate::split::build(&pair, "Pair", &all_facets()).expect("one");
    let two = crate::split::build(&pair, "Pair", &all_facets()).expect("two");
    assert_eq!(one.creation, two.creation);
    for (x, y) in one.facets.iter().zip(&two.facets) {
        assert_eq!((x.address, &x.init), (y.address, &y.init));
    }
    let other = format!(
        "{SPLIT_MODULES}
contract Other is {{
  storage is record {{
    a : address;
    b : nat;
  }}

  error Mine;

  use Beta;

  external use Alpha is {{
    view function alpha() : nat;
  }}

  external function set(const who : address) raises Mine is {{
    assert(who <> Address.zero, Mine);
    storage.a := who;
  }}
}}
"
    );
    let other = crate::split::build(&checked_src(&other), "Other", &all_facets()).expect("other");
    assert_eq!(facet_names(&other), ["Alpha"]);
    let alpha = |split: &crate::split::Split| {
        let facet = split.facets.iter().find(|f| f.name == "Alpha").expect("Alpha");
        (facet.address, facet.init.clone())
    };
    assert_eq!(alpha(&one), alpha(&other));
    // The router forwards only what the contract declares; the facet has all three.
    let facet = &other.facets[0];
    assert_eq!(facet.entries.len(), 3);
    assert_eq!(other.forwarded(facet).len(), 1);
    let runtime = deploy_split(&other);
    let out = call(&runtime, "alpha_add(uint256,uint256)", &[Word::from_u64(1), Word::from_u64(2)]);
    assert!(out.reverted, "undeclared externals are not reachable through the router");
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// Over the limit, `auto` moves the module that saves the most into its facet first, and
/// stops as soon as the router fits.
#[test]
fn auto_moves_the_largest_module_first() {
    let checked = checked_src(&pair_src(""));
    let whole = whole_build(&checked).runtime.len();
    let fits = crate::split::build(&checked, "Pair", &split_opts(whole)).expect("fits");
    assert!(fits.facets.is_empty());
    assert_eq!(fits.creation, whole_build(&checked).code);
    let first = (1..whole)
        .rev()
        .step_by(4)
        .find_map(|limit| {
            crate::split::build(&checked, "Pair", &split_opts(limit))
                .ok()
                .filter(|split| !split.facets.is_empty())
        })
        .expect("a limit that splits");
    assert_eq!(facet_names(&first), ["Alpha"]);
    assert!(first.whole == Some(whole));
    let both = (1..whole)
        .rev()
        .step_by(4)
        .find_map(|limit| {
            crate::split::build(&checked, "Pair", &split_opts(limit))
                .ok()
                .filter(|split| split.facets.len() == 2)
        })
        .expect("a limit that needs both");
    assert_eq!(facet_names(&both), ["Alpha", "Beta"]);
}

/// Only exposed modules can move: a contract over the limit that exposes none, or whose own
/// code is still too big, is an error that says so. With splitting off, the error lists
/// what takes the space.
#[test]
fn split_errors_say_what_cannot_move() {
    let checked = checked_src(SPLIT_VAULT);
    let whole = whole_build(&checked).runtime.len();
    let off = crate::Options {
        size_limit: whole - 1,
        split: crate::SplitMode::Off,
        ..crate::Options::default()
    };
    let err = crate::split::build(&checked, "Vault", &off)
        .err()
        .expect("too big")
        .to_string();
    let head = format!(
        "contract `Vault` is {} bytes; the limit is {}",
        crate::split::thousands(whole),
        crate::split::thousands(whole - 1)
    );
    assert!(err.starts_with(&head), "{err}");
    assert!(err.contains("\n  Vault "), "{err}");
    assert!(err.contains("\n  Counter "), "{err}");
    assert!(err.contains("\n  upgrade "), "{err}");
    assert!(err.contains("(dispatch and shared code)"), "{err}");
    let plain = checked_src(
        "storage is record { a : nat; }\n\
         external function set(const v : nat) is { storage.a := v * 3n + storage.a; }\n",
    );
    let err = crate::split::build(&plain, "Plain", &split_opts(10))
        .err()
        .expect("nothing can move")
        .to_string();
    assert!(err.contains("only a module exposed with `external use` can move"), "{err}");
    // Small enough for the facet, but not for the router with everything else.
    let split = crate::split::build(&checked, "Vault", &all_facets()).expect("split");
    let facet = split.facets[0].runtime.len().max(split.facets[0].init.len().div_ceil(2));
    assert!(facet < split.runtime.len());
    let err = crate::split::build(&checked, "Vault", &split_opts(facet))
        .err()
        .expect("the router is too big")
        .to_string();
    assert!(
        err.contains("contract `Vault` does not fit with every exposed module in its facet: its router is "),
        "{err}"
    );
}

/// A module's transient storage sits at the same slot in every contract that uses it and in
/// its facet, however many transient records come before it.
#[test]
fn module_transient_storage_has_one_slot() {
    let module = "module Lock is {\n\
          transient storage lock is record { held : bool; depth : nat; }\n\
          external function enter() is { lock.depth := lock.depth + 1n; }\n\
        }\n";
    let slot_of = |checked: &crate::check::Checked| {
        checked
            .transient_layout
            .iter()
            .find(|domain| domain.name == "Lock.lock")
            .map(|domain| domain.places.join(", "))
            .expect("Lock.lock")
    };
    let a = checked_src(&format!(
        "{module}storage is record {{ n : nat; }}\nexternal use Lock is {{ function enter(); }}\n"
    ));
    let b = checked_src(&format!(
        "{module}storage is record {{ n : nat; }}\n\
         transient storage is record {{ busy : bool; count : nat; more : nat; }}\n\
         external use Lock is {{ function enter(); }}\n\
         external function go() is {{ transient.busy := true; }}\n"
    ));
    let facet = crate::check::check(crate::split::facet_program(&a.source, "Lock")).expect("facet");
    assert_eq!(slot_of(&a), slot_of(&b));
    assert_eq!(slot_of(&a), slot_of(&facet));
}

const SPLIT_FACTORY: &str = r#"
module Folds is {
  storage folds at "split.folds" is record {
    count : nat;
  }

  external function fold(const a : nat; const b : nat; const c : nat) is {
    folds.count := folds.count + a * b * c + (a + b) / (c + 1n) + (a * c) % (b + 5n);
  }

  external function fold2(const a : nat; const b : nat; const c : nat) is {
    folds.count := folds.count * 2n + a * b * c + (a + b) / (c + 2n) + (a * c) % (b + 7n);
  }

  external function fold3(const a : nat; const b : nat; const c : nat) is {
    folds.count := folds.count * 3n + a * b * c + (a + b) / (c + 3n) + (a * c) % (b + 8n);
  }

  external view function folded() : nat is
    folds.count
}

contract Factory is {
  storage is record {
    last : address;
  }

  external function open() is {
    defer create Vault(Evm.sender()) then (vault : address) {
      storage.last := vault;
    };
  }

  external view function last() : address is
    storage.last
}

contract Vault is {
  storage is record {
    owner : address;
    count : nat;
  }

  deploy(const owner : address) is {
    storage.owner := owner;
  }

  external use Folds is {
    function fold(a : nat; b : nat; c : nat);
    function fold2(a : nat; b : nat; c : nat);
    function fold3(a : nat; b : nat; c : nat);
    view function folded() : nat;
  }

  external function bump(const by : nat) is {
    storage.count := storage.count + by * 3n;
  }

  external view function count() : nat is
    storage.count

  external view function owner() : address is
    storage.owner
}
"#;

/// A factory creates a contract that runs a module from its facet: the facet comes first in
/// the plan, and the router the factory creates reaches it.
#[test]
fn factories_create_split_contracts() {
    let units = crate::modules::split_units(crate::parse::parse(SPLIT_FACTORY).expect("parse"));
    let factory = units
        .into_iter()
        .find(|unit| unit.contract_name.as_deref() == Some("Factory"))
        .expect("factory");
    let checked = crate::check::check(factory).expect("check");
    let split = crate::split::build(&checked, "Factory", &all_facets()).expect("split");
    assert!(split.facets.is_empty(), "the factory itself exposes nothing");
    let needs: Vec<String> = split.prerequisites().iter().map(|f| f.name.clone()).collect();
    assert_eq!(needs, ["Folds"]);
    let factory = deploy_split(&split);
    let out = exec(
        &factory,
        &word_data("open()", &[]),
        HashMap::new(),
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("open");
    assert!(!out.reverted, "open: {}", pretty(&out.returndata));
    let last = exec(
        &factory,
        &word_data("last()", &[]),
        out.storage,
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("last");
    let vault = Word::from_be_bytes(last.returndata.try_into().expect("word"));
    let (code, storage) = DEPLOYED
        .with(|d| d.borrow().get(&vault).cloned())
        .expect("created");
    let folded = exec(
        &code,
        &word_data("fold(uint256,uint256,uint256)", &[Word::from_u64(2), Word::from_u64(3), Word::from_u64(4)]),
        storage,
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("fold");
    assert!(!folded.reverted, "fold: {}", pretty(&folded.returndata));
    for (sig, want) in [("folded()", 24 + 1), ("owner()", 7)] {
        let out = exec(
            &code,
            &word_data(sig, &[]),
            folded.storage.clone(),
            Word::from_u64(7),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect(sig);
        assert_eq!(out.returndata, Word::from_u64(want).to_be_bytes(), "{sig}");
    }
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// `lithe compile` prints a plan for a split contract, `lithe facets` which module runs
/// where, a directory build one artifact per facet, and `lithe upgrade-check` which facets
/// an upgrade reuses.
#[test]
fn split_tooling_output() {
    let dir = std::env::temp_dir().join(format!("lithe-split-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).expect("dir");
    let pair = dir.join("src/pair.lithe");
    std::fs::write(&pair, pair_src("")).expect("write");
    let pair2 = dir.join("pair2.lithe");
    let changed = pair_src("").replace("beta_state.m * 2n", "beta_state.m * 3n");
    std::fs::write(&pair2, changed).expect("write");
    let opts = all_facets();
    let compiled = crate::compile_file_with(&pair, &opts).expect("compile");
    assert!(compiled.text.starts_with("{\n  \"facets\": ["), "{}", compiled.text);
    assert!(compiled.text.contains("\"to\": \"0x4e59b44847b379578588920cA78FbF26c0B4956C\""));
    assert!(compiled.text.contains("\"name\": \"Beta\""), "{}", compiled.text);
    let note = compiled.note.expect("note");
    assert_eq!(note, "note: `Pair` `Alpha`, `Beta` run from their facets");
    let facets = crate::facets_file(&pair, &opts).expect("facets");
    assert!(facets.starts_with("router  "), "{facets}");
    assert!(facets.contains("  Pair: mix, supportsInterface\n"), "{facets}");
    assert!(facets.contains("\nfacet Alpha  0x"), "{facets}");
    assert!(facets.contains("\n  alpha_add, alpha_mix, alpha\n"), "{facets}");
    let unsplit = crate::facets_file(&pair, &crate::Options::default()).expect("facets");
    assert!(!unsplit.contains("facet "), "{unsplit}");
    assert!(unsplit.contains("  Alpha: alpha_add, alpha_mix, alpha\n"), "{unsplit}");
    let check = crate::upgrade_check(&pair, &pair2, &opts).expect("check");
    assert!(check.contains("facets\n  router "), "{check}");
    assert!(check.contains("\n  Alpha   unchanged  0x"), "{check}");
    assert!(check.contains("\n  Beta    new        0x"), "{check}");
    assert!(check.ends_with("\ncompatible\n"), "{check}");
    let out = dir.join("out");
    let built = crate::compile_dir_with(&dir.join("src"), &out, &opts).expect("dir");
    assert!(built.failed.is_empty(), "{}", built.failed.iter().map(|e| e.to_string()).collect::<String>());
    let artifact = std::fs::read_to_string(out.join("facets/Alpha.json")).expect("facet artifact");
    assert!(artifact.contains("\"name\": \"alpha_mix\""), "{artifact}");
    let router = std::fs::read_to_string(out.join("pair.lithe/Pair.json")).expect("router artifact");
    assert!(router.contains("\"facets\": [\n    {\n      \"name\": \"Alpha\""), "{router}");
    let vault = dir.join("vault.lithe");
    std::fs::write(&vault, SPLIT_VAULT).expect("write");
    let args = ["30".to_string()];
    let plan = crate::upgrade_plan("0xProxy", &vault, "init", None, &args, &opts).expect("upgrade");
    assert!(plan.contains("\"upgrade\": {\n    \"to\": \"0xProxy\""), "{plan}");
    assert!(plan.contains("\"router\": {\n    \"address\": \"0x"), "{plan}");
    let plain = crate::upgrade_plan("0xProxy", &vault, "init", None, &args, &crate::Options::default());
    assert!(plain.is_err(), "an unsplit upgrade needs --impl");
    let stubs = crate::stubs_file(&pair, "Alpha").expect("stubs");
    assert_eq!(
        stubs,
        "external use Alpha is {\n  function alpha_add(a : nat; b : nat);\n  function alpha_mix(a : nat; b : nat; c : nat)\n    raises Alpha_zero;\n  view function alpha() : nat;\n}\n"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// Writes `src` to its own file, so it can import the standard library, and compiles it.
fn compile_temp(name: &str, src: &str, opts: &crate::Options) -> Result<Vec<u8>, crate::Error> {
    let dir = std::env::temp_dir().join(format!("lithe-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("dir");
    let path = dir.join("main.lithe");
    std::fs::write(&path, src).expect("write");
    let out = crate::compile_file_with(&path, opts).map(|c| hex_decode(c.text.trim_start_matches("0x")));
    let _ = std::fs::remove_dir_all(&dir);
    out
}

fn abi_temp(name: &str, src: &str, opts: &crate::Options) -> String {
    let dir = std::env::temp_dir().join(format!("lithe-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("dir");
    let path = dir.join("main.lithe");
    std::fs::write(&path, src).expect("write");
    let abi = crate::abi_file_with(&path, opts).expect("abi");
    let _ = std::fs::remove_dir_all(&dir);
    abi
}

const ERC165_SRC: &str = r#"
import "std/token/erc20.lithe";
import "std/interfaces/erc1155.lithe";

module Uris is {
  storage uris at "t.uris" is record { base : string; }

  external view function uri(const id : nat) : string is
    uris.base
}

contract T is {
  external use ERC20 is IERC20, IERC20Metadata;
  external use Uris is IERC1155MetadataURI;
  storage is record {}
}
"#;

/// A contract that names interfaces answers ERC-165 for each: an interface's id is the XOR of
/// its methods' selectors, and the standard interfaces give the standard ids.
#[test]
fn erc165_answers_for_named_interfaces() {
    let init = compile_temp("erc165", ERC165_SRC, &crate::Options::default()).expect("compile");
    let runtime = deploy(&init).expect("deploy");
    let id = |sel: u64| Word::from_u64(sel).shl(224);
    for (sel, want) in [
        (0x01ffc9a7, 1),
        (0x36372b07, 1),
        (0xa219a025, 1),
        (0x0e89341c, 1),
        (0x80ac58cd, 0),
        (0xffffffff, 0),
    ] {
        let out = call(&runtime, "supportsInterface(bytes4)", &[id(sel)]);
        assert!(!out.reverted);
        assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(want), "{sel:#x}");
    }
    let off = crate::Options {
        erc165: false,
        ..crate::Options::default()
    };
    assert!(!abi_temp("erc165-off", ERC165_SRC, &off).contains("supportsInterface"));
    // A contract has an interface when it dispatches every method, however it gets them:
    // here `uri` comes from an inline interface, and `IERC20` from `ERC20`'s own externals.
    let inline = ERC165_SRC.replace(
        "external use Uris is IERC1155MetadataURI;",
        "external use Uris is { view function uri(id : nat) : string; }",
    );
    let inline = inline.replace(
        "external use ERC20 is IERC20, IERC20Metadata;",
        "external use ERC20 is IERC20;",
    );
    let runtime = deploy(&compile_temp("erc165-inline", &inline, &crate::Options::default()).expect("inline"))
        .expect("deploy");
    for (sel, want) in [(0x36372b07, 1), (0x0e89341c, 1), (0xa219a025, 0)] {
        let out = call(&runtime, "supportsInterface(bytes4)", &[id(sel)]);
        assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(want), "{sel:#x}");
    }
    // Every contract answers for ERC-165 itself.
    let plain = compile("storage is record { n : nat; }\nexternal function f() is { storage.n := 1n; }\n")
        .expect("plain");
    let runtime = deploy(&plain).expect("deploy");
    let out = call(&runtime, "supportsInterface(bytes4)", &[id(0x01ffc9a7)]);
    assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(1));
    // A contract that writes its own is left alone, with a warning.
    let own = ERC165_SRC.replace(
        "storage is record {}",
        "storage is record {}\n  external pure function supportsInterface(const interfaceId : bytes4) : bool is interfaceId = 0x01ffc9a7",
    );
    let dir = std::env::temp_dir().join(format!("lithe-erc165-own-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("dir");
    let path = dir.join("main.lithe");
    std::fs::write(&path, &own).expect("write");
    let warnings = crate::warnings_file(&path).expect("warnings");
    assert!(
        warnings.contains("the contract writes its own `supportsInterface`, so the compiler does not answer for `IERC20`, `IERC20Metadata`, `IERC1155MetadataURI`, which the contract has"),
        "{warnings}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// An interface is a list of function headers. The same list names what a contract calls and
/// what it exposes: overloads resolve by their arguments, only a `payable` method takes value,
/// and `external use` combines named interfaces with an inline one.
#[test]
fn interfaces_are_function_headers() {
    install_mocks();
    let src = r#"
interface Pinger is {
  function ping(a : nat);
  function ping(a : nat; b : nat);
  function put(a : address);
  function put(a : bool);
  payable function fund(a : nat);
}

storage is record { n : nat; }

external function go(const t : Pinger) is {
  defer t.ping(1n, 2n);
  defer t.put(Evm.sender());
  defer t.fund(3n) with value = 0n;
}
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let out = exec(
        &runtime,
        &word_data("go(address)", &[Word::from_u64(0xcd)]),
        HashMap::new(),
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("run");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    let calls = out.detail.join("\n");
    for sig in ["ping(uint256,uint256)", "put(address)", "fund(uint256)"] {
        assert!(calls.contains(&hex(&selector(sig))), "{sig}: {calls}");
    }
    for (body, want) in [
        (
            "defer t.ping(1n) with value = 1n;",
            "`ping` is not payable; declare it `payable function ping` in its interface",
        ),
        ("defer t.ping(1n, 2n, 3n);", "`ping` expects 1 arguments"),
        ("defer t.put(1n);", "no overload of `put` takes these arguments"),
    ] {
        let bad = src.replace("defer t.ping(1n, 2n);", body);
        let err = compile(&bad).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    for (iface, want) in [
        (
            "interface Pair is { view function both() : (nat, nat); }\nexternal view function f(const p : Pair) : nat is query p.both()",
            "a query returns a single word, a string, bytes, or a list",
        ),
        (
            "interface Bad is { function f() raises Missing; }",
            "unknown error `Missing`",
        ),
        (
            "interface Bad is { function f(const a : nat); }",
            "an interface's parameters are `name : type`, without `const`",
        ),
        (
            "interface Bad is { query f() : nat; }",
            "an interface declares functions, found `query`",
        ),
    ] {
        let bad = format!("{src}\n{iface}\n");
        let err = compile(&bad).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}

/// `external use M is I, J, { ... }` exposes every member of each: the interfaces and the
/// inline one. The module's definition keeps `nonreentrant` and how it treats its parameters.
#[test]
fn external_use_combines_interfaces() {
    let module = r#"
module Vault is {
  storage vault at "t.vault" is record { total : nat; }
  error Too_much;

  external view function total() : nat is vault.total
  external nonreentrant function add(var by : nat) raises Too_much is {
    assert(by < 1000n, Too_much);
    by := by * 2n;
    vault.total := vault.total + by;
  }
  external pure function version() : nat is 3n
}

interface ITotal is {
  view function total() : nat;
}

interface IAdd is {
  function add(by : nat) raises Too_much;
}
"#;
    let src = format!(
        "{module}\nexternal use Vault is ITotal, IAdd, {{\n  pure function version() : nat;\n}}\n"
    );
    let runtime = deploy(&compile(&src).expect("compile")).expect("deploy");
    let add = exec(
        &runtime,
        &word_data("add(uint256)", &[Word::from_u64(5)]),
        HashMap::new(),
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("add");
    assert!(!add.reverted, "{}", pretty(&add.returndata));
    let total = exec(
        &runtime,
        &word_data("total()", &[]),
        add.storage,
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("total");
    assert_eq!(load_bytes(&total.returndata, 0), Word::from_u64(10));
    let out = call(&runtime, "version()", &[]);
    assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(3));
    let footprint = crate::footprint(&src).expect("footprint");
    assert!(footprint.contains("add"), "{footprint}");
    for (bad, want) in [
        (
            src.replace("ITotal, IAdd,", "ITotal, IMissing,"),
            "unknown interface `IMissing`",
        ),
        (
            format!("{src}external use Vault is ITotal;\n"),
            "`external use Vault` appears twice; list all its interfaces in one",
        ),
        (
            src.replace("pure function version() : nat;", "view function version() : nat;"),
            "`version` is `view` in the inline interface and `pure` in `Vault`",
        ),
        (
            src.replace("  pure function version() : nat;\n}", "  pure function version() : nat;\n}, {\n  view function total() : nat;\n}"),
            "`external use` has one inline interface",
        ),
    ] {
        let err = compile(&bad).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}

/// A short `bytes` or `string` argument keeps only its own bytes from the word after its
/// length, which may be padding or the next argument.
#[test]
fn short_dynamic_arguments_ignore_what_follows() {
    let src = "\
storage is record { n : nat; }
external pure function bb(const a : bytes; const b : bytes) : (nat, nat) is (a.length, b.length)
external pure function bbs(const a : bytes; const b : bytes; const s : string) : (nat, nat, nat) is (a.length, b.length, s.length)
external pure function sb(const s : string; const b : bytes) : (nat, nat) is (s.length, b.length)
external pure function copy(const a : bytes; const s : string) : bytes is a
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let run = |data: &[u8]| {
        let out = exec(&runtime, data, HashMap::new(), w(7), w(0), w(0)).expect("run");
        assert!(!out.reverted);
        out.returndata
    };
    let words = |ns: &[u64]| ns.iter().flat_map(|&n| w(n).to_be_bytes()).collect::<Vec<u8>>();
    let hello = || Arg::B(b"hello".to_vec());
    for (sig, args, want) in [
        ("bb(bytes,bytes)", vec![Arg::B(vec![]), Arg::B(vec![1, 2])], vec![0, 2]),
        ("bbs(bytes,bytes,string)", vec![Arg::B(vec![1]), Arg::B(vec![]), hello()], vec![1, 0, 5]),
        ("sb(string,bytes)", vec![Arg::B(vec![]), Arg::B(vec![1, 2])], vec![0, 2]),
    ] {
        assert_eq!(run(&encode_args(sig, &args)), words(&want), "{sig}");
    }
    assert_eq!(
        abi_string_value(&run(&encode_args("copy(bytes,string)", &[Arg::B(vec![]), hello()]))),
        b""
    );
    let mut dirty = encode_args("copy(bytes,string)", &[Arg::B(vec![0xab]), hello()]);
    dirty[4 + 64 + 32 + 1..4 + 64 + 64].fill(0xff);
    assert_eq!(abi_string_value(&run(&dirty)), [0xab]);

    // A lone argument is decoded inline rather than by the shared helper.
    let src = "\
storage is record { n : nat; }
external pure function echo(const a : bytes; const n : nat) : bytes is a
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let mut dirty = encode_args("echo(bytes,uint256)", &[Arg::B(vec![0xab]), Arg::W(w(7))]);
    dirty[4 + 64 + 32 + 1..].fill(0xff);
    let out = exec(&runtime, &dirty, HashMap::new(), w(7), w(0), w(0)).expect("run");
    assert_eq!(abi_string_value(&out.returndata), [0xab]);
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
        let out = exec(&runtime, calldata, HashMap::new(), Word::from_u64(1), Word::from_u64(0), Word::from_u64(0))
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
        for (file_safe, no_padding) in [(false, false), (false, true), (true, false), (true, true)] {
            let want = base64_reference(&data, file_safe, no_padding);
            let out = run(&with_flags("enc(bytes,bool,bool)", &data, file_safe, no_padding));
            assert_eq!(abi_string_value(&out.returndata), want, "len {len} {file_safe} {no_padding}");
            let back = run(&abi_string("dec(string)", &want));
            assert_eq!(abi_string_value(&back.returndata), data, "decode len {len}");
        }
        let same = run(&abi_string("same(bytes)", &data));
        assert_eq!(load_bytes(&same.returndata, 0), Word::from_u64(1), "len {len}");
        let kept = run(&abi_string("keep(bytes)", &data));
        let last = exec(&runtime, &selector("last()"), kept.storage, Word::from_u64(1), Word::from_u64(0), Word::from_u64(0))
            .expect("last");
        assert_eq!(abi_string_value(&last.returndata), base64_reference(&data, false, false));
    }
    let out = run(&abi_string("text(string)", b"lithe?>"));
    assert_eq!(abi_string_value(&out.returndata), b"bGl0aGU_Pg");
}
