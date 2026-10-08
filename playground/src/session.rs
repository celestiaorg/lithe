//! A chain in memory that the page deploys compiled contracts to and calls. It starts empty
//! but for three funded callers, and keeps every account's code and storage between calls
//! until it is reset.

use std::cell::RefCell;
use std::collections::{btree_map, BTreeMap, HashMap};

use alloy_dyn_abi::{DynSolType, DynSolValue, EventExt, FunctionExt, JsonAbiExt, Specifier};
use alloy_json_abi::{JsonAbi, Param};
use revm::context::result::{ExecutionResult, Output};
use revm::context::{Context, TxEnv};
use revm::database::{CacheDB, EmptyDB};
use revm::inspector::Inspector;
use revm::interpreter::interpreter::EthInterpreter;
use revm::interpreter::interpreter_types::{Jumps, MemoryTr};
use revm::interpreter::{CreateInputs, CreateOutcome, Interpreter};
use revm::primitives::hardfork::SpecId;
use revm::primitives::{keccak256, Address, Bytes, Log, TxKind, B256, U256};
use revm::state::AccountInfo;
use revm::{InspectCommitEvm, InspectEvm, MainBuilder, MainContext};
use serde_json::{json, Value};

/// The callers, each with plenty of ether.
pub const CALLERS: [Address; 3] = [
    Address::repeat_byte(0x11),
    Address::repeat_byte(0x22),
    Address::repeat_byte(0x33),
];

/// A slot a field holds, or a part of one.
struct Field {
    name: String,
    ty: String,
    offset: usize,
    bytes: usize,
}

struct Instance {
    name: String,
    abi: JsonAbi,
    fields: HashMap<B256, Vec<Field>>,
}

struct Session {
    db: CacheDB<EmptyDB>,
    instances: BTreeMap<Address, Instance>,
    /// The contracts of the last deploy's file, by creation code: a contract one of them
    /// creates is known by the code it was created from.
    family: Vec<(Vec<u8>, Value)>,
    /// What each hash the code computed was a hash of: map slots and the data of lists
    /// and long strings are hashes of their keys and base slots.
    preimages: HashMap<U256, Vec<u8>>,
    block: u64,
    /// The last block's timestamp, in seconds.
    time: u64,
}

impl Session {
    fn new() -> Self {
        let mut db = CacheDB::<EmptyDB>::default();
        let ether = U256::from(10).pow(U256::from(18));
        for caller in CALLERS {
            db.insert_account_info(
                caller,
                AccountInfo {
                    balance: U256::from(1_000_000) * ether,
                    ..Default::default()
                },
            );
        }
        Session {
            db,
            instances: BTreeMap::new(),
            family: Vec::new(),
            preimages: HashMap::new(),
            block: 1,
            time: 0,
        }
    }
}

thread_local! {
    static SESSION: RefCell<Option<Session>> = const { RefCell::new(None) };
}

/// Answers one request from the page: `reset`, `deploy`, or `call`.
pub fn handle(request: &str) -> String {
    let result = serde_json::from_str::<Value>(request)
        .map_err(|e| e.to_string())
        .and_then(|request| {
            SESSION.with(|cell| {
                let mut cell = cell.borrow_mut();
                if request["op"] == "reset" {
                    *cell = None;
                    return Ok(json!({}));
                }
                let session = cell.get_or_insert_with(Session::new);
                match request["op"].as_str() {
                    Some("deploy") => deploy(session, &request),
                    Some("upgrade") => upgrade(session, &request),
                    Some("call") => call(session, &request),
                    _ => Err("unknown request".to_string()),
                }
            })
        });
    match result {
        Ok(value) => value.to_string(),
        Err(error) => json!({ "error": error }).to_string(),
    }
}

/// A compiled contract as the page sends it: `name`, `bytecode`, `abi`, and `storage`.
fn instance(contract: &Value) -> Result<Instance, String> {
    let abi: JsonAbi =
        serde_json::from_value(contract["abi"].clone()).map_err(|e| e.to_string())?;
    let mut fields: HashMap<B256, Vec<Field>> = HashMap::new();
    let mut seen: HashMap<&str, usize> = HashMap::new();
    for word in contract["storage"].as_array().into_iter().flatten() {
        let field = str_of(&word["field"]);
        let nth = seen.entry(field).or_default();
        let name = if *nth == 0 {
            field.to_string()
        } else {
            format!("{field} +{nth}")
        };
        *nth += 1;
        fields
            .entry(B256::from_slice(&hex(str_of(&word["slot"]))?))
            .or_default()
            .push(Field {
                name,
                ty: str_of(&word["ty"]).to_string(),
                offset: word["offset"].as_u64().unwrap_or(0) as usize,
                bytes: word["bytes"].as_u64().unwrap_or(32) as usize,
            });
    }
    let name = str_of(&contract["name"]).to_string();
    Ok(Instance { name, abi, fields })
}

/// The deterministic deployment proxy's code: calldata is a 32-byte salt, then the creation code,
/// and it `CREATE2`s that and returns the address. Contracts with delegated modules deploy their
/// facets through it.
const PROXY: &str = "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe03601600081602082378035828234f58015156039578182fd5b8082525050506014600cf3";

/// ERC-1967's implementation slot, and `Upgraded(address)`'s topic.
const IMPLEMENTATION_SLOT: &str =
    "360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc";
const UPGRADED: &str = "bc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b";

/// The creation code of a standard ERC-1967 proxy for `implementation`, as OpenZeppelin's
/// `ERC1967Proxy(implementation, data)` is: it stores the implementation, logs `Upgraded`, and
/// `delegatecall`s it with `data`, if any, while the proxy has no code yet, reverting with what
/// that reverts with, then leaves code that `delegatecall`s the implementation with every call.
fn proxy_creation(implementation: Address, data: &[u8]) -> Result<Vec<u8>, String> {
    let slot = hex(IMPLEMENTATION_SLOT)?;
    let mut runtime = vec![0x36, 0x5f, 0x5f, 0x37, 0x5f, 0x5f, 0x36, 0x5f, 0x7f];
    runtime.extend(&slot);
    runtime.extend([
        0x54, 0x5a, 0xf4, 0x3d, 0x5f, 0x5f, 0x3e, 0x60, 0x36, 0x57, 0x3d, 0x5f, 0xfd, 0x5b, 0x3d,
        0x5f, 0xf3,
    ]);
    debug_assert_eq!(runtime[0x36], 0x5b);
    // Offsets are patched once the init code's length is known.
    let mut init = vec![0x61, 0, 0, 0x38, 0x03, 0x80, 0x61, 0, 0, 0x5f, 0x39]; // len := codesize - tail; mem[0..len] = tail
    init.extend([0x5f, 0x51, 0x80, 0x7f]); // impl := mload(0)
    init.extend(&slot);
    init.push(0x55); // sstore(slot, impl)
    init.extend([0x80, 0x7f]);
    init.extend(hex(UPGRADED)?);
    init.extend([0x5f, 0x5f, 0xa2]); // log2(0, 0, Upgraded, impl)
    let mut fail_jump = None;
    if !data.is_empty() {
        // delegatecall(gas, impl, 32, len - 32, 0, 0)
        init.extend([
            0x5f, 0x5f, 0x60, 0x20, 0x84, 0x03, 0x60, 0x20, 0x84, 0x5a, 0xf4,
        ]);
        init.extend([0x15, 0x61, 0, 0, 0x57]); // if it failed, jump to fail
        fail_jump = Some(init.len() - 3);
    }
    init.extend([0x61, 0, 0, 0x61, 0, 0, 0x5f, 0x39, 0x61, 0, 0, 0x5f, 0xf3]); // return the runtime
    let ret = init.len() - 13;
    let fail = init.len();
    init.extend([0x5b, 0x3d, 0x5f, 0x5f, 0x3e, 0x3d, 0x5f, 0xfd]); // revert with its revert data
    let at = |code: &mut Vec<u8>, i: usize, v: usize| {
        code[i..i + 2].copy_from_slice(&(v as u16).to_be_bytes())
    };
    let start = init.len();
    let tail = start + runtime.len();
    at(&mut init, 1, tail);
    at(&mut init, 7, tail);
    if let Some(i) = fail_jump {
        at(&mut init, i, fail);
    }
    at(&mut init, ret + 1, runtime.len());
    at(&mut init, ret + 4, start);
    at(&mut init, ret + 9, runtime.len());
    let mut code = init;
    code.extend(runtime);
    code.extend([0u8; 12]);
    code.extend(implementation.as_slice());
    code.extend(data);
    Ok(code)
}

fn has_code(session: &Session, address: Address) -> bool {
    session
        .db
        .cache
        .accounts
        .get(&address)
        .is_some_and(|a| a.info.code_hash != revm::primitives::KECCAK_EMPTY)
}

/// Code put on the chain: the transaction that created it, its logs, where it is, and the facets
/// that went first.
struct Placed {
    result: ExecutionResult,
    logs: Vec<Log>,
    at: Option<Address>,
    facets: Vec<Value>,
}

/// Puts a compiled contract's code on the chain, with `args` after its creation code: first the
/// facets its plan lists that are not on the chain, each through the proxy, then the code, through
/// the proxy too when the plan says so. An answer for the page instead when it can't.
fn place(
    session: &mut Session,
    request: &Value,
    contract: &Value,
    name: &str,
    args: Vec<u8>,
    value: U256,
) -> Result<Result<Placed, Value>, String> {
    let plan = &contract["plan"];
    let mut facets = Vec::new();
    for facet in plan["facets"].as_array().into_iter().flatten() {
        let facet_name = str_of(&facet["name"]);
        let at: Address = str_of(&facet["address"])
            .parse()
            .map_err(|_| "bad facet address")?;
        if has_code(session, at) {
            facets.push(
                json!({ "name": facet_name, "address": at.to_checksum(None), "there": true }),
            );
            continue;
        }
        let to = proxy(session, &facet["to"])?;
        let tx = Tx {
            to: Some(to),
            data: hex(str_of(&facet["data"]))?,
            caller: caller(request)?,
            value: U256::ZERO,
            commit: true,
        };
        let (result, _) = execute(session, tx, request)?;
        let ok = result.is_success() && has_code(session, at);
        facets.push(json!({ "name": facet_name, "address": at.to_checksum(None), "gas": result.tx_gas_used(), "ok": ok }));
        if !ok {
            let mut out = outcome(session, &result, &[], None);
            out["ok"] = json!(false);
            out["error"] = json!(format!(
                "facet {facet_name} did not deploy: {}",
                out["error"]
                    .as_str()
                    .unwrap_or("its code ran but left none")
            ));
            out["facets"] = json!(facets);
            out["storage"] = storage(session);
            return Ok(Err(out));
        }
    }
    let router = &plan["router"];
    let through = router["to"].as_str().is_some();
    if through
        && router["address"]
            .as_str()
            .and_then(|a| a.parse().ok())
            .is_some_and(|a| has_code(session, a))
    {
        let at = str_of(&router["address"]);
        return Ok(Err(json!({
            "ok": false,
            "error": format!("{name} is already at {at}: CREATE2 puts the same code at the same address. Reset the chain to deploy it again."),
            "storage": storage(session),
        })));
    }
    let mut data = if through {
        hex(str_of(&router["data"]))?
    } else {
        hex(str_of(&contract["bytecode"]))?
    };
    data.extend(args);
    let tx = Tx {
        to: if through {
            Some(proxy(session, &router["to"])?)
        } else {
            None
        },
        data,
        caller: caller(request)?,
        value,
        commit: true,
    };
    let (result, logs) = execute(session, tx, request)?;
    let at = match &result {
        ExecutionResult::Success {
            output: Output::Create(_, Some(address)),
            ..
        } => Some(*address),
        ExecutionResult::Success { .. } if through => router["address"]
            .as_str()
            .and_then(|a| a.parse().ok())
            .filter(|a| has_code(session, *a)),
        _ => None,
    };
    Ok(Ok(Placed {
        result,
        logs,
        at,
        facets,
    }))
}

/// An upgradeable contract's code is the implementation behind an ERC-1967 proxy, and its
/// `deploy` the proxy's initializer.
fn upgradeable(abi: &JsonAbi) -> bool {
    ["proxiableUUID", "upgradeToAndCall"]
        .iter()
        .all(|n| abi.functions().any(|f| f.name == *n))
}

/// The answer for a placement and what came of it: its outcome, where the contract is, and the
/// facets and implementation that went first.
fn placed(
    session: &Session,
    placed: &Placed,
    at: Option<Address>,
    implementation: Option<Value>,
) -> Value {
    let mut out = outcome(session, &placed.result, &placed.logs, at);
    if let Some(address) = at {
        out["address"] = json!(address.to_checksum(None));
    }
    if !placed.facets.is_empty() {
        out["facets"] = json!(placed.facets);
    }
    if let Some(implementation) = implementation {
        out["implementation"] = implementation;
    }
    out["storage"] = storage(session);
    out
}

fn family(session: &mut Session, request: &Value) -> Result<(), String> {
    session.family = request["family"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|c| Ok((hex(str_of(&c["bytecode"]))?, c.clone())))
        .collect::<Result<_, String>>()?;
    Ok(())
}

/// Deploys a contract. An upgradeable one is its implementation, then a proxy for it whose
/// creation calls `deploy` with the arguments.
fn deploy(session: &mut Session, request: &Value) -> Result<Value, String> {
    let contract = &request["contract"];
    let made = instance(contract)?;
    family(session, request)?;
    if !upgradeable(&made.abi) {
        let mut args = Vec::new();
        if let Some(constructor) = &made.abi.constructor {
            let values = arguments(&constructor.inputs, &request["args"])?;
            args = constructor
                .abi_encode_input(&values)
                .map_err(|e| e.to_string())?;
        }
        let name = made.name.clone();
        let mut code = match place(
            session,
            request,
            contract,
            &name,
            args,
            value(&request["value"])?,
        )? {
            Ok(code) => code,
            Err(out) => return Ok(out),
        };
        if let Some(at) = code.at {
            session.instances.insert(at, made);
        }
        let at = code.at.take();
        return Ok(placed(session, &code, at, None));
    }
    let mut initializer = Vec::new();
    if let Some(f) = made.abi.functions().find(|f| f.name == "deploy") {
        let values = arguments(&f.inputs, &request["args"])?;
        initializer = f.abi_encode_input(&values).map_err(|e| e.to_string())?;
    }
    let name = format!("{}'s implementation", made.name);
    let mut code = match place(session, request, contract, &name, Vec::new(), U256::ZERO)? {
        Ok(code) => code,
        Err(out) => return Ok(out),
    };
    let Some(implementation) = code.at else {
        return Ok(placed(session, &code, None, None));
    };
    // The implementation is the code behind the proxy, not a contract of its own to call.
    session.instances.remove(&implementation);
    let gas = code.result.tx_gas_used();
    let tx = Tx {
        to: None,
        data: proxy_creation(implementation, &initializer)?,
        caller: caller(request)?,
        value: value(&request["value"])?,
        commit: true,
    };
    (code.result, code.logs) = execute(session, tx, request)?;
    let at = match &code.result {
        ExecutionResult::Success {
            output: Output::Create(_, Some(address)),
            ..
        } => Some(*address),
        _ => None,
    };
    if let Some(address) = at {
        session.instances.insert(address, made);
    }
    let implementation = json!({ "address": implementation.to_checksum(None), "gas": gas });
    Ok(placed(session, &code, at, Some(implementation)))
}

/// Upgrades the proxy at `to` to a new version: puts the version's implementation on the chain,
/// then calls the proxy's `upgradeToAndCall` with it and, when one is named, a call to the
/// version's migration. The proxy keeps its address and its storage.
fn upgrade(session: &mut Session, request: &Value) -> Result<Value, String> {
    let to: Address = str_of(&request["to"])
        .parse()
        .map_err(|_| "no such contract")?;
    if !session.instances.contains_key(&to) {
        return Err("no such contract".to_string());
    }
    let contract = &request["contract"];
    let made = instance(contract)?;
    if !upgradeable(&made.abi) {
        return Err(format!("the new {} is not upgradeable", made.name));
    }
    let mut migration = Vec::new();
    if let Some(name) = request["migration"].as_str().filter(|n| !n.is_empty()) {
        let item = contract["migrations"]
            .as_array()
            .into_iter()
            .flatten()
            .find(|m| m["name"] == name)
            .ok_or_else(|| format!("no migration `{name}`"))?;
        let f: alloy_json_abi::Function =
            serde_json::from_value(item.clone()).map_err(|e| e.to_string())?;
        let values = arguments(&f.inputs, &request["args"])?;
        migration = f.abi_encode_input(&values).map_err(|e| e.to_string())?;
    }
    family(session, request)?;
    let name = format!("{}'s new implementation", made.name);
    let mut code = match place(session, request, contract, &name, Vec::new(), U256::ZERO)? {
        Ok(code) => code,
        Err(out) => return Ok(out),
    };
    let Some(implementation) = code.at else {
        return Ok(placed(session, &code, None, None));
    };
    session.instances.remove(&implementation);
    let gas = code.result.tx_gas_used();
    let call = alloy_json_abi::Function::parse("upgradeToAndCall(address,bytes)")
        .map_err(|e| e.to_string())?;
    let data = call
        .abi_encode_input(&[
            DynSolValue::Address(implementation),
            DynSolValue::Bytes(migration),
        ])
        .map_err(|e| e.to_string())?;
    let tx = Tx {
        to: Some(to),
        data,
        caller: caller(request)?,
        value: value(&request["value"])?,
        commit: true,
    };
    (code.result, code.logs) = execute(session, tx, request)?;
    // The proxy runs the new version now: its ABI and storage layout are the new ones.
    if code.result.is_success() {
        session.instances.insert(to, made);
    }
    let implementation = json!({ "address": implementation.to_checksum(None), "gas": gas });
    Ok(placed(session, &code, Some(to), Some(implementation)))
}

/// The proxy at the address a plan sends a deployment to, put there first if the chain has none.
fn proxy(session: &mut Session, to: &Value) -> Result<Address, String> {
    let at: Address = str_of(to).parse().map_err(|_| "bad deployer address")?;
    if !has_code(session, at) {
        let code = revm::bytecode::Bytecode::new_raw(Bytes::from(hex(PROXY)?));
        session
            .db
            .insert_account_info(at, AccountInfo::default().with_code(code));
    }
    Ok(at)
}

fn call(session: &mut Session, request: &Value) -> Result<Value, String> {
    let to: Address = str_of(&request["to"])
        .parse()
        .map_err(|_| "no such contract")?;
    let instance = session.instances.get(&to).ok_or("no such contract")?;
    let signature = str_of(&request["function"]);
    let function = instance
        .abi
        .functions()
        .find(|f| f.signature() == signature)
        .ok_or_else(|| format!("`{signature}` is not a function of {}", instance.name))?
        .clone();
    let args = arguments(&function.inputs, &request["args"])?;
    let data = function
        .abi_encode_input(&args)
        .map_err(|e| e.to_string())?;
    let readonly = matches!(
        function.state_mutability,
        alloy_json_abi::StateMutability::View | alloy_json_abi::StateMutability::Pure
    );
    let tx = Tx {
        to: Some(to),
        data,
        caller: caller(request)?,
        value: value(&request["value"])?,
        commit: !readonly,
    };
    let (result, logs) = execute(session, tx, request)?;
    let mut out = outcome(session, &result, &logs, Some(to));
    if let ExecutionResult::Success {
        output: Output::Call(bytes),
        ..
    } = &result
    {
        let values = function
            .abi_decode_output(bytes)
            .map_err(|e| e.to_string())?;
        out["returns"] = json!(function
            .outputs
            .iter()
            .zip(&values)
            .map(|(param, v)| json!({ "name": param.name, "type": param.ty, "value": show(v) }))
            .collect::<Vec<_>>());
    }
    out["storage"] = storage(session);
    Ok(out)
}

struct Tx {
    to: Option<Address>,
    data: Vec<u8>,
    caller: Address,
    value: U256,
    commit: bool,
}

/// The largest gas a transaction may have since Osaka.
const TX_GAS: u64 = 1 << 24;

fn execute(
    session: &mut Session,
    tx: Tx,
    request: &Value,
) -> Result<(ExecutionResult, Vec<Log>), String> {
    let spec = match request["evm"].as_str() {
        Some("prague") => SpecId::PRAGUE,
        _ => SpecId::OSAKA,
    };
    let block = session.block;
    // The page's clock, kept moving forward: each block is later than the one before.
    let now = request["now"].as_u64().unwrap_or(session.time + 12);
    let time = if tx.commit {
        now.max(session.time + 1)
    } else {
        now.max(session.time)
    };
    let env = TxEnv::builder()
        .caller(tx.caller)
        .kind(tx.to.map_or(TxKind::Create, TxKind::Call))
        .data(Bytes::from(tx.data))
        .value(tx.value)
        .gas_limit(TX_GAS)
        .gas_price(0)
        .build()
        .map_err(|e| format!("{e:?}"))?;
    let mut evm = Context::mainnet()
        .with_db(&mut session.db)
        .modify_cfg_chained(|cfg| {
            cfg.spec = spec;
            cfg.disable_nonce_check = true;
            // A contract over the limit still builds, with a warning; here it runs too.
            cfg.limit_contract_code_size = Some(usize::MAX);
        })
        .modify_block_chained(|b| {
            b.number = U256::from(block);
            b.timestamp = U256::from(time);
            b.basefee = 0;
            b.gas_limit = TX_GAS;
        })
        .build_mainnet_with_inspector(Recorder::default());
    let result = if tx.commit {
        evm.inspect_tx_commit(env).map_err(|e| format!("{e:?}"))?
    } else {
        evm.inspect_tx(env).map_err(|e| format!("{e:?}"))?.result
    };
    let Recorder { found, created, .. } = std::mem::take(&mut evm.inspector);
    drop(evm);
    session.preimages.extend(found);
    if tx.commit {
        session.block += 1;
        session.time = time;
        for (address, init) in created {
            let known = session
                .family
                .iter()
                .filter(|(code, _)| init.starts_with(code))
                .max_by_key(|(code, _)| code.len());
            let exists = session.db.cache.accounts.contains_key(&address);
            if let (Some((_, contract)), true) = (known, exists) {
                if let btree_map::Entry::Vacant(slot) = session.instances.entry(address) {
                    slot.insert(instance(contract)?);
                }
            }
        }
    }
    let logs = result.logs().to_vec();
    Ok((result, logs))
}

fn outcome(
    session: &Session,
    result: &ExecutionResult,
    logs: &[Log],
    to: Option<Address>,
) -> Value {
    let mut out =
        json!({ "gas": result.tx_gas_used(), "block": session.block - 1, "time": session.time });
    match result {
        ExecutionResult::Success { .. } => out["ok"] = json!(true),
        ExecutionResult::Revert { output, .. } => {
            out["ok"] = json!(false);
            out["error"] = json!(revert_reason(session, to, output));
        }
        ExecutionResult::Halt { reason, .. } => {
            out["ok"] = json!(false);
            out["error"] = json!(format!("halted: {reason:?}"));
        }
    }
    out["events"] = json!(logs
        .iter()
        .map(|log| event(session, log))
        .collect::<Vec<_>>());
    out
}

fn revert_reason(session: &Session, to: Option<Address>, data: &[u8]) -> String {
    if data.is_empty() {
        return "reverted with no data".to_string();
    }
    if let (Some(instance), Some(selector)) =
        (to.and_then(|a| session.instances.get(&a)), data.get(..4))
    {
        for error in instance.abi.errors() {
            if error.selector().as_slice() == selector {
                if let Ok(values) = error.abi_decode_input(&data[4..]) {
                    return format!("{}{}", error.name, named(&error.inputs, &values));
                }
            }
        }
    }
    alloy_sol_types::decode_revert_reason(data)
        .unwrap_or_else(|| format!("reverted with 0x{}", hex_str(data)))
}

fn event(session: &Session, log: &Log) -> Value {
    let emitter = log.address.to_checksum(None);
    if let (Some(instance), Some(topic)) =
        (session.instances.get(&log.address), log.topics().first())
    {
        for event in instance.abi.events() {
            if event.anonymous || event.selector() != *topic {
                continue;
            }
            if let Ok(decoded) =
                event.decode_log_parts(log.topics().iter().copied(), &log.data.data)
            {
                let (mut indexed, mut body) = (decoded.indexed.iter(), decoded.body.iter());
                let args: Vec<String> = event
                    .inputs
                    .iter()
                    .filter_map(|input| {
                        let v = if input.indexed {
                            indexed.next()
                        } else {
                            body.next()
                        }?;
                        Some(format!("{} = {}", input.name, show(v)))
                    })
                    .collect();
                return json!({ "from": emitter, "text": format!("{}({})", event.name, args.join(", ")) });
            }
        }
    }
    // The proxy's own event, which the contract's ABI may not list.
    if let [topic, implementation] = log.topics() {
        if topic.to_string() == format!("0x{UPGRADED}") {
            let at = Address::from_word(*implementation).to_checksum(None);
            return json!({ "from": emitter, "text": format!("Upgraded(implementation = {at})") });
        }
    }
    let topics: Vec<String> = log.topics().iter().map(|t| t.to_string()).collect();
    json!({ "from": emitter, "text": format!("log [{}] 0x{}", topics.join(", "), hex_str(&log.data.data)) })
}

/// Every account's storage but the callers', an entry a field a nonzero slot holds, each
/// named for what holds it when that is known: `domain` is the storage the field is in, and
/// `name` the field, with the keys of a map entry.
fn storage(session: &Session) -> Value {
    let mut accounts = Vec::new();
    for (address, account) in &session.db.cache.accounts {
        let instance = session.instances.get(address);
        let mut entries: Vec<(Option<String>, String, U256, Value)> = Vec::new();
        for (slot, value) in account.storage.iter().filter(|(_, v)| !v.is_zero()) {
            let (slot, value) = (*slot, *value);
            let raw = format!("0x{}", hex_str(&value.to_be_bytes::<32>()));
            let mut push = |root: Option<&str>, suffix: &str, shown: String| {
                let (domain, field) = match root.and_then(|r| r.rsplit_once('.')) {
                    Some((domain, field)) => (Some(domain.to_string()), format!("{field}{suffix}")),
                    None => (None, String::new()),
                };
                let entry = json!({
                    "slot": format!("0x{}", hex_str(&slot.to_be_bytes::<32>())),
                    "domain": domain,
                    "name": field,
                    "value": raw,
                    "shown": shown,
                });
                entries.push((domain, field, slot, entry));
            };
            match instance.and_then(|i| i.fields.get(&B256::from(slot))) {
                Some(fields) => {
                    for f in fields {
                        push(Some(&f.name), "", show_word(part(value, f), &f.ty));
                    }
                }
                None if B256::from(slot).to_string() == format!("0x{IMPLEMENTATION_SLOT}") => push(
                    Some("ERC-1967.implementation"),
                    "",
                    show_word(value, "address"),
                ),
                None => match label(session, instance, slot, 0) {
                    Some((root, suffix, ty)) => push(Some(&root), &suffix, show_word(value, &ty)),
                    None => push(None, "", show_word(value, "")),
                },
            }
        }
        if entries.is_empty() && instance.is_none() {
            continue;
        }
        // Named entries first, by storage and name, so a map's entries sit together.
        entries.sort_by(|a, b| {
            (a.0.is_none(), &a.0, &a.1, a.2).cmp(&(b.0.is_none(), &b.0, &b.1, b.2))
        });
        accounts.push(json!({
            "address": address.to_checksum(None),
            "name": instance.map(|i| i.name.clone()),
            "balance": account.info.balance.to_string(),
            "entries": entries.into_iter().map(|e| e.3).collect::<Vec<_>>(),
        }));
    }
    json!(accounts)
}

/// What holds `slot`: the field it is, or holds an entry of, with the keys of the entry, and
/// the type of the value there.
fn label(
    session: &Session,
    instance: Option<&Instance>,
    slot: U256,
    depth: u32,
) -> Option<(String, String, String)> {
    if depth > 8 {
        return None;
    }
    if let Some(field) = instance
        .and_then(|i| i.fields.get(&B256::from(slot)))
        .and_then(|f| f.first())
    {
        return Some((field.name.clone(), String::new(), field.ty.clone()));
    }
    // The nearest hash below the slot, within a record's or list's reach of it.
    let (base, data) = session
        .preimages
        .iter()
        .filter(|(hash, _)| **hash <= slot && slot - **hash < U256::from(1u64 << 32))
        .max_by_key(|(hash, _)| **hash)?;
    let offset = slot - *base;
    let plus = if offset.is_zero() {
        String::new()
    } else {
        format!(" +{offset}")
    };
    match data.len() {
        64 => {
            let (key, parent) = (
                U256::from_be_slice(&data[..32]),
                U256::from_be_slice(&data[32..]),
            );
            let (root, suffix, ty) = label(session, instance, parent, depth + 1)?;
            Some((
                root,
                format!("{suffix}[{}]{plus}", show_key(key)),
                map_value(&ty),
            ))
        }
        32 => {
            let (root, suffix, ty) =
                label(session, instance, U256::from_be_slice(data), depth + 1)?;
            Some((root, format!("{suffix} data{plus}"), list_item(&ty)))
        }
        _ => None,
    }
}

/// A map type's value type: `uint256` of `map(address, uint256)`.
fn map_value(ty: &str) -> String {
    let Some(inner) = ty.strip_prefix("map(").and_then(|t| t.strip_suffix(')')) else {
        return String::new();
    };
    let mut depth = 0;
    for (i, c) in inner.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => return inner[i + 1..].trim().to_string(),
            _ => {}
        }
    }
    String::new()
}

fn list_item(ty: &str) -> String {
    ty.strip_prefix("list(")
        .and_then(|t| t.strip_suffix(')'))
        .unwrap_or_default()
        .to_string()
}

fn part(value: U256, field: &Field) -> U256 {
    if field.bytes >= 32 {
        return value;
    }
    (value >> (8 * field.offset)) & ((U256::from(1) << (8 * field.bytes)) - U256::from(1))
}

fn show_word(value: U256, ty: &str) -> String {
    match ty {
        // A string or bytes slot holds up to 31 bytes left-aligned, their length twice
        // over in the low byte; a longer one holds twice its length plus one, its data
        // elsewhere.
        "string" | "bytes" => {
            let word = value.to_be_bytes::<32>();
            let len = word[31] as usize / 2;
            if value.bit(0) {
                format!("{} bytes, stored apart", (value >> 1usize).to::<u64>())
            } else if ty == "string" {
                format!("{:?}", String::from_utf8_lossy(&word[..len.min(31)]))
            } else {
                format!("0x{}", hex_str(&word[..len.min(31)]))
            }
        }
        "address" => Address::from_word(B256::from(value)).to_checksum(None),
        "bool" => (!value.is_zero()).to_string(),
        t if t.starts_with("uint") || t.starts_with("int") && !t.starts_with("interface") => {
            if t.starts_with("int") && value.bit(255) {
                format!("-{}", (!value).wrapping_add(U256::from(1)))
            } else {
                value.to_string()
            }
        }
        _ if value < U256::from(1u64 << 48) => value.to_string(),
        _ => format!("0x{}", hex_str(&value.to_be_bytes::<32>())),
    }
}

/// A map key as it most likely reads: an address, a small number, or a word.
fn show_key(key: U256) -> String {
    if key < U256::from(1u64 << 48) {
        key.to_string()
    } else if key >> 160 == U256::ZERO {
        Address::from_word(B256::from(key)).to_checksum(None)
    } else {
        format!("0x{}", hex_str(&key.to_be_bytes::<32>()))
    }
}

fn named(params: &[Param], values: &[DynSolValue]) -> String {
    let parts: Vec<String> = params
        .iter()
        .zip(values)
        .map(|(p, v)| {
            if p.name.is_empty() {
                show(v)
            } else {
                format!("{} = {}", p.name, show(v))
            }
        })
        .collect();
    format!("({})", parts.join(", "))
}

fn show(value: &DynSolValue) -> String {
    match value {
        DynSolValue::Bool(b) => b.to_string(),
        DynSolValue::Int(i, _) => i.to_string(),
        DynSolValue::Uint(u, _) => u.to_string(),
        DynSolValue::Address(a) => a.to_checksum(None),
        DynSolValue::Function(f) => f.to_string(),
        DynSolValue::FixedBytes(w, n) => format!("0x{}", hex_str(&w[..*n])),
        DynSolValue::Bytes(b) => format!("0x{}", hex_str(b)),
        DynSolValue::String(s) => format!("{s:?}"),
        DynSolValue::Array(items) | DynSolValue::FixedArray(items) => {
            format!(
                "[{}]",
                items.iter().map(show).collect::<Vec<_>>().join(", ")
            )
        }
        DynSolValue::Tuple(items) => format!(
            "({})",
            items.iter().map(show).collect::<Vec<_>>().join(", ")
        ),
    }
}

/// The page's text arguments as the parameters' types read them.
fn arguments(params: &[Param], args: &Value) -> Result<Vec<DynSolValue>, String> {
    let args = args.as_array().cloned().unwrap_or_default();
    params
        .iter()
        .enumerate()
        .map(|(i, param)| {
            let ty: DynSolType = param.resolve().map_err(|e| e.to_string())?;
            let text = args.get(i).and_then(Value::as_str).unwrap_or("").trim();
            let name = if param.name.is_empty() {
                format!("argument {}", i + 1)
            } else {
                format!("`{}`", param.name)
            };
            ty.coerce_str(text)
                .map_err(|_| format!("{name} takes a `{}`, not `{text}`", param.ty))
        })
        .collect()
}

fn caller(request: &Value) -> Result<Address, String> {
    str_of(&request["caller"])
        .parse()
        .map_err(|_| "no such caller".to_string())
}

/// Wei, or an amount in `ether` or `gwei`: `1.5 ether`.
fn value(v: &Value) -> Result<U256, String> {
    let text = v.as_str().unwrap_or("").trim();
    if text.is_empty() {
        return Ok(U256::ZERO);
    }
    let (amount, unit) = text
        .split_once(' ')
        .map_or((text, "wei"), |(a, u)| (a, u.trim()));
    alloy_primitives::utils::parse_units(amount, unit)
        .map(Into::into)
        .map_err(|_| format!("`{text}` is not an amount of wei, gwei, or ether"))
}

fn str_of(v: &Value) -> &str {
    v.as_str().unwrap_or("")
}

fn hex(text: &str) -> Result<Vec<u8>, String> {
    let digits = text.strip_prefix("0x").unwrap_or(text);
    (0..digits.len())
        .step_by(2)
        .map(|i| {
            u8::from_str_radix(digits.get(i..i + 2).unwrap_or("x"), 16)
                .map_err(|_| "bad hex".to_string())
        })
        .collect()
}

fn hex_str(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Records the data each `KECCAK256` hashes, and each contract created with its init code.
#[derive(Default)]
struct Recorder {
    pending: Option<Vec<u8>>,
    found: HashMap<U256, Vec<u8>>,
    created: Vec<(Address, Bytes)>,
}

impl<CTX> Inspector<CTX, EthInterpreter> for Recorder {
    fn create_end(&mut self, _: &mut CTX, inputs: &CreateInputs, outcome: &mut CreateOutcome) {
        if let (true, Some(address)) = (outcome.result.result.is_ok(), outcome.address) {
            self.created.push((address, inputs.init_code().clone()));
        }
    }

    fn step(&mut self, interp: &mut Interpreter<EthInterpreter>, _: &mut CTX) {
        if interp.bytecode.opcode() != 0x20 {
            return;
        }
        let stack = interp.stack.data();
        let (Some(at), Some(len)) = (stack.last(), stack.len().checked_sub(2).map(|i| stack[i]))
        else {
            return;
        };
        let (Ok(at), Ok(len)) = (usize::try_from(*at), usize::try_from(len)) else {
            return;
        };
        // Only the preimages that can name a slot: a key and a slot, or a slot.
        if len == 32 || len == 64 {
            let size = interp.memory.size();
            let mut data = vec![0u8; len];
            if at < size {
                let end = (at + len).min(size);
                data[..end - at].copy_from_slice(&interp.memory.slice(at..end));
            }
            self.pending = Some(data);
        }
    }

    fn step_end(&mut self, interp: &mut Interpreter<EthInterpreter>, _: &mut CTX) {
        if let (Some(data), Some(hash)) = (self.pending.take(), interp.stack.data().last()) {
            debug_assert_eq!(keccak256(&data), B256::from(*hash));
            self.found.insert(*hash, data);
        }
    }
}
