//! Symbolic execution: a transition phase, run on unknown storage, as SMT terms.
//!
//! Storage words are integers and booleans, and maps are arrays, one for each word a map's
//! values hold. Each value the phase computes is a term over what it started from: its
//! inputs and the storage it read. `ok` says the phase has not reverted: a check that fails
//! is a revert, so the obligations only concern the states where `ok` holds.
//!
//! Some values are not modeled, such as strings, lists, bit operations, and what another
//! contract answers. Each becomes a new value, of which the prover knows only its type. That
//! lets the phase do more than it can, never less, so a proof about it holds for the real
//! one. For the same reason, a check the prover cannot state never counts as a revert.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use super::smt::Script;
use crate::ast::*;
use crate::check::{is_enum, is_sum, Checked, TyKind};
use crate::word::Word;

/// A value, as terms.
#[derive(Clone, Debug)]
pub(crate) enum Val {
    Int(String),
    Bool(String),
    /// A record's or tuple's fields, in order.
    Tuple(Vec<Val>),
    /// A value the prover does not model.
    Opaque,
    Unit,
}

/// Why a phase cannot be checked.
#[derive(Debug)]
pub(crate) struct Stop {
    pub reason: String,
    pub line: u32,
    pub col: u32,
}

type Res<T> = Result<T, Stop>;

fn stop<T>(line: u32, col: u32, reason: impl Into<String>) -> Res<T> {
    Err(Stop {
        reason: reason.into(),
        line,
        col,
    })
}

/// One map's words: its leaf, and the path from its keys to one word of its values, such as
/// `[]` or `[].status` or `[][]`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Cell {
    pub leaf: u32,
    pub shape: String,
    pub arity: usize,
}

/// What a phase changes, for knowing which invariants it can break.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Key {
    Word(u32),
    Cell(Cell),
    Balance,
}

/// The state of a phase in progress.
#[derive(Clone)]
pub(crate) struct St {
    words: BTreeMap<u32, Val>,
    arrays: BTreeMap<Cell, String>,
    /// The running `sum` (false) or `count` (true) of each map an invariant adds up.
    totals: BTreeMap<(Cell, bool), String>,
    locals: HashMap<usize, Val>,
    /// The phase has not reverted.
    pub ok: String,
    /// When it has, why: the first check that failed, as a revert code.
    pub why: String,
    /// Wei the phase's deferred calls send, which leave once it commits.
    pub out: String,
    pub written: BTreeSet<Key>,
}

/// How arithmetic is read: as the code runs it, where overflow reverts, or as a spec
/// states it, over the integers.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Mode {
    Code,
    Spec,
}

/// A loop invariant's claim, as a goal in the phase's script.
pub(crate) struct LoopClaim {
    pub label: String,
    pub goal: String,
    /// What a counterexample shows: the counter, and what the invariants read.
    pub watch: Vec<(String, String)>,
}

/// A continuation the phase's deferred calls start, to check as a phase of its own.
pub(crate) struct Continuation<'a> {
    pub then: &'a Then,
    /// What the phase that deferred it said about it: `after x.f`.
    pub after: String,
}

pub(crate) struct Exec<'a> {
    pub checked: &'a Checked,
    pub smt: Script,
    /// The phase starts from the empty storage a new contract has.
    zero: bool,
    init_words: HashMap<u32, Val>,
    init_arrays: HashMap<Cell, String>,
    init_totals: HashMap<(Cell, bool), String>,
    /// The keys each map was read or written at, for what its total says about them.
    keys: HashMap<Cell, Vec<String>>,
    /// The maps an invariant adds up, whose totals each write keeps.
    pub tracked: BTreeSet<(Cell, bool)>,
    /// While set, each total a spec reads joins `tracked`.
    pub collect: bool,
    /// While set, what a spec reads, for knowing which phases can change it.
    pub touched: Option<BTreeSet<Key>>,
    env: HashMap<String, Val>,
    pub self_addr: String,
    /// The contract's ether before the call, and as the call runs, with its value in it.
    pub balance_before: String,
    pub balance: String,
    pub value: String,
    pub continuations: Vec<Continuation<'a>>,
    /// What loop invariants claim: that they hold as their loop starts, and that each
    /// iteration keeps them.
    pub loop_claims: Vec<LoopClaim>,
    /// Where each loop whose invariants the run relied on is: `12:3`.
    pub loop_places: Vec<String>,
    /// While set, what a spec reads: for each storage word or total, its label and term.
    pub reads: Option<Vec<(String, String)>>,
    /// The type of each storage word read or written, and the sort of each map's array.
    word_tys: HashMap<u32, usize>,
    /// The maps whose values are never negative.
    unsigned: std::collections::HashSet<Cell>,
    /// A `forall` was read: a counterexample may rest on keys no one can see.
    pub quantified: bool,
    array_sorts: HashMap<Cell, String>,
    /// Calls in progress, which no function makes of itself.
    depth: usize,
    /// Each map parameter of a call in progress, and the leaf of the map it was given.
    maps: HashMap<usize, u32>,
    /// `old.` or `new.`, for the labels of what a function spec reads.
    prefix: String,
    /// How the expression being read counts: as code or as a spec.
    pub mode: Mode,
    /// Where the prover is: the expression or statement it reads.
    at: (u32, u32),
    /// A function spec's two states, which `old.` and `new.` read.
    pub states: Option<States>,
    /// What the phase's code does that the prover only approximates, with where.
    pub approximations: Vec<String>,
}

/// The ether a phase starts with.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Arrival {
    /// A call that takes no ether: `Evm.value()` is zero.
    None,
    /// A payable call: its value joins the contract's ether as it starts.
    Value,
    /// A continuation: the value of the call it continues, which arrived before.
    Carried,
}

const UNROLL: u64 = 16;

impl<'a> Exec<'a> {
    pub(crate) fn new(checked: &'a Checked, zero: bool, arrival: Arrival) -> Exec<'a> {
        let mut smt = Script::default();
        let self_addr = smt.fresh("self", "Int");
        smt.assume(&in_range(&self_addr, "0", &max_bits(160)));
        let balance_before = smt.fresh("balance", "Int");
        smt.assume(&format!("(<= 0 {balance_before})"));
        let value = if arrival == Arrival::None {
            "0".to_string()
        } else {
            let value = smt.fresh("value", "Int");
            smt.assume(&in_range(&value, "0", &max_bits(256)));
            value
        };
        let balance = if arrival == Arrival::Value {
            smt.define("balance", "Int", &format!("(+ {balance_before} {value})"))
        } else {
            balance_before.clone()
        };
        let mut env = HashMap::new();
        env.insert("value".to_string(), Val::Int(value.clone()));
        Exec {
            checked,
            smt,
            zero,
            init_words: HashMap::new(),
            init_arrays: HashMap::new(),
            init_totals: HashMap::new(),
            keys: HashMap::new(),
            tracked: BTreeSet::new(),
            collect: false,
            touched: None,
            env,
            self_addr,
            balance_before,
            balance,
            value,
            continuations: Vec::new(),
            loop_claims: Vec::new(),
            loop_places: Vec::new(),
            reads: None,
            word_tys: HashMap::new(),
            unsigned: std::collections::HashSet::new(),
            quantified: false,
            array_sorts: HashMap::new(),
            depth: 0,
            maps: HashMap::new(),
            prefix: String::new(),
            mode: Mode::Code,
            at: (0, 0),
            states: None,
            approximations: Vec::new(),
        }
    }

    pub(crate) fn start(&self) -> St {
        St {
            words: BTreeMap::new(),
            arrays: BTreeMap::new(),
            totals: BTreeMap::new(),
            locals: HashMap::new(),
            ok: "true".to_string(),
            why: "0".to_string(),
            out: "0".to_string(),
            written: BTreeSet::new(),
        }
    }

    /// A new value of type `ty`, with only what its type says.
    pub(crate) fn fresh(&mut self, ty: usize, what: &str) -> Val {
        let types = &self.checked.types;
        if let Some(word) = word_of(self.checked, ty) {
            return match word {
                Word1::Bool => Val::Bool(self.smt.fresh(what, "Bool")),
                Word1::Int(lo, hi) => {
                    let v = self.smt.fresh(what, "Int");
                    self.smt.assume(&in_range(&v, &lo, &hi));
                    Val::Int(v)
                }
            };
        }
        let peeled = peel(self.checked, ty);
        match types[peeled].kind {
            TyKind::Unit => Val::Unit,
            TyKind::Record | TyKind::Tuple if !is_sum(types, peeled) => {
                let fields: Vec<usize> = types[peeled].fields.iter().map(|f| f.ty).collect();
                Val::Tuple(fields.into_iter().map(|f| self.fresh(f, what)).collect())
            }
            _ => Val::Opaque,
        }
    }

    /// A local's terms, when it is a word.
    pub(crate) fn word_term(st: &St, sym: usize) -> Option<String> {
        match st.locals.get(&sym) {
            Some(Val::Int(t) | Val::Bool(t)) => Some(t.clone()),
            _ => None,
        }
    }

    /// An environment value the phase read, such as `Evm.sender()`.
    pub(crate) fn env_term(&self, key: &str) -> Option<String> {
        match self.env.get(key) {
            Some(Val::Int(t) | Val::Bool(t)) => Some(t.clone()),
            _ => None,
        }
    }

    pub(crate) fn bind(&mut self, st: &mut St, sym: usize, what: &str) {
        let ty = self.checked.syms[sym].ty;
        let v = self.fresh(ty, what);
        st.locals.insert(sym, v);
    }

    /// A local, or a new value for one this phase never set: a parameter, or a value an
    /// earlier phase kept, of which it knows only the type.
    fn local(&mut self, st: &mut St, sym: usize) -> Val {
        if let Some(v) = st.locals.get(&sym) {
            return v.clone();
        }
        let ty = self.checked.syms[sym].ty;
        let v = self.fresh(ty, "kept");
        st.locals.insert(sym, v.clone());
        v
    }

    // Storage.

    fn init_word(&mut self, leaf: u32, ty: usize) -> Val {
        self.word_tys.entry(leaf).or_insert(ty);
        if let Some(v) = self.init_words.get(&leaf) {
            return v.clone();
        }
        let v = if self.zero && !self.checked.transient_leaf(leaf) {
            match word_of(self.checked, ty) {
                Some(Word1::Bool) => Val::Bool("false".to_string()),
                Some(Word1::Int(..)) => Val::Int("0".to_string()),
                None => Val::Opaque,
            }
        } else {
            self.fresh(ty, &format!("s{leaf}"))
        };
        self.init_words.insert(leaf, v.clone());
        v
    }

    fn array(&mut self, st: &St, cell: &Cell, sort: &str) -> String {
        if let Some(a) = st.arrays.get(cell) {
            return a.clone();
        }
        if let Some(a) = self.init_arrays.get(cell) {
            return a.clone();
        }
        let array_sort = array_sort(cell.arity, sort);
        self.array_sorts.insert(cell.clone(), array_sort.clone());
        let a = if self.zero && !self.checked.transient_leaf(cell.leaf) {
            let zero = if sort == "Bool" { "false" } else { "0" };
            let mut term = zero.to_string();
            let mut inner = sort.to_string();
            for _ in 0..cell.arity {
                term = format!("((as const (Array Int {inner})) {term})");
                inner = format!("(Array Int {inner})");
            }
            self.smt.define("empty", &array_sort, &term)
        } else {
            self.smt.fresh(&format!("m{}", cell.leaf), &array_sort)
        };
        self.init_arrays.insert(cell.clone(), a.clone());
        a
    }

    fn total(&mut self, st: &St, key: &(Cell, bool)) -> String {
        if let Some(t) = st.totals.get(key) {
            return t.clone();
        }
        if let Some(t) = self.init_totals.get(key) {
            return t.clone();
        }
        let t = if self.zero {
            "0".to_string()
        } else {
            self.smt.fresh("total", "Int")
        };
        self.init_totals.insert(key.clone(), t.clone());
        t
    }

    /// What each total says of the maps it adds up: every value it holds, and any two of them
    /// at different keys, are at most the total. A total of signed values says nothing.
    pub(crate) fn total_facts(&mut self) {
        if self.zero {
            return;
        }
        let mut facts = Vec::new();
        for (key, total) in &self.init_totals {
            let Some(array) = self.init_arrays.get(&key.0) else {
                continue;
            };
            let count = key.1;
            if !count && !self.unsigned.contains(&key.0) {
                continue;
            }
            let val = |k: &str| {
                let v = format!("(select {array} {k})");
                if count {
                    format!("(ite (= {v} 0) 0 1)")
                } else {
                    v
                }
            };
            let mut keys: Vec<String> = Vec::new();
            for k in self.keys.get(&key.0).into_iter().flatten() {
                if !keys.contains(k) {
                    keys.push(k.clone());
                }
            }
            facts.push(format!("(<= 0 {total})"));
            if !count {
                facts.push(format!("(forall ((q Int)) (<= 0 (select {array} q)))"));
            }
            for (i, a) in keys.iter().enumerate() {
                facts.push(format!("(<= {} {total})", val(a)));
                facts.push(format!(
                    "(forall ((q Int)) (=> (not (= q {a})) (<= (+ {} {}) {total})))",
                    val("q"),
                    val(a)
                ));
                for b in &keys[i + 1..] {
                    facts.push(format!(
                        "(=> (not (= {a} {b})) (<= (+ {} {}) {total}))",
                        val(a),
                        val(b)
                    ));
                }
            }
        }
        for fact in facts {
            self.smt.assume(&fact);
        }
    }

    /// For checking a counterexample against what totals are: each total the phase started
    /// from, whether it counts, and each key it was read at, with the value there.
    pub(crate) fn total_checks(&self) -> Vec<(bool, String, Vec<(String, String)>)> {
        if self.zero {
            return Vec::new();
        }
        let mut out = Vec::new();
        for (key, total) in &self.init_totals {
            let Some(array) = self.init_arrays.get(&key.0) else {
                continue;
            };
            let mut keys: Vec<(String, String)> = Vec::new();
            for k in self.keys.get(&key.0).into_iter().flatten() {
                if !keys.iter().any(|(have, _)| have == k) {
                    keys.push((k.clone(), format!("(select {array} {k})")));
                }
            }
            out.push((key.1, total.clone(), keys));
        }
        out
    }

    fn read_cell(&mut self, st: &St, cell: &Cell, keys: &[String], ty: usize) -> Val {
        if let Some(touched) = &mut self.touched {
            touched.insert(Key::Cell(cell.clone()));
        }
        let Some(word) = word_of(self.checked, ty) else {
            return self.fresh(ty, "value");
        };
        let sort = word.sort();
        if matches!(&word, Word1::Int(lo, _) if lo == "0") {
            self.unsigned.insert(cell.clone());
        }
        let mut term = self.array(st, cell, sort);
        for k in keys {
            term = format!("(select {term} {k})");
        }
        if !self.smt.scoped() {
            self.keys
                .entry(cell.clone())
                .or_default()
                .extend(keys.first().cloned());
        }
        let name = self.smt.define("read", sort, &term);
        if let Word1::Int(lo, hi) = &word {
            self.smt.assume(&in_range(&name, lo, hi));
        }
        match word {
            Word1::Bool => Val::Bool(name),
            Word1::Int(..) => Val::Int(name),
        }
    }

    fn write_cell(&mut self, st: &mut St, cell: &Cell, keys: &[String], ty: usize, v: &Val) {
        let Some(word) = word_of(self.checked, ty) else {
            return;
        };
        let sort = word.sort();
        let term = match v {
            Val::Int(t) | Val::Bool(t) => t.clone(),
            _ => {
                let fresh = self.fresh(ty, "value");
                match fresh {
                    Val::Int(t) | Val::Bool(t) => t,
                    _ => return,
                }
            }
        };
        let array = self.array(st, cell, sort);
        for tracked in [(cell.clone(), false), (cell.clone(), true)] {
            if !self.tracked.contains(&tracked) || keys.len() != 1 {
                continue;
            }
            let before = self.read_cell(st, cell, keys, ty);
            let Val::Int(before) = before else { continue };
            let total = self.total(st, &tracked);
            let updated = if tracked.1 {
                format!("(+ (- {total} (ite (= {before} 0) 0 1)) (ite (= {term} 0) 0 1))")
            } else {
                format!("(+ (- {total} {before}) {term})")
            };
            let updated = self.smt.define("total", "Int", &updated);
            st.totals.insert(tracked, updated);
        }
        let stored = store_nested(&array, keys, &term);
        let array_sort = array_sort(cell.arity, sort);
        let stored = self.smt.define("store", &array_sort, &stored);
        self.keys
            .entry(cell.clone())
            .or_default()
            .extend(keys.first().cloned());
        st.arrays.insert(cell.clone(), stored);
        st.written.insert(Key::Cell(cell.clone()));
    }

    fn read_word(&mut self, st: &St, leaf: u32, ty: usize) -> Val {
        if let Some(touched) = &mut self.touched {
            touched.insert(Key::Word(leaf));
        }
        match st.words.get(&leaf) {
            Some(v) => v.clone(),
            None => self.init_word(leaf, ty),
        }
    }

    fn write_word(&mut self, st: &mut St, leaf: u32, ty: usize, v: Val) {
        self.word_tys.entry(leaf).or_insert(ty);
        st.words.insert(leaf, v);
        st.written.insert(Key::Word(leaf));
    }

    /// A stored record or tuple at `leaf`, or one word.
    fn read_stored(&mut self, st: &St, leaf: u32, ty: usize) -> Val {
        if word_of(self.checked, ty).is_some() {
            return self.read_word(st, leaf, ty);
        }
        let peeled = peel(self.checked, ty);
        let t = &self.checked.types[peeled];
        if matches!(t.kind, TyKind::Record | TyKind::Tuple) && !is_sum(&self.checked.types, peeled)
        {
            let fields: Vec<(u32, usize)> = t.fields.iter().map(|f| (f.slot, f.ty)).collect();
            return Val::Tuple(
                fields
                    .into_iter()
                    .map(|(slot, fty)| self.read_stored(st, leaf + slot, fty))
                    .collect(),
            );
        }
        self.fresh(ty, "stored")
    }

    fn write_stored(&mut self, st: &mut St, leaf: u32, ty: usize, v: &Val) {
        if word_of(self.checked, ty).is_some() {
            let v = match v {
                Val::Int(_) | Val::Bool(_) => v.clone(),
                _ => self.fresh(ty, "stored"),
            };
            self.write_word(st, leaf, ty, v);
            return;
        }
        let peeled = peel(self.checked, ty);
        let t = &self.checked.types[peeled];
        if matches!(t.kind, TyKind::Record | TyKind::Tuple) && !is_sum(&self.checked.types, peeled)
        {
            let fields: Vec<(u32, usize)> = t.fields.iter().map(|f| (f.slot, f.ty)).collect();
            for (i, (slot, fty)) in fields.into_iter().enumerate() {
                let part = match v {
                    Val::Tuple(parts) => parts.get(i).cloned().unwrap_or(Val::Opaque),
                    _ => Val::Opaque,
                };
                self.write_stored(st, leaf + slot, fty, &part);
            }
        }
    }

    /// A record in a map: each word of it is a map of its own.
    fn read_cells(&mut self, st: &St, cell: &Cell, keys: &[String], ty: usize) -> Val {
        if word_of(self.checked, ty).is_some() {
            return self.read_cell(st, cell, keys, ty);
        }
        let peeled = peel(self.checked, ty);
        let t = &self.checked.types[peeled];
        if matches!(t.kind, TyKind::Record | TyKind::Tuple) && !is_sum(&self.checked.types, peeled)
        {
            let fields: Vec<(String, usize)> = t
                .fields
                .iter()
                .enumerate()
                .map(|(i, f)| (field_name(&f.name, i), f.ty))
                .collect();
            return Val::Tuple(
                fields
                    .into_iter()
                    .map(|(name, fty)| {
                        let sub = Cell {
                            leaf: cell.leaf,
                            shape: format!("{}.{name}", cell.shape),
                            arity: cell.arity,
                        };
                        self.read_cells(st, &sub, keys, fty)
                    })
                    .collect(),
            );
        }
        self.fresh(ty, "value")
    }

    fn write_cells(&mut self, st: &mut St, cell: &Cell, keys: &[String], ty: usize, v: &Val) {
        if word_of(self.checked, ty).is_some() {
            self.write_cell(st, cell, keys, ty, v);
            return;
        }
        let peeled = peel(self.checked, ty);
        let t = &self.checked.types[peeled];
        if matches!(t.kind, TyKind::Record | TyKind::Tuple) && !is_sum(&self.checked.types, peeled)
        {
            let fields: Vec<(String, usize)> = t
                .fields
                .iter()
                .enumerate()
                .map(|(i, f)| (field_name(&f.name, i), f.ty))
                .collect();
            for (i, (name, fty)) in fields.into_iter().enumerate() {
                let sub = Cell {
                    leaf: cell.leaf,
                    shape: format!("{}.{name}", cell.shape),
                    arity: cell.arity,
                };
                let part = match v {
                    Val::Tuple(parts) => parts.get(i).cloned().unwrap_or(Val::Opaque),
                    _ => Val::Opaque,
                };
                self.write_cells(st, &sub, keys, fty, &part);
            }
        }
    }

    /// Where a storage expression reads, or `None` when it is no storage.
    fn place(&mut self, st: &mut St, e: &'a Expr, ctx: &Ctx) -> Res<Option<Place>> {
        let Some(root) = expr_root(e) else {
            return Ok(None);
        };
        let Some(sym) = self.checked.syms.get(root) else {
            return Ok(None);
        };
        if !sym.storage {
            return Ok(None);
        }
        let base = if self.checked.slot_syms.contains_key(&root) {
            match self.maps.get(&root) {
                Some(leaf) => *leaf,
                None => return stop(e.line(), e.col(), "it reads a map it cannot place"),
            }
        } else {
            sym.slot
        };
        let domain_ty = sym.ty;
        // Root first; the domain itself, however it is named, is not part of the path.
        let mut chain = Vec::new();
        let mut cur = e;
        loop {
            chain.push(cur);
            match cur {
                Expr::Field { base, .. } | Expr::Index { base, .. } => cur = base,
                _ => break,
            }
        }
        chain.reverse();
        let path: Vec<&Expr> = chain
            .into_iter()
            .skip_while(|node| node.ty() == domain_ty || matches!(node, Expr::Ident { .. }))
            .collect();
        let mut label = domain_label(e);
        let mut leaf = None;
        let mut shape = String::new();
        let mut keys = Vec::new();
        for node in &path {
            match node {
                Expr::Field { name, leaf: l, .. } => {
                    label.push('.');
                    label.push_str(name);
                    if keys.is_empty() {
                        leaf = Some(base + *l);
                    } else {
                        shape.push('.');
                        shape.push_str(name);
                    }
                }
                Expr::Index { index, leaf: l, .. } => {
                    if keys.is_empty() {
                        leaf.get_or_insert(base + *l);
                    }
                    shape.push_str("[]");
                    let k = self.eval(st, index, ctx)?;
                    let k = self.key(k)?;
                    label.push_str("[_]");
                    keys.push(k);
                }
                _ => {}
            }
        }
        let Some(leaf) = leaf else {
            return Ok(None);
        };
        Ok(Some(if keys.is_empty() {
            if peel_kind(self.checked, e.ty()) == TyKind::Map {
                Place::Map {
                    cell: Cell {
                        leaf,
                        shape: "[]".to_string(),
                        arity: 1,
                    },
                    label,
                }
            } else {
                Place::Word { leaf, label }
            }
        } else {
            let arity = keys.len();
            Place::Cell {
                cell: Cell { leaf, shape, arity },
                keys,
                label,
            }
        }))
    }

    /// A key as an array's index: a word, or a new integer for what the prover does not
    /// model.
    fn key(&mut self, v: Val) -> Res<String> {
        Ok(match v {
            Val::Int(t) => t,
            Val::Bool(t) => format!("(ite {t} 1 0)"),
            _ => {
                self.approx("a map key it does not model")?;
                self.smt.fresh("key", "Int")
            }
        })
    }

    fn read_place(&mut self, st: &St, place: &Place, ty: usize) -> Val {
        let v = match place {
            Place::Word { leaf, .. } => self.read_stored(st, *leaf, ty),
            Place::Cell { cell, keys, .. } => self.read_cells(st, cell, keys, ty),
            Place::Map { .. } => Val::Opaque,
        };
        if let Some(touched) = &mut self.touched {
            match place {
                Place::Word { leaf, .. } => {
                    touched.insert(Key::Word(*leaf));
                }
                Place::Cell { cell, .. } | Place::Map { cell, .. } => {
                    touched.insert(Key::Cell(cell.clone()));
                }
            }
        }
        if let (Some(reads), Place::Word { label, .. } | Place::Cell { label, .. }) =
            (&mut self.reads, place)
        {
            if let Val::Int(t) | Val::Bool(t) = &v {
                reads.push((format!("{}{label}", self.prefix), t.clone()));
            }
        }
        v
    }

    // Statements.

    pub(crate) fn stmts(&mut self, st: &mut St, stmts: &'a [Stmt], ctx: &Ctx) -> Res<()> {
        for s in stmts {
            self.stmt(st, s, ctx)?;
        }
        Ok(())
    }

    fn stmt(&mut self, st: &mut St, s: &'a Stmt, ctx: &Ctx) -> Res<()> {
        if let Some(at) = stmt_at(s) {
            self.at = at;
        }
        match s {
            Stmt::Const {
                expr,
                sym,
                part_syms,
                ..
            }
            | Stmt::Var {
                expr,
                sym,
                part_syms,
                ..
            } => {
                let v = self.eval(st, expr, ctx)?;
                if let Some(sym) = sym {
                    st.locals.insert(*sym, v.clone());
                }
                if !part_syms.is_empty() {
                    let parts = match &v {
                        Val::Tuple(parts) => parts.clone(),
                        _ => Vec::new(),
                    };
                    for (i, psym) in part_syms.iter().enumerate() {
                        match parts.get(i) {
                            Some(p) => {
                                st.locals.insert(*psym, p.clone());
                            }
                            None => self.bind(st, *psym, "part"),
                        }
                    }
                }
            }
            Stmt::AssignTuple { expr, syms, .. } => {
                let v = self.eval(st, expr, ctx)?;
                for (i, sym) in syms.iter().enumerate() {
                    match &v {
                        Val::Tuple(parts) if i < parts.len() => {
                            st.locals.insert(*sym, parts[i].clone());
                        }
                        _ => self.bind(st, *sym, "part"),
                    }
                }
            }
            Stmt::Assign {
                line,
                col,
                path,
                index,
                keys,
                fields,
                expr,
                root,
                leaf,
                target,
                push,
            } => {
                let v = self.eval(st, expr, ctx)?;
                let Some(root) = root else {
                    return stop(*line, *col, "an assignment the prover cannot place");
                };
                let sym = &self.checked.syms[*root];
                if !sym.storage {
                    if index.is_some() || !fields.is_empty() || target.is_some() || *push {
                        // An element of a local list or map: the local is no longer known.
                        self.bind(st, *root, "local");
                    } else if path.len() > 1 {
                        let current = self.local(st, *root);
                        let ty = self.checked.syms[*root].ty;
                        let updated = self.set_field(current, ty, &path[1..], v);
                        st.locals.insert(*root, updated);
                    } else {
                        st.locals.insert(*root, v);
                    }
                    return Ok(());
                }
                let base = if self.checked.slot_syms.contains_key(root) {
                    match self.maps.get(root) {
                        Some(leaf) => *leaf,
                        None => return stop(*line, *col, "it writes a map it cannot place"),
                    }
                } else {
                    sym.slot
                };
                if target.is_some() || *push {
                    // A list in storage: no word an invariant can read.
                    return Ok(());
                }
                let abs = base + *leaf;
                let ty = expr.ty();
                match index {
                    None => self.write_stored(st, abs, ty, &v),
                    Some(first) => {
                        let mut key_vals = vec![first];
                        key_vals.extend(keys.iter());
                        let mut ks = Vec::new();
                        for k in key_vals {
                            let kv = self.eval(st, k, ctx)?;
                            ks.push(self.key(kv)?);
                        }
                        let mut shape = String::new();
                        for depth in 1..=ks.len() {
                            shape.push_str("[]");
                            for (at, name) in fields {
                                if *at == depth {
                                    shape.push('.');
                                    shape.push_str(name);
                                }
                            }
                        }
                        let cell = Cell {
                            leaf: abs,
                            shape,
                            arity: ks.len(),
                        };
                        self.write_cells(st, &cell, &ks, ty, &v);
                    }
                }
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                let c = self.eval(st, cond, ctx)?;
                let c = self.boolean(c)?;
                let mut yes = st.clone();
                self.stmts(&mut yes, then_body, ctx)?;
                let mut no = st.clone();
                self.stmts(&mut no, else_body, ctx)?;
                *st = self.merge(&c, yes, no);
            }
            Stmt::Assert { cond, reason, .. } => {
                let c = self.eval(st, cond, ctx)?;
                let c = self.boolean(c)?;
                let code = reason_code(reason);
                self.check(st, &c, code);
            }
            Stmt::Fail { reason } => {
                let code = reason_code(reason);
                self.check(st, "false", code);
            }
            Stmt::Call { expr, .. } => {
                self.eval(st, expr, ctx)?;
            }
            Stmt::Skip => {}
            Stmt::Emit { fields, .. } => {
                for (_, e) in fields {
                    self.eval(st, e, ctx)?;
                }
            }
            Stmt::Defer {
                line,
                col,
                expr,
                value,
                gas,
                then,
            } => {
                if let Expr::Call {
                    builtin: Some(Builtin::DelegateCall),
                    ..
                } = expr
                {
                    return stop(
                        *line,
                        *col,
                        "it defers `Evm.delegate_call`, which runs other code on this contract's storage",
                    );
                }
                let sent = match expr {
                    Expr::Call {
                        builtin: Some(Builtin::Transfer),
                        args,
                        ..
                    } => Some(&args[1]),
                    _ => value.as_ref(),
                };
                if let Expr::Call { args, base, .. } = expr {
                    for a in args {
                        self.eval(st, a, ctx)?;
                    }
                    if let Some(b) = base.as_deref().filter(|b| !is_namespace(b)) {
                        self.eval(st, b, ctx)?;
                    }
                }
                if let Some(g) = gas {
                    self.eval(st, g, ctx)?;
                }
                if let Some(sent) = sent {
                    let v = self.eval(st, sent, ctx)?;
                    let v = match v {
                        Val::Int(t) => t,
                        _ => {
                            let t = self.smt.fresh("sent", "Int");
                            self.smt.assume(&format!("(<= 0 {t})"));
                            t
                        }
                    };
                    st.out = self
                        .smt
                        .define("out", "Int", &format!("(+ {} {v})", st.out));
                    st.written.insert(Key::Balance);
                }
                if let Some(then) = then {
                    self.continuations.push(Continuation {
                        then,
                        after: crate::route::fmt_expr(expr),
                    });
                }
            }
            Stmt::For {
                line,
                col,
                iter,
                until,
                body,
                counter,
                elem,
                cap,
                invariants,
                ..
            } => {
                let at = (*line, *col);
                if invariants.is_empty() {
                    self.for_loop(
                        st,
                        at,
                        iter,
                        until.as_ref(),
                        body,
                        *counter,
                        *elem,
                        *cap,
                        ctx,
                    )?
                } else {
                    self.invariant_loop(
                        st,
                        at,
                        iter,
                        until.as_ref(),
                        body,
                        *counter,
                        *elem,
                        *cap,
                        invariants,
                        ctx,
                    )?
                }
            }
        }
        Ok(())
    }

    fn set_field(&mut self, current: Val, ty: usize, path: &[String], v: Val) -> Val {
        let peeled = peel(self.checked, ty);
        let t = &self.checked.types[peeled];
        let Some(pos) = t.fields.iter().position(|f| f.name == path[0]) else {
            return Val::Opaque;
        };
        let fty = t.fields[pos].ty;
        let mut parts = match current {
            Val::Tuple(parts) => parts,
            _ => return Val::Opaque,
        };
        if pos >= parts.len() {
            return Val::Opaque;
        }
        parts[pos] = if path.len() > 1 {
            let inner = parts[pos].clone();
            self.set_field(inner, fty, &path[1..], v)
        } else {
            v
        };
        Val::Tuple(parts)
    }

    fn for_loop(
        &mut self,
        st: &mut St,
        (line, col): (u32, u32),
        iter: &'a ForIter,
        until: Option<&'a Expr>,
        body: &'a [Stmt],
        counter: Option<usize>,
        elem: Option<usize>,
        cap: Option<u64>,
        ctx: &Ctx,
    ) -> Res<()> {
        let ForIter::Range { lo, hi } = iter else {
            return self.forget_loop(st, (line, col), iter, body, counter, elem, ctx);
        };
        let lo_v = self.eval(st, lo, ctx)?;
        let hi_v = self.eval(st, hi, ctx)?;
        let (Val::Int(lo_t), Val::Int(hi_t)) = (lo_v, hi_v) else {
            return self.forget_loop(st, (line, col), iter, body, counter, elem, ctx);
        };
        // A bound the loop may not pass, or a count known now.
        let known = match (lo_t.parse::<u64>(), hi_t.parse::<u64>()) {
            (Ok(a), Ok(b)) => Some(b.saturating_sub(a)),
            _ => None,
        };
        let n = match (cap, known) {
            (_, Some(k)) if k <= UNROLL => k,
            (Some(c), _) if c <= UNROLL => {
                // More than `bound` iterations revert.
                self.check(st, &format!("(<= (- {hi_t} {lo_t}) {c})"), PANIC);
                c
            }
            (cap, _) => {
                if let Some(c) = cap {
                    self.check(st, &format!("(<= (- {hi_t} {lo_t}) {c})"), PANIC);
                }
                return self.forget_loop(st, (line, col), iter, body, counter, elem, ctx);
            }
        };
        let _ = elem;
        let mut running = "true".to_string();
        for i in 0..n {
            let at = format!("(+ {lo_t} {i})");
            let go = self
                .smt
                .define("go", "Bool", &and(&running, &format!("(< {at} {hi_t})")));
            let mut inside = st.clone();
            if let Some(c) = counter {
                let at = self.smt.define("i", "Int", &at);
                inside.locals.insert(c, Val::Int(at));
            }
            self.stmts(&mut inside, body, ctx)?;
            if let Some(until) = until {
                let stop_now = self.eval(&mut inside, until, ctx)?;
                let stop_now = self.boolean(stop_now)?;
                running = self
                    .smt
                    .define("go", "Bool", &and(&go, &format!("(not {stop_now})")));
            } else {
                running = go.clone();
            }
            let skipped = st.clone();
            *st = self.merge(&go, inside, skipped);
        }
        Ok(())
    }

    /// A loop too long to run iteration by iteration: what its body can change becomes
    /// unknown, and it may revert, so a claim that relies on what it does is only approximate.
    fn forget_loop(
        &mut self,
        st: &mut St,
        (line, col): (u32, u32),
        _iter: &'a ForIter,
        body: &'a [Stmt],
        counter: Option<usize>,
        elem: Option<usize>,
        ctx: &Ctx,
    ) -> Res<()> {
        let (keys, locals) = self.loop_writes(st, body, counter, elem, ctx)?;
        self.havoc(st, &keys, &locals);
        self.may_revert(st);
        self.at = (line, col);
        self.approx(&format!(
            "a loop that may run more than {UNROLL} times; give it a smaller `bound` or an `invariant`"
        ))?;
        Ok(())
    }

    /// A loop with invariants: they hold as it starts, each iteration keeps them, and so they
    /// hold when it ends, whatever it did in between.
    fn invariant_loop(
        &mut self,
        st: &mut St,
        (line, col): (u32, u32),
        iter: &'a ForIter,
        until: Option<&'a Expr>,
        body: &'a [Stmt],
        counter: Option<usize>,
        elem: Option<usize>,
        cap: Option<u64>,
        invariants: &'a [Expr],
        ctx: &Ctx,
    ) -> Res<()> {
        let (lo, hi) = match iter {
            ForIter::Range { lo, hi } => {
                let lo = self.eval(st, lo, ctx)?;
                let hi = self.eval(st, hi, ctx)?;
                (self.int(lo, 0)?, self.int(hi, 0)?)
            }
            ForIter::List(list) => {
                self.eval(st, list, ctx)?;
                let length = self.smt.fresh("length", "Int");
                self.smt.assume(&format!("(<= 0 {length})"));
                ("0".to_string(), length)
            }
        };
        if let Some(c) = cap {
            self.check(st, &format!("(<= (- {hi} {lo}) {c})"), PANIC);
        }
        let place = format!("{line}:{col}");
        if !self.loop_places.contains(&place) {
            self.loop_places.push(place.clone());
        }
        let bind = |exec: &mut Self, s: &mut St, at: &str| {
            if let Some(c) = counter {
                s.locals.insert(c, Val::Int(at.to_string()));
            }
            if let Some(e) = elem {
                exec.bind(s, e, "element");
            }
        };
        // As the loop starts.
        let mut entry = st.clone();
        bind(self, &mut entry, &lo);
        let outer = self.reads.replace(Vec::new());
        let held = self.invariants_hold(&mut entry, invariants, ctx);
        let mut watch = std::mem::replace(&mut self.reads, outer).unwrap_or_default();
        let held = held?;
        watch.insert(0, ("the loop starts at".to_string(), lo.clone()));
        self.loop_claims.push(LoopClaim {
            label: format!("loop invariant at {place} holds as the loop starts"),
            goal: format!("(=> {} {held})", st.ok),
            watch,
        });
        // Each iteration, from any state the invariants allow.
        let (keys, locals) = self.loop_writes(st, body, counter, elem, ctx)?;
        let mut any = st.clone();
        self.havoc(&mut any, &keys, &locals);
        let i = self.smt.fresh("i", "Int");
        bind(self, &mut any, &i);
        let outer = self.reads.replace(Vec::new());
        let before = self.invariants_hold(&mut any, invariants, ctx);
        let mut watch: Vec<(String, String)> = std::mem::replace(&mut self.reads, outer)
            .unwrap_or_default()
            .into_iter()
            .map(|(label, t)| (format!("{label} before the iteration"), t))
            .collect();
        let before = before?;
        watch.insert(0, ("the iteration's counter".to_string(), i.clone()));
        let running = format!("(and (<= {lo} {i}) (< {i} {hi}))");
        any.ok = "true".to_string();
        let continuations = self.continuations.len();
        self.stmts(&mut any, body, ctx)?;
        self.continuations.truncate(continuations);
        let next = self.smt.define("i", "Int", &format!("(+ {i} 1)"));
        if let Some(c) = counter {
            any.locals.insert(c, Val::Int(next));
        }
        let _ = until;
        let outer = self.reads.replace(Vec::new());
        let after = self.invariants_hold(&mut any, invariants, ctx);
        let reads = std::mem::replace(&mut self.reads, outer).unwrap_or_default();
        let after = after?;
        watch.extend(
            reads
                .into_iter()
                .map(|(label, t)| (format!("{label} after it"), t)),
        );
        self.loop_claims.push(LoopClaim {
            label: format!("loop invariant at {place} is kept by each iteration"),
            goal: format!("(=> (and {before} {running} {}) {after})", any.ok),
            watch,
        });
        // When it ends: what the invariants say, with the counter where the loop stopped.
        self.havoc(st, &keys, &locals);
        let end = match until {
            None => self
                .smt
                .define("i", "Int", &format!("(ite (>= {hi} {lo}) {hi} {lo})")),
            Some(_) => {
                let end = self.smt.fresh("i", "Int");
                self.smt.assume(&format!(
                    "(and (<= {lo} {end}) (<= {end} (ite (>= {hi} {lo}) {hi} {lo})))"
                ));
                end
            }
        };
        let mut done = st.clone();
        if let Some(c) = counter {
            done.locals.insert(c, Val::Int(end));
        }
        let held = self.invariants_hold(&mut done, invariants, ctx)?;
        self.smt.assume(&held);
        self.may_revert(st);
        self.at = (line, col);
        self.approx(&format!(
            "the loop at {place}, known only by its invariants"
        ))?;
        Ok(())
    }

    /// The loop's invariants, all of them, read as a spec in `st`.
    fn invariants_hold(&mut self, st: &mut St, invariants: &'a [Expr], ctx: &Ctx) -> Res<String> {
        let mode = std::mem::replace(&mut self.mode, Mode::Spec);
        let spec = Ctx {
            mode: Mode::Spec,
            balance: ctx.balance.clone(),
        };
        let mut terms = Vec::new();
        let mut result = Ok(());
        for inv in invariants {
            match self.eval(st, inv, &spec).and_then(|v| self.boolean(v)) {
                Ok(t) => terms.push(t),
                Err(stop) => {
                    result = Err(stop);
                    break;
                }
            }
        }
        self.mode = mode;
        result?;
        Ok(match terms.as_slice() {
            [one] => one.clone(),
            many => format!("(and {})", many.join(" ")),
        })
    }

    /// What a loop's body can change: the storage it writes, the ether it sends, and the
    /// locals of the loop's function it assigns. Running the body once finds them, and the
    /// continuations it starts.
    fn loop_writes(
        &mut self,
        st: &St,
        body: &'a [Stmt],
        counter: Option<usize>,
        elem: Option<usize>,
        ctx: &Ctx,
    ) -> Res<(BTreeSet<Key>, Vec<usize>)> {
        let mut probe = st.clone();
        probe.written.clear();
        if let Some(c) = counter {
            self.bind(&mut probe, c, "i");
        }
        if let Some(e) = elem {
            self.bind(&mut probe, e, "element");
        }
        let before = probe.locals.clone();
        self.stmts(&mut probe, body, ctx)?;
        let locals = before
            .iter()
            .filter(|(sym, v)| {
                Some(*sym) != counter.as_ref()
                    && Some(*sym) != elem.as_ref()
                    && probe.locals.get(sym).map(|p| format!("{p:?}")) != Some(format!("{v:?}"))
            })
            .map(|(sym, _)| *sym)
            .collect();
        let mut keys = probe.written;
        if probe.out != st.out {
            keys.insert(Key::Balance);
        }
        Ok((keys, locals))
    }

    /// Each of `keys` and `locals` becomes a value of which only its type is known.
    fn havoc(&mut self, st: &mut St, keys: &BTreeSet<Key>, locals: &[usize]) {
        for key in keys {
            match key {
                Key::Word(leaf) => {
                    let v = match self.word_tys.get(leaf).copied() {
                        Some(ty) => self.fresh(ty, &format!("s{leaf}")),
                        None => Val::Opaque,
                    };
                    st.words.insert(*leaf, v);
                }
                Key::Cell(cell) => {
                    let sort = self
                        .array_sorts
                        .get(cell)
                        .cloned()
                        .unwrap_or_else(|| array_sort(cell.arity, "Int"));
                    let a = self.smt.fresh(&format!("m{}", cell.leaf), &sort);
                    st.arrays.insert(cell.clone(), a);
                    for count in [false, true] {
                        let tracked = (cell.clone(), count);
                        if self.tracked.contains(&tracked) {
                            let t = self.smt.fresh("total", "Int");
                            if count || self.unsigned.contains(cell) {
                                self.smt.assume(&format!("(<= 0 {t})"));
                            }
                            st.totals.insert(tracked, t);
                        }
                    }
                }
                Key::Balance => {
                    let out = self.smt.fresh("out", "Int");
                    self.smt.assume(&format!("(<= {} {out})", st.out));
                    st.out = out;
                }
            }
        }
        for sym in locals {
            self.bind(st, *sym, "local");
        }
        st.written.extend(keys.iter().cloned());
    }

    /// The call may have reverted somewhere the prover did not follow, for any reason.
    fn may_revert(&mut self, st: &mut St) {
        let went = self.smt.fresh("ok", "Bool");
        let code = self.smt.fresh("why", "Int");
        let failed = and(&st.ok, &format!("(not {went})"));
        st.why = self
            .smt
            .define("why", "Int", &format!("(ite {failed} {code} {})", st.why));
        st.ok = self.smt.define("ok", "Bool", &and(&st.ok, &went));
    }

    /// The state that is `yes` when `c` holds, and `no` otherwise.
    fn merge(&mut self, c: &str, yes: St, no: St) -> St {
        let mut out = no.clone();
        out.ok = self
            .smt
            .define("ok", "Bool", &format!("(ite {c} {} {})", yes.ok, no.ok));
        out.why = self
            .smt
            .define("why", "Int", &format!("(ite {c} {} {})", yes.why, no.why));
        out.out = self
            .smt
            .define("out", "Int", &format!("(ite {c} {} {})", yes.out, no.out));
        let leaves: BTreeSet<u32> = yes.words.keys().chain(no.words.keys()).copied().collect();
        for leaf in leaves {
            let a = yes.words.get(&leaf).cloned();
            let b = no.words.get(&leaf).cloned();
            let init = match self.word_tys.get(&leaf).copied() {
                Some(ty) => self.init_word(leaf, ty),
                None => Val::Opaque,
            };
            let v = self.ite(c, a.unwrap_or_else(|| init.clone()), b.unwrap_or(init));
            out.words.insert(leaf, v);
        }
        let cells: BTreeSet<Cell> = yes.arrays.keys().chain(no.arrays.keys()).cloned().collect();
        for cell in cells {
            let init = self.init_arrays.get(&cell).cloned();
            let (Some(a), Some(b)) = (
                yes.arrays.get(&cell).cloned().or_else(|| init.clone()),
                no.arrays.get(&cell).cloned().or(init),
            ) else {
                continue;
            };
            let sort = self
                .array_sorts
                .get(&cell)
                .cloned()
                .unwrap_or_else(|| array_sort(cell.arity, "Int"));
            let merged = self.smt.define("arr", &sort, &format!("(ite {c} {a} {b})"));
            out.arrays.insert(cell, merged);
        }
        let totals: BTreeSet<(Cell, bool)> =
            yes.totals.keys().chain(no.totals.keys()).cloned().collect();
        for key in totals {
            let init = self.init_totals.get(&key).cloned();
            let (Some(a), Some(b)) = (
                yes.totals.get(&key).cloned().or_else(|| init.clone()),
                no.totals.get(&key).cloned().or(init),
            ) else {
                continue;
            };
            let t = self
                .smt
                .define("total", "Int", &format!("(ite {c} {a} {b})"));
            out.totals.insert(key, t);
        }
        let syms: BTreeSet<usize> = yes.locals.keys().chain(no.locals.keys()).copied().collect();
        for sym in syms {
            let v = match (yes.locals.get(&sym), no.locals.get(&sym)) {
                (Some(a), Some(b)) => self.ite(c, a.clone(), b.clone()),
                (Some(a), None) => a.clone(),
                (None, Some(b)) => b.clone(),
                (None, None) => continue,
            };
            out.locals.insert(sym, v);
        }
        out.written = yes.written.union(&no.written).cloned().collect();
        out
    }

    fn ite(&mut self, c: &str, a: Val, b: Val) -> Val {
        match (a, b) {
            (Val::Int(x), Val::Int(y)) if x == y => Val::Int(x),
            (Val::Bool(x), Val::Bool(y)) if x == y => Val::Bool(x),
            (Val::Int(x), Val::Int(y)) => {
                Val::Int(self.smt.define("v", "Int", &format!("(ite {c} {x} {y})")))
            }
            (Val::Bool(x), Val::Bool(y)) => {
                Val::Bool(self.smt.define("v", "Bool", &format!("(ite {c} {x} {y})")))
            }
            (Val::Tuple(xs), Val::Tuple(ys)) if xs.len() == ys.len() => Val::Tuple(
                xs.into_iter()
                    .zip(ys)
                    .map(|(x, y)| self.ite(c, x, y))
                    .collect(),
            ),
            (Val::Unit, Val::Unit) => Val::Unit,
            _ => Val::Opaque,
        }
    }

    /// Something the prover does not model: a spec must not use it, and code that does gives
    /// the phase behavior it may not have, so a counterexample may not be real.
    fn approx(&mut self, what: &str) -> Res<()> {
        let (line, col) = self.at;
        if self.mode == Mode::Spec {
            return stop(
                line,
                col,
                format!("the prover does not model {what} in a spec"),
            );
        }
        let note = format!("{what} at {line}:{col}");
        if !self.approximations.contains(&note) {
            self.approximations.push(note);
        }
        Ok(())
    }

    /// A new value of type `ty`, for something the prover does not model.
    fn approx_fresh(&mut self, ty: usize, what: &str) -> Res<Val> {
        self.approx(what)?;
        Ok(self.fresh(ty, "value"))
    }

    fn boolean(&mut self, v: Val) -> Res<String> {
        match v {
            Val::Bool(t) => Ok(t),
            _ => {
                self.approx("a condition it cannot compute")?;
                Ok(self.smt.fresh("cond", "Bool"))
            }
        }
    }

    fn int(&mut self, v: Val, ty: usize) -> Res<String> {
        Ok(match v {
            Val::Int(t) => t,
            Val::Bool(t) => format!("(ite {t} 1 0)"),
            _ => {
                self.approx("a number it cannot compute")?;
                match self.fresh(ty, "value") {
                    Val::Int(t) => t,
                    _ => self.smt.fresh("value", "Int"),
                }
            }
        })
    }

    // Expressions.

    pub(crate) fn eval(&mut self, st: &mut St, e: &'a Expr, ctx: &Ctx) -> Res<Val> {
        self.at = (e.line(), e.col());
        match e {
            Expr::Lit { lit, ty, .. } => Ok(match lit {
                Lit::Uint(w) | Lit::Wei(w) | Lit::Duration(w) => Val::Int(dec(*w)),
                Lit::Int(w, _) => {
                    // A literal of a signed type is written as its bits.
                    if matches!(word_of(self.checked, *ty), Some(Word1::Int(ref lo, _)) if lo.starts_with('-'))
                        && w.bit(255)
                    {
                        Val::Int(format!("(- {})", dec(w.wrapping_neg())))
                    } else {
                        Val::Int(dec(*w))
                    }
                }
                Lit::Bool(b) => Val::Bool(b.to_string()),
                Lit::Unit => Val::Unit,
                _ => Val::Opaque,
            }),
            Expr::Ident { sym, ty, .. } => {
                if let Some(sym) = sym {
                    if self.checked.syms[*sym].storage {
                        return self.approx_fresh(*ty, "a whole storage record");
                    }
                    return Ok(self.local(st, *sym));
                }
                self.approx_fresh(*ty, "a built-in value")
            }
            Expr::Field { base, name, ty, .. } => {
                if let Some(place) = self.place(st, e, ctx)? {
                    return Ok(self.read_place(st, &place, *ty));
                }
                let b = self.eval(st, base, ctx)?;
                let bty = peel(self.checked, base.ty());
                let t = &self.checked.types[bty];
                if let (Val::Tuple(parts), Some(pos)) =
                    (&b, t.fields.iter().position(|f| &f.name == name))
                {
                    return Ok(parts.get(pos).cloned().unwrap_or(Val::Opaque));
                }
                self.approx_fresh(*ty, &format!("`.{name}` of a value it does not model"))
            }
            Expr::Index {
                base, index, ty, ..
            } => {
                if let Some(place) = self.place(st, e, ctx)? {
                    return Ok(self.read_place(st, &place, *ty));
                }
                self.eval(st, base, ctx)?;
                self.eval(st, index, ctx)?;
                self.approx_fresh(*ty, "an element of a list or string")
            }
            Expr::Query { expr, gas, ty, .. } => {
                if let Expr::Call { args, base, .. } = expr.as_ref() {
                    for a in args {
                        self.eval(st, a, ctx)?;
                    }
                    if let Some(b) = base.as_deref().filter(|b| !is_namespace(b)) {
                        self.eval(st, b, ctx)?;
                    }
                }
                if let Some(g) = gas {
                    self.eval(st, g, ctx)?;
                }
                Ok(self.fresh(*ty, "answer"))
            }
            Expr::Call { .. } => self.call(st, e, ctx),
            Expr::Case {
                scrut, arms, ty, ..
            } => self.case(st, scrut, arms, *ty, ctx),
            Expr::Unary {
                op,
                expr,
                ty,
                line,
                col,
            } => {
                let v = self.eval(st, expr, ctx)?;
                match op {
                    UnOp::Not => {
                        let b = self.boolean(v)?;
                        Ok(Val::Bool(format!("(not {b})")))
                    }
                    UnOp::Neg => {
                        let x = self.int(v, *ty)?;
                        let r = self.smt.define("neg", "Int", &format!("(- {x})"));
                        self.checked_range(st, &r, *ty, ctx);
                        let _ = (line, col);
                        Ok(Val::Int(r))
                    }
                    UnOp::BitNot => self.approx_fresh(*ty, "`~`"),
                }
            }
            Expr::Binary {
                op,
                left,
                right,
                ty,
                ..
            } => self.binary(st, *op, left, right, *ty, ctx),
            Expr::Tuple { elems, .. } => {
                let mut parts = Vec::new();
                for x in elems {
                    parts.push(self.eval(st, x, ctx)?);
                }
                Ok(Val::Tuple(parts))
            }
            Expr::Record { fields, ty, .. } => {
                let mut by_name = HashMap::new();
                for (name, x) in fields {
                    let v = self.eval(st, x, ctx)?;
                    by_name.insert(name.clone(), v);
                }
                let peeled = peel(self.checked, *ty);
                let names: Vec<String> = self.checked.types[peeled]
                    .fields
                    .iter()
                    .map(|f| f.name.clone())
                    .collect();
                Ok(Val::Tuple(
                    names
                        .iter()
                        .map(|n| by_name.remove(n).unwrap_or(Val::Opaque))
                        .collect(),
                ))
            }
            Expr::List { elems, .. } => {
                for x in elems {
                    self.eval(st, x, ctx)?;
                }
                Ok(Val::Opaque)
            }
        }
    }

    /// In code, a value outside its type reverts.
    fn checked_range(&mut self, st: &mut St, term: &str, ty: usize, ctx: &Ctx) {
        if ctx.mode == Mode::Spec {
            return;
        }
        if let Some(Word1::Int(lo, hi)) = word_of(self.checked, ty) {
            self.check(st, &in_range(term, &lo, &hi), PANIC);
        }
    }

    /// A check the code makes: when `c` fails, the call reverts with `code`, unless it has
    /// already.
    fn check(&mut self, st: &mut St, c: &str, code: i64) {
        if c == "true" {
            return;
        }
        let failed = and(&st.ok, &format!("(not {c})"));
        st.why = self.smt.define(
            "why",
            "Int",
            &format!("(ite {failed} {} {})", smt_int(code), st.why),
        );
        st.ok = self.smt.define("ok", "Bool", &and(&st.ok, c));
    }

    fn binary(
        &mut self,
        st: &mut St,
        op: BinOp,
        left: &'a Expr,
        right: &'a Expr,
        ty: usize,
        ctx: &Ctx,
    ) -> Res<Val> {
        if matches!(op, BinOp::And | BinOp::Or) {
            // The right side runs only when the left does not decide.
            let l = self.eval(st, left, ctx)?;
            let l = self.boolean(l)?;
            let mut rest = st.clone();
            let r = self.eval(&mut rest, right, ctx)?;
            let r = self.boolean(r)?;
            let (decides, value) = if op == BinOp::And {
                (format!("(not {l})"), format!("(and {l} {r})"))
            } else {
                (l.clone(), format!("(or {l} {r})"))
            };
            let decided = st.clone();
            *st = self.merge(&decides, decided, rest);
            return Ok(Val::Bool(self.smt.define("b", "Bool", &value)));
        }
        let lv = self.eval(st, left, ctx)?;
        let rv = self.eval(st, right, ctx)?;
        if op.is_cmp() {
            return self.compare(op, lv, rv, left.ty());
        }
        let signed =
            matches!(word_of(self.checked, ty), Some(Word1::Int(ref lo, _)) if lo.starts_with('-'));
        let (Val::Int(a), Val::Int(b)) = (&lv, &rv) else {
            return self.approx_fresh(ty, "arithmetic on values it does not model");
        };
        let term = match op {
            BinOp::Add => format!("(+ {a} {b})"),
            BinOp::Sub => format!("(- {a} {b})"),
            BinOp::Mul => format!("(* {a} {b})"),
            BinOp::Div | BinOp::Mod if signed => {
                return self.approx_fresh(ty, "signed division");
            }
            BinOp::Div | BinOp::Mod => {
                if ctx.mode == Mode::Code {
                    st.ok =
                        self.smt
                            .define("ok", "Bool", &and(&st.ok, &format!("(not (= {b} 0))")));
                }
                if op == BinOp::Div {
                    format!("(div {a} {b})")
                } else {
                    format!("(mod {a} {b})")
                }
            }
            _ => return self.approx_fresh(ty, &format!("`{}`", crate::route::bin_op(op))),
        };
        let r = self.smt.define("v", "Int", &term);
        self.checked_range(st, &r, ty, ctx);
        if ctx.mode == Mode::Code {
            if let Some(Word1::Int(lo, hi)) = word_of(self.checked, ty) {
                // Past its check, the value is in its type.
                let _ = (lo, hi);
            }
        }
        Ok(Val::Int(r))
    }

    fn compare(&mut self, op: BinOp, a: Val, b: Val, ty: usize) -> Res<Val> {
        let ordering = match op {
            BinOp::Lt => Some("<"),
            BinOp::Le => Some("<="),
            BinOp::Gt => Some(">"),
            BinOp::Ge => Some(">="),
            _ => None,
        };
        if let Some(smt_op) = ordering {
            return Ok(match (a, b) {
                (Val::Int(x), Val::Int(y)) => Val::Bool(format!("({smt_op} {x} {y})")),
                _ => {
                    self.approx("a comparison of values it does not model")?;
                    Val::Bool(self.smt.fresh("cmp", "Bool"))
                }
            });
        }
        Ok(match self.equal(a, b, ty) {
            Some(t) if op == BinOp::Eq => Val::Bool(t),
            Some(t) => Val::Bool(format!("(not {t})")),
            None => {
                self.approx("a comparison of values it does not model")?;
                Val::Bool(self.smt.fresh("cmp", "Bool"))
            }
        })
    }

    /// `a = b`, or for an ordering, `a op b`; `None` when the values are not modeled.
    fn equal(&mut self, a: Val, b: Val, _ty: usize) -> Option<String> {
        match (a, b) {
            (Val::Int(x), Val::Int(y)) | (Val::Bool(x), Val::Bool(y)) => {
                Some(format!("(= {x} {y})"))
            }
            (Val::Tuple(xs), Val::Tuple(ys)) if xs.len() == ys.len() => {
                let mut parts = Vec::new();
                for (x, y) in xs.into_iter().zip(ys) {
                    parts.push(self.equal(x, y, 0)?);
                }
                Some(if parts.is_empty() {
                    "true".to_string()
                } else {
                    format!("(and {})", parts.join(" "))
                })
            }
            (Val::Unit, Val::Unit) => Some("true".to_string()),
            _ => None,
        }
    }

    fn case(
        &mut self,
        st: &mut St,
        scrut: &'a Expr,
        arms: &'a [Arm],
        ty: usize,
        ctx: &Ctx,
    ) -> Res<Val> {
        let s = self.eval(st, scrut, ctx)?;
        let sty = peel(self.checked, scrut.ty());
        let enum_like = is_enum(&self.checked.types, sty);
        if !(enum_like && matches!(s, Val::Int(_))) {
            self.approx("a `case` on a value it does not model")?;
        }
        let variants: Vec<String> = self.checked.types[sty]
            .variants
            .iter()
            .map(|v| v.name.clone())
            .collect();
        // Each arm, with the condition that picks it.
        let mut conds = Vec::new();
        let mut taken = "false".to_string();
        for (i, arm) in arms.iter().enumerate() {
            let last = i + 1 == arms.len();
            let pick = match (&s, enum_like) {
                (Val::Int(tag), true) => {
                    let mut any = Vec::new();
                    for ctor in &arm.ctors {
                        if let Some(k) = variants.iter().position(|v| v == ctor) {
                            any.push(format!("(= {tag} {k})"));
                        }
                    }
                    if arm.ctors.iter().any(|c| c == "_") || any.is_empty() && last {
                        "true".to_string()
                    } else if any.is_empty() {
                        "false".to_string()
                    } else {
                        format!("(or {})", any.join(" "))
                    }
                }
                _ if last => "true".to_string(),
                _ => self.smt.fresh("arm", "Bool"),
            };
            let cond = self
                .smt
                .define("arm", "Bool", &format!("(and (not {taken}) {pick})"));
            taken = self
                .smt
                .define("taken", "Bool", &format!("(or {taken} {pick})"));
            conds.push(cond);
        }
        let mut result: Option<(St, Val)> = None;
        for (arm, cond) in arms.iter().zip(conds).rev() {
            let mut inside = st.clone();
            if let Some(b) = arm.bind_sym {
                self.bind(&mut inside, b, "payload");
            }
            for sym in &arm.tuple_syms {
                self.bind(&mut inside, *sym, "payload");
            }
            self.stmts(&mut inside, &arm.stmts, ctx)?;
            let v = self.eval(&mut inside, &arm.expr, ctx)?;
            result = Some(match result {
                None => (inside, v),
                Some((other, ov)) => {
                    let merged = self.merge(&cond, inside, other);
                    let value = self.ite(&cond, v, ov);
                    (merged, value)
                }
            });
        }
        match result {
            Some((merged, v)) => {
                *st = merged;
                Ok(v)
            }
            None => Ok(self.fresh(ty, "case")),
        }
    }

    fn call(&mut self, st: &mut St, e: &'a Expr, ctx: &Ctx) -> Res<Val> {
        let Expr::Call {
            line,
            col,
            args,
            base,
            callee,
            builtin,
            ty,
            ..
        } = e
        else {
            unreachable!()
        };
        if let Some(b) = builtin {
            return self.builtin(st, *b, args, base.as_deref(), *ty, (*line, *col), ctx);
        }
        let Some(idx) = callee else {
            for a in args {
                self.eval(st, a, ctx)?;
            }
            return Ok(self.fresh(*ty, "result"));
        };
        let f = &self.checked.prog.funcs[*idx];
        let mut vals = Vec::new();
        let mut maps = Vec::new();
        for (a, p) in args.iter().zip(&f.params) {
            let by_slot = p.sym.filter(|s| self.checked.slot_syms.contains_key(s));
            if let Some(sym) = by_slot {
                // A map given by its slot: the call reads and writes that map.
                match self.place(st, a, ctx)? {
                    Some(Place::Map { cell, .. }) => maps.push((sym, cell.leaf)),
                    _ => {
                        return stop(
                            *line,
                            *col,
                            format!("it gives `{}` a map inside another", f.name),
                        )
                    }
                }
                vals.push(Val::Opaque);
            } else if p.storage {
                return stop(
                    *line,
                    *col,
                    format!("it calls `{}`, which takes storage", f.name),
                );
            } else {
                vals.push(self.eval(st, a, ctx)?);
            }
        }
        let saved: Vec<(usize, Option<u32>)> = maps
            .iter()
            .map(|(sym, leaf)| (*sym, self.maps.insert(*sym, *leaf)))
            .collect();
        if self.depth > 64 {
            return stop(*line, *col, "calls nest too deep");
        }
        self.depth += 1;
        for (p, v) in f.params.iter().zip(vals) {
            if let Some(sym) = p.sym {
                st.locals.insert(sym, v);
            }
        }
        let result = (|| {
            self.stmts(st, &f.stmts, ctx)?;
            match &f.tail {
                Some(tail) => self.eval(st, tail, ctx),
                None => Ok(Val::Unit),
            }
        })();
        self.depth -= 1;
        for (sym, before) in saved {
            match before {
                Some(leaf) => self.maps.insert(sym, leaf),
                None => self.maps.remove(&sym),
            };
        }
        result
    }

    fn builtin(
        &mut self,
        st: &mut St,
        b: Builtin,
        args: &'a [Expr],
        base: Option<&'a Expr>,
        ty: usize,
        (line, col): (u32, u32),
        ctx: &Ctx,
    ) -> Res<Val> {
        match b {
            Builtin::SpecState(state) => {
                let Some(states) = &self.states else {
                    return self.eval(st, &args[0], ctx);
                };
                let (mut there, balance, word) = match state {
                    State::Old => (states.old.clone(), states.old_balance.clone(), "old"),
                    State::New => (states.new.clone(), states.new_balance.clone(), "new"),
                };
                // The spec's own names: its parameters and constants.
                there.locals = st.locals.clone();
                let inner = Ctx {
                    mode: Mode::Spec,
                    balance,
                };
                let prefix = std::mem::replace(&mut self.prefix, format!("{word}."));
                let v = self.eval(&mut there, &args[0], &inner);
                self.prefix = prefix;
                v
            }
            Builtin::SpecSum | Builtin::SpecCount => {
                let arg = match &args[0] {
                    Expr::Call {
                        builtin: Some(Builtin::SpecState(_)),
                        args,
                        ..
                    } => &args[0],
                    other => other,
                };
                let Some(Place::Map { cell, label }) = self.place(st, arg, ctx)? else {
                    return stop(line, col, "a `sum` or `count` the prover cannot track yet");
                };
                let key = (cell, b == Builtin::SpecCount);
                if self.collect {
                    self.tracked.insert(key.clone());
                }
                if let Some(touched) = &mut self.touched {
                    touched.insert(Key::Cell(key.0.clone()));
                }
                if !self.tracked.contains(&key) {
                    return stop(line, col, "internal: an untracked total");
                }
                let t = self.total(st, &key);
                if let Some(reads) = &mut self.reads {
                    let word = if key.1 { "count" } else { "sum" };
                    reads.push((format!("{}{word}({label})", self.prefix), t.clone()));
                }
                Ok(Val::Int(t))
            }
            Builtin::SpecForall => {
                let (
                    Some(Expr::Ident {
                        sym: Some(binder),
                        ty: bty,
                        ..
                    }),
                    Some(body),
                ) = (args.first(), args.get(2))
                else {
                    return stop(line, col, "internal: a `forall` without its variable");
                };
                let Some(word) = word_of(self.checked, *bty) else {
                    return stop(line, col, "`forall` over a type the prover does not model");
                };
                self.quantified = true;
                let (var, outer) = self.smt.enter("q");
                let bound = match &word {
                    Word1::Bool => Val::Bool(var.clone()),
                    Word1::Int(..) => Val::Int(var.clone()),
                };
                let before = st.locals.insert(*binder, bound);
                let reads = self.reads.take();
                let v = self.eval(st, body, ctx);
                self.reads = reads;
                match before {
                    Some(b) => st.locals.insert(*binder, b),
                    None => st.locals.remove(binder),
                };
                let mut facts = self.smt.leave(outer);
                let v = v?;
                let body = self.boolean(v)?;
                let sort = word.sort();
                if let Word1::Int(lo, hi) = &word {
                    facts.insert(0, in_range(&var, lo, hi));
                }
                let guard = match facts.as_slice() {
                    [] => "true".to_string(),
                    [one] => one.clone(),
                    many => format!("(and {})", many.join(" ")),
                };
                let term = format!("(forall (({var} {sort})) (=> {guard} {body}))");
                Ok(Val::Bool(self.smt.define("all", "Bool", &term)))
            }
            Builtin::SelfAddr => Ok(Val::Int(self.self_addr.clone())),
            Builtin::Value => Ok(Val::Int(self.value.clone())),
            Builtin::Balance => {
                if let Some(touched) = &mut self.touched {
                    touched.insert(Key::Balance);
                }
                let a = self.eval(st, &args[0], ctx)?;
                let a = self.int(a, ty)?;
                let other = self.smt.fresh("balance", "Int");
                self.smt.assume(&format!("(<= 0 {other})"));
                let term = format!("(ite (= {a} {}) {} {other})", self.self_addr, ctx.balance);
                let term = self.smt.define("balance", "Int", &term);
                if let Some(reads) = &mut self.reads {
                    let whose = crate::route::fmt_expr(&args[0]);
                    reads.push((format!("{}Evm.balance({whose})", self.prefix), term.clone()));
                }
                Ok(Val::Int(term))
            }
            Builtin::Sender
            | Builtin::TxOrigin
            | Builtin::TxGasPrice
            | Builtin::BlockNumber
            | Builtin::BlockTimestamp
            | Builtin::BlockCoinbase
            | Builtin::BlockBaseFee
            | Builtin::BlobBaseFee
            | Builtin::ChainId
            | Builtin::BlockPrevrandao
            | Builtin::BlockGasLimit => {
                let key = format!("{b:?}");
                if let Some(v) = self.env.get(&key) {
                    return Ok(v.clone());
                }
                let v = self.fresh(ty, &key.to_lowercase());
                // No call comes from the zero address: no one has its key.
                if let (Builtin::Sender | Builtin::TxOrigin, Val::Int(t)) = (b, &v) {
                    self.smt.assume(&format!("(not (= {t} 0))"));
                }
                self.env.insert(key, v.clone());
                Ok(v)
            }
            // What the chain holds, which the call cannot see into: one unknown for each
            // account or block it names, the same each time the phase asks.
            Builtin::CodeSize | Builtin::CodeHash | Builtin::BlockHash | Builtin::BlobHash => {
                let a = self.eval(st, &args[0], ctx)?;
                let a = self.int(a, args[0].ty())?;
                let key = format!("{b:?}({a})");
                if let Some(v) = self.env.get(&key) {
                    return Ok(v.clone());
                }
                let v = self.fresh(ty, &format!("{b:?}").to_lowercase());
                if !self.smt.scoped() {
                    self.env.insert(key, v.clone());
                }
                Ok(v)
            }
            Builtin::Cast => {
                let v = self.eval(st, &args[0], ctx)?;
                let from = args[0].ty();
                match (word_of(self.checked, from), word_of(self.checked, ty)) {
                    (Some(Word1::Bool), Some(Word1::Int(..))) => {
                        let b = self.boolean(v)?;
                        Ok(Val::Int(format!("(ite {b} 1 0)")))
                    }
                    (Some(Word1::Int(..)), Some(Word1::Int(..))) => {
                        let x = self.int(v, from)?;
                        self.checked_range(st, &x, ty, ctx);
                        Ok(Val::Int(x))
                    }
                    (Some(Word1::Bool), Some(Word1::Bool)) => Ok(v),
                    _ => self.approx_fresh(ty, "a conversion"),
                }
            }
            Builtin::Ctor(k)
                if args.is_empty() && is_enum(&self.checked.types, peel(self.checked, ty)) =>
            {
                Ok(Val::Int(k.to_string()))
            }
            Builtin::UintMulDiv => {
                let a = self.eval(st, &args[0], ctx)?;
                let bb = self.eval(st, &args[1], ctx)?;
                let d = self.eval(st, &args[2], ctx)?;
                let (Val::Int(a), Val::Int(bb), Val::Int(d)) = (a, bb, d) else {
                    return self.approx_fresh(ty, "`Uint.mul_div` of values it does not model");
                };
                if ctx.mode == Mode::Code {
                    st.ok =
                        self.smt
                            .define("ok", "Bool", &and(&st.ok, &format!("(not (= {d} 0))")));
                }
                let r = self
                    .smt
                    .define("v", "Int", &format!("(div (* {a} {bb}) {d})"));
                self.checked_range(st, &r, ty, ctx);
                Ok(Val::Int(r))
            }
            Builtin::Wrapping(op, _) => {
                let a = self.eval(st, &args[0], ctx)?;
                let bb = self.eval(st, &args[1], ctx)?;
                let Some(Word1::Int(lo, hi)) = word_of(self.checked, ty) else {
                    return self.approx_fresh(ty, "wrapping arithmetic");
                };
                let (Val::Int(a), Val::Int(bb)) = (a, bb) else {
                    return self.approx_fresh(ty, "wrapping arithmetic");
                };
                if lo.starts_with('-') {
                    return self.approx_fresh(ty, "signed wrapping arithmetic");
                }
                let term = match op {
                    BinOp::Add => format!("(+ {a} {bb})"),
                    BinOp::Sub => format!("(- {a} {bb})"),
                    _ => format!("(* {a} {bb})"),
                };
                let modulus = format!("(+ {hi} 1)");
                Ok(Val::Int(self.smt.define(
                    "v",
                    "Int",
                    &format!("(mod {term} {modulus})"),
                )))
            }
            Builtin::ListPop | Builtin::ListPush => Ok(Val::Unit),
            Builtin::Transfer
            | Builtin::Create
            | Builtin::RawCreate
            | Builtin::RawCall
            | Builtin::DelegateCall => Ok(Val::Opaque),
            _ => {
                for a in args {
                    self.eval(st, a, ctx)?;
                }
                if let Some(b) = base.filter(|b| !is_namespace(b)) {
                    self.eval(st, b, ctx)?;
                }
                self.approx_fresh(ty, &format!("`{b:?}`"))
            }
        }
    }
}

/// A local of a state, for reading one phase's value into a spec.
pub(crate) fn get_local(st: &St, sym: usize) -> Option<Val> {
    st.locals.get(&sym).cloned()
}

pub(crate) fn put_local(st: &mut St, sym: usize, v: Val) {
    st.locals.insert(sym, v);
}

/// A function spec's states: before the call, and once its first phase commits.
pub(crate) struct States {
    pub old: St,
    pub new: St,
    pub old_balance: String,
    pub new_balance: String,
}

/// Why a call reverts: an error's index plus one, or one of these.
pub(crate) const PANIC: i64 = -1;
pub(crate) const FORWARDED: i64 = -2;
const UNKNOWN_REVERT: i64 = -3;

fn reason_code(reason: &Raised) -> i64 {
    if reason.forward {
        return FORWARDED;
    }
    match reason.index {
        Some(i) => i as i64 + 1,
        None => UNKNOWN_REVERT,
    }
}

pub(crate) fn smt_int(n: i64) -> String {
    if n < 0 {
        format!("(- {})", -n)
    } else {
        n.to_string()
    }
}

/// What a spec or the code reads its state with.
pub(crate) struct Ctx {
    pub mode: Mode,
    /// The contract's ether, as `Evm.balance(Evm.self())` reads it here.
    pub balance: String,
}

pub(crate) enum Place {
    Word {
        leaf: u32,
        label: String,
    },
    Cell {
        cell: Cell,
        keys: Vec<String>,
        label: String,
    },
    /// A whole map, as `sum` and `count` read it.
    Map {
        cell: Cell,
        label: String,
    },
}

/// The storage symbol a path starts from.
fn expr_root(e: &Expr) -> Option<usize> {
    match e {
        Expr::Field { root, .. } | Expr::Index { root, .. } => *root,
        _ => None,
    }
}

/// How a storage path names its domain: `storage`, `settings`, or `M.m`.
fn domain_label(e: &Expr) -> String {
    let mut cur = e;
    let mut names = Vec::new();
    loop {
        match cur {
            Expr::Field { base, name, .. } => {
                names.push(name.clone());
                cur = base;
            }
            Expr::Index { base, .. } => {
                names.clear();
                cur = base;
            }
            Expr::Ident { name, .. } => {
                return name.clone();
            }
            _ => return "storage".to_string(),
        }
    }
}

/// A word type: its SMT sort, and for an integer, its bounds.
#[derive(Clone)]
pub(crate) enum Word1 {
    Bool,
    Int(String, String),
}

impl Word1 {
    fn sort(&self) -> &'static str {
        match self {
            Word1::Bool => "Bool",
            Word1::Int(..) => "Int",
        }
    }
}

fn peel(checked: &Checked, ty: usize) -> usize {
    let t = &checked.types[ty];
    if t.kind == TyKind::Nominal && t.variants.is_empty() {
        if let Some(under) = t.elem {
            return peel(checked, under);
        }
    }
    ty
}

fn peel_kind(checked: &Checked, ty: usize) -> TyKind {
    checked.types[peel(checked, ty)].kind
}

pub(crate) fn word_of(checked: &Checked, ty: usize) -> Option<Word1> {
    let peeled = peel(checked, ty);
    let t = &checked.types[peeled];
    if is_enum(&checked.types, peeled) {
        return Some(Word1::Int(
            "0".to_string(),
            (t.variants.len().saturating_sub(1)).to_string(),
        ));
    }
    let bits = u32::from(t.bits);
    Some(match t.kind {
        TyKind::Bool => Word1::Bool,
        TyKind::Uint => Word1::Int(
            "0".to_string(),
            max_bits(if bits == 0 { 256 } else { bits }),
        ),
        TyKind::Wei | TyKind::Timestamp => Word1::Int("0".to_string(), max_bits(256)),
        TyKind::Int => {
            let bits = if bits == 0 { 256 } else { bits };
            Word1::Int(
                format!("(- {})", pow2(bits - 1)),
                format!("(- {} 1)", pow2(bits - 1)),
            )
        }
        TyKind::Address | TyKind::Interface => Word1::Int("0".to_string(), max_bits(160)),
        TyKind::Bytes if bits > 0 => Word1::Int("0".to_string(), max_bits(bits * 8)),
        _ => return None,
    })
}

fn field_name(name: &str, i: usize) -> String {
    if name.is_empty() {
        i.to_string()
    } else {
        name.to_string()
    }
}

fn array_sort(arity: usize, sort: &str) -> String {
    let mut s = sort.to_string();
    for _ in 0..arity {
        s = format!("(Array Int {s})");
    }
    s
}

fn store_nested(array: &str, keys: &[String], value: &str) -> String {
    match keys {
        [] => value.to_string(),
        [k, rest @ ..] => {
            let inner = format!("(select {array} {k})");
            format!("(store {array} {k} {})", store_nested(&inner, rest, value))
        }
    }
}

pub(crate) fn and(a: &str, b: &str) -> String {
    match (a, b) {
        ("true", x) | (x, "true") => x.to_string(),
        ("false", _) | (_, "false") => "false".to_string(),
        _ => format!("(and {a} {b})"),
    }
}

pub(crate) fn in_range(term: &str, lo: &str, hi: &str) -> String {
    format!("(and (<= {lo} {term}) (<= {term} {hi}))")
}

fn pow2(bits: u32) -> String {
    dec_big(bits)
}

/// `2^bits - 1`, in decimal.
fn max_bits(bits: u32) -> String {
    format!("(- {} 1)", pow2(bits))
}

/// `2^bits`, in decimal.
fn dec_big(bits: u32) -> String {
    let mut digits = vec![1u8];
    for _ in 0..bits {
        let mut carry = 0;
        for d in digits.iter_mut() {
            let v = *d * 2 + carry;
            *d = v % 10;
            carry = v / 10;
        }
        if carry > 0 {
            digits.push(carry);
        }
    }
    digits.iter().rev().map(|d| char::from(b'0' + d)).collect()
}

/// A word, in decimal.
fn dec(w: Word) -> String {
    let mut digits = vec![0u8];
    for byte in w.to_be_bytes() {
        for bit in (0..8).rev() {
            let mut carry = (byte >> bit) & 1;
            for d in digits.iter_mut() {
                let v = *d * 2 + carry;
                *d = v % 10;
                carry = v / 10;
            }
            if carry > 0 {
                digits.push(carry);
            }
        }
    }
    let s: String = digits.iter().rev().map(|d| char::from(b'0' + d)).collect();
    let trimmed = s.trim_start_matches('0');
    if trimmed.is_empty() {
        "0".to_string()
    } else {
        trimmed.to_string()
    }
}

fn stmt_at(s: &Stmt) -> Option<(u32, u32)> {
    match s {
        Stmt::Const { line, col, .. }
        | Stmt::Var { line, col, .. }
        | Stmt::Assign { line, col, .. }
        | Stmt::If { line, col, .. }
        | Stmt::Assert { line, col, .. }
        | Stmt::Call { line, col, .. }
        | Stmt::Emit { line, col, .. }
        | Stmt::Defer { line, col, .. }
        | Stmt::For { line, col, .. }
        | Stmt::AssignTuple { line, col, .. } => Some((*line, *col)),
        Stmt::Fail { reason } => Some((reason.line, reason.col)),
        Stmt::Skip => None,
    }
}

/// `Evm` in `Evm.transfer(...)`: a name for built-ins, not a value.
fn is_namespace(e: &Expr) -> bool {
    matches!(e, Expr::Ident { sym: None, .. })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn numbers_print_in_decimal() {
        assert_eq!(dec(Word::from_u64(1234)), "1234");
        assert_eq!(dec(Word::from_u64(0)), "0");
        assert_eq!(dec_big(8), "256");
        assert_eq!(
            dec(Word::from_u64(0).wrapping_sub(Word::from_u64(1))),
            "115792089237316195423570985008687907853269984665640564039457584007913129639935"
        );
    }
}
