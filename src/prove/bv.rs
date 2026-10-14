//! Terms for the bytecode prover: bitvectors, booleans and arrays, shared and simplified as
//! they are built, then printed as SMT-LIB.
//!
//! Every term is an index into an arena, and building the same term twice gives the same
//! index. Constants fold, and the shapes the EVM produces often, such as a comparison's
//! `0` or `1` tested for zero, or a word assembled from its own bytes, fold back into what
//! they came from. The simplifier only rewrites a term to an equal one, with one
//! exception, the assumptions about keccak the documentation lists: hashes of different
//! lengths differ, and a hash is far from every slot the layout fixes.

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::word::Word;

pub(crate) type T = u32;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Sort {
    Bool,
    Bv(u32),
    /// Memory, calldata, code and return data: a byte at each word.
    Bytes,
    /// Storage: a word at each word.
    Words,
}

impl Sort {
    pub(crate) fn smt(self) -> String {
        match self {
            Sort::Bool => "Bool".to_string(),
            Sort::Bv(w) => format!("(_ BitVec {w})"),
            Sort::Bytes => "(Array (_ BitVec 256) (_ BitVec 8))".to_string(),
            Sort::Words => "(Array (_ BitVec 256) (_ BitVec 256))".to_string(),
        }
    }

    pub(crate) fn width(self) -> u32 {
        match self {
            Sort::Bv(w) => w,
            _ => 0,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Op {
    Add,
    Sub,
    Mul,
    UDiv,
    URem,
    SDiv,
    SRem,
    And,
    Or,
    Xor,
    Shl,
    LShr,
    AShr,
    Eq,
    Ult,
    Ule,
    Slt,
    Sle,
    BAnd,
    BOr,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Node {
    Bool(bool),
    /// A width, and a value below `2^min(width, 256)`.
    Const(u32, Word),
    Var(u32),
    Bound(u32),
    Not(T),
    BvNot(T),
    Bin(Op, T, T),
    Extract(u32, u32, T),
    /// The most significant part first.
    Concat(Vec<T>),
    ZExt(u32, T),
    SExt(u32, T),
    Ite(T, T, T),
    Select(T, T),
    Store(T, T, T),
    Zeros(Sort),
    /// `dst` with the bytes at `[at, at + len)` taken from `src`, starting at `from`.
    Copy([T; 5]),
    /// An array's bytes below a size, and zero from there on.
    ZeroFrom(T, T),
    /// Keccak-256 of a number of bytes.
    Keccak(u32, T),
    Uf(u32, Vec<T>),
    Forall(u32, T),
}

/// How far apart two hashes, or a hash and a fixed slot, are assumed to be: far enough that
/// no record in a map reaches from one to the other.
pub(crate) const FAR_BITS: u32 = 64;

pub(crate) struct Arena {
    nodes: Vec<Node>,
    sorts: Vec<Sort>,
    /// Whether a term uses a quantifier's variable.
    bound_in: Vec<bool>,
    /// Whether a term has a quantifier in it.
    quantified_in: Vec<bool>,
    ids: HashMap<Node, T>,
    pub vars: Vec<(String, Sort)>,
    pub ufs: Vec<(String, Vec<Sort>, Sort)>,
    pub bounds: Vec<Sort>,
    /// Each hash computed of known bytes: its value, and the bytes.
    pub origins: HashMap<Word, Vec<u8>>,
    /// The slots the layout fixes, which no hash comes near.
    pub fixed: HashSet<Word>,
    /// The hashes of unknown bytes, outside quantifiers, in the order they were built.
    pub apps: Vec<T>,
    /// The lengths hashed inside a quantifier.
    pub quantified_lens: BTreeSet<u32>,
    /// Facts that hold of every value: what the keccak assumptions say about the hashes.
    pub facts: Vec<T>,
    /// Each length's inverse of the hash function.
    inverses: HashMap<u32, u32>,
    /// Storage at a loop's head: each fresh array, the storage before the loop, and the
    /// roots the loop writes, under which the two may differ.
    pub frames: HashMap<T, (T, Written)>,
    /// Each term's free symbols, once asked for: see `symbols`.
    symbols: HashMap<T, std::rc::Rc<Vec<u32>>>,
    /// Bounds every path of a run keeps on some words, such as the calldata's size, from
    /// the assumptions it starts with: the least and the most each can be.
    ranges: HashMap<T, (u64, u64)>,
    /// How many reads through copies a read is inside, which `select` splits so far only.
    through: u32,
}

/// The copies a read splits into a choice of where it reads, deepest first: past them it
/// stays a read of the copy, which the solver takes as a function of the index.
const SPLIT_COPIES: u32 = 6;

/// The storage a loop writes, by the roots of its slots: see `Arena::root`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Written {
    pub roots: Vec<Word>,
    /// A write the prover cannot place under a root.
    pub all: bool,
}

impl Default for Arena {
    fn default() -> Self {
        Arena::new()
    }
}

fn mask(w: u32) -> Word {
    if w >= 256 {
        Word::from_u64(0).not()
    } else {
        Word::from_u64(0).not().shr(256 - w)
    }
}

fn fit(w: u32, v: Word) -> Word {
    v.bitand(mask(w))
}

/// `v` of width `w`, sign-extended to a word.
fn sext256(w: u32, v: Word) -> Word {
    if w >= 256 || w == 0 {
        return v;
    }
    if v.bit(w - 1) {
        v.bitor(mask(256).shl(w))
    } else {
        v
    }
}

impl Arena {
    pub(crate) fn new() -> Arena {
        Arena {
            nodes: Vec::new(),
            sorts: Vec::new(),
            bound_in: Vec::new(),
            quantified_in: Vec::new(),
            ids: HashMap::new(),
            vars: Vec::new(),
            ufs: Vec::new(),
            bounds: Vec::new(),
            origins: HashMap::new(),
            fixed: HashSet::new(),
            apps: Vec::new(),
            quantified_lens: BTreeSet::new(),
            facts: Vec::new(),
            inverses: HashMap::new(),
            frames: HashMap::new(),
            through: 0,
            symbols: HashMap::new(),
            ranges: HashMap::new(),
        }
    }

    /// Every path of the run keeps `t` within `[lo, hi]`: a fact, and the bound the
    /// simplifier uses.
    pub(crate) fn keep_within(&mut self, t: T, lo: u64, hi: u64) {
        let (l, h) = (self.num(256, lo), self.num(256, hi));
        let above = self.mk(Node::Bin(Op::Ule, l, t));
        let below = self.mk(Node::Bin(Op::Ule, t, h));
        self.facts.push(above);
        self.facts.push(below);
        self.ranges.insert(t, (lo, hi));
    }

    /// The least and the most a word can be, when its shape and the run's bounds tell.
    fn span(&self, t: T) -> Option<(u128, u128)> {
        if self.width(t) != 256 {
            return None;
        }
        if let Some(&(lo, hi)) = self.ranges.get(&t) {
            return Some((u128::from(lo), u128::from(hi)));
        }
        match self.node(t) {
            Node::Const(_, v) => small(*v).map(|v| (u128::from(v), u128::from(v))),
            Node::Bin(Op::Add, x, c) => {
                let c = u128::from(small(self.cval(*c)?)?);
                let (lo, hi) = self.span(*x)?;
                Some((lo + c, hi + c))
            }
            Node::ZExt(n, x) if 256 - n <= 64 => Some((0, (1u128 << (256 - n)) - 1)),
            _ => None,
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.nodes.len()
    }

    pub(crate) fn node(&self, t: T) -> &Node {
        &self.nodes[t as usize]
    }

    pub(crate) fn sort(&self, t: T) -> Sort {
        self.sorts[t as usize]
    }

    pub(crate) fn width(&self, t: T) -> u32 {
        self.sorts[t as usize].width()
    }

    pub(crate) fn has_bound(&self, t: T) -> bool {
        self.bound_in[t as usize]
    }

    pub(crate) fn has_forall(&self, t: T) -> bool {
        self.quantified_in[t as usize]
    }

    fn children(node: &Node) -> Vec<T> {
        match node {
            Node::Bool(_) | Node::Const(..) | Node::Var(_) | Node::Bound(_) | Node::Zeros(_) => {
                Vec::new()
            }
            Node::Not(a)
            | Node::BvNot(a)
            | Node::Extract(_, _, a)
            | Node::ZExt(_, a)
            | Node::SExt(_, a)
            | Node::Keccak(_, a)
            | Node::Forall(_, a) => vec![*a],
            Node::Bin(_, a, b) | Node::Select(a, b) | Node::ZeroFrom(a, b) => vec![*a, *b],
            Node::Ite(a, b, c) | Node::Store(a, b, c) => vec![*a, *b, *c],
            Node::Concat(parts) | Node::Uf(_, parts) => parts.clone(),
            Node::Copy(parts) => parts.to_vec(),
        }
    }

    /// The symbols a term is made of, sorted: each variable, each function, and the hash of
    /// each length, which the keccak facts tie together.
    pub(crate) fn symbols(&mut self, t: T) -> std::rc::Rc<Vec<u32>> {
        if let Some(s) = self.symbols.get(&t) {
            return s.clone();
        }
        let mut out: Vec<u32> = match self.node(t) {
            Node::Var(v) => vec![2 * v],
            Node::Uf(f, _) => vec![2 * f + 1],
            Node::Keccak(n, _) => vec![u32::MAX - n],
            _ => Vec::new(),
        };
        for k in self.kids(t) {
            let inner = self.symbols(k);
            out.extend(inner.iter().copied());
        }
        out.sort_unstable();
        out.dedup();
        let out = std::rc::Rc::new(out);
        self.symbols.insert(t, out.clone());
        out
    }

    pub(crate) fn kids(&self, t: T) -> Vec<T> {
        Arena::children(&self.nodes[t as usize])
    }

    fn sort_of(&self, node: &Node) -> Sort {
        match node {
            Node::Bool(_) | Node::Not(_) | Node::Forall(..) => Sort::Bool,
            Node::Const(w, _) => Sort::Bv(*w),
            Node::Var(v) => self.vars[*v as usize].1,
            Node::Bound(b) => self.bounds[*b as usize],
            Node::BvNot(a) => self.sort(*a),
            Node::Bin(op, a, _) => match op {
                Op::Eq | Op::Ult | Op::Ule | Op::Slt | Op::Sle | Op::BAnd | Op::BOr => Sort::Bool,
                _ => self.sort(*a),
            },
            Node::Extract(hi, lo, _) => Sort::Bv(hi - lo + 1),
            Node::Concat(parts) => Sort::Bv(parts.iter().map(|p| self.width(*p)).sum()),
            Node::ZExt(n, a) | Node::SExt(n, a) => Sort::Bv(self.width(*a) + n),
            Node::Ite(_, a, _) => self.sort(*a),
            Node::Select(a, _) => match self.sort(*a) {
                Sort::Bytes => Sort::Bv(8),
                _ => Sort::Bv(256),
            },
            Node::Store(a, ..) | Node::ZeroFrom(a, _) => self.sort(*a),
            Node::Zeros(s) => *s,
            Node::Copy(parts) => self.sort(parts[0]),
            Node::Keccak(..) => Sort::Bv(256),
            Node::Uf(f, _) => self.ufs[*f as usize].2,
        }
    }

    /// The quantifiers' variables `t` uses outside quantifiers of their own.
    fn free_bounds(&self, t: T, memo: &mut HashMap<T, Vec<u32>>) -> Vec<u32> {
        if !self.bound_in[t as usize] {
            return Vec::new();
        }
        if let Some(f) = memo.get(&t) {
            return f.clone();
        }
        let out = match self.node(t) {
            Node::Bound(b) => vec![*b],
            Node::Forall(b, body) => {
                let mut f = self.free_bounds(*body, memo);
                f.retain(|x| x != b);
                f
            }
            node => {
                let mut f: Vec<u32> = Arena::children(node)
                    .into_iter()
                    .flat_map(|c| self.free_bounds(c, memo))
                    .collect();
                f.sort_unstable();
                f.dedup();
                f
            }
        };
        memo.insert(t, out.clone());
        out
    }

    fn mk(&mut self, node: Node) -> T {
        if let Some(&t) = self.ids.get(&node) {
            return t;
        }
        let sort = self.sort_of(&node);
        let bound = match &node {
            Node::Bound(_) => true,
            // A quantifier inside another may use the outer one's variable.
            Node::Forall(id, body) => self
                .free_bounds(*body, &mut HashMap::new())
                .iter()
                .any(|b| b != id),
            other => Arena::children(other)
                .iter()
                .any(|c| self.bound_in[*c as usize]),
        };
        let quantified = matches!(node, Node::Forall(..))
            || Arena::children(&node)
                .iter()
                .any(|c| self.quantified_in[*c as usize]);
        let t = self.nodes.len() as T;
        self.nodes.push(node.clone());
        self.sorts.push(sort);
        self.bound_in.push(bound);
        self.quantified_in.push(quantified);
        self.ids.insert(node, t);
        t
    }

    // Leaves.

    pub(crate) fn var(&mut self, name: &str, sort: Sort) -> T {
        let id = self.vars.len() as u32;
        let name = name.replace(|c: char| !c.is_ascii_alphanumeric() && c != '_', "_");
        self.vars.push((format!("{name}!{id}"), sort));
        self.mk(Node::Var(id))
    }

    pub(crate) fn bound(&mut self, sort: Sort) -> T {
        let id = self.bounds.len() as u32;
        self.bounds.push(sort);
        self.mk(Node::Bound(id))
    }

    pub(crate) fn uf(&mut self, name: &str, args: Vec<Sort>, result: Sort) -> u32 {
        let id = self.ufs.len() as u32;
        self.ufs.push((format!("{name}!{id}"), args, result));
        id
    }

    pub(crate) fn app(&mut self, f: u32, args: Vec<T>) -> T {
        self.mk(Node::Uf(f, args))
    }

    pub(crate) fn bool(&mut self, b: bool) -> T {
        self.mk(Node::Bool(b))
    }

    pub(crate) fn konst(&mut self, w: u32, v: Word) -> T {
        self.mk(Node::Const(w, fit(w, v)))
    }

    pub(crate) fn word(&mut self, v: Word) -> T {
        self.konst(256, v)
    }

    pub(crate) fn num(&mut self, w: u32, v: u64) -> T {
        self.konst(w, Word::from_u64(v))
    }

    pub(crate) fn zeros(&mut self, sort: Sort) -> T {
        self.mk(Node::Zeros(sort))
    }

    /// The value of a constant, when it is one.
    pub(crate) fn cval(&self, t: T) -> Option<Word> {
        match self.node(t) {
            Node::Const(_, v) => Some(*v),
            _ => None,
        }
    }

    pub(crate) fn cbool(&self, t: T) -> Option<bool> {
        match self.node(t) {
            Node::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// The bytes of a constant whose width is whole bytes, or of a concatenation of them.
    pub(crate) fn const_bytes(&self, t: T) -> Option<Vec<u8>> {
        match self.node(t) {
            Node::Const(w, v) if w % 8 == 0 => {
                let n = (*w / 8) as usize;
                if n > 32 {
                    let mut out = vec![0u8; n - 32];
                    out.extend(v.to_be_bytes());
                    return Some(out);
                }
                Some(v.to_be_bytes()[32 - n..].to_vec())
            }
            Node::Concat(parts) => {
                let mut out = Vec::new();
                for p in parts.clone() {
                    out.extend(self.const_bytes(p)?);
                }
                Some(out)
            }
            _ => None,
        }
    }

    // Booleans.

    pub(crate) fn not(&mut self, a: T) -> T {
        match self.node(a).clone() {
            Node::Bool(b) => self.bool(!b),
            Node::Not(x) => x,
            _ => self.mk(Node::Not(a)),
        }
    }

    pub(crate) fn and(&mut self, a: T, b: T) -> T {
        match (self.cbool(a), self.cbool(b)) {
            (Some(false), _) | (_, Some(false)) => self.bool(false),
            (Some(true), _) => b,
            (_, Some(true)) => a,
            _ if a == b => a,
            _ => {
                if let Node::Not(x) = self.node(a) {
                    if *x == b {
                        return self.bool(false);
                    }
                }
                if let Node::Not(x) = self.node(b) {
                    if *x == a {
                        return self.bool(false);
                    }
                }
                self.mk(Node::Bin(Op::BAnd, a.min(b), a.max(b)))
            }
        }
    }

    pub(crate) fn or(&mut self, a: T, b: T) -> T {
        match (self.cbool(a), self.cbool(b)) {
            (Some(true), _) | (_, Some(true)) => self.bool(true),
            (Some(false), _) => b,
            (_, Some(false)) => a,
            _ if a == b => a,
            _ => {
                if let Node::Not(x) = self.node(a) {
                    if *x == b {
                        return self.bool(true);
                    }
                }
                if let Node::Not(x) = self.node(b) {
                    if *x == a {
                        return self.bool(true);
                    }
                }
                self.mk(Node::Bin(Op::BOr, a.min(b), a.max(b)))
            }
        }
    }

    pub(crate) fn all(&mut self, terms: &[T]) -> T {
        let mut out = self.bool(true);
        for t in terms {
            out = self.and(out, *t);
        }
        out
    }

    pub(crate) fn any(&mut self, terms: &[T]) -> T {
        let mut out = self.bool(false);
        for t in terms {
            out = self.or(out, *t);
        }
        out
    }

    pub(crate) fn implies(&mut self, a: T, b: T) -> T {
        let na = self.not(a);
        self.or(na, b)
    }

    pub(crate) fn forall(&mut self, bound: T, body: T) -> T {
        let Node::Bound(id) = *self.node(bound) else {
            return body;
        };
        if self.cbool(body).is_some() {
            return body;
        }
        self.mk(Node::Forall(id, body))
    }

    /// `t` with each quantifier it holds of more when it holds replaced by what that one says
    /// of `v`: a condition `t` implies.
    pub(crate) fn weaken(&mut self, t: T, v: T) -> T {
        if !self.quantified_in[t as usize] {
            return t;
        }
        match *self.node(t) {
            Node::Forall(..) => self.instance(t, v).unwrap_or(t),
            Node::Bin(Op::BAnd, a, b) => {
                let (a, b) = (self.weaken(a, v), self.weaken(b, v));
                self.and(a, b)
            }
            Node::Bin(Op::BOr, a, b) => {
                let (a, b) = (self.weaken(a, v), self.weaken(b, v));
                self.or(a, b)
            }
            _ => t,
        }
    }

    /// What the quantifier `q` says of `v`: its body with `v` for its variable.
    pub(crate) fn instance(&mut self, q: T, v: T) -> Option<T> {
        let Node::Forall(id, body) = *self.node(q) else {
            return None;
        };
        if self.sort(v) != self.bounds[id as usize] {
            return None;
        }
        Some(self.substitute(body, id, v, &mut HashMap::new()))
    }

    fn substitute(&mut self, t: T, id: u32, v: T, done: &mut HashMap<T, T>) -> T {
        // A quantifier inside counts as closed, though its body may use `id`.
        self.rebuild(
            t,
            &mut |a, t| match *a.node(t) {
                _ if !a.bound_in[t as usize] && !a.quantified_in[t as usize] => Some(t),
                Node::Bound(b) if b == id => Some(v),
                _ => None,
            },
            done,
        )
    }

    /// `t` with each variable `map` names replaced by its term.
    pub(crate) fn rename(&mut self, t: T, map: &HashMap<u32, T>, done: &mut HashMap<T, T>) -> T {
        self.rebuild(
            t,
            &mut |a, t| {
                if let Node::Var(x) = *a.node(t) {
                    return Some(map.get(&x).copied().unwrap_or(t));
                }
                let mapped = a.symbols(t);
                (!mapped
                    .iter()
                    .any(|s| s % 2 == 0 && map.contains_key(&(s / 2))))
                .then_some(t)
            },
            done,
        )
    }

    /// `t` rebuilt bottom up, with each part `swap` gives a term for replaced by it.
    fn rebuild(
        &mut self,
        t: T,
        swap: &mut dyn FnMut(&mut Arena, T) -> Option<T>,
        done: &mut HashMap<T, T>,
    ) -> T {
        if let Some(&r) = done.get(&t) {
            return r;
        }
        if let Some(r) = swap(self, t) {
            done.insert(t, r);
            return r;
        }
        let node = self.nodes[t as usize].clone();
        let mut sub = |a: &mut Arena, x: T| a.rebuild(x, swap, done);
        let r = match node {
            Node::Bool(_) | Node::Const(..) | Node::Var(_) | Node::Bound(_) | Node::Zeros(_) => t,
            Node::Not(a) => {
                let a = sub(self, a);
                self.not(a)
            }
            Node::BvNot(a) => {
                let a = sub(self, a);
                self.bvnot(a)
            }
            Node::Bin(op, a, b) => {
                let (a, b) = (sub(self, a), sub(self, b));
                self.bin(op, a, b)
            }
            Node::Extract(hi, lo, a) => {
                let a = sub(self, a);
                self.extract(hi, lo, a)
            }
            Node::Concat(parts) => {
                let parts: Vec<T> = parts.into_iter().map(|p| sub(self, p)).collect();
                self.concat(&parts)
            }
            Node::ZExt(n, a) => {
                let a = sub(self, a);
                self.zext(n, a)
            }
            Node::SExt(n, a) => {
                let a = sub(self, a);
                self.sext(n, a)
            }
            Node::Ite(c, a, b) => {
                let (c, a, b) = (sub(self, c), sub(self, a), sub(self, b));
                self.ite(c, a, b)
            }
            Node::Select(a, i) => {
                let (a, i) = (sub(self, a), sub(self, i));
                self.select(a, i)
            }
            Node::Store(a, i, x) => {
                let (a, i, x) = (sub(self, a), sub(self, i), sub(self, x));
                self.store(a, i, x)
            }
            Node::Copy(parts) => {
                let [d, at, src, from, len] = parts.map(|p| sub(self, p));
                self.copy(d, at, src, from, len)
            }
            Node::ZeroFrom(a, n) => {
                let (a, n) = (sub(self, a), sub(self, n));
                self.zero_from(a, n)
            }
            Node::Keccak(_, a) => {
                let a = sub(self, a);
                self.keccak(a)
            }
            Node::Uf(f, args) => {
                let args: Vec<T> = args.into_iter().map(|x| sub(self, x)).collect();
                self.app(f, args)
            }
            Node::Forall(b, body) => {
                let body = sub(self, body);
                if self.cbool(body).is_some() {
                    body
                } else {
                    self.mk(Node::Forall(b, body))
                }
            }
        };
        done.insert(t, r);
        r
    }

    pub(crate) fn ite(&mut self, c: T, a: T, b: T) -> T {
        if let Some(c) = self.cbool(c) {
            return if c { a } else { b };
        }
        if a == b {
            return a;
        }
        if self.sort(a) == Sort::Bool {
            match (self.cbool(a), self.cbool(b)) {
                (Some(true), Some(false)) => return c,
                (Some(false), Some(true)) => return self.not(c),
                (Some(true), _) => return self.or(c, b),
                (Some(false), _) => {
                    let nc = self.not(c);
                    return self.and(nc, b);
                }
                (_, Some(false)) => return self.and(c, a),
                (_, Some(true)) => {
                    let nc = self.not(c);
                    return self.or(nc, a);
                }
                _ => {}
            }
        }
        if let Node::Not(inner) = *self.node(c) {
            return self.ite(inner, b, a);
        }
        self.mk(Node::Ite(c, a, b))
    }

    // Bitvectors.

    pub(crate) fn bvnot(&mut self, a: T) -> T {
        let w = self.width(a);
        if let Some(v) = self.cval(a) {
            if w <= 256 {
                return self.konst(w, v.not());
            }
        }
        if let Node::BvNot(x) = *self.node(a) {
            return x;
        }
        self.mk(Node::BvNot(a))
    }

    fn fold(&mut self, op: Op, a: T, b: T) -> Option<T> {
        let w = self.width(a);
        if w > 256 {
            return None;
        }
        let (x, y) = (self.cval(a)?, self.cval(b)?);
        let r = match op {
            Op::Add => x.wrapping_add(y),
            Op::Sub => x.wrapping_sub(y),
            Op::Mul => x.wrapping_mul(y),
            Op::UDiv if !y.is_zero() => x.div(y),
            Op::URem if !y.is_zero() => x.rem(y),
            Op::SDiv if !y.is_zero() && w == 256 => x.sdiv(y),
            Op::SRem if !y.is_zero() && w == 256 => x.smod(y),
            Op::And => x.bitand(y),
            Op::Or => x.bitor(y),
            Op::Xor => x.bitxor(y),
            Op::Shl => match small(y) {
                Some(n) if n < u64::from(w) => x.shl(n as u32),
                _ => Word::from_u64(0),
            },
            Op::LShr => match small(y) {
                Some(n) if n < u64::from(w) => x.shr(n as u32),
                _ => Word::from_u64(0),
            },
            Op::AShr if w == 256 => x.sar(small(y).unwrap_or(256).min(256) as u32),
            Op::Eq => return Some(self.bool(x == y)),
            Op::Ult => return Some(self.bool(x.lt(y))),
            Op::Ule => return Some(self.bool(!y.lt(x))),
            Op::Slt => return Some(self.bool(sext256(w, x).slt(sext256(w, y)))),
            Op::Sle => return Some(self.bool(!sext256(w, y).slt(sext256(w, x)))),
            _ => return None,
        };
        Some(self.konst(w, r))
    }

    fn is_zero(&self, t: T) -> bool {
        self.cval(t).is_some_and(Word::is_zero)
    }

    fn is_ones(&self, t: T) -> bool {
        let w = self.width(t);
        w <= 256 && self.cval(t) == Some(mask(w))
    }

    pub(crate) fn bin(&mut self, op: Op, a: T, b: T) -> T {
        match op {
            Op::Add => self.add(a, b),
            Op::Sub => self.sub(a, b),
            Op::Mul => self.mul(a, b),
            Op::And => self.bvand(a, b),
            Op::Or => self.bvor(a, b),
            Op::Xor => self.bvxor(a, b),
            Op::Shl => self.shl(a, b),
            Op::LShr => self.lshr(a, b),
            Op::AShr => self.ashr(a, b),
            Op::Eq => self.eq(a, b),
            Op::Ult => self.ult(a, b),
            Op::Ule => self.ule(a, b),
            Op::Slt | Op::Sle => {
                if let Some(t) = self.fold(op, a, b) {
                    return t;
                }
                if a == b {
                    return self.bool(op == Op::Sle);
                }
                self.mk(Node::Bin(op, a, b))
            }
            Op::BAnd => self.and(a, b),
            Op::BOr => self.or(a, b),
            Op::UDiv | Op::URem | Op::SDiv | Op::SRem => {
                if let Some(t) = self.fold(op, a, b) {
                    return t;
                }
                let w = self.width(a);
                if let Some(y) = self.cval(b) {
                    if w <= 256
                        && y.bits() > 0
                        && y.wrapping_sub(Word::from_u64(1)).bitand(y).is_zero()
                    {
                        let k = y.bits() - 1;
                        match op {
                            Op::UDiv => {
                                let s = self.num(w, u64::from(k));
                                return self.lshr(a, s);
                            }
                            Op::URem => {
                                let m = self.konst(w, y.wrapping_sub(Word::from_u64(1)));
                                return self.bvand(a, m);
                            }
                            _ => {}
                        }
                    }
                }
                self.mk(Node::Bin(op, a, b))
            }
        }
    }

    pub(crate) fn add(&mut self, a: T, b: T) -> T {
        if let Some(t) = self.fold(Op::Add, a, b) {
            return t;
        }
        // The constant on the right.
        let (a, b) = if self.cval(a).is_some() {
            (b, a)
        } else {
            (a, b)
        };
        if self.is_zero(b) {
            return a;
        }
        if let (Node::Bin(Op::Add, x, c1), Some(_)) = (self.node(a).clone(), self.cval(b)) {
            if self.cval(c1).is_some() {
                let c = self.add(c1, b);
                return self.add(x, c);
            }
        }
        self.mk(Node::Bin(Op::Add, a, b))
    }

    pub(crate) fn sub(&mut self, a: T, b: T) -> T {
        if let Some(t) = self.fold(Op::Sub, a, b) {
            return t;
        }
        if a == b {
            return self.num(self.width(a), 0);
        }
        let w = self.width(a);
        if w <= 256 {
            if let Some(y) = self.cval(b) {
                let negated = self.konst(w, y.wrapping_neg());
                return self.add(a, negated);
            }
        }
        // `(x + c1) - (x + c2)`, and `(x + c) - x`.
        let (xa, ca) = self.base_offset(a);
        let (xb, cb) = self.base_offset(b);
        if xa.is_some() && xa == xb && w == 256 {
            return self.word(ca.wrapping_sub(cb));
        }
        self.mk(Node::Bin(Op::Sub, a, b))
    }

    pub(crate) fn mul(&mut self, a: T, b: T) -> T {
        if let Some(t) = self.fold(Op::Mul, a, b) {
            return t;
        }
        let (a, b) = if self.cval(a).is_some() {
            (b, a)
        } else {
            (a, b)
        };
        if self.is_zero(b) {
            return b;
        }
        if let Some(y) = self.cval(b) {
            if y == Word::from_u64(1) {
                return a;
            }
            if y.wrapping_sub(Word::from_u64(1)).bitand(y).is_zero() && self.width(a) <= 256 {
                let s = self.num(self.width(a), u64::from(y.bits() - 1));
                return self.shl(a, s);
            }
        }
        // By a choice of two constants: a choice of two products.
        for (x, y) in [(a, b), (b, a)] {
            if let Node::Ite(c, k1, k2) = self.node(y).clone() {
                if self.cval(k1).is_some() && self.cval(k2).is_some() {
                    let p1 = self.mul(x, k1);
                    let p2 = self.mul(x, k2);
                    return self.ite(c, p1, p2);
                }
            }
        }
        self.mk(Node::Bin(Op::Mul, a, b))
    }

    pub(crate) fn bvand(&mut self, a: T, b: T) -> T {
        if let Some(t) = self.fold(Op::And, a, b) {
            return t;
        }
        let (a, b) = if self.cval(a).is_some() {
            (b, a)
        } else {
            (a, b)
        };
        if self.is_zero(b) {
            return b;
        }
        if self.is_ones(b) || a == b {
            return a;
        }
        let w = self.width(a);
        if let Some(m) = self.cval(b) {
            if w <= 256 {
                // A mask of low bits, or of high bits.
                let k = m.bits();
                if k > 0 && m == mask(k) {
                    let low = self.extract(k - 1, 0, a);
                    return self.zext(w - k, low);
                }
                let low_zeros = (0..w).find(|i| m.bit(*i)).unwrap_or(w);
                if low_zeros > 0 && fit(w, m) == fit(w, mask(256).shl(low_zeros)) {
                    let high = self.extract(w - 1, low_zeros, a);
                    let zero = self.num(low_zeros, 0);
                    return self.concat(&[high, zero]);
                }
            }
        }
        self.mk(Node::Bin(Op::And, a.min(b), a.max(b)))
    }

    pub(crate) fn bvor(&mut self, a: T, b: T) -> T {
        if let Some(t) = self.fold(Op::Or, a, b) {
            return t;
        }
        let (a, b) = if self.cval(a).is_some() {
            (b, a)
        } else {
            (a, b)
        };
        if self.is_zero(b) || a == b {
            return a;
        }
        if self.is_ones(b) {
            return b;
        }
        self.mk(Node::Bin(Op::Or, a.min(b), a.max(b)))
    }

    pub(crate) fn bvxor(&mut self, a: T, b: T) -> T {
        if let Some(t) = self.fold(Op::Xor, a, b) {
            return t;
        }
        let (a, b) = if self.cval(a).is_some() {
            (b, a)
        } else {
            (a, b)
        };
        if self.is_zero(b) {
            return a;
        }
        if a == b {
            return self.num(self.width(a), 0);
        }
        self.mk(Node::Bin(Op::Xor, a.min(b), a.max(b)))
    }

    /// `a << s`.
    pub(crate) fn shl(&mut self, a: T, s: T) -> T {
        if let Some(t) = self.fold(Op::Shl, a, s) {
            return t;
        }
        let w = self.width(a);
        if let Some(n) = self.cval(s).and_then(small) {
            if n == 0 {
                return a;
            }
            if n >= u64::from(w) {
                return self.num(w, 0);
            }
            let n = n as u32;
            let low = self.extract(w - 1 - n, 0, a);
            let zero = self.num(n, 0);
            return self.concat(&[low, zero]);
        }
        self.mk(Node::Bin(Op::Shl, a, s))
    }

    /// `a >> s`, unsigned.
    pub(crate) fn lshr(&mut self, a: T, s: T) -> T {
        if let Some(t) = self.fold(Op::LShr, a, s) {
            return t;
        }
        let w = self.width(a);
        if let Some(n) = self.cval(s).and_then(small) {
            if n == 0 {
                return a;
            }
            if n >= u64::from(w) {
                return self.num(w, 0);
            }
            let n = n as u32;
            let high = self.extract(w - 1, n, a);
            return self.zext(n, high);
        }
        self.mk(Node::Bin(Op::LShr, a, s))
    }

    pub(crate) fn ashr(&mut self, a: T, s: T) -> T {
        if let Some(t) = self.fold(Op::AShr, a, s) {
            return t;
        }
        let w = self.width(a);
        if let Some(n) = self.cval(s).and_then(small) {
            let n = n.min(u64::from(w - 1)) as u32;
            if n == 0 {
                return a;
            }
            let high = self.extract(w - 1, n, a);
            return self.sext(n, high);
        }
        self.mk(Node::Bin(Op::AShr, a, s))
    }

    pub(crate) fn extract(&mut self, hi: u32, lo: u32, a: T) -> T {
        let w = self.width(a);
        debug_assert!(hi < w && lo <= hi, "extract {hi}..{lo} of {w}");
        if lo == 0 && hi + 1 == w {
            return a;
        }
        let n = hi - lo + 1;
        match self.node(a).clone() {
            Node::Const(_, v) if w <= 256 => return self.konst(n, v.shr(lo)),
            Node::Const(_, v) => {
                // Wider than a word: its value is below 2^256.
                if lo >= 256 {
                    return self.num(n, 0);
                }
                return self.konst(n, v.shr(lo));
            }
            Node::Extract(_, lo2, x) => return self.extract(hi + lo2, lo + lo2, x),
            Node::Concat(parts) => {
                // The parts the range covers, from the most significant.
                let mut out = Vec::new();
                let mut top = w;
                for p in parts {
                    let pw = self.width(p);
                    let (phi, plo) = (top - 1, top - pw);
                    top -= pw;
                    if plo > hi || phi < lo {
                        continue;
                    }
                    let h = hi.min(phi) - plo;
                    let l = lo.max(plo) - plo;
                    out.push(self.extract(h, l, p));
                }
                return self.concat(&out);
            }
            Node::ZExt(_, x) => {
                let xw = self.width(x);
                if hi < xw {
                    return self.extract(hi, lo, x);
                }
                if lo >= xw {
                    return self.num(n, 0);
                }
                let inner = self.extract(xw - 1, lo, x);
                return self.zext(hi + 1 - xw, inner);
            }
            Node::SExt(_, x) => {
                let xw = self.width(x);
                if hi < xw {
                    return self.extract(hi, lo, x);
                }
            }
            Node::Ite(c, x, y) if self.cval(x).is_some() || self.cval(y).is_some() => {
                let ex = self.extract(hi, lo, x);
                let ey = self.extract(hi, lo, y);
                return self.ite(c, ex, ey);
            }
            Node::Bin(op @ (Op::And | Op::Or | Op::Xor), x, y)
                if self.cval(x).is_some() || self.cval(y).is_some() || op == Op::Or =>
            {
                let ex = self.extract(hi, lo, x);
                let ey = self.extract(hi, lo, y);
                return self.bin(op, ex, ey);
            }
            _ => {}
        }
        self.mk(Node::Extract(hi, lo, a))
    }

    pub(crate) fn concat(&mut self, parts: &[T]) -> T {
        let mut flat: Vec<T> = Vec::new();
        for p in parts {
            if self.width(*p) == 0 {
                continue;
            }
            match self.node(*p).clone() {
                Node::Concat(inner) => {
                    for q in inner {
                        self.flatten_into(q, &mut flat);
                    }
                }
                _ => self.flatten_into(*p, &mut flat),
            }
        }
        // Neighbours that join: constants, and pieces of one term.
        let mut out: Vec<T> = Vec::new();
        for p in flat {
            if let Some(&last) = out.last() {
                if let Some(joined) = self.join(last, p) {
                    out.pop();
                    out.push(joined);
                    continue;
                }
            }
            out.push(p);
        }
        match out.len() {
            0 => self.num(0, 0),
            1 => out[0],
            _ => {
                // Leading zeros are a zero extension.
                if self.is_zero(out[0]) {
                    let n = self.width(out[0]);
                    let rest = self.concat(&out[1..]);
                    return self.zext(n, rest);
                }
                self.mk(Node::Concat(out))
            }
        }
    }

    /// A part of a concatenation, with a zero extension as its zeros and what it extends,
    /// so one value has one form.
    fn flatten_into(&mut self, p: T, flat: &mut Vec<T>) {
        match self.node(p).clone() {
            Node::ZExt(n, x) => {
                let zero = self.num(n, 0);
                flat.push(zero);
                match self.node(x).clone() {
                    Node::Concat(inner) => flat.extend(inner),
                    _ => flat.push(x),
                }
            }
            _ => flat.push(p),
        }
    }

    fn join(&mut self, hi: T, lo: T) -> Option<T> {
        let (wh, wl) = (self.width(hi), self.width(lo));
        match (self.node(hi).clone(), self.node(lo).clone()) {
            (Node::Const(_, a), Node::Const(_, b)) if wh + wl <= 256 => {
                Some(self.konst(wh + wl, a.shl(wl).bitor(b)))
            }
            (Node::Extract(h1, l1, x), Node::Extract(h2, l2, y)) if x == y && l1 == h2 + 1 => {
                Some(self.extract(h1, l2, x))
            }
            _ => None,
        }
    }

    pub(crate) fn zext(&mut self, n: u32, a: T) -> T {
        if n == 0 {
            return a;
        }
        let w = self.width(a);
        match self.node(a).clone() {
            Node::Const(_, v) => self.konst(w + n, v),
            Node::ZExt(m, x) => self.zext(n + m, x),
            // `x + y`, widened, is the sum widened less the carry: the solver cancels terms
            // in the wide sum, where it cannot see through a widened wrapping one.
            Node::Bin(Op::Add, x, y) if w <= 256 => {
                let wx = self.zext(n, x);
                let wy = self.zext(n, y);
                let sum = self.add(wx, wy);
                let carry = self.ult(a, x);
                let big = if w < 256 {
                    self.konst(w + n, Word::from_u64(1).shl(w))
                } else {
                    let one = self.num(w + n, 1);
                    let s = self.num(w + n, u64::from(w));
                    self.shl(one, s)
                };
                let zero = self.num(w + n, 0);
                let wrap = self.ite(carry, big, zero);
                self.sub(sum, wrap)
            }
            Node::Bin(Op::Sub, x, y) if w <= 256 => {
                let wx = self.zext(n, x);
                let wy = self.zext(n, y);
                let diff = self.sub(wx, wy);
                let borrow = self.ult(x, y);
                let big = if w < 256 {
                    self.konst(w + n, Word::from_u64(1).shl(w))
                } else {
                    let one = self.num(w + n, 1);
                    let s = self.num(w + n, u64::from(w));
                    self.shl(one, s)
                };
                let zero = self.num(w + n, 0);
                let wrap = self.ite(borrow, big, zero);
                self.add(diff, wrap)
            }
            _ => self.mk(Node::ZExt(n, a)),
        }
    }

    pub(crate) fn sext(&mut self, n: u32, a: T) -> T {
        if n == 0 {
            return a;
        }
        let w = self.width(a);
        match self.node(a).clone() {
            Node::Const(_, v) if w + n <= 256 => self.konst(w + n, sext256(w, v)),
            Node::Const(_, v) if !v.bit(w - 1) => self.konst(w + n, v),
            Node::SExt(m, x) => self.sext(n + m, x),
            Node::ZExt(m, x) if m > 0 => self.zext(n + m, x),
            _ => self.mk(Node::SExt(n, a)),
        }
    }

    /// `a` at width `w`: extended with zeros, or cut to its low bits.
    pub(crate) fn resize(&mut self, a: T, w: u32) -> T {
        let have = self.width(a);
        if have < w {
            self.zext(w - have, a)
        } else if have > w {
            self.extract(w - 1, 0, a)
        } else {
            a
        }
    }

    // Comparisons.

    pub(crate) fn eq(&mut self, a: T, b: T) -> T {
        if a == b {
            return self.bool(true);
        }
        if self.sort(a) == Sort::Bool {
            let nb = self.not(b);
            return match (self.cbool(a), self.cbool(b)) {
                (Some(true), _) => b,
                (Some(false), _) => nb,
                (_, Some(true)) => a,
                (_, Some(false)) => self.not(a),
                _ => self.mk(Node::Bin(Op::Eq, a.min(b), a.max(b))),
            };
        }
        if let Some(t) = self.fold(Op::Eq, a, b) {
            return t;
        }
        let (a, b) = if self.cval(a).is_some() {
            (b, a)
        } else {
            (a, b)
        };
        if let Some(c) = self.cval(b) {
            let w = self.width(a);
            match self.node(a).clone() {
                // A comparison's result tested against a constant.
                Node::Ite(cond, x, y) => {
                    match (self.cval(x), self.cval(y)) {
                        (Some(vx), Some(vy)) => {
                            return match (vx == c, vy == c) {
                                (true, true) => self.bool(true),
                                (true, false) => cond,
                                (false, true) => self.not(cond),
                                (false, false) => self.bool(false),
                            };
                        }
                        // One side a constant other than `c`: the other must be `c`.
                        (Some(vx), None) if vx != c => {
                            let other = self.eq(y, b);
                            let not = self.not(cond);
                            return self.and(not, other);
                        }
                        (None, Some(vy)) if vy != c => {
                            let other = self.eq(x, b);
                            return self.and(cond, other);
                        }
                        (Some(_), None) => {
                            let other = self.eq(y, b);
                            return self.or(cond, other);
                        }
                        (None, Some(_)) => {
                            let other = self.eq(x, b);
                            let not = self.not(cond);
                            return self.or(not, other);
                        }
                        _ => {}
                    }
                }
                // `(x * c) / x = c`, a product's check that it does not wrap.
                Node::Bin(Op::UDiv, prod, x)
                    if w <= 256 && !c.is_zero() && self.mul(x, b) == prod =>
                {
                    let zero = self.num(w, 0);
                    let is_zero = self.eq(x, zero);
                    let nonzero = self.not(is_zero);
                    let max = fit(w, Word::from_u64(0).not());
                    let limit = self.konst(w, max.div(c));
                    let fits = self.ule(x, limit);
                    return self.and(nonzero, fits);
                }
                Node::ZExt(n, x) => {
                    let xw = w - n;
                    if c.bits() > xw {
                        return self.bool(false);
                    }
                    let cx = self.konst(xw, c);
                    return self.eq(x, cx);
                }
                Node::Concat(parts) if w <= 256 => {
                    let mut top = w;
                    let mut eqs = Vec::new();
                    for p in parts {
                        let pw = self.width(p);
                        top -= pw;
                        let piece = self.konst(pw, c.shr(top));
                        eqs.push(self.eq(p, piece));
                    }
                    return self.all(&eqs);
                }
                Node::Bin(Op::Add, x, k) if w == 256 => {
                    if let Some(k) = self.cval(k) {
                        let target = self.word(c.wrapping_sub(k));
                        return self.eq(x, target);
                    }
                }
                Node::BvNot(x) if w <= 256 => {
                    let target = self.konst(w, c.not());
                    return self.eq(x, target);
                }
                // A difference of zero, as the code tests two words equal.
                Node::Bin(Op::Sub, x, y) if c.is_zero() => return self.eq(x, y),
                // Nothing set in either.
                Node::Bin(Op::Or, x, y) if c.is_zero() => {
                    let zero = self.num(w, 0);
                    let ex = self.eq(x, zero);
                    let ey = self.eq(y, zero);
                    return self.and(ex, ey);
                }
                _ => {}
            }
        }
        if self.width(a) == 256 {
            match self.distinct(a, b) {
                Some(true) => return self.bool(false),
                Some(false) => return self.bool(true),
                None => {}
            }
            if let Some(t) = self.hash_eq(a, b) {
                return t;
            }
        }
        if let (Node::ZExt(n, x), Node::ZExt(m, y)) = (self.node(a).clone(), self.node(b).clone()) {
            if n == m {
                return self.eq(x, y);
            }
        }
        // `x * c / c = x`, the check that a product by a constant does not wrap, is
        // `x <= max / c`.
        for (x, q) in [(a, b), (b, a)] {
            if let Some(t) = self.no_wrap(x, q) {
                return t;
            }
        }
        self.mk(Node::Bin(Op::Eq, a.min(b), a.max(b)))
    }

    /// `x = (x * c) / c` for a constant `c` other than zero, as a bound on `x`.
    fn no_wrap(&mut self, x: T, q: T) -> Option<T> {
        let w = self.width(x);
        if w > 256 {
            return None;
        }
        let Node::Bin(Op::UDiv, prod, c) = self.node(q).clone() else {
            return None;
        };
        let k = self.cval(c).filter(|k| !k.is_zero())?;
        let Node::Bin(Op::Mul, u, v) = self.node(prod).clone() else {
            return None;
        };
        if !(u == x && v == c || v == x && u == c) {
            return None;
        }
        let max = fit(w, Word::from_u64(0).not());
        let limit = self.konst(w, max.div(k));
        Some(self.ule(x, limit))
    }

    pub(crate) fn ult(&mut self, a: T, b: T) -> T {
        if let Some(t) = self.fold(Op::Ult, a, b) {
            return t;
        }
        if a == b || self.is_zero(b) || self.is_ones(a) {
            return self.bool(false);
        }
        if self.is_zero(a) {
            let zero = a;
            let e = self.eq(b, zero);
            return self.not(e);
        }
        if let (Some((_, ahi)), Some((blo, _))) = (self.span(a), self.span(b)) {
            if ahi < blo {
                return self.bool(true);
            }
        }
        if let (Some((alo, _)), Some((_, bhi))) = (self.span(a), self.span(b)) {
            if alo >= bhi {
                return self.bool(false);
            }
        }
        // `x + c1 < x + c2`, where neither wraps.
        let (xa, ca) = self.base_offset(a);
        let (xb, cb) = self.base_offset(b);
        if let (Some(x), true) = (xa, xa == xb) {
            if let (Some(ca), Some(cb), Some(_)) = (small(ca), small(cb), self.span(x)) {
                return self.bool(ca < cb);
            }
        }
        // Both extended with zeros alike.
        if let (Node::ZExt(n, x), Node::ZExt(m, y)) = (self.node(a).clone(), self.node(b).clone()) {
            if n == m {
                return self.ult(x, y);
            }
        }
        if let (Node::ZExt(_, x), Some(c)) = (self.node(a).clone(), self.cval(b)) {
            let xw = self.width(x);
            if self.width(a) <= 256 {
                if c.bits() > xw {
                    return self.bool(true);
                }
                let cx = self.konst(xw, c);
                return self.ult(x, cx);
            }
        }
        if let (Some(c), Node::ZExt(_, y)) = (self.cval(a), self.node(b).clone()) {
            let yw = self.width(y);
            if self.width(b) <= 256 {
                if c.bits() > yw {
                    return self.bool(false);
                }
                let cy = self.konst(yw, c);
                return self.ult(cy, y);
            }
        }
        // `c < x` for an `x` whose low bits are zeros that span more than `c`: `x` is a
        // multiple of them, so above `c` exactly when it is not zero, as an offset into a
        // list of words is below the list's length in bytes.
        if let (Some(c), Node::Concat(parts)) = (self.cval(a), self.node(b).clone()) {
            let low = parts.last().copied();
            if let Some(low) = low.filter(|&l| self.cval(l).is_some_and(|v| v.is_zero())) {
                if c.bits() <= self.width(low) {
                    let w = self.width(b);
                    let zero = self.num(w, 0);
                    let e = self.eq(b, zero);
                    return self.not(e);
                }
            }
        }
        self.mk(Node::Bin(Op::Ult, a, b))
    }

    pub(crate) fn ule(&mut self, a: T, b: T) -> T {
        if let Some(t) = self.fold(Op::Ule, a, b) {
            return t;
        }
        if a == b || self.is_zero(a) || self.is_ones(b) {
            return self.bool(true);
        }
        let lt = self.ult(b, a);
        self.not(lt)
    }

    pub(crate) fn slt(&mut self, a: T, b: T) -> T {
        self.bin(Op::Slt, a, b)
    }

    pub(crate) fn sle(&mut self, a: T, b: T) -> T {
        self.bin(Op::Sle, a, b)
    }

    // Arrays.

    pub(crate) fn select(&mut self, arr: T, i: T) -> T {
        let mut a = arr;
        // Past the writes that are surely elsewhere.
        for _ in 0..4096 {
            match self.node(a).clone() {
                Node::Store(inner, j, v) => {
                    if i == j {
                        return v;
                    }
                    match self.distinct(i, j) {
                        Some(true) => a = inner,
                        Some(false) => return v,
                        None if self.hashed(i) && self.hashed(j) => {
                            // Two slots of maps: the same exactly when their keys are.
                            let same = self.eq(i, j);
                            if self.cbool(same).is_none() {
                                let rest = self.select(inner, i);
                                return self.ite(same, v, rest);
                            }
                            a = if self.cbool(same) == Some(true) {
                                return v;
                            } else {
                                inner
                            };
                        }
                        None => break,
                    }
                }
                Node::Zeros(sort) => {
                    return match sort {
                        Sort::Bytes => self.num(8, 0),
                        _ => self.num(256, 0),
                    };
                }
                Node::Var(_) => match self.frames.get(&a).cloned() {
                    Some((before, written)) if !written.all => match self.root(i) {
                        Some(r) if !written.roots.contains(&r) => a = before,
                        _ => break,
                    },
                    _ => break,
                },
                Node::ZeroFrom(inner, n) => {
                    let inside = self.ult(i, n);
                    let v = self.select(inner, i);
                    let zero = self.num(8, 0);
                    return self.ite(inside, v, zero);
                }
                Node::Copy([dst, at, src, from, len]) => {
                    let off = self.sub(i, at);
                    // Every copy is shorter than 2^32 bytes, as the path that made it says.
                    if self.cval(off).is_some_and(|o| o.bits() > 32) {
                        a = dst;
                        continue;
                    }
                    let inside = self.ult(off, len);
                    match self.cbool(inside) {
                        Some(true) => {
                            let k = self.add(from, off);
                            return self.select(src, k);
                        }
                        Some(false) => a = dst,
                        // Onto nothing, as a call's input is: zero past the copy.
                        None if matches!(self.node(dst), Node::Zeros(_)) => {
                            let k = self.add(from, off);
                            let copied = self.select(src, k);
                            let zero = self.num(8, 0);
                            return self.ite(inside, copied, zero);
                        }
                        // A choice between the two reads, which the solver settles without
                        // reasoning about whole arrays.
                        None if self.through < SPLIT_COPIES => {
                            self.through += 1;
                            let k = self.add(from, off);
                            let copied = self.select(src, k);
                            let under = self.select(dst, i);
                            self.through -= 1;
                            return self.ite(inside, copied, under);
                        }
                        None => break,
                    }
                }
                _ => break,
            }
        }
        self.mk(Node::Select(a, i))
    }

    pub(crate) fn store(&mut self, arr: T, i: T, v: T) -> T {
        if let Node::Store(inner, j, _) = *self.node(arr) {
            if i == j {
                return self.store(inner, i, v);
            }
        }
        self.mk(Node::Store(arr, i, v))
    }

    pub(crate) fn copy(&mut self, dst: T, at: T, src: T, from: T, len: T) -> T {
        if self.is_zero(len) {
            return dst;
        }
        self.mk(Node::Copy([dst, at, src, from, len]))
    }

    pub(crate) fn zero_from(&mut self, arr: T, n: T) -> T {
        self.mk(Node::ZeroFrom(arr, n))
    }

    // Keccak.

    /// The hash of `input`, whose width is `8 * n`: its value when the bytes are known,
    /// and otherwise an application of the hash function, with what the assumptions say
    /// about it.
    pub(crate) fn keccak(&mut self, input: T) -> T {
        let n = self.width(input) / 8;
        if let Some(bytes) = self.const_bytes(input) {
            let h = Word::from_be_bytes(crate::keccak::keccak256(&bytes));
            if !self.origins.contains_key(&h) {
                // The function maps these bytes to `h`.
                let y = self.bytes_const(&bytes);
                let raw = self.mk(Node::Keccak(n, y));
                let c = self.word(h);
                let def = self.mk(Node::Bin(Op::Eq, raw, c));
                self.facts.push(def);
                self.origins.insert(h, bytes);
                self.origin_axioms(h);
            }
            return self.word(h);
        }
        let fresh = !self.ids.contains_key(&Node::Keccak(n, input));
        let t = self.mk(Node::Keccak(n, input));
        if self.has_bound(t) {
            self.quantified_lens.insert(n);
            self.inverse_fn(n);
        } else if fresh {
            self.app_axioms(t);
        }
        t
    }

    /// `a` and `b` are far apart: neither is within `2^FAR_BITS` above the other.
    pub(crate) fn far(&mut self, a: T, b: T) -> T {
        let m = self.word(Word::from_u64(1).shl(FAR_BITS));
        let d1 = self.sub(a, b);
        let d2 = self.sub(b, a);
        let f1 = self.ule(m, d1);
        let f2 = self.ule(m, d2);
        self.and(f1, f2)
    }

    /// The inverse of the hash of `n` bytes.
    pub(crate) fn inverse_fn(&mut self, n: u32) -> u32 {
        if let Some(&f) = self.inverses.get(&n) {
            return f;
        }
        let f = self.uf(
            &format!("keccak{n}_inv"),
            vec![Sort::Bv(256)],
            Sort::Bv(8 * n),
        );
        self.inverses.insert(n, f);
        f
    }

    fn inverse(&mut self, n: u32, t: T) -> T {
        let f = self.inverse_fn(n);
        self.app(f, vec![t])
    }

    fn app_axioms(&mut self, t: T) {
        let Node::Keccak(n, x) = *self.node(t) else {
            return;
        };
        let inv = self.inverse(n, t);
        let back = self.eq(inv, x);
        self.facts.push(back);
        let fixed: Vec<Word> = self.fixed.iter().copied().collect();
        for f in fixed {
            let c = self.word(f);
            let far = self.far(t, c);
            self.facts.push(far);
        }
        let others: Vec<T> = self.apps.clone();
        for other in others {
            let Node::Keccak(m, y) = *self.node(other) else {
                continue;
            };
            let far = self.far(t, other);
            if m == n {
                let same = self.eq(x, y);
                let fact = self.or(same, far);
                self.facts.push(fact);
            } else {
                self.facts.push(far);
            }
        }
        let origins: Vec<(Word, Vec<u8>)> =
            self.origins.iter().map(|(h, b)| (*h, b.clone())).collect();
        for (h, bytes) in origins {
            self.origin_fact(t, h, &bytes);
        }
        self.apps.push(t);
    }

    fn origin_axioms(&mut self, h: Word) {
        let bytes = self.origins[&h].clone();
        let apps = self.apps.clone();
        for t in apps {
            self.origin_fact(t, h, &bytes);
        }
    }

    /// What a hash of unknown bytes, `t`, and a hash of known ones, `h`, say together: the
    /// function maps those bytes to `h`, and `t` is `h` exactly when its bytes are those.
    fn origin_fact(&mut self, t: T, h: Word, bytes: &[u8]) {
        let Node::Keccak(n, x) = *self.node(t) else {
            return;
        };
        let c = self.word(h);
        let far = self.far(t, c);
        if bytes.len() as u32 != n {
            self.facts.push(far);
            return;
        }
        let y = self.bytes_const(bytes);
        let same = self.eq(x, y);
        let fact = self.or(same, far);
        self.facts.push(fact);
    }

    /// A constant of the given bytes, of any length.
    pub(crate) fn bytes_const(&mut self, bytes: &[u8]) -> T {
        let parts: Vec<T> = bytes
            .chunks(32)
            .map(|chunk| {
                let mut b = [0u8; 32];
                b[32 - chunk.len()..].copy_from_slice(chunk);
                self.konst(8 * chunk.len() as u32, Word::from_be_bytes(b))
            })
            .collect();
        self.concat(&parts)
    }

    /// A slot the layout fixes: no hash comes near it.
    pub(crate) fn add_fixed(&mut self, f: Word) {
        if self.origins.contains_key(&f) || !self.fixed.insert(f) {
            return;
        }
        let c = self.word(f);
        for t in self.apps.clone() {
            let far = self.far(t, c);
            self.facts.push(far);
        }
    }

    /// A term and a constant offset added to it: `x + c` as `(Some(x), c)`, a constant as
    /// `(None, c)`.
    pub(crate) fn base_offset(&self, t: T) -> (Option<T>, Word) {
        match self.node(t) {
            Node::Const(256, v) => (None, *v),
            Node::Bin(Op::Add, x, c) => match self.cval(*c) {
                Some(v) if self.width(t) == 256 => (Some(*x), v),
                _ => (Some(t), Word::from_u64(0)),
            },
            _ => (Some(t), Word::from_u64(0)),
        }
    }

    /// The slot the layout fixes that a storage slot is under: the slot itself, or the map
    /// or string whose entry or data it is, the outermost of nested maps. Slots under
    /// different roots differ, by the keccak assumptions. `None` when the shape does not say.
    pub(crate) fn root(&mut self, slot: T) -> Option<Word> {
        match self.base_offset(slot) {
            (None, c) => {
                if self.fixed.contains(&c) && !self.origins.contains_key(&c) {
                    return Some(c);
                }
                let bytes = self
                    .origins
                    .iter()
                    .find(|(h, _)| c.wrapping_sub(**h).bits() <= 32)
                    .map(|(_, b)| b.clone())?;
                let under = match bytes.len() {
                    32 => Word::from_be_bytes(bytes.try_into().ok()?),
                    64 => Word::from_be_bytes(bytes[32..].try_into().ok()?),
                    _ => return None,
                };
                let under = self.word(under);
                self.root(under)
            }
            (Some(x), off) if off.bits() <= 32 => match self.node(x).clone() {
                Node::Keccak(64, input) => {
                    let lo = self.extract(255, 0, input);
                    self.root(lo)
                }
                Node::Keccak(32, input) => self.root(input),
                _ => None,
            },
            _ => None,
        }
    }

    /// Whether a word is a constant, or a hash with a small offset: a slot of fixed storage
    /// or of a map.
    fn hashed(&self, t: T) -> bool {
        match self.base_offset(t) {
            (None, _) => true,
            (Some(x), c) => matches!(self.node(x), Node::Keccak(..)) && near_zero(c),
        }
    }

    /// `a = b` for hashes, by the assumption that the hash of `n` bytes is one to one, and
    /// far from every other: the hashes, plus offsets, are equal when the bytes are and the
    /// offsets are.
    fn hash_eq(&mut self, a: T, b: T) -> Option<T> {
        let (xa, ca) = self.base_offset(a);
        let (xb, cb) = self.base_offset(b);
        let shape = |s: &Self, x: Option<T>| match x.map(|x| s.node(x).clone()) {
            Some(Node::Keccak(n, input)) => Some((n, input)),
            _ => None,
        };
        match (shape(self, xa), shape(self, xb)) {
            (Some((n, x)), Some((m, y))) if n == m => {
                if ca == cb {
                    Some(self.eq(x, y))
                } else if near_zero(ca.wrapping_sub(cb)) {
                    Some(self.bool(false))
                } else {
                    None
                }
            }
            (Some((n, x)), None) | (None, Some((n, x))) => {
                let (k, c) = if xa.is_some() { (ca, cb) } else { (cb, ca) };
                if xa.is_some() == xb.is_some() {
                    return None;
                }
                let bytes = self.origins.get(&c.wrapping_sub(k))?.clone();
                (bytes.len() as u32 == n).then(|| {
                    let y = self.bytes_const(&bytes);
                    self.eq(x, y)
                })
            }
            _ => None,
        }
    }

    /// Whether two words surely differ, or are surely equal, by their shapes and the
    /// keccak assumptions; `None` when only a solver can tell.
    pub(crate) fn distinct(&self, a: T, b: T) -> Option<bool> {
        if a == b {
            return Some(false);
        }
        if self.width(a) != 256 {
            return match (self.cval(a), self.cval(b)) {
                (Some(x), Some(y)) => Some(x != y),
                _ => None,
            };
        }
        if let (Some((alo, ahi)), Some((blo, bhi))) = (self.span(a), self.span(b)) {
            if ahi < blo || bhi < alo {
                return Some(true);
            }
        }
        let (xa, ca) = self.base_offset(a);
        let (xb, cb) = self.base_offset(b);
        match (xa, xb) {
            (None, None) => Some(ca != cb),
            (Some(x), Some(y)) if x == y => Some(ca != cb),
            (Some(x), Some(y)) => {
                let (Node::Keccak(n, _), Node::Keccak(m, _)) = (self.node(x), self.node(y)) else {
                    return None;
                };
                (n != m && near_zero(ca.wrapping_sub(cb))).then_some(true)
            }
            (Some(x), None) | (None, Some(x)) => {
                let (k, c) = if xa.is_some() { (ca, cb) } else { (cb, ca) };
                let Node::Keccak(..) = self.node(x) else {
                    return None;
                };
                // `hash + k = c`: `c - k` is near the fixed slot `c` itself.
                (self.fixed.contains(&c) && !self.origins.contains_key(&c) && near_zero(k))
                    .then_some(true)
            }
        }
    }
}

/// `v` when it fits in 64 bits.
pub(crate) fn small(v: Word) -> Option<u64> {
    (v.0[1] == 0 && v.0[2] == 0 && v.0[3] == 0).then_some(v.0[0])
}

/// Whether a word, read as a signed offset, is within `2^FAR_BITS` of zero.
fn near_zero(v: Word) -> bool {
    v.bits() <= FAR_BITS || v.wrapping_neg().bits() <= FAR_BITS
}

/// A word in decimal.
pub(crate) fn dec(w: Word) -> String {
    big_dec(&w.to_be_bytes())
}

/// Big-endian bytes, as a decimal number.
pub(crate) fn big_dec(bytes: &[u8]) -> String {
    let mut digits: Vec<u32> = vec![0];
    for &byte in bytes {
        let mut carry = u64::from(byte);
        for d in digits.iter_mut() {
            let v = u64::from(*d) * 256 + carry;
            *d = (v % 1_000_000_000) as u32;
            carry = v / 1_000_000_000;
        }
        while carry > 0 {
            digits.push((carry % 1_000_000_000) as u32);
            carry /= 1_000_000_000;
        }
    }
    let mut out = digits.last().map(|d| d.to_string()).unwrap_or_default();
    for d in digits.iter().rev().skip(1) {
        out.push_str(&format!("{d:09}"));
    }
    out
}

/// The text of a constant of width `w`.
pub(crate) fn const_text(w: u32, v: Word) -> String {
    if w.is_multiple_of(4) && w <= 256 {
        let hex: String = v.to_be_bytes().iter().map(|b| format!("{b:02x}")).collect();
        format!("#x{}", &hex[64 - (w / 4) as usize..])
    } else {
        format!("(_ bv{} {w})", dec(v))
    }
}

/// Prints terms, naming each shared one once with `define-fun`; the session sends what
/// it prints to the solver.
pub(crate) struct Printer {
    defined: Vec<bool>,
    declared: Vec<bool>,
    declared_ufs: Vec<bool>,
    keccak_lens: BTreeSet<u32>,
}

impl Printer {
    pub(crate) fn new() -> Printer {
        Printer {
            defined: Vec::new(),
            declared: Vec::new(),
            declared_ufs: Vec::new(),
            keccak_lens: BTreeSet::new(),
        }
    }

    fn atomic(a: &Arena, t: T) -> bool {
        matches!(
            a.node(t),
            Node::Bool(_) | Node::Const(..) | Node::Var(_) | Node::Bound(_)
        )
    }

    /// How `t` is written, after `out` defines what it uses.
    pub(crate) fn term(&mut self, a: &Arena, t: T, out: &mut String) -> String {
        if self.defined.len() < a.len() {
            self.defined.resize(a.len(), false);
        }
        // Define what `t` uses, children first, without recursion.
        let mut stack = vec![(t, false)];
        while let Some((u, ready)) = stack.pop() {
            if self.defined[u as usize] {
                continue;
            }
            if ready {
                self.declare_for(a, u, out);
                if !Printer::atomic(a, u) && !a.has_bound(u) {
                    let text = self.shallow(a, u, out);
                    out.push_str(&format!(
                        "(define-fun t{u} () {} {text})\n",
                        a.sort(u).smt()
                    ));
                }
                self.defined[u as usize] = true;
                continue;
            }
            stack.push((u, true));
            for c in a.kids(u) {
                if !self.defined[c as usize] {
                    stack.push((c, false));
                }
            }
        }
        self.reference(a, t, out)
    }

    fn reference(&mut self, a: &Arena, t: T, out: &mut String) -> String {
        if Printer::atomic(a, t) {
            return self.leaf(a, t);
        }
        if a.has_bound(t) {
            return self.shallow(a, t, out);
        }
        format!("t{t}")
    }

    fn leaf(&self, a: &Arena, t: T) -> String {
        match a.node(t) {
            Node::Bool(b) => b.to_string(),
            Node::Const(w, v) => const_text(*w, *v),
            Node::Var(v) => a.vars[*v as usize].0.clone(),
            Node::Bound(b) => format!("b!{b}"),
            _ => unreachable!(),
        }
    }

    fn declare_for(&mut self, a: &Arena, t: T, out: &mut String) {
        match a.node(t) {
            Node::Var(v) => {
                let v = *v as usize;
                if self.declared.len() <= v {
                    self.declared.resize(v + 1, false);
                }
                if !self.declared[v] {
                    self.declared[v] = true;
                    let (name, sort) = &a.vars[v];
                    out.push_str(&format!("(declare-const {name} {})\n", sort.smt()));
                }
            }
            Node::Uf(f, _) => self.declare_uf(a, *f, out),
            Node::Keccak(n, _) => self.declare_keccak(*n, out),
            _ => {}
        }
    }

    fn declare_uf(&mut self, a: &Arena, f: u32, out: &mut String) {
        let f = f as usize;
        if self.declared_ufs.len() <= f {
            self.declared_ufs.resize(f + 1, false);
        }
        if !self.declared_ufs[f] {
            self.declared_ufs[f] = true;
            let (name, args, result) = &a.ufs[f];
            let args: Vec<String> = args.iter().map(|s| s.smt()).collect();
            out.push_str(&format!(
                "(declare-fun {name} ({}) {})\n",
                args.join(" "),
                result.smt()
            ));
        }
    }

    pub(crate) fn declare_keccak(&mut self, n: u32, out: &mut String) {
        if self.keccak_lens.insert(n) {
            out.push_str(&format!(
                "(declare-fun keccak{n} ((_ BitVec {})) (_ BitVec 256))\n",
                8 * n
            ));
        }
    }

    /// The node itself, its children by reference.
    fn shallow(&mut self, a: &Arena, t: T, out: &mut String) -> String {
        let node = a.node(t).clone();
        let mut r = |c: T, s: &mut Self| s.reference(a, c, out);
        match node {
            Node::Bool(_) | Node::Const(..) | Node::Var(_) | Node::Bound(_) => self.leaf(a, t),
            Node::Not(x) => format!("(not {})", r(x, self)),
            Node::BvNot(x) => format!("(bvnot {})", r(x, self)),
            Node::Bin(op, x, y) => {
                let name = match op {
                    Op::Add => "bvadd",
                    Op::Sub => "bvsub",
                    Op::Mul => "bvmul",
                    Op::UDiv => "bvudiv",
                    Op::URem => "bvurem",
                    Op::SDiv => "bvsdiv",
                    Op::SRem => "bvsrem",
                    Op::And => "bvand",
                    Op::Or => "bvor",
                    Op::Xor => "bvxor",
                    Op::Shl => "bvshl",
                    Op::LShr => "bvlshr",
                    Op::AShr => "bvashr",
                    Op::Eq => "=",
                    Op::Ult => "bvult",
                    Op::Ule => "bvule",
                    Op::Slt => "bvslt",
                    Op::Sle => "bvsle",
                    Op::BAnd => "and",
                    Op::BOr => "or",
                };
                let (x, y) = (r(x, self), r(y, self));
                format!("({name} {x} {y})")
            }
            Node::Extract(hi, lo, x) => format!("((_ extract {hi} {lo}) {})", r(x, self)),
            Node::Concat(parts) => {
                let parts: Vec<String> = parts.iter().map(|p| r(*p, self)).collect();
                format!("(concat {})", parts.join(" "))
            }
            Node::ZExt(n, x) => format!("((_ zero_extend {n}) {})", r(x, self)),
            Node::SExt(n, x) => format!("((_ sign_extend {n}) {})", r(x, self)),
            Node::Ite(c, x, y) => {
                let (c, x, y) = (r(c, self), r(x, self), r(y, self));
                format!("(ite {c} {x} {y})")
            }
            Node::Select(arr, i) => {
                let (arr, i) = (r(arr, self), r(i, self));
                format!("(select {arr} {i})")
            }
            Node::Store(arr, i, v) => {
                let (arr, i, v) = (r(arr, self), r(i, self), r(v, self));
                format!("(store {arr} {i} {v})")
            }
            Node::Zeros(sort) => match sort {
                Sort::Bytes => "((as const (Array (_ BitVec 256) (_ BitVec 8))) #x00)".to_string(),
                _ => format!(
                    "((as const (Array (_ BitVec 256) (_ BitVec 256))) {})",
                    const_text(256, Word::from_u64(0))
                ),
            },
            Node::Copy([dst, at, src, from, len]) => {
                let (dst, at, src, from, len) = (
                    r(dst, self),
                    r(at, self),
                    r(src, self),
                    r(from, self),
                    r(len, self),
                );
                let i = format!("i!{t}");
                format!(
                    "(lambda (({i} (_ BitVec 256))) (ite (bvult (bvsub {i} {at}) {len}) (select {src} (bvadd {from} (bvsub {i} {at}))) (select {dst} {i})))"
                )
            }
            Node::ZeroFrom(arr, n) => {
                let (arr, n) = (r(arr, self), r(n, self));
                let i = format!("i!{t}");
                format!(
                    "(lambda (({i} (_ BitVec 256))) (ite (bvult {i} {n}) (select {arr} {i}) #x00))"
                )
            }
            Node::Keccak(n, x) => format!("(keccak{n} {})", r(x, self)),
            Node::Uf(f, args) => {
                let name = a.ufs[f as usize].0.clone();
                if args.is_empty() {
                    return name;
                }
                let args: Vec<String> = args.iter().map(|x| r(*x, self)).collect();
                format!("({name} {})", args.join(" "))
            }
            Node::Forall(b, body) => {
                let sort = a.bounds[b as usize].smt();
                format!("(forall ((b!{b} {sort})) {})", r(body, self))
            }
        }
    }

    /// The axioms for hashes inside quantifiers: for each length hashed there, the inverse,
    /// and the distance from each fixed slot. What they use is declared in `out`; the
    /// assertions come back, for the question that needs them.
    pub(crate) fn quantified_axioms(&mut self, a: &Arena, out: &mut String) -> Vec<String> {
        let mut axioms = Vec::new();
        for &n in &a.quantified_lens {
            self.declare_keccak(n, out);
            let Some(&inv) = a.inverses.get(&n) else {
                continue;
            };
            self.declare_uf(a, inv, out);
            let inv_name = a.ufs[inv as usize].0.clone();
            let m = const_text(256, Word::from_u64(1).shl(FAR_BITS));
            let mut far = Vec::new();
            for f in &a.fixed {
                let c = const_text(256, *f);
                far.push(format!(
                    "(bvule {m} (bvsub (keccak{n} x) {c})) (bvule {m} (bvsub {c} (keccak{n} x)))"
                ));
            }
            axioms.push(format!(
                "(assert (forall ((x (_ BitVec {}))) (! (and (= ({inv_name} (keccak{n} x)) x) {}) :pattern ((keccak{n} x)))))\n",
                8 * n,
                far.join(" ")
            ));
        }
        axioms
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn words_from_their_bytes_fold_back() {
        let mut a = Arena::new();
        let x = a.var("x", Sort::Bv(256));
        let bytes: Vec<T> = (0..32)
            .map(|k| a.extract(255 - 8 * k, 248 - 8 * k, x))
            .collect();
        assert_eq!(a.concat(&bytes), x);
        let one = a.word(Word::from_u64(1));
        let zero = a.word(Word::from_u64(0));
        let c = a.var("c", Sort::Bool);
        let flag = a.ite(c, one, zero);
        let tested = a.eq(flag, zero);
        assert_eq!(a.not(tested), c);
        let s = a.num(256, 224);
        let shifted = a.lshr(x, s);
        assert_eq!(a.width(shifted), 256);
        assert!(matches!(a.node(shifted), Node::ZExt(224, _)));
    }

    #[test]
    fn known_hashes_fold_and_writes_elsewhere_are_skipped() {
        let mut a = Arena::new();
        let key = a.word(Word::from_u64(5));
        let slot = a.word(Word::from_u64(1));
        let input = a.concat(&[key, slot]);
        let h = a.keccak(input);
        let mut buf = [0u8; 64];
        buf[31] = 5;
        buf[63] = 1;
        assert_eq!(
            a.cval(h),
            Some(Word::from_be_bytes(crate::keccak::keccak256(&buf)))
        );
        let s = a.var("s", Sort::Words);
        let v = a.word(Word::from_u64(7));
        let zero = a.word(Word::from_u64(0));
        let stored = a.store(s, zero, v);
        let read = a.select(stored, h);
        assert!(matches!(a.node(read), Node::Select(base, _) if *base == s));
        assert_eq!(dec(Word::from_u64(1234)), "1234");
        assert_eq!(big_dec(&[1, 0]), "256");
    }

    #[test]
    fn inner_quantifiers_using_outer_variables_stay_inside_them() {
        let mut a = Arena::new();
        let (i, j) = (a.bound(Sort::Bv(256)), a.bound(Sort::Bv(256)));
        let lt = a.ult(j, i);
        let inner = a.forall(j, lt);
        assert!(a.has_bound(inner));
        let outer = a.forall(i, inner);
        assert!(!a.has_bound(outer));
        let x = a.var("x", Sort::Bv(256));
        let closed = a.instance(outer, x).expect("an instance");
        assert!(!a.has_bound(closed));
    }

    #[test]
    fn renaming_rebuilds_and_differences_of_zero_are_equalities() {
        let mut a = Arena::new();
        let (x, y) = (a.var("x", Sort::Bv(256)), a.var("y", Sort::Bv(256)));
        let one = a.num(256, 1);
        let sum = a.add(x, one);
        let Node::Var(id) = *a.node(x) else {
            unreachable!()
        };
        let two = a.num(256, 2);
        let map = HashMap::from([(id, two)]);
        let renamed = a.rename(sum, &map, &mut HashMap::new());
        assert_eq!(a.cval(renamed), Some(Word::from_u64(3)));
        let diff = a.sub(x, y);
        let zero = a.num(256, 0);
        assert_eq!(a.eq(diff, zero), a.eq(y, x));
        let five = a.num(256, 5);
        let bytes = a.shl(x, five);
        let c = a.num(256, 31);
        let below = a.ult(c, bytes);
        let none = a.eq(bytes, zero);
        assert_eq!(below, a.not(none));
    }
}
