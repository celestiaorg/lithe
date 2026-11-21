//! Builds a function's graph. Constants fold, equal pure values are numbered once, stored
//! words are forwarded to later loads, and conditions known from the branches and asserts
//! above decide the ones below, all as the instructions are added.

use super::*;

/// What a slot is known to be, for telling slots apart.
#[derive(Clone, PartialEq, Eq)]
enum Slot {
    Const(Word),
    /// A hash of these operands, plus an offset.
    Hashed(Vec<V>, Word),
    Unknown,
}

/// What holds where the builder stands and may not hold on another path.
pub(super) struct State {
    stored: Vec<(V, V)>,
    transient: Vec<(V, V)>,
    facts: usize,
    ranges: usize,
    numbered: usize,
}

pub(super) struct Builder {
    pub f: Func,
    pub cur: B,
    /// The source function being lowered.
    pub tag: u32,
    /// Nothing reaches the code being built.
    pub dead: bool,
    numbered: HashMap<(Op, Vec<V>), V>,
    numbered_log: Vec<(Op, Vec<V>)>,
    consts: HashMap<Word, V>,
    /// The constants an instruction pushes, by value.
    held: HashMap<V, Word>,
    /// The functions that load and store through the journal, where storage is read and
    /// written through one: every store waits there for the body's end.
    pub(super) journal: Option<(u32, u32)>,
    envs: HashMap<(u8, u32), V>,
    /// Each slot's word, where it is known.
    stored: Vec<(V, V)>,
    transient: Vec<(V, V)>,
    /// Stores not yet made, so that a query after them still finds storage as the
    /// transition found it. Loads read them back.
    pending: Vec<(V, V)>,
    /// The last store to each slot, where nothing since could have read the slot: its
    /// block and instruction. A second store to the slot makes it dead.
    unread: Vec<(V, B, u32)>,
    /// Conditions and whether they hold.
    facts: Vec<(V, bool)>,
    /// What the conditions that hold say of a value's size: how many low bits it can
    /// have set, on this path.
    ranges: Vec<(V, u16)>,
    /// How many low bits a value can have set.
    bits: Vec<u16>,
    /// Where a value is defined: its block and instruction.
    defs: Vec<(B, u32)>,
    /// Knows nothing of paths or widths: the differential test's reference build.
    plain: bool,
}

const NO_DEF: (B, u32) = (u32::MAX, u32::MAX);
/// A constant whose push is longer than this many bytes is kept on the stack between uses.
const HELD_BYTES: usize = 8;

impl Builder {
    pub(super) fn new(name: &str) -> Builder {
        let mut b = Builder {
            f: Func {
                name: name.to_string(),
                notes: Notes::default(),
                params: Vec::new(),
                ret: None,
                blocks: Vec::new(),
                kinds: Vec::new(),
            },
            cur: 0,
            tag: NO_TAG,
            dead: false,
            numbered: HashMap::new(),
            numbered_log: Vec::new(),
            consts: HashMap::new(),
            held: HashMap::new(),
            journal: None,
            envs: HashMap::new(),
            stored: Vec::new(),
            transient: Vec::new(),
            pending: Vec::new(),
            unread: Vec::new(),
            facts: Vec::new(),
            ranges: Vec::new(),
            bits: Vec::new(),
            defs: Vec::new(),
            plain: plain(),
        };
        b.cur = b.block();
        b
    }

    fn value(&mut self, kind: Kind, bits: u16) -> V {
        self.f.kinds.push(kind);
        self.bits.push(bits);
        self.defs.push(NO_DEF);
        (self.f.kinds.len() - 1) as V
    }

    pub(super) fn param(&mut self, bits: u16) -> V {
        self.value(Kind::Var, bits)
    }

    pub(super) fn block(&mut self) -> B {
        self.f.blocks.push(Block {
            params: Vec::new(),
            insts: Vec::new(),
            term: Term::Open,
            preds: 0,
        });
        (self.f.blocks.len() - 1) as B
    }

    pub(super) fn block_param(&mut self, b: B, bits: u16) -> V {
        let v = self.value(Kind::Var, bits);
        self.f.blocks[b as usize].params.push(v);
        v
    }

    pub(super) fn word(&mut self, w: Word) -> V {
        if let Some(&v) = self.consts.get(&w) {
            return v;
        }
        if asm::encode_push(w).len() > HELD_BYTES {
            let v = self.pure(Op::Const(w), Vec::new(), w.bits() as u16);
            self.held.insert(v, w);
            return v;
        }
        let v = self.value(Kind::Const(w), w.bits() as u16);
        self.consts.insert(w, v);
        v
    }

    /// A constant kept on the stack between its uses whatever its length: one a loop
    /// uses, made before the loop.
    pub(super) fn kept(&mut self, w: Word) -> V {
        let v = self.pure(Op::Const(w), Vec::new(), w.bits() as u16);
        self.held.insert(v, w);
        v
    }

    pub(super) fn num(&mut self, n: u64) -> V {
        self.word(Word::from_u64(n))
    }

    pub(super) fn constant(&self, v: V) -> Option<Word> {
        match self.f.kinds[v as usize] {
            Kind::Const(w) => Some(w),
            _ => self.held.get(&v).copied(),
        }
    }

    pub(super) fn bits(&self, v: V) -> u16 {
        if self.plain && self.constant(v).is_none() {
            return 256;
        }
        let own = self.bits[v as usize];
        self.ranges
            .iter()
            .filter(|(of, _)| *of == v)
            .fold(own, |least, &(_, bits)| least.min(bits))
    }

    /// An operator of no operands, which every use runs again.
    pub(super) fn env(&mut self, op: u8) -> V {
        if let Some(&v) = self.envs.get(&(op, 0)) {
            return v;
        }
        let bits = match op {
            CALLER | ADDRESS | ORIGIN | COINBASE => 160,
            _ => 256,
        };
        let v = self.value(Kind::Env(op), bits);
        self.envs.insert((op, 0), v);
        v
    }

    /// The calldata word at a constant offset.
    pub(super) fn cd_word(&mut self, at: u32) -> V {
        if let Some(&v) = self.envs.get(&(CALLDATALOAD, at)) {
            return v;
        }
        let v = self.value(Kind::CdWord(at), 256);
        self.envs.insert((CALLDATALOAD, at), v);
        v
    }

    /// Says a value has no bits set from `bits` up, as its type or a check ensures.
    pub(super) fn narrow(&mut self, v: V, bits: u16) {
        let at = &mut self.bits[v as usize];
        *at = (*at).min(bits);
    }

    fn def(&self, v: V) -> Option<&Inst> {
        let (b, i) = self.defs[v as usize];
        (b != u32::MAX).then(|| &self.f.blocks[b as usize].insts[i as usize])
    }

    fn evm_def(&self, v: V, op: u8) -> Option<&[V]> {
        self.def(v)
            .filter(|inst| inst.op == Op::Evm(op))
            .map(|inst| inst.args.as_slice())
    }

    fn push(&mut self, op: Op, args: Vec<V>, outs: u8, bits: u16) -> V {
        let out = self.f.kinds.len() as V;
        let at = (
            self.cur,
            self.f.blocks[self.cur as usize].insts.len() as u32,
        );
        for _ in 0..outs {
            let v = self.value(Kind::Var, bits);
            self.defs[v as usize] = at;
        }
        self.f.blocks[self.cur as usize].insts.push(Inst {
            op,
            args,
            out,
            outs,
            tag: self.tag,
        });
        out
    }

    fn pure(&mut self, op: Op, args: Vec<V>, bits: u16) -> V {
        let key = (op, args);
        if let Some(&v) = self.numbered.get(&key) {
            return v;
        }
        let v = self.push(key.0.clone(), key.1.clone(), 1, bits);
        self.numbered_log.push(key.clone());
        self.numbered.insert(key, v);
        v
    }

    /// The value an equal pure instruction above already has.
    fn find(&self, op: u8, args: &[V]) -> Option<V> {
        self.numbered.get(&(Op::Evm(op), args.to_vec())).copied()
    }

    /// Whether a condition is known to hold, or not to.
    pub(super) fn truth(&self, v: V) -> Option<bool> {
        if let Some(w) = self.constant(v) {
            return Some(!w.is_zero());
        }
        self.facts
            .iter()
            .rev()
            .find(|(c, _)| *c == v)
            .map(|&(_, t)| t)
    }

    /// From here on, on this path, the value is not zero, or is zero.
    pub(super) fn assume(&mut self, v: V, holds: bool) {
        if self.plain || self.constant(v).is_some() {
            return;
        }
        self.facts.push((v, holds));
        if let Some(&[x]) = self.evm_def(v, ISZERO) {
            self.assume(x, !holds);
        }
        // A value under another is no wider than it, and one a shift leaves nothing of
        // fits below the shift.
        let Some(inst) = self.def(v) else { return };
        let (Op::Evm(op), &[a, b]) = (&inst.op, inst.args.as_slice()) else {
            return;
        };
        match (*op, holds) {
            (LT, true) | (GT, false) => self.ranges.push((a, self.bits(b))),
            (GT, true) | (LT, false) => self.ranges.push((b, self.bits(a))),
            (SHR, false) => {
                if let Some(k) = self.constant(a).filter(|k| k.bits() <= 8) {
                    self.ranges.push((b, k.0[0] as u16));
                }
            }
            // Both hold where their conjunction does, and neither where their
            // disjunction does not.
            (AND, true) | (OR, false) => {
                self.assume(a, holds);
                self.assume(b, holds);
            }
            _ => {}
        }
    }

    pub(super) fn op1(&mut self, op: u8, a: V) -> V {
        self.evm(op, vec![a])
    }

    pub(super) fn op2(&mut self, op: u8, a: V, b: V) -> V {
        self.evm(op, vec![a, b])
    }

    pub(super) fn is_zero(&mut self, a: V) -> V {
        self.op1(ISZERO, a)
    }

    /// 1 when the value is not zero.
    pub(super) fn as_bool(&mut self, a: V) -> V {
        if self.bits(a) <= 1 {
            return a;
        }
        let z = self.is_zero(a);
        self.is_zero(z)
    }

    /// A pure operator, simplified where its operands allow.
    pub(super) fn evm(&mut self, op: u8, mut args: Vec<V>) -> V {
        let known: Vec<Option<Word>> = args.iter().map(|&a| self.constant(a)).collect();
        let zero = |k: &Option<Word>| k.is_some_and(|w| w.is_zero());
        let one = |k: &Option<Word>| *k == Some(Word::from_u64(1));
        match (op, args.as_slice()) {
            (ISZERO, &[a]) => {
                if let Some(w) = known[0] {
                    return self.num(u64::from(w.is_zero()));
                }
                if let Some(t) = self.truth(a) {
                    return self.num(u64::from(!t));
                }
                if let Some(&[x]) = self.evm_def(a, ISZERO) {
                    if self.bits(x) <= 1 {
                        return x;
                    }
                }
                // Not both is either not, and not either is both not: one test fewer
                // where a side is itself a test for zero.
                for (op, dual) in [(AND, OR), (OR, AND)] {
                    if let Some(&[p, q]) = self.evm_def(a, op) {
                        let flag = self.bits(p) <= 1 && self.bits(q) <= 1;
                        let tests = [p, q].iter().any(|&v| self.evm_def(v, ISZERO).is_some());
                        if flag && tests {
                            let (np, nq) = (self.is_zero(p), self.is_zero(q));
                            return self.op2(dual, np, nq);
                        }
                    }
                }
                let v = self.pure(Op::Evm(ISZERO), args, 1);
                return self.decided(v);
            }
            (NOT, _) => {
                if let Some(w) = known[0] {
                    return self.word(w.not());
                }
                if let Some(&[x]) = self.evm_def(args[0], NOT) {
                    return x;
                }
                return self.pure(Op::Evm(NOT), args, 256);
            }
            (_, &[a, b]) => {
                if let (Some(x), Some(y)) = (known[0], known[1]) {
                    if let Some(w) = asm::fold_binary(op, x, y) {
                        return self.word(w);
                    }
                }
                let (ka, kb) = (&known[0], &known[1]);
                match op {
                    ADD | OR | XOR if zero(ka) => return b,
                    ADD | OR | XOR | SUB if zero(kb) => return a,
                    SUB | XOR if a == b => return self.num(0),
                    MUL | AND if zero(ka) || zero(kb) => return self.num(0),
                    MUL if one(ka) => return b,
                    MUL | DIV if one(kb) => return a,
                    SHL | SHR if zero(ka) => return b,
                    SHR if ka
                        .is_some_and(|k| k.bits() <= 16 && k.0[0] >= u64::from(self.bits(b))) =>
                    {
                        return self.num(0)
                    }
                    AND => {
                        // A mask of low bits the other side cannot exceed.
                        for (mask, x) in [(ka, b), (kb, a)] {
                            if let Some(m) = mask {
                                let k = m.bits();
                                let low = Word::from_u64(1).shl(k).wrapping_sub(Word::from_u64(1));
                                let full = k == 256 && m.not().is_zero();
                                if (full || (k < 256 && *m == low)) && u32::from(self.bits(x)) <= k
                                {
                                    return x;
                                }
                            }
                        }
                        let masked = match (ka, kb) {
                            (Some(m), None) => Some((*m, b)),
                            (None, Some(m)) => Some((*m, a)),
                            _ => None,
                        };
                        if let Some((m, x)) = masked {
                            // Two masks are one; and a mask over an `or` leaves alone the
                            // side whose bits it keeps anyway, so masks of one word gather.
                            if let Some(&[p, q]) = self.evm_def(x, AND) {
                                for (c, rest) in [(p, q), (q, p)] {
                                    if let Some(c) = self.constant(c) {
                                        let both = self.word(c.bitand(m));
                                        return self.op2(AND, rest, both);
                                    }
                                }
                            }
                            if let Some(&[p, q]) = self.evm_def(x, OR) {
                                for (kept, rest) in [(q, p), (p, q)] {
                                    let n = u32::from(self.bits(kept));
                                    let low =
                                        Word::from_u64(1).shl(n).wrapping_sub(Word::from_u64(1));
                                    if n < 256 && m.bitand(low) == low {
                                        let mask = self.word(m);
                                        let masked = self.op2(AND, rest, mask);
                                        return self.op2(OR, masked, kept);
                                    }
                                }
                            }
                        }
                    }
                    EQ if a == b => return self.num(1),
                    EQ if zero(ka) => return self.is_zero(b),
                    EQ if zero(kb) => return self.is_zero(a),
                    LT | GT | SLT | SGT if a == b => return self.num(0),
                    // `x > 0` and `0 < x` ask only whether `x` is zero.
                    GT if zero(kb) => return self.as_bool(a),
                    LT if zero(ka) => return self.as_bool(b),
                    LT if zero(kb) => return self.num(0),
                    GT if zero(ka) => return self.num(0),
                    _ => {}
                }
                if matches!(op, ADD | MUL | AND | OR | XOR | EQ) && a > b {
                    args.swap(0, 1);
                }
                let (a, b) = (args[0], args[1]);
                let (wa, wb) = (self.bits(a), self.bits(b));
                let bits = match op {
                    LT | GT | SLT | SGT | EQ => 1,
                    AND => wa.min(wb),
                    OR | XOR => wa.max(wb),
                    ADD => (wa.max(wb) + 1).min(256),
                    MUL => (wa + wb).min(256),
                    // A constant divisor takes off the bits below its top one.
                    DIV => match self.constant(b) {
                        Some(d) if !d.is_zero() => wa.saturating_sub(d.bits() as u16 - 1),
                        _ => wa,
                    },
                    // Less than a constant divisor.
                    MOD => match self.constant(b) {
                        Some(m) if !m.is_zero() => m.wrapping_sub(Word::from_u64(1)).bits() as u16,
                        _ => wb,
                    },
                    SUB => 256,
                    // `[shift, value]`
                    SHR => match self.constant(a) {
                        Some(k) if k.bits() <= 16 => wb.saturating_sub(k.0[0] as u16),
                        _ => wb,
                    },
                    SHL => match self.constant(a) {
                        Some(k) if k.bits() <= 16 => {
                            (u32::from(wb) + k.0[0] as u32).min(256) as u16
                        }
                        _ => 256,
                    },
                    _ => 256,
                };
                let v = self.pure(Op::Evm(op), args, bits);
                return if bits == 1 { self.decided(v) } else { v };
            }
            _ => {}
        }
        self.pure(Op::Evm(op), args, 256)
    }

    /// A condition, or the constant the facts here make it.
    fn decided(&mut self, v: V) -> V {
        match self.facts.iter().rev().find(|(c, _)| *c == v) {
            Some(&(_, t)) => self.num(u64::from(t)),
            None => v,
        }
    }

    /// Whether `a >= b` is known here, both unsigned.
    fn at_least(&self, a: V, b: V) -> bool {
        if a == b {
            return true;
        }
        if let (Some(x), Some(y)) = (self.constant(a), self.constant(b)) {
            return !x.lt(y);
        }
        // `LT [x, y]` is `x < y`; `GT [x, y]` is `x > y`.
        let known = |op: u8, x: V, y: V| self.find(op, &[x, y]).and_then(|c| self.truth(c));
        known(LT, a, b) == Some(false)
            || known(GT, b, a) == Some(false)
            || known(LT, b, a) == Some(true)
            || known(GT, a, b) == Some(true)
            // What is not zero is at least one.
            || (self.constant(b) == Some(Word::from_u64(1)) && self.truth(a) == Some(true))
    }

    /// The pairs `(x, y)` with `x <= y` known here by a comparison that went one way.
    fn orders(&self) -> impl Iterator<Item = (V, V)> + '_ {
        self.facts.iter().filter_map(|&(c, holds)| {
            let inst = self.def(c)?;
            let (Op::Evm(op), &[p, q]) = (&inst.op, inst.args.as_slice()) else {
                return None;
            };
            match (*op, holds) {
                (GT, false) | (LT, true) => Some((p, q)),
                (LT, false) | (GT, true) => Some((q, p)),
                _ => None,
            }
        })
    }

    /// Whether `a + b` is known to stay under `2 ** limit`: one of them is at most what a
    /// word of that width has left once the other is taken from it, by a subtraction that
    /// did not wrap. Becomes the width of that word.
    fn sum_fits(&self, a: V, b: V, limit: u16) -> Option<u16> {
        self.orders().find_map(|(small, big)| {
            let other = match small {
                x if x == a => b,
                x if x == b => a,
                _ => return None,
            };
            let inst = self.def(big)?;
            let whole = match (&inst.op, inst.args.as_slice()) {
                (Op::Checked(Arith::Sub, _, false), &[whole, taken]) if taken == other => whole,
                (Op::Evm(SUB), &[whole, taken]) if taken == other => {
                    self.at_least(whole, taken).then_some(whole)?
                }
                // All ones less a word.
                (Op::Evm(NOT), &[taken]) if taken == other => return (limit == 256).then_some(256),
                _ => return None,
            };
            Some(self.bits(whole)).filter(|&bits| bits <= limit)
        })
    }

    /// `a op b` in an unsigned type of `bits` bits, checked only where it can fail.
    pub(super) fn checked(&mut self, op: Arith, bits: u16, a: V, b: V) -> V {
        let limit = if bits == 0 { 256 } else { bits };
        let (wa, wb) = (self.bits(a), self.bits(b));
        let folded = match (op, self.constant(a), self.constant(b)) {
            (Arith::Fit, ..) => None,
            (_, Some(x), Some(y)) => {
                let (w, over) = match op {
                    Arith::Add => x.overflowing_add(y),
                    Arith::Sub => (x.wrapping_sub(y), x.lt(y)),
                    Arith::Mul => x.overflowing_mul(y),
                    Arith::Div if !y.is_zero() => (x.div(y), false),
                    Arith::Mod if !y.is_zero() => (x.rem(y), false),
                    _ => (x, true),
                };
                (!over && w.bits() <= u32::from(limit)).then_some(w)
            }
            _ => None,
        };
        if let Some(w) = folded {
            return self.word(w);
        }
        let plain = match op {
            Arith::Add => (wa.max(wb) < limit).then_some(ADD),
            Arith::Sub => self.at_least(a, b).then_some(SUB),
            Arith::Mul => (wa + wb <= limit).then_some(MUL),
            // A divisor is not zero when it is a constant that is not, or when an earlier
            // division by it went through.
            Arith::Div | Arith::Mod => {
                let nonzero =
                    self.constant(b).is_some_and(|w| !w.is_zero()) || self.truth(b) == Some(true);
                nonzero.then_some(if op == Arith::Div { DIV } else { MOD })
            }
            Arith::Fit => {
                if wa <= limit {
                    return a;
                }
                None
            }
        };
        if let (Arith::Add, None, Some(bits)) = (op, plain, self.sum_fits(a, b, limit)) {
            let v = self.op2(ADD, a, b);
            self.ranges.push((v, bits));
            return v;
        }
        if let Some(evm) = plain {
            let fresh = self.f.kinds.len() as V;
            let v = self.op2(evm, a, b);
            // The difference is no wider than what it was taken from, as wide as that is
            // known to be here. A difference from before what is known here was may have
            // wrapped where this is not known, so only this path learns its width.
            if op == Arith::Sub {
                if v >= fresh {
                    self.narrow(v, self.bits[a as usize]);
                }
                self.ranges.push((v, wa));
            }
            return v;
        }
        let args = if op == Arith::Fit {
            vec![a]
        } else {
            vec![a, b]
        };
        let out = match op {
            Arith::Sub | Arith::Div => wa.min(limit),
            Arith::Mod => wb.min(limit),
            _ => limit,
        };
        // Equal checked operations give equal values, and the second cannot fail.
        let v = self.pure(Op::Checked(op, limit, false), args, out);
        if matches!(op, Arith::Div | Arith::Mod) {
            self.assume(b, true);
        }
        v
    }

    /// `a op b` in a signed type of `bits` bits, or `None` where this pipeline has no
    /// checked form of it.
    pub(super) fn checked_signed(&mut self, op: Arith, bits: u16, a: V, b: V) -> Option<V> {
        let limit = if bits == 0 { 256 } else { bits };
        match op {
            Arith::Fit => {
                let fits = |w: Word| limit == 256 || w.sign_extend(u32::from(limit) / 8 - 1) == w;
                if limit == 256 || self.constant(a).is_some_and(fits) {
                    return Some(a);
                }
                Some(self.pure(Op::Checked(op, limit, true), vec![a], 256))
            }
            Arith::Add | Arith::Sub => {
                if let (Some(x), Some(y)) = (self.constant(a), self.constant(b)) {
                    // Overflow is when the sign of `y` and the direction of the result
                    // disagree.
                    let zero = Word::from_u64(0);
                    let (r, over) = if op == Arith::Add {
                        let r = x.wrapping_add(y);
                        (r, y.slt(zero) != r.slt(x))
                    } else {
                        let r = x.wrapping_sub(y);
                        (r, zero.slt(y) != r.slt(x))
                    };
                    let fits = limit == 256 || r.sign_extend(u32::from(limit) / 8 - 1) == r;
                    if !over && fits {
                        return Some(self.word(r));
                    }
                }
                Some(self.pure(Op::Checked(op, limit, true), vec![a, b], 256))
            }
            Arith::Mul if limit <= 128 => {
                Some(self.pure(Op::Checked(op, limit, true), vec![a, b], 256))
            }
            _ => None,
        }
    }

    /// keccak256 of words staged in order.
    pub(super) fn hash_words(&mut self, words: Vec<V>) -> V {
        self.pure(Op::Hash(Enc::words(words.len())), words, 256)
    }

    pub(super) fn hash(&mut self, enc: Enc, args: Vec<V>) -> V {
        // A stored string is read when the hash is taken.
        if enc.parts.contains(&Part::Stored) {
            self.unread.clear();
            return self.push(Op::Hash(enc), args, 1, 256);
        }
        self.pure(Op::Hash(enc), args, 256)
    }

    fn slot(&self, v: V) -> Slot {
        if let Some(w) = self.constant(v) {
            return Slot::Const(w);
        }
        let Some(inst) = self.def(v) else {
            return Slot::Unknown;
        };
        match &inst.op {
            Op::Hash(enc) if enc.fixed() => Slot::Hashed(inst.args.clone(), Word::from_u64(0)),
            Op::Evm(ADD) => {
                let (a, b) = (inst.args[0], inst.args[1]);
                for (x, k) in [(a, b), (b, a)] {
                    if let (Slot::Hashed(args, at), Some(k)) = (self.slot(x), self.constant(k)) {
                        return Slot::Hashed(args, at.wrapping_add(k));
                    }
                }
                Slot::Unknown
            }
            _ => Slot::Unknown,
        }
    }

    /// Whether two slots can be the same one. Hashes of operands that differ are taken to
    /// differ, as every Solidity layout takes them to.
    fn may_alias(&self, a: V, b: V) -> bool {
        if a == b {
            return true;
        }
        match (self.slot(a), self.slot(b)) {
            (Slot::Const(x), Slot::Const(y)) => x == y,
            (Slot::Const(_), Slot::Hashed(..)) | (Slot::Hashed(..), Slot::Const(_)) => false,
            (Slot::Hashed(x, i), Slot::Hashed(y, j)) => {
                if x == y {
                    return i == j;
                }
                // Apart when the hashes take different numbers of words, or some operand
                // is a different constant in each.
                x.len() == y.len()
                    && !x.iter().zip(&y).any(|(&p, &q)| {
                        matches!((self.constant(p), self.constant(q)), (Some(m), Some(n)) if m != n)
                    })
            }
            _ => true,
        }
    }

    /// Keeps a store back until `take_held`.
    pub(super) fn hold(&mut self, slot: V, word: V) {
        self.pending.retain(|&(s, _)| s != slot);
        self.pending.push((slot, word));
    }

    pub(super) fn held_empty(&self) -> bool {
        self.pending.is_empty()
    }

    /// Whether `slot` may be one a held store writes without being known to be it.
    pub(super) fn held_conflict(&self, slot: V) -> bool {
        self.pending
            .iter()
            .any(|&(s, _)| s != slot && self.may_alias(s, slot))
    }

    /// Whether a load of the slot would read storage: its word is not known here.
    pub(super) fn unknown(&self, slot: V, transient: bool) -> bool {
        let known = if transient {
            &self.transient
        } else {
            &self.stored
        };
        !known.iter().any(|&(s, _)| s == slot)
            && (transient || !self.pending.iter().any(|&(s, _)| s == slot))
    }

    pub(super) fn take_held(&mut self) -> Vec<(V, V)> {
        std::mem::take(&mut self.pending)
    }

    /// The stores held, to put back where another path starts from them.
    pub(super) fn held(&self) -> Vec<(V, V)> {
        self.pending.clone()
    }

    pub(super) fn set_held(&mut self, held: Vec<(V, V)>) {
        self.pending = held;
    }

    pub(super) fn imm(&mut self, k: u32, width: u8) -> V {
        self.pure(Op::Imm(k, width), Vec::new(), u16::from(width) * 8)
    }

    pub(super) fn load(&mut self, slot: V, transient: bool) -> V {
        if let Some(&(_, w)) = self.pending.iter().find(|(s, _)| *s == slot && !transient) {
            return w;
        }
        let known = if transient {
            &self.transient
        } else {
            &self.stored
        };
        if let Some(&(_, w)) = known.iter().find(|(s, _)| *s == slot) {
            return w;
        }
        let op = if transient { Op::TLoad } else { Op::SLoad };
        if !transient {
            let read: Vec<bool> = self
                .unread
                .iter()
                .map(|&(s, ..)| self.may_alias(s, slot))
                .collect();
            let mut read = read.into_iter();
            self.unread.retain(|_| !read.next().unwrap_or(true));
        }
        let op = match self.journal {
            Some((load, _)) if !transient => Op::Call(load),
            _ => op,
        };
        let w = self.push(op, vec![slot], 1, 256);
        let known = if transient {
            &mut self.transient
        } else {
            &mut self.stored
        };
        known.push((slot, w));
        w
    }

    pub(super) fn store(&mut self, slot: V, word: V, transient: bool) {
        let known = if transient {
            &self.transient
        } else {
            &self.stored
        };
        if known.contains(&(slot, word)) {
            return;
        }
        let kept: Vec<(V, V)> = known
            .iter()
            .copied()
            .filter(|&(s, _)| !self.may_alias(s, slot))
            .collect();
        let op = if transient { Op::TStore } else { Op::SStore };
        if !transient {
            // A store this one follows in the same block, with nothing between that could
            // read the slot, stores nothing anyone sees.
            if let Some(k) = self.unread.iter().position(|&(s, _, _)| s == slot) {
                let (_, b, i) = self.unread.remove(k);
                if b == self.cur {
                    let dead = &mut self.f.blocks[b as usize].insts[i as usize];
                    dead.op = Op::Nop;
                    dead.args.clear();
                }
            }
            let at = self.f.blocks[self.cur as usize].insts.len() as u32;
            self.unread.push((slot, self.cur, at));
        }
        let op = match self.journal {
            Some((_, store)) if !transient => Op::Call(store),
            _ => op,
        };
        self.push(op, vec![slot, word], 0, 0);
        let known = if transient {
            &mut self.transient
        } else {
            &mut self.stored
        };
        *known = kept;
        known.push((slot, word));
    }

    /// Other code may have run: nothing is known of storage.
    pub(super) fn forget_storage(&mut self) {
        self.unread.clear();
        self.stored.clear();
        self.transient.clear();
    }

    /// An instruction with effects, or one that reads what effects change.
    pub(super) fn effect(&mut self, op: Op, args: Vec<V>, outs: u8) -> V {
        // Other code, or a helper, may read what was stored.
        if matches!(
            op,
            Op::Call(_)
                | Op::ExtCall { .. }
                | Op::MemCall { .. }
                | Op::Create(_)
                | Op::StaticAt
                | Op::DelegateAt
                | Op::LoadStr
                | Op::Hash(_)
        ) {
            self.unread.clear();
        }
        self.push(op, args, outs, 256)
    }

    pub(super) fn state(&self) -> State {
        State {
            stored: self.stored.clone(),
            transient: self.transient.clone(),
            facts: self.facts.len(),
            ranges: self.ranges.len(),
            numbered: self.numbered_log.len(),
        }
    }

    /// Goes back to what held at `state`, keeping of storage what both it and here know.
    pub(super) fn restore(&mut self, state: &State) {
        self.unread.clear();
        self.stored = state.stored.clone();
        self.transient = state.transient.clone();
        self.facts.truncate(state.facts);
        self.ranges.truncate(state.ranges);
        for key in self.numbered_log.drain(state.numbered..) {
            self.numbered.remove(&key);
        }
    }

    /// What is known of storage here, to meet with another path's.
    pub(super) fn storage(&self) -> (Vec<(V, V)>, Vec<(V, V)>) {
        (self.stored.clone(), self.transient.clone())
    }

    /// Keeps of storage only what `other` also knows.
    pub(super) fn meet(&mut self, other: &(Vec<(V, V)>, Vec<(V, V)>)) {
        self.stored.retain(|e| other.0.contains(e));
        self.transient.retain(|e| other.1.contains(e));
    }

    fn end(&mut self, term: Term) {
        if self.dead {
            return;
        }
        let targets: Vec<B> = match &term {
            Term::Jump(b, _) => vec![*b],
            Term::Branch(_, t, f) => vec![*t, *f],
            _ => Vec::new(),
        };
        for t in targets {
            self.f.blocks[t as usize].preds += 1;
        }
        self.f.blocks[self.cur as usize].term = term;
        self.dead = true;
    }

    pub(super) fn jump(&mut self, to: B, args: Vec<V>) {
        self.end(Term::Jump(to, args));
    }

    pub(super) fn branch(&mut self, cond: V, then: B, other: B) {
        self.end(Term::Branch(cond, then, other));
    }

    pub(super) fn exit(&mut self, term: Term) {
        self.end(term);
    }

    /// Goes on building in `b`, which something reaches.
    pub(super) fn enter(&mut self, b: B) {
        self.unread.clear();
        self.cur = b;
        self.dead = false;
    }

    /// Whether `v` not being zero says `by` is under 256: `v` is a word shifted right by
    /// `by`, or whether such a word is nonzero.
    pub(super) fn shift_bounds(&self, mut v: V, by: V) -> bool {
        while let Some(&[inner]) = self.evm_def(v, ISZERO) {
            match self.evm_def(inner, ISZERO) {
                Some(&[word]) => v = word,
                None => return false,
                Some(_) => return false,
            }
        }
        self.evm_def(v, SHR).is_some_and(|args| args[0] == by)
    }

    /// A loop's blocks are those from `head` on, and `pre` is the block that enters it.
    /// A constant the loop keeps on the stack that takes more than a push to make is made
    /// once in `pre` and kept through the loop, not made again on every pass.
    pub(super) fn hold_through(&mut self, pre: B, head: B) {
        let from = head as usize;
        let mut swap: HashMap<V, V> = HashMap::new();
        // Constants: the first copy of each moves out, and the others become it.
        let mut moved: HashMap<Word, V> = HashMap::new();
        for b in from..self.f.blocks.len() {
            for i in 0..self.f.blocks[b].insts.len() {
                let inst = &mut self.f.blocks[b].insts[i];
                let (Op::Const(w), v) = (inst.op.clone(), inst.out) else {
                    continue;
                };
                if !costly(w) {
                    continue;
                }
                let tag = inst.tag;
                (inst.op, inst.outs) = (Op::Nop, 0);
                match moved.get(&w) {
                    Some(&first) => {
                        swap.insert(v, first);
                    }
                    None => {
                        moved.insert(w, v);
                        let at = self.f.blocks[pre as usize].insts.len() as u32;
                        self.f.blocks[pre as usize].insts.push(Inst {
                            op: Op::Const(w),
                            args: Vec::new(),
                            out: v,
                            outs: 1,
                            tag,
                        });
                        self.defs[v as usize] = (pre, at);
                    }
                }
            }
        }
        if swap.is_empty() {
            return;
        }
        for block in &mut self.f.blocks[from..] {
            let args = block.insts.iter_mut().flat_map(|inst| inst.args.iter_mut());
            for arg in args.chain(term_args(&mut block.term)) {
                if let Some(&to) = swap.get(arg) {
                    *arg = to;
                }
            }
        }
    }
}

/// Overflow checks next to each other in a block, with nothing between them that can fail
/// or be seen, fail as one: each becomes its operation and whether it overflowed, and one
/// jump after the last takes any of them to the panic. A value that was only checked to
/// fit is the value it was.
pub(super) fn share_checks(module: &mut Module) {
    // A mark is no code, so a build that certifies must share as one that does not.
    let quiet = |inst: &Inst| match inst.op {
        Op::Const(_) | Op::Imm(..) | Op::Nop | Op::Mark(_) => true,
        Op::Evm(op) => matches!(op, 0x01..=0x0b | 0x10..=0x1d | CALLDATALOAD),
        _ => false,
    };
    let shared = |inst: &Inst| {
        matches!(
            inst.op,
            Op::Checked(Arith::Add | Arith::Sub | Arith::Mul | Arith::Fit, _, false)
        )
    };
    for f in &mut module.funcs {
        let mut same: HashMap<V, V> = HashMap::new();
        for b in 0..f.blocks.len() {
            let mut i = 0;
            while i < f.blocks[b].insts.len() {
                // The run of checks from `i`, each reached from the one before by
                // instructions that only compute.
                let insts = &f.blocks[b].insts;
                let mut run = vec![i];
                let mut j = i + 1;
                while shared(&insts[i]) && j < insts.len() && run.len() < MERGED_CHECKS as usize {
                    match (shared(&insts[j]), quiet(&insts[j])) {
                        (true, _) => run.push(j),
                        (false, true) => {}
                        (false, false) => break,
                    }
                    j += 1;
                }
                if run.len() < 2 {
                    i += 1;
                    continue;
                }
                let last = run[run.len() - 1];
                let rest = f.blocks[b].insts.split_off(last + 1);
                let old = std::mem::take(&mut f.blocks[b].insts);
                let mut out = Vec::with_capacity(old.len() + 4 * run.len());
                let mut flags: Vec<V> = Vec::new();
                let kinds = &mut f.kinds;
                let mut fresh = |kind: Kind| {
                    kinds.push(kind);
                    (kinds.len() - 1) as V
                };
                for (k, inst) in old.into_iter().enumerate() {
                    // A mark between the checks names a place the first check's panic no
                    // longer comes before: the prover is told nothing of it.
                    if k > run[0] && matches!(inst.op, Op::Mark(_)) {
                        continue;
                    }
                    let (Op::Checked(arith, bits, _), true) = (inst.op.clone(), run.contains(&k))
                    else {
                        out.push(inst);
                        continue;
                    };
                    let tag = inst.tag;
                    let mut put = |op: u8, args: Vec<V>, out_v: Option<V>, kinds_v: V| {
                        let v = out_v.unwrap_or(kinds_v);
                        out.push(Inst {
                            op: Op::Evm(op),
                            args,
                            out: v,
                            outs: 1,
                            tag,
                        });
                        v
                    };
                    let (a, v) = (inst.args[0], inst.out);
                    let narrow = |put: &mut dyn FnMut(u8, Vec<V>, Option<V>, V) -> V,
                                  fresh: &mut dyn FnMut(Kind) -> V,
                                  of: V| {
                        let width = fresh(Kind::Const(Word::from_u64(u64::from(bits))));
                        let flag = fresh(Kind::Var);
                        put(SHR, vec![width, of], None, flag)
                    };
                    match arith {
                        Arith::Fit => {
                            flags.push(narrow(&mut put, &mut fresh, a));
                            same.insert(v, a);
                        }
                        Arith::Add => {
                            let b2 = inst.args[1];
                            put(ADD, vec![a, b2], Some(v), v);
                            flags.push(if bits < 256 {
                                narrow(&mut put, &mut fresh, v)
                            } else {
                                let flag = fresh(Kind::Var);
                                put(LT, vec![v, b2], None, flag)
                            });
                        }
                        Arith::Sub => {
                            let b2 = inst.args[1];
                            let flag = fresh(Kind::Var);
                            flags.push(put(LT, vec![a, b2], None, flag));
                            put(SUB, vec![a, b2], Some(v), v);
                        }
                        _ => {
                            let b2 = inst.args[1];
                            put(MUL, vec![a, b2], Some(v), v);
                            if bits > 128 {
                                // Lost when the product over one of them is not the other.
                                let (q, eq, ne, flag) = (
                                    fresh(Kind::Var),
                                    fresh(Kind::Var),
                                    fresh(Kind::Var),
                                    fresh(Kind::Var),
                                );
                                put(DIV, vec![v, b2], None, q);
                                put(EQ, vec![q, a], None, eq);
                                put(ISZERO, vec![eq], None, ne);
                                flags.push(put(MUL, vec![ne, b2], None, flag));
                            }
                            if bits < 256 {
                                flags.push(narrow(&mut put, &mut fresh, v));
                            }
                        }
                    }
                }
                let mut any = flags[0];
                for &flag in &flags[1..] {
                    let either = fresh(Kind::Var);
                    out.push(Inst {
                        op: Op::Evm(OR),
                        args: vec![any, flag],
                        out: either,
                        outs: 1,
                        tag: NO_TAG,
                    });
                    any = either;
                }
                out.push(Inst {
                    op: Op::Trap,
                    args: vec![any],
                    out: 0,
                    outs: 0,
                    tag: NO_TAG,
                });
                i = out.len();
                out.extend(rest);
                f.blocks[b].insts = out;
            }
        }
        if same.is_empty() {
            continue;
        }
        // One checked to fit may have been checked from another.
        let whole = |mut v: V| {
            while let Some(&to) = same.get(&v) {
                v = to;
            }
            v
        };
        for block in &mut f.blocks {
            let args = block.insts.iter_mut().flat_map(|inst| inst.args.iter_mut());
            for arg in args.chain(term_args(&mut block.term)) {
                *arg = whole(*arg);
            }
        }
        let notes = &mut f.notes;
        for note in &mut notes.loops {
            note.counter = whole(note.counter);
            for (_, v) in &mut note.locals {
                *v = v.map(whole);
            }
            for (_, at, len) in &mut note.lists {
                (*at, *len) = (whole(*at), whole(*len));
            }
        }
        let inlined = notes.marks.iter_mut().filter_map(|mark| match mark {
            MarkNote::Inline { params, .. } => Some(params),
            _ => None,
        });
        for (_, v) in inlined
            .chain(notes.entry.as_mut().map(|e| &mut e.3))
            .flatten()
        {
            *v = whole(*v);
        }
    }
}

/// A function compiled once is no longer passed the arguments its code never reads, and
/// its calls no longer make them. Becomes whether any went, which may leave what made
/// them unread in turn.
pub(super) fn drop_unread_params(module: &mut Module) -> bool {
    // Per function, the places among a call's arguments that go, last first.
    let mut gone: Vec<Vec<usize>> = Vec::new();
    for f in &mut module.funcs {
        let mut read = vec![false; f.kinds.len()];
        for block in &mut f.blocks {
            for inst in &block.insts {
                for &arg in &inst.args {
                    read[arg as usize] = true;
                }
            }
            for &mut arg in term_args(&mut block.term) {
                read[arg as usize] = true;
            }
        }
        // The stack as it starts is the arguments, the first on top, under the return
        // address: only a function called has one.
        let n = match f.ret {
            Some(_) => f.params.len() - 1,
            None => 0,
        };
        let unread: Vec<usize> = (0..n).filter(|&k| !read[f.params[k] as usize]).collect();
        for &k in unread.iter().rev() {
            f.params.remove(k);
        }
        gone.push(unread.iter().map(|&k| n - 1 - k).collect());
    }
    for f in &mut module.funcs {
        for inst in f.blocks.iter_mut().flat_map(|b| b.insts.iter_mut()) {
            if let Op::Call(to) = inst.op {
                for &k in &gone[to as usize] {
                    inst.args.remove(k);
                }
            }
        }
    }
    gone.iter().any(|g| !g.is_empty())
}

/// Whether a constant takes more than one push to make.
fn costly(w: Word) -> bool {
    let code = asm::encode_push(w);
    !(0x5f..=0x7f).contains(&code[0]) || code.len() != 1 + usize::from(code[0] - 0x5f)
}

/// The values a block's end reads.
fn term_args(term: &mut Term) -> impl Iterator<Item = &mut V> {
    let (one, many): (Option<&mut V>, &mut [V]) = match term {
        Term::Branch(cond, ..) => (Some(cond), &mut []),
        Term::Jump(_, args)
        | Term::Ret(args)
        | Term::Return(_, args)
        | Term::Revert(_, args)
        | Term::ReturnAt(args)
        | Term::RevertAt(args) => (None, args),
        Term::Open | Term::Stop | Term::Bubble | Term::Goto(_) => (None, &mut []),
    };
    one.into_iter().chain(many)
}

/// Drops the pure instructions nothing uses, in the blocks something reaches.
pub(super) fn dead_code(mut module: Module) -> Module {
    for f in &mut module.funcs {
        let n = f.kinds.len();
        let mut reached = vec![false; f.blocks.len()];
        let mut work = vec![0usize];
        while let Some(b) = work.pop() {
            if std::mem::replace(&mut reached[b], true) {
                continue;
            }
            match &f.blocks[b].term {
                Term::Jump(t, _) => work.push(*t as usize),
                Term::Branch(_, t, e) => work.extend([*t as usize, *e as usize]),
                _ => {}
            }
        }
        let mut def = vec![(usize::MAX, 0usize); n];
        for (b, block) in f.blocks.iter().enumerate() {
            for (i, inst) in block.insts.iter().enumerate() {
                for k in 0..inst.outs {
                    def[(inst.out + u32::from(k)) as usize] = (b, i);
                }
            }
        }
        let pure = |op: &Op| {
            matches!(
                op,
                Op::Const(_)
                    | Op::Nop
                    | Op::MLoad
                    | Op::Keccak
                    | Op::Imm(..)
                    | Op::Evm(_)
                    | Op::Hash(_)
                    | Op::SLoad
                    | Op::TLoad
                    | Op::RetSize
                    | Op::RetWord(_)
            )
        };
        let mut used = vec![false; n];
        let mut work: Vec<V> = Vec::new();
        for (b, block) in f.blocks.iter().enumerate() {
            if !reached[b] {
                continue;
            }
            for inst in &block.insts {
                if !pure(&inst.op) {
                    work.extend(&inst.args);
                }
            }
            match &block.term {
                Term::Jump(_, args)
                | Term::Ret(args)
                | Term::Return(_, args)
                | Term::Revert(_, args)
                | Term::ReturnAt(args)
                | Term::RevertAt(args) => work.extend(args),
                Term::Branch(c, ..) => work.push(*c),
                _ => {}
            }
        }
        work.extend(f.ret);
        while let Some(v) = work.pop() {
            if std::mem::replace(&mut used[v as usize], true) {
                continue;
            }
            let (b, i) = def[v as usize];
            if b != usize::MAX && pure(&f.blocks[b].insts[i].op) {
                work.extend(&f.blocks[b].insts[i].args);
            }
        }
        for (b, block) in f.blocks.iter_mut().enumerate() {
            if !reached[b] {
                block.insts.clear();
                block.term = Term::Open;
                continue;
            }
            block.insts.retain(|inst| {
                !pure(&inst.op) || (0..inst.outs).any(|k| used[(inst.out + u32::from(k)) as usize])
            });
        }
    }
    module
}

/// How many checks may become one: more keeps too much on the stack at once.
const MERGED_CHECKS: u32 = 4;

/// Two checks that fail alike, with nothing between them but what cannot fail or be seen,
/// become one check of either: the code that passes both branches once.
pub(super) fn merge_checks(module: &mut Module) {
    let fails = |f: &Func, b: B| match &f.blocks[b as usize] {
        Block {
            insts,
            term: Term::Revert(enc, args),
            ..
        } if insts.is_empty()
            && args
                .iter()
                .all(|&a| matches!(f.kinds[a as usize], Kind::Const(_))) =>
        {
            Some((enc.clone(), args.clone()))
        }
        _ => None,
    };
    let eager = |inst: &Inst| match inst.op {
        Op::Const(_) | Op::Imm(..) | Op::Nop | Op::Mark(_) => true,
        Op::Evm(op) => matches!(op, 0x01..=0x0b | 0x10..=0x1d | CALLDATALOAD),
        _ => false,
    };
    for f in &mut module.funcs {
        let mut merged = vec![1u32; f.blocks.len()];
        loop {
            let found = (0..f.blocks.len()).find_map(|p| {
                let Term::Branch(c1, out, next) = f.blocks[p].term else {
                    return None;
                };
                let n = &f.blocks[next as usize];
                let Term::Branch(c2, out2, after) = n.term else {
                    return None;
                };
                let alike = fails(f, out).is_some_and(|how| fails(f, out2) == Some(how));
                (alike
                    && n.preds == 1
                    && n.params.is_empty()
                    && merged[p] < MERGED_CHECKS
                    && n.insts.iter().all(eager))
                .then_some((p, c1, c2, out, out2, next as usize, after))
            });
            let Some((p, c1, c2, out, out2, next, after)) = found else {
                break;
            };
            let either = f.kinds.len() as V;
            f.kinds.push(Kind::Var);
            let mut insts = std::mem::take(&mut f.blocks[next].insts);
            // A mark between the two tests names a place that is no longer one: the first
            // test's revert is taken after it now. The prover is told nothing of it.
            insts.retain(|inst| !matches!(inst.op, Op::Mark(_)));
            insts.push(Inst {
                op: Op::Evm(OR),
                args: vec![c1, c2],
                out: either,
                outs: 1,
                tag: NO_TAG,
            });
            f.blocks[next].term = Term::Open;
            f.blocks[next].preds = 0;
            f.blocks[p].insts.extend(insts);
            f.blocks[p].term = Term::Branch(either, out, after);
            merged[p] += 1;
            if out2 != out {
                let gone = &mut f.blocks[out2 as usize];
                gone.preds -= 1;
                if gone.preds == 0 {
                    gone.term = Term::Open;
                }
            }
        }
    }
}
