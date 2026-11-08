//! The code as blocks. A block starts at its labels, or after an exit, and runs to the next
//! exit or label, so every label heads a block and only the first block or dead code has
//! none. A pushed label is an edge to the block it heads, and a block that does not end in
//! an exit falls into the next. The passes here edit blocks in place, move whole blocks, and
//! write the stream out once.

use super::{
    assemble, byte_gas, enters, entries, heat, inst_len, inst_len_wide, is_terminal, stack_io,
    track, FxHashMap, FxHashSet, Inst, ISZERO, JUMP, JUMPDEST, JUMPI, MAX_ROUNDS, MIN_TAIL_BYTES,
    TAIL_GAS,
};
use super::{Imm, Label, Op, Push, PushLabel, Table};

#[derive(Clone, Default, Debug, PartialEq)]
pub(crate) struct Block {
    pub labels: Vec<u32>,
    pub body: Vec<Inst>,
}

impl Block {
    /// Whether it ends in an exit, so nothing falls out of it.
    pub fn exits(&self) -> bool {
        matches!(self.body.last(), Some(Op(op)) if is_terminal(*op))
    }

    fn insts(&self) -> impl Iterator<Item = Inst> + '_ {
        let labels = self.labels.iter().map(|&l| Label(l));
        labels.chain(self.body.iter().copied())
    }

    /// The labels it pushes, once per push or table entry.
    fn refs(&self) -> impl Iterator<Item = u32> + '_ {
        self.body.iter().flat_map(|inst| {
            let (one, table) = match inst {
                PushLabel(l) => (Some(*l), None),
                Table(t) => (None, Some(entries(t))),
                _ => (None, None),
            };
            one.into_iter().chain(table.into_iter().flatten())
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Blocks {
    pub blocks: Vec<Block>,
}

impl Blocks {
    pub fn new(code: &[Inst]) -> Self {
        let mut blocks = Vec::new();
        let mut i = 0;
        while i < code.len() {
            let start = i;
            while let Some(Label(_)) = code.get(i) {
                i += 1;
            }
            let labels = code[start..i].iter().map(|inst| match inst {
                Label(l) => *l,
                _ => unreachable!("only labels head a block"),
            });
            let body = i;
            while let Some(&inst) = code.get(i) {
                if matches!(inst, Label(_)) {
                    break;
                }
                i += 1;
                if matches!(inst, Op(op) if is_terminal(op)) {
                    break;
                }
            }
            blocks.push(Block {
                labels: labels.collect(),
                body: code[body..i].to_vec(),
            });
        }
        Blocks { blocks }
    }

    pub fn code(&self) -> Vec<Inst> {
        serialize(&self.blocks)
    }

    /// The block each label heads.
    pub fn at(&self) -> FxHashMap<u32, usize> {
        let mut at = FxHashMap::default();
        for (k, b) in self.blocks.iter().enumerate() {
            at.extend(b.labels.iter().map(|&l| (l, k)));
        }
        at
    }

    /// Where block `k` can go: once per label it pushes, then the next block if it falls.
    pub fn succ(&self, k: usize, at: &FxHashMap<u32, usize>) -> Vec<usize> {
        let b = &self.blocks[k];
        let mut out: Vec<usize> = b.refs().filter_map(|l| at.get(&l).copied()).collect();
        if !b.exits() && k + 1 < self.blocks.len() {
            out.push(k + 1);
        }
        out
    }

    /// The blocks that can come to each, once per edge.
    pub fn preds(&self) -> Vec<Vec<usize>> {
        let at = self.at();
        let mut preds = vec![Vec::new(); self.blocks.len()];
        for k in 0..self.blocks.len() {
            for s in self.succ(k, &at) {
                preds[s].push(k);
            }
        }
        preds
    }

    fn fresh_label(&self) -> u32 {
        let labels = self
            .blocks
            .iter()
            .flat_map(|b| b.labels.iter().copied().chain(b.refs()));
        labels.max().unwrap_or(0) + 1
    }

    fn rename(&mut self, map: &FxHashMap<u32, u32>) {
        track::note(|t| t.renamed.extend(map.iter().map(|(a, b)| (*a, *b))));
        let follow = |l: &mut u32| {
            let mut to = *l;
            let mut hops = 0;
            while let Some(next) = map.get(&to) {
                if *next == to || hops > 64 {
                    break;
                }
                to = *next;
                hops += 1;
            }
            *l = to;
        };
        for inst in self.blocks.iter_mut().flat_map(|b| &mut b.body) {
            match inst {
                PushLabel(l) => follow(l),
                Table(t) => t.iter_mut().filter(|l| **l != 0).for_each(follow),
                _ => {}
            }
        }
    }

    /// Joins what an edit left apart: labels with no body move onto the next block, and a
    /// block with no labels that something falls into joins it.
    fn tidy(&mut self) {
        let mut out: Vec<Block> = Vec::with_capacity(self.blocks.len());
        for b in self.blocks.drain(..) {
            match out.last_mut() {
                Some(last) if last.body.is_empty() => {
                    last.labels.extend(b.labels);
                    last.body = b.body;
                }
                Some(last) if b.labels.is_empty() && !last.exits() => last.body.extend(b.body),
                _ if b.labels.is_empty() && b.body.is_empty() => {}
                _ => out.push(b),
            }
        }
        self.blocks = out;
    }

    /// Drops labels nothing jumps to and folds each block's labels into its first.
    fn prune_labels(&mut self) -> bool {
        let mut changed = false;
        let map: FxHashMap<u32, u32> = self
            .blocks
            .iter()
            .flat_map(|b| b.labels.iter().skip(1).map(|&l| (l, b.labels[0])))
            .collect();
        if !map.is_empty() {
            self.rename(&map);
            self.blocks.iter_mut().for_each(|b| b.labels.truncate(1));
            changed = true;
        }
        let refs: FxHashSet<u32> = self.blocks.iter().flat_map(Block::refs).collect();
        for b in &mut self.blocks {
            let n = b.labels.len();
            b.labels.retain(|l| refs.contains(l));
            changed |= b.labels.len() != n;
        }
        if changed {
            self.tidy();
        }
        changed
    }

    /// A block with no labels after the first follows an exit, so nothing reaches it.
    fn remove_dead(&mut self) -> bool {
        let before = self.blocks.len();
        let mut first = true;
        self.blocks
            .retain(|b| std::mem::take(&mut first) || !b.labels.is_empty());
        self.blocks.len() != before
    }

    /// Retargets jumps that land on another jump, and copies tiny exits in place of a jump.
    fn thread_jumps(&mut self) -> bool {
        let at = self.at();
        let blocks = &mut self.blocks;
        let mut changed = false;
        for k in 0..blocks.len() {
            let mut j = 0;
            while j + 1 < blocks[k].body.len() {
                let (PushLabel(l), Op(jump @ (JUMP | JUMPI))) =
                    (blocks[k].body[j], blocks[k].body[j + 1])
                else {
                    j += 1;
                    continue;
                };
                if !at.contains_key(&l) {
                    j += 1;
                    continue;
                }
                // Follow jump-to-jump chains. A cycle of bare jumps stays as it is.
                let mut to = l;
                let mut seen = vec![l];
                while let Some(&t) = at.get(&to) {
                    let body = &blocks[t].body;
                    let (Some(PushLabel(m)), Some(Op(JUMP))) = (body.first(), body.get(1)) else {
                        break;
                    };
                    if seen.contains(m) || !at.contains_key(m) {
                        break;
                    }
                    seen.push(*m);
                    to = *m;
                }
                if to != l {
                    blocks[k].body[j] = PushLabel(to);
                    changed = true;
                }
                if jump == JUMP {
                    if let Some(copy) = tiny_exit(&blocks[at[&to]].body) {
                        blocks[k].body.splice(j..j + 2, copy);
                        changed = true;
                    }
                }
                j += 1;
            }
        }
        changed
    }

    /// `peephole` on each block, with the labels of the next, which its rewrites look at but
    /// never take. A block that ends in a jump goes with the next, since emptying that
    /// one can show the jump its target. Otherwise nothing reaches across, so this is
    /// `peephole` on the stream.
    fn peephole(&mut self) -> bool {
        let jumps = |b: &Block| matches!(b.body[..], [.., PushLabel(_), Op(JUMP)]);
        let blocks = &mut self.blocks;
        // Spans whose code changed, and what replaces them.
        let mut edits: Vec<(usize, usize, Vec<Block>)> = Vec::new();
        let mut w = Vec::new();
        let mut k = 0;
        while k < blocks.len() {
            let mut e = k;
            while e + 1 < blocks.len() && jumps(&blocks[e]) {
                e += 1;
            }
            let labels = blocks.get(e + 1).map_or(&[][..], |b| &b.labels[..]);
            let next = labels.len();
            w.clear();
            w.extend(blocks[k].insts());
            w.extend(blocks[k + 1..=e].iter().flat_map(Block::insts));
            w.extend(labels.iter().map(|&l| Label(l)));
            if super::peephole(&mut w) {
                w.truncate(w.len() - next);
                edits.push((k, e, Blocks::new(&w).blocks));
            }
            k = e + 1;
        }
        if edits.is_empty() {
            return false;
        }
        let mut old = std::mem::take(blocks).into_iter();
        let mut at = 0;
        for (k, e, new) in edits {
            blocks.extend(old.by_ref().take(k - at));
            old.by_ref().take(e + 1 - k).for_each(drop);
            blocks.extend(new);
            at = e + 1;
        }
        blocks.extend(old);
        self.tidy();
        true
    }

    /// `dup_constants` on each block: it forgets the stack at a label and after an exit, so
    /// this is the same as on the stream.
    fn dup_constants(&mut self) -> bool {
        super::dup_constants_in(self.blocks.iter_mut().map(|b| &mut b.body[..]))
    }

    /// `schedule` on each block: its straight runs hold no label or exit. A body it empties
    /// passes its labels on.
    fn schedule(&mut self) -> bool {
        let exits = super::safe_exits(&self.code());
        let mut changed = false;
        for b in &mut self.blocks {
            changed |= super::schedule_runs(&mut b.body, &exits);
        }
        if changed {
            self.tidy();
        }
        changed
    }

    /// Blocks with the same body share one copy.
    fn dedup_blocks(&mut self) -> bool {
        let mut first: FxHashMap<&[Inst], u32> = FxHashMap::default();
        let mut map: FxHashMap<u32, u32> = FxHashMap::default();
        for b in &self.blocks {
            if b.labels.is_empty() || !b.exits() {
                continue;
            }
            let keep = *first.entry(&b.body).or_insert(b.labels[0]);
            if keep != b.labels[0] {
                map.extend(b.labels.iter().filter(|&&l| l != keep).map(|&l| (l, keep)));
            }
        }
        if map.is_empty() {
            return false;
        }
        self.rename(&map);
        true
    }

    /// Two exits that end the same way share the common tail.
    fn merge_tails(&mut self) -> bool {
        let blocks = &self.blocks;
        // Where each body starts in the stream, for the heat of its instructions.
        let mut start = Vec::with_capacity(blocks.len());
        let mut pos = 0;
        for b in blocks {
            start.push(pos + b.labels.len());
            pos += b.labels.len() + b.body.len();
        }
        // Only tails long enough to share need it.
        let heat = std::cell::OnceCell::new();
        let heat = |k: usize, j: usize| {
            let (heat, at) = heat.get_or_init(|| stream_heat(blocks));
            heat[at[start[k] + j] as usize]
        };
        let preds = std::cell::OnceCell::new();
        // Sharing a tail puts a jump on every path into the donor. A helper's body runs on
        // every call to it, so its tail must save a byte for each call it slows.
        let calls = |k: usize| {
            let body = &blocks[k].body;
            let n = body.len();
            if body[n - 1] != Op(JUMP) || matches!(body[n - 2], PushLabel(_)) {
                return 1;
            }
            preds.get_or_init(|| self.preds())[k].len().max(1)
        };
        // Exits that share a tail worth sharing share its shortest end of `MIN_TAIL_BYTES`.
        let mut by_last: FxHashMap<&[Inst], Vec<usize>> = FxHashMap::default();
        for (k, b) in blocks.iter().enumerate() {
            if !b.exits() {
                continue;
            }
            let mut bytes = 0;
            let short = b.body.iter().rev().position(|inst| {
                bytes += inst_len(inst);
                bytes >= MIN_TAIL_BYTES
            });
            if let Some(j) = short {
                let n = b.body.len();
                by_last.entry(&b.body[n - 1 - j..]).or_default().push(k);
            }
        }
        let mut pairs: Vec<(usize, usize, usize, usize)> = Vec::new();
        let common = |a: usize, b: usize| {
            let (ba, bb) = (&blocks[a].body, &blocks[b].body);
            ba.iter()
                .rev()
                .zip(bb.iter().rev())
                .take_while(|(x, y)| x == y)
                .count()
        };
        for group in by_last.values().filter(|g| g.len() > 1) {
            // Sorted by body read backwards, two exits share the least common tail of the
            // neighbours between them.
            let mut sorted = group.clone();
            sorted.sort_unstable_by(|&a, &b| {
                let key = |b: usize| blocks[b].body.iter().rev().map(order);
                key(a).cmp(key(b))
            });
            let near: Vec<usize> = sorted.windows(2).map(|w| common(w[0], w[1])).collect();
            // The bytes of each exit's last instructions, as many as it shares with any.
            let sums: Vec<Vec<usize>> = (0..sorted.len())
                .map(|x| {
                    let reach = near[x.saturating_sub(1)].max(*near.get(x).unwrap_or(&0));
                    let mut sums = vec![0];
                    for inst in blocks[sorted[x]].body.iter().rev().take(reach) {
                        sums.push(sums[sums.len() - 1] + inst_len(inst));
                    }
                    sums
                })
                .collect();
            for x in 0..sorted.len() {
                let mut n = usize::MAX;
                for y in x + 1..sorted.len() {
                    n = n.min(near[y - 1]);
                    let (a, b) = (sorted[x].min(sorted[y]), sorted[x].max(sorted[y]));
                    let sizes = &sums[x];
                    // The copy that takes the jump runs it where the shared tail starts, which a
                    // tail reaching back over a `JUMPI` makes hot, so each length and side is
                    // weighed: it must save a byte for each few gas it adds.
                    // Heat is never negative, so a shorter tail saves at most its bytes.
                    let mut best: Option<(f64, usize, usize, usize)> = None;
                    for m in (1..=n).rev() {
                        let bytes = sizes[m];
                        let most = (bytes + 1).saturating_sub(MIN_TAIL_BYTES) as f64;
                        if bytes < MIN_TAIL_BYTES || best.is_some_and(|(s, ..)| s >= most) {
                            break;
                        }
                        for (keep, give) in [(a, b), (b, a)] {
                            if bytes + 1 < MIN_TAIL_BYTES + calls(give)
                                || best.is_some_and(|(s, ..)| s >= most)
                            {
                                continue;
                            }
                            let (k, g) = (&blocks[keep], &blocks[give]);
                            let whole = m == k.body.len() && !k.labels.is_empty();
                            let label = if whole {
                                0.0
                            } else {
                                heat(keep, k.body.len() - m)
                            };
                            let slower =
                                (heat(give, g.body.len() - m) * TAIL_GAS + label) / byte_gas();
                            let saved = (bytes + 1 - MIN_TAIL_BYTES) as f64 - slower;
                            if saved >= 0.0 && best.is_none_or(|(s, ..)| saved > s) {
                                best = Some((saved, keep, give, m));
                            }
                        }
                    }
                    if let Some((_, keep, give, m)) = best {
                        pairs.push((keep, give, m, sizes[m]));
                    }
                }
            }
        }
        // The longest tails first, ties to the earliest pair, so the output never depends on
        // map order. A block takes part in at most its best merge a call, which keeps the
        // others' indices and heat as they were, and waits when that partner is taken.
        pairs.sort_unstable_by(|x, y| y.3.cmp(&x.3).then((x.0, x.1).cmp(&(y.0, y.1))));
        let mut used = vec![false; blocks.len()];
        let mut next = self.fresh_label();
        // Where a kept tail gets a label of its own.
        let mut split: Vec<Option<(usize, u32)>> = vec![None; blocks.len()];
        let mut gives: Vec<(usize, usize, u32)> = Vec::new();
        for &(a, b, n, _) in &pairs {
            let free = !used[a] && !used[b];
            used[a] = true;
            used[b] = true;
            if !free {
                continue;
            }
            let keep = &blocks[a];
            let whole = n == keep.body.len() && !keep.labels.is_empty();
            let label = if whole {
                keep.labels[0]
            } else {
                next += 1;
                split[a] = Some((keep.body.len() - n, next - 1));
                next - 1
            };
            gives.push((b, n, label));
        }
        if gives.is_empty() {
            return false;
        }
        for (give, n, label) in gives {
            let body = &mut self.blocks[give].body;
            body.truncate(body.len() - n);
            body.extend([PushLabel(label), Op(JUMP)]);
        }
        let mut out = Vec::with_capacity(self.blocks.len() + split.len());
        for (mut b, split) in self.blocks.drain(..).zip(split) {
            if let Some((at, label)) = split {
                let tail = b.body.split_off(at);
                if !b.labels.is_empty() || !b.body.is_empty() {
                    out.push(b);
                }
                out.push(Block {
                    labels: vec![label],
                    body: tail,
                });
            } else {
                out.push(b);
            }
        }
        self.blocks = out;
        true
    }

    /// Tests each top-tested loop at its bottom, so an iteration takes one jump, not two:
    /// `top: T PUSH done JUMPI B PUSH top JUMP` becomes
    /// `PUSH test JUMP body: B test: T' PUSH body JUMPI`, where `T'` is `T` with its result
    /// negated, and the exit falls through to `done` or jumps there. The same code runs in
    /// the same order, so any straight run `T` can move.
    fn rotate_loops(&mut self) -> bool {
        let mut next = self.fresh_label();
        let blocks = &mut self.blocks;
        let mut changed = false;
        let mut h = 0;
        while h < blocks.len() {
            if blocks[h].labels.is_empty() {
                h += 1;
                continue;
            }
            let tops = blocks[h].labels.clone();
            let head = &blocks[h].body;
            let Some(n) = head.iter().position(|inst| !is_test(inst)) else {
                h += 1;
                continue;
            };
            let (Some(&PushLabel(done)), Some(Op(JUMPI))) = (head.get(n), head.get(n + 1)) else {
                h += 1;
                continue;
            };
            // simplify: each head scans every block for its back jump and entries, as the
            // stream version scanned every instruction; a label-to-block reference index
            // would make it linear when loops are many.
            let back = (h..blocks.len()).rev().find(|&k| {
                let b = &blocks[k].body;
                b.len() >= 2
                    && b[b.len() - 1] == Op(JUMP)
                    && matches!(b[b.len() - 2], PushLabel(l) if tops.contains(&l))
                    && (k > h || b.len() - 2 > n + 1)
            });
            let Some(kb) = back else {
                h += 1;
                continue;
            };
            let e = blocks[kb].body.len() - 2;
            // Only a loop: nothing outside the head and body jumps to the head or into the body.
            let inner: FxHashSet<u32> = blocks[h + 1..=kb]
                .iter()
                .flat_map(|b| b.labels.iter().copied())
                .chain(tops.iter().copied())
                .collect();
            let outside =
                |k: usize, j: usize| k < h || k > kb || (k == h && j <= n) || (k == kb && j > e);
            let entered = blocks.iter().enumerate().any(|(k, b)| {
                b.body.iter().enumerate().any(|(j, inst)| match inst {
                    PushLabel(l) => inner.contains(l) && outside(k, j),
                    Table(t) => entries(t).any(|l| inner.contains(&l)),
                    _ => false,
                })
            });
            if entered {
                h += 1;
                continue;
            }
            let (body, test) = (next, next + 1);
            next += 2;
            changed = true;
            let t = blocks[h].body[..n].to_vec();
            let mut bottom = t.clone();
            if bottom.last() == Some(&Op(ISZERO)) {
                bottom.pop();
            } else {
                bottom.push(Op(ISZERO));
            }
            bottom.extend([PushLabel(body), Op(JUMPI)]);
            let falls = blocks.get(kb + 1).is_some_and(|b| b.labels.contains(&done));
            if !falls {
                bottom.extend([PushLabel(done), Op(JUMP)]);
            }
            blocks[kb].body.truncate(e);
            if blocks[kb].body.is_empty() {
                blocks[kb].labels.push(test);
                blocks[kb].body = bottom;
            } else {
                let b = Block {
                    labels: vec![test],
                    body: bottom,
                };
                blocks.insert(kb + 1, b);
            }
            let before = h.checked_sub(1).map_or(&[][..], |p| &blocks[p].body[..]);
            let falls_in = enters(before, &t);
            blocks[h].labels = vec![body];
            blocks[h].body.drain(..n + 2);
            // An iteration starts at the body now; when the test jumps there, the body is
            // the next head to try.
            let mut after = h + 1;
            if !falls_in {
                let jump = [PushLabel(test), Op(JUMP)];
                match h.checked_sub(1) {
                    Some(p) if !blocks[p].exits() => blocks[p].body.extend(jump),
                    _ => {
                        let b = Block {
                            labels: Vec::new(),
                            body: jump.to_vec(),
                        };
                        blocks.insert(h, b);
                        h += 1;
                    }
                }
                after = h;
            }
            if blocks[h].body.is_empty() && h + 1 < blocks.len() {
                let b = blocks.remove(h + 1);
                blocks[h].labels.extend(b.labels);
                blocks[h].body = b.body;
            }
            for inst in blocks.iter_mut().flat_map(|b| &mut b.body) {
                if matches!(inst, PushLabel(l) if tops.contains(l)) {
                    *inst = PushLabel(test);
                }
            }
            // An iteration starts at the body now, with the stack the test left.
            track::note(|t| t.renamed.extend(tops.iter().map(|&l| (l, body))));
            h = after;
        }
        changed
    }

    /// Drops the `ISZERO` from a branch around a block that ends in an exit:
    /// `c ISZERO PUSH skip JUMPI block skip:` becomes `c PUSH block JUMPI skip:`, and the
    /// block moves to after the next exit, where nothing falls into it. A top-tested loop's
    /// body is such a block, ending in the jump back to the test. A move that widens label
    /// pushes past what it saves is undone.
    fn rotate_exits(&mut self) -> bool {
        let mut next = self.fresh_label();
        let mut at = self.at();
        let mut size = None;
        let mut changed = false;
        // At least the bytes before the instruction looked at. Past 0xff, every label a move
        // touches already takes two bytes, so no push widens and the move cannot grow the
        // code.
        let mut low = 0;
        let mut k = 0;
        while k < self.blocks.len() {
            let mut j = 0;
            while j < self.blocks[k].body.len() {
                let body = &self.blocks[k].body;
                if let (Op(ISZERO), Some(&PushLabel(exit)), Some(Op(JUMPI))) =
                    (body[j], body.get(j + 1), body.get(j + 2))
                {
                    if let Some((x, a)) = exit_move(&self.blocks, &at, k, exit) {
                        let fits = low > 0xff || {
                            let mut trial = self.blocks.clone();
                            move_exit(&mut trial, k, j, x, a, next);
                            let len = |b: &[Block]| {
                                assemble(&serialize(b)).map_or(usize::MAX, |c| c.len())
                            };
                            let fits =
                                len(&trial) <= *size.get_or_insert_with(|| len(&self.blocks));
                            if fits {
                                self.blocks = trial;
                            }
                            fits
                        };
                        if fits {
                            if low > 0xff {
                                move_exit(&mut self.blocks, k, j, x, a, next);
                            }
                            size = None;
                            next += 1;
                            at = self.at();
                            changed = true;
                        }
                    }
                }
                low += match self.blocks[k].body[j] {
                    PushLabel(_) => 2,
                    inst => inst_len(&inst),
                };
                j += 1;
            }
            k += 1;
        }
        changed
    }

    /// Moves the most-jumped-to standalone runs of blocks to just after the first exit,
    /// where their labels fit in one byte. A standalone run starts after an exit and ends in
    /// one, so nothing falls into it or out of it.
    fn hoist(&mut self) -> bool {
        let blocks = &self.blocks;
        let Some(first) = blocks.iter().position(Block::exits) else {
            return false;
        };
        let wide = |b: &Block| b.insts().map(|i| inst_len_wide(&i)).sum::<usize>();
        let before: usize = blocks[..=first].iter().map(wide).sum();
        if before >= 0xff {
            return false;
        }
        let mut refs: FxHashMap<u32, usize> = FxHashMap::default();
        for inst in blocks.iter().flat_map(|b| &b.body) {
            if let PushLabel(l) = inst {
                *refs.entry(*l).or_default() += 1;
            }
        }
        // (first block, last block, references to their labels, bytes)
        let mut runs: Vec<(usize, usize, usize, usize)> = Vec::new();
        let mut k = first + 1;
        while k < blocks.len() {
            if blocks[k].labels.is_empty() || !blocks[k - 1].exits() {
                k += 1;
                continue;
            }
            let Some(end) = (k..blocks.len()).find(|&e| blocks[e].exits()) else {
                break;
            };
            let run = &blocks[k..=end];
            let hits = run
                .iter()
                .flat_map(|b| &b.labels)
                .map(|l| refs.get(l).copied().unwrap_or(0))
                .sum();
            runs.push((k, end, hits, run.iter().map(wide).sum()));
            k = end + 1;
        }
        runs.sort_by(|a, b| (b.2 * a.3).cmp(&(a.2 * b.3)).then(a.0.cmp(&b.0)));
        let mut at = before;
        let mut picked: Vec<(usize, usize)> = Vec::new();
        for &(start, end, hits, bytes) in &runs {
            // Its first label must land below 256 for the move to pay.
            if hits < 2 || at >= 0xff {
                continue;
            }
            picked.push((start, end));
            at += bytes;
        }
        if picked.is_empty() {
            return false;
        }
        let mut old: Vec<Option<Block>> = std::mem::take(&mut self.blocks)
            .into_iter()
            .map(Some)
            .collect();
        let mut take = |range: std::ops::RangeInclusive<usize>| {
            old[range]
                .iter_mut()
                .map(|b| b.take().expect("each block moves once"))
                .collect::<Vec<_>>()
        };
        let mut out = take(0..=first);
        for &(start, end) in &picked {
            out.extend(take(start..=end));
        }
        out.extend(old.into_iter().flatten());
        self.blocks = out;
        true
    }
}

/// Some total order on instructions, equal exactly when they are.
fn order(inst: &Inst) -> (u8, [u64; 4], [u32; 8]) {
    match *inst {
        Op(op) => (0, [op.into(), 0, 0, 0], [0; 8]),
        Push(w) => (1, w.0, [0; 8]),
        Label(l) => (2, [l.into(), 0, 0, 0], [0; 8]),
        PushLabel(l) => (3, [l.into(), 0, 0, 0], [0; 8]),
        super::Mem(m) => (4, [m.into(), 0, 0, 0], [0; 8]),
        Table(t) => (5, [0; 4], t),
        Imm(i, n) => (6, [i.into(), n.into(), 0, 0], [0; 8]),
    }
}

fn serialize(blocks: &[Block]) -> Vec<Inst> {
    let len = blocks.iter().map(|b| b.labels.len() + b.body.len()).sum();
    let mut code = Vec::with_capacity(len);
    for b in blocks {
        code.extend(b.labels.iter().map(|&l| Label(l)));
        code.extend_from_slice(&b.body);
    }
    code
}

thread_local! {
    static LAST_HEAT: std::cell::RefCell<(Vec<Inst>, Vec<f64>)> = Default::default();
}

/// `heat` of the stream `blocks` write, and where each instruction finds its value in it.
/// `flow` reads only labels, label pushes, tables, and the exits and `JUMPI`s that end its
/// blocks, so it runs on that skeleton with each run of other instructions standing as one,
/// and the last skeleton's heat is reused when it recurs.
fn stream_heat(blocks: &[Block]) -> (Vec<f64>, Vec<u32>) {
    let mut skel = Vec::new();
    let mut at = Vec::with_capacity(blocks.iter().map(|b| b.labels.len() + b.body.len()).sum());
    for b in blocks {
        skel.extend(b.labels.iter().map(|&l| Label(l)));
        at.extend((skel.len() - b.labels.len()) as u32..skel.len() as u32);
        let mut plain = false;
        for &inst in &b.body {
            let kept = match inst {
                PushLabel(_) | Table(_) => true,
                Op(op) => is_terminal(op) || op == JUMPI,
                _ => false,
            };
            if kept || !plain {
                skel.push(if kept { inst } else { Op(ISZERO) });
            }
            plain = !kept;
            at.push(skel.len() as u32 - 1);
        }
    }
    let heat = LAST_HEAT.with(|last| {
        let mut last = last.borrow_mut();
        if last.0 != skel {
            last.1 = heat(&skel);
            last.0 = skel;
        }
        last.1.clone()
    });
    if super::verify() {
        let out: Vec<f64> = at.iter().map(|&k| heat[k as usize]).collect();
        assert_eq!(out, super::heat(&serialize(blocks)), "skeleton heat");
    }
    (heat, at)
}

/// What can stand in a loop test: straight code with no jump.
fn is_test(inst: &Inst) -> bool {
    match inst {
        Op(op) => {
            stack_io(*op).is_some() && !is_terminal(*op) && !matches!(*op, JUMPI | JUMPDEST | 0x58)
        }
        Push(_) | Imm(..) => true,
        _ => false,
    }
}

/// A `PUSH0 PUSH0 REVERT` or `STOP` heading `body`, which is no larger than a jump to it.
fn tiny_exit(body: &[Inst]) -> Option<Vec<Inst>> {
    let mut bytes = 0;
    for (end, inst) in body.iter().enumerate() {
        match inst {
            Push(w) if w.is_zero() => bytes += 1,
            Op(op) if is_terminal(*op) && *op != JUMP => {
                return (bytes < 3).then(|| body[..=end].to_vec());
            }
            _ => return None,
        }
        if bytes > 3 {
            return None;
        }
    }
    None
}

/// For a branch in block `k` around blocks to `exit`: the block `exit` heads, when an exit
/// comes just before it, and the first block from there that ends in an exit.
fn exit_move(
    blocks: &[Block],
    at: &FxHashMap<u32, usize>,
    k: usize,
    exit: u32,
) -> Option<(usize, usize)> {
    let x = *at.get(&exit)?;
    if x <= k || blocks[x].labels[0] != exit || !blocks[x - 1].exits() {
        return None;
    }
    let a = (x..blocks.len()).find(|&a| blocks[a].exits())?;
    Some((x, a))
}

/// Turns `ISZERO PUSH exit JUMPI` at `j` in block `k` into `PUSH next JUMPI`, and moves what
/// came between it and block `x` to after block `a`, under label `next`.
fn move_exit(blocks: &mut Vec<Block>, k: usize, j: usize, x: usize, a: usize, next: u32) {
    let tail = blocks[k].body.split_off(j + 3);
    blocks[k].body.truncate(j);
    blocks[k].body.extend([PushLabel(next), Op(JUMPI)]);
    blocks[k + 1..=a].rotate_left(x - k - 1);
    let moved = a + k + 2 - x;
    if tail.is_empty() {
        blocks[moved].labels.insert(0, next);
    } else {
        let b = Block {
            labels: vec![next],
            body: tail,
        };
        blocks.insert(moved, b);
    }
}

fn run(code: &mut Vec<Inst>, pass: fn(&mut Blocks) -> bool) -> bool {
    let mut blocks = Blocks::new(code);
    let changed = pass(&mut blocks);
    if changed {
        *code = blocks.code();
    }
    changed
}

/// `optimize`'s rounds on one set of blocks, for code with no marks to carry between
/// passes. Each pass leaves the blocks as `Blocks::new` would split its output.
/// `optimize`'s rounds on one set of blocks, for code with no marks to carry between
/// passes. Each pass leaves the blocks as `Blocks::new` would split its output.
pub(super) fn optimize(code: &mut Vec<Inst>) {
    let mut b = Blocks::new(code);
    for _ in 0..MAX_ROUNDS {
        let mut changed = b.prune_labels() | b.remove_dead() | b.thread_jumps();
        changed |= b.peephole();
        changed |= b.dedup_blocks();
        changed |= b.dup_constants();
        if !changed {
            changed |= b.merge_tails();
        }
        if !changed {
            changed |= b.schedule();
        }
        if !changed {
            break;
        }
    }
    *code = b.code();
}

pub(super) fn prune_labels(code: &mut Vec<Inst>) -> bool {
    run(code, Blocks::prune_labels)
}

pub(super) fn remove_dead(code: &mut Vec<Inst>) -> bool {
    run(code, Blocks::remove_dead)
}

pub(super) fn thread_jumps(code: &mut Vec<Inst>) -> bool {
    run(code, Blocks::thread_jumps)
}

pub(super) fn dedup_blocks(code: &mut Vec<Inst>) -> bool {
    run(code, Blocks::dedup_blocks)
}

pub(super) fn merge_tails(code: &mut Vec<Inst>) -> bool {
    run(code, Blocks::merge_tails)
}

pub(crate) fn rotate_loops(code: &mut Vec<Inst>) {
    run(code, Blocks::rotate_loops);
}

pub(crate) fn rotate_exits(code: &mut Vec<Inst>) {
    run(code, Blocks::rotate_exits);
}

pub(crate) fn hoist(code: &mut Vec<Inst>) {
    run(code, Blocks::hoist);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::word::Word;

    /// The rounds on the stream, pass by pass, as `optimize` runs them for the prover.
    fn stream_optimize(code: &mut Vec<Inst>) {
        for _ in 0..MAX_ROUNDS {
            let mut changed = prune_labels(code) | remove_dead(code) | thread_jumps(code);
            changed |= super::super::peephole(code);
            changed |= dedup_blocks(code);
            changed |= super::super::dup_constants(code);
            if !changed {
                changed |= merge_tails(code);
            }
            if !changed {
                changed |= super::super::schedule(code);
            }
            if !changed {
                return;
            }
        }
    }

    /// A jump whose target the next block's labels hide until a rewrite empties that
    /// block, which the stream sees by backing up over the labels: one pass, and all.
    #[test]
    fn rounds_on_blocks_match_the_stream() {
        use super::super::{POP, RETURN};
        let w = |n| Push(Word::from_u64(n));
        let code = vec![
            Op(0x36),
            PushLabel(4),
            Op(JUMPI),
            PushLabel(3),
            Op(JUMP),
            Label(1),
            w(7),
            Op(POP),
            Label(2),
            Label(3),
            w(0),
            w(0),
            Op(RETURN),
            Label(4),
            w(5),
            PushLabel(4),
            Op(JUMPI),
            PushLabel(1),
            Op(JUMP),
        ];
        let mut blocks = Blocks::new(&code);
        let mut stream = code.clone();
        assert!(blocks.peephole());
        assert!(super::super::peephole(&mut stream));
        assert_eq!(blocks.code(), stream);
        let mut blocks = code.clone();
        optimize(&mut blocks);
        let mut stream = code;
        stream_optimize(&mut stream);
        assert_eq!(blocks, stream);
    }

    #[test]
    fn splits_links_and_writes_back() {
        let one = Push(Word::from_u64(1));
        let code = vec![
            one,
            PushLabel(2),
            Op(JUMPI),
            PushLabel(3),
            Op(JUMP),
            one,
            Label(2),
            Label(4),
            one,
            Label(3),
            Op(super::super::STOP),
        ];
        let b = Blocks::new(&code);
        let shape: Vec<(usize, usize)> = b
            .blocks
            .iter()
            .map(|b| (b.labels.len(), b.body.len()))
            .collect();
        assert_eq!(shape, [(0, 5), (0, 1), (2, 1), (1, 1)]);
        assert_eq!(b.code(), code);
        let at = b.at();
        assert_eq!(b.succ(0, &at), [2, 3]);
        assert_eq!(b.succ(2, &at), [3]);
        assert_eq!(b.preds(), [vec![], vec![], vec![0, 1], vec![0, 2]]);
        let mut pruned = b.clone();
        assert!(pruned.prune_labels() && pruned.remove_dead());
        assert_eq!(
            pruned.code(),
            [
                one,
                PushLabel(2),
                Op(JUMPI),
                PushLabel(3),
                Op(JUMP),
                Label(2),
                one,
                Label(3),
                Op(super::super::STOP)
            ]
        );
    }
}
