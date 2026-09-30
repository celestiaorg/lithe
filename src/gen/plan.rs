use super::*;

impl<'a> Gen<'a> {
    pub(super) fn new(checked: &'a Checked, plan: Plan, shape: &'a Shape) -> Result<Self, Error> {
        let mut g = Self {
            checked,
            plan,
            shape,
            needs: Vec::new(),
            entry_labels: Vec::new(),
            inlined: HashMap::new(),
            funcs: HashMap::new(),
            shared: false,
            log_sites: 0,
            return_sites: 0,
            direct: false,
            lists_in_order: true,
            any_nonreentrant: false,
            reject_value: None,
            decoding_args: false,
            tree_at: 0,
            tree_len: 0,
            code: Vec::new(),
            next_label: 0,
            spaces: Vec::new(),
            image: 0,
            dirty: 0,
            local: Vec::new(),
            query_buf: 0,
            in_query: false,
            query_gas: None,
            tail: false,
            fire_tail: false,
            hoisted: HashMap::new(),
            skip_queries: std::collections::HashSet::new(),
            scratch_a: 0,
            scratch_b: 0,
            scratch_c: 0,
            scratch_to: 0,
            scratch_val: 0,
            key_scratch: 0,
            base64_tbl: 0,
            mul_div_buf: 0,
            init: false,
            code_args: 0,
            code_end: Word::from_u64(0),
            bytes_sites: (0, 0),
            decode_sites: 0,
            value_sites: [0; 3],
            eq_sites: 0,
            slice_sites: [0; 2],
            mul_sites: 0,
            exp_sites: [0; 2],
            queued_sites: 0,
            queue_sites: HashMap::new(),
            trusted_index: false,
            cd_lists: std::collections::HashSet::new(),
            cd_bytes: std::collections::HashSet::new(),
            cd_lazy: std::collections::HashSet::new(),
            cd_words: std::collections::HashSet::new(),
            cd_trees: std::collections::HashSet::new(),
            slot_hint: None,
            bytes_rep: None,
            dyn_key: None,
            slot_binds: HashMap::new(),
            key_names: HashMap::new(),
            const_params: HashMap::new(),
            shared_temps: std::collections::HashSet::new(),
            func_ctx: None,
            func_calls: std::collections::HashSet::new(),
            transient_slot: false,
            data: Vec::new(),
            peer_built: HashMap::new(),
            literals: HashMap::new(),
            returned: None,
            slot_cache: HashMap::new(),
            val_cache: HashMap::new(),
            kept_store: false,
            cache_words: Vec::new(),
            leaf_words: Vec::new(),
            failing: 0,
            ret_scratch: 0,
            args_buf: 0,
            hash_buf: 0,
            topic_buf: 0,
            journal_len: 0,
            journal_at: 0,
            journal_base: 0,
            blob_ptr: 0,
            rooms: HashMap::new(),
            owners: HashMap::new(),
            owned: HashMap::new(),
            sharing: Vec::new(),
            blob_base: 0,
            fn_ret: Vec::new(),
            tuple_buf: 0,
            compiling: Vec::new(),
            fails: Vec::new(),
            raises: Vec::new(),
            raise_sites: HashMap::new(),
            subs: Vec::new(),
            revert_kinds: 0,
            revert_head: None,
            branch: 0,
            top_branch: 0,
            body: None,
            bodies: 0,
            loop_syms: Vec::new(),
            header_locals: std::collections::HashSet::new(),
            loop_counters: Vec::new(),
            facts: Vec::new(),
            imm_mem: 0,
            cd_tail: 0,
            imm_tail: Vec::new(),
            tail_blobs: Vec::new(),
        };
        // Immutables are never in memory, so the image has no words for them.
        let leaves =
            (g.checked.leaves - (g.checked.transient_from - g.checked.immutable_from)) as u32;
        g.image = g.region(Region::Image, leaves * 32);
        g.dirty = g.region(Region::Dirty, leaves * 32);
        let mut local = vec![-1; g.checked.syms.len()];
        for (i, slot) in local.iter_mut().enumerate() {
            let sym = &g.checked.syms[i];
            if sym.storage && !g.checked.slot_syms.contains_key(&i) {
                continue;
            }
            let w = if sym.span > 0 {
                sym.span
            } else {
                g.checked.types[sym.ty].words
            };
            if w == 0 {
                continue;
            }
            *slot = g.region(Region::Local(i), w * 32);
        }
        g.local = local;
        g.lists_in_order = g.stored_lists_in_order();
        g.any_nonreentrant = g.checked.routes.iter().any(|r| r.nonreentrant)
            || g.checked.prog.funcs.iter().any(|f| f.nonreentrant);
        let mut fn_ret = vec![-1i32; g.checked.prog.funcs.len()];
        for (i, slot) in fn_ret.iter_mut().enumerate() {
            let f = &g.checked.prog.funcs[i];
            let ret = &g.checked.types[f.ret_ty];
            let returned = matches!(f.kind, ItemKind::Entry | ItemKind::View)
                && is_static_aggregate(&g.checked.types, f.ret_ty);
            let option = ret.kind == TyKind::Option && ret.words > 1;
            let aggregate = matches!(ret.kind, TyKind::Tuple | TyKind::Record)
                || (ret.kind == TyKind::List && ret.bits > 0);
            if (aggregate || returned || option) && ret.words > 0 {
                let words = ret.words;
                *slot = g.region(Region::FnRet(i), words * 32);
            }
        }
        g.fn_ret = fn_ret;
        if shape.part {
            g.facet_tail();
        }
        let mut tuple_words = 2u32;
        for ty in &g.checked.types {
            if ty.kind == TyKind::Tuple {
                tuple_words = tuple_words.max(ty.words);
            }
        }
        g.tuple_buf = g.region(Region::Tuple, tuple_words * 32);
        g.topic_buf = g.region(Region::Topic, TOPIC_WORDS * 32);
        g.query_buf = g.region(Region::Query, 32);
        g.scratch_a = g.region(Region::Scratch(0), 32);
        g.scratch_b = g.region(Region::Scratch(1), 32);
        g.scratch_c = g.region(Region::Scratch(2), 32);
        g.scratch_to = g.region(Region::Scratch(3), 32);
        g.scratch_val = g.region(Region::Scratch(4), 32);
        g.key_scratch = g.region(Region::Scratch(5), 32);
        g.code_args = g.region(Region::Scratch(6), 32);
        g.mul_div_buf = g.region(Region::Scratch(7), 160);
        g.tree_at = g.region(Region::Scratch(8), 32);
        g.tree_len = g.region(Region::Scratch(9), 32);
        g.ret_scratch = g.region(Region::Ret, 96);
        g.args_buf = g.region(Region::Args, 128);
        g.hash_buf = g.region(Region::Hash, 0);
        g.journal_len = g.region(Region::JournalLen, 32);
        g.journal_at = g.region(Region::JournalAt, 32);
        g.journal_base = g.region(Region::Journal, MAX_JOURNAL as u32 * 64);
        g.blob_ptr = g.region(Region::BlobPtr, 32);
        g.blob_base = g.region(Region::Blob, 0);
        g.base64_tbl = g.region(Region::Base64, 0);
        g.owners = g.find_owners();
        Ok(g)
    }

    pub(super) fn region(&mut self, region: Region, size: u32) -> i32 {
        self.spaces.push(Space {
            region,
            size,
            extent: 0,
            heat: 0,
            users: Users::Nobody,
        });
        (self.spaces.len() as i32) << REGION_SHIFT
    }

    /// Pushes a memory address. Its region learns who uses it and how far in.
    pub(super) fn push_mem(&mut self, addr: i32) {
        self.note_mem(addr);
        self.code.push(Inst::Mem(addr as u32));
    }

    /// Whether a binding to zero can be left to the memory it lives in: a word local of the
    /// entry itself, declared outside loops, inlined calls, and continuation phases, has
    /// memory nothing in this call has written. The word is still noted as used.
    pub(super) fn fresh_zero(&mut self, sym: usize, expr: &Expr) -> bool {
        let zero = match expr {
            Expr::Lit { lit, .. } => match lit {
                Lit::Uint(w) | Lit::Int(w, _) | Lit::Wei(w) | Lit::Duration(w) => w.is_zero(),
                Lit::Bool(b) => !b,
                _ => false,
            },
            _ => false,
        };
        let ty = self.checked.syms[sym].ty;
        let word = self.checked.types[ty].words == 1
            && self.checked.types[self.peel_nominal(ty)].kind != TyKind::Option
            && self.is_word_ty(self.peel_nominal(ty));
        if !zero
            || !word
            || !self.compiling.is_empty()
            || !self.loop_syms.is_empty()
            || self.shared
            || self.body.as_ref().is_none_or(|b| b.nested)
            || self.local[sym] < 0
        {
            return false;
        }
        self.note_mem(self.local[sym]);
        true
    }

    /// Records a use of `addr` that reaches memory through arithmetic on another address.
    pub(super) fn note_mem(&mut self, addr: i32) {
        let ix = (addr >> REGION_SHIFT) as usize - 1;
        let off = (addr & ((1 << REGION_SHIFT) - 1)) as u32;
        let user = self.region_user();
        let shared = self.shared;
        let space = &mut self.spaces[ix];
        space.heat += 1;
        space.extent = space.extent.max(off + 32);
        space.users = match (std::mem::replace(&mut space.users, Users::Nobody), user) {
            (Users::Everyone, _) | (_, None) => Users::Everyone,
            (Users::Nobody, Some(id)) if shared => Users::Shared([id].into_iter().collect()),
            (Users::Nobody, Some(id)) => Users::Bodies([id].into_iter().collect()),
            (Users::Bodies(mut ids), Some(id)) if !shared => {
                ids.insert(id);
                Users::Bodies(ids)
            }
            (Users::Bodies(mut ids) | Users::Shared(mut ids), Some(id)) => {
                ids.insert(id);
                Users::Shared(ids)
            }
        };
    }

    /// The body, or the function compiled once, whose code is being emitted.
    pub(super) fn region_user(&self) -> Option<usize> {
        if self.shared {
            self.func_ctx
        } else {
            self.body.as_ref().map(|b| b.id)
        }
    }

    /// Outline a function when its copies cost more than one copy plus a call per use, the
    /// gas each run of a call adds priced at `asm::byte_gas`. One transaction runs one
    /// body, so the body that runs the calls most counts.
    pub(super) fn plan(&self) -> Plan {
        let mut outline = std::collections::HashSet::new();
        let mut looped = std::collections::HashSet::new();
        let mut outlinable = std::collections::HashSet::new();
        for (&idx, (calls, bytes, runs)) in &self.inlined {
            let (calls, bytes) = (*calls, *bytes);
            let runs = runs.values().fold(0.0, |a: f64, &b| a.max(b));
            if calls < 2 || !self.outline_safe(idx, &mut Vec::new()) {
                continue;
            }
            outlinable.insert(idx);
            // Each call also stores its arguments, which inlined copies may read in place.
            let params = self.checked.prog.funcs[idx].params.len();
            let inline = calls * bytes;
            let shared = bytes + 3 + calls * (8 + 3 * params);
            let slower = runs * (CALL_GAS + ARG_GAS * params as f64) / asm::byte_gas();
            if inline as f64 > shared as f64 + slower {
                outline.insert(idx);
                if runs > 1.0 {
                    looped.insert(idx);
                }
            }
        }
        // The pure functions whose copies here are large enough to run remotely, with what
        // each calls, which its library facet holds.
        let least = if remote_all(self.shape) {
            0
        } else {
            MIN_REMOTE_BYTES
        };
        let mut remotable: Vec<(usize, Vec<usize>)> = self
            .inlined
            .iter()
            .filter(|(&idx, (calls, bytes, _))| calls * bytes >= least && self.remotable(idx))
            .map(|(&idx, _)| {
                let mut calls = Vec::new();
                self.func_any(idx, &|_| false, &mut calls);
                calls.sort_unstable();
                (idx, calls)
            })
            .collect();
        remotable.sort_unstable();
        // A helper costs its body once plus a call per site; one site stays inline.
        let shared_bytes = (self.bytes_sites.0 >= 2, self.bytes_sites.1 >= 2);
        Plan {
            cache_slots: false,
            tight: false,
            hold_dups: false,
            frames: false,
            sink: false,
            outline,
            looped,
            outlinable,
            remote: Default::default(),
            remotable,
            shared_bytes,
            shared_decode: self.decode_sites >= 2,
            shared_value: self.value_sites.map(|n| n >= 2),
            shared_eq: self.eq_sites >= 2,
            shared_slice: self.slice_sites.map(|n| n >= 2),
            // A call costs 8 bytes to the 18 of the check inlined.
            shared_mul: self.mul_sites >= 3,
            shared_exp: self.exp_sites.map(|n| n >= 2),
            queue_helper: self.queued_sites >= 2,
            single_queues: self
                .queue_sites
                .iter()
                .filter(|(_, &n)| n == 1)
                .map(|(&q, _)| q)
                .collect(),
            shared_raises: self
                .raise_sites
                .iter()
                .filter(|(_, &n)| n >= 2)
                .map(|(key, _)| key.clone())
                .collect(),
        }
    }

    /// A function compiles the same way wherever it is called unless it defers, queries,
    /// or cases on a dispatched variant.
    /// Whether a library facet can run a function: it is pure, and takes and returns only
    /// values the ABI encodes as they are, so no option, variant with payloads, map, or
    /// storage.
    fn remotable(&self, idx: usize) -> bool {
        let f = &self.checked.prog.funcs[idx];
        f.kind == ItemKind::Pure
            && f.exported.is_none()
            && self.abi_value(f.ret_ty)
            && f.params.iter().all(|p| {
                !p.storage
                    && p.sym
                        .is_some_and(|s| !self.checked.slot_syms.contains_key(&s))
                    && self.abi_value(p.ty_id)
            })
    }

    fn abi_value(&self, ty: usize) -> bool {
        let t = &self.checked.types[ty];
        !matches!(
            t.kind,
            TyKind::Option | TyKind::Map | TyKind::Variant | TyKind::Operation
        ) && !is_sum(&self.checked.types, ty)
            && t.elem.is_none_or(|e| self.abi_value(e))
            && t.fields.iter().all(|f| self.abi_value(f.ty))
    }

    fn outline_safe(&self, idx: usize, seen: &mut Vec<usize>) -> bool {
        let bad = |node: Node<'_>| match node {
            Node::Stmt(st) => matches!(st, Stmt::Defer { .. }),
            Node::Expr(e) => match e {
                Expr::Query { .. } => true,
                Expr::Call { builtin, iface, .. } => {
                    iface.is_some() || *builtin == Some(Builtin::Transfer)
                }
                Expr::Case { scrut, .. } => self.checked.types[scrut.ty()].kind == TyKind::Variant,
                _ => false,
            },
        };
        !self.func_any(idx, &bad, seen)
    }

    /// Whether any statement or expression in a function, or in what it calls, is `bad`.
    pub(super) fn func_any(
        &self,
        idx: usize,
        bad: &dyn Fn(Node<'_>) -> bool,
        seen: &mut Vec<usize>,
    ) -> bool {
        if seen.contains(&idx) {
            return false;
        }
        seen.push(idx);
        let f = &self.checked.prog.funcs[idx];
        f.stmts.iter().any(|st| self.stmt_any(st, bad, seen))
            || f.tail.as_ref().is_some_and(|e| self.expr_any(e, bad, seen))
    }

    pub(super) fn stmt_any(
        &self,
        st: &Stmt,
        bad: &dyn Fn(Node<'_>) -> bool,
        seen: &mut Vec<usize>,
    ) -> bool {
        if bad(Node::Stmt(st)) {
            return true;
        }
        let expr = |e: &Expr, seen: &mut Vec<usize>| self.expr_any(e, bad, seen);
        match st {
            Stmt::Skip => false,
            Stmt::Emit { fields, .. } => fields.iter().any(|(_, e)| expr(e, seen)),
            Stmt::Defer {
                then: Some(then), ..
            } if then
                .arms()
                .flat_map(|arm| &arm.stmts)
                .any(|s| self.stmt_any(s, bad, seen)) =>
            {
                true
            }
            Stmt::Defer {
                expr: e,
                value,
                gas,
                ..
            } => expr(e, seen) || value.iter().chain(gas).any(|v| expr(v, seen)),
            Stmt::Const { expr: e, .. }
            | Stmt::Var { expr: e, .. }
            | Stmt::Call { expr: e, .. }
            | Stmt::AssignTuple { expr: e, .. } => expr(e, seen),
            Stmt::Assign {
                index,
                keys,
                expr: e,
                ..
            } => {
                index.as_ref().is_some_and(|i| expr(i, seen))
                    || keys.iter().any(|k| expr(k, seen))
                    || expr(e, seen)
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                expr(cond, seen)
                    || then_body.iter().any(|s| self.stmt_any(s, bad, seen))
                    || else_body.iter().any(|s| self.stmt_any(s, bad, seen))
            }
            Stmt::For {
                iter,
                until,
                bound,
                elem_init,
                length,
                body,
                ..
            } => {
                let in_iter = match iter {
                    ForIter::Range { lo, hi } => expr(lo, seen) || expr(hi, seen),
                    ForIter::List(xs) => expr(xs, seen),
                };
                in_iter
                    || until
                        .iter()
                        .chain(bound)
                        .chain(elem_init)
                        .chain(length)
                        .any(|e| expr(e, seen))
                    || body.iter().any(|s| self.stmt_any(s, bad, seen))
            }
            Stmt::Assert { cond, reason, .. } => {
                expr(cond, seen) || self.raised_any(reason, bad, seen)
            }
            Stmt::Fail { reason, .. } => self.raised_any(reason, bad, seen),
        }
    }

    /// Whether a loop in these statements, or in what they call, defers a call. Such a
    /// body keeps its deferred calls in a runtime list, since a site can fire many times.
    pub(super) fn loops_defer(&self, stmts: &[Stmt], tail: Option<&Expr>) -> bool {
        let defers = |node: Node<'_>| matches!(node, Node::Stmt(Stmt::Defer { .. }));
        let looped = |node: Node<'_>| match node {
            Node::Stmt(Stmt::For { body, .. }) => body
                .iter()
                .any(|s| self.stmt_any(s, &defers, &mut Vec::new())),
            _ => false,
        };
        stmts
            .iter()
            .any(|s| self.stmt_any(s, &looped, &mut Vec::new()))
            || tail.is_some_and(|e| self.expr_any(e, &looped, &mut Vec::new()))
    }

    /// Every local a statement or expression reads, for what a continuation captures.
    pub(super) fn stmt_syms(&self, st: &Stmt, out: &mut Vec<usize>) {
        match st {
            Stmt::Skip => {}
            Stmt::Emit { fields, .. } => {
                for (_, e) in fields {
                    self.expr_syms(e, out);
                }
            }
            Stmt::Defer {
                expr,
                value,
                gas,
                then,
                ..
            } => {
                self.expr_syms(expr, out);
                for v in value.iter().chain(gas) {
                    self.expr_syms(v, out);
                }
                if let Some(then) = then {
                    for arm in then.arms() {
                        for s in &arm.stmts {
                            self.stmt_syms(s, out);
                        }
                    }
                }
            }
            Stmt::Const { expr, .. }
            | Stmt::Var { expr, .. }
            | Stmt::Call { expr, .. }
            | Stmt::AssignTuple { expr, .. } => self.expr_syms(expr, out),
            Stmt::Assign {
                index,
                keys,
                expr,
                root,
                ..
            } => {
                out.extend(root);
                for e in index.iter().chain(keys) {
                    self.expr_syms(e, out);
                }
                self.expr_syms(expr, out);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                self.expr_syms(cond, out);
                for s in then_body.iter().chain(else_body) {
                    self.stmt_syms(s, out);
                }
            }
            Stmt::For {
                iter,
                until,
                bound,
                elem_init,
                length,
                body,
                ..
            } => {
                match iter {
                    ForIter::Range { lo, hi } => {
                        self.expr_syms(lo, out);
                        self.expr_syms(hi, out);
                    }
                    ForIter::List(xs) => self.expr_syms(xs, out),
                }
                for e in until.iter().chain(bound).chain(elem_init).chain(length) {
                    self.expr_syms(e, out);
                }
                for s in body {
                    self.stmt_syms(s, out);
                }
            }
            Stmt::Assert { cond, reason, .. } => {
                self.expr_syms(cond, out);
                self.raised_syms(reason, out);
            }
            Stmt::Fail { reason, .. } => self.raised_syms(reason, out),
        }
    }

    /// Every local a statement assigns.
    pub(super) fn written_syms(st: &Stmt, out: &mut Vec<usize>) {
        match st {
            Stmt::Assign { root, .. } => out.extend(root),
            Stmt::AssignTuple { syms, .. } => out.extend(syms),
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                for s in then_body.iter().chain(else_body) {
                    Self::written_syms(s, out);
                }
            }
            Stmt::For { body, .. } => {
                for s in body {
                    Self::written_syms(s, out);
                }
            }
            _ => {}
        }
    }

    fn raised_syms(&self, reason: &Raised, out: &mut Vec<usize>) {
        match &reason.form {
            RaisedForm::Unit => {}
            RaisedForm::Positional(e) => self.expr_syms(e, out),
            RaisedForm::Fields(fields) => {
                for (_, e) in fields {
                    self.expr_syms(e, out);
                }
            }
        }
    }

    pub(super) fn expr_syms(&self, e: &Expr, out: &mut Vec<usize>) {
        match e {
            Expr::Lit { .. } => {}
            Expr::Ident { sym, .. } => out.extend(sym),
            Expr::Query { expr, gas, .. } => {
                self.expr_syms(expr, out);
                if let Some(gas) = gas {
                    self.expr_syms(gas, out);
                }
            }
            Expr::Unary { expr, .. } => self.expr_syms(expr, out),
            Expr::Field { base, root, .. } => {
                out.extend(root);
                self.expr_syms(base, out);
            }
            Expr::Index {
                base, index, root, ..
            } => {
                out.extend(root);
                self.expr_syms(base, out);
                self.expr_syms(index, out);
            }
            Expr::Call {
                args, base, callee, ..
            } => {
                if let Some(idx) = callee {
                    // An inlined callee reads what its body reads.
                    for s in &self.checked.prog.funcs[*idx].stmts {
                        self.stmt_syms(s, out);
                    }
                    if let Some(tail) = &self.checked.prog.funcs[*idx].tail {
                        self.expr_syms(tail, out);
                    }
                }
                if let Some(b) = base {
                    self.expr_syms(b, out);
                }
                for a in args {
                    self.expr_syms(a, out);
                }
            }
            Expr::Case { scrut, arms, .. } => {
                self.expr_syms(scrut, out);
                for arm in arms {
                    for s in &arm.stmts {
                        self.stmt_syms(s, out);
                    }
                    self.expr_syms(&arm.expr, out);
                }
            }
            Expr::Binary { left, right, .. } => {
                self.expr_syms(left, out);
                self.expr_syms(right, out);
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                for x in elems {
                    self.expr_syms(x, out);
                }
            }
            Expr::Record { fields, .. } => {
                for (_, x) in fields {
                    self.expr_syms(x, out);
                }
            }
        }
    }

    /// The loop locals a continuation reads: each one's memory and words. The `defer`
    /// snapshots them, because the loop rebinds them before the call runs.
    pub(super) fn loop_captures(&self, then: Option<&Then>) -> Vec<(i32, u32)> {
        let Some(then) = then else {
            return Vec::new();
        };
        if self.loop_syms.is_empty() {
            return Vec::new();
        }
        let mut read = Vec::new();
        for arm in then.arms() {
            for s in &arm.stmts {
                self.stmt_syms(s, &mut read);
            }
        }
        read.sort_unstable();
        read.dedup();
        let mut out = Vec::new();
        for sym in read {
            if !self.loop_syms.iter().any(|syms| syms.contains(&sym)) {
                continue;
            }
            let info = &self.checked.syms[sym];
            if info.storage || self.local[sym] < 0 {
                continue;
            }
            let words = if info.span > 0 {
                info.span
            } else {
                self.checked.types[info.ty].words
            };
            if words > 0 {
                out.push((self.local[sym], words));
            }
        }
        out
    }

    fn raised_any(
        &self,
        reason: &Raised,
        bad: &dyn Fn(Node<'_>) -> bool,
        seen: &mut Vec<usize>,
    ) -> bool {
        match &reason.form {
            RaisedForm::Unit => false,
            RaisedForm::Positional(e) => self.expr_any(e, bad, seen),
            RaisedForm::Fields(fields) => fields.iter().any(|(_, e)| self.expr_any(e, bad, seen)),
        }
    }

    pub(super) fn expr_any(
        &self,
        e: &Expr,
        bad: &dyn Fn(Node<'_>) -> bool,
        seen: &mut Vec<usize>,
    ) -> bool {
        if bad(Node::Expr(e)) {
            return true;
        }
        match e {
            Expr::Lit { .. } | Expr::Ident { .. } => false,
            Expr::Query { expr, gas, .. } => {
                self.expr_any(expr, bad, seen)
                    || gas.as_ref().is_some_and(|g| self.expr_any(g, bad, seen))
            }
            Expr::Unary { expr, .. } => self.expr_any(expr, bad, seen),
            Expr::Field { base, .. } => self.expr_any(base, bad, seen),
            Expr::Index { base, index, .. } => {
                self.expr_any(base, bad, seen) || self.expr_any(index, bad, seen)
            }
            Expr::Call {
                args, base, callee, ..
            } => {
                callee.is_some_and(|idx| self.func_any(idx, bad, seen))
                    || base.as_ref().is_some_and(|b| self.expr_any(b, bad, seen))
                    || args.iter().any(|a| self.expr_any(a, bad, seen))
            }
            Expr::Case { scrut, arms, .. } => {
                self.expr_any(scrut, bad, seen)
                    || arms.iter().any(|arm| {
                        arm.stmts.iter().any(|s| self.stmt_any(s, bad, seen))
                            || self.expr_any(&arm.expr, bad, seen)
                    })
            }
            Expr::Binary { left, right, .. } => {
                self.expr_any(left, bad, seen) || self.expr_any(right, bad, seen)
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                elems.iter().any(|x| self.expr_any(x, bad, seen))
            }
            Expr::Record { fields, .. } => fields.iter().any(|(_, x)| self.expr_any(x, bad, seen)),
        }
    }

    /// Whether evaluating `e` even when its value is not needed is free of effects and
    /// failures, and about as cheap as the jump that would skip it: literals, locals,
    /// fixed context, stored fields read without a map key, and comparisons or bit
    /// operations of those.
    pub(super) fn eager_ok(&self, e: &Expr) -> bool {
        fn plain(e: &Expr) -> bool {
            match e {
                Expr::Field { base, .. } => plain(base),
                Expr::Ident { .. } => true,
                _ => false,
            }
        }
        match e {
            Expr::Lit { .. } => true,
            Expr::Field {
                root: Some(_), ty, ..
            } => plain(e) && self.map_place(e).is_none() && !self.is_dynamic(*ty),
            Expr::Ident {
                sym: Some(sym),
                builtin: None,
                ..
            } => !self.checked.syms[*sym].storage,
            Expr::Call {
                builtin: Some(b),
                args,
                ..
            } => {
                args.is_empty()
                    && matches!(
                        b,
                        Builtin::Sender
                            | Builtin::Value
                            | Builtin::TxOrigin
                            | Builtin::SelfAddr
                            | Builtin::BlockTimestamp
                            | Builtin::BlockNumber
                            | Builtin::ChainId
                    )
            }
            Expr::Unary {
                op: UnOp::Not,
                expr,
                ..
            } => self.eager_ok(expr),
            Expr::Binary {
                op, left, right, ..
            } => {
                (op.is_cmp()
                    || matches!(
                        op,
                        BinOp::And | BinOp::Or | BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor
                    ))
                    && self.eager_ok(left)
                    && self.eager_ok(right)
            }
            _ => false,
        }
    }

    /// Each compiled function's label, and how many words it returns on the stack.
    pub(super) fn func_leaves_by_label(&self) -> HashMap<u32, usize> {
        self.funcs.values().map(|f| (f.label, f.leaves)).collect()
    }

    /// Moves memory words that only one body, or one function compiled once, uses, and whose
    /// address never escapes, onto the stack.
    pub(super) fn promote(&mut self) {
        let mask = (1u32 << REGION_SHIFT) - 1;
        let mut escapes = vec![false; self.spaces.len()];
        for (i, inst) in self.code.iter().enumerate() {
            let Inst::Mem(addr) = inst else { continue };
            let ix = (addr >> REGION_SHIFT) as usize - 1;
            let direct = matches!(self.code.get(i + 1), Some(Inst::Op(MLOAD | MSTORE)));
            if !direct || !(addr & mask).is_multiple_of(32) {
                escapes[ix] = true;
            }
        }
        let spaces: Vec<bool> = self
            .spaces
            .iter()
            .zip(&escapes)
            .enumerate()
            .map(|(ix, (space, escaped))| {
                !escaped
                    && (matches!(&space.users, Users::Bodies(_))
                        || self.shared_temps.contains(&ix)
                        || matches!(&space.users, Users::Shared(ids) if ids.len() == 1 && ids.iter().all(|&i| i >= FUNC_CTX)))
            })
            .collect();
        let tracked = |addr: u32| spaces[(addr >> REGION_SHIFT) as usize - 1];
        self.read_calldata(&tracked);
        let mut calls: asm::Calls = self
            .subs
            .iter()
            .map(|&(sub, label, _)| {
                let effect = match sub {
                    Sub::JournalLoad => (1, 1),
                    Sub::JournalStore => (2, 0),
                    Sub::JournalFlush => (0, 0),
                    Sub::AllocBlob => (1, 1),
                    Sub::BytesSlice(end) => (2 + usize::from(end), 1),
                    Sub::StoreBytes => (2, 0),
                    Sub::LoadBytes => (1, 1),
                    Sub::RevertData => (0, 1),
                    Sub::MulDiv => (3, 1),
                    Sub::CheckedMul | Sub::CheckedExp(_) => (2, 1),
                    Sub::DecodeList(_) => (1, 1),
                    Sub::LoadList(..) | Sub::LoadRecords(..) => (2, 1),
                    Sub::StoreList(..) | Sub::StoreRecords(..) | Sub::StorePacked(..) => (3, 0),
                    Sub::LoadPacked(..) => (2, 1),
                    Sub::ZeroSlots(..) | Sub::ClearElems(..) => (2, 0),
                    Sub::LoadSlotBytes(..) => (1, 1),
                    Sub::StoreSlotBytes(..) => (2, 0),
                    Sub::QueuePush => (3, 1),
                    Sub::ListHead => (1, 1),
                    Sub::RevertAbi => (3, 0),
                    Sub::ShortBlob => (1, 1),
                    Sub::BlobsAbi => (1, 1),
                    Sub::DecodeBytes | Sub::CopyCdBytes => (1, 1),
                    Sub::StoredTail => (3, 1),
                    Sub::BlobsEq => (2, 1),
                    Sub::BytesEq => (2, 1),
                    Sub::BytesValue(_) => (2, 1),
                    Sub::Base64Encode => (3, 1),
                    Sub::Base64Decode => (1, 1),
                    Sub::DecimalString(_) => (1, 1),
                    Sub::HexString => (2, 1),
                    Sub::ChecksumString => (1, 1),
                    Sub::TreeEnc(_) => (2, 1),
                    Sub::TreeDec(..) => (2, 0),
                    Sub::TreeCdEnc(_) => (2, 1),
                };
                (label, effect)
            })
            .collect();
        for f in self.funcs.values() {
            calls.insert(f.label, (0, f.leaves));
        }
        asm::promote(
            &mut self.code,
            &tracked,
            &calls,
            self.plan.tight,
            self.plan.hold_dups,
            self.plan.sink,
        );
        // String helpers reach storage through a slot they are given, and others write
        // slots they are given, which may be a fixed list's.
        let opaque: std::collections::HashSet<u32> = self
            .funcs
            .values()
            .map(|f| f.label)
            .chain(
                self.subs
                    .iter()
                    .filter(|(sub, _, _)| matches!(sub, Sub::LoadBytes) || sub.writes_storage())
                    .map(|&(_, label, _)| label),
            )
            .collect();
        asm::forward_storage(&mut self.code, &calls, &opaque);
    }

    /// A word written only by `CALLDATALOAD` of a constant offset is read from calldata instead.
    /// Calldata cannot change, and the one store precedes every load of its word. A word
    /// the read also shifts stays when it is loaded more than once.
    fn read_calldata(&mut self, tracked: &dyn Fn(u32) -> bool) {
        let mut stores: HashMap<u32, Vec<usize>> = HashMap::new();
        let mut first_load: HashMap<u32, usize> = HashMap::new();
        let mut loads: HashMap<u32, usize> = HashMap::new();
        for i in 0..self.code.len() {
            let Inst::Mem(addr) = self.code[i] else {
                continue;
            };
            if !tracked(addr) {
                continue;
            }
            match self.code.get(i + 1) {
                Some(Inst::Op(MSTORE)) => stores.entry(addr).or_default().push(i),
                Some(Inst::Op(MLOAD)) => {
                    first_load.entry(addr).or_insert(i);
                    *loads.entry(addr).or_default() += 1;
                }
                _ => {}
            }
        }
        // A word read from calldata, maybe shifted into Lithe's alignment, then stored.
        let read_at = |code: &[Inst], i: usize| -> Option<Vec<Inst>> {
            match code.get(i.checked_sub(4)?..i)? {
                [Inst::Push(off), Inst::Op(CALLDATALOAD), Inst::Push(shift), Inst::Op(SHR)] => {
                    Some(vec![
                        Inst::Push(*off),
                        Inst::Op(CALLDATALOAD),
                        Inst::Push(*shift),
                        Inst::Op(SHR),
                    ])
                }
                [_, _, Inst::Push(off), Inst::Op(CALLDATALOAD)] => {
                    Some(vec![Inst::Push(*off), Inst::Op(CALLDATALOAD)])
                }
                _ => None,
            }
        };
        let mut from: HashMap<u32, Vec<Inst>> = HashMap::new();
        for (addr, at) in &stores {
            let [i] = at.as_slice() else { continue };
            if first_load.get(addr).is_some_and(|l| l < i) {
                continue;
            }
            // A read that also shifts costs more than a load from the word it was stored in.
            if let Some(read) = read_at(&self.code, *i)
                .filter(|read| read.len() < 4 || loads.get(addr).is_none_or(|&n| n < 2))
            {
                from.insert(*addr, read);
            }
        }
        if from.is_empty() {
            return;
        }
        let mut out: Vec<Inst> = Vec::with_capacity(self.code.len());
        let mut i = 0;
        while i < self.code.len() {
            if let (Inst::Mem(addr), Some(Inst::Op(op))) = (self.code[i], self.code.get(i + 1)) {
                if let Some(read) = from.get(&addr) {
                    if *op == MSTORE {
                        // The store goes, and the read just before it.
                        out.truncate(out.len() - read.len());
                        i += 2;
                        continue;
                    }
                    if *op == MLOAD {
                        out.extend_from_slice(read);
                        i += 2;
                        continue;
                    }
                }
            }
            out.push(self.code[i]);
            i += 1;
        }
        self.code = out;
    }

    /// Places every used region, hottest first. Regions no body shares can overlap.
    pub(super) fn resolve(&mut self) -> Result<Vec<Inst>, Error> {
        let mask = (1u32 << REGION_SHIFT) - 1;
        let mut offsets: Vec<Vec<u64>> = vec![Vec::new(); self.spaces.len()];
        for inst in &self.code {
            if let Inst::Mem(addr) = inst {
                offsets[(addr >> REGION_SHIFT) as usize - 1].push(u64::from(addr & mask));
            }
        }
        for (space, offs) in self.spaces.iter_mut().zip(&offsets) {
            space.heat = offs.len() as u64;
        }
        let mut order: Vec<usize> = (0..self.spaces.len())
            .filter(|&i| self.spaces[i].heat > 0 && self.spaces[i].region != Region::Blob)
            .collect();
        let words = |s: &Space| u64::from(s.size.max(s.extent).div_ceil(32).max(1));
        order.sort_by(|&a, &b| {
            let (sa, sb) = (&self.spaces[a], &self.spaces[b]);
            (sb.heat * words(sa))
                .cmp(&(sa.heat * words(sb)))
                .then(sb.heat.cmp(&sa.heat))
                .then(a.cmp(&b))
        });
        order.sort_by_key(|&i| self.spaces[i].region != Region::Base64);
        // Each user and the functions that can run while it does.
        let mut reach: HashMap<usize, std::collections::HashSet<usize>> = HashMap::new();
        for &(from, to) in &self.func_calls {
            reach.entry(from).or_default().insert(to);
        }
        loop {
            let mut grew = false;
            let keys: Vec<usize> = reach.keys().copied().collect();
            for k in keys {
                let next: Vec<usize> = reach[&k]
                    .iter()
                    .filter_map(|t| reach.get(t))
                    .flatten()
                    .copied()
                    .filter(|t| !reach[&k].contains(t))
                    .collect();
                grew |= !next.is_empty();
                reach.get_mut(&k).expect("key").extend(next);
            }
            if !grew {
                break;
            }
        }
        let anywhere = reach.get(&usize::MAX).cloned().unwrap_or_default();
        let runs = |a: usize, b: usize| reach.get(&a).is_some_and(|r| r.contains(&b));
        let together = |a: usize, b: usize| {
            a == b || anywhere.contains(&a) || anywhere.contains(&b) || runs(a, b) || runs(b, a)
        };
        let frames = self.plan.frames;
        let clashes = |x: &Users, y: &Users| match (x, y) {
            (Users::Bodies(a), Users::Bodies(b)) => a.intersection(b).next().is_some(),
            (Users::Bodies(_), Users::Shared(_)) | (Users::Shared(_), Users::Bodies(_))
                if !frames =>
            {
                true
            }
            (Users::Bodies(a) | Users::Shared(a), Users::Bodies(b) | Users::Shared(b)) => {
                a.iter().any(|&p| b.iter().any(|&q| together(p, q)))
            }
            (Users::Nobody, _) | (_, Users::Nobody) => false,
            _ => true,
        };
        let n = self.spaces.len();
        let mut clash = vec![false; n * n];
        for &a in &order {
            for &b in &order {
                clash[a * n + b] = clashes(&self.spaces[a].users, &self.spaces[b].users);
            }
        }
        let lens: Vec<u64> = self.spaces.iter().map(|s| words(s) * 32).collect();
        let push = |a: u64| u64::from(a != 0) + u64::from(64 - a.leading_zeros()).div_ceil(8);
        let cost_at = |i: usize, at: u64| offsets[i].iter().map(|&o| push(at + o)).sum::<u64>();
        // A region's pushes cost the least at address 0, and never less higher up.
        let floor: Vec<u64> = (0..n).map(|i| cost_at(i, 0)).collect();
        let mut listed = vec![false; n];
        for &i in &order {
            listed[i] = true;
        }
        let unplaced: u64 = (0..n).filter(|&i| !listed[i]).map(|i| floor[i]).sum();
        let lowest: u64 = order.iter().map(|&i| floor[i]).sum();
        // Each region goes to the lowest address no clashing region already holds, the first
        // `keep` where `prev` has them. A layout whose pushes cost `best` or more, or that puts
        // a region past `limit`'s highest start or end, is no use.
        let place =
            |order: &[usize], prev: &[u64], keep: usize, best: u64, limit: &[(u64, u64)]| {
                let mut base = vec![0u64; n];
                // By start address.
                let mut placed: Vec<(u64, u64, usize)> = Vec::with_capacity(order.len());
                let (mut top, mut cost, mut rest) = (0u64, unplaced, lowest);
                for (k, &i) in order.iter().enumerate() {
                    let len = lens[i];
                    let at = if k < keep {
                        prev[i]
                    } else {
                        let mut at = 0u64;
                        for &(start, end, j) in &placed {
                            if start >= at + len {
                                break;
                            }
                            if end > at && clash[i * n + j] {
                                at = end;
                            }
                        }
                        at
                    };
                    if at > limit[i].0 || at + len > limit[i].1 {
                        return None;
                    }
                    cost += cost_at(i, at);
                    rest -= floor[i];
                    if cost + rest >= best {
                        return None;
                    }
                    base[i] = at;
                    top = top.max(at + len);
                    placed.insert(placed.partition_point(|&(s, ..)| s < at), (at, at + len, i));
                }
                Some((base, top, cost))
            };
        // Memory a body touches costs it gas to expand: the highest end among its regions.
        let bodies: Vec<usize> = self
            .spaces
            .iter()
            .filter_map(|s| match &s.users {
                Users::Bodies(ids) | Users::Shared(ids) => Some(ids.iter().copied()),
                _ => None,
            })
            .flatten()
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect();
        // Hot words are worth the most below 0x100, where a one-byte push reaches them. A
        // region only its bodies use can share that space with other bodies' regions, so the
        // order by heat alone can waste it: move a region to the front or back when that shrinks
        // the pushes and grows no body's memory.
        let pinned = order
            .first()
            .map_or(0, |&i| usize::from(self.spaces[i].region == Region::Base64));
        let (mut base, mut top, mut best) =
            place(&order, &[], 0, u64::MAX, &vec![(u64::MAX, u64::MAX); n]).expect("unbounded");
        let mut peak = vec![0u64; bodies.len() + 1];
        for &i in &order {
            let end = base[i] + lens[i];
            match &self.spaces[i].users {
                Users::Bodies(ids) | Users::Shared(ids) => {
                    for id in ids {
                        let b = bodies.binary_search(id).expect("listed");
                        peak[b] = peak[b].max(end);
                    }
                }
                Users::Nobody => {}
                Users::Everyone => {
                    for p in &mut peak {
                        *p = (*p).max(end);
                    }
                }
            }
        }
        // No region may end past the memory of a body that uses it. Regions code shared
        // between bodies uses never move up: any body may touch them.
        let limit: Vec<(u64, u64)> = (0..n)
            .map(|i| match &self.spaces[i].users {
                Users::Bodies(ids) | Users::Shared(ids) => (
                    match self.spaces[i].users {
                        Users::Shared(_) => base[i],
                        _ => u64::MAX,
                    },
                    ids.iter()
                        .map(|id| peak[bodies.binary_search(id).expect("listed")])
                        .min()
                        .unwrap_or(u64::MAX),
                ),
                Users::Nobody => (u64::MAX, u64::MAX),
                Users::Everyone => (base[i], peak.iter().copied().min().unwrap_or(u64::MAX)),
            })
            .collect();
        for _ in 0..4 {
            let mut better = false;
            for k in pinned..order.len() {
                for to_front in [true, false] {
                    let mut trial = order.clone();
                    let i = trial.remove(k);
                    // The regions ahead of the moved one keep their places.
                    let keep = if to_front {
                        trial.insert(pinned, i);
                        pinned
                    } else {
                        trial.push(i);
                        k
                    };
                    if let Some((b, t, c)) = place(&trial, &base, keep, best, &limit) {
                        (order, base, top, best, better) = (trial, b, t, c, true);
                    }
                }
            }
            if !better {
                break;
            }
        }
        for (i, space) in self.spaces.iter().enumerate() {
            if space.region == Region::Blob {
                base[i] = top;
            }
        }
        let mut out = Vec::with_capacity(self.code.len());
        for inst in std::mem::take(&mut self.code) {
            out.push(match inst {
                Inst::Mem(addr) => {
                    let ix = (addr >> REGION_SHIFT) as usize;
                    if ix == 0 || ix > self.spaces.len() {
                        return Err(error(0, 0, "internal: bad memory address"));
                    }
                    Inst::Push(Word::from_u64(base[ix - 1] + u64::from(addr & mask)))
                }
                other => other,
            });
        }
        Ok(out)
    }
}
