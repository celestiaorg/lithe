//! Walks over the checked program's statements and expressions, into the functions they
//! call.

use super::*;

impl<'a> Gen<'a> {
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
            Expr::Unary { expr, .. } | Expr::Convert { expr, .. } => self.expr_any(expr, bad, seen),
            Expr::Field { base, .. } => self.expr_any(base, bad, seen),
            Expr::Index { base, index, .. } => {
                self.expr_any(base, bad, seen) || self.expr_any(index, bad, seen)
            }
            Expr::Call {
                args, base, callee, ..
            } => {
                callee.is_some_and(|idx| {
                    (self.calls_back_stateful(idx) && bad(Node::Stmt(&self.queued_call)))
                        || self.func_any(idx, bad, seen)
                }) || base.as_ref().is_some_and(|b| self.expr_any(b, bad, seen))
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
}
