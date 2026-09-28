use super::*;

pub(super) fn require_payable(funcs: &[Func]) -> Result<(), Error> {
    let mut reads = vec![false; funcs.len()];
    let mut calls = vec![Vec::new(); funcs.len()];
    for (i, func) in funcs.iter().enumerate() {
        let mut callees = Vec::new();
        reads[i] = func_reads_value(func, &mut callees);
        calls[i] = callees;
    }
    loop {
        let mut changed = false;
        for i in 0..funcs.len() {
            if reads[i] {
                continue;
            }
            if calls[i].iter().any(|callee| reads[*callee]) {
                reads[i] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for (func, reads_value) in funcs.iter().zip(reads) {
        if !reads_value {
            continue;
        }
        match func.kind {
            ItemKind::Entry if !func.payable => {
                return Err(error(
                    func.line,
                    func.col,
                    format!(
                        "external function `{}` reads `Evm.value()`; write `external payable function`",
                        func.name
                    ),
                ));
            }
            ItemKind::Deploy if !func.payable => {
                return Err(error(
                    func.line,
                    func.col,
                    "`deploy` reads `Evm.value()`; write `payable deploy`",
                ));
            }
            ItemKind::Fallback if !func.payable => {
                return Err(error(
                    func.line,
                    func.col,
                    "`fallback` reads `Evm.value()`; write `payable fallback`",
                ));
            }
            ItemKind::View => {
                return Err(error(
                    func.line,
                    func.col,
                    format!("view `{}` cannot read `Evm.value()`", func.name),
                ));
            }
            _ => {}
        }
    }
    Ok(())
}

fn func_reads_value(func: &Func, calls: &mut Vec<usize>) -> bool {
    let mut reads = false;
    for stmt in &func.stmts {
        reads |= stmt_reads_value(stmt, calls);
    }
    if let Some(tail) = &func.tail {
        reads |= expr_reads_value(tail, calls);
    }
    reads
}

fn stmt_reads_value(stmt: &Stmt, calls: &mut Vec<usize>) -> bool {
    match stmt {
        Stmt::Const { expr, .. } | Stmt::Var { expr, .. } | Stmt::Assign { expr, .. } => {
            expr_reads_value(expr, calls)
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            expr_reads_value(cond, calls)
                || then_body.iter().any(|stmt| stmt_reads_value(stmt, calls))
                || else_body.iter().any(|stmt| stmt_reads_value(stmt, calls))
        }
        Stmt::Assert { cond, reason, .. } => {
            expr_reads_value(cond, calls) || reason_reads_value(reason, calls)
        }
        Stmt::Fail { reason, .. } => reason_reads_value(reason, calls),
        Stmt::AssignTuple { expr, .. } => expr_reads_value(expr, calls),
        Stmt::For {
            iter, until, body, ..
        } => {
            let iter_reads = match iter {
                ForIter::Range { lo, hi } => {
                    expr_reads_value(lo, calls) || expr_reads_value(hi, calls)
                }
                ForIter::List(xs) => expr_reads_value(xs, calls),
            };
            iter_reads
                || until.as_ref().is_some_and(|c| expr_reads_value(c, calls))
                || body.iter().any(|stmt| stmt_reads_value(stmt, calls))
        }
        Stmt::Call { expr, .. } | Stmt::Defer { expr, .. } => {
            let mut reads = expr_reads_value(expr, calls);
            if let Stmt::Defer {
                value, gas, then, ..
            } = stmt
            {
                for value in value.iter().chain(gas) {
                    reads |= expr_reads_value(value, calls);
                }
                if let Some(then) = then {
                    reads |= then
                        .arms()
                        .flat_map(|arm| &arm.stmts)
                        .any(|stmt| stmt_reads_value(stmt, calls));
                }
            }
            reads
        }
        Stmt::Emit { fields, .. } => fields.iter().any(|(_, expr)| expr_reads_value(expr, calls)),
        Stmt::Skip => false,
    }
}

fn reason_reads_value(reason: &Raised, calls: &mut Vec<usize>) -> bool {
    match &reason.form {
        RaisedForm::Unit => false,
        RaisedForm::Positional(expr) => expr_reads_value(expr, calls),
        RaisedForm::Fields(fields) => fields.iter().any(|(_, expr)| expr_reads_value(expr, calls)),
    }
}

fn expr_reads_value(expr: &Expr, calls: &mut Vec<usize>) -> bool {
    match expr {
        Expr::Ident {
            builtin: Some(Builtin::Value),
            ..
        } => true,
        Expr::Ident { .. } | Expr::Lit { .. } => false,
        Expr::Query {
            expr: base, gas, ..
        } => {
            expr_reads_value(base, calls)
                || gas.as_ref().is_some_and(|g| expr_reads_value(g, calls))
        }
        Expr::Field { base, .. } | Expr::Unary { expr: base, .. } => expr_reads_value(base, calls),
        Expr::Index { base, index, .. } => {
            expr_reads_value(base, calls) || expr_reads_value(index, calls)
        }
        Expr::Call {
            args,
            base,
            callee,
            builtin,
            ..
        } => {
            if *builtin == Some(Builtin::Value) {
                return true;
            }
            if let Some(idx) = callee {
                if !calls.contains(idx) {
                    calls.push(*idx);
                }
            }
            args.iter().any(|arg| expr_reads_value(arg, calls))
                || base
                    .as_ref()
                    .is_some_and(|base| expr_reads_value(base, calls))
        }
        Expr::Case { scrut, arms, .. } => {
            expr_reads_value(scrut, calls)
                || arms.iter().any(|arm| {
                    arm.stmts.iter().any(|stmt| stmt_reads_value(stmt, calls))
                        || expr_reads_value(&arm.expr, calls)
                })
        }
        Expr::Binary { left, right, .. } => {
            expr_reads_value(left, calls) || expr_reads_value(right, calls)
        }
        Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
            elems.iter().any(|elem| expr_reads_value(elem, calls))
        }
        Expr::Record { fields, .. } => fields.iter().any(|(_, expr)| expr_reads_value(expr, calls)),
    }
}
