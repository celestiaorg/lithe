//! The contracts a contract creates: their code, built once and kept after its own.

use super::*;

impl<'a> Gen<'a> {
    /// An expression that reads only memory and fixed context, and cannot fail.
    pub(super) fn inert(&self, e: &Expr) -> bool {
        let fixed = |b: &Option<Builtin>| {
            matches!(
                b,
                Some(
                    Builtin::Sender
                        | Builtin::Value
                        | Builtin::Selector
                        | Builtin::TxOrigin
                        | Builtin::ChainId
                        | Builtin::SelfAddr
                        | Builtin::Some
                        | Builtin::None
                        | Builtin::Ctor(_)
                )
            )
        };
        match e {
            Expr::Lit { .. } => true,
            Expr::Ident { sym: Some(s), .. } => !self.checked.syms[*s].storage,
            Expr::Ident { builtin, .. } => fixed(builtin),
            Expr::Field { base, root, .. } => {
                root.is_none_or(|r| !self.checked.syms[r].storage) && self.inert(base)
            }
            Expr::Call {
                builtin: Some(Builtin::Cast),
                args,
                ty,
                ..
            } => {
                let dst = &self.checked.types[self.peel_nominal(*ty)];
                let widens = args.first().is_some_and(|a| {
                    self.checked.types[self.peel_nominal(a.ty())].kind != TyKind::Int
                }) && matches!(dst.bits, 0 | 256)
                    && dst.kind != TyKind::Int;
                let numeric = matches!(
                    dst.kind,
                    TyKind::Uint | TyKind::Int | TyKind::Wei | TyKind::Timestamp
                );
                (widens || !numeric) && args.iter().all(|a| self.inert(a))
            }
            Expr::Call { builtin, args, .. } => {
                fixed(builtin) && args.iter().all(|a| self.inert(a))
            }
            Expr::Unary { op, expr, .. } => *op != UnOp::Neg && self.inert(expr),
            Expr::Binary {
                op, left, right, ..
            } => {
                (op.is_cmp()
                    || matches!(
                        op,
                        BinOp::And
                            | BinOp::Or
                            | BinOp::BitAnd
                            | BinOp::BitOr
                            | BinOp::BitXor
                            | BinOp::Shl
                            | BinOp::Shr
                    ))
                    && self.inert(left)
                    && self.inert(right)
            }
            Expr::Case { scrut, arms, .. } => {
                self.inert(scrut)
                    && arms
                        .iter()
                        .all(|a| a.stmts.is_empty() && self.inert(&a.expr))
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                elems.iter().all(|x| self.inert(x))
            }
            Expr::Record { fields, .. } => fields.iter().all(|(_, x)| self.inert(x)),
            _ => false,
        }
    }

    /// The creation code of another contract of this file or its imports, embedded once.
    /// Its place in this code is a placeholder word until the code's length is known.
    /// Creation code keeps it ahead of its end, where its arguments begin.
    pub(super) fn peer_code(
        &mut self,
        name: &str,
        line: u32,
        col: u32,
    ) -> Result<(Word, u64), Error> {
        if let Some((marker, code)) = self
            .data
            .iter()
            .find(|(_, _, have)| have == name)
            .map(|(m, c, _)| (*m, c.len()))
        {
            return Ok((marker, code as u64));
        }
        let code = self.peer_creation(name, line, col)?;
        let marker = self.data_marker();
        let len = code.len() as u64;
        let end = self
            .init
            .then(|| self.data.iter().position(|(m, ..)| *m == self.code_end));
        let at = end.flatten().unwrap_or(self.data.len());
        self.data.insert(at, (marker, code, name.to_string()));
        Ok((marker, len))
    }

    /// A peer's creation code, compiled once however often it is embedded or hashed.
    pub(super) fn peer_creation(
        &mut self,
        name: &str,
        line: u32,
        col: u32,
    ) -> Result<Vec<u8>, Error> {
        if let Some(code) = self.peer_built.get(name) {
            return Ok(code.clone());
        }
        let opts = &self.shape.opts;
        let builds = &self.checked.peer_builds;
        let cached = builds
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .iter()
            .find(|(peer, o, ..)| peer == name && o == opts)
            .map(|(_, _, code, needs)| (code.clone(), needs.clone()));
        let (code, needs) = match cached {
            Some(built) => built,
            None => {
                let built = self.peer_build(name, line, col)?;
                builds.lock().unwrap_or_else(|e| e.into_inner()).push((
                    name.to_string(),
                    opts.clone(),
                    built.0.clone(),
                    built.1.clone(),
                ));
                built
            }
        };
        self.needs.extend(needs);
        self.peer_built.insert(name.to_string(), code.clone());
        Ok(code)
    }

    /// A peer's creation code and what must be deployed before it.
    fn peer_build(&self, name: &str, line: u32, col: u32) -> Result<(Vec<u8>, Vec<Facet>), Error> {
        let own = self.checked.prog.contract_name.clone();
        let peers = &self.checked.prog.peers;
        let Some(peer) = peers
            .iter()
            .find(|p| p.contract_name.as_deref() == Some(name))
        else {
            return Err(error(
                line,
                col,
                format!("`{name}` is not another contract of this file or its imports"),
            ));
        };
        // A created contract of this file may create the others, but never itself or its
        // creator. An imported one keeps what its own file lets it create.
        let mut unit = peer.clone();
        if peer.origin == self.checked.prog.origin {
            unit.peers = peers
                .iter()
                .filter(|p| p.contract_name.as_deref() != Some(name) && p.contract_name != own)
                .cloned()
                .collect();
        }
        let byte_gas = asm::GAS_PER_BYTE + asm::DEPOSIT_GAS / asm::CREATED_RUNS;
        let built = asm::with_byte_gas(byte_gas, || {
            crate::split::build(
                &crate::check::check(unit, self.shape.opts.evm)?,
                name,
                &self.shape.opts,
            )
        })?;
        Ok((built.creation.clone(), built.prerequisites()))
    }
}
