//! The expressions only spec blocks can write: `old.` and `new.` paths, `sum`, `count`, and
//! `forall`. `crate::spec` checks spec blocks as functions no code calls; these are their
//! types.

use super::*;

impl Checker {
    pub(super) fn check_spec_form(
        &mut self,
        span: Span,
        kind: Builtin,
        args: &mut [Expr],
        ty: &mut usize,
    ) -> Result<(), Error> {
        if !self.in_spec {
            return Err(error(
                span,
                "only a spec block reads `old.`, `new.`, `sum`, `count`, and `forall`",
            ));
        }
        match kind {
            Builtin::SpecState(_) => {
                self.check_expr(&mut args[0])?;
                *ty = args[0].ty();
            }
            Builtin::SpecSum | Builtin::SpecCount => {
                let word = if kind == Builtin::SpecSum {
                    "sum"
                } else {
                    "count"
                };
                if args.len() != 1 {
                    return Err(error(span, format!("`{word}` takes one map")));
                }
                let expect = self.expect.take();
                self.check_expr(&mut args[0])?;
                self.expect = expect;
                let map = self.peel(args[0].ty());
                if self.types[map].kind != TyKind::Map {
                    return Err(error(args[0].span(), format!("`{word}` takes a map")));
                }
                let val = self.types[map].right.unwrap_or(TY_UNIT);
                let numeric = matches!(
                    self.types[self.peel(val)].kind,
                    TyKind::Uint | TyKind::Int | TyKind::Wei
                );
                *ty = if kind == Builtin::SpecCount {
                    if !is_word(self.types[self.peel(val)].kind) {
                        return Err(error(
                            args[0].span(),
                            "`count` counts a map whose values are words",
                        ));
                    }
                    TY_UINT
                } else if numeric {
                    val
                } else {
                    return Err(error(
                        args[0].span(),
                        "`sum` adds a map whose values are numbers",
                    ));
                };
            }
            Builtin::SpecForall => {
                let [binder, ty_name, body] = args else {
                    return Err(error(span, "expected `forall x : T . e`"));
                };
                let Expr::Ident {
                    name: tname,
                    span: tspan,
                    ..
                } = ty_name
                else {
                    return Err(error(span, "expected `forall x : T . e`"));
                };
                let bound = self.build(&TypeRef::Name {
                    span: *tspan,
                    name: *tname,
                })?;
                let Expr::Ident {
                    name,
                    sym,
                    ty: bty,
                    span: bspan,
                    ..
                } = binder
                else {
                    return Err(error(span, "expected `forall x : T . e`"));
                };
                let parent = self.scope;
                self.scope = self.push_scope(parent);
                let id = self.add_sym(Sym {
                    ty: bound,
                    mutable: false,
                    storage: false,
                    slot: 0,
                    span: 0,
                });
                self.define(*bspan, &name.to_string(), id)?;
                *sym = Some(id);
                *bty = bound;
                let expect = self.expect.take();
                let checked = self.check_expr(body);
                self.expect = expect;
                self.scope = parent;
                checked?;
                if self.peel(body.ty()) != TY_BOOL {
                    return Err(error(body.span(), "`forall` needs a `bool`"));
                }
                *ty = TY_BOOL;
            }
            _ => unreachable!("not a spec form"),
        }
        Ok(())
    }
}
