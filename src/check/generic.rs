use super::*;

impl Checker {
    pub(super) fn generic_call(&self, base: &Option<Box<Expr>>, name: &str) -> Option<GenericCall> {
        if let Some(expr) = base {
            let Expr::Ident {
                name: module,
                sym: None,
                ..
            } = expr.as_ref()
            else {
                return None;
            };
            if let Some(index) = self.generic_module(module) {
                if self.modules[index]
                    .funcs
                    .iter()
                    .any(|func| func.name == name)
                {
                    return Some(GenericCall {
                        module: Some(index),
                        func: name.to_string(),
                        qualified: format!("{module}.{name}"),
                    });
                }
            }
            let qualified = format!("{module}.{name}");
            if self.generic_fns.iter().any(|func| func.name == qualified) {
                return Some(GenericCall {
                    module: None,
                    func: qualified.clone(),
                    qualified,
                });
            }
            return None;
        }
        if let Some(module) = &self.module_name {
            if let Some(index) = self.generic_module(module) {
                if self.modules[index]
                    .funcs
                    .iter()
                    .any(|func| func.name == name)
                {
                    return Some(GenericCall {
                        module: Some(index),
                        func: name.to_string(),
                        qualified: format!("{module}.{name}"),
                    });
                }
            }
        }
        if let Some(module) = &self.spec_module {
            if let Some(index) = self.generic_module(module) {
                if self.modules[index]
                    .funcs
                    .iter()
                    .any(|func| func.name == name)
                {
                    return Some(GenericCall {
                        module: Some(index),
                        func: name.to_string(),
                        qualified: format!("{module}.{name}"),
                    });
                }
            }
        }
        if self.generic_fns.iter().any(|func| func.name == name) {
            return Some(GenericCall {
                module: None,
                func: name.to_string(),
                qualified: name.to_string(),
            });
        }
        if let Some(module) = &self.module_name {
            let qualified = format!("{module}.{name}");
            if self.generic_fns.iter().any(|func| func.name == qualified) {
                return Some(GenericCall {
                    module: None,
                    func: qualified.clone(),
                    qualified,
                });
            }
        }
        None
    }

    /// Among overloads, the one taking as many arguments as the call passes, or of several,
    /// the one whose parameters the arguments' types match. The call is renamed to it.
    pub(super) fn pick_overload(
        &mut self,
        line: u32,
        col: u32,
        base: &Option<Box<Expr>>,
        name: &mut String,
        args: &mut [Expr],
    ) -> Result<(), Error> {
        let keys = match base.as_deref() {
            Some(Expr::Ident { name: alias, .. }) => vec![format!("{alias}.{name}")],
            Some(_) => return Ok(()),
            None => [&self.module_name, &self.spec_module]
                .into_iter()
                .flatten()
                .map(|module| format!("{module}.{name}"))
                .chain([name.clone()])
                .collect(),
        };
        let Some(group) = keys.iter().find_map(|key| self.overloads.get(key)).cloned() else {
            return Ok(());
        };
        let candidates: Vec<(String, Overload)> = group
            .into_iter()
            .map(|full| {
                let overload = self.overload(&full);
                (full, overload)
            })
            .filter(|(_, overload)| overload.arity() == args.len())
            .collect();
        let chosen = match candidates.as_slice() {
            [] => {
                let n = args.len();
                let s = if n == 1 { "" } else { "s" };
                return Err(error(
                    line,
                    col,
                    format!("no overload of `{name}` takes {n} argument{s}"),
                ));
            }
            [(full, _)] => full.clone(),
            several => {
                let saved = self.expect;
                self.expect = None;
                for arg in args.iter_mut() {
                    self.check_expr(arg)?;
                }
                self.expect = saved;
                let mut fitting = Vec::new();
                for (full, overload) in several {
                    if self.fits(overload, args) {
                        fitting.push(full.clone());
                    }
                }
                match fitting.as_slice() {
                    [one] => one.clone(),
                    [] => {
                        return Err(error(
                            line,
                            col,
                            format!("no overload of `{name}` takes these arguments"),
                        ));
                    }
                    _ => {
                        return Err(error(
                            line,
                            col,
                            format!("more than one overload of `{name}` takes these arguments"),
                        ));
                    }
                }
            }
        };
        let suffix = &chosen[chosen.rfind('@').unwrap_or(chosen.len())..];
        name.push_str(suffix);
        Ok(())
    }

    /// An overload's parameters. A template is looked up first: a copy made of it takes its name.
    fn overload(&self, full: &str) -> Overload {
        if let Some(func) = self.generic_fns.iter().find(|func| func.name == full) {
            return Overload::Template(None, func.clone());
        }
        if let Some((module, own)) = full.rsplit_once('.') {
            if let Some(index) = self.generic_module(module) {
                if let Some(func) = self.modules[index]
                    .funcs
                    .iter()
                    .find(|func| func.name == own)
                {
                    return Overload::Template(Some(index), func.clone());
                }
            }
        }
        let i = self
            .fn_names
            .iter()
            .position(|n| n == full)
            .expect("an overload is a function");
        Overload::Sig(self.sigs[i].params.iter().map(|(ty, _)| *ty).collect())
    }

    fn fits(&mut self, overload: &Overload, args: &[Expr]) -> bool {
        match overload {
            Overload::Sig(params) => params
                .iter()
                .zip(args)
                .all(|(&param, arg)| self.same(arg.ty(), param)),
            Overload::Template(module, func) => {
                let params = match module {
                    Some(index) => self.modules[*index].params.clone(),
                    None => func.type_params.clone(),
                };
                let mut env = HashMap::new();
                for (param, arg) in func.params.iter().zip(args) {
                    let (line, col) = (arg.line(), arg.col());
                    if self
                        .unify(&param.ty, arg.ty(), *module, &params, &mut env, line, col)
                        .is_err()
                    {
                        return false;
                    }
                }
                true
            }
        }
    }

    fn generic_module(&self, name: &str) -> Option<usize> {
        self.modules
            .iter()
            .position(|module| module.name == name && !module.params.is_empty())
    }

    pub(super) fn specialize(
        &mut self,
        line: u32,
        col: u32,
        target: GenericCall,
        args: &mut Vec<Expr>,
        callee: &mut Option<usize>,
        ty: &mut usize,
    ) -> Result<(), Error> {
        // A call checked again, as another specialized call's argument is, keeps its copy.
        if let Some(idx) = *callee {
            *ty = self.sigs[idx].ret;
            return Ok(());
        }
        let template = self.template(&target)?;
        if args.len() != template.params.len() {
            let n = template.params.len();
            return Err(error(
                line,
                col,
                format!(
                    "`{}` expects {n} argument{}",
                    target.qualified,
                    if n == 1 { "" } else { "s" }
                ),
            ));
        }
        let params = match target.module {
            Some(index) => self.modules[index].params.clone(),
            None => template.type_params.clone(),
        };
        // A literal takes its type from its parameter, once the other arguments have
        // settled the type parameters that parameter names.
        let literal = |arg: &Expr| {
            matches!(
                arg,
                Expr::Lit { .. } | Expr::List { .. } | Expr::Record { .. }
            )
        };
        let mut env = HashMap::new();
        for pass in [false, true] {
            for (param, arg) in template.params.iter().zip(args.iter_mut()) {
                if literal(arg) != pass {
                    continue;
                }
                let expect = if pass {
                    self.build_subst(&param.ty, target.module, &env).ok()
                } else {
                    None
                };
                self.check_expr_as(arg, expect)?;
                self.unify(
                    &param.ty,
                    arg.ty(),
                    target.module,
                    &params,
                    &mut env,
                    arg.line(),
                    arg.col(),
                )?;
            }
        }
        for param in &params {
            if !env.contains_key(&param.name) {
                return Err(error(
                    line,
                    col,
                    format!("could not infer type parameter `{}`", param.name),
                ));
            }
            if param.constraint.as_deref() == Some("MapKey") {
                let id = env[&param.name];
                if !self.map_key_ok(id) {
                    return Err(error(
                        line,
                        col,
                        format!("type `{}` does not satisfy `MapKey`", self.ty_label(id)),
                    ));
                }
            }
        }
        let mut places = Vec::new();
        let mut shapes = Vec::new();
        let mut keep = Vec::new();
        let mut slots = Vec::new();
        let mut hidden = Vec::new();
        for (param, arg) in template.params.iter().zip(args.iter()) {
            let concrete = self.build_subst(&param.ty, target.module, &env)?;
            if !param.storage && self.holds_map(concrete) {
                return Err(error(
                    arg.line(),
                    arg.col(),
                    format!(
                        "`{}` takes `{}` : {}, which lives only in storage: declare it `storage {}`",
                        source_name(&target.qualified),
                        param.name,
                        self.ty_label(concrete),
                        param.name
                    ),
                ));
            }
            if param.storage {
                let Some(path) = storage_path(arg, &param.name, &mut hidden) else {
                    return Err(error(
                        arg.line(),
                        arg.col(),
                        format!("pass a storage path to `{}`", param.name),
                    ));
                };
                let root = storage_root(arg);
                if !root.is_some_and(|sym| self.syms.get(sym).is_some_and(|sym| sym.storage)) {
                    return Err(error(
                        arg.line(),
                        arg.col(),
                        format!("pass a storage path to `{}`", param.name),
                    ));
                }
                // A map is reached through its slot alone, so one copy serves every map of
                // the type: the call passes the slot.
                if let Some(transient) = self.map_slot_transient(concrete, arg) {
                    slots.push((param.name.clone(), transient));
                    keep.push(param.clone());
                    continue;
                }
                // The same place, however its name was written, shares one copy.
                let named = match path.first() {
                    Some(Seg::Field(first)) if self.known_modules.contains(first) => 2,
                    _ => 1,
                };
                let mut shape = format!("{}", root.unwrap_or(0));
                for seg in &path[named..] {
                    match seg {
                        Seg::Field(name) => shape.push_str(name),
                        Seg::Key(_) => shape.push_str("[]"),
                    }
                    shape.push('.');
                }
                shapes.push(shape);
                places.push((param.name.clone(), path));
            } else {
                keep.push(param.clone());
            }
        }
        let mut key = target.qualified.clone();
        for param in &params {
            key.push('\u{1}');
            key.push_str(&env[&param.name].to_string());
        }
        for shape in &shapes {
            key.push('\u{1}');
            key.push_str(shape);
        }
        for (name, arg) in &hidden {
            keep.push(Param {
                line: arg.line(),
                col: arg.col(),
                mutable: false,
                storage: false,
                name: name.clone(),
                ty: TypeRef::Hole { id: arg.ty() },
                ty_id: 0,
                sym: None,
            });
        }
        for (name, transient) in &slots {
            key.push_str(&format!("\u{1}{name}:{transient}"));
        }
        let idx = if let Some(idx) = self.specs.get(&key).copied() {
            idx
        } else {
            if self.busy.iter().any(|have| have == &key) {
                return Err(error(
                    line,
                    col,
                    "recursion is not supported: iteration is bounded, write a `for` loop",
                ));
            }
            self.busy.push(key.clone());
            let saved = std::mem::replace(&mut self.slot_params, slots);
            let made = self.monomorphize(&target, &template, &env, &places, &keep);
            self.slot_params = saved;
            self.busy.pop();
            let idx = made?;
            self.specs.insert(key, idx);
            idx
        };
        let mut kept_args = Vec::new();
        for (param, arg) in template.params.iter().zip(args.iter()) {
            if places.iter().any(|(name, _)| name == &param.name) {
                continue;
            }
            kept_args.push(arg.clone());
        }
        kept_args.extend(hidden.into_iter().map(|(_, arg)| arg));
        let sig_params = self.sigs[idx].params.clone();
        if kept_args.len() != sig_params.len() {
            return Err(error(line, col, "argument has the wrong type"));
        }
        for (arg, (pty, _)) in kept_args.iter_mut().zip(&sig_params) {
            self.check_expr_as(arg, Some(*pty))?;
            if !self.same(arg.ty(), *pty) {
                return Err(error(arg.line(), arg.col(), "argument has the wrong type"));
            }
        }
        self.callee_effect(line, col, &target.qualified, self.sigs[idx].kind)?;
        self.check_private(idx, line, col)?;
        *args = kept_args;
        *callee = Some(idx);
        *ty = self.sigs[idx].ret;
        self.note_call(idx, line, col);
        Ok(())
    }

    /// For a map argument, whether the map is transient: a stored map named by its path, or a
    /// map parameter passed on.
    fn map_slot_transient(&self, ty: usize, arg: &Expr) -> Option<bool> {
        if self.types[peel_id(&self.types, ty)].kind != TyKind::Map {
            return None;
        }
        match arg {
            Expr::Ident { sym: Some(sym), .. } => self.slot_syms.get(sym).copied(),
            Expr::Field {
                root: Some(sym),
                leaf,
                ..
            } if !self.slot_syms.contains_key(sym) => {
                Some((self.syms[*sym].slot + leaf) as usize >= self.transient_from)
            }
            _ => None,
        }
    }

    fn template(&self, target: &GenericCall) -> Result<Func, Error> {
        if let Some(index) = target.module {
            if let Some(func) = self.modules[index]
                .funcs
                .iter()
                .find(|func| func.name == target.func)
            {
                return Ok(func.clone());
            }
        }
        if let Some(func) = self
            .generic_fns
            .iter()
            .find(|func| func.name == target.func)
        {
            return Ok(func.clone());
        }
        Err(error(
            1,
            1,
            format!("unknown function `{}`", target.qualified),
        ))
    }

    fn monomorphize(
        &mut self,
        target: &GenericCall,
        template: &Func,
        env: &HashMap<String, usize>,
        places: &[(String, Vec<Seg>)],
        keep: &[Param],
    ) -> Result<usize, Error> {
        let mut func = template.clone();
        func.type_params.clear();
        func.params = keep.to_vec();
        self.subst_func(&mut func, target.module, env)?;
        for (name, path) in places {
            rewrite_place(&mut func, name, path);
        }
        let mut spec_name = target.qualified.clone();
        if self.fn_names.iter().any(|name| name == &spec_name) {
            let mut n = 2;
            while self
                .fn_names
                .iter()
                .any(|name| name == &format!("{spec_name}#{n}"))
            {
                n += 1;
            }
            spec_name = format!("{spec_name}#{n}");
        }
        func.name = spec_name;
        // A generic module's copy resolves its names through `spec_module`; any other
        // function stays inside its own module.
        if target.module.is_some() {
            func.module = None;
            func.requires.clear();
        }
        let idx = self.work.len();
        self.prepare_sig(&func)?;
        self.work.push(func.clone());
        self.pieces.push(Vec::new());
        self.declared.push(None);
        let saved = CheckSave {
            scope: self.scope,
            kind: self.kind,
            external_pure: self.external_pure,
            cur_fn: self.cur_fn,
            expect: self.expect,
            once: self.once,
            fn_name: self.fn_name.clone(),
            module_name: self.module_name.clone(),
            requires: self.requires.clone(),
            spec_module: self.spec_module.clone(),
            spec_places: self.spec_places.clone(),
            in_spec: self.in_spec,
            origin: self.origin.clone(),
            guard_label: self.guard_label.clone(),
            hook_label: self.hook_label.clone(),
        };
        self.cur_fn = idx;
        self.spec_module = target.module.map(|index| self.modules[index].name.clone());
        self.spec_places = places
            .iter()
            .filter_map(|(_, path)| match path.first() {
                Some(Seg::Field(root)) => Some(root.clone()),
                _ => None,
            })
            .collect();
        let checked = self.check_func(&mut func);
        self.scope = saved.scope;
        self.kind = saved.kind;
        self.external_pure = saved.external_pure;
        self.cur_fn = saved.cur_fn;
        self.expect = saved.expect;
        self.once = saved.once;
        self.fn_name = saved.fn_name;
        self.module_name = saved.module_name;
        self.requires = saved.requires;
        self.spec_module = saved.spec_module;
        self.spec_places = saved.spec_places;
        self.in_spec = saved.in_spec;
        self.origin = saved.origin;
        self.guard_label = saved.guard_label;
        self.hook_label = saved.hook_label;
        checked?;
        self.work[idx] = func;
        Ok(idx)
    }

    fn unify(
        &mut self,
        param: &TypeRef,
        arg: usize,
        module: Option<usize>,
        params: &[TypeParam],
        env: &mut HashMap<String, usize>,
        line: u32,
        col: u32,
    ) -> Result<(), Error> {
        let param = self.expand_name(param, module, params, env)?;
        match &param {
            TypeRef::Name { name, .. } if params.iter().any(|item| item.name == *name) => {
                if let Some(have) = env.get(name).copied() {
                    if !self.same(have, arg) {
                        return Err(error(
                            line,
                            col,
                            format!(
                                "type parameter `{name}` is both `{}` and `{}`",
                                self.ty_label(have),
                                self.ty_label(arg)
                            ),
                        ));
                    }
                } else {
                    env.insert(name.clone(), arg);
                }
                Ok(())
            }
            TypeRef::Hole { id } => {
                if !self.same(*id, arg) {
                    return Err(error(line, col, "argument has the wrong type"));
                }
                Ok(())
            }
            TypeRef::Map { key, val, .. } => {
                if self.types[arg].kind != TyKind::Map {
                    return Err(error(line, col, "argument has the wrong type"));
                }
                let left = self.types[arg].left.unwrap_or(TY_UNIT);
                let right = self.types[arg].right.unwrap_or(TY_UNIT);
                self.unify(key, left, module, params, env, line, col)?;
                self.unify(val, right, module, params, env, line, col)
            }
            TypeRef::List {
                elem, len, size, ..
            } => {
                let len = match size {
                    Some(size) => self.list_size(size)?,
                    None => len.unwrap_or(0),
                };
                if self.types[arg].kind != TyKind::List || u32::from(self.types[arg].bits) != len {
                    return Err(error(line, col, "argument has the wrong type"));
                }
                let inner = self.types[arg].elem.unwrap_or(TY_UNIT);
                self.unify(elem, inner, module, params, env, line, col)
            }
            TypeRef::Option { elem, .. } => {
                if self.types[arg].kind != TyKind::Option {
                    return Err(error(line, col, "argument has the wrong type"));
                }
                let inner = self.types[arg].elem.unwrap_or(TY_UNIT);
                self.unify(elem, inner, module, params, env, line, col)
            }
            TypeRef::Record { fields, .. } => {
                if self.types[arg].kind != TyKind::Record
                    || self.types[arg].fields.len() != fields.len()
                {
                    return Err(error(line, col, "argument has the wrong type"));
                }
                let concrete: Vec<(String, usize)> = self.types[arg]
                    .fields
                    .iter()
                    .map(|field| (field.name.clone(), field.ty))
                    .collect();
                // A field such as `SetEnumerable(K)` can only be built once `K` is bound,
                // so generic applications unify after the other fields.
                let (applied, plain): (Vec<_>, Vec<_>) = fields
                    .iter()
                    .partition(|field| matches!(field.ty, TypeRef::Apply { .. }));
                for field in plain.into_iter().chain(applied) {
                    let Some((_, fty)) = concrete.iter().find(|(name, _)| name == &field.name)
                    else {
                        return Err(error(line, col, "argument has the wrong type"));
                    };
                    self.unify(&field.ty, *fty, module, params, env, line, col)?;
                }
                Ok(())
            }
            TypeRef::Tuple { elems, .. } => {
                if self.types[arg].kind != TyKind::Tuple
                    || self.types[arg].fields.len() != elems.len()
                {
                    return Err(error(line, col, "argument has the wrong type"));
                }
                let concrete: Vec<usize> = self.types[arg]
                    .fields
                    .iter()
                    .map(|field| field.ty)
                    .collect();
                for (elem, fty) in elems.iter().zip(concrete) {
                    self.unify(elem, fty, module, params, env, line, col)?;
                }
                Ok(())
            }
            other => {
                let bound = subst_bound(other, env);
                if mentions_params(&bound, params) {
                    return Ok(());
                }
                let id = self.build(&bound)?;
                if !self.same(id, arg) {
                    return Err(error(line, col, "argument has the wrong type"));
                }
                Ok(())
            }
        }
    }

    fn expand_name(
        &mut self,
        ty: &TypeRef,
        module: Option<usize>,
        params: &[TypeParam],
        _env: &HashMap<String, usize>,
    ) -> Result<TypeRef, Error> {
        let TypeRef::Name { name, line, col } = ty else {
            return Ok(ty.clone());
        };
        if params.iter().any(|param| param.name == *name) {
            return Ok(ty.clone());
        }
        let Some(index) = module else {
            return Ok(ty.clone());
        };
        let Some(decl) = self.modules[index]
            .types
            .iter()
            .find(|decl| decl.name == *name)
            .cloned()
        else {
            return Ok(ty.clone());
        };
        let _ = (line, col);
        Ok(decl.ty)
    }

    pub(super) fn build_subst(
        &mut self,
        ty: &TypeRef,
        module: Option<usize>,
        env: &HashMap<String, usize>,
    ) -> Result<usize, Error> {
        let params = match module {
            Some(index) => self.modules[index].params.clone(),
            None => Vec::new(),
        };
        let expanded = self.expand_name(ty, module, &params, env)?;
        let substituted = subst_bound(&expanded, env);
        self.build(&substituted)
    }

    fn subst_func(
        &mut self,
        func: &mut Func,
        module: Option<usize>,
        env: &HashMap<String, usize>,
    ) -> Result<(), Error> {
        let params = match module {
            Some(index) => self.modules[index].params.clone(),
            None => Vec::new(),
        };
        for param in &mut func.params {
            param.ty = subst_bound(&self.expand_name(&param.ty, module, &params, env)?, env);
        }
        if let Some(ret) = &mut func.ret {
            *ret = subst_bound(&self.expand_name(ret, module, &params, env)?, env);
        }
        subst_stmts(&mut func.stmts, module, &params, env, self)?;
        if let Some(tail) = &mut func.tail {
            subst_expr_types(tail, module, &params, env, self)?;
        }
        Ok(())
    }
}

fn subst_bound(ty: &TypeRef, env: &HashMap<String, usize>) -> TypeRef {
    match ty {
        TypeRef::Name { name, line, col } => {
            if let Some(id) = env.get(name) {
                TypeRef::Hole { id: *id }
            } else {
                TypeRef::Name {
                    line: *line,
                    col: *col,
                    name: name.clone(),
                }
            }
        }
        TypeRef::Hole { id } => TypeRef::Hole { id: *id },
        TypeRef::List {
            line,
            col,
            elem,
            len,
            size,
        } => TypeRef::List {
            line: *line,
            col: *col,
            elem: Box::new(subst_bound(elem, env)),
            len: *len,
            size: size.clone(),
        },
        TypeRef::Option { line, col, elem } => TypeRef::Option {
            line: *line,
            col: *col,
            elem: Box::new(subst_bound(elem, env)),
        },
        TypeRef::Map {
            line,
            col,
            key,
            val,
        } => TypeRef::Map {
            line: *line,
            col: *col,
            key: Box::new(subst_bound(key, env)),
            val: Box::new(subst_bound(val, env)),
        },
        TypeRef::Tuple { line, col, elems } => TypeRef::Tuple {
            line: *line,
            col: *col,
            elems: elems.iter().map(|elem| subst_bound(elem, env)).collect(),
        },
        TypeRef::Record {
            line,
            col,
            fields,
            tuple,
        } => TypeRef::Record {
            line: *line,
            col: *col,
            tuple: *tuple,
            fields: fields
                .iter()
                .map(|field| FieldRef {
                    line: field.line,
                    col: field.col,
                    name: field.name.clone(),
                    ty: subst_bound(&field.ty, env),
                    indexed: field.indexed,
                })
                .collect(),
        },
        TypeRef::Variant {
            line,
            col,
            variants,
        } => TypeRef::Variant {
            line: *line,
            col: *col,
            variants: variants
                .iter()
                .map(|variant| VariantRef {
                    line: variant.line,
                    col: variant.col,
                    name: variant.name.clone(),
                    payload: variant
                        .payload
                        .as_ref()
                        .map(|payload| subst_bound(payload, env)),
                    param: variant.param.clone(),
                    external: variant.external.clone(),
                })
                .collect(),
        },
        TypeRef::Apply {
            line,
            col,
            name,
            args,
            member,
        } => TypeRef::Apply {
            line: *line,
            col: *col,
            name: name.clone(),
            args: args.iter().map(|arg| subst_bound(arg, env)).collect(),
            member: member.clone(),
        },
    }
}

fn subst_stmts(
    stmts: &mut [Stmt],
    module: Option<usize>,
    params: &[TypeParam],
    env: &HashMap<String, usize>,
    cx: &mut Checker,
) -> Result<(), Error> {
    for stmt in stmts {
        match stmt {
            Stmt::Const { ty, .. } | Stmt::Var { ty, .. } => {
                let expanded = cx.expand_name(ty, module, params, env)?;
                *ty = subst_bound(&expanded, env);
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                subst_stmts(then_body, module, params, env, cx)?;
                subst_stmts(else_body, module, params, env, cx)?;
            }
            Stmt::Defer {
                then: Some(then), ..
            } => {
                if let Some(ty) = &mut then.ty {
                    let expanded = cx.expand_name(ty, module, params, env)?;
                    *ty = subst_bound(&expanded, env);
                }
                subst_stmts(&mut then.stmts, module, params, env, cx)?;
                if let Some(failed) = &mut then.error {
                    if let Some(ty) = &mut failed.ty {
                        let expanded = cx.expand_name(ty, module, params, env)?;
                        *ty = subst_bound(&expanded, env);
                    }
                    subst_stmts(&mut failed.stmts, module, params, env, cx)?;
                }
            }
            Stmt::For { ty, body, .. } => {
                let expanded = cx.expand_name(ty, module, params, env)?;
                *ty = subst_bound(&expanded, env);
                subst_stmts(body, module, params, env, cx)?;
            }
            Stmt::Assign { .. }
            | Stmt::AssignTuple { .. }
            | Stmt::Assert { .. }
            | Stmt::Fail { .. }
            | Stmt::Call { .. }
            | Stmt::Skip
            | Stmt::Emit { .. }
            | Stmt::Defer { .. } => {}
        }
    }
    Ok(())
}

fn subst_expr_types(
    _expr: &mut Expr,
    _module: Option<usize>,
    _params: &[TypeParam],
    _env: &HashMap<String, usize>,
    _cx: &mut Checker,
) -> Result<(), Error> {
    Ok(())
}

/// A step of the storage path a call passes for a storage parameter. A key names the
/// hidden parameter that carries the caller's key into the specialized copy, so the key is
/// evaluated once, at the call.
#[derive(Clone)]
enum Seg {
    Field(String),
    Key(String),
}

fn rewrite_place(func: &mut Func, name: &str, path: &[Seg]) {
    rewrite_stmts(&mut func.stmts, name, path);
    if let Some(tail) = &mut func.tail {
        rewrite_expr(tail, name, path);
    }
}

fn rewrite_stmts(stmts: &mut [Stmt], name: &str, path: &[Seg]) {
    for stmt in stmts {
        match stmt {
            Stmt::Const { expr, .. } | Stmt::Var { expr, .. } => rewrite_expr(expr, name, path),
            Stmt::Assign {
                line,
                col,
                path: dest,
                index,
                keys,
                fields,
                expr,
                ..
            } => {
                if dest.first().is_some_and(|head| head == name) {
                    rewrite_dest(*line, *col, path, dest, index, keys, fields);
                }
                if let Some(index) = index {
                    rewrite_expr(index, name, path);
                }
                for key in keys.iter_mut() {
                    rewrite_expr(key, name, path);
                }
                rewrite_expr(expr, name, path);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                rewrite_expr(cond, name, path);
                rewrite_stmts(then_body, name, path);
                rewrite_stmts(else_body, name, path);
            }
            Stmt::Assert { cond, reason, .. } => {
                rewrite_expr(cond, name, path);
                rewrite_raised(reason, name, path);
            }
            Stmt::Fail { reason, .. } => rewrite_raised(reason, name, path),
            Stmt::Call { expr, .. } | Stmt::AssignTuple { expr, .. } => {
                rewrite_expr(expr, name, path)
            }
            Stmt::For {
                iter,
                until,
                bound,
                body,
                ..
            } => {
                match iter {
                    ForIter::Range { lo, hi } => {
                        rewrite_expr(lo, name, path);
                        rewrite_expr(hi, name, path);
                    }
                    ForIter::List(xs) => rewrite_expr(xs, name, path),
                }
                for e in until.iter_mut().chain(bound.iter_mut()) {
                    rewrite_expr(e, name, path);
                }
                rewrite_stmts(body, name, path);
            }
            Stmt::Emit { fields, .. } => {
                for (_, expr) in fields {
                    rewrite_expr(expr, name, path);
                }
            }
            Stmt::Defer {
                expr,
                value,
                gas,
                then,
                ..
            } => {
                rewrite_expr(expr, name, path);
                for value in value.iter_mut().chain(gas) {
                    rewrite_expr(value, name, path);
                }
                if let Some(then) = then {
                    rewrite_stmts(&mut then.stmts, name, path);
                    if let Some(failed) = &mut then.error {
                        rewrite_stmts(&mut failed.stmts, name, path);
                    }
                }
            }
            Stmt::Skip => {}
        }
    }
}

fn rewrite_raised(reason: &mut Raised, name: &str, path: &[Seg]) {
    match &mut reason.form {
        RaisedForm::Unit => {}
        RaisedForm::Positional(expr) => rewrite_expr(expr, name, path),
        RaisedForm::Fields(fields) => {
            for (_, expr) in fields {
                rewrite_expr(expr, name, path);
            }
        }
    }
}

fn rewrite_expr(expr: &mut Expr, name: &str, path: &[Seg]) {
    match expr {
        Expr::Ident {
            name: ident,
            line,
            col,
            ..
        } if ident == name => {
            *expr = seg_expr(*line, *col, path);
        }
        Expr::Field { base, .. } => rewrite_expr(base, name, path),
        Expr::Index { base, index, .. } => {
            rewrite_expr(base, name, path);
            rewrite_expr(index, name, path);
        }
        Expr::Call { args, base, .. } => {
            for arg in args {
                rewrite_expr(arg, name, path);
            }
            if let Some(base) = base {
                rewrite_expr(base, name, path);
            }
        }
        Expr::Query { expr, gas, .. } => {
            rewrite_expr(expr, name, path);
            if let Some(gas) = gas {
                rewrite_expr(gas, name, path);
            }
        }
        Expr::Unary { expr, .. } | Expr::Convert { expr, .. } => rewrite_expr(expr, name, path),
        Expr::Case { scrut, arms, .. } => {
            rewrite_expr(scrut, name, path);
            for arm in arms {
                rewrite_stmts(&mut arm.stmts, name, path);
                rewrite_expr(&mut arm.expr, name, path);
            }
        }
        Expr::Binary { left, right, .. } => {
            rewrite_expr(left, name, path);
            rewrite_expr(right, name, path);
        }
        Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
            for elem in elems {
                rewrite_expr(elem, name, path);
            }
        }
        Expr::Record { fields, .. } => {
            for (_, expr) in fields {
                rewrite_expr(expr, name, path);
            }
        }
        Expr::Lit { .. } | Expr::Ident { .. } => {}
    }
}

/// A storage path's name and fields, then its keys, each after the steps before it.
/// `keys` collects each key's hidden parameter and the caller's key, in order.
fn storage_path(expr: &Expr, param: &str, keys: &mut Vec<(String, Expr)>) -> Option<Vec<Seg>> {
    match expr {
        Expr::Ident { name, .. } => {
            Some(name.split('.').map(|s| Seg::Field(s.to_string())).collect())
        }
        Expr::Field { base, name, .. } => {
            let mut path = storage_path(base, param, keys)?;
            path.push(Seg::Field(name.clone()));
            Some(path)
        }
        Expr::Index { base, index, .. } => {
            let mut path = storage_path(base, param, keys)?;
            let hidden = format!("${param}{}", keys.len());
            keys.push((hidden.clone(), index.as_ref().clone()));
            path.push(Seg::Key(hidden));
            Some(path)
        }
        _ => None,
    }
}

fn seg_expr(line: u32, col: u32, path: &[Seg]) -> Expr {
    let mut expr: Option<Expr> = None;
    for seg in path {
        expr = Some(match (seg, expr) {
            (Seg::Field(name), None) => Expr::Ident {
                line,
                col,
                name: name.clone(),
                sym: None,
                builtin: None,
                ty: 0,
            },
            (Seg::Field(name), Some(base)) => Expr::Field {
                line,
                col,
                base: Box::new(base),
                name: name.clone(),
                root: None,
                leaf: 0,
                ty: 0,
            },
            (Seg::Key(name), base) => Expr::Index {
                line,
                col,
                base: Box::new(base.expect("a path starts with a name")),
                index: Box::new(Expr::Ident {
                    line,
                    col,
                    name: name.clone(),
                    sym: None,
                    builtin: None,
                    ty: 0,
                }),
                root: None,
                leaf: 0,
                ty: 0,
            },
        });
    }
    expr.expect("a path has a name")
}

/// An assignment through a storage parameter, written onto the path the caller passed:
/// its fields and keys come first, then the assignment's own.
fn rewrite_dest(
    line: u32,
    col: u32,
    path: &[Seg],
    dest: &mut Vec<String>,
    index: &mut Option<Expr>,
    keys: &mut Vec<Expr>,
    fields: &mut Vec<(usize, String)>,
) {
    let key = |name: &str| Expr::Ident {
        line,
        col,
        name: name.to_string(),
        sym: None,
        builtin: None,
        ty: 0,
    };
    let rest: Vec<String> = dest.drain(1..).collect();
    dest.clear();
    let mut steps = path.iter();
    let mut added = Vec::new();
    let mut named = Vec::new();
    for seg in steps.by_ref() {
        match seg {
            Seg::Field(name) => dest.push(name.clone()),
            Seg::Key(name) => {
                added.push(key(name));
                break;
            }
        }
    }
    if added.is_empty() {
        dest.extend(rest);
        return;
    }
    for seg in steps {
        match seg {
            Seg::Field(name) => named.push((added.len(), name.clone())),
            Seg::Key(name) => added.push(key(name)),
        }
    }
    named.extend(rest.into_iter().map(|name| (added.len(), name)));
    let shift = added.len();
    named.extend(fields.drain(..).map(|(at, name)| (at + shift, name)));
    added.extend(index.take());
    added.append(keys);
    let mut added = added.into_iter();
    *index = added.next();
    *keys = added.collect();
    *fields = named;
}
