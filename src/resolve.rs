//! Per-file scopes. A file sees its own declarations and the public names of the files it
//! imports directly, under the alias if one is given. Every declaration has one canonical
//! name, whichever files import it and however they spell it, and the loader rewrites each
//! file's references to those names before the files are merged into one program.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::{Component, Path, PathBuf};
use std::sync::OnceLock;

use crate::ast::*;
use crate::modules::{clash, file_label, kind_name, Site, STD_ROOT};
use crate::{error, Error};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Cat {
    Type,
    Error,
    ErrorSet,
    Event,
    Interface,
    Func,
    Module,
}

impl Cat {
    fn noun(self) -> &'static str {
        match self {
            Cat::Type => "type",
            Cat::Error => "error",
            Cat::ErrorSet => "error set",
            Cat::Event => "event",
            Cat::Interface => "interface",
            Cat::Func => "function",
            Cat::Module => "module",
        }
    }
}

/// A declaration of a type, error, error set, event, interface, function, or module at the
/// top of a file or a contract.
#[derive(Debug, Clone)]
pub(crate) struct Decl {
    pub cat: Cat,
    pub origin: String,
    pub name: String,
    pub canonical: String,
    pub private: bool,
    pub line: u32,
    pub col: u32,
    kind: Option<ItemKind>,
    shape: Vec<String>,
}

/// What one name in a scope refers to, and the import that brought it, if any.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Entry {
    pub decl: usize,
    pub import: Option<usize>,
}

/// An `import` line of a file, and what it names.
#[derive(Debug, Clone)]
pub(crate) struct Import {
    pub decl: UseDecl,
    /// The imported file of declarations. `None` for a file of contracts.
    pub target: Option<String>,
    /// The contracts of an imported file of contracts.
    pub contracts: Vec<String>,
}

/// The names one file sees, or one contract of a file of contracts.
#[derive(Debug, Clone, Default)]
pub(crate) struct Scope {
    pub names: BTreeMap<String, Vec<Entry>>,
    pub modules: BTreeMap<String, Entry>,
    pub aliases: BTreeMap<String, usize>,
    pub imports: Vec<Import>,
    /// The contracts it may create by name: its file's and those of the files it imports.
    pub contracts: BTreeSet<String>,
    /// The imports its references use.
    pub used: BTreeSet<usize>,
}

/// A scope's key: a file, and the contract when the file declares several.
pub(crate) type Key = (String, Option<String>);

/// Every scope of one program, over its declarations.
#[derive(Debug, Clone, Default)]
pub(crate) struct Scopes {
    pub decls: Vec<Decl>,
    pub scopes: BTreeMap<Key, Scope>,
    /// Names declared inside modules, which `use` publishes: they keep their names.
    members: BTreeSet<String>,
    ctors: BTreeSet<String>,
    /// The intrinsics of each module the compiler implements, by its canonical name.
    pub intrinsics: BTreeMap<String, BTreeMap<String, Tag>>,
}

/// One file, or one contract of a file of contracts, with its imports.
pub(crate) struct Unit<'a> {
    pub key: Key,
    pub prog: &'a mut Program,
    pub imports: Vec<Import>,
    /// The contracts of its file.
    pub contracts: Vec<String>,
    /// The file is the one being built, not an import.
    pub root: bool,
}

impl Scopes {
    pub(crate) fn scope(&self, key: &Key) -> Option<&Scope> {
        self.scopes.get(key)
    }

    /// The scope of the file `origin`, or of its first contract.
    pub(crate) fn of_file(&self, origin: &str) -> Option<&Scope> {
        self.scopes.get(&(origin.to_string(), None)).or_else(|| {
            self.scopes
                .iter()
                .filter(|(key, _)| key.0 == origin)
                .map(|(_, scope)| scope)
                .next()
        })
    }
}

/// Builds each unit's scope, gives every declaration its canonical name, and rewrites every
/// unit's declarations and references to canonical names. `units` comes deepest import
/// first, as the files are merged.
pub(crate) fn link(units: &mut [Unit]) -> Result<Scopes, Error> {
    let mut scopes = Scopes::default();
    let mut own: HashMap<Key, Vec<usize>> = HashMap::new();
    let mut file_modules: HashMap<String, Vec<usize>> = HashMap::new();
    for unit in units.iter() {
        let origin = &unit.key.0;
        let prog = &*unit.prog;
        let mut ids = Vec::new();
        let mut add = |scopes: &mut Scopes, decl: Decl| {
            scopes.decls.push(decl);
            ids.push(scopes.decls.len() - 1);
        };
        let item = |cat: Cat, name: &str, private: bool, line: u32, col: u32| Decl {
            cat,
            origin: origin.clone(),
            name: name.to_string(),
            canonical: String::new(),
            private,
            line,
            col,
            kind: None,
            shape: Vec::new(),
        };
        for d in &prog.types {
            add(
                &mut scopes,
                item(Cat::Type, &d.name, d.private, d.line, d.col),
            );
        }
        for d in &prog.errors {
            add(
                &mut scopes,
                item(Cat::Error, &d.name, d.private, d.line, d.col),
            );
        }
        for d in &prog.error_sets {
            add(
                &mut scopes,
                item(Cat::ErrorSet, &d.name, false, d.line, d.col),
            );
        }
        for d in &prog.events {
            add(
                &mut scopes,
                item(Cat::Event, &d.name, d.private, d.line, d.col),
            );
        }
        for d in &prog.interfaces {
            add(
                &mut scopes,
                item(Cat::Interface, &d.name, false, d.line, d.col),
            );
        }
        for f in &prog.funcs {
            let mut decl = item(Cat::Func, &f.name, f.private, f.line, f.col);
            decl.kind = Some(f.kind);
            decl.shape = f
                .params
                .iter()
                .map(|p| crate::check::shape_ty(&p.ty))
                .collect();
            add(&mut scopes, decl);
        }
        own.insert(unit.key.clone(), ids);
        if !file_modules.contains_key(origin) {
            let mut ids = Vec::new();
            for m in &prog.modules {
                scopes
                    .decls
                    .push(item(Cat::Module, &m.name, false, m.line, m.col));
                ids.push(scopes.decls.len() - 1);
            }
            file_modules.insert(origin.clone(), ids);
        }
        for m in &prog.modules {
            let names = m
                .types
                .iter()
                .map(|d| &d.name)
                .chain(m.errors.iter().map(|d| &d.name))
                .chain(m.error_sets.iter().map(|d| &d.name))
                .chain(m.events.iter().map(|d| &d.name));
            scopes.members.extend(names.cloned());
            for d in &m.types {
                collect_ctors(&d.ty, &mut scopes.ctors);
            }
        }
        for d in &prog.types {
            collect_ctors(&d.ty, &mut scopes.ctors);
        }
    }

    // Each unit's scope: its imports' public names, then its own. Functions one scope sees
    // under one name are overloads, which share their canonical name.
    let mut groups: Vec<usize> = (0..scopes.decls.len()).collect();
    for unit in units.iter() {
        let mut scope = Scope {
            imports: unit.imports.clone(),
            ..Scope::default()
        };
        scope.contracts.extend(unit.contracts.iter().cloned());
        for (k, import) in unit.imports.iter().enumerate() {
            let via = Some(&import.decl);
            if let Some(alias) = &import.decl.alias {
                scope.aliases.insert(alias.clone(), k);
            }
            scope.contracts.extend(import.contracts.iter().cloned());
            let Some(target) = &import.target else {
                continue;
            };
            let public: Vec<usize> = own
                .get(&(target.clone(), None))
                .into_iter()
                .flatten()
                .copied()
                .filter(|&id| !scopes.decls[id].private)
                .collect();
            let spell = |name: &str| match &import.decl.alias {
                Some(alias) => format!("{alias}.{name}"),
                None => name.to_string(),
            };
            for id in public {
                let name = spell(&scopes.decls[id].name);
                insert(
                    &scopes.decls,
                    &mut groups,
                    &mut scope,
                    name,
                    id,
                    Some(k),
                    via,
                )
                .map_err(|err| err.in_file(&unit.key.0))?;
            }
            for &id in file_modules.get(target).into_iter().flatten() {
                let name = spell(&scopes.decls[id].name);
                insert_module(&scopes.decls, &mut scope, name, id, Some(k), via)
                    .map_err(|err| err.in_file(&unit.key.0))?;
            }
        }
        for &id in &own[&unit.key] {
            let name = scopes.decls[id].name.clone();
            insert(&scopes.decls, &mut groups, &mut scope, name, id, None, None)
                .map_err(|err| err.in_file(&unit.key.0))?;
        }
        for &id in &file_modules[&unit.key.0] {
            let name = scopes.decls[id].name.clone();
            insert_module(&scopes.decls, &mut scope, name, id, None, None)
                .map_err(|err| err.in_file(&unit.key.0))?;
        }
        scopes.scopes.insert(unit.key.clone(), scope);
    }

    // Canonical names: a declaration keeps its own name unless another has it. The file
    // being built comes first, then its imports nearest first.
    let mut taken: HashSet<String> = HashSet::new();
    let mut taken_modules: HashSet<String> = HashSet::new();
    let mut order: Vec<usize> = Vec::new();
    for unit in units.iter().rev() {
        order.extend(&own[&unit.key]);
    }
    let roots: HashSet<String> = units
        .iter()
        .filter(|unit| unit.root)
        .map(|unit| unit.key.0.clone())
        .collect();
    let mut seen_files = HashSet::new();
    for unit in units.iter().rev() {
        if seen_files.insert(unit.key.0.clone()) {
            order.extend(&file_modules[&unit.key.0]);
        }
    }
    let mut named: HashMap<usize, String> = HashMap::new();
    let mut root_names: HashSet<String> = HashSet::new();
    for unit in units.iter().filter(|unit| unit.root) {
        for &id in &own[&unit.key] {
            let decl = &scopes.decls[id];
            if !decl.private {
                root_names.insert(decl.name.clone());
            }
        }
    }
    for id in order {
        let group = find(&mut groups, id);
        if let Some(name) = named.get(&group) {
            scopes.decls[id].canonical = name.clone();
            continue;
        }
        let decl = &scopes.decls[id];
        let root = roots.contains(&decl.origin);
        let name = if decl.cat == Cat::Module {
            unique(&decl.name, &decl.origin, &mut taken_modules, |_| false)
        } else if decl.private {
            unique(
                &format!("{}::{}", file_label(Path::new(&decl.origin)), decl.name),
                &decl.origin,
                &mut taken,
                |_| false,
            )
        } else if root {
            // The contracts of the file being built keep their names: two contracts of one
            // file are two programs.
            taken.insert(decl.name.clone());
            decl.name.clone()
        } else {
            let members = &scopes.members;
            unique(&decl.name, &decl.origin, &mut taken, |name| {
                members.contains(name) || root_names.contains(name)
            })
        };
        named.insert(group, name.clone());
        scopes.decls[id].canonical = name;
    }

    // Rename the declarations, then rewrite the references in each unit.
    for unit in units.iter_mut() {
        let ids = &own[&unit.key];
        let prog = &mut *unit.prog;
        let mut ids = ids.iter();
        let mut next = || {
            scopes.decls[*ids.next().expect("a declaration")]
                .canonical
                .clone()
        };
        for d in &mut prog.types {
            d.name = next();
        }
        for d in &mut prog.errors {
            d.name = next();
        }
        for d in &mut prog.error_sets {
            d.name = next();
        }
        for d in &mut prog.events {
            d.name = next();
        }
        for d in &mut prog.interfaces {
            d.name = next();
        }
        for f in &mut prog.funcs {
            f.name = next();
        }
    }
    for unit in units.iter() {
        for module in &unit.prog.modules {
            if module.intrinsics.is_empty() {
                continue;
            }
            let canonical = file_modules[&unit.key.0]
                .iter()
                .map(|&id| &scopes.decls[id])
                .find(|decl| decl.name == module.name)
                .map_or_else(|| module.name.clone(), |decl| decl.canonical.clone());
            let tags = module
                .intrinsics
                .iter()
                .filter_map(|i| Some((i.name.clone(), i.tag?)))
                .collect();
            scopes.intrinsics.insert(canonical, tags);
        }
    }
    let members = scopes.members.clone();
    let ctors = scopes.ctors.clone();
    let intrinsics = scopes.intrinsics.clone();
    for unit in units.iter_mut() {
        let mut scope = scopes.scopes.remove(&unit.key).expect("a scope");
        let module_names: HashMap<String, String> = file_modules[&unit.key.0]
            .iter()
            .map(|&id| {
                let decl = &scopes.decls[id];
                (decl.name.clone(), decl.canonical.clone())
            })
            .collect();
        let mut r = Resolver {
            scope: &mut scope,
            decls: &scopes.decls,
            members: &members,
            ctors: &ctors,
            intrinsics: &intrinsics,
            origin: &unit.key.0,
            module: None,
            type_params: HashSet::new(),
            locals: HashSet::new(),
        };
        r.program(unit.prog, &module_names)
            .map_err(|err| err.in_file(&unit.key.0))?;
        scopes.scopes.insert(unit.key.clone(), scope);
    }
    Ok(scopes)
}

/// Rewrites spec blocks from a `.spec.lithe` file as the file they describe sees names.
pub(crate) fn resolve_specs(
    scopes: &Scopes,
    key: &Key,
    blocks: &mut [SpecBlock],
) -> Result<(), Error> {
    let Some(scope) = scopes.scope(key).or_else(|| scopes.of_file(&key.0)) else {
        return Ok(());
    };
    let mut scope = scope.clone();
    let mut r = Resolver {
        scope: &mut scope,
        decls: &scopes.decls,
        members: &scopes.members,
        ctors: &scopes.ctors,
        intrinsics: &scopes.intrinsics,
        origin: &key.0,
        module: None,
        type_params: HashSet::new(),
        locals: HashSet::new(),
    };
    r.specs(blocks)
}

fn collect_ctors(ty: &TypeRef, out: &mut BTreeSet<String>) {
    if let TypeRef::Variant { variants, .. } = ty {
        out.extend(variants.iter().map(|v| v.name.clone()));
    }
}

fn find(groups: &mut [usize], mut id: usize) -> usize {
    while groups[id] != id {
        groups[id] = groups[groups[id]];
        id = groups[id];
    }
    id
}

/// `name`, or when another declaration has it, the name qualified by the declaring file.
fn unique(
    name: &str,
    origin: &str,
    taken: &mut HashSet<String>,
    reserved: impl Fn(&str) -> bool,
) -> String {
    if !taken.contains(name) && !reserved(name) {
        taken.insert(name.to_string());
        return name.to_string();
    }
    let (prefix, short) = match name.rsplit_once("::") {
        Some((prefix, short)) => (prefix.to_string(), short),
        None => (
            Path::new(origin)
                .file_stem()
                .map(|stem| stem.to_string_lossy().into_owned())
                .unwrap_or_default(),
            name,
        ),
    };
    let mut n = 1;
    loop {
        let candidate = if n == 1 {
            format!("{prefix}::{short}")
        } else {
            format!("{prefix}{n}::{short}")
        };
        if !taken.contains(&candidate) {
            taken.insert(candidate.clone());
            return candidate;
        }
        n += 1;
    }
}

fn external(kind: Option<ItemKind>) -> bool {
    matches!(kind, Some(ItemKind::Entry | ItemKind::View))
}

fn single(kind: Option<ItemKind>) -> bool {
    matches!(
        kind,
        Some(ItemKind::Deploy | ItemKind::Receive | ItemKind::Fallback)
    )
}

fn site(decl: &Decl) -> Site<'_> {
    let kind = match decl.kind {
        Some(kind) => kind_name(kind),
        None => decl.cat.noun(),
    };
    Site::of(&decl.origin, decl.line, decl.col, kind)
}

/// Adds `id` to the scope as `name`, or fails as two declarations of one name do.
fn insert(
    decls: &[Decl],
    groups: &mut [usize],
    scope: &mut Scope,
    name: String,
    id: usize,
    import: Option<usize>,
    via: Option<&UseDecl>,
) -> Result<(), Error> {
    let new = &decls[id];
    let have: Vec<Entry> = scope.names.get(&name).cloned().unwrap_or_default();
    if have.iter().any(|entry| entry.decl == id) {
        return Ok(());
    }
    if new.cat == Cat::Func {
        let funcs: Vec<&Decl> = have
            .iter()
            .map(|entry| &decls[entry.decl])
            .filter(|decl| decl.cat == Cat::Func)
            .collect();
        if let Some(first) = funcs.first() {
            let (line, col) = at(via, new.line, new.col);
            if single(new.kind) && first.kind == new.kind {
                return Err(error(
                    line,
                    col,
                    format!("a contract has at most one `{}`", new.name),
                ));
            }
            if single(new.kind) || single(first.kind) {
                return Err(error(
                    line,
                    col,
                    format!(
                        "the contract declares `{}`, so no function can take that name",
                        new.name
                    ),
                ));
            }
        }
        // Overloads share a name, all external or all internal, and differ in their
        // parameter types; the checker compares the types themselves.
        let overload = (external(new.kind) || !funcs.is_empty())
            && funcs
                .iter()
                .all(|f| external(f.kind) == external(new.kind) && f.shape != new.shape);
        if overload {
            for entry in &have {
                if decls[entry.decl].cat == Cat::Func {
                    let a = find(groups, entry.decl);
                    let b = find(groups, id);
                    groups[b] = a;
                }
            }
            scope
                .names
                .entry(name)
                .or_default()
                .push(Entry { decl: id, import });
            return Ok(());
        }
        if let Some(first) = funcs.first() {
            let fix = if external(first.kind) != external(new.kind) {
                "an external and an internal function cannot share a name; rename one of them"
            } else {
                "overloads need different parameter types; rename one or change its parameters"
            };
            return Err(taken_error(
                &decls[have[0].decl],
                new,
                &name,
                via,
                Some(fix),
            ));
        }
    }
    if let Some(entry) = have.first() {
        return Err(taken_error(&decls[entry.decl], new, &name, via, None));
    }
    scope
        .names
        .entry(name)
        .or_default()
        .push(Entry { decl: id, import });
    Ok(())
}

fn insert_module(
    decls: &[Decl],
    scope: &mut Scope,
    name: String,
    id: usize,
    import: Option<usize>,
    via: Option<&UseDecl>,
) -> Result<(), Error> {
    if let Some(have) = scope.modules.get(&name) {
        if have.decl == id {
            return Ok(());
        }
        let have = &decls[have.decl];
        let new = &decls[id];
        let have_site = Site::of(&have.origin, have.line, have.col, "");
        let new_site = Site::of(&new.origin, new.line, new.col, "");
        return Err(clash(
            format!("duplicate module `{name}`"),
            &name,
            &have_site,
            &new_site,
            via,
            "rename one of them",
        ));
    }
    scope.modules.insert(name, Entry { decl: id, import });
    Ok(())
}

/// In one file, `fix` or a rename resolves a clash; across files, so does an alias.
fn taken_error(
    have: &Decl,
    new: &Decl,
    name: &str,
    via: Option<&UseDecl>,
    fix: Option<&str>,
) -> Error {
    let have_site = site(have);
    let new_site = site(new);
    if have.origin == new.origin {
        let noun = |decl: &Decl| decl.cat.noun();
        let what = if noun(have) == noun(new) {
            noun(new)
        } else {
            "name"
        };
        let headline = format!("duplicate {what} `{name}`");
        return clash(
            headline,
            name,
            &have_site,
            &new_site,
            via,
            fix.unwrap_or("rename one of them"),
        );
    }
    let fix = match via {
        Some(decl) if decl.alias.is_some() => {
            format!(
                "rename one, or import `{}` with a different alias",
                decl.path
            )
        }
        Some(decl) => format!(
            "rename one, or import `{}` with an alias: `import \"{}\" as Name;`",
            decl.path, decl.path
        ),
        None => "rename one, or import the other file with an alias: `import \"./file\" as Name;`"
            .to_string(),
    };
    clash(
        format!("ambiguous symbol `{name}`"),
        name,
        &have_site,
        &new_site,
        via,
        &fix,
    )
}

fn at(via: Option<&UseDecl>, line: u32, col: u32) -> (u32, u32) {
    via.map(|decl| (decl.line, decl.col)).unwrap_or((line, col))
}

/// The types every file knows.
fn universe_type(name: &str) -> bool {
    if matches!(
        name,
        "unit"
            | "bool"
            | "uint"
            | "int"
            | "address"
            | "string"
            | "operation"
            | "wei"
            | "timestamp"
            | "bytes"
            | "storage"
            | "Self"
    ) {
        return true;
    }
    let sized = |prefix: &str, max: u32, step: u32| {
        name.strip_prefix(prefix)
            .and_then(|n| n.parse::<u32>().ok())
            .is_some_and(|n| n >= step && n <= max && n % step == 0)
    };
    sized("uint", 256, 8) || sized("int", 256, 8) || sized("bytes", 32, 1)
}

/// The module whose body is being rewritten: its functions and its other members, which its
/// code names bare.
struct InModule {
    name: String,
    funcs: HashSet<String>,
    members: HashSet<String>,
}

struct Resolver<'a> {
    scope: &'a mut Scope,
    decls: &'a [Decl],
    members: &'a BTreeSet<String>,
    ctors: &'a BTreeSet<String>,
    intrinsics: &'a BTreeMap<String, BTreeMap<String, Tag>>,
    origin: &'a str,
    module: Option<InModule>,
    type_params: HashSet<String>,
    locals: HashSet<String>,
}

impl Resolver<'_> {
    fn program(
        &mut self,
        prog: &mut Program,
        module_names: &HashMap<String, String>,
    ) -> Result<(), Error> {
        for d in &mut prog.types {
            self.ty(&mut d.ty)?;
        }
        for d in &mut prog.errors {
            if let Some(ty) = &mut d.payload {
                self.ty(ty)?;
            }
        }
        for d in &mut prog.error_sets {
            for member in &mut d.members {
                self.named(
                    &mut member.name,
                    member.line,
                    member.col,
                    &[Cat::Error],
                    "error",
                )?;
            }
        }
        for d in &mut prog.events {
            for field in &mut d.fields {
                self.ty(&mut field.ty)?;
            }
        }
        for iface in &mut prog.interfaces {
            for method in &mut iface.methods {
                self.header(method)?;
            }
        }
        for d in &mut prog.domains {
            self.ty(&mut d.ty)?;
        }
        for func in &mut prog.funcs {
            self.func(func)?;
        }
        for guard in &mut prog.guards {
            if let Some(of) = &mut guard.guard_of {
                self.module_ref(&mut of.module.name, of.module.line, of.module.col)?;
            }
            self.func(guard)?;
        }
        for hook in &mut prog.hooks {
            if let Some(of) = &mut hook.hook_of {
                self.module_ref(&mut of.module.name, of.module.line, of.module.col)?;
            }
            self.func(hook)?;
        }
        for use_ in prog.compose.iter_mut().chain(&mut prog.facets) {
            self.module_ref(&mut use_.name, use_.line, use_.col)?;
        }
        for exposed in &mut prog.exposes {
            self.module_ref(&mut exposed.module, exposed.line, exposed.col)?;
            for iface in &mut exposed.interfaces {
                self.named(
                    &mut iface.name,
                    iface.line,
                    iface.col,
                    &[Cat::Interface],
                    "interface",
                )?;
            }
            for decl in &mut exposed.decls {
                self.header(decl)?;
            }
        }
        for iface in &mut prog.supports {
            self.named(
                &mut iface.name,
                iface.line,
                iface.col,
                &[Cat::Interface],
                "interface",
            )?;
        }
        if let Some(guard) = &mut prog.guard {
            self.locals.clear();
            for stmt in &guard.stmts {
                bind_stmt(stmt, &mut self.locals);
            }
            self.stmts(&mut guard.stmts)?;
        }
        for module in &mut prog.modules {
            self.module_decl(module, module_names)?;
        }
        self.specs(&mut prog.specs)
    }

    fn module_decl(
        &mut self,
        module: &mut ModuleDecl,
        module_names: &HashMap<String, String>,
    ) -> Result<(), Error> {
        if let Some(name) = module_names.get(&module.name) {
            module.name = name.clone();
        }
        for req in &mut module.requires {
            self.module_ref(&mut req.name, req.line, req.col)?;
        }
        let requires: Vec<String> = module.requires.iter().map(|r| r.name.clone()).collect();
        let mut members: HashSet<String> = module
            .types
            .iter()
            .map(|d| d.name.clone())
            .chain(module.errors.iter().map(|d| d.name.clone()))
            .chain(module.error_sets.iter().map(|d| d.name.clone()))
            .chain(module.events.iter().map(|d| d.name.clone()))
            .collect();
        members.insert("Self".to_string());
        self.module = Some(InModule {
            name: module.name.clone(),
            funcs: module
                .funcs
                .iter()
                .chain(&module.hooks)
                .map(|f| f.name.clone())
                .collect(),
            members,
        });
        self.type_params = module.params.iter().map(|p| p.name.clone()).collect();
        let result = (|| {
            for d in &mut module.types {
                self.ty(&mut d.ty)?;
            }
            for d in &mut module.errors {
                if let Some(ty) = &mut d.payload {
                    self.ty(ty)?;
                }
            }
            for d in &mut module.error_sets {
                for member in &mut d.members {
                    self.named(
                        &mut member.name,
                        member.line,
                        member.col,
                        &[Cat::Error],
                        "error",
                    )?;
                }
            }
            for d in &mut module.events {
                for field in &mut d.fields {
                    self.ty(&mut field.ty)?;
                }
            }
            for d in &mut module.domains {
                self.ty(&mut d.ty)?;
                d.owner = Some(module.name.clone());
            }
            for func in &mut module.funcs {
                func.module = Some(module.name.clone());
                func.requires = requires.clone();
                self.func(func)?;
            }
            for guard in &mut module.guards {
                guard.module = Some(module.name.clone());
                self.header(guard)?;
            }
            for hook in &mut module.hooks {
                hook.module = Some(module.name.clone());
                self.header(hook)?;
            }
            for block in &mut module.specs {
                block.module = Some(module.name.clone());
            }
            self.specs(&mut module.specs)
        })();
        self.module = None;
        self.type_params.clear();
        result
    }

    fn func(&mut self, func: &mut Func) -> Result<(), Error> {
        let saved = self.type_params.clone();
        self.type_params
            .extend(func.type_params.iter().map(|p| p.name.clone()));
        self.locals.clear();
        for p in &func.params {
            self.locals.insert(p.name.clone());
        }
        for stmt in &func.stmts {
            bind_stmt(stmt, &mut self.locals);
        }
        if let Some(tail) = &func.tail {
            bind_expr(tail, &mut self.locals);
        }
        let result = (|| {
            self.header(func)?;
            self.stmts(&mut func.stmts)?;
            if let Some(tail) = &mut func.tail {
                self.expr(tail)?;
            }
            Ok(())
        })();
        self.type_params = saved;
        result
    }

    fn header(&mut self, func: &mut Func) -> Result<(), Error> {
        for p in &mut func.params {
            self.ty(&mut p.ty)?;
        }
        if let Some(ret) = &mut func.ret {
            self.ty(ret)?;
        }
        if let Some(raises) = &mut func.raises {
            for part in &mut raises.parts {
                self.named(
                    &mut part.name,
                    part.line,
                    part.col,
                    &[Cat::Error, Cat::ErrorSet],
                    "error",
                )?;
            }
        }
        Ok(())
    }

    fn specs(&mut self, blocks: &mut [SpecBlock]) -> Result<(), Error> {
        for block in blocks {
            self.locals.clear();
            for clause in &block.clauses {
                if let ClauseKind::Const { name, .. } = &clause.kind {
                    self.locals.insert(name.clone());
                }
                bind_expr(&clause.expr, &mut self.locals);
            }
            if let Some(module) = &mut block.module {
                self.module_ref(module, block.line, block.col)?;
            } else if let Some(target) = &mut block.target {
                if let Some(name) = self.lookup(&target.name, &[Cat::Func]) {
                    target.name = name;
                }
            }
            for clause in &mut block.clauses {
                match &mut clause.kind {
                    ClauseKind::Const { ty, .. } => self.ty(ty)?,
                    ClauseKind::Raises(named) => {
                        self.named(
                            &mut named.name,
                            named.line,
                            named.col,
                            &[Cat::Error],
                            "error",
                        )?;
                    }
                    ClauseKind::Invariant(_) | ClauseKind::Panics | ClauseKind::Ensures => {}
                }
                self.expr(&mut clause.expr)?;
            }
        }
        Ok(())
    }

    /// The canonical name `spelled` has in this scope among `cats`, noting the import used.
    fn lookup(&mut self, spelled: &str, cats: &[Cat]) -> Option<String> {
        let entries = self.scope.names.get(spelled)?;
        let found: Vec<Entry> = entries
            .iter()
            .copied()
            .filter(|entry| cats.contains(&self.decls[entry.decl].cat))
            .collect();
        let first = found.first()?;
        for entry in &found {
            if let Some(k) = entry.import {
                self.scope.used.insert(k);
            }
        }
        Some(self.decls[first.decl].canonical.clone())
    }

    fn lookup_module(&mut self, spelled: &str) -> Option<String> {
        let entry = *self.scope.modules.get(spelled)?;
        if let Some(k) = entry.import {
            self.scope.used.insert(k);
        }
        Some(self.decls[entry.decl].canonical.clone())
    }

    fn module_ref(&mut self, name: &mut String, line: u32, col: u32) -> Result<(), Error> {
        if let Some(canonical) = self.lookup_module(name) {
            *name = canonical;
            return Ok(());
        }
        self.missing(&name.clone(), &[Cat::Module], "module", line, col)
    }

    /// A name that some file this one does not import declares.
    fn hidden(&self, spelled: &str, cats: &[Cat]) -> Option<String> {
        if spelled.contains('.') {
            return None;
        }
        let aliased = |key: &String, entry: &Entry| {
            let decl = &self.decls[entry.decl];
            (key.contains('.') && decl.name == spelled && cats.contains(&decl.cat))
                .then(|| key.clone())
        };
        let alias = self
            .scope
            .names
            .iter()
            .flat_map(|(key, entries)| entries.iter().map(move |entry| (key, entry)))
            .chain(self.scope.modules.iter())
            .find_map(|(key, entry)| aliased(key, entry));
        if let Some(key) = alias {
            return Some(format!("this file imports it as `{key}`"));
        }
        let here = self
            .decls
            .iter()
            .find(|decl| {
                decl.name == spelled
                    && cats.contains(&decl.cat)
                    && decl.origin != self.origin
                    && !decl.private
            })
            .map(|decl| decl.origin.clone());
        let path = match here {
            Some(origin) => match module_path_between(self.origin, &origin) {
                Some(path) => path,
                None => {
                    return Some(format!(
                        "`{spelled}` is declared in `{}`, which no import from this file reaches",
                        crate::shown_path(&origin)
                    ))
                }
            },
            None => std_index()
                .iter()
                .find(|(name, cat, _)| name == spelled && cats.contains(cat))
                .map(|(_, _, path)| path.clone())?,
        };
        Some(format!(
            "`{spelled}` is declared in `{path}`: `import \"{path}\";`"
        ))
    }

    fn missing(
        &self,
        spelled: &str,
        cats: &[Cat],
        what: &str,
        line: u32,
        col: u32,
    ) -> Result<(), Error> {
        match self.hidden(spelled, cats) {
            Some(note) => Err(error(
                line,
                col,
                format!("unknown {what} `{spelled}`\n\n{note}"),
            )),
            None => Ok(()),
        }
    }

    fn own_member(&self, name: &str) -> bool {
        self.module
            .as_ref()
            .is_some_and(|m| m.members.contains(name))
    }

    /// An error, error set, event, or interface name.
    fn named(
        &mut self,
        name: &mut String,
        line: u32,
        col: u32,
        cats: &[Cat],
        what: &str,
    ) -> Result<(), Error> {
        if self.own_member(name) {
            return Ok(());
        }
        if let Some(canonical) = self.lookup(name, cats) {
            *name = canonical;
            return Ok(());
        }
        if self.members.contains(name.as_str()) {
            return Ok(());
        }
        self.missing(name, cats, what, line, col)
    }

    fn ty(&mut self, ty: &mut TypeRef) -> Result<(), Error> {
        match ty {
            TypeRef::Name { name, line, col } => {
                if self.type_params.contains(name.as_str())
                    || universe_type(name)
                    || self.own_member(name)
                {
                    return Ok(());
                }
                if let Some(canonical) = self.lookup(name, &[Cat::Type, Cat::Interface]) {
                    *name = canonical;
                    return Ok(());
                }
                if self.members.contains(name.as_str()) {
                    return Ok(());
                }
                let (line, col) = (*line, *col);
                self.missing(
                    &name.clone(),
                    &[Cat::Type, Cat::Interface],
                    "type",
                    line,
                    col,
                )
            }
            TypeRef::Record { fields, .. } => {
                for field in fields {
                    self.ty(&mut field.ty)?;
                }
                Ok(())
            }
            TypeRef::Variant { variants, .. } => {
                for variant in variants {
                    if let Some(payload) = &mut variant.payload {
                        self.ty(payload)?;
                    }
                }
                Ok(())
            }
            TypeRef::List { elem, size, .. } => {
                if let Some(size) = size {
                    self.size(size)?;
                }
                self.ty(elem)
            }
            TypeRef::Option { elem, .. } => self.ty(elem),
            TypeRef::Map { key, val, .. } => {
                self.ty(key)?;
                self.ty(val)
            }
            TypeRef::Tuple { elems, .. } => {
                for elem in elems {
                    self.ty(elem)?;
                }
                Ok(())
            }
            TypeRef::Apply {
                name,
                args,
                line,
                col,
                ..
            } => {
                if let Some(canonical) = self.lookup_module(name) {
                    *name = canonical;
                } else if self.lookup(name, &[Cat::Type]).is_none() {
                    let (line, col) = (*line, *col);
                    self.missing(&name.clone(), &[Cat::Module], "module", line, col)?;
                }
                for arg in args {
                    self.ty(arg)?;
                }
                Ok(())
            }
            TypeRef::Hole { .. } => Ok(()),
        }
    }

    /// A list length names constants from wherever the type is used, so a module's own
    /// constant is qualified: `list(T, n())` in `M` is `M.n()`.
    fn size(&mut self, size: &mut Expr) -> Result<(), Error> {
        if let (
            Expr::Call {
                name,
                base: base @ None,
                line,
                col,
                ..
            },
            Some(module),
        ) = (&mut *size, &self.module)
        {
            if module.funcs.contains(name.as_str()) {
                *base = Some(Box::new(Expr::Ident {
                    line: *line,
                    col: *col,
                    name: module.name.clone(),
                    sym: None,
                    builtin: None,
                    ty: 0,
                }));
                return Ok(());
            }
        }
        match size {
            Expr::Binary { left, right, .. } => {
                self.size(left)?;
                self.size(right)
            }
            // A cast, `uint16(n())`: its argument is a length too.
            Expr::Call {
                base: None, args, ..
            } if !args.is_empty() => {
                let mut taken = std::mem::take(args);
                for arg in &mut taken {
                    self.size(arg)?;
                }
                let result = self.expr(size);
                if let Expr::Call { args, .. } = size {
                    *args = taken;
                }
                result
            }
            _ => self.expr(size),
        }
    }

    fn stmts(&mut self, stmts: &mut [Stmt]) -> Result<(), Error> {
        for stmt in stmts {
            self.stmt(stmt)?;
        }
        Ok(())
    }

    fn stmt(&mut self, stmt: &mut Stmt) -> Result<(), Error> {
        match stmt {
            Stmt::Const { ty, expr, .. } | Stmt::Var { ty, expr, .. } => {
                self.ty(ty)?;
                self.expr(expr)
            }
            Stmt::Assign {
                path,
                index,
                keys,
                expr,
                line,
                col,
                ..
            } => {
                self.path(path, *line, *col)?;
                if let Some(index) = index {
                    self.expr(index)?;
                }
                for key in keys.iter_mut() {
                    self.expr(key)?;
                }
                self.expr(expr)
            }
            Stmt::Call { expr, .. } | Stmt::AssignTuple { expr, .. } => self.expr(expr),
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                self.expr(cond)?;
                self.stmts(then_body)?;
                self.stmts(else_body)
            }
            Stmt::Assert { cond, reason, .. } => {
                self.expr(cond)?;
                self.raised(reason)
            }
            Stmt::Fail { reason } => self.raised(reason),
            Stmt::Emit {
                name,
                fields,
                line,
                col,
            } => {
                self.named(name, *line, *col, &[Cat::Event], "event")?;
                for (_, expr) in fields {
                    self.expr(expr)?;
                }
                Ok(())
            }
            Stmt::Defer {
                expr,
                value,
                gas,
                then,
                ..
            } => {
                self.expr(expr)?;
                for value in value.iter_mut().chain(gas.iter_mut()) {
                    self.expr(value)?;
                }
                if let Some(then) = then {
                    if let Some(ty) = &mut then.ty {
                        self.ty(ty)?;
                    }
                    self.stmts(&mut then.stmts)?;
                    if let Some(failed) = &mut then.error {
                        if let Some(ty) = &mut failed.ty {
                            self.ty(ty)?;
                        }
                        self.stmts(&mut failed.stmts)?;
                    }
                }
                Ok(())
            }
            Stmt::For {
                ty,
                iter,
                until,
                bound,
                body,
                invariants,
                ..
            } => {
                for inv in invariants.iter_mut() {
                    self.expr(inv)?;
                }
                self.ty(ty)?;
                match iter {
                    ForIter::Range { lo, hi } => {
                        self.expr(lo)?;
                        self.expr(hi)?;
                    }
                    ForIter::List(xs) => self.expr(xs)?,
                }
                for e in until.iter_mut().chain(bound.iter_mut()) {
                    self.expr(e)?;
                }
                self.stmts(body)
            }
            Stmt::Skip => Ok(()),
        }
    }

    /// `M.domain.field := v` and `A.M.domain := v`: the module named as this file names it.
    fn path(&mut self, path: &mut Vec<String>, line: u32, col: u32) -> Result<(), Error> {
        let Some(first) = path.first() else {
            return Ok(());
        };
        if self.locals.contains(first) {
            return Ok(());
        }
        if path.len() >= 2 && self.scope.aliases.contains_key(first) {
            let spelled = format!("{}.{}", path[0], path[1]);
            if let Some(canonical) = self.lookup_module(&spelled) {
                path.splice(0..2, [canonical]);
                return Ok(());
            }
        }
        if let Some(canonical) = self.lookup_module(&path[0].clone()) {
            path[0] = canonical;
            return Ok(());
        }
        if path.len() >= 2 {
            let first = Expr::Ident {
                line,
                col,
                name: path[0].clone(),
                sym: None,
                builtin: None,
                ty: 0,
            };
            self.hidden_namespace(&first)?;
        }
        Ok(())
    }

    fn raised(&mut self, reason: &mut Raised) -> Result<(), Error> {
        if !reason.forward {
            let (line, col) = (reason.line, reason.col);
            self.named(&mut reason.name, line, col, &[Cat::Error], "error")?;
        }
        match &mut reason.form {
            RaisedForm::Unit => Ok(()),
            RaisedForm::Positional(expr) => self.expr(expr),
            RaisedForm::Fields(fields) => {
                for (_, expr) in fields {
                    self.expr(expr)?;
                }
                Ok(())
            }
        }
    }

    /// The module an expression names, as `M` or `A.M`, when it is not a value.
    fn module_expr(&mut self, expr: &Expr) -> Option<String> {
        match expr {
            Expr::Ident { name, .. } if !self.locals.contains(name) => self.lookup_module(name),
            Expr::Field { base, name, .. } => match base.as_ref() {
                Expr::Ident { name: alias, .. }
                    if !self.locals.contains(alias) && self.scope.aliases.contains_key(alias) =>
                {
                    self.lookup_module(&format!("{alias}.{name}"))
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// A namespace this file does not import: `Evm` with no `import "std/evm";`.
    fn hidden_namespace(&self, expr: &Expr) -> Result<(), Error> {
        let Expr::Ident {
            name, line, col, ..
        } = expr
        else {
            return Ok(());
        };
        if self.locals.contains(name) || self.scope.aliases.contains_key(name) {
            return Ok(());
        }
        match self.hidden(name, &[Cat::Module]) {
            Some(note) => Err(error(
                *line,
                *col,
                format!("unknown name `{name}`\n\n{note}"),
            )),
            None => Ok(()),
        }
    }

    /// The interfaces and types an intrinsic's arguments name: `Abi.interfaceId(I)`,
    /// `Abi.selector(I.method)`, `Abi.encodeCall(I.method, ...)`, and `Abi.decode(data, T)`.
    fn intrinsic_args(&mut self, tag: Tag, args: &mut [Expr]) -> Result<(), Error> {
        match (tag, args) {
            (Tag::AbiInterfaceId, [iface, ..]) => {
                self.named_expr(iface, &[Cat::Interface], "interface")
            }
            (
                Tag::AbiSelector | Tag::Call(Builtin::AbiEncodeCall),
                [Expr::Field { base, .. }, ..],
            ) => self.named_expr(base, &[Cat::Interface], "interface"),
            (Tag::Call(Builtin::AbiDecode), [_, Expr::Tuple { elems, .. }, ..]) => {
                for elem in elems {
                    self.named_expr(elem, &[Cat::Type, Cat::Interface], "type")?;
                }
                Ok(())
            }
            (Tag::Call(Builtin::AbiDecode), [_, ty, ..]) => {
                self.named_expr(ty, &[Cat::Type, Cat::Interface], "type")
            }
            (
                Tag::Call(Builtin::CreationCode),
                [Expr::Ident {
                    name, line, col, ..
                }, ..],
            ) => self.visible_contract(name, *line, *col),
            (
                Tag::Call(Builtin::FacetAddress),
                [Expr::Ident {
                    name, line, col, ..
                }, ..],
            ) => {
                if let Some(canonical) = self.lookup_module(name) {
                    *name = canonical;
                    return Ok(());
                }
                let spelled = name.clone();
                self.missing(&spelled, &[Cat::Module], "module", *line, *col)
            }
            _ => Ok(()),
        }
    }

    /// A type or interface named as a value, `T` or `A.T`.
    fn named_expr(&mut self, expr: &mut Expr, cats: &[Cat], what: &str) -> Result<(), Error> {
        let (line, col) = (expr.line(), expr.col());
        let spelled = match &*expr {
            Expr::Ident { name, .. } if !self.locals.contains(name) => name.clone(),
            Expr::Field { base, name, .. } => match base.as_ref() {
                Expr::Ident { name: alias, .. } if self.scope.aliases.contains_key(alias) => {
                    format!("{alias}.{name}")
                }
                _ => return Ok(()),
            },
            _ => return Ok(()),
        };
        if universe_type(&spelled)
            || self.type_params.contains(&spelled)
            || self.own_member(&spelled)
        {
            return Ok(());
        }
        if let Some(canonical) = self.lookup(&spelled, cats) {
            *expr = Expr::Ident {
                line,
                col,
                name: canonical,
                sym: None,
                builtin: None,
                ty: 0,
            };
            return Ok(());
        }
        if self.members.contains(&spelled) {
            return Ok(());
        }
        self.missing(&spelled, cats, what, line, col)
    }

    /// A contract this file names must be its file's or come from a file it imports.
    fn visible_contract(&self, name: &str, line: u32, col: u32) -> Result<(), Error> {
        if self.scope.contracts.contains(name) || self.locals.contains(name) {
            return Ok(());
        }
        Err(error(
            line,
            col,
            format!("`{name}` is not another contract of this file or its imports"),
        ))
    }

    /// A contract named by `create C(...)` or `Evm.creationCode(C)`: its file's import is
    /// used.
    fn contract_ref(&mut self, name: &str) {
        for (k, import) in self.scope.imports.iter().enumerate() {
            if import.contracts.iter().any(|c| c == name) {
                self.scope.used.insert(k);
            }
        }
    }

    fn expr(&mut self, expr: &mut Expr) -> Result<(), Error> {
        match expr {
            Expr::Lit { .. } => Ok(()),
            Expr::Ident { name, .. } => {
                if !self.locals.contains(name.as_str()) {
                    self.contract_ref(&name.clone());
                }
                Ok(())
            }
            Expr::Field { .. } => {
                if let Some(canonical) = self.module_expr(expr) {
                    let (line, col) = (expr.line(), expr.col());
                    *expr = Expr::Ident {
                        line,
                        col,
                        name: canonical,
                        sym: None,
                        builtin: None,
                        ty: 0,
                    };
                    return Ok(());
                }
                let Expr::Field { base, .. } = expr else {
                    unreachable!()
                };
                if let Some(canonical) = self.module_expr(base) {
                    let (line, col) = (base.line(), base.col());
                    **base = Expr::Ident {
                        line,
                        col,
                        name: canonical,
                        sym: None,
                        builtin: None,
                        ty: 0,
                    };
                    return Ok(());
                }
                self.hidden_namespace(base)?;
                self.expr(base)
            }
            Expr::Query { expr, gas, .. } => {
                self.expr(expr)?;
                if let Some(gas) = gas {
                    self.expr(gas)?;
                }
                Ok(())
            }
            Expr::Unary { expr, .. } => self.expr(expr),
            Expr::Index { base, index, .. } => {
                self.expr(base)?;
                self.expr(index)
            }
            Expr::Case { scrut, arms, .. } => {
                self.expr(scrut)?;
                for arm in arms {
                    self.stmts(&mut arm.stmts)?;
                    self.expr(&mut arm.expr)?;
                }
                Ok(())
            }
            Expr::Binary { left, right, .. } => {
                self.expr(left)?;
                self.expr(right)
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                for elem in elems {
                    self.expr(elem)?;
                }
                Ok(())
            }
            Expr::Record { fields, .. } => {
                for (_, expr) in fields {
                    self.expr(expr)?;
                }
                Ok(())
            }
            Expr::Call {
                name,
                args,
                base,
                builtin,
                line,
                col,
                ..
            } => {
                let (line, col) = (*line, *col);
                for arg in args.iter_mut() {
                    self.expr(arg)?;
                }
                if let Some(kind) = builtin {
                    if *kind == Builtin::Create {
                        self.contract_ref(&name.clone());
                        self.visible_contract(name, line, col)?;
                    }
                    if *kind == Builtin::SpecForall {
                        if let Some(Expr::Ident {
                            name, line, col, ..
                        }) = args.get_mut(1)
                        {
                            let mut ty = TypeRef::Name {
                                line: *line,
                                col: *col,
                                name: name.clone(),
                            };
                            self.ty(&mut ty)?;
                            if let TypeRef::Name { name: resolved, .. } = ty {
                                *name = resolved;
                            }
                        }
                    }
                    if let Some(base) = base {
                        self.expr(base)?;
                    }
                    return Ok(());
                }
                let callable = [Cat::Func, Cat::Type, Cat::Interface];
                match base {
                    None => {
                        if self
                            .module
                            .as_ref()
                            .is_some_and(|m| m.funcs.contains(name.as_str()))
                        {
                            return Ok(());
                        }
                        if let Some(canonical) = self.lookup(name, &callable) {
                            *name = canonical;
                            return Ok(());
                        }
                        if universe_type(name)
                            || self.type_params.contains(name.as_str())
                            || self.ctors.contains(name.as_str())
                            || self.members.contains(name.as_str())
                            || matches!(name.as_str(), "Some" | "None")
                        {
                            return Ok(());
                        }
                        self.missing(&name.clone(), &callable, "function", line, col)
                    }
                    Some(inner) => {
                        if let Expr::Ident { name: alias, .. } = inner.as_ref() {
                            if !self.locals.contains(alias)
                                && self.scope.aliases.contains_key(alias)
                            {
                                let spelled = format!("{alias}.{name}");
                                if let Some(canonical) = self.lookup(&spelled, &callable) {
                                    *name = canonical;
                                    *base = None;
                                    return Ok(());
                                }
                            }
                        }
                        if let Some(canonical) = self.module_expr(inner) {
                            let (line, col) = (inner.line(), inner.col());
                            let tag = self
                                .intrinsics
                                .get(&canonical)
                                .and_then(|members| members.get(name.as_str()))
                                .copied();
                            **inner = Expr::Ident {
                                line,
                                col,
                                name: canonical,
                                sym: None,
                                builtin: None,
                                ty: 0,
                            };
                            if let Some(tag) = tag {
                                self.intrinsic_args(tag, args)?;
                            }
                            return Ok(());
                        }
                        self.hidden_namespace(inner)?;
                        self.expr(inner)
                    }
                }
            }
        }
    }
}

/// The names a statement binds, anywhere inside it: parameters and locals shadow modules.
fn bind_stmt(stmt: &Stmt, out: &mut HashSet<String>) {
    match stmt {
        Stmt::Const {
            name, parts, expr, ..
        } => {
            out.insert(name.clone());
            out.extend(parts.iter().cloned());
            bind_expr(expr, out);
        }
        Stmt::Var {
            name, parts, expr, ..
        } => {
            out.insert(name.clone());
            out.extend(parts.iter().cloned());
            bind_expr(expr, out);
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            bind_expr(cond, out);
            for s in then_body.iter().chain(else_body) {
                bind_stmt(s, out);
            }
        }
        Stmt::Defer { expr, then, .. } => {
            bind_expr(expr, out);
            if let Some(then) = then {
                for arm in then.arms() {
                    out.extend(arm.names.iter().cloned());
                    for s in &arm.stmts {
                        bind_stmt(s, out);
                    }
                }
            }
        }
        Stmt::For {
            index, name, body, ..
        } => {
            out.extend(index.iter().cloned());
            out.insert(name.clone());
            for s in body {
                bind_stmt(s, out);
            }
        }
        Stmt::Call { expr, .. } | Stmt::AssignTuple { expr, .. } => bind_expr(expr, out),
        Stmt::Assign { expr, .. } => bind_expr(expr, out),
        Stmt::Assert { .. } | Stmt::Fail { .. } | Stmt::Emit { .. } | Stmt::Skip => {}
    }
}

fn bind_expr(expr: &Expr, out: &mut HashSet<String>) {
    match expr {
        Expr::Case { scrut, arms, .. } => {
            bind_expr(scrut, out);
            for arm in arms {
                out.extend(arm.bind.iter().cloned());
                out.extend(arm.tuple_names.iter().cloned());
                for s in &arm.stmts {
                    bind_stmt(s, out);
                }
                bind_expr(&arm.expr, out);
            }
        }
        Expr::Call {
            builtin: Some(Builtin::SpecForall),
            args,
            ..
        } => {
            if let Some(Expr::Ident { name, .. }) = args.first() {
                out.insert(name.clone());
            }
            if let Some(body) = args.get(2) {
                bind_expr(body, out);
            }
        }
        Expr::Call { args, base, .. } => {
            for arg in args {
                bind_expr(arg, out);
            }
            if let Some(base) = base {
                bind_expr(base, out);
            }
        }
        Expr::Query { expr, .. } | Expr::Field { base: expr, .. } | Expr::Unary { expr, .. } => {
            bind_expr(expr, out)
        }
        Expr::Index { base, index, .. } => {
            bind_expr(base, out);
            bind_expr(index, out);
        }
        Expr::Binary { left, right, .. } => {
            bind_expr(left, out);
            bind_expr(right, out);
        }
        Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
            for e in elems {
                bind_expr(e, out);
            }
        }
        Expr::Record { fields, .. } => {
            for (_, e) in fields {
                bind_expr(e, out);
            }
        }
        Expr::Lit { .. } | Expr::Ident { .. } => {}
    }
}

/// How a file imports another: `std/...` for the standard library, `name/...` for a file of
/// one of its packages, or a path relative to the importing file. None when no import path
/// reaches it, as for a file of a package it doesn't declare.
pub(crate) fn module_path_between(from: &str, to: &str) -> Option<String> {
    let to = Path::new(to);
    if let Ok(rel) = to.strip_prefix(STD_ROOT) {
        return Some(rel.with_extension("").display().to_string());
    }
    for (name, dir) in crate::packages::packages_holding(Path::new(from), to) {
        let dir = dir.canonicalize().unwrap_or(dir);
        if let Ok(rel) = to.strip_prefix(&dir) {
            return Some(format!("{name}/{}", rel.with_extension("").display()));
        }
    }
    let from_dir = Path::new(from).parent().unwrap_or(Path::new(""));
    let a: Vec<Component> = from_dir.components().collect();
    let to = to.with_extension("");
    let b: Vec<Component> = to.components().collect();
    let common = a.iter().zip(&b).take_while(|(x, y)| x == y).count();
    let mut out = PathBuf::new();
    for _ in common..a.len() {
        out.push("..");
    }
    for part in &b[common..] {
        out.push(part);
    }
    let text = out.display().to_string();
    let text = if text.starts_with("..") {
        text
    } else {
        format!("./{text}")
    };
    crate::parse::module_path(&text).then_some(text)
}

/// Each public name the standard library declares at the top of a file, with its category
/// and the import that brings it.
pub(crate) fn std_index() -> &'static [(String, Cat, String)] {
    static INDEX: OnceLock<Vec<(String, Cat, String)>> = OnceLock::new();
    INDEX.get_or_init(|| {
        let mut out = Vec::new();
        for (path, src) in crate::modules::STD {
            if path.ends_with(".spec.lithe") {
                continue;
            }
            let Ok(prog) = crate::parse::parse(src) else {
                continue;
            };
            let import = path.trim_end_matches(".lithe").to_string();
            let mut add = |name: &str, cat: Cat| out.push((name.to_string(), cat, import.clone()));
            for d in prog.types.iter().filter(|d| !d.private) {
                add(&d.name, Cat::Type);
            }
            for d in prog.errors.iter().filter(|d| !d.private) {
                add(&d.name, Cat::Error);
            }
            for d in &prog.error_sets {
                add(&d.name, Cat::ErrorSet);
            }
            for d in prog.events.iter().filter(|d| !d.private) {
                add(&d.name, Cat::Event);
            }
            for d in &prog.interfaces {
                add(&d.name, Cat::Interface);
            }
            for f in prog.funcs.iter().filter(|f| !f.private) {
                add(&f.name, Cat::Func);
            }
            for m in &prog.modules {
                add(&m.name, Cat::Module);
            }
        }
        out
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths_between_files() {
        assert_eq!(
            module_path_between("/a/main.lithe", "/a/lib/fees.lithe"),
            Some("./lib/fees".to_string())
        );
        assert_eq!(
            module_path_between("/a/b/main.lithe", "/a/shared/errors.lithe"),
            Some("../shared/errors".to_string())
        );
        assert_eq!(
            module_path_between("/a/main.lithe", &format!("{STD_ROOT}/std/evm.lithe")),
            Some("std/evm".to_string())
        );
        assert_eq!(
            module_path_between(
                "/a/main.lithe",
                "/h/.lithe/packages/math-1a2b/c0/scale.lithe"
            ),
            None
        );
    }
}
