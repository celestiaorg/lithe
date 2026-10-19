//! What an editor asks of a checked program: the declaration each name refers to, what
//! hovering it shows, what may be typed next, and the parameters of the call being typed.

use std::collections::{HashMap, HashSet};
use std::path::Path;

use crate::ast::*;
use crate::check::{Checked, TyKind};
use crate::modules::{std_source, STD_ROOT};
use crate::route::{self, Route};

/// Positions are 1-based lines and 1-based byte columns, as the compiler reports them.
pub struct Index {
    /// The file the index was built for comes first.
    pub files: Vec<File>,
    pub defs: Vec<Def>,
    pub refs: Vec<Ref>,
    /// Each type's declaring definition, whose children are its fields, variants, or methods.
    shapes: HashMap<usize, usize>,
    tys: Vec<Ty>,
    /// The names the indexed file sees, as it writes them, and the canonical name each
    /// stands for: `Math`, `Fees.apply`, `Chain.Evm`.
    spelled: HashMap<String, String>,
}

pub struct File {
    pub path: String,
    /// `std/...` for a standard library file, which has no path on disk.
    pub std: Option<String>,
    pub text: String,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    Function,
    External,
    Type,
    Storage,
    Field,
    Variant,
    Error,
    ErrorSet,
    Event,
    Interface,
    Method,
    Module,
    Contract,
    Local,
    Param,
    Builtin,
    Keyword,
}

pub struct Def {
    pub name: String,
    pub kind: Kind,
    /// Where the name is declared. A built-in has no place.
    pub at: Option<Span>,
    /// One line: a signature, or a name and its type.
    pub detail: String,
    pub hover: String,
    pub parent: Option<usize>,
    /// The type of the value the name holds or returns, for what may follow a dot.
    ty: Option<usize>,
    /// Each parameter as written, for signature help.
    pub params: Vec<String>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Span {
    pub file: usize,
    pub line: u32,
    pub col: u32,
    pub len: u32,
}

pub struct Ref {
    pub at: Span,
    pub def: usize,
    /// Hover text for this use, when it says more than the declaration's.
    pub hover: Option<String>,
}

pub struct Completion {
    pub label: String,
    pub kind: Kind,
    pub detail: String,
    pub doc: String,
    /// LSP snippet syntax, inserted instead of the label.
    pub snippet: Option<String>,
}

pub struct Signature {
    pub label: String,
    pub params: Vec<String>,
    pub active: usize,
    pub doc: String,
}

#[derive(Clone, Copy)]
struct Ty {
    /// The type under any nominal wrapper.
    under: usize,
    /// What indexing gives: a map's value, or a list's element.
    item: Option<usize>,
}

const KEYWORDS: [&str; 65] = [
    "type",
    "is",
    "record",
    "function",
    "view",
    "event",
    "indexed",
    "anonymous",
    "error",
    "errors",
    "raises",
    "payable",
    "external",
    "pure",
    "nonreentrant",
    "import",
    "module",
    "use",
    "exposing",
    crate::parse::DELEGATED,
    "supports",
    "requires",
    "as",
    "private",
    "migrate",
    "deploy",
    "upgradeable",
    "upgrade",
    "guard",
    "guarded",
    "hook",
    "at",
    "contract",
    "fail",
    "forward",
    "forwarded",
    "interface",
    "query",
    "emit",
    "defer",
    "create",
    "const",
    "var",
    "if",
    "then",
    "else",
    "for",
    "in",
    "do",
    "until",
    "bound",
    "case",
    "of",
    "with",
    "skip",
    "delete",
    "assert",
    "storage",
    "transient",
    "immutable",
    "receive",
    "fallback",
    "delegates",
    "forwards",
    "tuple",
];

const TYPE_NAMES: [&str; 17] = [
    "uint",
    "int",
    "bool",
    "address",
    "string",
    "bytes",
    "wei",
    "timestamp",
    "unit",
    "bytes32",
    "bytes4",
    "uint8",
    "uint256",
    "int256",
    "list",
    "map",
    "option",
];

pub(crate) fn build(root: &str, text: &str, units: &[Checked]) -> Index {
    let mut b = Builder {
        ix: Index {
            files: Vec::new(),
            defs: Vec::new(),
            refs: Vec::new(),
            shapes: HashMap::new(),
            tys: Vec::new(),
            spelled: HashMap::new(),
        },
        root: root.to_string(),
        text,
        file_ids: HashMap::new(),
        starts: Vec::new(),
        def_at: HashMap::new(),
        ref_at: HashSet::new(),
        kids: HashMap::new(),
        stored: HashSet::new(),
        builtins: HashMap::new(),
        contracts: HashMap::new(),
        c: None,
        base: 0,
        names: HashMap::new(),
        funcs: Vec::new(),
        storage_params: HashMap::new(),
        syms: HashMap::new(),
        type_names: HashMap::new(),
        file: 0,
        func: None,
        module: None,
    };
    b.file(root);
    for c in units {
        b.c = Some(c);
        b.contract();
    }
    for c in units {
        b.unit(c);
    }
    for c in units {
        let key = (c.prog.origin.clone(), c.prog.contract_name.clone());
        let Some(scope) = c.prog.scopes.scope(&key) else {
            continue;
        };
        let decls = &c.prog.scopes.decls;
        let names = scope.names.iter().map(|(k, entries)| (k, entries[0].decl));
        let modules = scope.modules.iter().map(|(k, entry)| (k, entry.decl));
        for (spelled, decl) in names.chain(modules) {
            b.ix.spelled
                .insert(spelled.clone(), decls[decl].canonical.clone());
        }
    }
    b.ix
}

struct Builder<'a> {
    ix: Index,
    root: String,
    text: &'a str,
    file_ids: HashMap<String, usize>,
    starts: Vec<Vec<usize>>,
    def_at: HashMap<(usize, u32, u32), usize>,
    ref_at: HashSet<(usize, u32, u32)>,
    kids: HashMap<(usize, String), usize>,
    /// Fields declared inside storage, whose hover already says where they are stored.
    stored: HashSet<usize>,
    builtins: HashMap<String, usize>,
    contracts: HashMap<String, usize>,
    // The unit being indexed. A file with several contracts has one per contract.
    c: Option<&'a Checked>,
    base: usize,
    names: HashMap<(char, String), usize>,
    funcs: Vec<usize>,
    /// Each function's `storage` parameters, which the checker substitutes away.
    storage_params: HashMap<(usize, String), usize>,
    syms: HashMap<usize, usize>,
    type_names: HashMap<usize, String>,
    file: usize,
    func: Option<usize>,
    module: Option<String>,
}

const BUILTINS_DOC: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/docs/src/pages/language/builtins.mdx"
));

/// The paragraph under the documentation heading that names `name`: `## \`Evm\``.
fn section_intro(name: &str) -> String {
    let mut lines = BUILTINS_DOC.lines();
    let tick = format!("`{name}`");
    for line in lines.by_ref() {
        if line.starts_with("## ") && (line.contains(&tick) || line == format!("## {name}")) {
            break;
        }
    }
    lines
        .skip_while(|l| l.trim().is_empty())
        .take_while(|l| !l.trim().is_empty())
        .collect::<Vec<_>>()
        .join("\n")
}

impl<'a> Builder<'a> {
    fn c(&self) -> &'a Checked {
        self.c.expect("a unit")
    }

    fn file(&mut self, origin: &str) -> usize {
        let path = if origin.is_empty() {
            self.root.clone()
        } else {
            origin.to_string()
        };
        if let Some(&id) = self.file_ids.get(&path) {
            return id;
        }
        let text = if path == self.root {
            self.text.to_string()
        } else if let Some(src) = std_source(Path::new(&path)) {
            src.to_string()
        } else {
            std::fs::read_to_string(&path).unwrap_or_default()
        };
        let mut starts = vec![0];
        starts.extend(text.match_indices('\n').map(|(i, _)| i + 1));
        let std = path
            .strip_prefix(STD_ROOT)
            .map(|rel| rel.trim_start_matches('/').to_string());
        let id = self.ix.files.len();
        self.ix.files.push(File { path, std, text });
        self.starts.push(starts);
        self.file_ids.insert(self.ix.files[id].path.clone(), id);
        id
    }

    fn offset(&self, file: usize, line: u32, col: u32) -> usize {
        let starts = &self.starts[file];
        let text = &self.ix.files[file].text;
        let start = starts
            .get(line.saturating_sub(1) as usize)
            .copied()
            .unwrap_or(text.len());
        let mut at = (start + col.saturating_sub(1) as usize).min(text.len());
        while !text.is_char_boundary(at) {
            at -= 1;
        }
        at
    }

    fn pos(&self, file: usize, offset: usize) -> (u32, u32) {
        let starts = &self.starts[file];
        let line = starts.partition_point(|&s| s <= offset).max(1);
        (line as u32, (offset - starts[line - 1] + 1) as u32)
    }

    /// The first whole-word `name` at or after a position: declarations start at their
    /// keyword, and a path's segments share one position.
    fn locate(&self, file: usize, line: u32, col: u32, name: &str) -> (u32, u32) {
        let text = &self.ix.files[file].text;
        let start = self.offset(file, line, col);
        let mut end = (start + 2000).min(text.len());
        while !text.is_char_boundary(end) {
            end -= 1;
        }
        let mut from = start;
        while from < end {
            let Some(i) = text[from..end].find(name) else {
                break;
            };
            let at = from + i;
            if !name.is_empty() && is_word(text, at, name.len()) {
                return self.pos(file, at);
            }
            from = at + name.len().max(1);
        }
        (line, col)
    }

    /// Where `name` is written as the label of `name = e`.
    fn label(&self, file: usize, e: &Expr, name: &str) -> Option<(u32, u32)> {
        let (line, col) = start(e);
        let text = &self.ix.files[file].text;
        let mut at = self.offset(file, line, col);
        // A folded `Address.zero` starts at `zero`.
        while let Some(dot) = text[..at].strip_suffix('.') {
            at = dot.trim_end_matches(is_ident).len();
        }
        let before = text[..at].trim_end().strip_suffix('=')?.trim_end();
        let start = before.len().checked_sub(name.len())?;
        (before.ends_with(name) && is_word(text, start, name.len())).then(|| self.pos(file, start))
    }

    /// The word that names a continuation arm: `Ok` in `then { | Ok(x : T) -> ...`, whose
    /// success arm starts at `then`.
    fn arm_word(&self, line: u32, col: u32) -> ((u32, u32), String) {
        let text = &self.ix.files[self.file].text;
        let mut at = self.offset(self.file, line, col);
        if text[at..].starts_with("then") {
            at += "then".len();
        }
        at += text[at..]
            .find(|c: char| !(c.is_whitespace() || c == '{' || c == '|'))
            .unwrap_or(0);
        let pos = self.pos(self.file, at);
        (pos, self.word_at(self.file, pos.0, pos.1).to_string())
    }

    fn word_at(&self, file: usize, line: u32, col: u32) -> &str {
        let text = &self.ix.files[file].text;
        let at = self.offset(file, line, col);
        let len = text[at..]
            .find(|c: char| !is_ident(c))
            .unwrap_or(text.len() - at);
        &text[at..at + len]
    }

    /// The comment that ends on the line before a declaration.
    fn doc(&self, file: usize, line: u32) -> String {
        let text = &self.ix.files[file].text;
        let start = self.offset(file, line, 1);
        let before = text[..start].trim_end();
        if !before.ends_with("*)") || text[before.len()..start].matches('\n').count() > 1 {
            return String::new();
        }
        let bytes = before.as_bytes();
        let mut depth = 0;
        let mut i = before.len();
        while i >= 2 {
            match &bytes[i - 2..i] {
                b"*)" => {
                    depth += 1;
                    i -= 2;
                }
                b"(*" => {
                    depth -= 1;
                    i -= 2;
                    if depth == 0 {
                        let inner = &before[i + 2..before.len() - 2];
                        return inner
                            .lines()
                            .map(str::trim)
                            .collect::<Vec<_>>()
                            .join("\n")
                            .trim()
                            .to_string();
                    }
                }
                _ => i -= 1,
            }
        }
        String::new()
    }

    fn key(&self, ty: usize) -> usize {
        self.base + ty
    }

    fn def(&mut self, at: Option<Span>, mut d: Def) -> usize {
        if let Some(at) = at {
            if let Some(&id) = self.def_at.get(&(at.file, at.line, at.col)) {
                return id;
            }
        }
        d.at = at;
        let id = self.ix.defs.len();
        if let Some(parent) = d.parent {
            self.kids.entry((parent, d.name.clone())).or_insert(id);
        }
        self.ix.defs.push(d);
        if let Some(at) = at {
            self.def_at.insert((at.file, at.line, at.col), id);
            self.reference(at, id, None);
        }
        id
    }

    fn reference(&mut self, at: Span, def: usize, hover: Option<String>) {
        if self.ref_at.insert((at.file, at.line, at.col)) {
            self.ix.refs.push(Ref { at, def, hover });
        }
    }

    fn span(&self, file: usize, (line, col): (u32, u32), name: &str) -> Span {
        Span {
            file,
            line,
            col,
            len: name.len() as u32,
        }
    }

    fn refer(&mut self, (line, col): (u32, u32), name: &str, def: Option<usize>) {
        if self.storage_param_at(line, col, name) {
            return;
        }
        if let Some(def) = def {
            let name = name.rsplit('.').next().unwrap_or(name);
            let at = self.span(self.file, self.locate(self.file, line, col, name), name);
            self.reference(at, def, None);
        }
    }

    /// Whether the word at a position is a `storage` parameter that the checker replaced
    /// with the storage the caller passed, and so refers to the parameter.
    fn storage_param_at(&mut self, line: u32, col: u32, name: &str) -> bool {
        let word = self.word_at(self.file, line, col).to_string();
        let param = self
            .func
            .and_then(|f| self.storage_params.get(&(f, word.clone())).copied());
        match param {
            Some(p) if word != name.rsplit('.').next().unwrap_or(name) => {
                let at = self.span(self.file, (line, col), &word);
                self.reference(at, p, None);
                true
            }
            _ => false,
        }
    }

    /// The function as written, before the checker specialized it for the storage its
    /// `storage` parameters are passed.
    fn template(&self, f: &Func) -> Option<&'a Func> {
        let src = &self.c().source;
        src.funcs
            .iter()
            .chain(src.modules.iter().flat_map(|m| &m.funcs))
            .find(|g| {
                g.origin == f.origin
                    && g.line == f.line
                    && g.col == f.col
                    && g.params.iter().any(|p| p.storage)
            })
    }

    /// `storage.orders[k]` passed for a `storage` parameter: the checker drops it from the
    /// call, so it is read from the text between the parentheses.
    fn storage_args(&mut self, line: u32, col: u32, name: &str, template: &Func) {
        let file = self.file;
        let text = &self.ix.files[file].text;
        let at = self.offset(file, line, col) + name.len();
        let Some(open) = text[at..].find('(').map(|i| at + i + 1) else {
            return;
        };
        let mut args = Vec::new();
        let (mut depth, mut start) = (0, open);
        for (i, ch) in text[open..].char_indices() {
            match ch {
                '(' | '[' => depth += 1,
                ')' | ']' if depth > 0 => depth -= 1,
                ',' | ')' if depth == 0 => {
                    args.push(start);
                    start = open + i + 1;
                    if ch == ')' {
                        break;
                    }
                }
                _ => {}
            }
        }
        let starts: Vec<(u32, u32)> = template
            .params
            .iter()
            .zip(&args)
            .filter(|(p, _)| p.storage)
            .map(|(_, &arg)| {
                self.pos(
                    file,
                    arg + text[arg..].len() - text[arg..].trim_start().len(),
                )
            })
            .collect();
        for (l, c) in starts {
            self.stored_arg(l, c);
        }
    }

    /// References along a stored path written at a position, resolved by name.
    fn stored_arg(&mut self, line: u32, col: u32) {
        let head = self.word_at(self.file, line, col).to_string();
        let param = self
            .func
            .and_then(|f| self.storage_params.get(&(f, head.clone())).copied());
        let d = param.or_else(|| self.place_def(&head));
        self.refer((line, col), &head, d);
        let mut ty = d.and_then(|d| self.ix.defs[d].ty);
        let text = &self.ix.files[self.file].text;
        let mut at = self.offset(self.file, line, col) + head.len();
        let mut steps = Vec::new();
        loop {
            let rest = &text[at..];
            if let Some(after) = rest.strip_prefix('.') {
                let word: String = after.chars().take_while(|&c| is_ident(c)).collect();
                if word.is_empty() {
                    break;
                }
                steps.push((Some(word.clone()), at + 1));
                at += 1 + word.len();
            } else if rest.starts_with('[') {
                let mut depth = 0;
                let len = rest
                    .char_indices()
                    .find(|&(_, c)| {
                        depth += match c {
                            '[' => 1,
                            ']' => -1,
                            _ => 0,
                        };
                        depth == 0
                    })
                    .map_or(rest.len(), |(i, _)| i + 1);
                steps.push((None, at));
                at += len;
            } else {
                break;
            }
        }
        for (word, offset) in steps {
            match word {
                Some(word) => {
                    let pos = self.pos(self.file, offset);
                    let d = ty.and_then(|t| self.member(t, &word));
                    self.refer(pos, &word, d);
                    ty = d.and_then(|d| self.ix.defs[d].ty);
                }
                None => ty = ty.and_then(|t| self.ix.tys[t].item),
            }
        }
    }

    fn unit(&mut self, c: &'a Checked) {
        self.c = Some(c);
        self.base = self.ix.tys.len();
        for i in 0..c.types.len() {
            let mut under = i;
            // A variant's cases stay themselves, as the checker's `peel` keeps them.
            while c.types[under].kind == TyKind::Nominal && c.types[under].variants.is_empty() {
                match c.types[under].elem {
                    Some(elem) if elem != under => under = elem,
                    _ => break,
                }
            }
            let item = match c.types[under].kind {
                TyKind::Map => c.types[under].right,
                TyKind::List => c.types[under].elem,
                _ => None,
            };
            self.ix.tys.push(Ty {
                under: self.base + under,
                item: item.map(|t| self.base + t),
            });
        }
        self.names.clear();
        self.syms.clear();
        self.type_names.clear();
        let mut named: Vec<(&String, &usize)> = c.named.iter().collect();
        named.sort_by_key(|(name, _)| (name.len(), name.as_str()));
        for (name, &ty) in named {
            self.type_names.entry(ty).or_insert_with(|| name.clone());
        }
        self.declare();
        self.walk();
    }

    /// The contract a unit defines, with its entrypoints.
    fn contract(&mut self) {
        let c = self.c();
        let Some(name) = &c.prog.contract_name else {
            return;
        };
        let file = self.file("");
        let at = self.locate(file, c.prog.contract_line, c.prog.contract_col, name);
        let mut entries: Vec<String> = c
            .routes
            .iter()
            .map(|r| format!("- `{}` `0x{}`", r.sig, hex(&r.sel)))
            .collect();
        for f in c.prog.funcs.iter().filter(|f| f.kind == ItemKind::View) {
            if let Ok(sig) = route::view_sig(c, f) {
                entries.push(format!("- `{sig}` `{}` (view)", selector_hex(&sig)));
            }
        }
        let mut hover = vec![
            code(&format!("contract {name}")),
            self.doc(file, c.prog.contract_line),
        ];
        if c.prog.upgradeable {
            hover.push("upgradeable".to_string());
        }
        if !entries.is_empty() {
            hover.push(format!("**Entrypoints**\n{}", entries.join("\n")));
        }
        let d = self.def(
            Some(self.span(file, at, name)),
            Def {
                name: name.clone(),
                kind: Kind::Contract,
                at: None,
                detail: format!("contract {name}"),
                hover: join(hover),
                parent: None,
                ty: None,
                params: Vec::new(),
            },
        );
        self.contracts.insert(name.clone(), d);
    }

    /// A built-in with no table row: a namespace, `Some`, `None`, a conversion, `length`.
    fn pseudo(&mut self, key: &str, detail: String, doc: String) -> usize {
        if let Some(&d) = self.builtins.get(key) {
            return d;
        }
        let name = key.rsplit(':').next().unwrap_or(key).to_string();
        let d = self.def(
            None,
            Def {
                name,
                kind: Kind::Builtin,
                at: None,
                hover: join(vec![code(&detail), doc]),
                detail,
                parent: None,
                ty: None,
                params: Vec::new(),
            },
        );
        self.builtins.insert(key.to_string(), d);
        d
    }

    /// A module the compiler implements, by its canonical name.
    fn namespace(&self, ns: &str) -> Option<usize> {
        let c = self.c();
        c.prog
            .modules
            .iter()
            .any(|m| m.name == ns && !m.intrinsics.is_empty())
            .then(|| self.names.get(&('m', ns.to_string())).copied())
            .flatten()
    }

    /// The module a name before a dot stands for in the file being walked.
    fn module_named(&self, spelled: &str) -> Option<String> {
        let c = self.c();
        let origin = &self.ix.files[self.file].path;
        let scope = c.prog.scopes.of_file(origin)?;
        let entry = scope.modules.get(spelled)?;
        Some(c.prog.scopes.decls[entry.decl].canonical.clone())
    }

    fn ty_text(&self, ty: usize) -> String {
        let c = self.c();
        if let Some(name) = self.type_names.get(&ty) {
            return name.clone();
        }
        let t = &c.types[ty];
        let sub = |id: Option<usize>| id.map_or("?".to_string(), |id| self.ty_text(id));
        match t.kind {
            TyKind::List if t.bits == 0 => format!("list({})", sub(t.elem)),
            TyKind::List => format!("list({}, {})", sub(t.elem), t.bits),
            TyKind::Option => format!("option({})", sub(t.elem)),
            TyKind::Map => format!("map({}, {})", sub(t.left), sub(t.right)),
            TyKind::Nominal => sub(t.elem),
            TyKind::Tuple => format!(
                "({})",
                t.fields
                    .iter()
                    .map(|f| self.ty_text(f.ty))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            TyKind::Record => format!(
                "record {{ {} }}",
                t.fields
                    .iter()
                    .map(|f| format!("{} : {};", f.name, self.ty_text(f.ty)))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            _ => format!("{:?}", t.kind).to_lowercase(),
        }
    }

    fn declare(&mut self) {
        let c = self.c();
        let prog = &c.prog;
        for m in &prog.modules {
            let file = self.file(&m.origin);
            let at = self.span(file, self.locate(file, m.line, m.col, &m.name), &m.name);
            let doc = self.doc(file, m.line);
            let d = self.def(
                Some(at),
                Def {
                    name: m.name.clone(),
                    kind: Kind::Module,
                    at: None,
                    detail: format!("module {}", m.name),
                    hover: String::new(),
                    parent: None,
                    ty: None,
                    params: Vec::new(),
                },
            );
            self.names.insert(('m', m.name.clone()), d);
            let domains: Vec<String> = prog
                .domains
                .iter()
                .filter(|decl| decl.owner.as_deref() == Some(&m.name))
                .map(|decl| format!("`{}` at `\"{}\"`", decl.name, decl.id))
                .collect();
            let funcs: Vec<String> = m.funcs.iter().map(|f| format!("`{}`", f.name)).collect();
            let mut hover = vec![code(&format!("module {}", m.name)), doc];
            if !domains.is_empty() {
                hover.push(format!("**Storage** {}", domains.join(", ")));
            }
            if !funcs.is_empty() {
                hover.push(format!("**Functions** {}", funcs.join(", ")));
            }
            if m.intrinsics.is_empty() && !prog.compose.iter().any(|u| u.name == m.name) {
                hover.push("not used by this contract".to_string());
            }
            self.ix.defs[d].hover = join(hover);
            for i in &m.intrinsics {
                let at = self.locate(file, i.line, i.col, &i.name);
                let text = &self.ix.files[file].text;
                let from = self.offset(file, i.line, i.col);
                let written = text[from..]
                    .split(';')
                    .next()
                    .unwrap_or("")
                    .split_whitespace()
                    .collect::<Vec<_>>()
                    .join(" ")
                    .replace("( ", "(");
                let member = format!("{}.{}", short(&m.name), i.name);
                let detail = match &i.sig {
                    Some(f) => format!(
                        "{member}({}){}",
                        f.params
                            .iter()
                            .map(param_text)
                            .collect::<Vec<_>>()
                            .join("; "),
                        ret_raises(f)
                    ),
                    // Without a signature, the doc comment's first line gives the call's
                    // shape: `keccak256(x : bytes | string) : bytes32`.
                    None => match self.doc(file, i.line).lines().next() {
                        Some(shape) => format!("{}.{shape}", short(&m.name)),
                        None => member,
                    },
                };
                let def = self.def(
                    Some(self.span(file, at, &i.name)),
                    Def {
                        name: i.name.clone(),
                        kind: Kind::Builtin,
                        at: None,
                        hover: join(vec![code(&written), self.doc(file, i.line)]),
                        detail,
                        parent: Some(d),
                        ty: None,
                        params: i
                            .sig
                            .iter()
                            .flat_map(|f| f.params.iter().map(param_text))
                            .collect(),
                    },
                );
                self.builtins.insert(format!("{}.{}", m.name, i.name), def);
            }
        }
        for decl in &prog.interfaces {
            let file = self.file(&decl.origin);
            let written = short(&decl.name);
            let at = self.span(
                file,
                self.locate(file, decl.line, decl.col, written),
                written,
            );
            let ty = c.named.get(&decl.name).copied();
            let methods = ty.and_then(|ty| c.ifaces.get(&ty));
            let mut lines = Vec::new();
            let mut sels = Vec::new();
            for m in &decl.methods {
                lines.push(format!("  {};", method_text(m)));
                if let Some(im) = methods.and_then(|ms| ms.iter().find(|im| im.name == m.name)) {
                    sels.push(format!("- `{}` `{}`", im.sig, selector_hex(&im.sig)));
                }
            }
            let hover = join(vec![
                code(&format!(
                    "interface {} is {{\n{}\n}}",
                    decl.name,
                    lines.join("\n")
                )),
                self.doc(file, decl.line),
                sels.join("\n"),
            ]);
            let d = self.def(
                Some(at),
                Def {
                    name: decl.name.clone(),
                    kind: Kind::Interface,
                    at: None,
                    detail: format!("interface {}", decl.name),
                    hover,
                    parent: None,
                    ty: ty.map(|t| self.key(t)),
                    params: Vec::new(),
                },
            );
            self.names.insert(('i', decl.name.clone()), d);
            if let Some(ty) = ty {
                self.ix.shapes.insert(self.key(ty), d);
            }
            for m in &decl.methods {
                let im = methods.and_then(|ms| ms.iter().find(|im| im.name == m.name));
                let at = self.span(file, self.locate(file, m.line, m.col, &m.name), &m.name);
                let text = method_text(m);
                let mut hover = vec![code(&text), self.doc(file, m.line)];
                if let Some(im) = im {
                    hover.push(format!(
                        "`{}` · selector `{}`",
                        im.sig,
                        selector_hex(&im.sig)
                    ));
                    if im.query {
                        hover.push("read-only: called with `query`, answers at once".to_string());
                    } else {
                        hover.push(
                            "an operation: runs with `defer`, after this transition's effects"
                                .to_string(),
                        );
                    }
                }
                self.def(
                    Some(at),
                    Def {
                        name: m.name.clone(),
                        kind: Kind::Method,
                        at: None,
                        detail: text,
                        hover: join(hover),
                        parent: Some(d),
                        ty: im.map(|im| self.key(im.ret)),
                        params: m
                            .params
                            .iter()
                            .map(|p| format!("{} : {}", p.name, ty_ref(&p.ty)))
                            .collect(),
                    },
                );
                let md = self.def_at.get(&(at.file, at.line, at.col)).copied();
                let mut from = (at.line, at.col + at.len);
                for Param { name: n, ty: t, .. } in &m.params {
                    let pos = self.locate(file, from.0, from.1, n);
                    from = (pos.0, pos.1 + n.len() as u32);
                    let text = format!("{n} : {}", ty_ref(t));
                    self.def(
                        Some(self.span(file, pos, n)),
                        Def {
                            name: n.clone(),
                            kind: Kind::Param,
                            at: None,
                            hover: join(vec![code(&text), format!("parameter of `{}`", m.name)]),
                            detail: text,
                            parent: md,
                            ty: None,
                            params: Vec::new(),
                        },
                    );
                }
            }
        }
        for decl in &prog.types {
            let file = self.file(&decl.origin);
            let written = short(&decl.name);
            let at = self.span(
                file,
                self.locate(file, decl.line, decl.col, written),
                written,
            );
            let ty = c.named.get(&decl.name).copied();
            let storage = decl.name == "storage";
            let text = if storage {
                format!("storage is {}", ty_ref_long(&decl.ty))
            } else {
                format!("type {} is {}", decl.name, ty_ref_long(&decl.ty))
            };
            let mut hover = vec![code(&text), self.doc(file, decl.line)];
            if storage {
                if let Some(layout) = c.layout.iter().find(|l| l.name == "storage") {
                    hover.push(format!(
                        "```text\n{}\n```",
                        crate::format_layout(std::slice::from_ref(layout)).trim_end()
                    ));
                }
            }
            let d = self.def(
                Some(at),
                Def {
                    name: decl.name.clone(),
                    kind: if storage { Kind::Storage } else { Kind::Type },
                    at: None,
                    detail: text.lines().next().unwrap_or("").to_string(),
                    hover: join(hover),
                    parent: None,
                    ty: ty.map(|t| self.key(t)),
                    params: Vec::new(),
                },
            );
            self.names.insert(('t', decl.name.clone()), d);
            if let Some(ty) = ty {
                let path = storage.then(|| "storage".to_string());
                self.shape(&decl.ty, ty, d, file, path.as_deref());
            }
        }
        for decl in &prog.domains {
            let file = self.file(&decl.origin);
            let written = short(&decl.name);
            let at = self.span(
                file,
                self.locate(file, decl.line, decl.col, written),
                written,
            );
            let qualified = match &decl.owner {
                Some(module) => format!("{module}.{}", decl.name),
                None => decl.name.clone(),
            };
            let ty = c.domain_tys.get(&qualified).copied();
            let space = if decl.transient {
                "transient storage"
            } else {
                "storage"
            };
            let text = if decl.transient {
                format!(
                    "transient storage {} is {}",
                    decl.name,
                    ty_ref_long(&decl.ty)
                )
            } else {
                format!(
                    "storage {} at \"{}\" is {}",
                    decl.name,
                    decl.id,
                    ty_ref_long(&decl.ty)
                )
            };
            let mut hover = vec![code(&text), self.doc(file, decl.line)];
            let layouts = if decl.transient {
                &c.transient_layout
            } else {
                &c.layout
            };
            if let Some(layout) = layouts.iter().find(|l| l.name == qualified) {
                let body = if decl.transient {
                    crate::format_transient(std::slice::from_ref(layout))
                } else {
                    crate::format_layout(std::slice::from_ref(layout))
                };
                hover.push(format!("```text\n{}\n```", body.trim_end()));
            }
            let parent = decl
                .owner
                .as_ref()
                .and_then(|m| self.names.get(&('m', m.clone())).copied());
            let d = self.def(
                Some(at),
                Def {
                    name: decl.name.clone(),
                    kind: Kind::Storage,
                    at: None,
                    detail: format!("{space} {qualified}"),
                    hover: join(hover),
                    parent,
                    ty: ty.map(|t| self.key(t)),
                    params: Vec::new(),
                },
            );
            self.names.insert(('d', qualified.clone()), d);
            if let Some(ty) = ty {
                let path = if decl.transient {
                    format!("transient {qualified}")
                } else {
                    qualified.clone()
                };
                self.shape(&decl.ty, ty, d, file, Some(&path));
            }
        }
        for decl in &prog.errors {
            let file = self.file(&decl.origin);
            let written = short(&decl.name);
            let at = self.span(
                file,
                self.locate(file, decl.line, decl.col, written),
                written,
            );
            let info = c.errors.iter().find(|e| e.name == decl.name);
            let text = match &decl.payload {
                Some(t) => format!("error {} of {}", decl.name, ty_ref_long(t)),
                None => format!("error {}", decl.name),
            };
            let mut hover = vec![code(&text), self.doc(file, decl.line)];
            if let Some(info) = info {
                hover.push(format!(
                    "`{}` · selector `0x{}`",
                    info.abi_sig,
                    hex(&info.selector)
                ));
                let raisers: Vec<String> = c
                    .routes
                    .iter()
                    .filter(|r| r.raises.contains(&info.abi_sig))
                    .map(|r| format!("`{}`", r.name))
                    .chain(
                        prog.funcs
                            .iter()
                            .filter(|f| {
                                matches!(f.kind, ItemKind::View | ItemKind::Deploy)
                                    && f.errors.iter().any(|&e| {
                                        c.errors.get(e).is_some_and(|e| e.name == decl.name)
                                    })
                            })
                            .map(|f| format!("`{}`", short(&f.name))),
                    )
                    .collect();
                hover.push(if raisers.is_empty() {
                    "no entrypoint raises it".to_string()
                } else {
                    format!("**Raised by** {}", raisers.join(", "))
                });
            }
            let d = self.def(
                Some(at),
                Def {
                    name: decl.name.clone(),
                    kind: Kind::Error,
                    at: None,
                    detail: text.lines().next().unwrap_or("").to_string(),
                    hover: join(hover),
                    parent: None,
                    ty: info.and_then(|i| i.payload).map(|t| self.key(t)),
                    params: Vec::new(),
                },
            );
            self.names.insert(('e', decl.name.clone()), d);
            if let (Some(t), Some(ty)) = (&decl.payload, info.and_then(|i| i.payload)) {
                self.shape(t, ty, d, file, None);
            }
        }
        for set in &prog.error_sets {
            let file = self.file("");
            let at = self.span(
                file,
                self.locate(file, set.line, set.col, &set.name),
                &set.name,
            );
            let members: Vec<&str> = set.members.iter().map(|m| m.name.as_str()).collect();
            let text = format!("errors {} is | {}", set.name, members.join(" | "));
            let d = self.def(
                Some(at),
                Def {
                    name: set.name.clone(),
                    kind: Kind::ErrorSet,
                    at: None,
                    detail: text.clone(),
                    hover: join(vec![code(&text), self.doc(file, set.line)]),
                    parent: None,
                    ty: None,
                    params: Vec::new(),
                },
            );
            self.names.insert(('s', set.name.clone()), d);
        }
        for decl in &prog.events {
            let file = self.file(&decl.origin);
            let written = short(&decl.name);
            let at = self.span(
                file,
                self.locate(file, decl.line, decl.col, written),
                written,
            );
            let info = c.events.iter().find(|e| e.name == decl.name);
            let fields: Vec<String> = decl
                .fields
                .iter()
                .map(|f| {
                    let indexed = if f.indexed { "indexed " } else { "" };
                    format!("  {indexed}{} : {};", f.name, ty_ref(&f.ty))
                })
                .collect();
            let anonymous = if decl.anonymous { "anonymous " } else { "" };
            let text = format!(
                "{anonymous}event {} of record {{\n{}\n}}",
                decl.name,
                fields.join("\n")
            );
            let mut hover = vec![code(&text), self.doc(file, decl.line)];
            if let Some(info) = info {
                if decl.anonymous {
                    hover.push(format!(
                        "`{}` · anonymous: no topic0, so logs are found by their indexed fields",
                        info.topic_sig
                    ));
                } else {
                    let topic = crate::keccak::keccak256(info.topic_sig.as_bytes());
                    hover.push(format!("`{}` · topic0 `0x{}`", info.topic_sig, hex(&topic)));
                }
                let hashed: Vec<String> = info
                    .fields
                    .iter()
                    .filter(|f| f.hashed)
                    .map(|f| format!("`{}`", f.name))
                    .collect();
                if !hashed.is_empty() {
                    hover.push(format!(
                        "{} indexed by hash: the log holds only its keccak",
                        hashed.join(", ")
                    ));
                }
                let emitters: Vec<String> = c
                    .routes
                    .iter()
                    .filter(|r| {
                        r.events
                            .iter()
                            .chain(r.phases.iter().flat_map(|p| &p.events))
                            .any(|e| bare(e) == decl.name)
                    })
                    .map(|r| format!("`{}`", r.name))
                    .collect();
                hover.push(if emitters.is_empty() {
                    "no entrypoint emits it".to_string()
                } else {
                    format!("**Emitted by** {}", emitters.join(", "))
                });
            }
            let d = self.def(
                Some(at),
                Def {
                    name: decl.name.clone(),
                    kind: Kind::Event,
                    at: None,
                    detail: format!("event {}", decl.name),
                    hover: join(hover),
                    parent: None,
                    ty: None,
                    params: Vec::new(),
                },
            );
            self.names.insert(('v', decl.name.clone()), d);
            for f in &decl.fields {
                let at = self.span(file, self.locate(file, f.line, f.col, &f.name), &f.name);
                let indexed = if f.indexed { "indexed " } else { "" };
                let text = format!("{indexed}{} : {}", f.name, ty_ref(&f.ty));
                let ty = info
                    .and_then(|i| i.fields.iter().find(|g| g.name == f.name))
                    .map(|g| self.key(g.ty));
                self.def(
                    Some(at),
                    Def {
                        name: f.name.clone(),
                        kind: Kind::Field,
                        at: None,
                        detail: text.clone(),
                        hover: join(vec![code(&text), format!("field of event `{}`", decl.name)]),
                        parent: Some(d),
                        ty,
                        params: Vec::new(),
                    },
                );
            }
        }
        let views: Vec<(String, route::Footprint)> = prog
            .funcs
            .iter()
            .filter(|f| f.kind == ItemKind::View)
            .map(|f| {
                (
                    short(&f.name).to_string(),
                    route::footprint(c, &f.stmts, f.tail.as_ref()),
                )
            })
            .collect();
        self.funcs.clear();
        for f in &prog.funcs {
            if let Some(d) = self.hook_def(f) {
                self.funcs.push(d);
                continue;
            }
            let file = self.file(&f.origin);
            let name = short(&f.name);
            // A member of a named interface is written there, not at the `exposing` naming it.
            // A function the compiler writes, such as `supportsInterface`, is written nowhere.
            let found = self.locate(file, f.line, f.col, name);
            let written = found.0 <= f.line + 1 && self.word_at(file, found.0, found.1) == name;
            let at = (f.interface.is_none() && written).then(|| self.span(file, found, name));
            // An exposed entrypoint is declared in an interface's form.
            let written_as = self.template(f).unwrap_or(f);
            let (text, params) = if f.promoted.is_some() {
                let params = f
                    .params
                    .iter()
                    .map(|p| format!("{} : {}", p.name, ty_ref(&p.ty)))
                    .collect();
                (method_text(f), params)
            } else {
                (
                    func_text(written_as),
                    written_as.params.iter().map(param_text).collect(),
                )
            };
            let runs = match (&f.promoted, &f.declares) {
                (Some(m), Some(implementation)) => {
                    format!("runs `{m}`'s external `{}`", short(implementation))
                }
                _ => String::new(),
            };
            let hover = join(vec![
                code(&text),
                self.doc(file, f.line),
                runs,
                self.func_facts(f, &views),
            ]);
            let parent = f
                .module
                .as_ref()
                .and_then(|m| self.names.get(&('m', m.clone())).copied());
            let external = matches!(
                f.kind,
                ItemKind::Entry
                    | ItemKind::View
                    | ItemKind::Migrate
                    | ItemKind::Deploy
                    | ItemKind::Receive
                    | ItemKind::Fallback
            );
            let shown = if f.module.is_some() {
                name
            } else {
                published(&f.name)
            };
            let d = self.def(
                at,
                Def {
                    name: shown.to_string(),
                    kind: if external {
                        Kind::External
                    } else {
                        Kind::Function
                    },
                    at: None,
                    detail: text,
                    hover,
                    parent,
                    ty: Some(self.key(f.ret_ty)),
                    params,
                },
            );
            self.funcs.push(d);
        }
    }

    /// A module's hook, as its code calls it: declared in the module, with what the contract
    /// does for it. The contract's entrypoint a facet calls a hook back through is written
    /// nowhere.
    fn hook_def(&mut self, f: &Func) -> Option<usize> {
        let of = f.hook_of.as_ref()?;
        let c = self.c();
        let hidden = Def {
            name: published(&f.name).to_string(),
            kind: Kind::External,
            at: None,
            detail: String::new(),
            hover: String::new(),
            parent: None,
            ty: None,
            params: Vec::new(),
        };
        let found = c
            .prog
            .modules
            .iter()
            .find(|m| m.name == of.module.name)
            .and_then(|m| Some((m, m.hooks.iter().find(|h| h.name == of.name)?)));
        let (Some((m, sig)), false) = (found, of.form == HookForm::Entry) else {
            return Some(self.def(None, hidden));
        };
        let file = self.file(&m.origin);
        let at = self.span(
            file,
            self.locate(file, sig.line, sig.col, &sig.name),
            &sig.name,
        );
        let effect = match sig.kind {
            ItemKind::Readonly => "view ",
            ItemKind::Pure => "pure ",
            _ => "",
        };
        let params: Vec<String> = sig.params.iter().map(param_text).collect();
        let ret = sig
            .ret
            .as_ref()
            .map(|t| format!(" : {}", ty_ref(t)))
            .unwrap_or_default();
        let text = format!("{effect}hook {}({}){ret}", sig.name, params.join("; "));
        let hook = format!("{}.{}", crate::modules::shown(&m.name), sig.name);
        let status = match of.form {
            HookForm::Body | HookForm::Via(_) => {
                format!("the contract implements it: `hook {hook} ...`")
            }
            HookForm::Skip => format!("the contract skips it: `hook {hook} is skip;`"),
            _ => "the contract that uses the module implements it".to_string(),
        };
        let hover = join(vec![code(&text), self.doc(file, sig.line), status]);
        let parent = self.names.get(&('m', m.name.clone())).copied();
        Some(self.def(
            Some(at),
            Def {
                name: sig.name.clone(),
                kind: Kind::Function,
                at: None,
                detail: text,
                hover,
                parent,
                ty: Some(self.key(f.ret_ty)),
                params,
            },
        ))
    }

    /// Declares the fields and variants a type spells out, under `parent`. `path` names a
    /// stored field, as footprints do: `storage.orders.status`.
    fn shape(&mut self, t: &TypeRef, ty: usize, parent: usize, file: usize, path: Option<&str>) {
        let c = self.c();
        let under = self.ix.tys[self.key(ty)].under - self.base;
        let rt = &c.types[under];
        match t {
            TypeRef::Record { fields, .. } if rt.kind == TyKind::Record => {
                self.ix.shapes.entry(self.key(under)).or_insert(parent);
                let owner = self.ix.defs[parent].name.clone();
                for f in fields {
                    let fty = rt.fields.iter().find(|r| r.name == f.name).map(|r| r.ty);
                    let at = self.span(file, self.locate(file, f.line, f.col, &f.name), &f.name);
                    let text = format!("{} : {}", f.name, ty_ref(&f.ty));
                    let sub = path.map(|p| format!("{p}.{}", f.name));
                    let mut hover = vec![code(&text), self.doc(file, f.line)];
                    match &sub {
                        Some(sub) => {
                            let place = self.place(path.unwrap_or(""), &f.name);
                            hover.push(format!("stored at `{sub}`{place}"));
                            hover.push(self.access(sub));
                        }
                        None => hover.push(format!("field of `{owner}`")),
                    }
                    let d = self.def(
                        Some(at),
                        Def {
                            name: f.name.clone(),
                            kind: Kind::Field,
                            at: None,
                            detail: text,
                            hover: join(hover),
                            parent: Some(parent),
                            ty: fty.map(|t| self.key(t)),
                            params: Vec::new(),
                        },
                    );
                    if sub.is_some() {
                        self.stored.insert(d);
                    }
                    if let Some(fty) = fty {
                        self.shape(&f.ty, fty, d, file, sub.as_deref());
                    }
                }
            }
            TypeRef::Variant { variants, .. } if !rt.variants.is_empty() => {
                self.ix.shapes.entry(self.key(under)).or_insert(parent);
                let owner = self.ix.defs[parent].name.clone();
                for v in variants {
                    let payload = rt
                        .variants
                        .iter()
                        .find(|r| r.name == v.name)
                        .and_then(|r| r.payload);
                    let at = self.span(file, self.locate(file, v.line, v.col, &v.name), &v.name);
                    let text = match &v.payload {
                        Some(p) if !v.param.is_empty() => {
                            format!("| {} of ({} : {})", v.name, v.param, ty_ref(p))
                        }
                        Some(p) => format!("| {} of {}", v.name, ty_ref(p)),
                        None => format!("| {}", v.name),
                    };
                    let hover = join(vec![
                        code(&text),
                        self.doc(file, v.line),
                        format!("variant of `{owner}`"),
                        self.entrypoint(&v.name),
                    ]);
                    let d = self.def(
                        Some(at),
                        Def {
                            name: v.name.clone(),
                            kind: Kind::Variant,
                            at: None,
                            detail: text,
                            hover,
                            parent: Some(parent),
                            ty: Some(self.key(ty)),
                            params: v.payload.iter().map(ty_ref).collect(),
                        },
                    );
                    if let (Some(p), Some(pty)) = (&v.payload, payload) {
                        self.shape(p, pty, d, file, None);
                    }
                }
            }
            TypeRef::List { elem, .. } | TypeRef::Option { elem, .. } => {
                if let Some(e) = rt.elem {
                    self.shape(elem, e, parent, file, path);
                }
            }
            TypeRef::Map { val, .. } => {
                if let Some(v) = rt.right {
                    self.shape(val, v, parent, file, path);
                }
            }
            _ => {}
        }
    }

    /// Where a top-level stored field sits.
    fn place(&self, domain: &str, field: &str) -> String {
        let c = self.c();
        let (layouts, name) = match domain.strip_prefix("transient ") {
            Some(name) => (&c.transient_layout, name),
            None => (&c.layout, domain),
        };
        layouts
            .iter()
            .find(|l| l.name == name)
            .and_then(|l| {
                let i = l.fields.iter().position(|(n, _)| n == field)?;
                Some(format!(" · {}", l.places[i]))
            })
            .unwrap_or_default()
    }

    /// What a use of a field adds when the field is reached through storage.
    fn stored_hover(&self, d: usize, path: &str) -> Option<String> {
        let field = self.ix.defs[d].kind == Kind::Field;
        (field && !self.stored.contains(&d)).then(|| {
            join(vec![
                self.ix.defs[d].hover.clone(),
                format!("stored at `{path}`"),
                self.access(path),
            ])
        })
    }

    /// Which entrypoints read and write a stored path.
    fn access(&self, path: &str) -> String {
        let c = self.c();
        let hits = |labels: Vec<&String>| {
            labels.into_iter().any(|l| {
                let l = l.strip_prefix("transient ").unwrap_or(l);
                let p = path.strip_prefix("transient ").unwrap_or(path);
                l == p || l.starts_with(&format!("{p}.")) || l.starts_with(&format!("{p}["))
            })
        };
        let mut writers = Vec::new();
        let mut readers = Vec::new();
        for r in &c.routes {
            if hits(
                r.writes
                    .iter()
                    .chain(r.phases.iter().flat_map(|p| &p.writes))
                    .collect(),
            ) {
                writers.push(format!("`{}`", r.name));
            }
            if hits(
                r.reads
                    .iter()
                    .chain(r.phases.iter().flat_map(|p| &p.reads))
                    .collect(),
            ) {
                readers.push(format!("`{}`", r.name));
            }
        }
        for f in c.prog.funcs.iter().filter(|f| f.kind == ItemKind::View) {
            let fx = route::footprint(c, &f.stmts, f.tail.as_ref());
            if hits(fx.reads.iter().collect()) {
                readers.push(format!("`{}`", short(&f.name)));
            }
        }
        let mut out = Vec::new();
        if !writers.is_empty() {
            out.push(format!("**Written by** {}", writers.join(", ")));
        }
        if !readers.is_empty() {
            out.push(format!("**Read by** {}", readers.join(", ")));
        }
        if out.is_empty() {
            return "no entrypoint reads or writes it".to_string();
        }
        out.join(" · ")
    }

    /// The entrypoint a dispatch arm becomes, for a variant of that name.
    fn entrypoint(&self, variant: &str) -> String {
        self.c()
            .routes
            .iter()
            .filter(|r| r.path.len() > 1 && r.case.as_deref() == Some(variant))
            .map(route_line)
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn func_facts(&self, f: &Func, views: &[(String, route::Footprint)]) -> String {
        let c = self.c();
        let mut out = Vec::new();
        match f.kind {
            ItemKind::Entry => {
                let routes: Vec<&Route> = c
                    .routes
                    .iter()
                    .filter(|r| r.path.first() == Some(&f.name))
                    .collect();
                if let [r] = routes.as_slice() {
                    if r.path.len() == 1 {
                        out.push(format!("`{}` · selector `0x{}`", r.sig, hex(&r.sel)));
                        out.push(effects(
                            &r.reads,
                            &r.writes,
                            &r.events,
                            &r.operations,
                            &r.queries,
                            &r.raises,
                        ));
                        out.extend(phases(r));
                    } else {
                        out.push(format!("**Entrypoints**\n{}", route_line(r)));
                    }
                } else if !routes.is_empty() {
                    let lines: Vec<String> = routes.iter().map(|r| route_line(r)).collect();
                    out.push(format!("**Entrypoints**\n{}", lines.join("\n")));
                }
                if routes
                    .iter()
                    .any(|r| !r.operations.is_empty() || !r.phases.is_empty())
                {
                    out.push(if f.nonreentrant {
                        "rejects re-entry while its deferred calls run".to_string()
                    } else {
                        "callable again while its deferred calls run".to_string()
                    });
                }
            }
            ItemKind::View => {
                if let Ok(sig) = route::view_sig(c, f) {
                    out.push(format!("`{sig}` · selector `{}`", selector_hex(&sig)));
                }
                let fx = route::footprint(c, &f.stmts, f.tail.as_ref());
                out.push(effects(
                    &fx.reads,
                    &[],
                    &[],
                    &[],
                    &fx.queries,
                    &raises(c, f),
                ));
            }
            _ => {
                let fx = route::footprint(c, &f.stmts, f.tail.as_ref());
                let mut writes = fx.writes.clone();
                let mut events = fx.events.clone();
                let mut ops = fx.operations.clone();
                for p in &fx.phases {
                    writes.extend(p.writes.iter().cloned());
                    events.extend(p.events.iter().cloned());
                    ops.extend(p.operations.iter().cloned());
                }
                out.push(effects(
                    &fx.reads,
                    &writes,
                    &events,
                    &ops,
                    &fx.queries,
                    &raises(c, f),
                ));
                let mut from: Vec<String> = c
                    .routes
                    .iter()
                    .filter(|r| r.path.first() != Some(&f.name))
                    .filter(|r| r.path.iter().chain(&r.calls).any(|n| n == &f.name))
                    .map(|r| r.name.clone())
                    .chain(
                        views
                            .iter()
                            .filter(|(_, fx)| fx.calls.contains(&f.name))
                            .map(|(n, _)| n.clone()),
                    )
                    .map(|n| format!("`{n}`"))
                    .collect();
                // Overloads share a name.
                from.dedup();
                if !from.is_empty() && !matches!(f.kind, ItemKind::Migrate | ItemKind::Deploy) {
                    out.push(format!("**Reached from** {}", from.join(", ")));
                }
                if f.exported.is_some() {
                    let exposed: Vec<String> = c
                        .prog
                        .funcs
                        .iter()
                        .filter(|g| g.declares.as_deref() == Some(&f.name))
                        .flat_map(|g| self.entry_lines(g))
                        .collect();
                    out.push(if exposed.is_empty() {
                        "no contract exposes it".to_string()
                    } else {
                        format!("**Exposed as**\n{}", exposed.join("\n"))
                    });
                }
            }
        }
        join(out)
    }

    fn walk(&mut self) {
        let c = self.c();
        let prog = &c.prog;
        for decl in &prog.types {
            self.file = self.file(&decl.origin);
            self.type_refs(&decl.ty);
        }
        for decl in &prog.domains {
            self.file = self.file(&decl.origin);
            self.type_refs(&decl.ty);
        }
        for decl in &prog.errors {
            self.file = self.file(&decl.origin);
            if let Some(t) = &decl.payload {
                self.type_refs(t);
            }
        }
        for decl in &prog.events {
            self.file = self.file(&decl.origin);
            for f in &decl.fields {
                self.type_refs(&f.ty);
            }
        }
        for decl in &prog.interfaces {
            self.file = self.file(&decl.origin);
            for m in &decl.methods {
                for p in &m.params {
                    self.type_refs(&p.ty);
                }
                if let Some(ret) = &m.ret {
                    self.type_refs(ret);
                }
            }
        }
        for (origin, target) in &c.conversions {
            self.file = self.file(origin);
            self.type_refs(target);
        }
        self.file = self.file("");
        for set in &prog.error_sets {
            for m in &set.members {
                let d = self.error_name(&m.name);
                let at = self.locate(self.file, m.line, m.col, &m.name);
                self.refer(at, &m.name, d);
            }
        }
        for u in &prog.compose {
            let d = self.names.get(&('m', u.name.clone())).copied();
            let at = self.locate(self.file, u.line, u.col, &u.name);
            self.refer(at, &u.name, d);
        }
        if let Some(guard) = &prog.guard {
            self.func = None;
            self.module = None;
            self.stmts(&guard.stmts);
        }
        for exposed in &prog.exposes {
            for named in &exposed.interfaces {
                let d = self.names.get(&('i', named.name.clone())).copied();
                let entries: Vec<String> = prog
                    .funcs
                    .iter()
                    .filter(|f| {
                        f.interface.as_deref() == Some(&named.name)
                            && f.promoted.as_deref() == Some(&exposed.module)
                    })
                    .flat_map(|f| self.entry_lines(f))
                    .collect();
                if let Some(d) = d {
                    let hover = join(vec![
                        self.ix.defs[d].hover.clone(),
                        format!(
                            "**Exposed from `{}`**\n{}",
                            exposed.module,
                            entries.join("\n")
                        ),
                    ]);
                    let at = self.locate(self.file, named.line, named.col, &named.name);
                    let span = self.span(self.file, at, &named.name);
                    self.reference(span, d, Some(hover));
                }
            }
        }
        // The checker's second pass, which adds `supportsInterface`, clears the program's list.
        for named in &c.source.supports {
            let d = self.names.get(&('i', named.name.clone())).copied();
            let at = self.locate(self.file, named.line, named.col, &named.name);
            self.refer(at, &named.name, d);
        }
        for (i, f) in prog.funcs.iter().enumerate() {
            self.file = self.file(&f.origin);
            self.func = Some(self.funcs[i]);
            self.module = f.module.clone();
            if self.ix.defs[self.funcs[i]].at.is_none() && f.interface.is_none() {
                continue;
            }
            if let Some(t) = self.template(f) {
                for p in t.params.iter().filter(|p| p.storage) {
                    self.type_refs(&p.ty);
                    let pos = self.locate(self.file, p.line, p.col, &p.name);
                    let text = param_text(p);
                    let d = self.def(
                        Some(self.span(self.file, pos, &p.name)),
                        Def {
                            name: p.name.clone(),
                            kind: Kind::Param,
                            at: None,
                            hover: join(vec![
                                code(&text),
                                "a reference to the storage each caller passes, which the function may write".to_string(),
                            ]),
                            detail: text,
                            parent: self.func,
                            ty: None,
                            params: Vec::new(),
                        },
                    );
                    self.storage_params
                        .insert((self.funcs[i], p.name.clone()), d);
                }
            }
            // A named interface's member is written in the interface, which is indexed there.
            if f.interface.is_none() {
                for p in &f.params {
                    self.type_refs(&p.ty);
                    self.local(p.line, p.col, &p.name, p.sym, param_word(p), Kind::Param);
                }
                if let Some(t) = &f.ret {
                    self.type_refs(t);
                }
                if let Some(raises) = &f.raises {
                    for part in &raises.parts {
                        let d = self.error_name(&part.name).or_else(|| {
                            (part.name == "forwarded").then(|| {
                                self.pseudo(
                                    "forwarded",
                                    "raises forwarded".to_string(),
                                    "raw revert data passed on with `fail forward`: no declared error, so no selector".to_string(),
                                )
                            })
                        });
                        let at = self.locate(self.file, part.line, part.col, &part.name);
                        self.refer(at, &part.name, d);
                    }
                }
            }
            // An exposed entrypoint runs its module external's body, indexed there.
            if f.promoted.is_some() {
                continue;
            }
            self.stmts(&f.stmts);
            if let Some(tail) = &f.tail {
                self.expr(tail);
            }
        }
    }

    /// One line per entrypoint a function is: its selector and effects.
    fn entry_lines(&self, f: &Func) -> Vec<String> {
        let c = self.c();
        let mut out: Vec<String> = c
            .routes
            .iter()
            .filter(|r| r.path.first() == Some(&f.name))
            .map(route_line)
            .collect();
        if f.kind == ItemKind::View {
            if let Ok(sig) = route::view_sig(c, f) {
                let fx = route::footprint(c, &f.stmts, f.tail.as_ref());
                out.push(format!(
                    "- `{sig}` `{}` — {}",
                    selector_hex(&sig),
                    effects(&fx.reads, &[], &[], &[], &fx.queries, &raises(c, f))
                ));
            }
        }
        out
    }

    fn error_name(&self, name: &str) -> Option<usize> {
        self.names
            .get(&('e', name.to_string()))
            .or_else(|| self.names.get(&('s', name.to_string())))
            .copied()
    }

    fn type_name(&self, name: &str) -> Option<usize> {
        self.names
            .get(&('t', name.to_string()))
            .or_else(|| self.names.get(&('i', name.to_string())))
            .copied()
    }

    /// The named constants in a list length, which the checker evaluates but never checks
    /// as calls: `list(T, M.n())`.
    fn size_refs(&mut self, e: &Expr) {
        match e {
            Expr::Binary { left, right, .. } => {
                self.size_refs(left);
                self.size_refs(right);
            }
            Expr::Call {
                line,
                col,
                name,
                args,
                base,
                ..
            } => {
                let key = match base.as_deref() {
                    Some(Expr::Ident {
                        line, col, name: m, ..
                    }) => {
                        let d = self.names.get(&('m', m.clone())).copied();
                        self.refer((*line, *col), m, d);
                        format!("{m}.{name}")
                    }
                    _ => name.clone(),
                };
                let c = self.c();
                let d = c
                    .prog
                    .funcs
                    .iter()
                    .position(|f| f.name == key)
                    .and_then(|i| self.funcs.get(i).copied())
                    .or_else(|| self.type_name(name));
                let short_name = short(name);
                let pos = self.locate(self.file, *line, *col, short_name);
                self.refer(pos, short_name, d);
                for a in args {
                    self.size_refs(a);
                }
            }
            _ => {}
        }
    }

    fn type_refs(&mut self, t: &TypeRef) {
        match t {
            TypeRef::Name { line, col, name } => {
                let d = self.type_name(name);
                self.refer((*line, *col), name, d);
            }
            TypeRef::Record { fields, .. } => {
                for f in fields {
                    self.type_refs(&f.ty);
                }
            }
            TypeRef::Variant { variants, .. } => {
                for v in variants {
                    if let Some(p) = &v.payload {
                        self.type_refs(p);
                    }
                }
            }
            TypeRef::List { elem, size, .. } => {
                if let Some(size) = size {
                    self.size_refs(size);
                }
                self.type_refs(elem);
            }
            TypeRef::Option { elem, .. } => self.type_refs(elem),
            TypeRef::Map { key, val, .. } => {
                self.type_refs(key);
                self.type_refs(val);
            }
            TypeRef::Tuple { elems, .. } => {
                for e in elems {
                    self.type_refs(e);
                }
            }
            TypeRef::Apply { args, .. } => {
                for a in args {
                    self.type_refs(a);
                }
            }
            TypeRef::Hole { .. } => {}
        }
    }

    /// Declares a local at the first `name` from a position, and returns where it is.
    fn local(
        &mut self,
        line: u32,
        col: u32,
        name: &str,
        sym: Option<usize>,
        word: &str,
        kind: Kind,
    ) -> (u32, u32) {
        let pos = self.locate(self.file, line, col, name);
        if name == "_" || name.is_empty() {
            return pos;
        }
        let ty = sym.map(|s| self.c().syms[s].ty);
        let text = format!(
            "{word} {name} : {}",
            ty.map_or("?".to_string(), |t| self.ty_text(t))
        );
        let at = self.span(self.file, pos, name);
        let d = self.def(
            Some(at),
            Def {
                name: name.to_string(),
                kind,
                at: None,
                detail: text.clone(),
                hover: code(&text),
                parent: self.func,
                ty: ty.map(|t| self.key(t)),
                params: Vec::new(),
            },
        );
        if let Some(s) = sym {
            self.syms.insert(s, d);
        }
        pos
    }

    /// Declares names written one after another, from a position.
    fn locals(&mut self, line: u32, col: u32, names: &[String], syms: &[usize], word: &str) {
        let mut at = (line, col);
        for (i, name) in names.iter().enumerate() {
            let pos = self.local(at.0, at.1, name, syms.get(i).copied(), word, Kind::Local);
            at = (pos.0, pos.1 + name.len() as u32);
        }
    }

    /// `storage` or a storage domain, as named inside the current function.
    fn place_def(&self, name: &str) -> Option<usize> {
        if name == "storage" {
            return self.names.get(&('t', "storage".to_string())).copied();
        }
        if let Some(&d) = self.names.get(&('d', name.to_string())) {
            return Some(d);
        }
        self.module
            .as_ref()
            .and_then(|m| self.names.get(&('d', format!("{m}.{name}"))))
            .or_else(|| self.names.get(&('d', name.to_string())))
            .copied()
            .or_else(|| {
                self.names
                    .iter()
                    .find(|((tag, q), _)| *tag == 'd' && q.rsplit('.').next() == Some(name))
                    .map(|(_, d)| *d)
            })
    }

    /// A field, variant, or method of the type with this key.
    fn member(&self, key: usize, name: &str) -> Option<usize> {
        let under = self.ix.tys.get(key)?.under;
        let shape = *self.ix.shapes.get(&under)?;
        self.kids.get(&(shape, name.to_string())).copied()
    }

    /// A name used as a value that is not a local: a variant, module, or type.
    fn value_name(&self, name: &str, ty: usize) -> Option<usize> {
        self.member(self.key(ty), name)
            .filter(|&d| self.ix.defs[d].kind == Kind::Variant)
            .or_else(|| self.names.get(&('m', name.to_string())).copied())
            .or_else(|| self.type_name(name))
            .or_else(|| self.error_name(name))
    }

    /// The intrinsic `name` of the module the compiler implements named `namespace`.
    fn builtin(&self, namespace: &str, name: &str) -> Option<usize> {
        self.builtins.get(&format!("{namespace}.{name}")).copied()
    }

    fn stmts(&mut self, ss: &[Stmt]) {
        for s in ss {
            self.stmt(s);
        }
    }

    fn stmt(&mut self, s: &Stmt) {
        match s {
            Stmt::Const {
                line,
                col,
                name,
                parts,
                ty,
                expr,
                sym,
                part_syms,
            } => {
                self.expr(expr);
                self.type_refs(ty);
                if parts.is_empty() {
                    self.local(*line, *col, name, *sym, "const", Kind::Local);
                } else {
                    self.locals(*line, *col, parts, part_syms, "const");
                }
            }
            Stmt::Var {
                line,
                col,
                name,
                parts,
                ty,
                expr,
                sym,
                part_syms,
            } => {
                self.expr(expr);
                self.type_refs(ty);
                if parts.is_empty() {
                    self.local(*line, *col, name, *sym, "var", Kind::Local);
                } else {
                    self.locals(*line, *col, parts, part_syms, "var");
                }
            }
            Stmt::Assign {
                line,
                col,
                path,
                index,
                keys,
                fields,
                expr,
                root,
                ..
            } => {
                let mut path = path.as_slice();
                let mut at = (*line, *col);
                // A module's domain path starts with the module, written or not.
                if let [module, domain, ..] = path {
                    if let Some(&m) = self.names.get(&('m', module.clone())) {
                        if self.word_at(self.file, *line, *col) == module {
                            self.refer(at, module, Some(m));
                            at.1 += module.len() as u32 + 1;
                        }
                        path = &path[1..];
                        let qualified = format!("{module}.{domain}");
                        let d = self.names.get(&('d', qualified)).copied();
                        let pos = self.locate(self.file, at.0, at.1, domain);
                        self.refer(pos, domain, d);
                    }
                }
                let Some(head) = path.first() else {
                    return;
                };
                // A `storage` parameter the checker replaced: its path is not in the text.
                if self.storage_param_at(at.0, at.1, short(head)) {
                    for k in index.iter().chain(keys) {
                        self.expr(k);
                    }
                    self.expr(expr);
                    return;
                }
                let mut pos = self.locate(self.file, at.0, at.1, short(head));
                let head_def = root
                    .and_then(|s| self.syms.get(&s).copied())
                    .or_else(|| self.place_def(head));
                self.refer(pos, head, head_def);
                let mut ty = head_def.and_then(|d| self.ix.defs[d].ty);
                let stored = root.is_some_and(|s| self.c().syms[s].storage);
                let mut label = match &head_def {
                    Some(d) if self.ix.defs[*d].kind == Kind::Storage => {
                        let q = self.names.iter().find(|(k, v)| k.0 == 'd' && **v == *d);
                        q.map_or(head.clone(), |((_, q), _)| q.clone())
                    }
                    _ => head.clone(),
                };
                let walk = |b: &mut Self,
                            name: &str,
                            pos: &mut (u32, u32),
                            ty: &mut Option<usize>,
                            label: &mut String| {
                    let at = b.locate(b.file, pos.0, pos.1 + 1, name);
                    let d = ty.and_then(|t| b.member(t, name));
                    label.push('.');
                    label.push_str(name);
                    if let Some(d) = d {
                        let hover = if stored {
                            b.stored_hover(d, label)
                        } else {
                            None
                        };
                        let span = b.span(b.file, at, name);
                        b.reference(span, d, hover);
                    }
                    *ty = d.and_then(|d| b.ix.defs[d].ty);
                    *pos = at;
                };
                for seg in &path[1..] {
                    walk(self, seg, &mut pos, &mut ty, &mut label);
                }
                let keys: Vec<&Expr> = index.iter().chain(keys).collect();
                let mut next = 0;
                for (before, f) in fields {
                    for k in &keys[next..(*before).clamp(next, keys.len())] {
                        self.expr(k);
                        ty = ty.and_then(|t| self.ix.tys[t].item);
                    }
                    next = next.max(*before);
                    walk(self, f, &mut pos, &mut ty, &mut label);
                }
                for k in &keys[next.min(keys.len())..] {
                    self.expr(k);
                    ty = ty.and_then(|t| self.ix.tys[t].item);
                }
                self.expr(expr);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                self.expr(cond);
                self.stmts(then_body);
                self.stmts(else_body);
            }
            Stmt::Assert { cond, reason, .. } => {
                self.expr(cond);
                self.raised(reason);
            }
            Stmt::Fail { reason, .. } => self.raised(reason),
            Stmt::Call { expr, .. } => self.expr(expr),
            Stmt::Skip => {}
            Stmt::Emit {
                line,
                col,
                name,
                fields,
            } => {
                let pos = self.locate(self.file, *line, *col, name);
                let event = self.names.get(&('v', name.clone())).copied();
                self.refer(pos, name, event);
                for (field, e) in fields {
                    self.expr(e);
                    let d = event.and_then(|ev| self.kids.get(&(ev, field.clone())).copied());
                    if let Some(at) = self.label(self.file, e, field) {
                        self.refer(at, field, d);
                    }
                }
            }
            Stmt::Defer {
                expr,
                value,
                gas,
                then,
                ..
            } => {
                self.expr(expr);
                if let Some(g) = gas {
                    self.expr(g);
                }
                if let Some(v) = value {
                    self.expr(v);
                }
                if let Some(t) = then {
                    for arm in t.arms() {
                        if let Some(ty) = &arm.ty {
                            self.type_refs(ty);
                        }
                        let (arm_at, word) = self.arm_word(arm.line, arm.col);
                        let outcome = match word.as_str() {
                            "Ok" => Some((
                                "Ok(x : T)",
                                "the call returned: `x` is its decoded result",
                            )),
                            "Error" => Some((
                                "Error(reason : bytes)",
                                "the call reverted: `reason` is its raw revert data, and this runs as its own phase",
                            )),
                            _ => None,
                        };
                        if let Some((detail, doc)) = outcome {
                            let key = detail.split('(').next().unwrap_or(detail);
                            let d = self.pseudo(
                                &format!("then:{key}"),
                                detail.to_string(),
                                doc.to_string(),
                            );
                            self.refer(arm_at, key, Some(d));
                        }
                        self.locals(arm.line, arm.col, &arm.names, &arm.syms, "then");
                        self.stmts(&arm.stmts);
                    }
                }
            }
            Stmt::For {
                line,
                col,
                index,
                name,
                ty,
                iter,
                until,
                bound,
                body,
                counter,
                elem,
                elem_init,
                length,
                ..
            } => {
                match iter {
                    ForIter::Range { lo, hi } => {
                        self.expr(lo);
                        self.expr(hi);
                    }
                    ForIter::List(xs) => self.expr(xs),
                }
                for e in elem_init.iter().chain(length) {
                    self.expr(e);
                }
                self.type_refs(ty);
                let mut at = (*line, *col);
                if let Some(i) = index {
                    let pos = self.local(at.0, at.1, i, *counter, "for", Kind::Local);
                    at = (pos.0, pos.1 + i.len() as u32);
                }
                let sym = match iter {
                    ForIter::Range { .. } if index.is_none() => *counter,
                    _ => *elem,
                };
                self.local(at.0, at.1, name, sym, "for", Kind::Local);
                for e in until.iter().chain(bound) {
                    self.expr(e);
                }
                self.stmts(body);
            }
            Stmt::AssignTuple {
                line,
                col,
                names,
                expr,
                syms,
            } => {
                self.expr(expr);
                let mut at = (*line, *col);
                for (name, sym) in names.iter().zip(syms) {
                    let pos = self.locate(self.file, at.0, at.1, name);
                    let d = self.syms.get(sym).copied();
                    self.refer(pos, name, d);
                    at = (pos.0, pos.1 + name.len() as u32);
                }
            }
        }
    }

    fn raised(&mut self, r: &Raised) {
        let c = self.c();
        let pos = self.locate(self.file, r.line, r.col, &r.name);
        let name = r
            .index
            .and_then(|i| c.errors.get(i))
            .map_or(r.name.as_str(), |e| e.name.as_str());
        let d = self.error_name(name);
        self.refer(pos, &r.name, d);
        match &r.form {
            RaisedForm::Unit => {}
            RaisedForm::Positional(e) => self.expr(e),
            RaisedForm::Fields(fields) => {
                let payload = r.index.and_then(|i| c.errors.get(i)?.payload);
                for (field, e) in fields {
                    self.expr(e);
                    let d = payload.and_then(|t| self.member(self.key(t), field));
                    if let Some(at) = self.label(self.file, e, field) {
                        self.refer(at, field, d);
                    }
                }
            }
        }
    }

    fn expr(&mut self, e: &Expr) {
        let c = self.c();
        match e {
            Expr::Lit { line, col, ty, .. } => {
                // `Uint.max` and `Address.zero` are folded into literals where they stand.
                let word = self.word_at(self.file, *line, *col).to_string();
                let text = &self.ix.files[self.file].text;
                let at = self.offset(self.file, *line, *col);
                let spelled = text[..at]
                    .strip_suffix('.')
                    .map(|b| &b[b.trim_end_matches(is_ident).len()..])
                    .map(str::to_string);
                let ns = spelled
                    .as_deref()
                    .and_then(|ns| self.module_named(ns))
                    .filter(|ns| self.namespace(ns).is_some());
                // `Abi.interfaceId(I)` and `Abi.selector(I.f)` fold to their `bytes4`.
                let arg: Option<String> = text[at + word.len()..].strip_prefix('(').map(|inner| {
                    inner
                        .chars()
                        .take_while(|&c| is_ident(c) || c == '.')
                        .collect()
                });
                // A case with no payload is a literal of its variant.
                if ns.is_none() {
                    let d = self.member(self.key(*ty), &word);
                    self.refer((*line, *col), &word, d);
                }
                if let (Some(ns), Some(spelled)) = (ns, spelled) {
                    let d = self.builtin(&ns, &word);
                    self.refer((*line, *col), &word, d);
                    let n = self.namespace(&ns);
                    let back = col.saturating_sub(spelled.len() as u32 + 1);
                    self.refer((*line, back), &spelled, n);
                    if let Some(arg) = arg {
                        let arg_col = *col + word.len() as u32 + 1;
                        let (iface, method) = arg.split_once('.').unwrap_or((&arg, ""));
                        if let Some(i) = self.names.get(&('i', iface.to_string())).copied() {
                            self.refer((*line, arg_col), iface, Some(i));
                            let m = self.kids.get(&(i, method.to_string())).copied();
                            let method_col = arg_col + iface.len() as u32 + 1;
                            if m.is_some() {
                                self.refer((*line, method_col), method, m);
                            }
                        }
                    }
                }
            }
            Expr::Ident {
                line,
                col,
                name,
                sym,
                ty,
                ..
            } => {
                let d = sym
                    .and_then(|s| self.syms.get(&s).copied())
                    .or_else(|| {
                        sym.filter(|&s| c.syms[s].storage)
                            .and_then(|_| self.place_def(name))
                    })
                    .or_else(|| self.value_name(name, *ty))
                    .or_else(|| {
                        (name == "None").then(|| {
                            self.pseudo(
                                "None",
                                "None : option(T)".to_string(),
                                section_intro("None"),
                            )
                        })
                    });
                self.refer((*line, *col), name, d);
            }
            Expr::Field {
                line,
                col,
                base,
                name,
                root,
                ..
            } => {
                let d = match base.as_ref() {
                    Expr::Ident {
                        name: ns,
                        sym: None,
                        line: nl,
                        col: nc,
                        ..
                    } if self.namespace(ns).is_some() => {
                        let n = self.namespace(ns);
                        self.refer((*nl, *nc), ns, n);
                        self.builtin(ns, name)
                    }
                    Expr::Ident {
                        line: ml,
                        col: mc,
                        name: ns,
                        sym: None,
                        ..
                    } if self.names.contains_key(&('m', ns.clone())) => {
                        let m = self.names.get(&('m', ns.clone())).copied();
                        self.refer((*ml, *mc), ns, m);
                        self.names.get(&('d', format!("{ns}.{name}"))).copied()
                    }
                    _ => {
                        self.expr(base);
                        let under = self.ix.tys[self.key(base.ty())].under - self.base;
                        self.member(self.key(base.ty()), name).or_else(|| {
                            let sized = matches!(
                                c.types[under].kind,
                                TyKind::List | TyKind::Bytes | TyKind::String
                            );
                            (name == "length" && sized).then(|| {
                                self.pseudo(
                                    "length",
                                    "xs.length : uint".to_string(),
                                    "the number of elements of a list, or of bytes in `bytes` or a `string`".to_string(),
                                )
                            })
                        })
                    }
                };
                let hover = match (d, root) {
                    (Some(d), Some(sym)) if c.syms[*sym].storage => {
                        self.stored_hover(d, &stored_path(e))
                    }
                    _ => None,
                };
                if self.storage_param_at(*line, *col, name) {
                    return;
                }
                if let Some(d) = d {
                    let at = self.span(self.file, (*line, *col), name);
                    self.reference(at, d, hover);
                }
            }
            Expr::Index { base, index, .. } => {
                self.expr(base);
                self.expr(index);
            }
            Expr::Call { name, args, .. } if name.is_empty() => self.expr(&args[0]),
            Expr::Call {
                line,
                col,
                name,
                args,
                base,
                callee,
                builtin,
                iface,
                method,
                ty,
            } => {
                let short_name = short(name);
                let namespace = match base.as_deref() {
                    Some(Expr::Ident {
                        name: ns,
                        sym: None,
                        ..
                    }) => Some(ns.clone()),
                    _ => None,
                };
                let d = if let Some(i) = callee {
                    self.funcs.get(*i).copied()
                } else if let (Some(ity), Some(m)) = (iface, method) {
                    let im = c.ifaces.get(ity).and_then(|ms| ms.get(*m));
                    im.and_then(|im| {
                        let shape = *self.ix.shapes.get(&self.key(*ity))?;
                        self.kids.get(&(shape, im.name.clone())).copied()
                    })
                } else if let Some(b) = builtin {
                    match b {
                        crate::ast::Builtin::Some => Some(self.pseudo(
                            "Some",
                            "Some(x) : option(T)".to_string(),
                            section_intro("Some"),
                        )),
                        crate::ast::Builtin::Create => self.contracts.get(short_name).copied(),
                        crate::ast::Builtin::Cast => self.type_name(name).or_else(|| {
                            Some(self.pseudo(
                                &format!("cast:{name}"),
                                format!("{name}(x) : {name}"),
                                section_intro("Conversions"),
                            ))
                        }),
                        crate::ast::Builtin::Ctor(_) => self.value_name(short_name, *ty),
                        _ => namespace.as_deref().and_then(|ns| self.builtin(ns, name)),
                    }
                } else {
                    self.value_name(short_name, *ty)
                };
                match (base.as_deref(), &namespace) {
                    (
                        Some(Expr::Ident {
                            line, col, name, ..
                        }),
                        Some(ns),
                    ) => {
                        let m = self.names.get(&('m', ns.clone())).copied();
                        let d = m
                            .or_else(|| self.type_name(ns))
                            .or_else(|| self.namespace(ns));
                        self.refer((*line, *col), name, d);
                    }
                    (Some(b), _) => self.expr(b),
                    (None, _) => {
                        if let Some((m, _)) = name.rsplit_once('.') {
                            let d = self.names.get(&('m', m.to_string())).copied();
                            let back = col.saturating_sub(m.len() as u32 + 1);
                            if back > 0 && self.word_at(self.file, *line, back) == m {
                                self.refer((*line, back), m, d);
                            }
                        }
                    }
                }
                let pos = self.locate(self.file, *line, *col, short_name);
                self.refer(pos, short_name, d);
                if let Some(t) = callee.and_then(|i| self.template(&c.prog.funcs[i])) {
                    self.storage_args(pos.0, pos.1, short_name, t);
                }
                for a in args {
                    self.expr(a);
                }
            }
            Expr::Query { expr, .. } => self.expr(expr),
            Expr::Case { scrut, arms, .. } => {
                self.expr(scrut);
                for arm in arms {
                    let mut at = (arm.line, arm.col);
                    for ctor in &arm.ctors {
                        let pos = self.locate(self.file, at.0, at.1, ctor);
                        let d = self.member(self.key(scrut.ty()), ctor).or_else(|| {
                            match ctor.as_str() {
                                "Some" => Some(self.pseudo(
                                    "Some",
                                    "Some(x) : option(T)".to_string(),
                                    section_intro("Some"),
                                )),
                                "None" => Some(self.pseudo(
                                    "None",
                                    "None : option(T)".to_string(),
                                    section_intro("None"),
                                )),
                                _ => None,
                            }
                        });
                        self.refer(pos, ctor, d);
                        at = (pos.0, pos.1 + ctor.len() as u32);
                    }
                    if let Some(bind) = &arm.bind {
                        let p = self.local(at.0, at.1, bind, arm.bind_sym, "const", Kind::Local);
                        at = (p.0, p.1 + bind.len() as u32);
                    }
                    self.locals(at.0, at.1, &arm.tuple_names, &arm.tuple_syms, "const");
                    self.stmts(&arm.stmts);
                    self.expr(&arm.expr);
                }
            }
            Expr::Unary { expr, .. } => self.expr(expr),
            Expr::Convert { target, expr, .. } => {
                self.type_refs(target);
                self.expr(expr);
            }
            Expr::Binary { left, right, .. } => {
                self.expr(left);
                self.expr(right);
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                for e in elems {
                    self.expr(e);
                }
            }
            Expr::Record {
                line,
                col,
                fields,
                ty,
            } => {
                let word = self.word_at(self.file, *line, *col).to_string();
                if let Some(d) = self.type_name(&word) {
                    self.refer((*line, *col), &word, Some(d));
                }
                for (field, e) in fields {
                    self.expr(e);
                    let d = self.member(self.key(*ty), field);
                    if let Some(at) = self.label(self.file, e, field) {
                        self.refer(at, field, d);
                    }
                }
            }
        }
    }
}

/// Where an expression's text begins: a field or call starts at its base.
fn start(e: &Expr) -> (u32, u32) {
    match e {
        Expr::Field { base, .. } | Expr::Index { base, .. } => start(base),
        Expr::Call { base: Some(b), .. } => start(b),
        Expr::Binary { left, .. } => start(left),
        other => (other.line(), other.col()),
    }
}

/// A stored path as footprints name it: `storage.orders.status`, without keys.
fn stored_path(e: &Expr) -> String {
    match e {
        Expr::Index { base, .. } => stored_path(base),
        Expr::Field { base, name, .. } => format!("{}.{name}", stored_path(base)),
        Expr::Ident { name, .. } => name.clone(),
        _ => String::new(),
    }
}

fn raises(c: &Checked, f: &Func) -> Vec<String> {
    f.errors
        .iter()
        .map(|&e| {
            c.errors
                .get(e)
                .map_or("forwarded".to_string(), |e| e.name.clone())
        })
        .collect()
}

fn route_line(r: &Route) -> String {
    format!(
        "- `{}` `0x{}` — {}",
        r.sig,
        hex(&r.sel),
        effects(
            &r.reads,
            &r.writes,
            &r.events,
            &r.operations,
            &r.queries,
            &r.raises
        )
    )
}

fn phases(r: &Route) -> Vec<String> {
    r.phases
        .iter()
        .map(|p| {
            format!(
                "then, after `{}`: {}",
                p.after,
                effects(
                    &p.reads,
                    &p.writes,
                    &p.events,
                    &p.operations,
                    &p.queries,
                    &[]
                )
            )
        })
        .collect()
}

fn effects(
    reads: &[String],
    writes: &[String],
    events: &[String],
    operations: &[String],
    queries: &[String],
    raises: &[String],
) -> String {
    let list = |items: &[String]| {
        let mut seen = Vec::new();
        for item in items {
            let item = bare(item).to_string();
            if !seen.contains(&item) {
                seen.push(item);
            }
        }
        seen.iter()
            .map(|i| format!("`{i}`"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let parts: Vec<String> = [
        ("reads", reads),
        ("writes", writes),
        ("emits", events),
        ("defers", operations),
        ("queries", queries),
        ("raises", raises),
    ]
    .iter()
    .filter(|(_, items)| !items.is_empty())
    .map(|(word, items)| format!("{word} {}", list(items)))
    .collect();
    if parts.is_empty() {
        "no effects".to_string()
    } else {
        parts.join(" · ")
    }
}

/// An event or error without its fields: `Transfer(indexed from)` is `Transfer`.
fn bare(item: &str) -> &str {
    item.split('(').next().unwrap_or(item)
}

/// A function's header as it is declared. A module's external shows as it was written,
/// though it is checked as an internal function.
fn func_text(f: &Func) -> String {
    let (kind, payable, nonreentrant, external_pure, name) = match &f.exported {
        Some(e) => (
            e.kind,
            e.payable,
            e.nonreentrant,
            e.external_pure,
            e.name.as_str(),
        ),
        None => (
            f.kind,
            f.payable,
            f.nonreentrant,
            f.external_pure,
            short(&f.name),
        ),
    };
    let head = match kind {
        ItemKind::Entry => format!(
            "external {}{}function {name}",
            if payable { "payable " } else { "" },
            if nonreentrant { "nonreentrant " } else { "" }
        ),
        ItemKind::View if external_pure => format!("external pure function {name}"),
        ItemKind::View => format!("external view function {name}"),
        ItemKind::Function => format!("function {name}"),
        ItemKind::Readonly => format!("view function {name}"),
        ItemKind::Pure => format!("pure function {name}"),
        ItemKind::Migrate => format!("migrate {name}"),
        ItemKind::Deploy => "deploy".to_string(),
        ItemKind::Receive => return "payable receive".to_string(),
        ItemKind::Fallback => {
            return match f.forward {
                Some(Forward::Delegate) => "fallback delegates to",
                Some(Forward::Call) => "fallback forwards to",
                None => "fallback",
            }
            .to_string()
        }
    };
    let params: Vec<String> = f.params.iter().map(param_text).collect();
    format!("{head}({}){}", params.join("; "), ret_raises(f))
}

/// A header as an interface writes it: `view function f(a : T) : R raises E`.
fn method_text(m: &Func) -> String {
    let head = match m.kind {
        ItemKind::View if m.external_pure => "pure function",
        ItemKind::View | ItemKind::Readonly => "view function",
        ItemKind::Pure => "pure function",
        _ if m.payable => "payable function",
        _ => "function",
    };
    let params: Vec<String> = m
        .params
        .iter()
        .map(|p| format!("{} : {}", p.name, ty_ref(&p.ty)))
        .collect();
    format!("{head} {}({}){}", m.name, params.join("; "), ret_raises(m))
}

fn ret_raises(f: &Func) -> String {
    let mut out = String::new();
    if let Some(ret) = &f.ret {
        out.push_str(&format!(" : {}", ty_ref(ret)));
    }
    if let Some(r) = &f.raises {
        let names: Vec<&str> = r.parts.iter().map(|p| p.name.as_str()).collect();
        out.push_str(&format!(" raises {}", names.join(" | ")));
    }
    out
}

fn param_word(p: &Param) -> &'static str {
    if p.storage {
        "storage"
    } else if p.mutable {
        "var"
    } else {
        "const"
    }
}

fn param_text(p: &Param) -> String {
    format!("{} {} : {}", param_word(p), p.name, ty_ref(&p.ty))
}

fn ty_ref(t: &TypeRef) -> String {
    match t {
        TypeRef::Name { name, .. } => name.clone(),
        TypeRef::Record { fields, .. } => format!(
            "record {{ {} }}",
            fields
                .iter()
                .map(|f| format!("{} : {};", f.name, ty_ref(&f.ty)))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        TypeRef::Variant { variants, .. } => variants
            .iter()
            .map(|v| {
                let name = match &v.external {
                    Some(e) => format!("{} external {e}", v.name),
                    None => v.name.clone(),
                };
                match &v.payload {
                    Some(p) => format!("| {name} of {}", ty_ref(p)),
                    None => format!("| {name}"),
                }
            })
            .collect::<Vec<_>>()
            .join(" "),
        TypeRef::List {
            elem,
            size: Some(size),
            ..
        } => format!("list({}, {})", ty_ref(elem), size_text(size)),
        TypeRef::List {
            elem, len: None, ..
        } => format!("list({})", ty_ref(elem)),
        TypeRef::List {
            elem, len: Some(n), ..
        } => format!("list({}, {n})", ty_ref(elem)),
        TypeRef::Option { elem, .. } => format!("option({})", ty_ref(elem)),
        TypeRef::Map { key, val, .. } => format!("map({}, {})", ty_ref(key), ty_ref(val)),
        TypeRef::Tuple { elems, .. } => format!(
            "({})",
            elems.iter().map(ty_ref).collect::<Vec<_>>().join(", ")
        ),
        TypeRef::Apply {
            name, args, member, ..
        } => {
            let args: Vec<String> = args.iter().map(ty_ref).collect();
            match member {
                Some(m) => format!("{name}({}).{m}", args.join(", ")),
                None => format!("{name}({})", args.join(", ")),
            }
        }
        TypeRef::Hole { .. } => "_".to_string(),
    }
}

/// Records and variants one member to a line, for a declaration's hover.
fn ty_ref_long(t: &TypeRef) -> String {
    match t {
        TypeRef::Record { fields, .. } => format!(
            "record {{\n{}\n}}",
            fields
                .iter()
                .map(|f| format!("  {} : {};", f.name, ty_ref(&f.ty)))
                .collect::<Vec<_>>()
                .join("\n")
        ),
        TypeRef::Variant { variants, .. } => {
            let lines: Vec<String> = variants
                .iter()
                .map(|v| {
                    let name = match &v.external {
                        Some(e) => format!("{} external {e}", v.name),
                        None => v.name.clone(),
                    };
                    match &v.payload {
                        Some(p) => format!("  | {name} of {}", ty_ref(p)),
                        None => format!("  | {name}"),
                    }
                })
                .collect();
            format!("\n{}", lines.join("\n"))
        }
        other => ty_ref(other),
    }
}

/// The name as written where it is declared: `Ledger.transfer` and `erc20.lithe::f` are
/// `transfer` and `f`.
fn short(name: &str) -> &str {
    let name = name.rsplit("::").next().unwrap_or(name);
    let name = name.split(['@', '#']).next().unwrap_or(name);
    name.rsplit('.').next().unwrap_or(name)
}

/// The name as other code writes it: `Math.add` from `import ... as Math`, without the
/// file prefix of a private import or the suffix of a generic instance.
fn published(name: &str) -> &str {
    let name = name.rsplit("::").next().unwrap_or(name);
    name.split(['@', '#']).next().unwrap_or(name)
}

fn code(text: &str) -> String {
    format!("```lithe\n{text}\n```")
}

fn join(parts: Vec<String>) -> String {
    parts
        .into_iter()
        .filter(|p| !p.is_empty())
        .collect::<Vec<_>>()
        .join("\n\n")
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn selector_hex(sig: &str) -> String {
    format!("0x{}", hex(&crate::keccak::selector(sig)))
}

fn is_ident(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

fn is_word(text: &str, at: usize, len: usize) -> bool {
    let before = text[..at].chars().next_back().is_none_or(|c| !is_ident(c));
    let after = text[at + len..].chars().next().is_none_or(|c| !is_ident(c));
    before && after
}

/// A dotted path before the cursor, one segment at a time: `storage.orders[id].` is
/// `storage`, `orders`, an index, and the empty name being typed.
#[derive(Debug, PartialEq)]
enum Seg {
    Name(String, bool),
    Index,
}

/// The segments of the path that ends `text`, and where the path starts.
fn chain(text: &str) -> (Vec<Seg>, usize) {
    let bytes = text.as_bytes();
    let mut i = text.len();
    let mut segs = Vec::new();
    loop {
        let mut called = false;
        while i > 0 && matches!(bytes[i - 1], b']' | b')') {
            let (open, close) = if bytes[i - 1] == b']' {
                (b'[', b']')
            } else {
                (b'(', b')')
            };
            let mut depth = 0;
            let mut j = i;
            while j > 0 {
                j -= 1;
                if bytes[j] == close {
                    depth += 1;
                } else if bytes[j] == open {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
            }
            if depth != 0 {
                return (Vec::new(), i);
            }
            if open == b'[' {
                segs.push(Seg::Index);
            } else {
                called = true;
            }
            i = j;
        }
        let end = i;
        while i > 0 && (bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_') {
            i -= 1;
        }
        if i == end {
            break;
        }
        segs.push(Seg::Name(text[i..end].to_string(), called));
        if i > 0 && bytes[i - 1] == b'.' {
            i -= 1;
        } else {
            break;
        }
    }
    segs.reverse();
    (segs, i)
}

impl Index {
    fn text_of(&self, file: usize, span: Span) -> Option<&str> {
        let text = &self.files.get(file)?.text;
        line_slice(text, span)
    }

    /// Whether a use still reads the same in `text`, which may have changed since.
    pub fn live(&self, text: &str, r: &Ref) -> bool {
        r.at.file != 0
            || text == self.files[0].text
            || line_slice(text, r.at).is_some_and(|now| Some(now) == self.text_of(0, r.at))
    }

    /// The use or declaration at a position of `file`, whose text is now `text`.
    pub fn at(&self, file: usize, text: &str, line: u32, col: u32) -> Option<&Ref> {
        self.refs.iter().find(|r| {
            r.at.file == file
                && r.at.line == line
                && (r.at.col..=r.at.col + r.at.len).contains(&col)
                && self.live(text, r)
        })
    }

    pub fn references(&self, def: usize) -> impl Iterator<Item = &Ref> {
        self.refs.iter().filter(move |r| r.def == def)
    }

    pub fn hover<'a>(&'a self, r: &'a Ref) -> &'a str {
        r.hover.as_deref().unwrap_or(&self.defs[r.def].hover)
    }

    fn children(&self, def: usize) -> impl Iterator<Item = usize> + '_ {
        (0..self.defs.len()).filter(move |&d| self.defs[d].parent == Some(def))
    }

    fn members(&self, ty: usize) -> Vec<usize> {
        let Some(t) = self.tys.get(ty) else {
            return Vec::new();
        };
        match self.shapes.get(&t.under) {
            Some(&shape) => self.children(shape).collect(),
            None => Vec::new(),
        }
    }

    /// The function around a line of the indexed file: the last one declared before it.
    fn enclosing(&self, line: u32) -> Option<usize> {
        self.defs
            .iter()
            .enumerate()
            .filter(|(_, d)| matches!(d.kind, Kind::Function | Kind::External))
            .filter_map(|(i, d)| Some((i, d.at?)))
            .filter(|(_, at)| at.file == 0 && at.line <= line)
            .max_by_key(|(_, at)| at.line)
            .map(|(i, _)| i)
    }

    // simplify: a local is visible from its declaration to the end of its function, not
    // just its block. Needs block extents in the index.
    fn locals(&self, line: u32) -> Vec<usize> {
        let Some(func) = self.enclosing(line) else {
            return Vec::new();
        };
        (0..self.defs.len())
            .filter(|&d| {
                let def = &self.defs[d];
                def.parent == Some(func)
                    && matches!(def.kind, Kind::Local | Kind::Param)
                    && def.at.is_some_and(|at| at.line <= line)
            })
            .collect()
    }

    fn named(&self, name: &str, kinds: &[Kind]) -> Option<usize> {
        self.defs
            .iter()
            .position(|d| d.name == name && kinds.contains(&d.kind))
    }

    /// The type of the value a path names, from the scope around a line of `text`.
    fn resolve(&self, segs: &[Seg], text: &str, line: u32) -> Option<usize> {
        let (first, rest) = segs.split_first()?;
        let mut ty = match first {
            Seg::Name(name, false) => {
                let local = self
                    .locals(line)
                    .into_iter()
                    .rev()
                    .find(|&d| &self.defs[d].name == name);
                local
                    .or_else(|| self.named(name, &[Kind::Storage]))
                    .and_then(|d| self.defs[d].ty)
                    .or_else(|| self.declared(text, line, name))?
            }
            Seg::Name(name, true) => self
                .named(name, &[Kind::Function, Kind::External])
                .and_then(|d| self.defs[d].ty)?,
            Seg::Index => return None,
        };
        for seg in rest {
            ty = match seg {
                Seg::Index => self.tys.get(ty)?.item?,
                Seg::Name(name, _) => {
                    let d = self
                        .members(ty)
                        .into_iter()
                        .find(|&d| &self.defs[d].name == name)?;
                    self.defs[d].ty?
                }
            };
        }
        Some(ty)
    }

    /// The type of `name : T` written last before a line, for names the index has not seen.
    fn declared(&self, text: &str, line: u32, name: &str) -> Option<usize> {
        let before: Vec<&str> = text.lines().take(line as usize).collect();
        let before = before.join("\n");
        let mut from = before.len();
        while let Some(at) = before[..from].rfind(name) {
            from = at;
            if !is_word(&before, at, name.len()) {
                continue;
            }
            let rest = before[at + name.len()..].trim_start();
            let Some(rest) = rest.strip_prefix(':').filter(|r| !r.starts_with('=')) else {
                continue;
            };
            let ty: String = rest
                .trim_start()
                .chars()
                .take_while(|&c| is_ident(c) || c == '.')
                .collect();
            return self
                .named(&ty, &[Kind::Type, Kind::Interface, Kind::Storage])
                .and_then(|d| self.defs[d].ty);
        }
        None
    }

    fn item(&self, d: usize) -> Completion {
        let def = &self.defs[d];
        Completion {
            label: def.name.clone(),
            kind: def.kind,
            detail: def.detail.clone(),
            doc: def.hover.clone(),
            snippet: None,
        }
    }

    /// What may be typed at a position of `text`, the indexed file as it is now.
    pub fn completions(&self, text: &str, line: u32, col: u32) -> Vec<Completion> {
        let src = text
            .lines()
            .nth(line.saturating_sub(1) as usize)
            .unwrap_or("");
        let mut end = (col.saturating_sub(1) as usize).min(src.len());
        while !src.is_char_boundary(end) {
            end -= 1;
        }
        let upto = &src[..end];
        let before = upto.trim_end_matches(is_ident);
        if let Some(path) = before.strip_suffix('.') {
            return self.after_dot(text, path, line);
        }
        let trimmed = before.trim_end();
        let last = trimmed.rsplit(|c: char| !is_ident(c)).next().unwrap_or("");
        if last == "emit" {
            return self.emits();
        }
        if let Some(i) = trimmed.rfind("raises") {
            let after = &trimmed[i + "raises".len()..];
            if is_word(trimmed, i, "raises".len())
                && after.chars().all(|c| is_ident(c) || c == ',' || c == ' ')
            {
                return self.by_kind(&[Kind::Error, Kind::ErrorSet]);
            }
        }
        if trimmed.ends_with(':') && !trimmed.ends_with("::") {
            let mut out = self.by_kind(&[Kind::Type, Kind::Interface]);
            out.extend(TYPE_NAMES.iter().map(|&t| keyword(t, Kind::Type)));
            return out;
        }
        let mut out = Vec::new();
        if matches!(trimmed, "" | "|") {
            out.extend(self.case_arms(text, line, trimmed.is_empty()));
        }
        out.extend(self.scope(line));
        out
    }

    /// The canonical name a name of the indexed file stands for.
    fn canonical<'a>(&'a self, spelled: &'a str) -> &'a str {
        self.spelled.get(spelled).map_or(spelled, String::as_str)
    }

    fn after_dot(&self, text: &str, path: &str, line: u32) -> Vec<Completion> {
        let (segs, _) = chain(path);
        let head = match segs.as_slice() {
            [Seg::Name(head, false)] => Some(head.clone()),
            [Seg::Name(alias, false), Seg::Name(m, false)] => Some(format!("{alias}.{m}")),
            _ => None,
        };
        if let Some(head) = head {
            if let Some(m) = self.named(self.canonical(&head), &[Kind::Module]) {
                return self
                    .children(m)
                    .filter(|&d| {
                        matches!(
                            self.defs[d].kind,
                            Kind::Function | Kind::External | Kind::Builtin
                        )
                    })
                    .map(|d| self.item(d))
                    .collect();
            }
            if let Some(i) = self.named(self.canonical(&head), &[Kind::Interface]) {
                return self.children(i).map(|d| self.item(d)).collect();
            }
            // An alias: what its file declares, and its modules.
            let prefix = format!("{head}.");
            let mut aliased: Vec<Completion> = self
                .spelled
                .iter()
                .filter_map(|(spelled, canonical)| {
                    let label = spelled.strip_prefix(&prefix)?;
                    let d = self.defs.iter().position(|d| {
                        d.parent.is_none() && (d.name == *canonical || d.name == short(canonical))
                    });
                    let mut item = match d {
                        Some(d) => self.item(d),
                        None => keyword(label, Kind::Module),
                    };
                    item.label = label.to_string();
                    Some(item)
                })
                .collect();
            if !aliased.is_empty() {
                aliased.sort_by(|a, b| a.label.cmp(&b.label));
                return aliased;
            }
        }
        let Some(ty) = self.resolve(&segs, text, line) else {
            return Vec::new();
        };
        self.members(ty).into_iter().map(|d| self.item(d)).collect()
    }

    fn by_kind(&self, kinds: &[Kind]) -> Vec<Completion> {
        let mut seen = HashSet::new();
        (0..self.defs.len())
            .filter(|&d| kinds.contains(&self.defs[d].kind) && seen.insert(&self.defs[d].name))
            .map(|d| self.item(d))
            .collect()
    }

    fn emits(&self) -> Vec<Completion> {
        (0..self.defs.len())
            .filter(|&d| self.defs[d].kind == Kind::Event)
            .map(|d| {
                let fields: Vec<String> = self
                    .children(d)
                    .enumerate()
                    .map(|(i, f)| format!("{} = ${};", self.defs[f].name, i + 1))
                    .collect();
                let mut item = self.item(d);
                item.snippet = Some(format!("{} {{ {} }};", item.label, fields.join(" ")));
                item
            })
            .collect()
    }

    /// Every arm of a `case` on the line before, or the variants for one more arm.
    fn case_arms(&self, text: &str, line: u32, scaffold: bool) -> Vec<Completion> {
        let lines: Vec<&str> = text.lines().collect();
        let prev = (0..line.saturating_sub(1) as usize)
            .rev()
            .map(|i| lines.get(i).copied().unwrap_or("").trim())
            .find(|l| !l.is_empty() && *l != "{")
            .unwrap_or("");
        let head = prev.trim_end_matches('{').trim_end();
        let Some(scrut) = head
            .strip_suffix(" of")
            .and_then(|h| h.rsplit_once("case "))
            .map(|(_, s)| s.trim())
        else {
            return Vec::new();
        };
        let (segs, _) = chain(scrut);
        let Some(ty) = self.resolve(&segs, text, line) else {
            return Vec::new();
        };
        let variants: Vec<usize> = self
            .members(ty)
            .into_iter()
            .filter(|&d| self.defs[d].kind == Kind::Variant)
            .collect();
        if variants.is_empty() {
            return Vec::new();
        }
        let mut out = Vec::new();
        if scaffold {
            let mut n = 0;
            let arms: Vec<String> = variants
                .iter()
                .map(|&v| {
                    let def = &self.defs[v];
                    n += 1;
                    if def.params.is_empty() {
                        format!("| {} -> ${{{n}:skip}}", def.name)
                    } else {
                        let bind = def.name.to_lowercase();
                        n += 1;
                        format!("| {}(${{{}:{bind}}}) -> ${{{n}:skip}}", def.name, n - 1)
                    }
                })
                .collect();
            out.push(Completion {
                label: format!("case {scrut} of (every arm)"),
                kind: Kind::Keyword,
                detail: format!("{} arms", variants.len()),
                doc: String::new(),
                snippet: Some(arms.join("\n")),
            });
        }
        out.extend(variants.into_iter().map(|v| self.item(v)));
        out
    }

    fn scope(&self, line: u32) -> Vec<Completion> {
        let mut seen = HashSet::new();
        let mut out = Vec::new();
        for d in self.locals(line).into_iter().rev() {
            if seen.insert(self.defs[d].name.clone()) {
                out.push(self.item(d));
            }
        }
        let module = self.enclosing(line).and_then(|f| self.defs[f].parent);
        // What another file declares is in scope only through this file's imports.
        let imported = |def: &Def| {
            def.at.is_some_and(|at| at.file == 0)
                || self
                    .spelled
                    .iter()
                    .any(|(k, v)| !k.contains('.') && (*v == def.name || short(v) == def.name))
        };
        for (d, def) in self.defs.iter().enumerate() {
            let visible = match def.kind {
                Kind::Function => def.parent == module || (def.parent.is_none() && imported(def)),
                Kind::Storage => def.parent.is_none() || def.parent == module,
                Kind::Type | Kind::Error | Kind::Interface | Kind::Module => {
                    def.parent.is_some() || imported(def)
                }
                Kind::Variant => true,
                _ => false,
            };
            if visible && seen.insert(def.name.clone()) {
                out.push(self.item(d));
            }
        }
        // An alias, which names what its file declares.
        for spelled in self.spelled.keys() {
            if let Some((alias, _)) = spelled.split_once('.') {
                if seen.insert(alias.to_string()) {
                    out.push(keyword(alias, Kind::Module));
                }
            }
        }
        for kw in KEYWORDS {
            if seen.insert(kw.to_string()) {
                out.push(keyword(kw, Kind::Keyword));
            }
        }
        out
    }

    /// The call whose arguments a position of `text` is in, and which argument.
    pub fn signature(&self, text: &str, line: u32, col: u32) -> Option<Signature> {
        let starts: Vec<usize> = std::iter::once(0)
            .chain(text.match_indices('\n').map(|(i, _)| i + 1))
            .collect();
        let mut at = starts.get(line.saturating_sub(1) as usize)? + col.saturating_sub(1) as usize;
        at = at.min(text.len());
        while !text.is_char_boundary(at) {
            at -= 1;
        }
        let bytes = text.as_bytes();
        let floor = at.saturating_sub(4000);
        let mut depth = 0;
        let mut active = 0;
        let mut i = at;
        let open = loop {
            if i <= floor {
                return None;
            }
            i -= 1;
            match bytes[i] {
                b')' | b']' => depth += 1,
                b'(' | b'[' if depth > 0 => depth -= 1,
                b'(' => break i,
                b',' if depth == 0 => active += 1,
                b';' | b'{' | b'}' if depth == 0 => return None,
                _ => {}
            }
        };
        let line_of = starts.partition_point(|&s| s <= open) as u32;
        let (segs, _) = chain(text[..open].trim_end());
        let def = match segs.as_slice() {
            [Seg::Name(name, _)] => {
                self.named(name, &[Kind::Function, Kind::External, Kind::Variant])
            }
            [Seg::Name(m, false), Seg::Name(name, _)]
                if self.named(self.canonical(m), &[Kind::Module]).is_some() =>
            {
                let m = self.named(self.canonical(m), &[Kind::Module])?;
                self.children(m).find(|&d| &self.defs[d].name == name)
            }
            [Seg::Name(alias, false), Seg::Name(m, false), Seg::Name(name, _)] => {
                let m = self.named(self.canonical(&format!("{alias}.{m}")), &[Kind::Module])?;
                self.children(m).find(|&d| &self.defs[d].name == name)
            }
            [rest @ .., Seg::Name(name, _)] => {
                let ty = self.resolve(rest, text, line_of)?;
                self.members(ty)
                    .into_iter()
                    .find(|&d| &self.defs[d].name == name)
            }
            _ => None,
        }?;
        let d = &self.defs[def];
        Some(Signature {
            label: d.detail.clone(),
            params: d.params.clone(),
            active,
            doc: d.hover.clone(),
        })
    }
}

fn keyword(name: &str, kind: Kind) -> Completion {
    Completion {
        label: name.to_string(),
        kind,
        detail: String::new(),
        doc: String::new(),
        snippet: None,
    }
}

fn line_slice(text: &str, span: Span) -> Option<&str> {
    let line = text.lines().nth(span.line.checked_sub(1)? as usize)?;
    let start = span.col.checked_sub(1)? as usize;
    line.get(start..start + span.len as usize)
}
