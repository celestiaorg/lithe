use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use crate::word::Word;

/// An interned identifier: an index into a [`Names`] table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Symbol(u32);

/// The table every `Symbol` a program holds indexes, one per process.
///
/// `std/` and imported files come from process-wide parse caches, so a `Symbol` from a cached
/// parse must name the same text in every later build, and merging files must never remap. One
/// table also makes a symbol depend on its text alone, never on the order `emit_dir`'s parallel
/// builds parse files in.
///
/// simplify: the table never shrinks, so a long language-server session keeps every identifier
/// it has seen. Dropping entries on a content-hash miss is the upgrade if that ever matters.
#[derive(Debug, Default)]
pub(crate) struct Names {
    inner: Mutex<Inner>,
}

#[derive(Debug, Default)]
struct Inner {
    ids: HashMap<Box<str>, Symbol>,
    text: Vec<Arc<str>>,
}

impl Names {
    pub fn new() -> Self {
        Self::default()
    }

    /// The table every build interns into.
    pub fn shared() -> Arc<Names> {
        static SHARED: std::sync::OnceLock<Arc<Names>> = std::sync::OnceLock::new();
        SHARED.get_or_init(|| Arc::new(Names::new())).clone()
    }

    /// The symbol for `text`, interned once per process.
    pub fn intern(&self, text: &str) -> Symbol {
        let mut inner = self.inner.lock().unwrap_or_else(|err| err.into_inner());
        if let Some(sym) = inner.ids.get(text) {
            return *sym;
        }
        let sym = Symbol(inner.text.len() as u32);
        let arc: Arc<str> = Arc::from(text);
        inner.ids.insert(arc.as_ref().into(), sym);
        inner.text.push(arc);
        sym
    }

    /// How many distinct texts the table holds. Test-only: nothing reads it back yet.
    #[cfg(test)]
    pub fn len(&self) -> usize {
        let inner = self.inner.lock().unwrap_or_else(|err| err.into_inner());
        inner.text.len()
    }

    /// The text of `sym`.
    #[allow(dead_code)] // diagnostics read names back once 5.1b holds symbols in the AST
    pub fn get(&self, sym: Symbol) -> Arc<str> {
        let inner = self.inner.lock().unwrap_or_else(|err| err.into_inner());
        inner.text[sym.0 as usize].clone()
    }
}

/// Where a node is in its file: the bytes of the token it starts at.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub(crate) struct Span {
    pub lo: u32,
    pub hi: u32,
}

impl Span {
    /// No place in any file: a node the compiler wrote, which reads as line 0.
    pub const NONE: Span = Span {
        lo: u32::MAX,
        hi: u32::MAX,
    };
}

/// A file of one compilation, as its [`SourceMap`] numbers it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub(crate) struct FileId(pub u32);

impl FileId {
    /// No file: a declaration the compiler wrote. Its path is empty.
    pub const NONE: FileId = FileId(u32::MAX);
}

/// The files one compilation reads: each one's path, and where each of its lines starts.
#[derive(Debug, Default, Clone)]
pub(crate) struct SourceMap {
    files: Vec<SourceFile>,
}

#[derive(Clone)]
struct SourceFile {
    path: String,
    hash: u64,
    starts: Vec<u32>,
}

/// A file's path and content hash say which file it is; `Debug` keys leave the lines out.
impl std::fmt::Debug for SourceFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}#{:016x}", self.path, self.hash)
    }
}

impl SourceMap {
    /// A map of the one file `src`, as `FileId::default()`.
    pub fn of(path: &str, src: &str) -> Self {
        let mut map = SourceMap::default();
        map.add(path, src);
        map
    }

    /// The id of `src` at `path`, added once per path and content.
    pub fn add(&mut self, path: &str, src: &str) -> FileId {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        src.hash(&mut hasher);
        let hash = hasher.finish();
        if let Some(i) = self
            .files
            .iter()
            .position(|f| f.hash == hash && f.path == path)
        {
            return FileId(i as u32);
        }
        self.files.push(SourceFile {
            path: path.to_string(),
            hash,
            starts: crate::parse::line_starts(src),
        });
        FileId(self.files.len() as u32 - 1)
    }

    /// The file's path as the compiler read it; empty for text with no file.
    pub fn path(&self, file: FileId) -> &str {
        self.files.get(file.0 as usize).map_or("", |f| &f.path)
    }

    /// The file at `path`, the first one added there.
    pub fn find(&self, path: &str) -> Option<FileId> {
        let i = self.files.iter().position(|f| f.path == path)?;
        Some(FileId(i as u32))
    }

    /// The 1-based line and byte column `span` starts at; `(0, 0)` for [`Span::NONE`].
    pub fn line_col(&self, file: FileId, span: Span) -> (u32, u32) {
        let Some(f) = self.files.get(file.0 as usize) else {
            return (0, 0);
        };
        if span == Span::NONE {
            return (0, 0);
        }
        let line = f.starts.partition_point(|&s| s <= span.lo);
        let start = f.starts[line.max(1) - 1];
        (line as u32, span.lo - start + 1)
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Program {
    pub uses: Vec<UseDecl>,
    pub types: Vec<TypeDecl>,
    pub errors: Vec<ErrorDecl>,
    pub error_sets: Vec<ErrorSetDecl>,
    pub events: Vec<EventDecl>,
    pub interfaces: Vec<InterfaceDecl>,
    pub funcs: Vec<Func>,
    pub domains: Vec<DomainDecl>,
    pub modules: Vec<ModuleDecl>,
    pub compose: Vec<NameAt>,
    /// The modules in `compose` only because a module the contract uses requires them,
    /// directly or through others. The contract's own code can't call into them.
    pub implied: Vec<String>,
    /// The modules the contract's own code names, by canonical name.
    pub refs: Vec<String>,
    /// `use M delegated;` or `use M delegated exposing ...;`: the modules whose code runs from their
    /// facets, never in the contract.
    pub facets: Vec<NameAt>,
    /// `use M exposing { ... }`: the module externals the contract exposes.
    pub exposes: Vec<Exposing>,
    /// `supports I, J`: the interfaces the contract announces through ERC-165.
    pub supports: Vec<NameAt>,
    pub upgradeable: bool,
    /// `storage at "id" is ...`: the ERC-7201 id the default storage record is rooted at.
    /// Empty roots it at slot 0.
    pub storage_id: String,
    pub guard: Option<GuardDecl>,
    /// `use M ... with { guard editor(...) is { ... } }`: the contract's checks for its modules'
    /// guards.
    pub guards: Vec<Func>,
    /// `hook h(...) is { ... }`, `hook h is f;`, and `hook h is skip;` in `use M ... with`: the
    /// contract's implementations of its modules' hooks.
    pub hooks: Vec<Func>,
    /// A facet's program: its modules' hooks call back into the contract that runs it.
    pub calls_back: bool,
    /// Set when the file names its contract. An implicit file leaves this empty;
    /// tooling may still label artifacts from the file name.
    pub contract_name: Option<String>,
    pub contract_span: Span,
    /// Further contracts from the same file. One bytecode uses a single contract.
    pub siblings: Vec<Program>,
    /// The other contracts of the file, which this one may `defer create`.
    pub peers: Vec<Program>,
    /// The file the contract is written in, as its declarations' `file` names it.
    pub file: FileId,
    /// The contract's spec blocks, and those of the files it imports. The checker drops
    /// them: only `spec::check` reads them.
    pub specs: Vec<SpecBlock>,
    /// Checked for the spec tools, which read loop invariants. A build drops them.
    pub proving: bool,
    /// What each file of the program sees, and the canonical name of each declaration.
    pub scopes: std::sync::Arc<crate::resolve::Scopes>,
    /// The table every `Symbol` this program holds indexes.
    pub names: Arc<Names>,
    /// The files every `FileId` this program holds names, and their lines.
    pub files: Arc<SourceMap>,
}

impl Program {
    /// Points the program, its sibling contracts, and its peers at `files`.
    pub(crate) fn share_files(&mut self, files: &Arc<SourceMap>) {
        self.files = files.clone();
        for prog in self.siblings.iter_mut().chain(&mut self.peers) {
            prog.share_files(files);
        }
    }
}

/// `spec is { ... }` or `spec for f is { ... }`: claims about the program that `lithe prove`
/// checks. Nothing in a spec block runs on chain.
#[derive(Debug, Clone)]
pub(crate) struct SpecBlock {
    pub span: Span,
    pub file: FileId,
    /// The function or route the block describes. `None` for `spec is`, the invariants.
    pub target: Option<NameAt>,
    /// `spec for f is partial`: the listed `raises` and `panics` conditions need not be the
    /// only ways `f` reverts.
    pub partial: bool,
    pub clauses: Vec<Clause>,
    /// Set when the block describes a module, from inside it or from `spec for module M`.
    pub module: Option<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct Clause {
    pub span: Span,
    pub kind: ClauseKind,
    pub expr: Expr,
    /// The expression as written, on one line: what the spec tools say the clause claims.
    pub text: String,
}

#[derive(Debug, Clone)]
pub(crate) enum ClauseKind {
    /// `invariant name is e;`, in `spec is`.
    Invariant(String),
    /// `const x : T := e;`, a name for a value the later clauses use.
    Const { name: String, ty: TypeRef },
    /// `raises E when e;`
    Raises(NameAt),
    /// `panics when e;`
    Panics,
    /// `ensures e;`
    Ensures,
}

/// Which state a spec reads: `old.` before the call, `new.` after it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum State {
    Old,
    New,
}

#[derive(Debug, Clone)]
pub(crate) struct DomainDecl {
    pub span: Span,
    pub file: FileId,
    pub name: String,
    pub id: String,
    pub ty: TypeRef,
    /// `Some` when this domain is declared inside a module.
    pub owner: Option<String>,
    /// `transient storage`: kept for the transaction only, in `TLOAD`/`TSTORE` slots.
    pub transient: bool,
    /// `immutable`: written only while the contract is set up, then read as a constant.
    pub immutable: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct TypeParam {
    pub span: Span,
    pub name: String,
    /// Compiler-known constraint, currently `MapKey`.
    pub constraint: Option<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct ModuleDecl {
    pub span: Span,
    pub file: FileId,
    pub name: String,
    pub params: Vec<TypeParam>,
    pub requires: Vec<NameAt>,
    pub domains: Vec<DomainDecl>,
    pub types: Vec<TypeDecl>,
    pub errors: Vec<ErrorDecl>,
    pub error_sets: Vec<ErrorSetDecl>,
    pub events: Vec<EventDecl>,
    pub funcs: Vec<Func>,
    /// The spec blocks written inside the module.
    pub specs: Vec<SpecBlock>,
    /// `guard editor(const id : uint);`: checks the module's externals name with `guarded`,
    /// which each contract that exposes them writes. Only a header: no body.
    pub guards: Vec<Func>,
    /// `[view | pure] hook name(params) [: T];`: calls the module's code makes into the
    /// contract that uses it, which that contract implements. Only a header: no body.
    pub hooks: Vec<Func>,
    /// The members the compiler implements, in a module of the standard library.
    pub intrinsics: Vec<Intrinsic>,
    /// The other modules its code names, by canonical name: those it calls, reads, or names
    /// a type, error, or event of.
    pub refs: Vec<String>,
}

/// `intrinsic view function sender() : address;` or `intrinsic call;`: a member of a
/// standard library module that the compiler implements. The checker's rules for it are
/// its own; the signature, when Lithe can write one, states them.
#[derive(Debug, Clone)]
pub(crate) struct Intrinsic {
    pub span: Span,
    pub name: String,
    pub sig: Option<Func>,
    /// What the compiler does for it, set when its file is loaded.
    pub tag: Option<Tag>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Tag {
    Call(Builtin),
    /// `Uint.max`, `Int.min`, `Int.max`, and `Address.zero`: literals as wide as the
    /// context expects.
    UintMax,
    IntMin,
    IntMax,
    AddressZero,
    /// `Evm.osaka`: whether the target fork has Osaka's opcodes, a `bool` constant.
    EvmOsaka,
    /// `Abi.selector(I.method)` and `Abi.interfaceId(I)`: `bytes4` constants.
    AbiSelector,
    AbiInterfaceId,
}

/// `use M exposing I, J, { ... }`: the contract uses `M` and exposes the members of the
/// interfaces it names and of its inline one. Each member is one of `M`'s externals.
#[derive(Debug, Clone)]
pub(crate) struct Exposing {
    pub span: Span,
    pub module: String,
    pub interfaces: Vec<NameAt>,
    /// The inline interface's members.
    pub decls: Vec<Func>,
}

/// What a module's external function was declared as, before it became the internal
/// function that the contracts exposing it call.
#[derive(Debug, Clone)]
pub(crate) struct Exported {
    /// Its name in the ABI.
    pub name: String,
    pub kind: ItemKind,
    pub payable: bool,
    pub nonreentrant: bool,
    pub external_pure: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct GuardDecl {
    pub span: Span,
    pub stmts: Vec<Stmt>,
    /// `upgrade guard is f;`: the function its body calls.
    pub via: Option<NameAt>,
}

#[derive(Debug, Clone)]
pub(crate) struct UseDecl {
    pub span: Span,
    pub path: String,
    pub alias: Option<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct TypeDecl {
    pub span: Span,
    pub private: bool,
    pub file: FileId,
    pub name: String,
    pub ty: TypeRef,
}

#[derive(Debug, Clone)]
pub(crate) struct ErrorDecl {
    pub span: Span,
    pub private: bool,
    pub file: FileId,
    pub name: String,
    pub payload: Option<TypeRef>,
}

#[derive(Debug, Clone)]
pub(crate) struct ErrorSetDecl {
    pub span: Span,
    pub file: FileId,
    pub name: String,
    pub members: Vec<NameAt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NameAt {
    pub span: Span,
    pub name: String,
}

#[derive(Debug, Clone)]
pub(crate) struct EventDecl {
    pub span: Span,
    pub private: bool,
    pub anonymous: bool,
    pub file: FileId,
    pub name: String,
    pub fields: Vec<FieldRef>,
}

#[derive(Debug, Clone)]
pub(crate) struct InterfaceDecl {
    pub span: Span,
    pub file: FileId,
    pub name: String,
    /// Each method's header, with no body: `view function f(a : T) : R raises E;`.
    pub methods: Vec<Func>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ItemKind {
    /// `function`: internal and stateful.
    Function,
    /// `view function`: internal and read-only.
    Readonly,
    /// `pure function`: internal. The result depends only on explicit inputs.
    Pure,
    /// `external function`: a state transition.
    Entry,
    /// `external view function`, or `external pure function` with `external_pure`.
    View,
    Migrate,
    /// `deploy`: runs once, when the contract is created or, if upgradeable, its proxy is.
    Deploy,
    /// `payable receive`: a transition for calls with no calldata, such as plain ether.
    Receive,
    /// `fallback`: a transition for calldata that matches no entrypoint, or, with
    /// `delegates to` or `forwards to`, a call passed on whole to another contract.
    Fallback,
}

/// How a `fallback` passes its call on: `delegates to` runs the target's code as this
/// contract, with `DELEGATECALL`; `forwards to` calls the target, with `CALL`. The target
/// is the function's tail, and the call's result or revert comes back as it is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Forward {
    Delegate,
    Call,
}

#[derive(Debug, Clone)]
pub(crate) enum TypeRef {
    Name {
        span: Span,
        name: String,
    },
    Record {
        span: Span,
        fields: Vec<FieldRef>,
    },
    Variant {
        span: Span,
        variants: Vec<VariantRef>,
    },
    List {
        span: Span,
        elem: Box<TypeRef>,
        /// `None` is a dynamic list. `Some(n)` is a fixed list of length `n`.
        len: Option<u32>,
        /// A fixed length written as a constant expression, `list(T, maxOwners())`, which
        /// the checker evaluates. `len` is then `None`.
        size: Option<Box<Expr>>,
    },
    Option {
        span: Span,
        elem: Box<TypeRef>,
    },
    Map {
        span: Span,
        key: Box<TypeRef>,
        val: Box<TypeRef>,
    },
    Tuple {
        span: Span,
        elems: Vec<TypeRef>,
    },
    /// `Set(address)` or `SetEnumerable(address).iterator`.
    Apply {
        span: Span,
        name: String,
        args: Vec<TypeRef>,
        member: Option<String>,
    },
    /// A type parameter already bound to a concrete type.
    Hole {
        id: usize,
    },
}

impl TypeRef {
    pub(crate) fn span(&self) -> Span {
        match self {
            Self::Name { span, .. }
            | Self::Record { span, .. }
            | Self::Variant { span, .. }
            | Self::List { span, .. }
            | Self::Option { span, .. }
            | Self::Map { span, .. }
            | Self::Tuple { span, .. }
            | Self::Apply { span, .. } => *span,
            Self::Hole { .. } => Span::NONE,
        }
    }
}

/// A list length as written, `M.n()` or `n() * 2`, with each name as declared.
pub(crate) fn size_text(e: &Expr) -> String {
    let short = |name: &str| name.rsplit("::").next().unwrap_or(name).to_string();
    match e {
        Expr::Lit {
            lit: Lit::Uint(w) | Lit::Int(w, _),
            ..
        } => w.0[0].to_string(),
        Expr::Ident { name, .. } => short(name),
        Expr::Call {
            name, args, base, ..
        } => {
            let args: Vec<String> = args.iter().map(size_text).collect();
            let base = base
                .as_deref()
                .map(|b| format!("{}.", size_text(b)))
                .unwrap_or_default();
            format!("{base}{}({})", short(name), args.join(", "))
        }
        Expr::Binary {
            op, left, right, ..
        } => format!(
            "({} {} {})",
            size_text(left),
            op_text(*op),
            size_text(right)
        ),
        _ => "_".to_string(),
    }
}

pub(crate) fn op_text(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::Pow => "**",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        _ => "?",
    }
}

/// Calls `f` on each expression directly inside `e`.
pub(crate) fn each_child(e: &mut Expr, f: &mut dyn FnMut(&mut Expr)) {
    match e {
        Expr::Lit { .. } | Expr::Ident { .. } => {}
        Expr::Field { base, .. }
        | Expr::Unary { expr: base, .. }
        | Expr::Convert { expr: base, .. } => f(base),
        Expr::Index { base, index, .. } => {
            f(base);
            f(index);
        }
        Expr::Query { expr, gas, .. } => {
            f(expr);
            if let Some(gas) = gas {
                f(gas);
            }
        }
        Expr::Call { args, base, .. } => {
            for arg in args {
                f(arg);
            }
            if let Some(base) = base {
                f(base);
            }
        }
        Expr::Case { scrut, arms, .. } => {
            f(scrut);
            for arm in arms {
                f(&mut arm.expr);
            }
        }
        Expr::Binary { left, right, .. } => {
            f(left);
            f(right);
        }
        Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
            for elem in elems {
                f(elem);
            }
        }
        Expr::Record { fields, .. } => {
            for (_, value) in fields {
                f(value);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct FieldRef {
    pub span: Span,
    pub name: String,
    pub ty: TypeRef,
    /// Set on an event field. Other records leave this false.
    pub indexed: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct VariantRef {
    pub span: Span,
    pub name: String,
    pub payload: Option<TypeRef>,
    /// The ABI parameter name of a single-value payload, from `of (name : ty)`.
    pub param: String,
    /// `| Case external name`: the name of the entrypoint a dispatched case becomes.
    pub external: Option<String>,
    /// `of flat R`: a dispatched case takes the record's fields as its ABI parameters.
    pub flat: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct Func {
    pub span: Span,
    pub kind: ItemKind,
    pub private: bool,
    pub file: FileId,
    pub name: String,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub ret: Option<TypeRef>,
    /// `: flat R`: the record's fields are the ABI's outputs.
    pub ret_flat: bool,
    pub ret_ty: usize,
    pub payable: bool,
    pub nonreentrant: bool,
    /// An `external pure function`: dispatched like a view, checked as pure.
    pub external_pure: bool,
    pub raises: Option<Raises>,
    /// Effective error set: the declared set, or the inferred set when `raises` is omitted.
    pub errors: Vec<usize>,
    pub stmts: Vec<Stmt>,
    pub tail: Option<Expr>,
    /// `Some` when this function was declared inside a module.
    pub module: Option<String>,
    pub requires: Vec<String>,
    /// On an entrypoint that `use M exposing` declares: `M`, whose external it runs.
    pub promoted: Option<String>,
    /// On an entrypoint that `use M exposing` declares: the module function it runs.
    pub declares: Option<String>,
    /// On an entrypoint that `use M exposing` declares: the named interface it comes from.
    /// `None` for the inline interface.
    pub interface: Option<String>,
    /// On a module's external function: how it was declared. It is checked as an internal
    /// function, which the entrypoints that declare it call.
    pub exported: Option<Exported>,
    /// On a `fallback` that passes its call on: how. Its tail is the target.
    pub forward: Option<Forward>,
    /// On a module's external, `guarded editor(id)`, and on the entrypoints that expose it,
    /// with the guard's name qualified: the guard that runs first. An entrypoint's first
    /// statement then calls the contract's check.
    pub guarded: Option<Guarded>,
    /// On the contract's check for a module's guard: which guard it is.
    pub guard_of: Option<GuardOf>,
    /// On the function a module's code calls for one of its hooks, and on a contract's
    /// entrypoint a facet calls it back through: which hook it is.
    pub hook_of: Option<HookOf>,
    /// `const name : T := e;` outside a function: a pure function of no parameters that
    /// code names without `()`, and whose value is known when the contract compiles.
    pub constant: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct Guarded {
    pub span: Span,
    pub name: String,
    /// The external's parameters the guard takes, by name.
    pub args: Vec<NameAt>,
}

/// `guard editor(...) is { ... }` in `use M ... with`, or `guard editor is f;`, which checks
/// by calling `f`. `module` is where the binding names the guard.
#[derive(Debug, Clone)]
pub(crate) struct GuardOf {
    pub module: NameAt,
    pub name: String,
    pub via: Option<NameAt>,
}

/// `hook h ... is ...` in `use M ... with`: which of `M`'s hooks a function is, and what it
/// is. `module` is where the binding names the hook.
#[derive(Debug, Clone)]
pub(crate) struct HookOf {
    pub module: NameAt,
    pub name: String,
    pub form: HookForm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum HookForm {
    /// `is { ... }`: a body the contract writes.
    Body,
    /// `is f;`: calls `f`.
    Via(NameAt),
    /// `is skip;`: explicitly unimplemented.
    Skip,
    /// Not written. An error once code the contract runs reaches it.
    Missing,
    /// In a facet: a call back into the contract that runs the facet.
    Callback,
    /// The contract's hidden entrypoint a facet calls the hook back through.
    Entry,
}

#[derive(Debug, Clone)]
pub(crate) struct Raises {
    pub parts: Vec<NameAt>,
}

#[derive(Debug, Clone)]
pub(crate) struct Param {
    pub span: Span,
    pub mutable: bool,
    /// `storage name : T`: a reference to the storage the caller passes, which the
    /// function may write.
    pub storage: bool,
    pub name: String,
    /// `name : flat R`: the record's fields are separate ABI parameters.
    pub flat: bool,
    pub ty: TypeRef,
    pub ty_id: usize,
    pub sym: Option<usize>,
}

#[derive(Debug, Clone)]
pub(crate) enum Stmt {
    Const {
        span: Span,
        name: String,
        /// Element names when this binding is `const (a, b) : (T, U)`.
        parts: Vec<String>,
        ty: TypeRef,
        expr: Expr,
        sym: Option<usize>,
        part_syms: Vec<usize>,
    },
    Var {
        span: Span,
        name: String,
        /// Element names when this binding is `var (a, b) : (T, U)`.
        parts: Vec<String>,
        ty: TypeRef,
        expr: Expr,
        sym: Option<usize>,
        part_syms: Vec<usize>,
    },
    Assign {
        span: Span,
        path: Vec<String>,
        index: Option<Expr>,
        /// Keys after the first, for a map of maps: `m[a][b] := v`.
        keys: Vec<Expr>,
        /// Fields after the first key, each with how many keys come before it:
        /// `m[k].a[j].b := v` has `(1, a)` and `(2, b)`.
        fields: Vec<(usize, String)>,
        expr: Expr,
        /// `place op= expr`: the checker rewrites it to `place := place op expr`,
        /// evaluating the place's keys once.
        op: Option<BinOp>,
        root: Option<usize>,
        leaf: u32,
        /// The place as an expression, when it lies past a list or a map's list or
        /// record: `m[k].a[j] := v`. The checker fills it in.
        target: Option<Box<Expr>>,
        /// `List.push(xs, v)`, checked into `xs[xs.length] := v`: the one write that may
        /// land past the end, growing the list by one.
        push: bool,
    },
    If {
        span: Span,
        cond: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
    },
    Assert {
        span: Span,
        cond: Expr,
        reason: Raised,
    },
    Fail {
        reason: Raised,
    },
    Call {
        span: Span,
        expr: Expr,
    },
    Skip,
    Emit {
        span: Span,
        name: String,
        fields: Vec<(String, Expr)>,
    },
    Defer {
        span: Span,
        expr: Expr,
        value: Option<Expr>,
        /// `with gas = g`: the most gas the call may use, instead of all that is left.
        gas: Option<Expr>,
        /// What runs after the call returns: a later, separate transition phase.
        then: Option<Box<Then>>,
    },
    /// `for x : T in xs do { ... }` or `for i : T in lo .. hi do { ... }`. The number of
    /// iterations is fixed when the loop starts; `until` ends it early.
    For {
        span: Span,
        /// The index name of `(i, x)`, if the loop binds one. `_` binds nothing.
        index: Option<String>,
        /// The element or counter name. `_` binds nothing.
        name: String,
        /// The declared type of `name`, or of `(index, name)` as a tuple.
        ty: TypeRef,
        iter: ForIter,
        until: Option<Expr>,
        bound: Option<Expr>,
        body: Vec<Stmt>,
        /// The loop counter. The checker binds it, under the index name or a hidden one.
        counter: Option<usize>,
        /// The element binding of a list loop.
        elem: Option<usize>,
        /// A hidden local holding the number to count to: `hi`, or the list's length.
        limit: Option<usize>,
        /// `xs[counter]`, typed by the checker, for a list loop.
        elem_init: Option<Expr>,
        /// The list's length, typed by the checker, for a dynamic list loop.
        length: Option<Expr>,
        /// `bound` as a number, set by the checker.
        cap: Option<u64>,
        /// A hidden local holding the list when it is not a name, field, or element.
        list: Option<usize>,
        /// Every local the loop declares, counter and element included. A deferred call
        /// inside the loop snapshots those its continuation reads.
        declared: Vec<usize>,
        /// `invariant e`: what holds each time an iteration starts, and when the loop ends.
        /// Only the spec tools read them; a build drops them.
        invariants: Vec<Expr>,
    },
    /// `(a, b) := expr;` assigns each element of a tuple to a `var`.
    AssignTuple {
        span: Span,
        names: Vec<String>,
        expr: Expr,
        syms: Vec<usize>,
    },
}

#[derive(Debug, Clone)]
pub(crate) enum ForIter {
    /// `lo .. hi`, half-open.
    Range { lo: Expr, hi: Expr },
    /// The elements of a list, in order.
    List(Expr),
}

/// `then (result : T) { ... }` on a deferred call. The call separates two complete
/// transitions; this is the second, and it receives the call's result.
#[derive(Debug, Clone)]
pub(crate) struct Then {
    pub span: Span,
    /// One name, the names of a tuple pattern, or none when the result is not bound.
    pub names: Vec<String>,
    pub tuple: bool,
    pub ty: Option<TypeRef>,
    pub stmts: Vec<Stmt>,
    /// The checker's symbols for `names`, in order.
    pub syms: Vec<usize>,
    /// The call's declared return type, set by the checker.
    pub ret: usize,
    /// `| Error(reason : bytes) -> { ... }`: runs as its own phase when the call reverts,
    /// with the revert data. Without it, a failed call reverts the transaction.
    pub error: Option<Box<Then>>,
}

impl Then {
    /// The success continuation, then the failure one when the call is recoverable.
    pub(crate) fn arms(&self) -> impl Iterator<Item = &Then> {
        std::iter::once(self).chain(self.error.as_deref())
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Raised {
    pub span: Span,
    pub name: String,
    pub form: RaisedForm,
    pub index: Option<usize>,
    /// `forward name`: the raw `bytes` in `name` are the whole revert.
    pub forward: bool,
}

#[derive(Debug, Clone)]
pub(crate) enum RaisedForm {
    Unit,
    Positional(Expr),
    Fields(Vec<(String, Expr)>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Eq,
    Neq,
    Lt,
    Gt,
    Le,
    Ge,
    And,
    Or,
    Cons,
}

impl BinOp {
    pub(crate) fn is_cmp(self) -> bool {
        matches!(
            self,
            Self::Eq | Self::Neq | Self::Lt | Self::Gt | Self::Le | Self::Ge
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnOp {
    Not,
    Neg,
    BitNot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Builtin {
    /// A read of an immutable that is a value in memory while `deploy` runs, and after it is
    /// built from the code.
    ImmutableRead,
    Sender,
    Value,
    Calldata,
    Selector,
    TxOrigin,
    TxGasPrice,
    BlockNumber,
    BlockTimestamp,
    BlockCoinbase,
    BlockBaseFee,
    BlobBaseFee,
    ChainId,
    BlockPrevrandao,
    BlockGasLimit,
    BlockHash,
    BlobHash,
    SelfAddr,
    Balance,
    CodeSize,
    CodeHash,
    GasLeft,
    Keccak256,
    Sha256,
    Ripemd160,
    Ecrecover,
    AbiEncode,
    AbiDecode,
    AbiEncodePacked,
    AbiEncodeSelector,
    AbiEncodeSignature,
    AbiEncodeCall,
    BytesConcat,
    StringConcat,
    UintDivRem,
    /// `Bytes.word(b, offset)`: the 32 bytes of `b` starting at `offset`, as a `bytes32`.
    BytesWord,
    /// `b[i]` for `b : bytes` or `bytesN`: the byte at `i`, as a `bytes1`.
    BytesAt,
    /// `b[start:end]`: a copy of the bytes between. With two arguments, `b[start:]`.
    BytesSlice,
    /// `Base64.encode(data)`: RFC 4648 base64, padded, as a `string`.
    Base64Encode,
    /// `Base64.encodeUrl(data)`: the URL and filename safe alphabet, unpadded.
    Base64EncodeUrl,
    /// `Base64.encodeWith(data, fileSafe, noPadding)`.
    Base64EncodeWith,
    /// `Base64.decode(data)`: the bytes a base64 string encodes, in either alphabet.
    Base64Decode,
    /// `String.lower(s)`, or with `true`, `String.upper(s)`: ASCII letters recased.
    StringCase(bool),
    /// `String.escapeJson(s)`, or with `true`, `String.escapeHtml(s)`.
    StringEscape(bool),
    /// `String.indexOf(s, needle, from)`: where `needle` first starts, from `from` on.
    StringIndexOf,
    /// `String.replace(s, needle, replacement)`: every `needle` replaced, left to right.
    StringReplace,
    /// `Bytes.join(xs)`, or with `true`, `String.join(xs)`: a list's values one after another.
    Join(bool),
    /// `Uint.mulDiv(a, b, d)`: `a * b / d` without overflow in the product.
    UintMulDiv,
    UintMulMod,
    UintAddMod,
    /// `Uint.popCount(x)`: how many bits of `x` are set.
    UintPopCount,
    /// `Uint.clz(x)`: how many zero bits lead `x`'s highest set bit, 256 for zero.
    UintClz,
    IntDivRem,
    /// `Uint.toString(n)`: an unsigned integer in decimal, as a `string`.
    UintToString,
    /// `Int.toString(n)`: a signed integer in decimal, with a `-` when negative.
    IntToString,
    /// `Uint.toHexString(n)`: `0x` and the fewest whole bytes in lowercase hex. With a
    /// second argument, exactly that many bytes.
    UintToHexString,
    /// `Address.toHexString(a)`: `0x` and 40 lowercase hex digits. `true` is
    /// `Address.toChecksumString`, cased as EIP-55.
    AddressToHexString(bool),
    /// `Uint.fromBits(i)` and `Int.fromBits(n)`, the unchecked bit-cast between `int` and
    /// `uint`. `true` is `Int.fromBits`.
    FromBits(bool),
    /// `List.pop(xs)`: drops a dynamic list's last element. Checked into an assignment of
    /// the list, `xs := List.pop(xs)`, so it writes what an assignment writes.
    ListPop,
    /// `List.push(xs, v)`: appends to a dynamic list. Checked into an assignment at the
    /// list's length that grows it.
    ListPush,
    /// `List.resized(xs, n)`: a new list of `xs`'s first `n` elements, padded with zero
    /// values when `xs` is shorter.
    ListResized,
    /// `Abi.supportsInterface(id)`: whether `id` is ERC-165's or one the contract's
    /// `supports` lists, as the `supportsInterface` the compiler generates answers.
    AbiSupportsInterface,
    /// `Evm.creationCode(C)`: the creation code `create C(...)` runs, before its arguments.
    CreationCode,
    /// `Evm.facetAddress(M)`: the address of the facet of a module `M` the contract uses
    /// `delegated`.
    FacetAddress,
    /// `Uint.wrappingAdd(a, b)`, `Int.wrappingMul(a, b)`, and so on: the operation on two
    /// values of one integer type, wrapped to its width instead of checked. `true` is `Int`.
    Wrapping(BinOp, bool),
    Transfer,
    /// `Evm.call(to, data)`: a `CALL` with `data` as the whole calldata. Its continuation
    /// gets the raw return data.
    RawCall,
    /// `Evm.delegateCall(to, data)`: `to`'s code runs as this contract, on `data`.
    DelegateCall,
    /// `Evm.staticCall(to, data)`: a `STATICCALL` with `data` as the calldata, queried.
    StaticCall,
    /// `Evm.create(code)`: runs `code` as creation code. `base` holds the `CREATE2` salt,
    /// if any.
    RawCreate,
    /// `Evm.code(a)`: the code at `a`, as `bytes`.
    Code,
    /// A precompiled contract, given its input as it lays it out.
    Precompile(Pre),
    /// `create Contract(args)`: the arguments go to its `deploy`; `base` holds the
    /// `CREATE2` salt, if any.
    Create,
    Cast,
    Some,
    None,
    /// A variant constructor, by its index in the variant's cases.
    Ctor(usize),
    /// `Name { field = ...; }` as parsed: a constructor given a record payload, until the
    /// checker resolves the constructor.
    Braced,
    /// `old.e` or `new.e` in a spec: `e` read in the state before or after the call.
    SpecState(State),
    /// `sum(m)` in a spec: the sum of a map's values.
    SpecSum,
    /// `count(m)` in a spec: how many of a map's values are not zero.
    SpecCount,
    /// `forall x : T . e` in a spec. Its arguments are `x`, the name of `T`, and `e`.
    SpecForall,
}

/// The precompiled contracts past the hashes and `ecrecover`, each a built-in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Pre {
    /// `Crypto.modExp(base, exponent, modulus)`: 0x05 on byte strings.
    ModExp,
    /// `Uint.powMod(base, exponent, modulus)`: 0x05 on words.
    PowMod,
    /// `Crypto.bn254Add(a, b)`: 0x06.
    Bn254Add,
    /// `Crypto.bn254Mul(p, s)`: 0x07.
    Bn254Mul,
    /// `Crypto.bn254Pairing(pairs)`: 0x08.
    Bn254Pairing,
    /// `Crypto.blake2f(rounds, h, m, t, final)`: 0x09.
    Blake2f,
    /// `Crypto.kzgPointEvaluation(versionedHash, z, y, commitment, proof)`: 0x0a.
    PointEvaluation,
    /// `Crypto.bls12G1Add(a, b)`: 0x0b.
    Bls12G1Add,
    /// `Crypto.bls12G1Msm(pairs)`: 0x0c.
    Bls12G1Msm,
    /// `Crypto.bls12G2Add(a, b)`: 0x0d.
    Bls12G2Add,
    /// `Crypto.bls12G2Msm(pairs)`: 0x0e.
    Bls12G2Msm,
    /// `Crypto.bls12Pairing(pairs)`: 0x0f.
    Bls12Pairing,
    /// `Crypto.bls12MapFpToG1(fp)`: 0x10.
    Bls12MapFpToG1,
    /// `Crypto.bls12MapFp2ToG2(fp2)`: 0x11.
    Bls12MapFp2ToG2,
    /// `Crypto.p256Verify(hash, r, s, x, y)`: 0x100, EIP-7951.
    P256Verify,
}

impl Pre {
    pub(crate) fn address(self) -> u64 {
        match self {
            Pre::ModExp | Pre::PowMod => 0x05,
            Pre::Bn254Add => 0x06,
            Pre::Bn254Mul => 0x07,
            Pre::Bn254Pairing => 0x08,
            Pre::Blake2f => 0x09,
            Pre::PointEvaluation => 0x0a,
            Pre::Bls12G1Add => 0x0b,
            Pre::Bls12G1Msm => 0x0c,
            Pre::Bls12G2Add => 0x0d,
            Pre::Bls12G2Msm => 0x0e,
            Pre::Bls12Pairing => 0x0f,
            Pre::Bls12MapFpToG1 => 0x10,
            Pre::Bls12MapFp2ToG2 => 0x11,
            Pre::P256Verify => 0x100,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Hash)]
pub(crate) enum Lit {
    Uint(Word),
    /// Hex literals keep how many digits were written.
    Int(Word, Option<u8>),
    Wei(Word),
    Duration(Word),
    Bool(bool),
    Str(String),
    /// A hex literal longer than a word, which only `bytes` can hold.
    Bytes(Vec<u8>),
    Unit,
    Nil,
    /// What `delete place;` assigns: the place type's zero value, filled in by the checker.
    Zero,
}

#[derive(Debug, Clone)]
pub(crate) enum Expr {
    Lit {
        span: Span,
        lit: Lit,
        ty: usize,
    },
    Ident {
        span: Span,
        name: String,
        sym: Option<usize>,
        builtin: Option<Builtin>,
        ty: usize,
    },
    Field {
        span: Span,
        base: Box<Expr>,
        name: String,
        root: Option<usize>,
        leaf: u32,
        ty: usize,
    },
    Index {
        span: Span,
        base: Box<Expr>,
        index: Box<Expr>,
        root: Option<usize>,
        leaf: u32,
        ty: usize,
    },
    Call {
        span: Span,
        name: String,
        args: Vec<Expr>,
        base: Option<Box<Expr>>,
        callee: Option<usize>,
        builtin: Option<Builtin>,
        iface: Option<usize>,
        method: Option<usize>,
        ty: usize,
    },
    Query {
        span: Span,
        expr: Box<Expr>,
        /// `with gas = g`: the most gas the call may use, instead of all that is left.
        gas: Option<Box<Expr>>,
        ty: usize,
    },
    Case {
        span: Span,
        scrut: Box<Expr>,
        arms: Vec<Arm>,
        ty: usize,
    },
    Unary {
        span: Span,
        op: UnOp,
        expr: Box<Expr>,
        ty: usize,
    },
    /// `list(uint)(xs)`: a conversion to a type that has no name of its own. The checker
    /// makes it a `Cast`.
    Convert {
        span: Span,
        target: Box<TypeRef>,
        expr: Box<Expr>,
        ty: usize,
    },
    Binary {
        span: Span,
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
        ty: usize,
    },
    Tuple {
        span: Span,
        elems: Vec<Expr>,
        ty: usize,
    },
    List {
        span: Span,
        elems: Vec<Expr>,
        ty: usize,
    },
    Record {
        span: Span,
        fields: Vec<(String, Expr)>,
        ty: usize,
    },
}

impl Expr {
    /// Whether a `case` on `scrut` with `arms` is `case query ... of`, which branches on the
    /// call's outcome. `if c then a else b` parses as a `case` with arms `true` and `false`,
    /// so an `if` on a query branches on the answer instead.
    pub(crate) fn is_outcome_case(scrut: &Expr, arms: &[Arm]) -> bool {
        matches!(scrut, Expr::Query { .. })
            && arms
                .first()
                .and_then(|arm| arm.ctors.first())
                .is_none_or(|ctor| ctor != "true")
    }

    pub(crate) fn span(&self) -> Span {
        match self {
            Self::Lit { span, .. }
            | Self::Ident { span, .. }
            | Self::Field { span, .. }
            | Self::Index { span, .. }
            | Self::Call { span, .. }
            | Self::Query { span, .. }
            | Self::Case { span, .. }
            | Self::Unary { span, .. }
            | Self::Convert { span, .. }
            | Self::Binary { span, .. }
            | Self::Tuple { span, .. }
            | Self::List { span, .. }
            | Self::Record { span, .. } => *span,
        }
    }

    pub(crate) fn set_ty(&mut self, to: usize) {
        match self {
            Self::Lit { ty, .. }
            | Self::Ident { ty, .. }
            | Self::Field { ty, .. }
            | Self::Index { ty, .. }
            | Self::Call { ty, .. }
            | Self::Query { ty, .. }
            | Self::Case { ty, .. }
            | Self::Unary { ty, .. }
            | Self::Convert { ty, .. }
            | Self::Binary { ty, .. }
            | Self::Tuple { ty, .. }
            | Self::List { ty, .. }
            | Self::Record { ty, .. } => *ty = to,
        }
    }

    pub(crate) fn ty(&self) -> usize {
        match self {
            Self::Lit { ty, .. }
            | Self::Ident { ty, .. }
            | Self::Field { ty, .. }
            | Self::Index { ty, .. }
            | Self::Call { ty, .. }
            | Self::Query { ty, .. }
            | Self::Case { ty, .. }
            | Self::Unary { ty, .. }
            | Self::Convert { ty, .. }
            | Self::Binary { ty, .. }
            | Self::Tuple { ty, .. }
            | Self::List { ty, .. }
            | Self::Record { ty, .. } => *ty,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Arm {
    pub span: Span,
    /// `| A | B -> ...` lists both. An arm with several binds no payload.
    pub ctors: Vec<String>,
    pub bind: Option<String>,
    pub bind_sym: Option<usize>,
    /// Names from `Some((q, r))`, or from `Some { x; y = b }` in the order written.
    pub tuple_names: Vec<String>,
    /// The field each of `tuple_names` binds in a brace pattern; empty for a tuple pattern.
    pub fields: Vec<String>,
    /// A brace pattern ends in `_`, which ignores the fields it does not name.
    pub rest: bool,
    /// One per name that is not `_`, set by the checker. Each is a field of `bind_sym`,
    /// which holds the payload whole.
    pub tuple_syms: Vec<usize>,
    /// Each of `tuple_syms`' index in the payload's fields.
    pub tuple_at: Vec<usize>,
    pub stmts: Vec<Stmt>,
    pub expr: Expr,
}

impl Arm {
    /// The arm's block ends in `fail`, so it produces no value.
    pub(crate) fn fails(&self) -> bool {
        matches!(self.stmts.last(), Some(Stmt::Fail { .. }))
            && matches!(self.expr, Expr::Lit { lit: Lit::Unit, .. })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_map_places_bytes_as_the_lexer_counts_lines() {
        let src = "ab\n\ncé d\r\n  x\n";
        let mut map = SourceMap::of("f.lithe", src);
        for lo in 0..src.len() {
            let before = &src.as_bytes()[..lo];
            let line = before.iter().filter(|&&b| b == b'\n').count() as u32 + 1;
            let start = before
                .iter()
                .rposition(|&b| b == b'\n')
                .map_or(0, |i| i + 1);
            let span = Span {
                lo: lo as u32,
                hi: lo as u32 + 1,
            };
            let want = (line, (lo - start) as u32 + 1);
            assert_eq!(map.line_col(FileId(0), span), want, "byte {lo}");
        }
        assert_eq!(map.line_col(FileId(0), Span::NONE), (0, 0));
        assert_eq!(map.line_col(FileId::NONE, Span::default()), (0, 0));
        assert_eq!(map.add("f.lithe", src), FileId(0));
        assert_eq!(map.add("f.lithe", "x"), FileId(1));
        assert_eq!(map.find("f.lithe"), Some(FileId(0)));
        assert_eq!(map.path(FileId::NONE), "");
    }
}
