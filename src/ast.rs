use crate::word::Word;

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
    /// `use M exposing { ... }`: the module externals the contract exposes.
    pub exposes: Vec<Exposing>,
    /// `supports I, J`: the interfaces the contract announces through ERC-165.
    pub supports: Vec<NameAt>,
    pub upgradeable: bool,
    pub guard: Option<GuardDecl>,
    /// `guard M.editor(...) is { ... }`: the contract's checks for its modules' guards.
    pub guards: Vec<Func>,
    /// Set when the file names its contract. An implicit file leaves this empty;
    /// tooling may still label artifacts from the file name.
    pub contract_name: Option<String>,
    pub contract_line: u32,
    pub contract_col: u32,
    /// Further contracts from the same file. One bytecode uses a single contract.
    pub siblings: Vec<Program>,
    /// The other contracts of the file, which this one may `defer create`.
    pub peers: Vec<Program>,
    /// The file the contract is written in, as its declarations' `origin` names it.
    pub origin: String,
    /// The contract's spec blocks, and those of the files it imports. The checker drops
    /// them: only `spec::check` reads them.
    pub specs: Vec<SpecBlock>,
    /// Checked for the spec tools, which read loop invariants. A build drops them.
    pub proving: bool,
    /// What each file of the program sees, and the canonical name of each declaration.
    pub scopes: std::sync::Arc<crate::resolve::Scopes>,
}

/// `spec is { ... }` or `spec for f is { ... }`: claims about the program that `lithe prove`
/// checks. Nothing in a spec block runs on chain.
#[derive(Debug, Clone)]
pub(crate) struct SpecBlock {
    pub line: u32,
    pub col: u32,
    pub origin: String,
    /// The function or route the block describes. `None` for `spec is`, the invariants.
    pub target: Option<NameAt>,
    /// `spec for external f` or `spec for function f`, for a module that has both.
    pub external: Option<bool>,
    /// `spec for f is partial`: the listed `raises` and `panics` conditions need not be the
    /// only ways `f` reverts.
    pub partial: bool,
    pub clauses: Vec<Clause>,
    /// Set when the block describes a module, from inside it or from `spec for module M`.
    pub module: Option<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct Clause {
    pub line: u32,
    pub col: u32,
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
    pub line: u32,
    pub col: u32,
    pub origin: String,
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
    pub line: u32,
    pub col: u32,
    pub name: String,
    /// Compiler-known constraint, currently `map_key`.
    pub constraint: Option<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct ModuleDecl {
    pub line: u32,
    pub col: u32,
    pub origin: String,
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
    /// The members the compiler implements, in a module of the standard library.
    pub intrinsics: Vec<Intrinsic>,
}

/// `intrinsic view function sender() : address;` or `intrinsic call;`: a member of a
/// standard library module that the compiler implements. The checker's rules for it are
/// its own; the signature, when Lithe can write one, states them.
#[derive(Debug, Clone)]
pub(crate) struct Intrinsic {
    pub line: u32,
    pub col: u32,
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
    /// `Abi.selector(I.method)` and `Abi.interface_id(I)`: `bytes4` constants.
    AbiSelector,
    AbiInterfaceId,
}

/// `use M exposing I, J, { ... }`: the contract uses `M` and exposes the members of the
/// interfaces it names and of its inline one. Each member is one of `M`'s externals.
#[derive(Debug, Clone)]
pub(crate) struct Exposing {
    pub line: u32,
    pub col: u32,
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
    pub line: u32,
    pub col: u32,
    pub stmts: Vec<Stmt>,
}

#[derive(Debug, Clone)]
pub(crate) struct UseDecl {
    pub line: u32,
    pub col: u32,
    pub path: String,
    pub alias: Option<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct TypeDecl {
    pub line: u32,
    pub col: u32,
    pub private: bool,
    pub origin: String,
    pub name: String,
    pub ty: TypeRef,
}

#[derive(Debug, Clone)]
pub(crate) struct ErrorDecl {
    pub line: u32,
    pub col: u32,
    pub private: bool,
    pub origin: String,
    pub name: String,
    pub payload: Option<TypeRef>,
}

#[derive(Debug, Clone)]
pub(crate) struct ErrorSetDecl {
    pub line: u32,
    pub col: u32,
    pub origin: String,
    pub name: String,
    pub members: Vec<NameAt>,
}

#[derive(Debug, Clone)]
pub(crate) struct NameAt {
    pub line: u32,
    pub col: u32,
    pub name: String,
}

#[derive(Debug, Clone)]
pub(crate) struct EventDecl {
    pub line: u32,
    pub col: u32,
    pub private: bool,
    pub anonymous: bool,
    pub origin: String,
    pub name: String,
    pub fields: Vec<FieldRef>,
}

#[derive(Debug, Clone)]
pub(crate) struct InterfaceDecl {
    pub line: u32,
    pub col: u32,
    pub origin: String,
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
        line: u32,
        col: u32,
        name: String,
    },
    Record {
        line: u32,
        col: u32,
        fields: Vec<FieldRef>,
        /// `tuple record`: one ABI tuple even as a whole parameter or result.
        tuple: bool,
    },
    Variant {
        line: u32,
        col: u32,
        variants: Vec<VariantRef>,
    },
    List {
        line: u32,
        col: u32,
        elem: Box<TypeRef>,
        /// `None` is a dynamic list. `Some(n)` is a fixed list of length `n`.
        len: Option<u32>,
        /// A fixed length written as a constant expression, `list(T, max_owners())`, which
        /// the checker evaluates. `len` is then `None`.
        size: Option<Box<Expr>>,
    },
    Option {
        line: u32,
        col: u32,
        elem: Box<TypeRef>,
    },
    Map {
        line: u32,
        col: u32,
        key: Box<TypeRef>,
        val: Box<TypeRef>,
    },
    Tuple {
        line: u32,
        col: u32,
        elems: Vec<TypeRef>,
    },
    /// `Set(address)` or `SetEnumerable(address).iterator`.
    Apply {
        line: u32,
        col: u32,
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
    pub(crate) fn line(&self) -> u32 {
        match self {
            Self::Name { line, .. }
            | Self::Record { line, .. }
            | Self::Variant { line, .. }
            | Self::List { line, .. }
            | Self::Option { line, .. }
            | Self::Map { line, .. }
            | Self::Tuple { line, .. }
            | Self::Apply { line, .. } => *line,
            Self::Hole { .. } => 0,
        }
    }

    pub(crate) fn col(&self) -> u32 {
        match self {
            Self::Name { col, .. }
            | Self::Record { col, .. }
            | Self::Variant { col, .. }
            | Self::List { col, .. }
            | Self::Option { col, .. }
            | Self::Map { col, .. }
            | Self::Tuple { col, .. }
            | Self::Apply { col, .. } => *col,
            Self::Hole { .. } => 0,
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

#[derive(Debug, Clone)]
pub(crate) struct FieldRef {
    pub line: u32,
    pub col: u32,
    pub name: String,
    pub ty: TypeRef,
    /// Set on an event field. Other records leave this false.
    pub indexed: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct VariantRef {
    pub line: u32,
    pub col: u32,
    pub name: String,
    pub payload: Option<TypeRef>,
    /// The ABI parameter name of a single-value payload, from `of (name : ty)`.
    pub param: String,
}

#[derive(Debug, Clone)]
pub(crate) struct Func {
    pub line: u32,
    pub col: u32,
    pub kind: ItemKind,
    pub private: bool,
    pub origin: String,
    pub name: String,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub ret: Option<TypeRef>,
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
}

#[derive(Debug, Clone)]
pub(crate) struct Guarded {
    pub line: u32,
    pub col: u32,
    pub name: String,
    /// The external's parameters the guard takes, by name.
    pub args: Vec<NameAt>,
}

/// `guard M.editor(...) is { ... }`, or `guard M.editor is f;`, which checks by calling `f`.
#[derive(Debug, Clone)]
pub(crate) struct GuardOf {
    pub module: NameAt,
    pub name: String,
    pub via: Option<NameAt>,
}

#[derive(Debug, Clone)]
pub(crate) struct Raises {
    pub parts: Vec<NameAt>,
}

#[derive(Debug, Clone)]
pub(crate) struct Param {
    pub line: u32,
    pub col: u32,
    pub mutable: bool,
    /// `storage name : T`: a reference to the storage the caller passes, which the
    /// function may write.
    pub storage: bool,
    pub name: String,
    pub ty: TypeRef,
    pub ty_id: usize,
    pub sym: Option<usize>,
}

#[derive(Debug, Clone)]
pub(crate) enum Stmt {
    Const {
        line: u32,
        col: u32,
        name: String,
        /// Element names when this binding is `const (a, b) : (T, U)`.
        parts: Vec<String>,
        ty: TypeRef,
        expr: Expr,
        sym: Option<usize>,
        part_syms: Vec<usize>,
    },
    Var {
        line: u32,
        col: u32,
        name: String,
        /// Element names when this binding is `var (a, b) : (T, U)`.
        parts: Vec<String>,
        ty: TypeRef,
        expr: Expr,
        sym: Option<usize>,
        part_syms: Vec<usize>,
    },
    Assign {
        line: u32,
        col: u32,
        path: Vec<String>,
        index: Option<Expr>,
        /// Keys after the first, for a map of maps: `m[a][b] := v`.
        keys: Vec<Expr>,
        /// Fields after the first key, each with how many keys come before it:
        /// `m[k].a[j].b := v` has `(1, a)` and `(2, b)`.
        fields: Vec<(usize, String)>,
        expr: Expr,
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
        line: u32,
        col: u32,
        cond: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
    },
    Assert {
        line: u32,
        col: u32,
        cond: Expr,
        reason: Raised,
    },
    Fail {
        reason: Raised,
    },
    Call {
        line: u32,
        col: u32,
        expr: Expr,
    },
    Skip,
    Emit {
        line: u32,
        col: u32,
        name: String,
        fields: Vec<(String, Expr)>,
    },
    Defer {
        line: u32,
        col: u32,
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
        line: u32,
        col: u32,
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
        line: u32,
        col: u32,
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
    pub line: u32,
    pub col: u32,
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
    pub line: u32,
    pub col: u32,
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
    /// `Base64.encode_url(data)`: the URL and filename safe alphabet, unpadded.
    Base64EncodeUrl,
    /// `Base64.encode_with(data, file_safe, no_padding)`.
    Base64EncodeWith,
    /// `Base64.decode(data)`: the bytes a base64 string encodes, in either alphabet.
    Base64Decode,
    /// `String.escape_json(s)`, or with `true`, `String.escape_html(s)`.
    StringEscape(bool),
    /// `String.replace(s, needle, replacement)`: every `needle` replaced, left to right.
    StringReplace,
    /// `Bytes.join(xs)`, or with `true`, `String.join(xs)`: a list's values one after another.
    Join(bool),
    /// `Uint.mul_div(a, b, d)`: `a * b / d` without overflow in the product.
    UintMulDiv,
    UintMulMod,
    UintAddMod,
    IntDivRem,
    /// `Uint.to_string(n)`: an unsigned integer in decimal, as a `string`.
    UintToString,
    /// `Int.to_string(n)`: a signed integer in decimal, with a `-` when negative.
    IntToString,
    /// `Uint.to_hex_string(n)`: `0x` and the fewest whole bytes in lowercase hex. With a
    /// second argument, exactly that many bytes.
    UintToHexString,
    /// `Address.to_hex_string(a)`: `0x` and 40 lowercase hex digits. `true` is
    /// `Address.to_checksum_string`, cased as EIP-55.
    AddressToHexString(bool),
    /// `Uint.from_bits(i)` and `Int.from_bits(n)`, the unchecked bit-cast between `int` and
    /// `uint`. `true` is `Int.from_bits`.
    FromBits(bool),
    /// `List.pop(xs)`: drops a dynamic list's last element. Checked into an assignment of
    /// the list, `xs := List.pop(xs)`, so it writes what an assignment writes.
    ListPop,
    /// `List.push(xs, v)`: appends to a dynamic list. Checked into an assignment at the
    /// list's length that grows it.
    ListPush,
    /// `Abi.supports_interface(id)`: whether `id` is ERC-165's or one the contract's
    /// `supports` lists, as the `supportsInterface` the compiler generates answers.
    AbiSupportsInterface,
    /// `Evm.creation_code(C)`: the creation code `create C(...)` runs, before its arguments.
    CreationCode,
    /// `Uint.wrapping_add(a, b)`, `Int.wrapping_mul(a, b)`, and so on: the operation on two
    /// values of one integer type, wrapped to its width instead of checked. `true` is `Int`.
    Wrapping(BinOp, bool),
    Transfer,
    /// `Evm.call(to, data)`: a `CALL` with `data` as the whole calldata. Its continuation
    /// gets the raw return data.
    RawCall,
    /// `Evm.delegate_call(to, data)`: `to`'s code runs as this contract, on `data`.
    DelegateCall,
    /// `Evm.static_call(to, data)`: a `STATICCALL` with `data` as the calldata, queried.
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
    /// `Crypto.mod_exp(base, exponent, modulus)`: 0x05 on byte strings.
    ModExp,
    /// `Uint.pow_mod(base, exponent, modulus)`: 0x05 on words.
    PowMod,
    /// `Crypto.bn254_add(a, b)`: 0x06.
    Bn254Add,
    /// `Crypto.bn254_mul(p, s)`: 0x07.
    Bn254Mul,
    /// `Crypto.bn254_pairing(pairs)`: 0x08.
    Bn254Pairing,
    /// `Crypto.blake2f(rounds, h, m, t, final)`: 0x09.
    Blake2f,
    /// `Crypto.kzg_point_evaluation(versioned_hash, z, y, commitment, proof)`: 0x0a.
    PointEvaluation,
    /// `Crypto.bls12_g1_add(a, b)`: 0x0b.
    Bls12G1Add,
    /// `Crypto.bls12_g1_msm(pairs)`: 0x0c.
    Bls12G1Msm,
    /// `Crypto.bls12_g2_add(a, b)`: 0x0d.
    Bls12G2Add,
    /// `Crypto.bls12_g2_msm(pairs)`: 0x0e.
    Bls12G2Msm,
    /// `Crypto.bls12_pairing(pairs)`: 0x0f.
    Bls12Pairing,
    /// `Crypto.bls12_map_fp_to_g1(fp)`: 0x10.
    Bls12MapFpToG1,
    /// `Crypto.bls12_map_fp2_to_g2(fp2)`: 0x11.
    Bls12MapFp2ToG2,
    /// `Crypto.p256_verify(hash, r, s, x, y)`: 0x100, EIP-7951.
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

#[derive(Debug, Clone)]
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
}

#[derive(Debug, Clone)]
pub(crate) enum Expr {
    Lit {
        line: u32,
        col: u32,
        lit: Lit,
        ty: usize,
    },
    Ident {
        line: u32,
        col: u32,
        name: String,
        sym: Option<usize>,
        builtin: Option<Builtin>,
        ty: usize,
    },
    Field {
        line: u32,
        col: u32,
        base: Box<Expr>,
        name: String,
        root: Option<usize>,
        leaf: u32,
        ty: usize,
    },
    Index {
        line: u32,
        col: u32,
        base: Box<Expr>,
        index: Box<Expr>,
        root: Option<usize>,
        leaf: u32,
        ty: usize,
    },
    Call {
        line: u32,
        col: u32,
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
        line: u32,
        col: u32,
        expr: Box<Expr>,
        /// `with gas = g`: the most gas the call may use, instead of all that is left.
        gas: Option<Box<Expr>>,
        ty: usize,
    },
    Case {
        line: u32,
        col: u32,
        scrut: Box<Expr>,
        arms: Vec<Arm>,
        ty: usize,
    },
    Unary {
        line: u32,
        col: u32,
        op: UnOp,
        expr: Box<Expr>,
        ty: usize,
    },
    Binary {
        line: u32,
        col: u32,
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
        ty: usize,
    },
    Tuple {
        line: u32,
        col: u32,
        elems: Vec<Expr>,
        ty: usize,
    },
    List {
        line: u32,
        col: u32,
        elems: Vec<Expr>,
        ty: usize,
    },
    Record {
        line: u32,
        col: u32,
        fields: Vec<(String, Expr)>,
        ty: usize,
    },
}

impl Expr {
    pub(crate) fn line(&self) -> u32 {
        match self {
            Self::Lit { line, .. }
            | Self::Ident { line, .. }
            | Self::Field { line, .. }
            | Self::Index { line, .. }
            | Self::Call { line, .. }
            | Self::Query { line, .. }
            | Self::Case { line, .. }
            | Self::Unary { line, .. }
            | Self::Binary { line, .. }
            | Self::Tuple { line, .. }
            | Self::List { line, .. }
            | Self::Record { line, .. } => *line,
        }
    }

    pub(crate) fn col(&self) -> u32 {
        match self {
            Self::Lit { col, .. }
            | Self::Ident { col, .. }
            | Self::Field { col, .. }
            | Self::Index { col, .. }
            | Self::Call { col, .. }
            | Self::Query { col, .. }
            | Self::Case { col, .. }
            | Self::Unary { col, .. }
            | Self::Binary { col, .. }
            | Self::Tuple { col, .. }
            | Self::List { col, .. }
            | Self::Record { col, .. } => *col,
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
            | Self::Binary { ty, .. }
            | Self::Tuple { ty, .. }
            | Self::List { ty, .. }
            | Self::Record { ty, .. } => *ty,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Arm {
    pub line: u32,
    pub col: u32,
    /// `| A | B -> ...` lists both. An arm with several binds no payload.
    pub ctors: Vec<String>,
    pub bind: Option<String>,
    pub bind_sym: Option<usize>,
    /// Names from `Some((q, r))`.
    pub tuple_names: Vec<String>,
    pub tuple_syms: Vec<usize>,
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
