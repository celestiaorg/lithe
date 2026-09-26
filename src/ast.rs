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
        ty: TypeRef,
        expr: Expr,
        sym: Option<usize>,
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
    NatDivRem,
    /// `Bytes.word(b, offset)`: the 32 bytes of `b` starting at `offset`, as a `bytes32`.
    BytesWord,
    /// `Base64.encode(data)`: RFC 4648 base64, padded, as a `string`.
    Base64Encode,
    /// `Base64.encode_url(data)`: the URL and filename safe alphabet, unpadded.
    Base64EncodeUrl,
    /// `Base64.encode_with(data, file_safe, no_padding)`.
    Base64EncodeWith,
    /// `Base64.decode(data)`: the bytes a base64 string encodes, in either alphabet.
    Base64Decode,
    /// `Nat.mul_div(a, b, d)`: `a * b / d` without overflow in the product.
    NatMulDiv,
    NatMulMod,
    NatAddMod,
    IntDivRem,
    /// `Nat.to_string(n)`: an unsigned integer in decimal, as a `string`.
    NatToString,
    /// `Int.to_string(n)`: a signed integer in decimal, with a `-` when negative.
    IntToString,
    /// `List.pop(xs)`: drops a dynamic list's last element. Checked into an assignment of
    /// the list, `xs := List.pop(xs)`, so it writes what an assignment writes.
    ListPop,
    /// `Abi.supports_interface(id)`: whether `id` is ERC-165's or one the contract's
    /// `supports` lists, as the `supportsInterface` the compiler generates answers.
    AbiSupportsInterface,
    /// `Evm.creation_code(C)`: the creation code `create C(...)` runs, before its arguments.
    CreationCode,
    /// `Nat.wrapping_add(a, b)`, `Int.wrapping_mul(a, b)`, and so on: the operation on two
    /// values of one integer type, wrapped to its width instead of checked. `true` is `Int`.
    Wrapping(BinOp, bool),
    Transfer,
    /// `create Contract(args)`: the arguments go to its `deploy`; `base` holds the
    /// `CREATE2` salt, if any.
    Create,
    Cast,
    Some,
    None,
    /// A variant constructor, by its index in the variant's cases.
    Ctor(usize),
}

#[derive(Debug, Clone)]
pub(crate) enum Lit {
    Nat(Word),
    /// Hex literals keep how many digits were written.
    Int(Word, Option<u8>),
    Wei(Word),
    Duration(Word),
    Bool(bool),
    Str(String),
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
