//! Recursive descent for declarations and statements. Pratt parser for expressions.

use crate::ast::*;
use crate::error;
use crate::lex::{self, Kind, Token};
use crate::Error;

/// The word after a module's name in `use M delegated ...` that runs the module from its facet.
pub(crate) const DELEGATED: &str = "delegated";
/// Where `flat` may go: the positions whose ABI a record's fields can spread into.
pub(crate) const FLAT_ONLY: &str = "`flat` goes only on an external function's or interface method's parameter or result, or a dispatched case's payload";

pub(crate) fn parse(src: &str, names: &std::sync::Arc<Names>) -> Result<Program, Error> {
    let files = std::sync::Arc::new(SourceMap::of("", src));
    let mut parser = Parser {
        src,
        toks: lex::tokenize(src)?,
        names: names.clone(),
        i: 0,
        declaring: false,
        in_spec: false,
        errors: Vec::new(),
    };
    let prog = match parser.program() {
        Ok(prog) => Some(prog),
        // Whatever ended the parse joins the errors already recovered from, so the error the
        // caller sees first is the earliest one in the file, as it was before recovery existed.
        Err(err) => {
            parser.errors.push(err);
            None
        }
    };
    if let Some(err) = parser.all_errors() {
        return Err(err.placed(&files, FileId::default()));
    }
    let mut prog = prog.expect("a parse with no error builds a program");
    prog.share_files(&files);
    Ok(prog)
}

/// Where each line of `src` starts, in bytes: what turns a [`Span`] back into a line and column.
pub(crate) fn line_starts(src: &str) -> Vec<u32> {
    std::iter::once(0)
        .chain(src.match_indices('\n').map(|(i, _)| i as u32 + 1))
        .collect()
}

/// A spec file, `x.spec.lithe`: spec blocks for the contract and modules of `x.lithe`.
pub(crate) struct SpecFile {
    /// `spec is` and `spec for f` at the top level, for a file's one implicit contract.
    pub bare: Vec<SpecBlock>,
    /// `spec for contract C is { ... }`.
    pub contracts: Vec<(NameAt, Vec<SpecBlock>)>,
    /// `spec for module M is { ... }`: each block has `module` set.
    pub modules: Vec<(NameAt, Vec<SpecBlock>)>,
}

pub(crate) fn parse_specs(src: &str) -> Result<SpecFile, Error> {
    let files = SourceMap::of("", src);
    spec_file(src).map_err(|err| err.placed(&files, FileId::default()))
}

fn spec_file(src: &str) -> Result<SpecFile, Error> {
    let toks = lex::tokenize(src)?;
    let mut parser = Parser {
        src,
        toks,
        names: Names::shared(),
        i: 0,
        declaring: false,
        in_spec: false,
        errors: Vec::new(),
    };
    let mut file = SpecFile {
        bare: Vec::new(),
        contracts: Vec::new(),
        modules: Vec::new(),
    };
    let built = (|| -> Result<(), Error> {
        while parser.kind() != Kind::Eof {
            if parser.kind() == Kind::Semi {
                parser.bump();
                continue;
            }
            if !parser.spec_ahead() {
                return Err(parser.err(format!(
                    "a spec file holds only spec blocks; found {}",
                    parser.found()
                )));
            }
            match parser.peek_kind(2) {
                Kind::Contract => {
                    let (name, blocks) = parser.spec_wrapper()?;
                    file.contracts.push((name, blocks));
                }
                Kind::Module => {
                    let (name, blocks) = parser.spec_wrapper()?;
                    file.modules.push((name, blocks));
                }
                _ => file.bare.push(parser.spec_block(None)?),
            }
        }
        Ok(())
    })();
    // Statement errors recovered from inside a spec block are errors too, in file order.
    if let Err(err) = built {
        parser.errors.push(err);
    }
    if let Some(err) = parser.all_errors() {
        return Err(err);
    }
    Ok(file)
}

enum StorageItem {
    Default(TypeDecl, String),
    Named(DomainDecl),
}

struct Deco {
    kind: ItemKind,
    payable: bool,
    nonreentrant: bool,
    external_pure: bool,
}

impl Deco {
    fn of(kind: ItemKind) -> Self {
        Deco {
            kind,
            payable: false,
            nonreentrant: false,
            external_pure: false,
        }
    }
}

#[derive(Default)]
struct CallOptions {
    value: Option<Expr>,
    salt: Option<Expr>,
    gas: Option<Expr>,
}

struct Parser<'a> {
    src: &'a str,
    toks: Vec<Token>,
    i: usize,
    /// The table names are interned into.
    names: std::sync::Arc<Names>,
    /// Inside `use M exposing { ... }`: functions are external and have no body.
    declaring: bool,
    /// Inside a spec block, where `old.`, `new.`, `sum`, `count`, and `forall` are spec forms.
    in_spec: bool,
    /// Errors recovered from at the statement level, after the one that ends the parse.
    errors: Vec<Error>,
}

impl Parser<'_> {
    /// The parse's first error, with the statement-level ones it recovered from after it.
    fn all_errors(&mut self) -> Option<Error> {
        let mut errors = std::mem::take(&mut self.errors);
        if errors.len() > 1 {
            errors[0].more = errors.split_off(1);
        }
        errors.into_iter().next()
    }
}

/// A fixed list's length, which must be from 1 to 1024.
pub(crate) fn list_len(word: crate::word::Word, span: Span) -> Result<u32, Error> {
    if word.0[1] != 0 || word.0[2] != 0 || word.0[3] != 0 || word.0[0] == 0 || word.0[0] > 1024 {
        return Err(error(span, "list length must be from 1 to 1024"));
    }
    Ok(word.0[0] as u32)
}

fn path_expr(names: &Names, span: Span, path: &[String]) -> Expr {
    let mut expr = Expr::Ident {
        span,
        name: names.intern(&path[0]),
        sym: None,
        builtin: None,
        ty: 0,
    };
    for name in path.iter().skip(1) {
        expr = Expr::Field {
            span,
            base: Box::new(expr),
            name: names.intern(name),
            root: None,
            leaf: 0,
            ty: 0,
        };
    }
    expr
}

struct Body {
    span: Span,
    name: Option<String>,
    types: Vec<TypeDecl>,
    errors: Vec<ErrorDecl>,
    error_sets: Vec<ErrorSetDecl>,
    events: Vec<EventDecl>,
    interfaces: Vec<InterfaceDecl>,
    funcs: Vec<Func>,
    domains: Vec<DomainDecl>,
    compose: Vec<NameAt>,
    facets: Vec<NameAt>,
    exposes: Vec<Exposing>,
    supports: Vec<NameAt>,
    upgradeable: bool,
    storage_id: String,
    guard: Option<GuardDecl>,
    guards: Vec<Func>,
    hooks: Vec<Func>,
    specs: Vec<SpecBlock>,
}

impl Body {
    fn new(span: Span, name: Option<String>) -> Self {
        Self {
            span,
            name,
            types: Vec::new(),
            errors: Vec::new(),
            error_sets: Vec::new(),
            events: Vec::new(),
            interfaces: Vec::new(),
            funcs: Vec::new(),
            domains: Vec::new(),
            compose: Vec::new(),
            facets: Vec::new(),
            exposes: Vec::new(),
            supports: Vec::new(),
            upgradeable: false,
            storage_id: String::new(),
            guard: None,
            guards: Vec::new(),
            hooks: Vec::new(),
            specs: Vec::new(),
        }
    }

    fn into_program(
        self,
        modules: Vec<ModuleDecl>,
        uses: Vec<UseDecl>,
        names: std::sync::Arc<Names>,
    ) -> Program {
        let named = self.name.is_some();
        Program {
            uses,
            types: self.types,
            errors: self.errors,
            error_sets: self.error_sets,
            events: self.events,
            interfaces: self.interfaces,
            funcs: self.funcs,
            domains: self.domains,
            modules,
            compose: self.compose,
            implied: Vec::new(),
            refs: Vec::new(),
            facets: self.facets,
            exposes: self.exposes,
            supports: self.supports,
            upgradeable: self.upgradeable,
            storage_id: self.storage_id,
            guard: self.guard,
            guards: self.guards,
            hooks: self.hooks,
            calls_back: false,
            contract_name: self.name,
            contract_span: if named { self.span } else { Span::NONE },
            siblings: Vec::new(),
            peers: Vec::new(),
            file: FileId::default(),
            specs: self.specs,
            proving: false,
            scopes: Default::default(),
            names,
            files: Default::default(),
        }
    }
}

impl<'a> Parser<'a> {
    fn program(&mut self) -> Result<Program, Error> {
        let mut uses = Vec::new();
        let mut modules = Vec::new();
        let mut shared_interfaces = Vec::new();
        let mut implicit = Body::new(Span::default(), None);
        let mut explicit = Vec::new();
        let mut saw_implicit = false;
        let mut contract_specs: Vec<(NameAt, Vec<SpecBlock>)> = Vec::new();
        let mut module_specs: Vec<(NameAt, Vec<SpecBlock>)> = Vec::new();
        while self.kind() == Kind::Import {
            uses.push(self.use_decl()?);
        }
        while self.kind() != Kind::Eof {
            if self.kind() == Kind::Semi {
                self.bump();
                continue;
            }
            match self.kind() {
                Kind::Module => modules.push(self.module_decl()?),
                Kind::Interface => shared_interfaces.push(self.interface_decl()?),
                Kind::Ident if self.spec_ahead() && self.peek_kind(2) == Kind::Contract => {
                    contract_specs.push(self.spec_wrapper()?);
                }
                Kind::Ident if self.spec_ahead() && self.peek_kind(2) == Kind::Module => {
                    module_specs.push(self.spec_wrapper()?);
                }
                Kind::Contract => {
                    if saw_implicit {
                        let span = self.at();
                        self.bump();
                        let name = self.ident()?;
                        return Err(error(
                            span,
                            format!(
                                "explicit `contract {name}` cannot share a file with top-level contract declarations"
                            ),
                        ));
                    }
                    let body = self.contract_body()?;
                    if explicit.iter().any(|have: &Body| have.name == body.name) {
                        return Err(error(
                            body.span,
                            format!(
                                "contract `{}` is already declared",
                                body.name.as_deref().unwrap_or("")
                            ),
                        ));
                    }
                    explicit.push(body);
                }
                Kind::End => {
                    return Err(self.err("`end` no longer closes a contract or module; use `}`"));
                }
                Kind::Private => {
                    self.bump();
                    if matches!(self.kind(), Kind::Module | Kind::Contract | Kind::Interface) {
                        return Err(self.err(match self.kind() {
                            Kind::Module => "a module cannot be private",
                            Kind::Contract => "a contract cannot be private",
                            _ => "an interface cannot be private",
                        }));
                    }
                    self.bare_decl(&mut implicit, &explicit, &mut saw_implicit, true)?;
                }
                _ => {
                    self.bare_decl(&mut implicit, &explicit, &mut saw_implicit, false)?;
                }
            }
        }
        for (name, blocks) in contract_specs {
            let written = self.names.get(name.name);
            let Some(body) = explicit
                .iter_mut()
                .find(|body| body.name.as_deref() == Some(&*written))
            else {
                return Err(error(
                    name.span,
                    format!("no contract `{}` in this file", name.name),
                ));
            };
            body.specs.extend(blocks);
        }
        // `spec for module M` blocks join `M`'s when the contract is checked, which knows
        // whether it uses `M`.
        let module_specs: Vec<SpecBlock> = module_specs
            .into_iter()
            .flat_map(|(_, blocks)| blocks)
            .collect();
        if explicit.is_empty() {
            implicit.interfaces.extend(shared_interfaces);
            implicit.specs.extend(module_specs);
            return Ok(implicit.into_program(modules, uses, self.names.clone()));
        }
        let mut programs = Vec::new();
        for (index, mut body) in explicit.into_iter().enumerate() {
            body.interfaces.extend(shared_interfaces.clone());
            body.specs.extend(module_specs.iter().cloned());
            let unit_uses = if index == 0 { uses.clone() } else { Vec::new() };
            programs.push(body.into_program(modules.clone(), unit_uses, self.names.clone()));
        }
        let mut main = programs.remove(0);
        main.siblings = programs;
        Ok(main)
    }

    fn bare_decl(
        &mut self,
        implicit: &mut Body,
        explicit: &[Body],
        saw_implicit: &mut bool,
        private: bool,
    ) -> Result<(), Error> {
        if !explicit.is_empty() {
            let span = self.at();
            return Err(error(
                span,
                "this file uses explicit contracts\nmove this declaration inside a contract",
            ));
        }
        *saw_implicit = true;
        self.take_decl(private, implicit)
    }

    fn contract_body(&mut self) -> Result<Body, Error> {
        let span = self.at();
        self.want(Kind::Contract)?;
        let name = self.ident()?;
        let mut body = Body::new(span, Some(name));
        if self.kind() == Kind::Upgradeable {
            body.upgradeable = true;
            self.bump();
        }
        self.want(Kind::Is)?;
        self.want(Kind::LBrace)?;
        while self.kind() != Kind::RBrace && self.kind() != Kind::Eof {
            if self.kind() == Kind::Semi {
                self.bump();
                continue;
            }
            if self.kind() == Kind::End {
                return Err(self.err("close this contract with `}`"));
            }
            if self.kind() == Kind::Module {
                return Err(self.err("declare a module outside the contract"));
            }
            if self.kind() == Kind::Contract {
                return Err(self.err("a contract cannot contain another contract"));
            }
            let private = self.kind() == Kind::Private;
            if private {
                self.bump();
                if self.kind() == Kind::Module {
                    return Err(self.err("declare a module outside the contract"));
                }
                if self.kind() == Kind::Contract {
                    return Err(self.err("a contract cannot contain another contract"));
                }
            }
            self.take_decl(private, &mut body)?;
        }
        self.want(Kind::RBrace)?;
        Ok(body)
    }

    fn take_decl(&mut self, private: bool, body: &mut Body) -> Result<(), Error> {
        match self.kind() {
            Kind::Type => {
                let mut decl = self.type_decl()?;
                decl.private = private;
                body.types.push(decl);
            }
            Kind::ErrorKw => {
                let mut decl = self.error_decl()?;
                decl.private = private;
                body.errors.push(decl);
            }
            Kind::ErrorsKw if private => {
                return Err(self.err("an error set cannot be private"));
            }
            Kind::ErrorsKw => body.error_sets.push(self.error_set_decl()?),
            Kind::Anonymous | Kind::Event => {
                let mut decl = self.event_decl()?;
                decl.private = private;
                body.events.push(decl);
            }
            Kind::Interface if private => {
                return Err(self.err("an interface cannot be private"));
            }
            Kind::Interface => body.interfaces.push(self.interface_decl()?),
            Kind::View | Kind::Pure if self.hook_ahead() => {
                return Err(self.err(
                    "a contract implements a hook without restating its effect: write `hook h ...` in `use M ... with { ... }`; the module's declaration says what it may do",
                ));
            }
            Kind::External
            | Kind::Payable
            | Kind::Nonreentrant
            | Kind::View
            | Kind::Pure
            | Kind::Function => {
                let deco = self.header()?;
                if private && matches!(deco.kind, ItemKind::Entry | ItemKind::View) {
                    return Err(self.err("an external function cannot be private"));
                }
                if private && deco.kind == ItemKind::Deploy {
                    return Err(self.err("`deploy` cannot be private"));
                }
                if let (true, Some(word)) = (private, special_word(deco.kind)) {
                    return Err(self.err(format!("`{word}` cannot be private")));
                }
                let func = self.item(deco, private)?;
                if let Some(guarded) = &func.guarded {
                    return Err(error(
                        guarded.span,
                        "`guarded` names a guard of the external's module; a contract's own external checks in its body",
                    ));
                }
                body.funcs.push(func);
            }
            Kind::Const => body.funcs.push(self.const_decl(private)?),
            Kind::Ident if self.spec_ahead() => {
                if private {
                    return Err(self.err("a spec block cannot be private"));
                }
                if matches!(self.peek_kind(2), Kind::Contract | Kind::Module) {
                    return Err(self.err(
                        "a spec block inside a contract describes that contract; write `spec is` or `spec for f`",
                    ));
                }
                body.specs.push(self.spec_block(None)?);
            }
            Kind::Ident if self.special_ahead() => {
                if private {
                    return Err(self.err(format!("`{}` cannot be private", self.slice())));
                }
                let deco = self.header()?;
                body.funcs.push(self.item(deco, false)?);
            }
            Kind::Deploy if private => {
                return Err(self.err("`deploy` cannot be private"));
            }
            Kind::Deploy => body
                .funcs
                .push(self.item(Deco::of(ItemKind::Deploy), false)?),
            Kind::Migrate if private => {
                return Err(self.err("a migration cannot be private"));
            }
            Kind::Migrate => body
                .funcs
                .push(self.item(Deco::of(ItemKind::Migrate), false)?),
            Kind::Upgradeable if private => {
                return Err(self.err("`upgradeable` cannot be private"));
            }
            Kind::Upgradeable => {
                if body.upgradeable {
                    return Err(self.err("`upgradeable` is already set"));
                }
                body.upgradeable = true;
                self.bump();
            }
            Kind::Upgrade if private => {
                return Err(self.err("an upgrade guard cannot be private"));
            }
            Kind::Upgrade => body.guard = Some(self.guard_decl()?),
            Kind::Module => return Err(self.err("declare a module outside the contract")),
            Kind::Use if private => return Err(self.err("`use` cannot be private")),
            Kind::Use => {
                let span = self.at();
                self.bump();
                let names = self.name_list()?;
                if names.len() > 1 {
                    let last = &names[names.len() - 1].name;
                    let shape = match (self.kind(), self.slice()) {
                        (Kind::Ident, DELEGATED) => {
                            Some((DELEGATED, format!("use {last} delegated;")))
                        }
                        (Kind::Ident, "exposing") => {
                            Some(("exposing", format!("use {last} exposing ...;")))
                        }
                        (Kind::With, _) => Some(("with", format!("use {last} with {{ ... }}"))),
                        _ => None,
                    };
                    if let Some((word, shape)) = shape {
                        return Err(self.err(format!(
                            "`{word}` applies to one module: write `{shape}` on its own line"
                        )));
                    }
                    if self.kind() == Kind::Semi {
                        self.bump();
                    }
                    body.compose.extend(names);
                    return Ok(());
                }
                let module = names.into_iter().next().expect("a name").name;
                let written = module.to_string();
                if self.kind() == Kind::Ident && self.slice() == DELEGATED {
                    self.bump();
                    body.facets.push(NameAt { span, name: module });
                }
                if self.kind() == Kind::Ident && self.slice() == "exposing" {
                    self.bump();
                    let exposed = self.use_exposing(span, written.clone())?;
                    if body.exposes.iter().any(|have| have.module == written) {
                        return Err(error(
                            span,
                            format!(
                                "`use {module} exposing` appears twice; list all its interfaces in one"
                            ),
                        ));
                    }
                    body.exposes.push(exposed);
                }
                if self.kind() == Kind::With {
                    self.use_with(&written, body)?;
                } else if self.kind() == Kind::Semi {
                    self.bump();
                }
                body.compose.push(NameAt { span, name: module });
            }
            Kind::Contract => {
                return Err(self.err("a contract cannot contain another contract"));
            }
            Kind::Ident
                if matches!(self.slice(), "guard" | "hook") && self.peek_kind(1) == Kind::Ident =>
            {
                let span = self.at();
                let word = self.slice().to_string();
                self.bump();
                let path = self.dotted()?;
                let (module, name) = path.rsplit_once('.').unwrap_or(("M", &path));
                return Err(error(
                    span,
                    format!(
                        "a {word} is bound where the contract uses its module: move it into `use {} ... with {{ {word} {name} ... }}`",
                        crate::modules::shown(module)
                    ),
                ));
            }
            Kind::Ident if !private && self.slice() == "supports" => {
                let names = self.supports_list()?;
                body.supports.extend(names);
            }
            Kind::Ident if !private && self.slice() == "storage" => match self.storage_decl()? {
                StorageItem::Default(decl, id) => {
                    body.types.push(decl);
                    body.storage_id = id;
                }
                StorageItem::Named(decl) => body.domains.push(decl),
            },
            Kind::Ident if !private && self.slice() == "transient" => {
                let decl = self.transient_decl()?;
                body.domains.push(decl);
            }
            Kind::Ident if !private && self.slice() == "immutable" => {
                let mut decl = self.immutable_decl()?;
                if decl.id.is_empty() {
                    decl.id = "lithe.immutable".to_string();
                }
                body.domains.push(decl);
            }
            _ => {
                return Err(self.err(format!("expected a declaration, found {}", self.found())));
            }
        }
        Ok(())
    }

    /// `A, B.C`: the modules a `use` or `requires` names, each where its name is written.
    fn name_list(&mut self) -> Result<Vec<NameAt>, Error> {
        let mut names = Vec::new();
        loop {
            let span = self.at();
            let name = self.dotted_at(span)?;
            names.push(name);
            if self.kind() != Kind::Comma {
                return Ok(names);
            }
            self.bump();
        }
    }

    /// `exposing I, J, { ... }` after `use M`: the interfaces whose members the contract
    /// exposes from `M`, named or inline. Each member is one of `M`'s externals.
    fn use_exposing(&mut self, span: Span, module: String) -> Result<Exposing, Error> {
        let mut interfaces = Vec::new();
        let mut decls = None;
        loop {
            if self.kind() == Kind::LBrace {
                let bspan = self.at();
                if decls.is_some() {
                    return Err(error(
                        bspan,
                        "`use ... exposing` has one inline interface; put its members together",
                    ));
                }
                let members = self.interface_body()?;
                if members.is_empty() {
                    return Err(error(bspan, "an inline interface needs a method"));
                }
                decls = Some(members);
            } else {
                interfaces.push(self.interface_name()?);
            }
            if self.kind() != Kind::Comma {
                break;
            }
            self.bump();
        }
        Ok(Exposing {
            span,
            module,
            interfaces,
            decls: decls.unwrap_or_default(),
        })
    }

    /// `supports I, J`: the named interfaces the contract announces through ERC-165.
    fn supports_list(&mut self) -> Result<Vec<NameAt>, Error> {
        self.bump();
        let mut names = Vec::new();
        loop {
            if self.kind() == Kind::LBrace {
                return Err(self.err(
                    "`supports` lists named interfaces; declare this one with `interface` and name it",
                ));
            }
            names.push(self.interface_name()?);
            if self.kind() != Kind::Comma {
                break;
            }
            self.bump();
        }
        if self.kind() == Kind::Semi {
            self.bump();
        }
        Ok(names)
    }

    fn interface_name(&mut self) -> Result<NameAt, Error> {
        let span = self.at();
        let mut name = self.ident_sym()?;
        while self.kind() == Kind::Dot {
            self.bump();
            let rest = self.ident_sym()?;
            name = self.sym(&format!("{name}.{rest}"));
        }
        Ok(Self::named_at(span, name))
    }

    fn module_decl(&mut self) -> Result<ModuleDecl, Error> {
        let span = self.at();
        self.want(Kind::Module)?;
        let name = self.ident()?;
        let params = if self.kind() == Kind::LParen {
            self.type_param_list()?
        } else {
            Vec::new()
        };
        self.want(Kind::Is)?;
        self.want(Kind::LBrace)?;
        let mut requires: Vec<NameAt> = Vec::new();
        let mut domains: Vec<DomainDecl> = Vec::new();
        let mut types = Vec::new();
        let mut errors = Vec::new();
        let mut error_sets = Vec::new();
        let mut events = Vec::new();
        let mut funcs = Vec::new();
        let mut specs = Vec::new();
        let mut intrinsics = Vec::new();
        let mut guards = Vec::new();
        let mut hooks = Vec::new();
        while self.kind() != Kind::RBrace && self.kind() != Kind::Eof {
            if self.kind() == Kind::Semi {
                self.bump();
                continue;
            }
            if self.kind() == Kind::End {
                return Err(self.err("close this module with `}`"));
            }
            if self.spec_ahead() {
                if matches!(self.peek_kind(2), Kind::Contract | Kind::Module) {
                    return Err(self.err(
                        "a spec block inside a module describes that module; write `spec is` or `spec for f`",
                    ));
                }
                specs.push(self.spec_block(Some(name.clone()))?);
                continue;
            }
            let private = self.kind() == Kind::Private;
            if private {
                self.bump();
                if !matches!(
                    self.kind(),
                    Kind::View
                        | Kind::Pure
                        | Kind::Function
                        | Kind::External
                        | Kind::Payable
                        | Kind::Const
                ) {
                    return Err(
                        self.err("only a module's internal functions and constants can be private")
                    );
                }
            }
            match self.kind() {
                Kind::Requires => {
                    self.bump();
                    for required in self.name_list()? {
                        if requires.iter().any(|have| have.name == required.name) {
                            return Err(error(
                                required.span,
                                format!(
                                    "module `{name}` requires `{}` more than once",
                                    required.name
                                ),
                            ));
                        }
                        requires.push(required);
                    }
                    if self.kind() == Kind::Semi {
                        self.bump();
                    }
                }
                Kind::Import => {
                    return Err(self
                        .err("declare storage in the module: `storage name at \"id\" is record`"));
                }
                Kind::Ident if matches!(self.slice(), "storage" | "transient" | "immutable") => {
                    let mut decl = if self.slice() == "immutable" {
                        self.immutable_decl()?
                    } else if self.slice() == "transient" {
                        self.transient_decl()?
                    } else {
                        match self.storage_decl()? {
                            StorageItem::Named(decl) => decl,
                            StorageItem::Default(decl, id) => DomainDecl {
                                span: decl.span,
                                file: FileId::default(),
                                name: decl.name,
                                id,
                                ty: decl.ty,
                                owner: None,
                                transient: false,
                                immutable: false,
                            },
                        }
                    };
                    if !decl.transient && decl.id.is_empty() {
                        let kind = if decl.immutable {
                            "immutable"
                        } else {
                            "storage"
                        };
                        return Err(error(
                            decl.span,
                            format!(
                                "a module's default {kind} record needs an ERC-7201 id: `{kind} at \"id\" is record`"
                            ),
                        ));
                    }
                    if let Some(have) = domains.iter().find(|have| have.name == decl.name) {
                        let files = SourceMap::of("", self.src);
                        let at =
                            |span| crate::modules::Site::of(&files, FileId::default(), span, "");
                        return Err(crate::modules::clash(
                            format!(
                                "module `{name}` declares storage `{}` more than once",
                                decl.name
                            ),
                            &decl.name,
                            &at(have.span),
                            &at(decl.span),
                            None,
                            "rename one of them",
                        ));
                    }
                    decl.owner = Some(name.clone());
                    if self.kind() == Kind::Semi {
                        self.bump();
                    }
                    domains.push(decl);
                }
                Kind::Ident if self.slice() == "intrinsic" => {
                    let decl = self.intrinsic_decl()?;
                    if intrinsics
                        .iter()
                        .any(|have: &Intrinsic| have.name == decl.name)
                    {
                        return Err(error(
                            decl.span,
                            format!("module `{name}` declares `{}` more than once", decl.name),
                        ));
                    }
                    intrinsics.push(decl);
                }
                _ if self.hook_ahead() => {
                    if private {
                        return Err(self.err("a hook cannot be private"));
                    }
                    let decl = self.hook_sig()?;
                    if hooks.iter().any(|have: &Func| have.name == decl.name) {
                        return Err(error(
                            decl.span,
                            format!(
                                "module `{name}` declares hook `{}` more than once",
                                decl.name
                            ),
                        ));
                    }
                    hooks.push(decl);
                }
                Kind::Ident if self.slice() == "guard" && self.peek_kind(1) == Kind::Ident => {
                    let decl = self.guard_sig()?;
                    if guards.iter().any(|have: &Func| have.name == decl.name) {
                        return Err(error(
                            decl.span,
                            format!(
                                "module `{name}` declares guard `{}` more than once",
                                decl.name
                            ),
                        ));
                    }
                    guards.push(decl);
                }
                Kind::Const => funcs.push(self.const_decl(private)?),
                Kind::Type => types.push(self.type_decl()?),
                Kind::ErrorKw => errors.push(self.error_decl()?),
                Kind::ErrorsKw => error_sets.push(self.error_set_decl()?),
                Kind::Anonymous | Kind::Event => events.push(self.event_decl()?),
                Kind::External
                | Kind::Payable
                | Kind::Nonreentrant
                | Kind::View
                | Kind::Pure
                | Kind::Function => {
                    let at = self.at();
                    let deco = self.header()?;
                    if let Some(word) = special_word(deco.kind) {
                        return Err(error(at, format!("`{word}` belongs to the contract")));
                    }
                    if private && matches!(deco.kind, ItemKind::Entry | ItemKind::View) {
                        return Err(error(at, "an external function cannot be private"));
                    }
                    let mut func = self.item(deco, false)?;
                    func.private = private;
                    funcs.push(func);
                }
                Kind::Ident if self.special_ahead() => {
                    return Err(self.err(format!("`{}` belongs to the contract", self.slice())));
                }
                Kind::Module => {
                    return Err(self.err("a module cannot contain another module"));
                }
                Kind::Use => {
                    return Err(self.err("use a module from the contract"));
                }
                Kind::Deploy | Kind::Migrate | Kind::Upgrade => {
                    return Err(self.err(format!("{} belongs to the contract", self.found())));
                }
                Kind::Contract => {
                    return Err(self.err("a module cannot contain a contract"));
                }
                _ => {
                    return Err(self.err(format!("expected a declaration, found {}", self.found())));
                }
            }
        }
        self.want(Kind::RBrace)?;
        let require_names: Vec<String> = requires.iter().map(|s| s.name.to_string()).collect();
        for func in funcs.iter_mut().chain(&mut guards).chain(&mut hooks) {
            func.module = Some(name.clone());
            func.requires = require_names.clone();
        }
        if let Some(c) = funcs.iter().find(|c| {
            c.constant
                && funcs
                    .iter()
                    .any(|f| f.name == c.name && !std::ptr::eq(f, *c))
        }) {
            return Err(error(
                c.span,
                format!("module `{name}` declares `{}` more than once", c.name),
            ));
        }
        if let Some(hook) = hooks
            .iter()
            .find(|hook| funcs.iter().any(|f| f.name == hook.name))
        {
            return Err(error(
                hook.span,
                format!(
                    "module `{name}` declares `{}` as a hook and as a function; rename one",
                    hook.name
                ),
            ));
        }
        Ok(ModuleDecl {
            span,
            file: FileId::default(),
            name,
            params,
            requires,
            domains,
            types,
            errors,
            error_sets,
            events,
            funcs,
            specs,
            guards,
            hooks,
            intrinsics,
            refs: Vec::new(),
        })
    }

    /// `intrinsic name;`, or `intrinsic [view | pure] function name(a : T; ...) [: R];`.
    fn intrinsic_decl(&mut self) -> Result<Intrinsic, Error> {
        let span = self.at();
        self.bump();
        if self.kind() == Kind::Ident && self.peek_kind(1) == Kind::Semi {
            let name = self.ident()?;
            self.bump();
            return Ok(Intrinsic {
                span,
                name,
                sig: None,
                tag: None,
            });
        }
        let kind = match self.kind() {
            Kind::View => ItemKind::Readonly,
            Kind::Pure => ItemKind::Pure,
            _ => ItemKind::Function,
        };
        if kind != ItemKind::Function {
            self.bump();
        }
        self.want(Kind::Function)?;
        let fspan = self.at();
        let name = self.member_name()?;
        self.want(Kind::LParen)?;
        let mut params = Vec::new();
        while self.kind() != Kind::RParen {
            let pspan = self.at();
            let pname = self.ident()?;
            self.want(Kind::Colon)?;
            let ty = self.ty()?;
            params.push(Param {
                span: pspan,
                mutable: false,
                storage: false,
                name: pname,
                flat: false,
                ty,
                ty_id: 0,
                sym: None,
            });
            if self.kind() != Kind::Semi {
                break;
            }
            self.bump();
        }
        self.want(Kind::RParen)?;
        let ret = if self.kind() == Kind::Colon {
            self.bump();
            Some(self.ty()?)
        } else {
            None
        };
        self.want(Kind::Semi)?;
        Ok(Intrinsic {
            span,
            name: name.clone(),
            sig: Some(Func {
                span: fspan,
                kind,
                private: false,
                file: FileId::default(),
                name,
                type_params: Vec::new(),
                params,
                ret,
                ret_flat: false,
                ret_ty: 0,
                payable: false,
                nonreentrant: false,
                external_pure: false,
                raises: None,
                errors: Vec::new(),
                stmts: Vec::new(),
                tail: None,
                module: None,
                requires: Vec::new(),
                promoted: None,
                declares: None,
                interface: None,
                exported: None,
                forward: None,
                guarded: None,
                guard_of: None,
                constant: false,
                hook_of: None,
            }),
            tag: None,
        })
    }

    /// `(T, U)` names type parameters; `(storage s : T)` opens the parameters.
    fn looks_like_type_params(&self) -> bool {
        self.kind() == Kind::LParen
            && self.peek_kind(1) == Kind::Ident
            && self.peek_kind(2) != Kind::Ident
    }

    fn type_param_list(&mut self) -> Result<Vec<TypeParam>, Error> {
        self.want(Kind::LParen)?;
        if self.kind() == Kind::RParen {
            return Err(self.err("expected a type parameter"));
        }
        let mut params: Vec<TypeParam> = Vec::new();
        loop {
            let span = self.at();
            let name = self.ident()?;
            if params.iter().any(|param| param.name == name) {
                return Err(error(span, format!("duplicate type parameter `{name}`")));
            }
            let constraint = if self.kind() == Kind::Colon {
                self.bump();
                Some(self.ident()?)
            } else {
                None
            };
            params.push(TypeParam {
                span,
                name,
                constraint,
            });
            if self.kind() == Kind::Comma {
                self.bump();
                if self.kind() == Kind::RParen {
                    break;
                }
                continue;
            }
            break;
        }
        self.want(Kind::RParen)?;
        Ok(params)
    }

    fn slice(&self) -> &str {
        let tok = &self.toks[self.i];
        &self.src[tok.start..tok.end]
    }

    /// `spec is` or `spec for`: a spec block, where a declaration may be.
    fn spec_ahead(&self) -> bool {
        self.kind() == Kind::Ident
            && self.slice() == "spec"
            && matches!(self.peek_kind(1), Kind::Is | Kind::For)
    }

    /// `spec is { invariants }`, or `spec for f is [partial] { clauses }`.
    fn spec_block(&mut self, module: Option<String>) -> Result<SpecBlock, Error> {
        let span = self.at();
        self.bump();
        let target = if self.kind() == Kind::For {
            self.bump();
            let tspan = self.at();
            let name = self.ident_sym()?;
            Some(Self::named_at(tspan, name))
        } else {
            None
        };
        self.want(Kind::Is)?;
        let partial = self.kind() == Kind::Ident && self.slice() == "partial";
        if partial {
            if target.is_none() {
                return Err(self.err("only `spec for f` can be `partial`"));
            }
            self.bump();
        }
        self.want(Kind::LBrace)?;
        let saved = std::mem::replace(&mut self.in_spec, true);
        let mut clauses = Vec::new();
        while self.kind() != Kind::RBrace && self.kind() != Kind::Eof {
            if self.kind() == Kind::Semi {
                self.bump();
                continue;
            }
            clauses.push(self.clause(target.is_some())?);
        }
        self.in_spec = saved;
        self.want(Kind::RBrace)?;
        Ok(SpecBlock {
            span,
            file: FileId::default(),
            target,
            partial,
            clauses,
            module,
        })
    }

    /// `spec for contract C is { ... }` or `spec for module M is { ... }`: spec blocks written
    /// outside the contract or module they describe.
    fn spec_wrapper(&mut self) -> Result<(NameAt, Vec<SpecBlock>), Error> {
        self.bump();
        self.want(Kind::For)?;
        let module = self.kind() == Kind::Module;
        self.bump();
        let span = self.at();
        let name = self.ident_sym()?;
        self.want(Kind::Is)?;
        self.want(Kind::LBrace)?;
        let mut blocks = Vec::new();
        while self.kind() != Kind::RBrace && self.kind() != Kind::Eof {
            if self.kind() == Kind::Semi {
                self.bump();
                continue;
            }
            if !self.spec_ahead() || matches!(self.peek_kind(2), Kind::Contract | Kind::Module) {
                return Err(self.err(format!(
                    "expected `spec is` or `spec for f`, found {}",
                    self.found()
                )));
            }
            blocks.push(self.spec_block(module.then(|| name.to_string()))?);
        }
        self.want(Kind::RBrace)?;
        Ok((Self::named_at(span, name), blocks))
    }

    /// One clause of a spec block, and the `;` that ends it.
    fn clause(&mut self, for_fn: bool) -> Result<Clause, Error> {
        let span = self.at();
        let word = match self.kind() {
            Kind::Const => "const",
            Kind::Raises => "raises",
            Kind::Ident => match self.slice() {
                "invariant" => "invariant",
                "panics" => "panics",
                "ensures" => "ensures",
                _ => "",
            },
            _ => "",
        };
        if word.is_empty() {
            return Err(self.err(if for_fn {
                format!(
                    "expected `const`, `raises`, `panics`, or `ensures`, found {}",
                    self.found()
                )
            } else {
                format!("expected `invariant`, found {}", self.found())
            }));
        }
        if for_fn && word == "invariant" {
            return Err(self.err("an invariant describes the contract; write it in `spec is`"));
        }
        if !for_fn && word != "invariant" {
            return Err(self.err(format!(
                "`{word}` describes a function; write it in `spec for f`"
            )));
        }
        self.bump();
        let kind = match word {
            "invariant" => {
                let name = self.ident()?;
                self.want(Kind::Is)?;
                ClauseKind::Invariant(name)
            }
            "const" => {
                let name = self.ident()?;
                self.want(Kind::Colon)?;
                let ty = self.ty()?;
                self.want(Kind::Assign)?;
                ClauseKind::Const { name, ty }
            }
            "raises" => {
                let espan = self.at();
                let name = self.ident_sym()?;
                self.want_word("when")?;
                ClauseKind::Raises(Self::named_at(espan, name))
            }
            "panics" => {
                self.want_word("when")?;
                ClauseKind::Panics
            }
            _ => ClauseKind::Ensures,
        };
        let start = self.toks[self.i].start;
        let expr = self.expr()?;
        let text = self.src[start..self.toks[self.i - 1].end]
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        self.want(Kind::Semi)?;
        Ok(Clause {
            span,
            kind,
            expr,
            text,
        })
    }

    /// A word that is a keyword only here, such as `when` in a spec clause.
    fn want_word(&mut self, word: &str) -> Result<(), Error> {
        if self.kind() == Kind::Ident && self.slice() == word {
            self.bump();
            Ok(())
        } else {
            Err(self.err(format!("expected `{word}`, found {}", self.found())))
        }
    }

    /// `old.path`, `new.path`, `sum(m)`, `count(m)`, and `forall x : T . e`, inside a spec
    /// block. `None` when the identifier ahead starts none of them.
    fn spec_form(&mut self) -> Result<Option<Expr>, Error> {
        let span = self.at();
        let names = self.names.clone();
        let table = names.clone();
        let call = move |name: &str, builtin: Builtin, args: Vec<Expr>| Expr::Call {
            span,
            name: table.intern(name),
            args,
            base: None,
            callee: None,
            builtin: Some(builtin),
            iface: None,
            method: None,
            ty: 0,
        };
        let word = self.slice().to_string();
        match word.as_str() {
            "old" | "new" if self.peek_kind(1) == Kind::LParen => Err(self.err(format!(
                "`{word}.` starts a path, such as `{word}.storage.x`"
            ))),
            "old" | "new" if self.peek_kind(1) == Kind::Dot => {
                self.bump();
                self.bump();
                if self.kind() != Kind::Ident {
                    return Err(self.err(format!(
                        "expected what `{word}.` reads, such as `{word}.storage.x`, found {}",
                        self.found()
                    )));
                }
                let state = if word == "old" {
                    State::Old
                } else {
                    State::New
                };
                let path = self.primary()?;
                Ok(Some(call(&word, Builtin::SpecState(state), vec![path])))
            }
            "sum" | "count" if self.peek_kind(1) == Kind::LParen => {
                self.bump();
                self.bump();
                let args = self.args()?;
                let builtin = if word == "sum" {
                    Builtin::SpecSum
                } else {
                    Builtin::SpecCount
                };
                Ok(Some(call(&word, builtin, args)))
            }
            "forall" if self.peek_kind(1) == Kind::Ident && self.peek_kind(2) == Kind::Colon => {
                self.bump();
                let bspan = self.at();
                let name = self.ident()?;
                self.want(Kind::Colon)?;
                let tspan = self.at();
                let ty = self.ident()?;
                self.want(Kind::Dot)?;
                let body = self.expr()?;
                let ident = |span: Span, name: String| Expr::Ident {
                    span,
                    name: names.intern(&name),
                    sym: None,
                    builtin: None,
                    ty: 0,
                };
                Ok(Some(call(
                    "forall",
                    Builtin::SpecForall,
                    vec![ident(bspan, name), ident(tspan, ty), body],
                )))
            }
            _ => Ok(None),
        }
    }

    fn storage_decl(&mut self) -> Result<StorageItem, Error> {
        let span = self.at();
        self.bump();
        let unnamed = self.kind() == Kind::Is
            || (self.kind() == Kind::AtKw && self.peek_kind(1) == Kind::String);
        if unnamed {
            let mut id = String::new();
            if self.kind() == Kind::AtKw {
                self.bump();
                id = self.tok().string.clone().unwrap_or_default();
                self.bump();
            }
            self.want(Kind::Is)?;
            let ty = self.ty()?;
            let decl = TypeDecl {
                span,
                private: false,
                file: FileId::default(),
                name: "storage".to_string(),
                ty,
            };
            return Ok(StorageItem::Default(decl, id));
        }
        let name = format!("storage.{}", self.ident()?);
        self.want(Kind::AtKw)?;
        if self.kind() != Kind::String {
            return Err(self.err("storage domain expects a string id"));
        }
        let id = self.tok().string.clone().unwrap_or_default();
        self.bump();
        self.want(Kind::Is)?;
        let ty = self.ty()?;
        Ok(StorageItem::Named(DomainDecl {
            span,
            file: FileId::default(),
            name,
            id,
            ty,
            owner: None,
            transient: false,
            immutable: false,
        }))
    }

    /// `transient storage name is record { ... }`, reached as `transient.name`, or `transient
    /// storage is ...`, reached as `transient`. Transient storage has no id: it never outlives
    /// the transaction.
    fn transient_decl(&mut self) -> Result<DomainDecl, Error> {
        let span = self.at();
        self.bump();
        if self.kind() != Kind::Ident || self.slice() != "storage" {
            return Err(self.err(format!("expected `storage`, found {}", self.found())));
        }
        self.bump();
        let name = if self.kind() == Kind::Is {
            "transient".to_string()
        } else {
            format!("transient.{}", self.ident()?)
        };
        self.want(Kind::Is)?;
        let ty = self.ty()?;
        Ok(DomainDecl {
            span,
            file: FileId::default(),
            name,
            id: String::new(),
            ty,
            owner: None,
            transient: true,
            immutable: false,
        })
    }

    /// `immutable name at "id" is record { ... }`, reached as `immutable.name`, or `immutable
    /// [at "id"] is ...`, reached as `immutable`. A contract's has the id `lithe.immutable`
    /// when it names none.
    fn immutable_decl(&mut self) -> Result<DomainDecl, Error> {
        let span = self.at();
        self.bump();
        let (name, id) = if self.kind() == Kind::Is {
            ("immutable".to_string(), String::new())
        } else if self.kind() == Kind::AtKw && self.peek_kind(1) == Kind::String {
            self.bump();
            let id = self.tok().string.clone().unwrap_or_default();
            self.bump();
            ("immutable".to_string(), id)
        } else {
            let name = format!("immutable.{}", self.ident()?);
            self.want(Kind::AtKw)?;
            if self.kind() != Kind::String {
                return Err(self.err("immutables expect a string id"));
            }
            let id = self.tok().string.clone().unwrap_or_default();
            self.bump();
            (name, id)
        };
        self.want(Kind::Is)?;
        let ty = self.ty()?;
        Ok(DomainDecl {
            span,
            file: FileId::default(),
            name,
            id,
            ty,
            owner: None,
            transient: false,
            immutable: true,
        })
    }

    fn guard_decl(&mut self) -> Result<GuardDecl, Error> {
        let span = self.at();
        self.want(Kind::Upgrade)?;
        if self.kind() != Kind::Ident || self.slice() != "guard" {
            return Err(self.err("expected `guard`"));
        }
        self.bump();
        self.want(Kind::Is)?;
        if self.kind() == Kind::LBrace {
            let stmts = self.block()?;
            return Ok(GuardDecl {
                span,
                stmts,
                via: None,
            });
        }
        let (stmts, via) = self.guard_via()?;
        Ok(GuardDecl {
            span,
            stmts,
            via: Some(via),
        })
    }

    fn type_decl(&mut self) -> Result<TypeDecl, Error> {
        let span = self.at();
        self.want(Kind::Type)?;
        let name = self.ident()?;
        if name == "storage" {
            return Err(self.err("declare contract storage as `storage is record`"));
        }
        self.want(Kind::Is)?;
        // `Open | Closed` or `Open of uint`: a variant without its opening `|`.
        let ty = if self.kind() == Kind::Ident && matches!(self.peek_kind(1), Kind::Pipe | Kind::Of)
        {
            self.variant_ty()?
        } else {
            self.ty()?
        };
        Ok(TypeDecl {
            span,
            private: false,
            file: FileId::default(),
            name,
            ty,
        })
    }

    fn error_decl(&mut self) -> Result<ErrorDecl, Error> {
        let span = self.at();
        self.want(Kind::ErrorKw)?;
        let name = self.ident()?;
        let payload = if self.kind() == Kind::Of {
            self.bump();
            Some(self.ty()?)
        } else {
            None
        };
        Ok(ErrorDecl {
            span,
            private: false,
            file: FileId::default(),
            name,
            payload,
        })
    }

    fn error_set_decl(&mut self) -> Result<ErrorSetDecl, Error> {
        let span = self.at();
        self.want(Kind::ErrorsKw)?;
        let name = self.ident()?;
        self.want(Kind::Is)?;
        if self.kind() == Kind::Pipe {
            self.bump();
        }
        let mut members = Vec::new();
        if self.kind() != Kind::Ident {
            return Err(self.err("error set needs a member"));
        }
        loop {
            let mspan = self.at();
            let name = self.dotted_at(mspan)?;
            members.push(name);
            if self.kind() == Kind::Pipe {
                self.bump();
                continue;
            }
            break;
        }
        Ok(ErrorSetDecl {
            span,
            file: FileId::default(),
            name,
            members,
        })
    }

    fn event_decl(&mut self) -> Result<EventDecl, Error> {
        let span = self.at();
        let anonymous = self.kind() == Kind::Anonymous;
        if anonymous {
            self.bump();
        }
        self.want(Kind::Event)?;
        let name = self.ident()?;
        self.want(Kind::Of)?;
        let ty = self.record_ty(true)?;
        let TypeRef::Record { fields, .. } = ty else {
            return Err(error(span, "event must be a record"));
        };
        Ok(EventDecl {
            span,
            private: false,
            anonymous,
            file: FileId::default(),
            name,
            fields,
        })
    }

    fn interface_decl(&mut self) -> Result<InterfaceDecl, Error> {
        let span = self.at();
        self.want(Kind::Interface)?;
        let name = self.ident()?;
        self.want(Kind::Is)?;
        let methods = self.interface_body()?;
        if methods.is_empty() {
            return Err(error(span, "interface needs a method"));
        }
        Ok(InterfaceDecl {
            span,
            file: FileId::default(),
            name,
            methods,
        })
    }

    /// `{ view function f(a : T) : R raises E; ... }`: external function headers, with no
    /// bodies, for an `interface` or inline in `use M exposing`.
    fn interface_body(&mut self) -> Result<Vec<Func>, Error> {
        self.want(Kind::LBrace)?;
        let mut methods = Vec::new();
        self.declaring = true;
        let result = (|| {
            while self.kind() != Kind::RBrace && self.kind() != Kind::Eof {
                if self.kind() == Kind::Semi {
                    self.bump();
                    continue;
                }
                if !matches!(
                    self.kind(),
                    Kind::External
                        | Kind::Payable
                        | Kind::Nonreentrant
                        | Kind::View
                        | Kind::Pure
                        | Kind::Function
                ) {
                    return Err(self.err(format!(
                        "an interface declares functions, found {}",
                        self.found()
                    )));
                }
                let deco = self.header()?;
                methods.push(self.item(deco, false)?);
            }
            self.want(Kind::RBrace)
        })();
        self.declaring = false;
        result?;
        Ok(methods)
    }

    fn ty(&mut self) -> Result<TypeRef, Error> {
        let span = self.at();
        match self.kind() {
            Kind::List => self.list_ty(span),
            Kind::LParen => self.tuple_ty(span),
            Kind::Record => self.record_ty(false),
            Kind::Ident if self.at_flat() => Err(self.err(FLAT_ONLY)),
            Kind::Pipe => self.variant_ty(),
            Kind::Ident => {
                let name = self.ident_sym()?;
                if self.kind() == Kind::LParen {
                    return self.generic(name.as_str(), span);
                }
                if self.kind() == Kind::Dot {
                    self.bump();
                    let rest = self.ident_sym()?;
                    let qualified = format!("{name}.{rest}");
                    if self.kind() == Kind::LParen {
                        return self.generic(&qualified, span);
                    }
                    return Ok(TypeRef::Name {
                        span,
                        name: self.sym(&qualified),
                    });
                }
                Ok(TypeRef::Name { span, name })
            }
            Kind::Unit => Err(self.err("expected type `unit`, found value `Unit`")),
            _ => Err(self.err(format!("expected a type, found {}", self.found()))),
        }
    }

    /// `flat` before a type: a contextual word, as no type is named `flat`.
    fn at_flat(&self) -> bool {
        self.kind() == Kind::Ident
            && self.lexeme() == "flat"
            && matches!(
                self.peek_kind(1),
                Kind::Ident | Kind::Record | Kind::List | Kind::LParen | Kind::Pipe
            )
    }

    fn flat(&mut self) -> bool {
        let flat = self.at_flat();
        if flat {
            self.bump();
        }
        flat
    }

    fn generic(&mut self, name: &str, span: Span) -> Result<TypeRef, Error> {
        match name {
            "option" => self.one_arg(|elem| TypeRef::Option {
                span,
                elem: Box::new(elem),
            }),
            "map" => {
                self.want(Kind::LParen)?;
                let key = self.ty()?;
                self.want(Kind::Comma)?;
                let val = self.ty()?;
                self.want(Kind::RParen)?;
                Ok(TypeRef::Map {
                    span,
                    key: Box::new(key),
                    val: Box::new(val),
                })
            }
            _ => {
                self.want(Kind::LParen)?;
                let mut args = vec![self.ty()?];
                while self.kind() == Kind::Comma {
                    self.bump();
                    if self.kind() == Kind::RParen {
                        break;
                    }
                    args.push(self.ty()?);
                }
                self.want(Kind::RParen)?;
                let member = if self.kind() == Kind::Dot {
                    self.bump();
                    Some(self.ident()?)
                } else {
                    None
                };
                Ok(TypeRef::Apply {
                    span,
                    name: name.to_string(),
                    args,
                    member,
                })
            }
        }
    }

    fn tuple_ty(&mut self, span: Span) -> Result<TypeRef, Error> {
        self.want(Kind::LParen)?;
        let mut elems = vec![self.ty()?];
        if self.kind() != Kind::Comma {
            return Err(self.err("a tuple needs at least two elements"));
        }
        while self.kind() == Kind::Comma {
            self.bump();
            elems.push(self.ty()?);
        }
        self.want(Kind::RParen)?;
        Ok(TypeRef::Tuple { span, elems })
    }

    fn one_arg(&mut self, make: impl FnOnce(TypeRef) -> TypeRef) -> Result<TypeRef, Error> {
        self.want(Kind::LParen)?;
        let elem = self.ty()?;
        self.want(Kind::RParen)?;
        Ok(make(elem))
    }

    fn list_ty(&mut self, span: Span) -> Result<TypeRef, Error> {
        self.bump();
        self.want(Kind::LParen)?;
        let elem = self.ty()?;
        let (mut len, mut size) = (None, None);
        if self.kind() == Kind::Comma {
            self.bump();
            if self.kind() == Kind::Int && self.peek_kind(1) == Kind::RParen {
                let span = self.at();
                len = Some(list_len(self.tok().word, span)?);
                self.bump();
            } else {
                size = Some(Box::new(self.expr()?));
            }
        }
        self.want(Kind::RParen)?;
        Ok(TypeRef::List {
            span,
            elem: Box::new(elem),
            len,
            size,
        })
    }

    fn record_ty(&mut self, event: bool) -> Result<TypeRef, Error> {
        let span = self.at();
        self.want(Kind::Record)?;
        self.want(Kind::LBrace)?;
        let mut fields = Vec::new();
        while self.kind() != Kind::RBrace && self.kind() != Kind::Eof {
            if self.kind() == Kind::Semi {
                self.bump();
                continue;
            }
            let indexed = if self.kind() == Kind::Indexed {
                if !event {
                    return Err(self.err("`indexed` is only valid on an event field"));
                }
                self.bump();
                true
            } else {
                false
            };
            let fspan = self.at();
            let name = self.ident()?;
            self.want(Kind::Colon)?;
            let ty = self.ty()?;
            if self.kind() == Kind::Indexed {
                return Err(self.err("write `indexed` before the field name"));
            }
            fields.push(FieldRef {
                span: fspan,
                name,
                ty,
                indexed,
            });
            if self.kind() == Kind::Semi {
                self.bump();
            }
        }
        self.want(Kind::RBrace)?;
        Ok(TypeRef::Record { span, fields })
    }

    fn variant_ty(&mut self) -> Result<TypeRef, Error> {
        let span = self.at();
        let mut variants = Vec::new();
        if self.kind() == Kind::Pipe {
            self.bump();
        }
        loop {
            let vspan = self.at();
            let name = self.ident()?;
            let external = if self.kind() == Kind::External && self.peek_kind(1) == Kind::Ident {
                self.bump();
                Some(self.ident()?)
            } else {
                None
            };
            let mut param = String::new();
            let mut flat = false;
            let payload = if self.kind() == Kind::Of {
                self.bump();
                if self.kind() == Kind::LParen
                    && self.peek_kind(1) == Kind::Ident
                    && self.peek_kind(2) == Kind::Colon
                {
                    self.bump();
                    param = self.ident()?;
                    self.want(Kind::Colon)?;
                    if self.at_flat() {
                        return Err(self.err(
                            "a `flat` payload's fields name its ABI parameters; write `of flat T`",
                        ));
                    }
                    let ty = self.ty()?;
                    self.want(Kind::RParen)?;
                    Some(ty)
                } else {
                    flat = self.flat();
                    Some(self.ty()?)
                }
            } else {
                None
            };
            variants.push(VariantRef {
                span: vspan,
                name,
                payload,
                param,
                external,
                flat,
            });
            if self.kind() != Kind::Pipe {
                break;
            }
            self.bump();
        }
        Ok(TypeRef::Variant { span, variants })
    }

    fn use_decl(&mut self) -> Result<UseDecl, Error> {
        let span = self.at();
        self.want(Kind::Import)?;
        if self.kind() != Kind::String {
            return Err(self.err("`import` expects a path string"));
        }
        let path = self.tok().string.clone().unwrap_or_default();
        if !module_path(&path) {
            return Err(self.err(format!(
                "invalid import path `{path}`\n\nan import names a module: `std/`, `./`, `../`, or a package name and `/`, then `/`-separated names of lowercase letters, digits, and `_`, as in `std/token/erc20`, `./lib/fees`, or `tokens/erc20`"
            )));
        }
        self.bump();
        let alias = if self.kind() == Kind::As {
            self.bump();
            Some(self.ident()?)
        } else {
            None
        };
        if self.kind() == Kind::Semi {
            self.bump();
        }
        Ok(UseDecl { span, path, alias })
    }

    /// `[external [payable] [nonreentrant]] [view | pure] function`, in that order.
    fn header(&mut self) -> Result<Deco, Error> {
        // Each keyword's place in the fixed order: visibility, payability, reentrancy, effect.
        let mut seen: Vec<(u8, Kind)> = Vec::new();
        loop {
            let rank = match self.kind() {
                Kind::External => 0,
                Kind::Payable => 1,
                Kind::Nonreentrant => 2,
                Kind::View | Kind::Pure => 3,
                _ => break,
            };
            if seen.iter().any(|&(r, _)| r == rank) {
                return Err(self.err(format!("{} is already set", self.found())));
            }
            if rank == 0 && self.declaring {
                return Err(self.err("an interface's methods are external; drop `external`"));
            }
            if rank == 2 && self.declaring {
                return Err(self.err(
                    "`nonreentrant` is not part of an interface; it belongs to the function's definition",
                ));
            }
            seen.push((rank, self.kind()));
            self.bump();
            if rank == 2 && self.kind() == Kind::LParen {
                return Err(self.err("named nonreentrant domains are not supported"));
            }
        }
        let has = |k: Kind| seen.iter().any(|&(_, have)| have == k);
        let (external, payable) = (has(Kind::External) || self.declaring, has(Kind::Payable));
        if self.kind() == Kind::Deploy {
            if seen.iter().any(|&(_, k)| k != Kind::Payable) {
                return Err(self.err("`deploy` takes only `payable`"));
            }
            return Ok(Deco {
                payable,
                ..Deco::of(ItemKind::Deploy)
            });
        }
        let nonreentrant = has(Kind::Nonreentrant);
        if self.special_ahead() {
            let word = self.slice().to_string();
            if self.declaring {
                return Err(self.err(format!(
                    "`{word}` belongs to the contract, not an interface"
                )));
            }
            if seen
                .iter()
                .any(|&(_, k)| !matches!(k, Kind::Payable | Kind::Nonreentrant))
            {
                return Err(self.err(format!("`{word}` takes only `payable` and `nonreentrant`")));
            }
            if seen.windows(2).any(|w| w[0].0 > w[1].0) {
                return Err(self.err(format!(
                    "keywords out of order; write `payable nonreentrant {word}`"
                )));
            }
            let kind = if word == "receive" {
                if !payable {
                    return Err(self.err("`receive` accepts ether; write `payable receive`"));
                }
                ItemKind::Receive
            } else {
                ItemKind::Fallback
            };
            return Ok(Deco {
                kind,
                payable,
                nonreentrant,
                external_pure: false,
            });
        }
        let effect = seen.iter().find(|&&(r, _)| r == 3).map(|&(_, k)| k);
        if nonreentrant && !external {
            return Err(self.err(
                "nonreentrant functions must be external; write `external nonreentrant function`",
            ));
        }
        if seen.windows(2).any(|w| w[0].0 > w[1].0) {
            let mut words: Vec<&str> = Vec::new();
            if external && !self.declaring {
                words.push("external");
            }
            if payable {
                words.push("payable");
            }
            if nonreentrant {
                words.push("nonreentrant");
            }
            match effect {
                Some(Kind::View) => words.push("view"),
                Some(Kind::Pure) => words.push("pure"),
                _ => {}
            }
            words.push("function");
            return Err(self.err(format!(
                "keywords out of order; write `{}`",
                words.join(" ")
            )));
        }
        if payable && !external {
            return Err(
                self.err("payable functions must be external; write `external payable function`")
            );
        }
        if payable && effect.is_some() {
            return Err(self.err("payable functions must be stateful"));
        }
        if nonreentrant && effect == Some(Kind::Pure) {
            return Err(self.err("a pure function reads no state, so it cannot be nonreentrant"));
        }
        if self.kind() != Kind::Function {
            return Err(self.err(format!("expected `function`, found {}", self.found())));
        }
        let kind = match (external, effect) {
            (true, None) => ItemKind::Entry,
            (true, Some(_)) => ItemKind::View,
            (false, None) => ItemKind::Function,
            (false, Some(Kind::View)) => ItemKind::Readonly,
            (false, Some(_)) => ItemKind::Pure,
        };
        Ok(Deco {
            kind,
            payable,
            nonreentrant,
            external_pure: external && effect == Some(Kind::Pure),
        })
    }

    fn item(&mut self, deco: Deco, private: bool) -> Result<Func, Error> {
        let Deco {
            kind,
            payable,
            nonreentrant,
            external_pure,
        } = deco;
        let span = self.at();
        self.bump();
        if let Some(word) = special_word(kind) {
            return self.special_item(span, kind, word, payable, nonreentrant);
        }
        let name = if kind == ItemKind::Deploy {
            "deploy".to_string()
        } else {
            self.member_name()?
        };
        // An interface's `f(a : T)` has parameters, never type parameters.
        let type_params = if !self.declaring && self.looks_like_type_params() {
            self.type_param_list()?
        } else {
            Vec::new()
        };
        let params = self.params()?;
        if !matches!(
            kind,
            ItemKind::Function | ItemKind::Readonly | ItemKind::Pure
        ) {
            if let Some(p) = params.iter().find(|p| p.storage) {
                return Err(error(
                    p.span,
                    format!(
                        "`{}` is called from outside, so its parameters are values: take `{}` as `const` or `var`",
                        name, p.name
                    ),
                ));
            }
        }
        let mut ret_flat = false;
        let ret = match kind {
            ItemKind::View => {
                if self.kind() != Kind::Colon {
                    let what = match (self.declaring, external_pure) {
                        (true, true) => "a `pure` method",
                        (true, false) => "a `view` method",
                        (false, true) => "an `external pure` function",
                        (false, false) => "an `external view` function",
                    };
                    return Err(self.err(format!(
                        "{what} must return a value: return a `bool` the caller can check, and let the caller fail"
                    )));
                }
                self.bump();
                ret_flat = self.flat();
                Some(self.ty()?)
            }
            ItemKind::Function | ItemKind::Readonly | ItemKind::Pure
                if self.kind() == Kind::Colon =>
            {
                self.bump();
                ret_flat = self.flat();
                Some(self.ty()?)
            }
            ItemKind::Function | ItemKind::Readonly | ItemKind::Pure => None,
            // An entry may return a value to its caller, after its effects have run.
            ItemKind::Entry if self.kind() == Kind::Colon => {
                self.bump();
                ret_flat = self.flat();
                Some(self.ty()?)
            }
            ItemKind::Entry => None,
            ItemKind::Migrate => {
                if self.kind() == Kind::Colon {
                    return Err(self.err("a migration does not declare a return type"));
                }
                None
            }
            ItemKind::Deploy => {
                if self.kind() == Kind::Colon {
                    return Err(self.err("`deploy` does not declare a return type"));
                }
                None
            }
            ItemKind::Receive | ItemKind::Fallback => None,
        };
        let guarded = if self.kind() == Kind::Ident && self.slice() == "guarded" {
            if self.declaring {
                return Err(self.err(
                    "an interface doesn't say how an external is guarded; `guarded` goes on the module's external",
                ));
            }
            if !matches!(kind, ItemKind::Entry | ItemKind::View) {
                return Err(self.err("only an external function can be guarded"));
            }
            Some(self.guarded()?)
        } else {
            None
        };
        let raises = if self.kind() == Kind::Raises {
            Some(self.raises_clause()?)
        } else {
            None
        };
        let (stmts, tail) = if self.declaring {
            if self.kind() == Kind::Is {
                return Err(self.err(
                    "an interface's methods have no body; to wrap a module's function, write an external of the contract's own",
                ));
            }
            self.want(Kind::Semi)?;
            (Vec::new(), None)
        } else {
            self.want(Kind::Is)?;
            self.item_body()?
        };
        Ok(Func {
            span,
            kind,
            private,
            file: FileId::default(),
            name,
            type_params,
            params,
            ret,
            ret_flat,
            ret_ty: 0,
            payable,
            nonreentrant,
            external_pure,
            raises,
            errors: Vec::new(),
            stmts,
            tail,
            module: None,
            requires: Vec::new(),
            promoted: None,
            declares: None,
            interface: None,
            exported: None,
            forward: None,
            guarded,
            guard_of: None,
            constant: false,
            hook_of: None,
        })
    }

    /// `const name : T := e;` outside a function: a named value known when the contract
    /// compiles.
    fn const_decl(&mut self, private: bool) -> Result<Func, Error> {
        let span = self.at();
        self.want(Kind::Const)?;
        let name = self.ident()?;
        if self.kind() != Kind::Colon {
            return Err(self.err("a constant needs a type: `const name : T := value`"));
        }
        let ty = self.binding_ty()?;
        self.want(Kind::Assign)?;
        let mut func = guard_func(span, name, Vec::new());
        func.kind = ItemKind::Pure;
        func.private = private;
        func.ret = Some(ty);
        func.tail = Some(self.expr()?);
        func.constant = true;
        Ok(func)
    }

    /// `guarded editor(id)` on a module's external: its guard, and the parameters it takes.
    fn guarded(&mut self) -> Result<Guarded, Error> {
        self.bump();
        let span = self.at();
        let name = self.ident()?;
        let mut args = Vec::new();
        if self.kind() == Kind::LParen {
            self.bump();
            while self.kind() != Kind::RParen {
                let aspan = self.at();
                if self.kind() != Kind::Ident || self.peek_kind(1) == Kind::Dot {
                    return Err(self.err(format!(
                        "a guard takes the external's parameters, by name; found {}",
                        self.found()
                    )));
                }
                let name = self.ident_sym()?;
                args.push(Self::named_at(aspan, name));
                if self.kind() != Kind::Comma {
                    break;
                }
                self.bump();
            }
            if self.kind() != Kind::RParen {
                return Err(self.err(format!(
                    "a guard takes the external's parameters, by name; found {}",
                    self.found()
                )));
            }
            self.bump();
        }
        Ok(Guarded { span, name, args })
    }

    /// `guard editor(const id : uint);` in a module: a guard's name and parameters.
    fn guard_sig(&mut self) -> Result<Func, Error> {
        self.bump();
        let span = self.at();
        let name = self.ident()?;
        let params = if self.kind() == Kind::LParen {
            self.params()?
        } else {
            Vec::new()
        };
        if self.kind() == Kind::Is {
            return Err(self.err(
                "a module's guard has no body: each contract that exposes its externals writes the check",
            ));
        }
        self.want(Kind::Semi)?;
        Ok(guard_func(span, name, params))
    }

    /// `with { ... }` after `use M ...`: the contract's checks for `M`'s guards and its
    /// implementations of `M`'s hooks, by their names in `M`.
    fn use_with(&mut self, module: &str, body: &mut Body) -> Result<(), Error> {
        self.bump();
        self.want(Kind::LBrace)?;
        while self.kind() != Kind::RBrace && self.kind() != Kind::Eof {
            if self.kind() == Kind::Semi {
                self.bump();
                continue;
            }
            if matches!(self.kind(), Kind::View | Kind::Pure) && self.hook_ahead() {
                return Err(self.err(
                    "a contract implements a hook without restating its effect: write `hook h ...`; the module's declaration says what it may do",
                ));
            }
            if self.kind() != Kind::Ident || !matches!(self.slice(), "guard" | "hook") {
                return Err(self.err(format!(
                    "`use ... with` binds the module's guards and hooks: expected `guard` or `hook`, found {}",
                    self.found()
                )));
            }
            let word = self.slice().to_string();
            self.bump();
            if self.kind() == Kind::Ident && self.peek_kind(1) == Kind::Dot {
                let span = self.at();
                let path = self.dotted()?;
                let name = path.rsplit('.').next().unwrap_or(&path);
                return Err(error(
                    span,
                    format!(
                        "inside `use {} ... with`, a {word} is named bare: write `{word} {name}`",
                        crate::modules::shown(module)
                    ),
                ));
            }
            if word == "guard" {
                body.guards.push(self.guard_impl(module)?);
            } else {
                body.hooks.push(self.hook_impl(module)?);
            }
        }
        self.want(Kind::RBrace)?;
        Ok(())
    }

    /// `guard editor(const id : uint) raises E is { ... }`, or `guard editor is f;`, in
    /// `use M ... with { ... }`: the contract's check for `M`'s guard.
    fn guard_impl(&mut self, module: &str) -> Result<Func, Error> {
        let span = self.at();
        let name = &self.ident()?;
        let params = if self.kind() == Kind::LParen {
            self.params()?
        } else {
            Vec::new()
        };
        let raises = if self.kind() == Kind::Raises {
            Some(self.raises_clause()?)
        } else {
            None
        };
        self.want(Kind::Is)?;
        let mut func = guard_func(span, name.to_string(), params);
        let mut via = None;
        if self.kind() == Kind::LBrace {
            func.stmts = self.block()?;
        } else {
            if raises.is_some() {
                return Err(self.err(
                    "a guard that names a function raises what the function does; drop `raises`",
                ));
            }
            let (stmts, named) = self.guard_via()?;
            func.stmts = stmts;
            via = Some(named);
        }
        func.raises = raises;
        func.guard_of = Some(GuardOf {
            module: self.name_at(span, module),
            name: name.to_string(),
            via,
        });
        Ok(func)
    }

    /// `hook name`, `view hook name`, or `pure hook name`: a module's hook.
    fn hook_ahead(&self) -> bool {
        let at = usize::from(matches!(self.kind(), Kind::View | Kind::Pure));
        let Some(tok) = self.toks.get(self.i + at) else {
            return false;
        };
        tok.kind == Kind::Ident
            && &self.src[tok.start..tok.end] == "hook"
            && self.peek_kind(at + 1) == Kind::Ident
    }

    /// `[view | pure] hook name(params) [: T];` in a module: a hook's header. Its effect is
    /// the most the contract's implementation may do.
    fn hook_sig(&mut self) -> Result<Func, Error> {
        let kind = match self.kind() {
            Kind::View => ItemKind::Readonly,
            Kind::Pure => ItemKind::Pure,
            _ => ItemKind::Function,
        };
        if kind != ItemKind::Function {
            self.bump();
        }
        self.bump();
        let span = self.at();
        let name = self.ident()?;
        let params = if self.kind() == Kind::LParen {
            self.params()?
        } else {
            Vec::new()
        };
        let ret = if self.kind() == Kind::Colon {
            self.bump();
            Some(self.ty()?)
        } else {
            None
        };
        if self.kind() == Kind::Raises {
            return Err(self.err(
                "a module's hook declares no errors: the contract's implementation raises its own, and they join those of the externals that reach it",
            ));
        }
        if self.kind() == Kind::Is {
            return Err(self.err(
                "a module's hook has no body: each contract that uses the module implements it",
            ));
        }
        self.want(Kind::Semi)?;
        let mut func = guard_func(span, name, params);
        func.kind = kind;
        func.ret = ret;
        Ok(func)
    }

    /// `hook h(params) [: T] [raises E] is { ... } [with e]`, `hook h is f;`, or
    /// `hook h is skip;`, in `use M ... with { ... }`: the contract's implementation of `M`'s
    /// hook.
    fn hook_impl(&mut self, module: &str) -> Result<Func, Error> {
        let span = self.at();
        let name = &self.ident()?;
        let params = if self.kind() == Kind::LParen {
            self.params()?
        } else {
            Vec::new()
        };
        let ret = if self.kind() == Kind::Colon {
            self.bump();
            Some(self.ty()?)
        } else {
            None
        };
        let raises = if self.kind() == Kind::Raises {
            Some(self.raises_clause()?)
        } else {
            None
        };
        self.want(Kind::Is)?;
        let mut func = guard_func(span, name.to_string(), params);
        func.ret = ret;
        let form = if self.kind() == Kind::LBrace {
            let (stmts, tail) = self.item_body()?;
            func.stmts = stmts;
            func.tail = tail;
            HookForm::Body
        } else if self.kind() == Kind::SkipKw {
            if raises.is_some() {
                return Err(
                    self.err("a skipped hook runs nothing, so it raises nothing; drop `raises`")
                );
            }
            self.bump();
            self.want(Kind::Semi)?;
            HookForm::Skip
        } else {
            if raises.is_some() {
                return Err(self.err(
                    "a hook that names a function raises what the function does; drop `raises`",
                ));
            }
            let (stmts, named) = self.guard_via()?;
            func.stmts = stmts;
            HookForm::Via(named)
        };
        func.raises = raises;
        func.hook_of = Some(HookOf {
            module: self.name_at(span, module),
            name: name.to_string(),
            form,
        });
        Ok(func)
    }

    /// `is f;` after a guard: a body that calls `f`, and where `f` is named.
    fn guard_via(&mut self) -> Result<(Vec<Stmt>, NameAt), Error> {
        let vspan = self.at();
        let path = self.dotted()?;
        let mut pieces: Vec<&str> = path.split('.').collect();
        let last = pieces.pop().unwrap_or_default().to_string();
        let base = pieces.iter().fold(None, |base, piece| {
            Some(match base {
                None => Expr::Ident {
                    span: vspan,
                    name: self.sym(piece),
                    sym: None,
                    builtin: None,
                    ty: 0,
                },
                Some(base) => Expr::Field {
                    span: vspan,
                    base: Box::new(base),
                    name: self.sym(piece),
                    root: None,
                    leaf: 0,
                    ty: 0,
                },
            })
        });
        let stmts = vec![Stmt::Call {
            span: vspan,
            expr: self.call(vspan, self.sym(&last), Vec::new(), base),
        }];
        self.want(Kind::Semi)?;
        Ok((
            stmts,
            NameAt {
                span: vspan,
                name: self.sym(&path),
            },
        ))
    }

    /// `(const a : T; var b : U)`, or an interface's `(a : T; b : U)`.
    fn params(&mut self) -> Result<Vec<Param>, Error> {
        self.want(Kind::LParen)?;
        let mut params = Vec::new();
        if self.kind() != Kind::RParen {
            loop {
                let pspan = self.at();
                let storage_mode = self.kind() == Kind::Ident
                    && self.slice() == "storage"
                    && self.peek_kind(1) == Kind::Ident;
                let (mutable, storage) = match self.kind() {
                    // An interface's parameters are values in the ABI: `name : type`.
                    Kind::Var | Kind::Const if self.declaring => {
                        return Err(self.err(format!(
                            "an interface's parameters are `name : type`, without {}",
                            self.found()
                        )));
                    }
                    _ if self.declaring && storage_mode => {
                        return Err(self.err(
                            "an interface's parameters are `name : type`, without `storage`",
                        ));
                    }
                    _ if self.declaring => (false, false),
                    Kind::Var => {
                        self.bump();
                        (true, false)
                    }
                    Kind::Const => {
                        self.bump();
                        (false, false)
                    }
                    _ if storage_mode => {
                        self.bump();
                        (false, true)
                    }
                    _ => {
                        return Err(self.err(format!(
                            "expected `const`, `var`, or `storage`, found {}",
                            self.found()
                        )))
                    }
                };
                let pname = self.ident()?;
                self.want(Kind::Colon)?;
                let flat = self.flat();
                let ty = self.ty()?;
                params.push(Param {
                    span: pspan,
                    mutable,
                    storage,
                    name: pname,
                    flat,
                    ty,
                    ty_id: 0,
                    sym: None,
                });
                if self.kind() == Kind::Semi {
                    self.bump();
                    if self.kind() == Kind::RParen {
                        break;
                    }
                    continue;
                }
                break;
            }
        }
        self.want(Kind::RParen)?;
        Ok(params)
    }

    /// `payable receive [raises E] is ...`, `[payable] fallback [: bytes] [raises E] is ...`,
    /// or `[payable] fallback [raises E] delegates to target;` and `forwards to target;`.
    /// The keyword is already consumed.
    fn special_item(
        &mut self,
        span: Span,
        kind: ItemKind,
        word: &str,
        payable: bool,
        nonreentrant: bool,
    ) -> Result<Func, Error> {
        if self.kind() == Kind::LParen {
            return Err(self.err(if kind == ItemKind::Fallback {
                "`fallback` takes no parameters; read the calldata with `Evm.calldata()`"
                    .to_string()
            } else {
                format!("`{word}` takes no parameters")
            }));
        }
        let ret = if self.kind() == Kind::Colon {
            if kind == ItemKind::Receive {
                return Err(self.err("`receive` does not return a value"));
            }
            self.bump();
            Some(self.ty()?)
        } else {
            None
        };
        let raises = if self.kind() == Kind::Raises {
            Some(self.raises_clause()?)
        } else {
            None
        };
        let forward = match (kind, self.kind(), self.slice()) {
            (ItemKind::Fallback, Kind::Ident, "delegates") => Some(Forward::Delegate),
            (ItemKind::Fallback, Kind::Ident, "forwards") => Some(Forward::Call),
            _ => None,
        };
        let (stmts, tail) = if let Some(how) = forward {
            let verb = if how == Forward::Delegate {
                "delegates"
            } else {
                "forwards"
            };
            if ret.is_some() {
                return Err(self.err(format!(
                    "a `fallback` that {verb} returns what its target returns; drop the result type"
                )));
            }
            if nonreentrant {
                return Err(self.err(format!("a `fallback` that {verb} cannot be nonreentrant")));
            }
            self.bump();
            if self.kind() != Kind::Ident || self.slice() != "to" {
                return Err(self.err(format!(
                    "expected `to` after `{verb}`, found {}",
                    self.found()
                )));
            }
            self.bump();
            let target = self.expr()?;
            self.want(Kind::Semi)?;
            (Vec::new(), Some(target))
        } else {
            if self.kind() != Kind::Is && kind == ItemKind::Fallback {
                return Err(self.err(format!(
                    "expected `is`, `delegates to`, or `forwards to`, found {}",
                    self.found()
                )));
            }
            self.want(Kind::Is)?;
            self.item_body()?
        };
        Ok(Func {
            span,
            kind,
            private: false,
            file: FileId::default(),
            name: word.to_string(),
            type_params: Vec::new(),
            params: Vec::new(),
            ret,
            ret_flat: false,
            ret_ty: 0,
            payable,
            nonreentrant,
            external_pure: false,
            raises,
            errors: Vec::new(),
            stmts,
            tail,
            module: None,
            requires: Vec::new(),
            promoted: None,
            declares: None,
            interface: None,
            exported: None,
            forward,
            guarded: None,
            guard_of: None,
            constant: false,
            hook_of: None,
        })
    }

    /// `receive` or `fallback` where a declaration can start: a contextual keyword.
    fn special_ahead(&self) -> bool {
        self.kind() == Kind::Ident && matches!(self.slice(), "receive" | "fallback")
    }

    fn raises_clause(&mut self) -> Result<Raises, Error> {
        let span = self.at();
        self.want(Kind::Raises)?;
        if self.kind() == Kind::Ident && self.lexeme() == "none" {
            let nspan = self.at();
            self.bump();
            if self.kind() == Kind::Pipe {
                return Err(error(nspan, "`none` cannot be combined with other errors"));
            }
            return Ok(Raises { parts: Vec::new() });
        }
        let mut parts = Vec::new();
        loop {
            let pspan = self.at();
            let name = self.dotted_at(pspan)?;
            if name.name == "none" {
                return Err(error(pspan, "`none` cannot be combined with other errors"));
            }
            parts.push(name);
            if self.kind() == Kind::Pipe {
                self.bump();
                continue;
            }
            break;
        }
        if parts.is_empty() {
            return Err(error(span, "`raises` needs an error"));
        }
        Ok(Raises { parts })
    }

    fn item_body(&mut self) -> Result<(Vec<Stmt>, Option<Expr>), Error> {
        if self.kind() == Kind::LBrace && !self.brace_is_record() {
            let stmts = self.block()?;
            if self.kind() == Kind::With {
                self.bump();
                Ok((stmts, Some(self.expr()?)))
            } else {
                Ok((stmts, None))
            }
        } else {
            Ok((Vec::new(), Some(self.expr()?)))
        }
    }

    fn arm_body(&mut self) -> Result<(Vec<Stmt>, Expr), Error> {
        if self.kind() == Kind::Fail || self.forward_ahead() {
            let span = self.at();
            let reason = self.fail_reason()?;
            return Ok((
                vec![Stmt::Fail { reason }],
                Expr::Lit {
                    span,
                    lit: Lit::Unit,
                    ty: 0,
                },
            ));
        }
        if self.kind() == Kind::LBrace && !self.brace_is_record() {
            let span = self.at();
            let stmts = self.block()?;
            // `{ ... } with e`: the statements, then a value, as a function body ends.
            if self.kind() == Kind::With {
                self.bump();
                return Ok((stmts, self.expr()?));
            }
            Ok((
                stmts,
                Expr::Lit {
                    span,
                    lit: Lit::Unit,
                    ty: 0,
                },
            ))
        } else {
            Ok((Vec::new(), self.expr()?))
        }
    }

    /// `{ name = ... }` is a record. `{ name := ... }` and other statements are blocks.
    fn brace_is_record(&self) -> bool {
        if self.kind() != Kind::LBrace {
            return false;
        }
        let Some(next) = self.toks.get(self.i + 1) else {
            return false;
        };
        if next.kind != Kind::Ident {
            return false;
        }
        self.toks
            .get(self.i + 2)
            .is_some_and(|tok| tok.kind == Kind::Eq)
    }

    fn block(&mut self) -> Result<Vec<Stmt>, Error> {
        self.want(Kind::LBrace)?;
        let mut stmts = Vec::new();
        while self.kind() != Kind::RBrace && self.kind() != Kind::Eof {
            if self.kind() == Kind::Semi {
                self.bump();
                continue;
            }
            let start = self.i;
            match self.stmt() {
                Ok(stmt) => stmts.push(stmt),
                // Report the statement's error and carry on at the next one, so a file shows
                // every broken statement, not only the first. The statements around it are
                // dropped with the program when `parse` returns the first error.
                Err(err) => {
                    self.errors.push(err);
                    self.skip_stmt(start);
                }
            }
        }
        self.want(Kind::RBrace)?;
        Ok(stmts)
    }

    /// Moves past the tokens of the statement that began at `start` to the next `;` or `}` at
    /// the block's level. Scanning from the statement's first token, not from where it failed,
    /// is what makes the bracket depth right: a failure after `Foo {` must still count that `{`.
    /// Every other token is bumped, so a block always makes progress on a broken statement.
    ///
    /// Brackets are counted by kind, because a `}` with only `(`/`[` open above the statement's
    /// own braces is the block's `}`, not a closer: `foo(x;` ends the statement there instead of
    /// consuming the block's `}` and carrying recovery into the next declaration. A closer with
    /// nothing of its kind open saturates at zero rather than underflowing.
    fn skip_stmt(&mut self, start: usize) {
        self.i = start;
        let (mut braces, mut parens, mut brackets) = (0u32, 0u32, 0u32);
        loop {
            match self.kind() {
                Kind::Eof => return,
                Kind::RBrace if braces == 0 => return,
                Kind::Semi if braces == 0 && parens == 0 && brackets == 0 => {
                    self.bump();
                    return;
                }
                Kind::LBrace => braces += 1,
                Kind::LParen => parens += 1,
                Kind::LBrack => brackets += 1,
                Kind::RBrace => braces -= 1,
                Kind::RParen => parens = parens.saturating_sub(1),
                Kind::RBrack => brackets = brackets.saturating_sub(1),
                _ => {}
            }
            self.bump();
        }
    }

    fn stmt(&mut self) -> Result<Stmt, Error> {
        let span = self.at();
        match self.kind() {
            Kind::Const => {
                self.bump();
                let (name, parts) = self.binding_names()?;
                let ty = self.binding_ty()?;
                self.want(Kind::Assign)?;
                let expr = self.expr()?;
                Ok(Stmt::Const {
                    span,
                    name,
                    parts,
                    ty,
                    expr,
                    sym: None,
                    part_syms: Vec::new(),
                })
            }
            Kind::Var => {
                self.bump();
                let (name, parts) = self.binding_names()?;
                let ty = self.binding_ty()?;
                self.want(Kind::Assign)?;
                let expr = self.expr()?;
                Ok(Stmt::Var {
                    span,
                    name,
                    parts,
                    ty,
                    expr,
                    sym: None,
                    part_syms: Vec::new(),
                })
            }
            Kind::If => {
                self.bump();
                let cond = self.expr()?;
                self.want(Kind::Then)?;
                let then_body = self.block()?;
                let else_body = if self.kind() == Kind::Else {
                    self.bump();
                    if self.kind() == Kind::If {
                        vec![self.stmt()?]
                    } else {
                        self.block()?
                    }
                } else {
                    Vec::new()
                };
                Ok(Stmt::If {
                    span,
                    cond,
                    then_body,
                    else_body,
                })
            }
            Kind::Assert => {
                self.bump();
                self.want(Kind::LParen)?;
                let cond = self.expr()?;
                self.want(Kind::Comma)?;
                let reason = self.reason()?;
                self.want(Kind::RParen)?;
                Ok(Stmt::Assert { span, cond, reason })
            }
            Kind::Case => {
                let expr = self.case_expr()?;
                Ok(Stmt::Call { span, expr })
            }
            kind if kind == Kind::Fail || self.forward_ahead() => Ok(Stmt::Fail {
                reason: self.fail_reason()?,
            }),
            Kind::Failwith => Err(self.err("errors must be typed; use `fail`")),
            Kind::SkipKw => {
                self.bump();
                Ok(Stmt::Skip)
            }
            Kind::Emit => self.emit_stmt(span),
            Kind::Defer => self.defer_stmt(span),
            Kind::For => self.for_stmt(span),
            Kind::LParen => self.assign_tuple(span),
            Kind::Ident if self.slice() == "delete" && self.peek_kind(1) == Kind::Ident => {
                self.bump();
                let span = self.at();
                self.assign_or_call(span, true)
            }
            Kind::Ident | Kind::AtKw => self.assign_or_call(span, false),
            _ => Err(self.err(format!("expected a statement, found {}", self.found()))),
        }
    }

    /// `for x : T in xs [until c] [bound n] do { ... }`, or over `lo .. hi`, or with
    /// `(i, x) : (uint, T)` to bind the index too.
    fn for_stmt(&mut self, span: Span) -> Result<Stmt, Error> {
        self.want(Kind::For)?;
        let (index, name) = if self.kind() == Kind::LParen {
            self.bump();
            let index = self.ident()?;
            self.want(Kind::Comma)?;
            let name = self.ident()?;
            self.want(Kind::RParen)?;
            (Some(index), name)
        } else {
            (None, self.ident()?)
        };
        let ty = self.binding_ty()?;
        self.want(Kind::In)?;
        let first = self.expr()?;
        let iter = if self.kind() == Kind::DotDot {
            self.bump();
            let hi = self.expr()?;
            ForIter::Range { lo: first, hi }
        } else {
            ForIter::List(first)
        };
        let until = if self.kind() == Kind::Until {
            self.bump();
            Some(self.expr()?)
        } else {
            None
        };
        let bound = if self.kind() == Kind::Bound {
            self.bump();
            Some(self.expr()?)
        } else {
            None
        };
        let mut invariants = Vec::new();
        while self.kind() == Kind::Ident && self.slice() == "invariant" {
            self.bump();
            let saved = std::mem::replace(&mut self.in_spec, true);
            let e = self.expr();
            self.in_spec = saved;
            invariants.push(e?);
        }
        self.want(Kind::Do)?;
        let body = self.block()?;
        Ok(Stmt::For {
            span,
            index,
            name,
            ty,
            iter,
            until,
            bound,
            body,
            counter: None,
            elem: None,
            limit: None,
            elem_init: None,
            length: None,
            cap: None,
            list: None,
            declared: Vec::new(),
            invariants,
        })
    }

    /// `(a, b) := expr;`
    fn assign_tuple(&mut self, span: Span) -> Result<Stmt, Error> {
        self.want(Kind::LParen)?;
        let mut names = vec![self.ident()?];
        if self.kind() != Kind::Comma {
            return Err(self.err("a tuple assignment needs at least two names"));
        }
        while self.kind() == Kind::Comma {
            self.bump();
            names.push(self.ident()?);
        }
        self.want(Kind::RParen)?;
        self.want(Kind::Assign)?;
        let expr = self.expr()?;
        Ok(Stmt::AssignTuple {
            span,
            names,
            expr,
            syms: Vec::new(),
        })
    }

    /// One name, or the names of a `(a, b)` tuple pattern with an empty name.
    fn binding_names(&mut self) -> Result<(String, Vec<String>), Error> {
        if self.kind() != Kind::LParen {
            return Ok((self.ident()?, Vec::new()));
        }
        self.bump();
        let mut names = vec![self.ident()?];
        if self.kind() != Kind::Comma {
            return Err(self.err("a tuple pattern needs at least two names"));
        }
        while self.kind() == Kind::Comma {
            self.bump();
            names.push(self.ident()?);
        }
        self.want(Kind::RParen)?;
        Ok((String::new(), names))
    }

    fn binding_ty(&mut self) -> Result<TypeRef, Error> {
        if self.kind() != Kind::Colon {
            return Err(self.err("local bindings require a type"));
        }
        self.bump();
        self.ty()
    }

    fn emit_stmt(&mut self, span: Span) -> Result<Stmt, Error> {
        self.want(Kind::Emit)?;
        let name = self.dotted()?;
        if self.kind() == Kind::LParen {
            return Err(self.err(format!(
                "an event takes its fields in braces: `emit {name} {{ field = ...; }}`"
            )));
        }
        self.want(Kind::LBrace)?;
        let fields = self.named_fields()?;
        Ok(Stmt::Emit { span, name, fields })
    }

    fn defer_stmt(&mut self, span: Span) -> Result<Stmt, Error> {
        self.want(Kind::Defer)?;
        let create = self.kind() == Kind::Create;
        let mut expr = if create {
            // `create Vault(args)`: a contract of the same file, given its `deploy` arguments.
            // `create(code)`: creation code as a `bytes` value.
            self.bump();
            let cspan = self.at();
            let (name, kind) = if self.kind() == Kind::LParen {
                (self.sym("create"), Builtin::RawCreate)
            } else {
                let name = self.ident_sym()?;
                (name, Builtin::Create)
            };
            self.want(Kind::LParen)?;
            let args = self.args()?;
            let mut call = self.call(cspan, name, args, None);
            if let Expr::Call { builtin, .. } = &mut call {
                *builtin = Some(kind);
            }
            call
        } else {
            self.expr()?
        };
        let CallOptions { value, salt, gas } = self.with_options()?;
        if let Some(salt) = salt {
            let (Expr::Call { base, .. }, true) = (&mut expr, create) else {
                return Err(error(salt.span(), "`salt` is only for `create`"));
            };
            *base = Some(Box::new(salt));
        }
        let then = if self.kind() == Kind::Then {
            Some(Box::new(self.then_clause()?))
        } else {
            None
        };
        Ok(Stmt::Defer {
            span,
            expr,
            value,
            gas,
            then,
        })
    }

    /// `then { ... }`, `then (name : T) { ... }`, or `then ((a, b) : (T, U)) { ... }`.
    /// `then (name : T) { ... }`, `then { ... }`, or the recoverable form
    /// `then { | Ok(name : T) -> { ... } | Error(reason : bytes) -> { ... } }`.
    fn then_clause(&mut self) -> Result<Then, Error> {
        let span = self.at();
        self.want(Kind::Then)?;
        if self.kind() == Kind::LBrace && self.peek_kind(1) == Kind::Pipe {
            return self.recover_arms(span);
        }
        let (names, tuple, ty) = self.then_binding()?;
        let stmts = self.block()?;
        Ok(Then {
            span,
            names,
            tuple,
            ty,
            stmts,
            syms: Vec::new(),
            ret: 0,
            error: None,
        })
    }

    /// `(name : T)` or `((a, b) : T)`, or nothing. `(_)` binds nothing.
    fn then_binding(&mut self) -> Result<(Vec<String>, bool, Option<TypeRef>), Error> {
        let mut names = Vec::new();
        let mut tuple = false;
        let mut ty = None;
        if self.kind() == Kind::LParen {
            self.bump();
            if self.kind() == Kind::LParen {
                self.bump();
                tuple = true;
                loop {
                    names.push(self.ident()?);
                    if self.kind() != Kind::Comma {
                        break;
                    }
                    self.bump();
                }
                self.want(Kind::RParen)?;
            } else {
                names.push(self.ident()?);
            }
            if names == ["_"] && self.kind() == Kind::RParen {
                self.bump();
                return Ok((Vec::new(), false, None));
            }
            if self.kind() != Kind::Colon {
                return Err(self.err("a continuation result needs a type: `then (name : type)`"));
            }
            self.bump();
            ty = Some(self.ty()?);
            self.want(Kind::RParen)?;
            if names == ["_"] {
                names.clear();
            }
        }
        Ok((names, tuple, ty))
    }

    fn recover_arms(&mut self, span: Span) -> Result<Then, Error> {
        self.want(Kind::LBrace)?;
        let mut ok: Option<Then> = None;
        let mut failed: Option<Then> = None;
        while self.kind() != Kind::RBrace && self.kind() != Kind::Eof {
            if self.kind() == Kind::Semi {
                self.bump();
                continue;
            }
            self.want(Kind::Pipe)?;
            let aspan = self.at();
            let ctor = self.ident()?;
            let (names, tuple, ty) = self.then_binding()?;
            self.want(Kind::Arrow)?;
            let stmts = self.block()?;
            let arm = Then {
                span: aspan,
                names,
                tuple,
                ty,
                stmts,
                syms: Vec::new(),
                ret: 0,
                error: None,
            };
            let slot = match ctor.as_str() {
                "Ok" => &mut ok,
                "Error" => &mut failed,
                _ => {
                    return Err(error(
                        aspan,
                        format!("a call's outcome is `Ok` or `Error`, not `{ctor}`"),
                    ))
                }
            };
            if slot.is_some() {
                return Err(error(aspan, format!("duplicate arm `{ctor}`")));
            }
            *slot = Some(arm);
        }
        self.want(Kind::RBrace)?;
        let (Some(mut ok), Some(failed)) = (ok, failed) else {
            return Err(error(
                span,
                "a recoverable call needs both `Ok` and `Error` arms",
            ));
        };
        ok.span = span;
        ok.error = Some(Box::new(failed));
        Ok(ok)
    }

    /// `with value = x`, `with gas = g`, `with salt = s`, or several in braces:
    /// `with { value = x; gas = g }`. Nothing when there is no `with`.
    fn with_options(&mut self) -> Result<CallOptions, Error> {
        let mut options = CallOptions::default();
        if self.kind() != Kind::With {
            return Ok(options);
        }
        self.bump();
        if self.kind() == Kind::LBrace {
            self.bump();
            while self.kind() != Kind::RBrace && self.kind() != Kind::Eof {
                if self.kind() == Kind::Semi {
                    self.bump();
                    continue;
                }
                self.with_option(&mut options)?;
            }
            self.want(Kind::RBrace)?;
        } else {
            self.with_option(&mut options)?;
        }
        Ok(options)
    }

    fn with_option(&mut self, options: &mut CallOptions) -> Result<(), Error> {
        let name = self.ident()?;
        self.want(Kind::Eq)?;
        let expr = self.expr()?;
        let slot = match name.as_str() {
            "value" => &mut options.value,
            "salt" => &mut options.salt,
            "gas" => &mut options.gas,
            _ => return Err(self.err(format!("unknown `with` option `{name}`"))),
        };
        if slot.is_some() {
            return Err(self.err(format!("duplicate `{name}`")));
        }
        *slot = Some(expr);
        Ok(())
    }

    /// `place := expr;`, `f(...);`, or with `delete`, `delete place;`.
    fn assign_or_call(&mut self, span: Span, delete: bool) -> Result<Stmt, Error> {
        let name = self.ident_sym()?;
        if self.kind() == Kind::LParen && delete {
            return Err(self.err("`delete` takes a place, not a call"));
        }
        if self.kind() == Kind::LParen {
            self.bump();
            let args = self.args()?;
            return Ok(Stmt::Call {
                span,
                expr: self.call(span, name, args, None),
            });
        }
        let mut path = vec![name.to_string()];
        while self.kind() == Kind::Dot {
            self.bump();
            let fspan = self.at();
            let field = self.member_name_sym()?;
            if self.kind() == Kind::LParen && delete {
                return Err(self.err("`delete` takes a place, not a call"));
            }
            if self.kind() == Kind::LParen {
                self.bump();
                let args = self.args()?;
                let base = path_expr(&self.names, span, &path);
                return Ok(Stmt::Call {
                    span,
                    expr: self.call(fspan, field, args, Some(base)),
                });
            }
            path.push(field.to_string());
        }
        let mut keys = Vec::new();
        let mut fields = Vec::new();
        while self.kind() == Kind::LBrack || (!keys.is_empty() && self.kind() == Kind::Dot) {
            if self.kind() == Kind::Dot {
                self.bump();
                fields.push((keys.len(), self.ident()?));
                continue;
            }
            self.bump();
            keys.push(self.expr()?);
            self.want(Kind::RBrack)?;
        }
        let index = if keys.is_empty() {
            None
        } else {
            Some(keys.remove(0))
        };
        let op = if delete { None } else { self.compound_op() };
        let expr = if delete {
            Expr::Lit {
                span,
                lit: Lit::Zero,
                ty: 0,
            }
        } else {
            if op.is_none() {
                self.want(Kind::Assign)?;
            }
            self.expr()?
        };
        Ok(Stmt::Assign {
            span,
            path,
            index,
            keys,
            fields,
            expr,
            op,
            root: None,
            leaf: 0,
            target: None,
            push: false,
        })
    }

    /// The operator of `place op= expr`, which then wants no `:=`.
    fn compound_op(&mut self) -> Option<BinOp> {
        if self.kind() != Kind::OpAssign {
            return None;
        }
        let op = self.slice().strip_suffix('=')?;
        let op = [
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::Div,
            BinOp::Mod,
            BinOp::Pow,
            BinOp::BitAnd,
            BinOp::BitOr,
            BinOp::BitXor,
            BinOp::Shl,
            BinOp::Shr,
        ]
        .into_iter()
        .find(|o| op_text(*o) == op)?;
        self.bump();
        Some(op)
    }

    fn reason(&mut self) -> Result<Raised, Error> {
        if self.kind() == Kind::String {
            return Err(self.err("errors must be typed"));
        }
        self.raised()
    }

    /// `forward name`: a contextual keyword, so `forward` still names functions and values.
    fn forward_ahead(&self) -> bool {
        self.kind() == Kind::Ident && self.slice() == "forward" && self.peek_kind(1) == Kind::Ident
    }

    /// `fail E(...)`, or `forward reason`, which reverts with the raw `bytes` in `reason`.
    fn fail_reason(&mut self) -> Result<Raised, Error> {
        let forward = self.kind() != Kind::Fail;
        self.bump();
        if !forward {
            return self.raised();
        }
        let span = self.at();
        Ok(Raised {
            span,
            name: self.ident()?,
            form: RaisedForm::Unit,
            index: None,
            forward,
        })
    }

    fn raised(&mut self) -> Result<Raised, Error> {
        let span = self.at();
        let name = self.dotted()?;
        let form = if self.kind() == Kind::LParen {
            self.bump();
            let expr = self.expr()?;
            self.want(Kind::RParen)?;
            RaisedForm::Positional(expr)
        } else if self.kind() == Kind::LBrace {
            self.bump();
            RaisedForm::Fields(self.named_fields()?)
        } else {
            RaisedForm::Unit
        };
        Ok(Raised {
            span,
            name,
            form,
            index: None,
            forward: false,
        })
    }

    /// Pratt parser. Binding power rises with precedence.
    /// Comparisons are non-associative; `#` is right-associative.
    fn expr(&mut self) -> Result<Expr, Error> {
        self.expr_bp(0)
    }

    fn expr_bp(&mut self, min_bp: u8) -> Result<Expr, Error> {
        let mut left = self.prefix()?;
        loop {
            if self.kind() == Kind::Pipe && self.pipe_starts_arm() {
                break;
            }
            let Some((op, lbp, rbp)) = infix(self.kind()) else {
                break;
            };
            if lbp < min_bp {
                break;
            }
            if lbp == min_bp && op.is_cmp() {
                return Err(self.err("comparisons cannot be chained"));
            }
            let span = self.at();
            self.bump();
            let right = self.expr_bp(rbp)?;
            left = Expr::Binary {
                span,
                op,
                left: Box::new(left),
                right: Box::new(right),
                ty: 0,
            };
        }
        Ok(left)
    }

    fn prefix(&mut self) -> Result<Expr, Error> {
        let span = self.at();
        match self.kind() {
            Kind::Tilde => {
                self.bump();
                let expr = self.expr_bp(PREFIX_BP)?;
                Ok(Expr::Unary {
                    span,
                    op: UnOp::BitNot,
                    expr: Box::new(expr),
                    ty: 0,
                })
            }
            Kind::Not => {
                self.bump();
                let expr = self.expr_bp(PREFIX_BP)?;
                Ok(Expr::Unary {
                    span,
                    op: UnOp::Not,
                    expr: Box::new(expr),
                    ty: 0,
                })
            }
            Kind::Minus => {
                self.bump();
                let expr = self.expr_bp(PREFIX_BP)?;
                Ok(Expr::Unary {
                    span,
                    op: UnOp::Neg,
                    expr: Box::new(expr),
                    ty: 0,
                })
            }
            Kind::Query => {
                self.bump();
                let expr = self.primary()?;
                let CallOptions { value, salt, gas } = self.with_options()?;
                if let Some(e) = value.or(salt) {
                    return Err(error(e.span(), "a query takes only `with gas`"));
                }
                Ok(Expr::Query {
                    span,
                    expr: Box::new(expr),
                    gas: gas.map(Box::new),
                    ty: 0,
                })
            }
            _ => self.primary(),
        }
    }

    fn primary(&mut self) -> Result<Expr, Error> {
        let span = self.at();
        match self.kind() {
            Kind::Int => {
                let digits = self
                    .slice()
                    .strip_prefix("0x")
                    .map(|d| d.bytes().filter(|b| *b != b'_').count() as u8);
                let lit = Lit::Int(self.tok().word, digits);
                self.bump();
                Ok(Expr::Lit { span, lit, ty: 0 })
            }
            Kind::WeiLit => {
                let lit = Lit::Wei(self.tok().word);
                self.bump();
                Ok(Expr::Lit { span, lit, ty: 0 })
            }
            Kind::DurationLit => {
                let lit = Lit::Duration(self.tok().word);
                self.bump();
                Ok(Expr::Lit { span, lit, ty: 0 })
            }
            Kind::True => {
                self.bump();
                Ok(Expr::Lit {
                    span,
                    lit: Lit::Bool(true),
                    ty: 0,
                })
            }
            Kind::False => {
                self.bump();
                Ok(Expr::Lit {
                    span,
                    lit: Lit::Bool(false),
                    ty: 0,
                })
            }
            Kind::Unit => {
                self.bump();
                Ok(Expr::Lit {
                    span,
                    lit: Lit::Unit,
                    ty: 0,
                })
            }
            Kind::Nil => {
                self.bump();
                Ok(Expr::Lit {
                    span,
                    lit: Lit::Nil,
                    ty: 0,
                })
            }
            Kind::HexBytes => {
                let digits = self.tok().string.clone().unwrap_or_default();
                let bytes = (0..digits.len())
                    .step_by(2)
                    .map(|i| u8::from_str_radix(&digits[i..i + 2], 16).unwrap_or(0))
                    .collect();
                self.bump();
                Ok(Expr::Lit {
                    span,
                    lit: Lit::Bytes(bytes),
                    ty: 0,
                })
            }
            Kind::String => {
                let s = self.tok().string.clone().unwrap_or_default();
                self.bump();
                Ok(Expr::Lit {
                    span,
                    lit: Lit::Str(s),
                    ty: 0,
                })
            }
            Kind::Case => self.case_expr(),
            Kind::If => self.if_expr(),
            Kind::LBrace => self.record_expr(span),
            Kind::LBrack => self.list_expr(span),
            Kind::LParen => {
                self.bump();
                let first = self.expr()?;
                if self.kind() == Kind::Comma {
                    let mut elems = vec![first];
                    while self.kind() == Kind::Comma {
                        self.bump();
                        elems.push(self.expr()?);
                    }
                    self.want(Kind::RParen)?;
                    Ok(Expr::Tuple { span, elems, ty: 0 })
                } else {
                    self.want(Kind::RParen)?;
                    Ok(first)
                }
            }
            Kind::List => {
                let target = self.list_ty(span)?;
                self.want(Kind::LParen)?;
                let expr = self.expr()?;
                self.want(Kind::RParen)?;
                self.postfix(Expr::Convert {
                    span,
                    target: Box::new(target),
                    expr: Box::new(expr),
                    ty: 0,
                })
            }
            Kind::Ident | Kind::AtKw => {
                if self.in_spec {
                    if let Some(form) = self.spec_form()? {
                        return Ok(form);
                    }
                }
                let name = self.ident_sym()?;
                self.postfix(Expr::Ident {
                    span,
                    name,
                    sym: None,
                    builtin: None,
                    ty: 0,
                })
            }
            _ => Err(self.err(format!("expected an expression, found {}", self.found()))),
        }
    }

    fn postfix(&mut self, mut e: Expr) -> Result<Expr, Error> {
        loop {
            if self.kind() == Kind::LBrack {
                let ispan = self.at();
                self.bump();
                let start = if self.kind() == Kind::Colon {
                    Expr::Lit {
                        span: ispan,
                        lit: Lit::Uint(crate::word::Word::from_u64(0)),
                        ty: 0,
                    }
                } else {
                    self.expr()?
                };
                if self.kind() == Kind::Colon {
                    self.bump();
                    let mut args = vec![e, start];
                    if self.kind() != Kind::RBrack {
                        args.push(self.expr()?);
                    }
                    self.want(Kind::RBrack)?;
                    e = Expr::Call {
                        span: ispan,
                        name: Symbol::empty(),
                        args,
                        base: None,
                        callee: None,
                        builtin: Some(Builtin::BytesSlice),
                        iface: None,
                        method: None,
                        ty: 0,
                    };
                    continue;
                }
                let index = start;
                self.want(Kind::RBrack)?;
                e = Expr::Index {
                    span: ispan,
                    base: Box::new(e),
                    index: Box::new(index),
                    root: None,
                    leaf: 0,
                    ty: 0,
                };
                continue;
            }
            if self.kind() == Kind::LParen {
                let Expr::Ident { name, span, .. } = &e else {
                    break;
                };
                let (name, span) = (*name, *span);
                self.bump();
                let args = self.args()?;
                e = self.call(span, name, args, None);
                continue;
            }
            // `Case { field = ...; }`: a constructor given a record payload.
            if self.brace_is_record() {
                let Expr::Ident { name, span, .. } = &e else {
                    break;
                };
                let (name, span) = (*name, *span);
                let rspan = self.at();
                let payload = self.record_expr(rspan)?;
                e = self.call(span, name, vec![payload], None);
                if let Expr::Call { builtin, .. } = &mut e {
                    *builtin = Some(Builtin::Braced);
                }
                continue;
            }
            if self.kind() != Kind::Dot {
                break;
            }
            self.bump();
            let fspan = self.at();
            let name = self.member_name_sym()?;
            if self.kind() == Kind::LParen {
                self.bump();
                let args = self.args()?;
                e = self.call(fspan, name, args, Some(e));
            } else {
                e = Expr::Field {
                    span: fspan,
                    base: Box::new(e),
                    name,
                    root: None,
                    leaf: 0,
                    ty: 0,
                };
            }
        }
        Ok(e)
    }

    fn call(&self, span: Span, name: Symbol, args: Vec<Expr>, base: Option<Expr>) -> Expr {
        Expr::Call {
            span,
            name,
            args,
            base: base.map(Box::new),
            callee: None,
            builtin: None,
            iface: None,
            method: None,
            ty: 0,
        }
    }

    fn args(&mut self) -> Result<Vec<Expr>, Error> {
        let mut args = Vec::new();
        if self.kind() == Kind::RParen {
            self.bump();
            return Ok(args);
        }
        loop {
            args.push(self.expr()?);
            if self.kind() == Kind::Comma {
                self.bump();
                continue;
            }
            break;
        }
        self.want(Kind::RParen)?;
        Ok(args)
    }

    fn named_fields(&mut self) -> Result<Vec<(String, Expr)>, Error> {
        let mut fields = Vec::new();
        while self.kind() != Kind::RBrace && self.kind() != Kind::Eof {
            if self.kind() == Kind::Semi {
                self.bump();
                continue;
            }
            if self.kind() == Kind::Indexed {
                return Err(self.err("`indexed` belongs on the event declaration"));
            }
            let name = self.ident()?;
            self.want(Kind::Eq)?;
            let expr = self.expr()?;
            fields.push((name, expr));
            if self.kind() == Kind::Semi {
                self.bump();
            }
        }
        self.want(Kind::RBrace)?;
        Ok(fields)
    }

    fn record_expr(&mut self, span: Span) -> Result<Expr, Error> {
        self.want(Kind::LBrace)?;
        let fields = self.named_fields()?;
        Ok(Expr::Record {
            span,
            fields,
            ty: 0,
        })
    }

    fn list_expr(&mut self, span: Span) -> Result<Expr, Error> {
        self.want(Kind::LBrack)?;
        let mut elems = Vec::new();
        if self.kind() != Kind::RBrack {
            loop {
                elems.push(self.expr()?);
                if self.kind() == Kind::Comma {
                    self.bump();
                    if self.kind() == Kind::RBrack {
                        break;
                    }
                    continue;
                }
                break;
            }
        }
        self.want(Kind::RBrack)?;
        Ok(Expr::List { span, elems, ty: 0 })
    }

    fn case_expr(&mut self) -> Result<Expr, Error> {
        let span = self.at();
        self.want(Kind::Case)?;
        let scrut = self.expr()?;
        self.want(Kind::Of)?;
        self.want(Kind::LBrace)?;
        let mut arms = Vec::new();
        while self.kind() != Kind::RBrace && self.kind() != Kind::Eof {
            if self.kind() == Kind::Semi {
                self.bump();
                continue;
            }
            // The first arm's `|` is optional: `{ Open | Paused -> 1 | Closed -> 2 }`.
            if self.kind() == Kind::Pipe {
                self.bump();
            } else if !arms.is_empty() {
                return Err(self.err(format!("expected `|`, found {}", self.found())));
            }
            let aspan = self.at();
            let mut ctors = Vec::new();
            let mut patterns = Vec::new();
            loop {
                ctors.push(self.ident()?);
                patterns.push(self.arm_pattern()?);
                if self.kind() != Kind::Pipe {
                    break;
                }
                self.bump();
            }
            // `| A(x) | B(x) ->`: every case of the arm binds the same names.
            if patterns.iter().any(|p| p != &patterns[0]) {
                return Err(error(
                    aspan,
                    "every case of an arm must bind the same names",
                ));
            }
            let Pattern {
                bind,
                names: tuple_names,
                fields,
                rest,
            } = patterns.swap_remove(0);
            self.want(Kind::Arrow)?;
            let (stmts, expr) = self.arm_body()?;
            arms.push(Arm {
                span: aspan,
                ctors,
                bind,
                bind_sym: None,
                tuple_names,
                fields,
                rest,
                tuple_syms: Vec::new(),
                tuple_at: Vec::new(),
                stmts,
                expr,
            });
        }
        if arms.is_empty() {
            return Err(self.err("expected at least one case arm"));
        }
        self.want(Kind::RBrace)?;
        Ok(Expr::Case {
            span,
            scrut: Box::new(scrut),
            arms,
            ty: 0,
        })
    }

    /// `if c then a else b` is a `case` on `c`, so its branches are arms.
    fn if_expr(&mut self) -> Result<Expr, Error> {
        let span = self.at();
        self.want(Kind::If)?;
        let scrut = self.expr()?;
        let mut arms = Vec::new();
        for (kind, ctor) in [(Kind::Then, "true"), (Kind::Else, "false")] {
            let aspan = self.at();
            self.want(kind)?;
            let (stmts, expr) = self.arm_body()?;
            arms.push(Arm {
                span: aspan,
                ctors: vec![ctor.to_string()],
                bind: None,
                bind_sym: None,
                tuple_names: Vec::new(),
                fields: Vec::new(),
                rest: false,
                tuple_syms: Vec::new(),
                tuple_at: Vec::new(),
                stmts,
                expr,
            });
        }
        Ok(Expr::Case {
            span,
            scrut: Box::new(scrut),
            arms,
            ty: 0,
        })
    }

    /// What a case arm binds: `(x)`, `((a, b))`, `{ x; y = b; _ }`, or nothing.
    fn arm_pattern(&mut self) -> Result<Pattern, Error> {
        if self.kind() == Kind::LBrace {
            return self.brace_pattern();
        }
        if self.kind() != Kind::LParen {
            return Ok(Pattern::default());
        }
        self.bump();
        if self.kind() == Kind::LParen {
            self.bump();
            let mut names = vec![self.ident()?];
            if self.kind() != Kind::Comma {
                return Err(self.err("a tuple pattern needs at least two names"));
            }
            while self.kind() == Kind::Comma {
                self.bump();
                names.push(self.ident()?);
            }
            self.want(Kind::RParen)?;
            self.want(Kind::RParen)?;
            return Ok(Pattern {
                names,
                ..Pattern::default()
            });
        }
        let name = self.ident()?;
        self.want(Kind::RParen)?;
        Ok(Pattern {
            bind: Some(name),
            ..Pattern::default()
        })
    }

    /// `{ x; y = b; _ }`: fields bound under their own names or others, `_` last for the rest.
    fn brace_pattern(&mut self) -> Result<Pattern, Error> {
        self.want(Kind::LBrace)?;
        let mut pattern = Pattern::default();
        while self.kind() != Kind::RBrace && self.kind() != Kind::Eof {
            if pattern.rest {
                return Err(self.err("`_` ends a brace pattern: it stands for every other field"));
            }
            let field = self.ident()?;
            if field == "_" {
                pattern.rest = true;
            } else if self.kind() == Kind::Eq {
                self.bump();
                pattern.names.push(self.ident()?);
                pattern.fields.push(field);
            } else {
                pattern.names.push(field.clone());
                pattern.fields.push(field);
            }
            if self.kind() != Kind::Semi {
                break;
            }
            self.bump();
        }
        self.want(Kind::RBrace)?;
        if pattern.fields.is_empty() && !pattern.rest {
            return Err(self.err("a brace pattern names at least one field"));
        }
        Ok(pattern)
    }

    /// A function's name, or a member's after `.`: an identifier, or `create`, which
    /// Solidity ABIs use for factories' functions.
    fn member_name(&mut self) -> Result<String, Error> {
        Ok(self.member_name_sym()?.to_string())
    }

    fn member_name_sym(&mut self) -> Result<Symbol, Error> {
        if self.kind() == Kind::Create {
            self.bump();
            return Ok(self.sym("create"));
        }
        self.ident_sym()
    }

    /// The identifier at the cursor, as its text. The token carries only its bytes, so the
    /// `String` is built here, for the declaration fields that hold one; a caller that wants a
    /// `Symbol` interns the text once, through [`Parser::sym`].
    fn ident(&mut self) -> Result<String, Error> {
        Ok(self.ident_sym()?.to_string())
    }

    /// The identifier at the cursor, interned: the form every expression, type, and name site
    /// needs, with no `String` in between.
    fn ident_sym(&mut self) -> Result<Symbol, Error> {
        if self.kind() == Kind::AtKw {
            self.bump();
            return Ok(self.sym("at"));
        }
        if self.kind() != Kind::Ident {
            return Err(self.err(format!("expected identifier, found {}", self.found())));
        }
        let name = self.sym(self.lexeme());
        self.bump();
        Ok(name)
    }

    /// The symbol for `text`, in this parser's table.
    fn sym(&self, text: &str) -> Symbol {
        self.names.intern(text)
    }

    /// `text` as a name written at `span`.
    fn name_at(&self, span: Span, text: &str) -> NameAt {
        NameAt {
            span,
            name: self.sym(text),
        }
    }

    /// `name` as a name written at `span`, with the symbol it already has.
    fn named_at(span: Span, name: Symbol) -> NameAt {
        NameAt { span, name }
    }

    /// A dotted name written at `span`, interned: one intern for `M`, none for `M.E`, which
    /// has to join the two texts into one symbol.
    fn dotted_at(&mut self, span: Span) -> Result<NameAt, Error> {
        let first = self.ident_sym()?;
        if self.kind() != Kind::Dot || self.peek_kind(1) != Kind::Ident {
            return Ok(Self::named_at(span, first));
        }
        let mut path = first.to_string();
        while self.kind() == Kind::Dot && self.peek_kind(1) == Kind::Ident {
            self.bump();
            path = format!("{path}.{}", self.ident_sym()?);
        }
        Ok(Self::named_at(span, self.sym(&path)))
    }

    /// A name, or one qualified by an import alias or a module: `E.Denied`.
    fn dotted(&mut self) -> Result<String, Error> {
        let mut name = self.ident_sym()?.to_string();
        while self.kind() == Kind::Dot && self.peek_kind(1) == Kind::Ident {
            self.bump();
            name = format!("{name}.{}", self.ident_sym()?);
        }
        Ok(name)
    }

    fn kind(&self) -> Kind {
        self.toks[self.i].kind
    }

    fn peek_kind(&self, ahead: usize) -> Kind {
        self.toks
            .get(self.i + ahead)
            .map_or(Kind::Eof, |tok| tok.kind)
    }

    /// `| Name ->`, `| Name(...) ->`, and `| Name { ... } ->` close a case arm. Other pipes
    /// are bitwise or.
    fn pipe_starts_arm(&self) -> bool {
        let mut i = self.i + 1;
        if self.toks.get(i).map(|tok| tok.kind) != Some(Kind::Ident) {
            return false;
        }
        i += 1;
        let kind = |i: usize| self.toks.get(i).map(|tok| tok.kind);
        loop {
            if matches!(kind(i), Some(Kind::LParen | Kind::LBrace)) {
                let mut depth = 0i32;
                loop {
                    match kind(i) {
                        Some(Kind::LParen | Kind::LBrace) => depth += 1,
                        Some(Kind::RParen | Kind::RBrace) => depth -= 1,
                        None | Some(Kind::Eof) => return false,
                        _ => {}
                    }
                    i += 1;
                    if depth == 0 {
                        break;
                    }
                }
            }
            // `| A(x) | B(x) ->`: an arm for several constructors.
            if kind(i) == Some(Kind::Pipe) && kind(i + 1) == Some(Kind::Ident) {
                i += 2;
                continue;
            }
            return kind(i) == Some(Kind::Arrow);
        }
    }

    fn tok(&self) -> &Token {
        &self.toks[self.i]
    }

    fn at(&self) -> Span {
        let tok = self.tok();
        Span {
            lo: tok.start as u32,
            hi: tok.end as u32,
        }
    }

    fn bump(&mut self) {
        if self.i + 1 < self.toks.len() {
            self.i += 1;
        }
    }

    fn want(&mut self, k: Kind) -> Result<(), Error> {
        if self.kind() == k {
            self.bump();
            Ok(())
        } else {
            Err(self.err(format!(
                "expected {}, found {}",
                lex::kind_name(k),
                self.found()
            )))
        }
    }

    fn lexeme(&self) -> &str {
        let t = self.tok();
        self.src.get(t.start..t.end).unwrap_or("")
    }

    fn found(&self) -> String {
        if self.kind() == Kind::Eof {
            "end of file".to_string()
        } else if matches!(self.kind(), Kind::Ident | Kind::Int | Kind::String) {
            format!("`{}`", self.lexeme())
        } else {
            lex::kind_name(self.kind()).to_string()
        }
    }

    fn err(&self, message: impl Into<String>) -> Error {
        let span = self.at();
        error(span, message)
    }
}

/// `std/a/b`, `./a/b`, `../../a/b`, or a package's `name/a/b`, never a bare `name`: each name
/// a lowercase identifier.
pub(crate) fn module_path(path: &str) -> bool {
    let mut rest = path.trim_start_matches("../");
    if rest == path {
        rest = path.strip_prefix("./").unwrap_or(path);
    }
    let rest = (rest != path || path.contains('/')).then_some(rest);
    rest.is_some_and(|rest| {
        rest.split('/').all(|seg| {
            let mut chars = seg.chars();
            chars
                .next()
                .is_some_and(|c| c.is_ascii_lowercase() || c == '_')
                && chars.all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
        })
    })
}

fn special_word(kind: ItemKind) -> Option<&'static str> {
    match kind {
        ItemKind::Receive => Some("receive"),
        ItemKind::Fallback => Some("fallback"),
        _ => None,
    }
}

const PREFIX_BP: u8 = 21;

fn infix(k: Kind) -> Option<(BinOp, u8, u8)> {
    // Looser to tighter: boolean, comparison, bitwise, cons, shift, add, mul, prefix, power.
    // Comparisons stay non-associative. `#` and `**` stay right-associative.
    // Bitwise binds tighter than comparison, so `flags & mask = 0` is `(flags & mask) = 0`.
    Some(match k {
        Kind::Or => (BinOp::Or, 1, 2),
        Kind::And => (BinOp::And, 3, 4),
        Kind::Eq => (BinOp::Eq, 5, 5),
        Kind::Neq => (BinOp::Neq, 5, 5),
        Kind::Lt => (BinOp::Lt, 5, 5),
        Kind::Gt => (BinOp::Gt, 5, 5),
        Kind::Le => (BinOp::Le, 5, 5),
        Kind::Ge => (BinOp::Ge, 5, 5),
        Kind::Pipe => (BinOp::BitOr, 7, 8),
        Kind::Caret => (BinOp::BitXor, 9, 10),
        Kind::Amp => (BinOp::BitAnd, 11, 12),
        Kind::Hash => (BinOp::Cons, 13, 13),
        Kind::Shl => (BinOp::Shl, 15, 16),
        Kind::Shr => (BinOp::Shr, 15, 16),
        Kind::Plus => (BinOp::Add, 17, 18),
        Kind::Minus => (BinOp::Sub, 17, 18),
        Kind::Star => (BinOp::Mul, 19, 20),
        Kind::Slash => (BinOp::Div, 19, 20),
        Kind::Percent => (BinOp::Mod, 19, 20),
        Kind::StarStar => (BinOp::Pow, 23, 23),
        _ => return None,
    })
}

/// A guard as a function: a `view` that only fails, whose body the contract writes.
fn guard_func(span: Span, name: String, params: Vec<Param>) -> Func {
    Func {
        span,
        kind: ItemKind::Readonly,
        private: false,
        file: FileId::default(),
        name,
        type_params: Vec::new(),
        params,
        ret: None,
        ret_flat: false,
        ret_ty: 0,
        payable: false,
        nonreentrant: false,
        external_pure: false,
        raises: None,
        errors: Vec::new(),
        stmts: Vec::new(),
        tail: None,
        module: None,
        requires: Vec::new(),
        promoted: None,
        declares: None,
        interface: None,
        exported: None,
        forward: None,
        guarded: None,
        guard_of: None,
        constant: false,
        hook_of: None,
    }
}

/// What a case arm binds, as written.
#[derive(Default, PartialEq)]
struct Pattern {
    bind: Option<String>,
    names: Vec<String>,
    fields: Vec<String>,
    rest: bool,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(src: &str) -> Result<super::Program, crate::Error> {
        super::parse(src, &super::Names::shared())
    }

    /// `parse` interns every identifier it reads, and only once per distinct text, so a
    /// `Program` from one file names the same `Symbol` as the same text in another.
    #[test]
    fn parsing_interns_each_identifier_once_into_the_given_table() {
        let names = std::sync::Arc::new(Names::new());
        let left = "storage is record { count : uint; }\nexternal function a() is { storage.count := 1; }\n";
        let right = "storage is record { count : uint; }\nexternal function a() is { storage.count := 2; }\n";
        super::parse(left, &names).unwrap();
        let after_left = names.len();
        // More than zero rules out a parse that never touches the table.
        assert!(after_left > 0, "left parsed without interning anything");
        super::parse(right, &names).unwrap();
        assert_eq!(
            names.len(),
            after_left,
            "the same texts in a second file must reuse their symbols, not add new ones"
        );
        assert_eq!(&*names.get(names.intern("count")), "count");
    }

    #[test]
    fn chained_comparison_points_at_the_operator() {
        let src = "function f (const a : uint) : uint is\n  1 = 2 = 3\n";
        let err = parse(src).expect_err("chained comparison");
        assert_eq!(err.line, 2);
        assert!(
            err.message.contains("comparisons cannot be chained"),
            "{err}"
        );
    }

    #[test]
    fn unterminated_comment_uses_the_opening_line() {
        let src = "(*\ncomment\n";
        let err = parse(src).expect_err("comment");
        assert_eq!(err.line, 1);
        assert_eq!(err.column, 1);
        assert_eq!(err.message, "unterminated comment");
    }

    #[test]
    fn comment_newlines_do_not_stick_the_next_token() {
        let src = "(*\ncomment\n*)\n$$\n";
        let err = parse(src).expect_err("dollar");
        assert_eq!(err.line, 4);
        assert!(err.message.contains("unexpected character `$`"), "{err}");
    }

    #[test]
    fn unit_value_is_not_the_unit_type() {
        let src = "type T is Unit\n";
        let err = parse(src).expect_err("Unit");
        assert!(
            err.message
                .contains("expected type `unit`, found value `Unit`"),
            "{err}"
        );
    }

    /// A broken statement does not hide the ones after it: every statement of every block is
    /// parsed, and each broken one adds its error. The first is the one the parse would have
    /// reported had it stopped there, so a diagnostic that names one error names the same one.
    #[test]
    fn statement_errors_are_all_reported_in_file_order() {
        let src = "storage is record { count : uint; }\n\
external function f(const a : uint) : uint is {\n\
  var x : uint := 1;\n\
  x := ;\n\
  if x > 0 then {\n\
    var q : uint := a +;\n\
  }\n\
  var z : uint := ;\n\
  storage.count := x;\n\
} with x\n";
        let err = parse(src).expect_err("broken statements");
        let found: Vec<(u32, String)> = err
            .chain()
            .map(|err| (err.line, err.message.clone()))
            .collect();
        assert_eq!(
            found,
            vec![
                (4, "expected an expression, found `;`".to_string()),
                (6, "expected an expression, found `;`".to_string()),
                (8, "expected an expression, found `;`".to_string()),
            ],
            "every broken statement, in file order"
        );
    }

    /// A file with one broken statement reports exactly the one error it always did: recovery
    /// adds errors, it never changes or drops the first.
    #[test]
    fn one_broken_statement_is_one_error() {
        let src = "storage is record { count : uint; }\n\
external function f() : uint is {\n\
  var x : uint := ;\n\
  storage.count := 5;\n\
} with 0\n";
        let err = parse(src).expect_err("broken statement");
        assert_eq!(err.chain().count(), 1);
        assert_eq!(err.line, 3);
    }

    /// The statement a failure happened in is skipped from its first token, so a `}` inside a
    /// record literal it had already opened is not mistaken for the end of the block: the block
    /// still ends where it does, and the file reports the one error it always did.
    #[test]
    fn skipping_a_broken_statement_counts_the_brackets_it_opened() {
        let src = "event Foo of record {\n\
  amount : uint;\n\
}\n\
storage is record {\n\
  n : uint;\n\
}\n\
external function go() is {\n\
  emit Foo { indexed amount = 1 };\n\
}\n";
        let err = parse(src).expect_err("indexed in an emit");
        let found: Vec<(u32, String)> = err
            .chain()
            .map(|err| (err.line, err.message.clone()))
            .collect();
        assert_eq!(
            found,
            vec![(8, "`indexed` belongs on the event declaration".to_string())],
            "one error, and no cascade from the record's own `}}`"
        );
    }

    /// A `}` with only `(` open above the statement's own braces is the block's `}`, not that
    /// paren's closer: `bar(a;` ends the statement at the block's `}` without consuming it, so
    /// the declaration after it is parsed and reports its own error instead of a cascade.
    #[test]
    fn an_unclosed_paren_does_not_swallow_the_block() {
        let src = "storage is record { n : uint; }\n\
external function f() : uint is {\n\
  bar(1;\n\
} with 0\n\
\n\
external function g() : uint is {\n\
  var y : uint := ;\n\
} with 0\n";
        let err = parse(src).expect_err("broken statements");
        let found: Vec<(u32, String)> = err
            .chain()
            .map(|err| (err.line, err.message.clone()))
            .collect();
        assert_eq!(
            found,
            vec![
                (3, "expected `)`, found `;`".to_string()),
                (7, "expected an expression, found `;`".to_string()),
            ],
            "the first error unchanged, the second function's reported, no cascade"
        );
    }

    /// The same for a `[`: the block's `}` closes the statement, not the index.
    #[test]
    fn an_unclosed_bracket_does_not_swallow_the_block() {
        let src = "storage is record { n : uint; }\nexternal function f(const a : list(uint, 4)) : uint is {\n\
  var z : uint := a[0;\n\
  z := 1;\n\
} with z\n\
\n\
external function g() : uint is {\n\
  var y : uint := ;\n\
} with 0\n";
        let err = parse(src).expect_err("broken statements");
        let found: Vec<(u32, String)> = err
            .chain()
            .map(|err| (err.line, err.message.clone()))
            .collect();
        assert_eq!(
            found,
            vec![
                (3, "expected `]`, found `;`".to_string()),
                (8, "expected an expression, found `;`".to_string()),
            ],
            "the first error unchanged, the second function's reported, no cascade"
        );
    }

    /// A block a spec clause reaches recovers errors too, and a spec file with a broken
    /// statement is rejected rather than accepted with the statement silently dropped.
    #[test]
    fn statement_errors_inside_a_spec_block_are_reported() {
        let src = "spec for deposit is {\n\
  ensures if true then { var y : uint := ; } with true else true;\n\
}\n";
        let err = match super::parse_specs(src) {
            Ok(_) => panic!("a broken statement in a spec block must be an error"),
            Err(err) => err,
        };
        assert_eq!(err.line, 2);
        assert_eq!(err.message, "expected an expression, found `;`");
    }
}
