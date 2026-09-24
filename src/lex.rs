//! Logos tokenizes. Line and column, and every message, are ours.

use logos::{Lexer, Logos, Skip};

use crate::error;
use crate::word::Word;
use crate::Error;

#[derive(Clone, Debug)]
struct Extras {
    line: u32,
    line_start: usize,
}

impl Default for Extras {
    fn default() -> Self {
        Self {
            line: 1,
            line_start: 0,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Num {
    Nat(Word),
    Int(Word),
    Wei(Word),
    Duration(Word),
}

#[derive(Debug, Clone, PartialEq)]
enum LexError {
    Unexpected,
    UnterminatedComment {
        line: u32,
        col: u32,
    },
    UnterminatedString {
        line: u32,
        col: u32,
    },
    BadNumber {
        line: u32,
        col: u32,
        message: String,
    },
}

impl Default for LexError {
    fn default() -> Self {
        Self::Unexpected
    }
}

#[derive(Logos, Debug, Clone)]
#[logos(extras = Extras)]
#[logos(error = LexError)]
enum Raw {
    #[regex(r"[ \t\r]+", logos::skip)]
    #[regex(r"\n", newline)]
    #[token("(*", comment)]
    Skipped,

    #[regex(r"[A-Za-z_][A-Za-z0-9_]*")]
    Ident,

    #[regex(r"0x[0-9a-fA-F_]+", hex_lit)]
    #[regex(r"[0-9][0-9_]*(n|eth|gwei|wei|seconds|minutes|hours|days)?", number)]
    Number(Num),

    #[token("\"", string_lit)]
    String(String),

    #[token("type")]
    Type,
    #[token("is")]
    Is,
    #[token("record")]
    Record,
    #[token("function")]
    Function,
    #[token("view")]
    View,
    #[token("event")]
    Event,
    #[token("indexed")]
    Indexed,
    #[token("error")]
    ErrorKw,
    #[token("errors")]
    ErrorsKw,
    #[token("raises")]
    Raises,
    #[token("payable")]
    Payable,
    #[token("external")]
    External,
    #[token("pure")]
    Pure,
    #[token("nonreentrant")]
    Nonreentrant,
    #[token("import")]
    Import,
    #[token("module")]
    Module,
    #[token("use")]
    Use,
    #[token("requires")]
    Requires,
    #[token("as")]
    As,
    #[token("private")]
    Private,
    #[token("migrate")]
    Migrate,
    #[token("deploy")]
    Deploy,
    #[token("upgradeable")]
    Upgradeable,
    #[token("upgrade")]
    Upgrade,
    #[token("at")]
    AtKw,
    #[token("contract")]
    Contract,
    #[token("fail")]
    Fail,
    #[token("interface")]
    Interface,
    #[token("query")]
    Query,
    #[token("emit")]
    Emit,
    #[token("defer")]
    Defer,
    #[token("end")]
    End,
    #[token("call")]
    CallKw,
    #[token("create")]
    Create,
    #[token("const")]
    Const,
    #[token("var")]
    Var,
    #[token("if")]
    If,
    #[token("then")]
    Then,
    #[token("else")]
    Else,
    #[token("for")]
    For,
    #[token("in")]
    In,
    #[token("do")]
    Do,
    #[token("until")]
    Until,
    #[token("bound")]
    Bound,
    #[token("case")]
    Case,
    #[token("of")]
    Of,
    #[token("with")]
    With,
    #[token("skip")]
    SkipKw,
    #[token("and")]
    And,
    #[token("or")]
    Or,
    #[token("not")]
    Not,
    #[token("failwith")]
    Failwith,
    #[token("assert")]
    Assert,
    #[token("list")]
    List,
    #[token("true")]
    True,
    #[token("false")]
    False,
    #[token("Unit")]
    Unit,
    #[token("nil")]
    Nil,

    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("[")]
    LBrack,
    #[token("]")]
    RBrack,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token(":=")]
    Assign,
    #[token(":")]
    Colon,
    #[token(";")]
    Semi,
    #[token(",")]
    Comma,
    #[token("..")]
    DotDot,
    #[token(".")]
    Dot,
    #[token("#")]
    Hash,
    #[token("->")]
    Arrow,
    #[token("|")]
    Pipe,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("%")]
    Percent,
    #[token("&")]
    Amp,
    #[token("^")]
    Caret,
    #[token("~")]
    Tilde,
    #[token("<<")]
    Shl,
    #[token(">>")]
    Shr,
    #[token("=/=")]
    #[token("<>")]
    Neq,
    #[token("=")]
    Eq,
    #[token("<=")]
    Le,
    #[token(">=")]
    Ge,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,
    #[token("@")]
    At,
}

fn newline(lex: &mut Lexer<Raw>) -> Skip {
    lex.extras.line += 1;
    lex.extras.line_start = lex.span().end;
    Skip
}

fn comment(lex: &mut Lexer<Raw>) -> Result<Skip, LexError> {
    let line = lex.extras.line;
    let col = col_at(lex, lex.span().start);
    let mut depth = 1;
    loop {
        let rest = lex.remainder();
        if rest.is_empty() {
            return Err(LexError::UnterminatedComment { line, col });
        }
        if rest.starts_with("(*") {
            depth += 1;
            lex.bump(2);
            continue;
        }
        if rest.starts_with("*)") {
            depth -= 1;
            lex.bump(2);
            if depth == 0 {
                return Ok(Skip);
            }
            continue;
        }
        if rest.starts_with('\n') {
            lex.bump(1);
            lex.extras.line += 1;
            lex.extras.line_start = lex.span().end;
            continue;
        }
        let ch = rest.chars().next().unwrap_or('\0');
        lex.bump(ch.len_utf8());
    }
}

fn string_lit(lex: &mut Lexer<Raw>) -> Result<String, LexError> {
    let line = lex.extras.line;
    let col = col_at(lex, lex.span().start);
    let mut out = String::new();
    loop {
        let rest = lex.remainder();
        if rest.is_empty() || rest.starts_with('\n') {
            return Err(LexError::UnterminatedString { line, col });
        }
        let ch = rest.chars().next().unwrap_or('\0');
        lex.bump(ch.len_utf8());
        if ch == '"' {
            return Ok(out);
        }
        if ch == '\\' {
            let rest = lex.remainder();
            let n = rest
                .chars()
                .next()
                .ok_or(LexError::UnterminatedString { line, col })?;
            if n == '\n' {
                return Err(LexError::UnterminatedString { line, col });
            }
            lex.bump(n.len_utf8());
            out.push(n);
            continue;
        }
        out.push(ch);
    }
}

fn number(lex: &mut Lexer<Raw>) -> Result<Num, LexError> {
    let line = lex.extras.line;
    let col = col_at(lex, lex.span().start);
    let slice = lex.slice();
    let (digits, kind) = if let Some(rest) = slice.strip_suffix("seconds") {
        (rest, NumKind::Duration(1))
    } else if let Some(rest) = slice.strip_suffix("minutes") {
        (rest, NumKind::Duration(60))
    } else if let Some(rest) = slice.strip_suffix("hours") {
        (rest, NumKind::Duration(3_600))
    } else if let Some(rest) = slice.strip_suffix("days") {
        (rest, NumKind::Duration(86_400))
    } else if let Some(rest) = slice.strip_suffix("gwei") {
        (rest, NumKind::Wei(1_000_000_000))
    } else if let Some(rest) = slice.strip_suffix("eth") {
        (rest, NumKind::Wei(1_000_000_000_000_000_000))
    } else if let Some(rest) = slice.strip_suffix("wei") {
        (rest, NumKind::Wei(1))
    } else if let Some(rest) = slice.strip_suffix('n') {
        (rest, NumKind::Nat)
    } else {
        (slice, NumKind::Plain)
    };
    let Some(word) = Word::from_dec(digits) else {
        return Err(LexError::BadNumber {
            line,
            col,
            message: "number does not fit in 256 bits".to_string(),
        });
    };
    let word = match kind {
        NumKind::Wei(scale) | NumKind::Duration(scale) => word.wrapping_mul(Word::from_u64(scale)),
        NumKind::Nat | NumKind::Plain => word,
    };
    match kind {
        NumKind::Nat => Ok(Num::Nat(word)),
        NumKind::Wei(_) => Ok(Num::Wei(word)),
        NumKind::Duration(_) => Ok(Num::Duration(word)),
        NumKind::Plain => Ok(Num::Int(word)),
    }
}

enum NumKind {
    Nat,
    Plain,
    Wei(u64),
    Duration(u64),
}

fn hex_lit(lex: &mut Lexer<Raw>) -> Result<Num, LexError> {
    let line = lex.extras.line;
    let col = col_at(lex, lex.span().start);
    let digits = lex.slice()[2..].replace('_', "");
    if digits.is_empty() || digits.len() > 64 {
        return Err(LexError::BadNumber {
            line,
            col,
            message: "hex literal does not fit in 256 bits".to_string(),
        });
    }
    let Some(word) = Word::from_hex(&digits) else {
        return Err(LexError::BadNumber {
            line,
            col,
            message: "hex literal does not fit in 256 bits".to_string(),
        });
    };
    Ok(Num::Int(word))
}

fn col_at(lex: &Lexer<Raw>, start: usize) -> u32 {
    (start.saturating_sub(lex.extras.line_start) + 1) as u32
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Kind {
    Eof,
    Ident,
    Nat,
    Int,
    WeiLit,
    DurationLit,
    String,
    Type,
    Is,
    Record,
    Function,
    View,
    Event,
    Indexed,
    ErrorKw,
    ErrorsKw,
    Raises,
    Payable,
    External,
    Pure,
    Nonreentrant,
    Import,
    Module,
    Use,
    Requires,
    As,
    Private,
    Migrate,
    Deploy,
    Upgradeable,
    Upgrade,
    AtKw,
    Contract,
    Fail,
    Interface,
    Query,
    Emit,
    Defer,
    End,
    CallKw,
    Create,
    Const,
    Var,
    If,
    Then,
    Else,
    For,
    In,
    Do,
    Until,
    Bound,
    Case,
    Of,
    With,
    SkipKw,
    And,
    Or,
    Not,
    Failwith,
    Assert,
    List,
    True,
    False,
    Unit,
    Nil,
    LParen,
    RParen,
    LBrack,
    RBrack,
    LBrace,
    RBrace,
    Assign,
    Colon,
    Semi,
    Comma,
    DotDot,
    Dot,
    Hash,
    Arrow,
    Pipe,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Amp,
    Caret,
    Tilde,
    Shl,
    Shr,
    Neq,
    Eq,
    Le,
    Ge,
    Lt,
    Gt,
    At,
}

pub(crate) struct Token {
    pub kind: Kind,
    pub line: u32,
    pub col: u32,
    pub start: usize,
    pub end: usize,
    pub word: Word,
    pub string: Option<String>,
}

pub(crate) fn tokenize(src: &str) -> Result<Vec<Token>, Error> {
    let mut lex = Raw::lexer(src);
    let mut out = Vec::new();
    while let Some(item) = lex.next() {
        let span = lex.span();
        let line = lex.extras.line;
        let col = (span.start.saturating_sub(lex.extras.line_start) + 1) as u32;
        let raw = match item {
            Ok(raw) => raw,
            Err(LexError::Unexpected) => {
                let ch = src.get(span.clone()).unwrap_or("?");
                return Err(error(line, col, format!("unexpected character `{ch}`")));
            }
            Err(LexError::UnterminatedComment { line, col }) => {
                return Err(error(line, col, "unterminated comment"));
            }
            Err(LexError::UnterminatedString { line, col }) => {
                return Err(error(line, col, "unterminated string"));
            }
            Err(LexError::BadNumber { line, col, message }) => {
                return Err(error(line, col, message));
            }
        };
        if matches!(raw, Raw::Skipped) {
            continue;
        }
        let (kind, word, string) = match raw {
            Raw::Skipped => continue,
            Raw::Ident => (Kind::Ident, Word::from_u64(0), None),
            Raw::Number(Num::Nat(w)) => (Kind::Nat, w, None),
            Raw::Number(Num::Int(w)) => (Kind::Int, w, None),
            Raw::Number(Num::Wei(w)) => (Kind::WeiLit, w, None),
            Raw::Number(Num::Duration(w)) => (Kind::DurationLit, w, None),
            Raw::String(s) => (Kind::String, Word::from_u64(0), Some(s)),
            Raw::Type => (Kind::Type, Word::from_u64(0), None),
            Raw::Is => (Kind::Is, Word::from_u64(0), None),
            Raw::Record => (Kind::Record, Word::from_u64(0), None),
            Raw::Function => (Kind::Function, Word::from_u64(0), None),
            Raw::View => (Kind::View, Word::from_u64(0), None),
            Raw::Event => (Kind::Event, Word::from_u64(0), None),
            Raw::Indexed => (Kind::Indexed, Word::from_u64(0), None),
            Raw::ErrorKw => (Kind::ErrorKw, Word::from_u64(0), None),
            Raw::ErrorsKw => (Kind::ErrorsKw, Word::from_u64(0), None),
            Raw::Raises => (Kind::Raises, Word::from_u64(0), None),
            Raw::Payable => (Kind::Payable, Word::from_u64(0), None),
            Raw::External => (Kind::External, Word::from_u64(0), None),
            Raw::Pure => (Kind::Pure, Word::from_u64(0), None),
            Raw::Nonreentrant => (Kind::Nonreentrant, Word::from_u64(0), None),
            Raw::Import => (Kind::Import, Word::from_u64(0), None),
            Raw::Module => (Kind::Module, Word::from_u64(0), None),
            Raw::Use => (Kind::Use, Word::from_u64(0), None),
            Raw::Requires => (Kind::Requires, Word::from_u64(0), None),
            Raw::As => (Kind::As, Word::from_u64(0), None),
            Raw::Private => (Kind::Private, Word::from_u64(0), None),
            Raw::Migrate => (Kind::Migrate, Word::from_u64(0), None),
            Raw::Deploy => (Kind::Deploy, Word::from_u64(0), None),
            Raw::Upgradeable => (Kind::Upgradeable, Word::from_u64(0), None),
            Raw::Upgrade => (Kind::Upgrade, Word::from_u64(0), None),
            Raw::AtKw => (Kind::AtKw, Word::from_u64(0), None),
            Raw::Contract => (Kind::Contract, Word::from_u64(0), None),
            Raw::Fail => (Kind::Fail, Word::from_u64(0), None),
            Raw::Interface => (Kind::Interface, Word::from_u64(0), None),
            Raw::Query => (Kind::Query, Word::from_u64(0), None),
            Raw::Emit => (Kind::Emit, Word::from_u64(0), None),
            Raw::Defer => (Kind::Defer, Word::from_u64(0), None),
            Raw::End => (Kind::End, Word::from_u64(0), None),
            Raw::CallKw => (Kind::CallKw, Word::from_u64(0), None),
            Raw::Create => (Kind::Create, Word::from_u64(0), None),
            Raw::Const => (Kind::Const, Word::from_u64(0), None),
            Raw::Var => (Kind::Var, Word::from_u64(0), None),
            Raw::If => (Kind::If, Word::from_u64(0), None),
            Raw::Then => (Kind::Then, Word::from_u64(0), None),
            Raw::Else => (Kind::Else, Word::from_u64(0), None),
            Raw::For => (Kind::For, Word::from_u64(0), None),
            Raw::In => (Kind::In, Word::from_u64(0), None),
            Raw::Do => (Kind::Do, Word::from_u64(0), None),
            Raw::Until => (Kind::Until, Word::from_u64(0), None),
            Raw::Bound => (Kind::Bound, Word::from_u64(0), None),
            Raw::Case => (Kind::Case, Word::from_u64(0), None),
            Raw::Of => (Kind::Of, Word::from_u64(0), None),
            Raw::With => (Kind::With, Word::from_u64(0), None),
            Raw::SkipKw => (Kind::SkipKw, Word::from_u64(0), None),
            Raw::And => (Kind::And, Word::from_u64(0), None),
            Raw::Or => (Kind::Or, Word::from_u64(0), None),
            Raw::Not => (Kind::Not, Word::from_u64(0), None),
            Raw::Failwith => (Kind::Failwith, Word::from_u64(0), None),
            Raw::Assert => (Kind::Assert, Word::from_u64(0), None),
            Raw::List => (Kind::List, Word::from_u64(0), None),
            Raw::True => (Kind::True, Word::from_u64(0), None),
            Raw::False => (Kind::False, Word::from_u64(0), None),
            Raw::Unit => (Kind::Unit, Word::from_u64(0), None),
            Raw::Nil => (Kind::Nil, Word::from_u64(0), None),
            Raw::LParen => (Kind::LParen, Word::from_u64(0), None),
            Raw::RParen => (Kind::RParen, Word::from_u64(0), None),
            Raw::LBrack => (Kind::LBrack, Word::from_u64(0), None),
            Raw::RBrack => (Kind::RBrack, Word::from_u64(0), None),
            Raw::LBrace => (Kind::LBrace, Word::from_u64(0), None),
            Raw::RBrace => (Kind::RBrace, Word::from_u64(0), None),
            Raw::Assign => (Kind::Assign, Word::from_u64(0), None),
            Raw::Colon => (Kind::Colon, Word::from_u64(0), None),
            Raw::Semi => (Kind::Semi, Word::from_u64(0), None),
            Raw::Comma => (Kind::Comma, Word::from_u64(0), None),
            Raw::DotDot => (Kind::DotDot, Word::from_u64(0), None),
            Raw::Dot => (Kind::Dot, Word::from_u64(0), None),
            Raw::Hash => (Kind::Hash, Word::from_u64(0), None),
            Raw::Arrow => (Kind::Arrow, Word::from_u64(0), None),
            Raw::Pipe => (Kind::Pipe, Word::from_u64(0), None),
            Raw::Plus => (Kind::Plus, Word::from_u64(0), None),
            Raw::Minus => (Kind::Minus, Word::from_u64(0), None),
            Raw::Star => (Kind::Star, Word::from_u64(0), None),
            Raw::Slash => (Kind::Slash, Word::from_u64(0), None),
            Raw::Percent => (Kind::Percent, Word::from_u64(0), None),
            Raw::Amp => (Kind::Amp, Word::from_u64(0), None),
            Raw::Caret => (Kind::Caret, Word::from_u64(0), None),
            Raw::Tilde => (Kind::Tilde, Word::from_u64(0), None),
            Raw::Shl => (Kind::Shl, Word::from_u64(0), None),
            Raw::Shr => (Kind::Shr, Word::from_u64(0), None),
            Raw::Neq => (Kind::Neq, Word::from_u64(0), None),
            Raw::Eq => (Kind::Eq, Word::from_u64(0), None),
            Raw::Le => (Kind::Le, Word::from_u64(0), None),
            Raw::Ge => (Kind::Ge, Word::from_u64(0), None),
            Raw::Lt => (Kind::Lt, Word::from_u64(0), None),
            Raw::Gt => (Kind::Gt, Word::from_u64(0), None),
            Raw::At => (Kind::At, Word::from_u64(0), None),
        };
        out.push(Token {
            kind,
            line,
            col,
            start: span.start,
            end: span.end,
            word,
            string,
        });
    }
    let line = lex.extras.line;
    let col = (src.len().saturating_sub(lex.extras.line_start) + 1) as u32;
    out.push(Token {
        kind: Kind::Eof,
        line,
        col,
        start: src.len(),
        end: src.len(),
        word: Word::from_u64(0),
        string: None,
    });
    Ok(out)
}

pub(crate) fn kind_name(k: Kind) -> &'static str {
    match k {
        Kind::Eof => "end of file",
        Kind::Ident => "identifier",
        Kind::Nat => "nat",
        Kind::Int => "int",
        Kind::WeiLit => "wei",
        Kind::DurationLit => "duration",
        Kind::String => "string",
        Kind::Type => "`type`",
        Kind::Is => "`is`",
        Kind::Record => "`record`",
        Kind::Function => "`function`",
        Kind::View => "`view`",
        Kind::Event => "`event`",
        Kind::Indexed => "`indexed`",
        Kind::ErrorKw => "`error`",
        Kind::ErrorsKw => "`errors`",
        Kind::Raises => "`raises`",
        Kind::Payable => "`payable`",
        Kind::External => "`external`",
        Kind::Pure => "`pure`",
        Kind::Nonreentrant => "`nonreentrant`",
        Kind::Import => "`import`",
        Kind::Module => "`module`",
        Kind::Use => "`use`",
        Kind::Requires => "`requires`",
        Kind::As => "`as`",
        Kind::Private => "`private`",
        Kind::Migrate => "`migrate`",
        Kind::Deploy => "`deploy`",
        Kind::Upgradeable => "`upgradeable`",
        Kind::Upgrade => "`upgrade`",
        Kind::AtKw => "`at`",
        Kind::Contract => "`contract`",
        Kind::Fail => "`fail`",
        Kind::Interface => "`interface`",
        Kind::Query => "`query`",
        Kind::Emit => "`emit`",
        Kind::Defer => "`defer`",
        Kind::End => "`end`",
        Kind::CallKw => "`call`",
        Kind::Create => "`create`",
        Kind::Const => "`const`",
        Kind::Var => "`var`",
        Kind::If => "`if`",
        Kind::Then => "`then`",
        Kind::Else => "`else`",
        Kind::For => "`for`",
        Kind::In => "`in`",
        Kind::Do => "`do`",
        Kind::Until => "`until`",
        Kind::Bound => "`bound`",
        Kind::Case => "`case`",
        Kind::Of => "`of`",
        Kind::With => "`with`",
        Kind::SkipKw => "`skip`",
        Kind::And => "`and`",
        Kind::Or => "`or`",
        Kind::Not => "`not`",
        Kind::Failwith => "`failwith`",
        Kind::Assert => "`assert`",
        Kind::List => "`list`",
        Kind::True => "`true`",
        Kind::False => "`false`",
        Kind::Unit => "`Unit`",
        Kind::Nil => "`nil`",
        Kind::LParen => "`(`",
        Kind::RParen => "`)`",
        Kind::LBrack => "`[`",
        Kind::RBrack => "`]`",
        Kind::LBrace => "`{`",
        Kind::RBrace => "`}`",
        Kind::Assign => "`:=`",
        Kind::Colon => "`:`",
        Kind::Semi => "`;`",
        Kind::Comma => "`,`",
        Kind::DotDot => "`..`",
        Kind::Dot => "`.`",
        Kind::Hash => "`#`",
        Kind::Arrow => "`->`",
        Kind::Pipe => "`|`",
        Kind::Plus => "`+`",
        Kind::Minus => "`-`",
        Kind::Star => "`*`",
        Kind::Slash => "`/`",
        Kind::Percent => "`%`",
        Kind::Amp => "`&`",
        Kind::Caret => "`^`",
        Kind::Tilde => "`~`",
        Kind::Shl => "`<<`",
        Kind::Shr => "`>>`",
        Kind::Neq => "`=/=`",
        Kind::Eq => "`=`",
        Kind::Le => "`<=`",
        Kind::Ge => "`>=`",
        Kind::Lt => "`<`",
        Kind::Gt => "`>`",
        Kind::At => "`@`",
    }
}
