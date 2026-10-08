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
    Int(Word),
    Wei(Word),
    Duration(Word),
    /// A hex literal past a word's 64 digits: `bytes`, as digits.
    Bytes(String),
}

#[derive(Debug, Clone, PartialEq, Default)]
enum LexError {
    #[default]
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
    BadEscape {
        line: u32,
        col: u32,
        message: String,
    },
}

#[derive(Logos, Debug, Clone)]
#[logos(extras = Extras)]
#[logos(error = LexError)]
enum Raw {
    #[regex(r"[ \t\r]+", logos::skip)]
    #[regex(r"\n", newline)]
    Skipped,

    #[token("(*", comment)]
    Comment,

    #[regex(r"[A-Za-z_][A-Za-z0-9_]*")]
    Ident,

    #[regex(r"0x[0-9a-fA-F_]+", hex_lit)]
    #[regex(r"[0-9][0-9_]*(eth|gwei|wei|seconds|minutes|hours|days)?", number)]
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
    #[token("anonymous")]
    Anonymous,
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
    #[token("**")]
    StarStar,
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

fn comment(lex: &mut Lexer<Raw>) -> Result<(), LexError> {
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
                return Ok(());
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
            let bad = |message: String| LexError::BadEscape { line, col, message };
            out.push(match n {
                'n' => '\n',
                't' => '\t',
                'r' => '\r',
                '0' => '\0',
                '\\' | '"' | '\'' => n,
                'x' => {
                    let hex = lex.remainder().get(..2).filter(|h| is_hex(h)).unwrap_or("");
                    // simplify: \x stops at 7f because string literals are UTF-8; raw bytes use a hex literal.
                    match u8::from_str_radix(hex, 16) {
                        Ok(b) if b < 0x80 => {
                            lex.bump(2);
                            b as char
                        }
                        _ => return Err(bad("`\\x` takes two hex digits from 00 to 7f".into())),
                    }
                }
                'u' => {
                    let rest = lex.remainder();
                    let ch = rest
                        .strip_prefix('{')
                        .and_then(|r| r.split_once('}'))
                        .filter(|(h, _)| (1..=6).contains(&h.len()) && is_hex(h))
                        .and_then(|(h, _)| u32::from_str_radix(h, 16).ok().map(|v| (h.len(), v)))
                        .and_then(|(len, v)| char::from_u32(v).map(|c| (len, c)));
                    match ch {
                        Some((len, c)) => {
                            lex.bump(len + 2);
                            c
                        }
                        None => {
                            return Err(bad("`\\u` takes a code point like `\\u{1F600}`".into()))
                        }
                    }
                }
                _ => return Err(bad(format!("unknown escape `\\{n}`"))),
            });
            continue;
        }
        out.push(ch);
    }
}

fn is_hex(s: &str) -> bool {
    s.bytes().all(|c| c.is_ascii_hexdigit())
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
        NumKind::Plain => word,
    };
    match kind {
        NumKind::Wei(_) => Ok(Num::Wei(word)),
        NumKind::Duration(_) => Ok(Num::Duration(word)),
        NumKind::Plain => Ok(Num::Int(word)),
    }
}

enum NumKind {
    Plain,
    Wei(u64),
    Duration(u64),
}

fn hex_lit(lex: &mut Lexer<Raw>) -> Result<Num, LexError> {
    let line = lex.extras.line;
    let col = col_at(lex, lex.span().start);
    let digits = lex.slice()[2..].replace('_', "");
    if digits.len() > 64 {
        if digits.len() % 2 == 1 {
            return Err(LexError::BadNumber {
                line,
                col,
                message: "a hex literal longer than a word is `bytes`, and needs an even number of digits".to_string(),
            });
        }
        return Ok(Num::Bytes(digits));
    }
    if digits.is_empty() {
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
    Int,
    WeiLit,
    DurationLit,
    HexBytes,
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
    Anonymous,
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
    StarStar,
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
        let raw = item.map_err(|err| lex_error(src, &lex, err))?;
        let (word, string) = match &raw {
            Raw::Skipped | Raw::Comment => continue,
            Raw::Number(Num::Int(w) | Num::Wei(w) | Num::Duration(w)) => (*w, None),
            Raw::Number(Num::Bytes(digits)) => (Word::from_u64(0), Some(digits.clone())),
            Raw::String(s) => (Word::from_u64(0), Some(s.clone())),
            _ => (Word::from_u64(0), None),
        };
        let kind = kind_of(raw);
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PieceKind {
    Token(Kind),
    Comment,
}

pub(crate) struct Piece {
    pub kind: PieceKind,
    pub start: usize,
    pub end: usize,
    /// Newlines in the whitespace gap before this piece. Comments are pieces.
    pub newlines_before: u32,
}

/// Tokens and comments, with the newline count of the gap before each one.
pub(crate) fn pieces(src: &str) -> Result<Vec<Piece>, Error> {
    let mut lex = Raw::lexer(src);
    let mut out = Vec::new();
    let mut prev = 0;
    while let Some(item) = lex.next() {
        let span = lex.span();
        let raw = match item {
            Ok(raw) => raw,
            Err(err) => return Err(lex_error(src, &lex, err)),
        };
        if matches!(raw, Raw::Skipped) {
            continue;
        }
        let kind = match raw {
            Raw::Comment => PieceKind::Comment,
            other => PieceKind::Token(kind_of(other)),
        };
        let newlines_before = src[prev..span.start]
            .bytes()
            .filter(|b| *b == b'\n')
            .count() as u32;
        out.push(Piece {
            kind,
            start: span.start,
            end: span.end,
            newlines_before,
        });
        prev = span.end;
    }
    Ok(out)
}

fn lex_error(src: &str, lex: &Lexer<Raw>, err: LexError) -> Error {
    let span = lex.span();
    let line = lex.extras.line;
    let col = (span.start.saturating_sub(lex.extras.line_start) + 1) as u32;
    match err {
        LexError::Unexpected => {
            let ch = src.get(span.clone()).unwrap_or("?");
            error(line, col, format!("unexpected character `{ch}`"))
        }
        LexError::UnterminatedComment { line, col } => error(line, col, "unterminated comment"),
        LexError::UnterminatedString { line, col } => error(line, col, "unterminated string"),
        LexError::BadNumber { line, col, message } | LexError::BadEscape { line, col, message } => {
            error(line, col, message)
        }
    }
}

fn kind_of(raw: Raw) -> Kind {
    match raw {
        Raw::Skipped | Raw::Comment | Raw::Ident => Kind::Ident,
        Raw::Number(Num::Int(_)) => Kind::Int,
        Raw::Number(Num::Wei(_)) => Kind::WeiLit,
        Raw::Number(Num::Duration(_)) => Kind::DurationLit,
        Raw::Number(Num::Bytes(_)) => Kind::HexBytes,
        Raw::String(_) => Kind::String,
        Raw::Type => Kind::Type,
        Raw::Is => Kind::Is,
        Raw::Record => Kind::Record,
        Raw::Function => Kind::Function,
        Raw::View => Kind::View,
        Raw::Event => Kind::Event,
        Raw::Indexed => Kind::Indexed,
        Raw::Anonymous => Kind::Anonymous,
        Raw::ErrorKw => Kind::ErrorKw,
        Raw::ErrorsKw => Kind::ErrorsKw,
        Raw::Raises => Kind::Raises,
        Raw::Payable => Kind::Payable,
        Raw::External => Kind::External,
        Raw::Pure => Kind::Pure,
        Raw::Nonreentrant => Kind::Nonreentrant,
        Raw::Import => Kind::Import,
        Raw::Module => Kind::Module,
        Raw::Use => Kind::Use,
        Raw::Requires => Kind::Requires,
        Raw::As => Kind::As,
        Raw::Private => Kind::Private,
        Raw::Migrate => Kind::Migrate,
        Raw::Deploy => Kind::Deploy,
        Raw::Upgradeable => Kind::Upgradeable,
        Raw::Upgrade => Kind::Upgrade,
        Raw::AtKw => Kind::AtKw,
        Raw::Contract => Kind::Contract,
        Raw::Fail => Kind::Fail,
        Raw::Interface => Kind::Interface,
        Raw::Query => Kind::Query,
        Raw::Emit => Kind::Emit,
        Raw::Defer => Kind::Defer,
        Raw::End => Kind::End,
        Raw::Create => Kind::Create,
        Raw::Const => Kind::Const,
        Raw::Var => Kind::Var,
        Raw::If => Kind::If,
        Raw::Then => Kind::Then,
        Raw::Else => Kind::Else,
        Raw::For => Kind::For,
        Raw::In => Kind::In,
        Raw::Do => Kind::Do,
        Raw::Until => Kind::Until,
        Raw::Bound => Kind::Bound,
        Raw::Case => Kind::Case,
        Raw::Of => Kind::Of,
        Raw::With => Kind::With,
        Raw::SkipKw => Kind::SkipKw,
        Raw::And => Kind::And,
        Raw::Or => Kind::Or,
        Raw::Not => Kind::Not,
        Raw::Failwith => Kind::Failwith,
        Raw::Assert => Kind::Assert,
        Raw::List => Kind::List,
        Raw::True => Kind::True,
        Raw::False => Kind::False,
        Raw::Unit => Kind::Unit,
        Raw::Nil => Kind::Nil,
        Raw::LParen => Kind::LParen,
        Raw::RParen => Kind::RParen,
        Raw::LBrack => Kind::LBrack,
        Raw::RBrack => Kind::RBrack,
        Raw::LBrace => Kind::LBrace,
        Raw::RBrace => Kind::RBrace,
        Raw::Assign => Kind::Assign,
        Raw::Colon => Kind::Colon,
        Raw::Semi => Kind::Semi,
        Raw::Comma => Kind::Comma,
        Raw::DotDot => Kind::DotDot,
        Raw::Dot => Kind::Dot,
        Raw::Hash => Kind::Hash,
        Raw::Arrow => Kind::Arrow,
        Raw::Pipe => Kind::Pipe,
        Raw::Plus => Kind::Plus,
        Raw::Minus => Kind::Minus,
        Raw::StarStar => Kind::StarStar,
        Raw::Star => Kind::Star,
        Raw::Slash => Kind::Slash,
        Raw::Percent => Kind::Percent,
        Raw::Amp => Kind::Amp,
        Raw::Caret => Kind::Caret,
        Raw::Tilde => Kind::Tilde,
        Raw::Shl => Kind::Shl,
        Raw::Shr => Kind::Shr,
        Raw::Neq => Kind::Neq,
        Raw::Eq => Kind::Eq,
        Raw::Le => Kind::Le,
        Raw::Ge => Kind::Ge,
        Raw::Lt => Kind::Lt,
        Raw::Gt => Kind::Gt,
        Raw::At => Kind::At,
    }
}

pub(crate) fn kind_name(k: Kind) -> &'static str {
    match k {
        Kind::Eof => "end of file",
        Kind::Ident => "identifier",
        Kind::Int => "int",
        Kind::HexBytes => "hex bytes",
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
        Kind::Anonymous => "`anonymous`",
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
        Kind::StarStar => "`**`",
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

#[cfg(test)]
mod tests {
    use super::tokenize;

    fn lit(src: &str) -> Result<String, String> {
        tokenize(src)
            .map(|t| t[0].string.clone().unwrap())
            .map_err(|e| e.message)
    }

    #[test]
    fn string_escapes() {
        assert_eq!(
            lit(r#""\x19Ethereum Signed Message:\n32""#).unwrap(),
            "\x19Ethereum Signed Message:\n32"
        );
        assert_eq!(lit(r#""a\tb\r\0\\\"\'""#).unwrap(), "a\tb\r\0\\\"'");
        assert_eq!(lit(r#""\u{1F600}\u{e9}""#).unwrap(), "\u{1F600}é");
        for bad in [
            r#""\q""#,
            r#""\x8f""#,
            r#""\x+1""#,
            r#""\u{}""#,
            r#""\u{d800}""#,
            r#""\u{+1}""#,
        ] {
            assert!(lit(bad).is_err(), "{bad}");
        }
        assert_eq!(lit(r#""\z""#).unwrap_err(), "unknown escape `\\z`");
    }
}
