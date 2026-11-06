//! Reprint tokens. Line breaks stay; spacing and indent are canonical. A line over its width
//! gets more breaks, outermost structure first, until it fits or nothing is left to break.

use crate::error;
use crate::lex::{self, Kind, Piece, PieceKind};
use crate::Error;

/// `src` in the canonical style, with lines wrapped at `width` columns where they can be.
pub fn format_source(src: &str, width: usize) -> Result<String, Error> {
    let arranged = header(src)?;
    same_tokens(src, &arranged)?;
    let out = render(&arranged, width)?;
    verify(&arranged, &out)?;
    let again = render(&header(&out)?, width)?;
    if again != out {
        return Err(error(0, 0, "formatter is not idempotent"));
    }
    Ok(out)
}

/// The canonical start of each contract and module body, and of a file of top-level
/// declarations: `supports`, then one grouped `use` of the plain uses, then each `use` with
/// `delegated`, `exposing`, or `with`, with blank lines between them. A module's `requires`
/// are grouped the same way. Everything else keeps its order after them.
fn header(src: &str) -> Result<String, Error> {
    let pieces = lex::pieces(src)?;
    let partner = partners(&pieces);
    let mut out = src.to_string();
    let bodies = bodies(&pieces, &partner);
    for scope in bodies.iter().rev() {
        if let Some(text) = arrange(src, &pieces, &partner, scope) {
            out.replace_range(scope.start..scope.end, &text);
        }
    }
    if bodies.iter().any(|scope| !scope.module) {
        return Ok(out);
    }
    let src = out;
    let pieces = lex::pieces(&src)?;
    let partner = partners(&pieces);
    let scope = top(&src, &pieces);
    Ok(match arrange(&src, &pieces, &partner, &scope) {
        Some(text) => format!("{}{text}", &src[..scope.start]),
        None => src,
    })
}

/// Where a quick fix adds `name` to the plain uses of the contract around byte `at`, or of
/// the file's first contract, or of its top-level declarations: after the last name of its
/// grouped `use`, or in a `use` of its own where `lithe fmt` puts one. The insertion's byte
/// and text.
pub fn add_use(src: &str, at: usize, name: &str) -> Option<(usize, String)> {
    let pieces = lex::pieces(src).ok()?;
    let partner = partners(&pieces);
    let contracts: Vec<Scope> = bodies(&pieces, &partner)
        .into_iter()
        .filter(|scope| !scope.module)
        .collect();
    let scope = match contracts
        .iter()
        .position(|scope| (scope.start..=scope.end).contains(&at))
    {
        Some(k) => contracts.into_iter().nth(k)?,
        None => match contracts.into_iter().next() {
            Some(first) => first,
            None => top(src, &pieces),
        },
    };
    let heads = heads(src, &pieces, &partner, &scope);
    if let Some(head) = heads.iter().find(|head| head.names.is_some()) {
        return Some((head.names_end, format!(", {name}")));
    }
    let indent = (scope.from..scope.to)
        .find(|&i| token_kind(&pieces[i]).is_some())
        .map_or(if scope.lead == "\n" { 2 } else { 0 }, |i| {
            column(src, pieces[i].start)
        });
    let line = format!("{}use {name};", " ".repeat(indent));
    if let Some(supports) = heads.iter().rfind(|head| head.rank == 0) {
        return Some((supports.cut.1, format!("\n\n{line}")));
    }
    let text = match scope.lead {
        "" => format!("{line}\n\n"),
        "\n" if !src[scope.start..scope.end].trim().is_empty() => format!("\n{line}\n"),
        lead => format!("{lead}{line}"),
    };
    Some((scope.start, text))
}

/// The bodies of the file's contracts and modules.
fn bodies(pieces: &[Piece], partner: &[Option<usize>]) -> Vec<Scope> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < pieces.len() {
        let kind = token_kind(&pieces[i]);
        if matches!(kind, Some(Kind::Contract | Kind::Module)) {
            if let Some((open, close)) = body_of(pieces, partner, i) {
                out.push(Scope {
                    from: open + 1,
                    to: close,
                    start: pieces[open].end,
                    end: pieces[close].start,
                    lead: "\n",
                    module: kind == Some(Kind::Module),
                });
                i = close + 1;
                continue;
            }
        }
        i = match (kind, partner[i]) {
            (Some(Kind::LParen | Kind::LBrack | Kind::LBrace), Some(close)) => close + 1,
            _ => i + 1,
        };
    }
    out
}

/// A file of top-level declarations, whose header follows the imports.
fn top(src: &str, pieces: &[Piece]) -> Scope {
    let tok = |j: usize| pieces.get(j).and_then(token_kind);
    let first = (0..pieces.len())
        .find(|&j| tok(j).is_some())
        .unwrap_or(pieces.len());
    let mut last = None;
    let mut j = first;
    while tok(j) == Some(Kind::Import) {
        let mut k = next_token(pieces, j);
        if tok(k) == Some(Kind::String) {
            k = next_token(pieces, k);
        }
        if tok(k) == Some(Kind::Ident) && &src[pieces[k].start..pieces[k].end] == "as" {
            k = next_token(pieces, next_token(pieces, k));
        }
        if tok(k) == Some(Kind::Semi) {
            k = next_token(pieces, k);
        }
        last = Some(prev_token(pieces, k.min(pieces.len())));
        j = k;
    }
    let (from, start, lead) = match last {
        Some(l) => (l + 1, pieces[l].end, "\n\n"),
        None if first > 0 && first < pieces.len() && pieces[first].newlines_before > 1 => {
            (first, pieces[first - 1].end, "\n\n")
        }
        None => (0, 0, ""),
    };
    Scope {
        from,
        to: pieces.len(),
        start,
        end: src.len(),
        lead,
        module: false,
    }
}

/// The braces of the body of the contract or module whose keyword is at `at`.
fn body_of(pieces: &[Piece], partner: &[Option<usize>], at: usize) -> Option<(usize, usize)> {
    let mut j = next_token(pieces, at);
    loop {
        match pieces.get(j).and_then(token_kind)? {
            Kind::LBrace => return Some((j, partner[j]?)),
            Kind::LParen => j = next_token(pieces, partner[j]?),
            Kind::Ident | Kind::Dot | Kind::Is | Kind::Upgradeable => j = next_token(pieces, j),
            _ => return None,
        }
    }
}

/// The pieces `from..to` of a body, which spans the bytes `start..end`.
struct Scope {
    from: usize,
    to: usize,
    start: usize,
    end: usize,
    /// What goes before the header: a line break after a brace, a blank line after imports.
    lead: &'static str,
    module: bool,
}

/// A `supports`, `use`, or `requires` declaration, with the comments on the lines just above
/// it and after it on its own line.
struct Head {
    /// `supports` first, then plain uses and `requires`, then the uses that say more.
    rank: u8,
    /// The names of a plain declaration that has no comment, which join the grouped one.
    names: Option<Vec<String>>,
    /// The end of its last name.
    names_end: usize,
    text: String,
    /// The bytes it leaves behind: from the end of what precedes it to its own end.
    cut: (usize, usize),
}

/// The header declarations of `scope`, in the order written.
fn heads(src: &str, pieces: &[Piece], partner: &[Option<usize>], scope: &Scope) -> Vec<Head> {
    let mut heads = Vec::new();
    let mut prev: Option<usize> = None;
    let mut i = scope.from;
    while i < scope.to {
        let Some(kind) = token_kind(&pieces[i]) else {
            i += 1;
            continue;
        };
        let fresh = pieces[i].newlines_before > 0
            || prev.is_none_or(|p| {
                matches!(
                    token_kind(&pieces[p]),
                    Some(Kind::Semi | Kind::LBrace | Kind::RBrace)
                )
            });
        if fresh {
            if let Some((head, last)) = head_at(src, pieces, partner, scope, i) {
                heads.push(head);
                prev = Some(last);
                i = last + 1;
                continue;
            }
        }
        let close = match kind {
            Kind::LParen | Kind::LBrack | Kind::LBrace => partner[i].unwrap_or(i),
            _ => i,
        };
        prev = Some(close);
        i = close + 1;
    }
    heads
}

/// `scope`'s text with its header in canonical form, or `None` when it has no header.
fn arrange(
    src: &str,
    pieces: &[Piece],
    partner: &[Option<usize>],
    scope: &Scope,
) -> Option<String> {
    let heads = heads(src, pieces, partner, scope);
    if heads.is_empty() {
        return None;
    }
    let mut rest = String::new();
    let mut at = scope.start;
    for head in &heads {
        rest.push_str(&src[at..head.cut.0]);
        at = head.cut.1;
    }
    rest.push_str(&src[at..scope.end]);
    let rest = match rest.find(|c: char| !c.is_whitespace()) {
        Some(k) => &rest[rest[..k].rfind('\n').map_or(0, |n| n + 1)..],
        None => "",
    };
    let ranked = |rank: u8| heads.iter().filter(move |head| head.rank == rank);
    let mut blocks = Vec::new();
    let supports: Vec<&str> = ranked(0).map(|head| head.text.as_str()).collect();
    if !supports.is_empty() {
        blocks.push(supports.join("\n"));
    }
    let names: Vec<&str> = ranked(1)
        .filter_map(|head| head.names.as_ref())
        .flatten()
        .map(String::as_str)
        .collect();
    let mut plain = Vec::new();
    if !names.is_empty() {
        let word = if scope.module { "requires" } else { "use" };
        plain.push(format!("{word} {};", names.join(", ")));
    }
    plain.extend(
        ranked(1)
            .filter(|head| head.names.is_none())
            .map(|head| head.text.clone()),
    );
    if !plain.is_empty() {
        blocks.push(plain.join("\n"));
    }
    blocks.extend(ranked(2).map(|head| head.text.clone()));
    let mut out = format!("{}{}", scope.lead, blocks.join("\n\n"));
    if rest.is_empty() {
        out.push('\n');
    } else {
        out.push_str("\n\n");
        out.push_str(rest);
    }
    Some(out)
}

/// The header declaration whose keyword is at `i`, and its last piece.
fn head_at(
    src: &str,
    pieces: &[Piece],
    partner: &[Option<usize>],
    scope: &Scope,
    i: usize,
) -> Option<(Head, usize)> {
    let tok = |j: usize| (j < scope.to).then(|| token_kind(&pieces[j])).flatten();
    let text = |j: usize| &src[pieces[j].start..pieces[j].end];
    let next = |j: usize| next_token(pieces, j);
    let word = text(i);
    let supports = !scope.module && tok(i) == Some(Kind::Ident) && word == "supports";
    let wanted = if scope.module {
        tok(i) == Some(Kind::Requires)
    } else {
        tok(i) == Some(Kind::Use) || (supports && tok(next(i)) == Some(Kind::Ident))
    };
    if !wanted {
        return None;
    }
    // `A.B` from the identifier at `j`: its text, and its last piece.
    let dotted = |j: usize| -> Option<(String, usize)> {
        tok(j).filter(|&k| k == Kind::Ident)?;
        let mut name = text(j).to_string();
        let mut end = j;
        while tok(next(end)) == Some(Kind::Dot) && tok(next(next(end))) == Some(Kind::Ident) {
            end = next(next(end));
            name.push('.');
            name.push_str(text(end));
        }
        Some((name, end))
    };
    let mut names = Vec::new();
    let mut last;
    let mut j = next(i);
    loop {
        let (name, end) = dotted(j)?;
        names.push(name);
        last = end;
        j = next(end);
        if tok(j) != Some(Kind::Comma) {
            break;
        }
        j = next(j);
    }
    let names_end = pieces[last].end;
    let mut plain = true;
    let is_word = |j: usize, w: &str| tok(j) == Some(Kind::Ident) && text(j) == w;
    if !supports && !scope.module {
        if is_word(j, crate::parse::DELEGATED) {
            plain = false;
            last = j;
            j = next(j);
        }
        if is_word(j, "exposing") {
            plain = false;
            j = next(j);
            loop {
                last = match tok(j) {
                    Some(Kind::LBrace) => partner[j]?,
                    _ => dotted(j)?.1,
                };
                j = next(last);
                if tok(j) != Some(Kind::Comma) {
                    break;
                }
                j = next(j);
            }
        }
        if tok(j) == Some(Kind::With) && tok(next(j)) == Some(Kind::LBrace) {
            plain = false;
            last = partner[next(j)]?;
            j = next(last);
        }
    }
    if tok(j) == Some(Kind::Semi) {
        last = j;
    }
    let own_line = |k: usize| {
        let from = line_start(src, pieces[k].start);
        src[from..pieces[k].start].trim().is_empty()
    };
    let mut first = i;
    while first > scope.from
        && pieces[first - 1].kind == PieceKind::Comment
        && pieces[first].newlines_before == 1
        && own_line(first - 1)
    {
        first -= 1;
    }
    while last + 1 < scope.to
        && pieces[last + 1].kind == PieceKind::Comment
        && pieces[last + 1].newlines_before == 0
    {
        last += 1;
    }
    let commented = pieces[first..=last]
        .iter()
        .any(|piece| piece.kind == PieceKind::Comment);
    let cut_from = if first > scope.from {
        pieces[first - 1].end
    } else {
        scope.start
    };
    let head = Head {
        rank: match (supports, plain) {
            (true, _) => 0,
            (false, true) => 1,
            (false, false) => 2,
        },
        names: (plain && !supports && !commented).then_some(names),
        names_end,
        text: format!(
            "{}{}",
            " ".repeat(column(src, pieces[first].start)),
            &src[pieces[first].start..pieces[last].end]
        ),
        cut: (cut_from, pieces[last].end),
    };
    Some((head, last))
}

/// The header pass only moves declarations, and merges `use A; use B;` into `use A, B;`, so
/// every other token and comment is still there.
fn same_tokens(src: &str, out: &str) -> Result<(), Error> {
    let kept = |text: &str| -> Result<Vec<String>, Error> {
        let mut out: Vec<String> = lex::pieces(text)?
            .iter()
            .filter(|piece| {
                !matches!(
                    token_kind(piece),
                    Some(Kind::Use | Kind::Requires | Kind::Semi | Kind::Comma)
                )
            })
            .map(|piece| text[piece.start..piece.end].trim().to_string())
            .collect();
        out.sort();
        Ok(out)
    };
    if kept(src)? != kept(out)? {
        return Err(error(0, 0, "formatter changed the declarations"));
    }
    Ok(())
}

fn render(src: &str, max: usize) -> Result<String, Error> {
    let mut pieces = lex::pieces(src)?;
    // A `raises` list is refilled, not kept as written, so it never ends up with a short line.
    for i in 1..pieces.len() {
        if pieces[i - 1].kind != PieceKind::Comment
            && token_kind(&pieces[i]) == Some(Kind::Pipe)
            && in_raises(src, &pieces, i)
        {
            pieces[i].newlines_before = 0;
        }
    }
    let partner = partners(&pieces);
    break_use_with(src, &mut pieces, &partner);
    let mut stuck = Vec::new();
    loop {
        let (out, starts) = print(src, &pieces);
        let Some((a, b)) = long_line(&out, &starts, &stuck, max) else {
            return align_fields(&out, max);
        };
        let from = line_start(&out, starts[a]);
        let options = options(src, &pieces, &partner, &out, &starts, from, a, b, max);
        let pick = options
            .iter()
            .find(|o| fits(src, &mut pieces, o, a, b, max))
            .or(options.first());
        match pick {
            Some(o) => {
                for &i in o {
                    pieces[i].newlines_before = pieces[i].newlines_before.max(1);
                }
            }
            None => stuck.push(a),
        }
    }
}

/// The `:` of record fields on consecutive lines in one column. A blank line, or a field that
/// shares its line, starts a new run. A run whose padding would push a line past `max` stays
/// unaligned.
fn align_fields(out: &str, max: usize) -> Result<String, Error> {
    let pieces = lex::pieces(out)?;
    let partner = partners(&pieces);
    let mut colons = Vec::new();
    for (i, piece) in pieces.iter().enumerate() {
        let o = next_token(&pieces, i);
        if token_kind(piece) != Some(Kind::Record)
            || o == pieces.len()
            || token_kind(&pieces[o]) != Some(Kind::LBrace)
        {
            continue;
        }
        let Some(c) = partner[o] else { continue };
        let mut run: Vec<usize> = Vec::new();
        let mut j = o + 1;
        while j < c {
            let start = next_token(&pieces, j - 1);
            if start >= c {
                break;
            }
            let blank = pieces[j..=start].iter().any(|p| p.newlines_before > 1);
            let mut colon = None;
            j = start;
            while j < c && token_kind(&pieces[j]) != Some(Kind::Semi) {
                match token_kind(&pieces[j]) {
                    Some(Kind::Colon) if colon.is_none() => colon = Some(j),
                    Some(Kind::LParen | Kind::LBrack | Kind::LBrace) => j = partner[j].unwrap_or(j),
                    _ => {}
                }
                j += 1;
            }
            let ends_line = j >= c
                || pieces[j + 1..=next_token(&pieces, j)]
                    .iter()
                    .any(|p| p.newlines_before > 0);
            j += 1;
            let at = pieces[start].start;
            let own_line = colon.filter(|&k| {
                ends_line
                    && out[line_start(out, at)..at].trim().is_empty()
                    && !out[at..pieces[k].start].contains('\n')
            });
            if blank || own_line.is_none() {
                colons.push(std::mem::take(&mut run));
            }
            run.extend(own_line.map(|k| pieces[k].start));
        }
        colons.push(run);
    }
    let col = |at: usize| width(&out[line_start(out, at)..at]);
    let line = |at: usize| {
        let end = out[at..].find('\n').map_or(out.len(), |n| at + n);
        width(&out[line_start(out, at)..end])
    };
    let mut pads: Vec<(usize, usize)> = colons
        .iter()
        .filter_map(|run| {
            let to = run.iter().map(|&at| col(at)).max().unwrap_or(0);
            let fits = run.iter().all(|&at| line(at) + to - col(at) <= max);
            fits.then(|| run.iter().map(move |&at| (at, to - col(at))))
        })
        .flatten()
        .collect();
    pads.sort();
    let mut text = out.to_string();
    for &(at, n) in pads.iter().rev() {
        text.insert_str(at, &" ".repeat(n));
    }
    Ok(text)
}

fn print(src: &str, pieces: &[Piece]) -> (String, Vec<usize>) {
    let mut p = Printer {
        src,
        out: String::new(),
        groups: Vec::new(),
        line_indent: 0,
        prev_indent: 0,
        decl_indent: 0,
        raises_indent: 0,
        prev_line_last: None,
        line_last: None,
        prev_clause: None,
        line_clause: None,
        prev_kind: None,
        in_raises: false,
        tight: false,
        line_head: String::new(),
        recent: Vec::new(),
        forall_dot: false,
        col: 0,
        starts: Vec::new(),
        ifs: Vec::new(),
        list_indent: None,
        for_indent: None,
    };
    for piece in pieces {
        p.emit(piece);
    }
    if !p.out.ends_with('\n') {
        p.out.push('\n');
    }
    while p.out.ends_with("\n\n") {
        p.out.pop();
    }
    (p.out, p.starts)
}

/// The first line over its width that is not known to be unbreakable, as its first and last piece.
fn long_line(out: &str, starts: &[usize], stuck: &[usize], max: usize) -> Option<(usize, usize)> {
    let mut a = 0;
    for i in 1..=starts.len() {
        if i < starts.len() && !out[starts[i - 1]..starts[i]].contains('\n') {
            continue;
        }
        let from = line_start(out, starts[a]);
        let to = out[starts[a]..]
            .find('\n')
            .map_or(out.len(), |n| starts[a] + n);
        if width(&out[from..to]) > max && !stuck.contains(&a) {
            return Some((a, i - 1));
        }
        a = i;
    }
    None
}

fn line_start(out: &str, pos: usize) -> usize {
    out[..pos].rfind('\n').map_or(0, |i| i + 1)
}

fn width(line: &str) -> usize {
    line.chars().count()
}

/// Whether breaking before `breaks` makes every line of pieces `a..=b` fit.
fn fits(src: &str, pieces: &mut [Piece], breaks: &[usize], a: usize, b: usize, max: usize) -> bool {
    let saved: Vec<u32> = breaks.iter().map(|&i| pieces[i].newlines_before).collect();
    for &i in breaks {
        pieces[i].newlines_before = pieces[i].newlines_before.max(1);
    }
    let (out, starts) = print(src, pieces);
    for (&i, n) in breaks.iter().zip(saved) {
        pieces[i].newlines_before = n;
    }
    let from = line_start(&out, starts[a]);
    let to = out[starts[b]..]
        .find('\n')
        .map_or(out.len(), |n| starts[b] + n);
    out[from..to].lines().all(|line| width(line) <= max)
}

fn partners(pieces: &[Piece]) -> Vec<Option<usize>> {
    let mut out = vec![None; pieces.len()];
    let mut open = Vec::new();
    for (i, piece) in pieces.iter().enumerate() {
        match token_kind(piece) {
            Some(Kind::LParen | Kind::LBrack | Kind::LBrace) => open.push(i),
            Some(Kind::RParen | Kind::RBrack | Kind::RBrace) => {
                if let Some(o) = open.pop() {
                    out[o] = Some(i);
                    out[i] = Some(o);
                }
            }
            _ => {}
        }
    }
    out
}

/// A `use M ... with { ... }` block holds one binding per line, and closes on its own.
fn break_use_with(src: &str, pieces: &mut [Piece], partner: &[Option<usize>]) {
    for i in 0..pieces.len() {
        if token_kind(&pieces[i]) != Some(Kind::Use) {
            continue;
        }
        let mut j = i + 1;
        let block = loop {
            match pieces.get(j).map(|p| (token_kind(p), partner[j])) {
                Some((None | Some(Kind::Ident | Kind::Dot | Kind::Comma), _)) => j += 1,
                Some((Some(Kind::LBrace), Some(close))) => j = close + 1,
                Some((Some(Kind::With), _))
                    if pieces.get(j + 1).and_then(token_kind) == Some(Kind::LBrace) =>
                {
                    break partner[j + 1].map(|close| (j + 1, close));
                }
                _ => break None,
            }
        };
        let Some((open, close)) = block else {
            continue;
        };
        let mut k = open + 1;
        while k < close {
            let piece = &pieces[k];
            let word = &src[piece.start..piece.end];
            if token_kind(piece) == Some(Kind::Ident) && matches!(word, "guard" | "hook") {
                pieces[k].newlines_before = pieces[k].newlines_before.max(1);
            }
            k = match (token_kind(&pieces[k]), partner[k]) {
                (Some(Kind::LParen | Kind::LBrack | Kind::LBrace), Some(end)) => end + 1,
                _ => k + 1,
            };
        }
        if close > open + 1 {
            pieces[close].newlines_before = pieces[close].newlines_before.max(1);
        }
    }
}

/// Ways to break line `a..=b`, each a set of pieces to start a new line at, best first.
/// Only the outermost nesting level that offers a break is used.
fn options(
    src: &str,
    pieces: &[Piece],
    partner: &[Option<usize>],
    out: &str,
    starts: &[usize],
    from: usize,
    a: usize,
    b: usize,
    max: usize,
) -> Vec<Vec<usize>> {
    let kind = |i: usize| token_kind(&pieces[i]);
    let toks: Vec<usize> = (a..=b).filter(|&i| kind(i).is_some()).collect();
    let mut depth = Vec::new();
    let mut d = 0i32;
    for &i in &toks {
        let k = kind(i).expect("token");
        if matches!(k, Kind::RParen | Kind::RBrack | Kind::RBrace) {
            d -= 1;
        }
        depth.push(d);
        if matches!(k, Kind::LParen | Kind::LBrack | Kind::LBrace) {
            d += 1;
        }
    }
    let (Some(&lo), Some(&hi)) = (depth.iter().min(), depth.iter().max()) else {
        return Vec::new();
    };
    for d in lo..=hi {
        let at: Vec<usize> = toks
            .iter()
            .zip(&depth)
            .filter(|(_, &e)| e == d)
            .map(|(&i, _)| i)
            .collect();
        let inner: Vec<usize> = at.iter().copied().filter(|&i| i != toks[0]).collect();
        let is = |i: usize, k: Kind| kind(i) == Some(k);
        let mut opts = Vec::new();
        let header = at.iter().any(|&i| is(i, Kind::Function));
        if header {
            if let Some(&r) = inner.iter().find(|&&i| is(i, Kind::Raises)) {
                let mut o = vec![r];
                o.extend(inner.iter().copied().find(|&i| i > r && is(i, Kind::Is)));
                return vec![o];
            }
            if let Some(&i) = inner.iter().find(|&&i| is(i, Kind::Is)) {
                if i < b && !is(i + 1, Kind::LBrace) {
                    opts.push(vec![i + 1]);
                }
            }
        }
        let pipes: Vec<usize> = inner
            .iter()
            .copied()
            .filter(|&i| is(i, Kind::Pipe) && in_raises(src, pieces, i))
            .collect();
        if let Some(&first) = pipes.first() {
            let fit = pipes
                .iter()
                .rev()
                .find(|&&i| width(out[from..starts[i]].trim_end()) <= max);
            opts.push(vec![*fit.unwrap_or(&first)]);
        }
        let commas: Vec<usize> = inner
            .iter()
            .copied()
            .filter(|&i| is(i, Kind::Comma) && in_names(src, pieces, i))
            .collect();
        if let Some(&first) = commas.first() {
            let fit = commas
                .iter()
                .rev()
                .find(|&&i| width(out[from..starts[i]].trim_end()) < max);
            opts.push(vec![next_token(pieces, *fit.unwrap_or(&first))]);
        }
        let ops: Vec<(usize, u8)> = inner
            .iter()
            .filter_map(|&i| binary(pieces, i).map(|p| (i, p)))
            .collect();
        if let Some(loose) = ops.iter().map(|o| o.1).min() {
            opts.push(ops.iter().filter(|o| o.1 == loose).map(|o| o.0).collect());
        }
        let mut groups: Vec<usize> = at
            .iter()
            .copied()
            .filter(|&i| {
                partner[i].is_some_and(|c| c <= b && next_token(pieces, i) < c)
                    && match kind(i) {
                        Some(Kind::LParen | Kind::LBrace) => true,
                        Some(Kind::LBrack) => !index(pieces, i),
                        _ => false,
                    }
            })
            .collect();
        if !header {
            groups.reverse();
        }
        groups.sort_by_key(|&i| !is(i, Kind::LBrace));
        for o in groups {
            opts.push(group_breaks(pieces, partner, o));
        }
        if let Some(&i) = inner
            .iter()
            .find(|&&i| (is(i, Kind::Assign) || is(i, Kind::OpAssign)) && i < b)
        {
            let line = out[from..].lines().next().unwrap_or("");
            let indent = line.len() - line.trim_start().len();
            let rest = &out[starts[i + 1]..from + line.len()];
            if width(out[from..starts[i + 1]].trim_end()) <= max && indent + 2 + width(rest) <= max
            {
                opts.push(vec![i + 1]);
            }
        }
        if !opts.is_empty() {
            return opts;
        }
    }
    Vec::new()
}

/// One element per line. A paren or bracket group whose only element ends in another group
/// breaks that group instead: `f(g(` … `))`.
fn group_breaks(pieces: &[Piece], partner: &[Option<usize>], o: usize) -> Vec<usize> {
    let c = partner[o].expect("closed group");
    let top = top_level(pieces, o, c);
    let kind = |i: usize| token_kind(&pieces[i]);
    if kind(o) != Some(Kind::LBrace) {
        let last = prev_token(pieces, c);
        let single = top.iter().all(|&i| {
            !matches!(kind(i), Some(Kind::Comma | Kind::Semi)) && binary(pieces, i).is_none()
        });
        if single && kind(last) == Some(Kind::RParen) {
            if let Some(inner) = partner[last].filter(|&p| next_token(pieces, p) < last) {
                return group_breaks(pieces, partner, inner);
            }
        }
    }
    let arms = kind(o) == Some(Kind::LBrace)
        && (kind(prev_token(pieces, o)) == Some(Kind::Of)
            || kind(next_token(pieces, o)) == Some(Kind::Pipe));
    let mut out = vec![o + 1];
    for i in top {
        match kind(i) {
            Some(Kind::Pipe) if arms => out.push(i),
            Some(Kind::Semi) if !arms => out.push(i + 1),
            Some(Kind::Comma) if kind(o) != Some(Kind::LBrace) => out.push(i + 1),
            _ => {}
        }
    }
    out.push(c);
    out
}

/// Tokens strictly inside the group `o..c`, not nested deeper.
fn top_level(pieces: &[Piece], o: usize, c: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut d = 0;
    for i in o + 1..c {
        match token_kind(&pieces[i]) {
            Some(Kind::RParen | Kind::RBrack | Kind::RBrace) => d -= 1,
            Some(_) if d == 0 => out.push(i),
            _ => {}
        }
        if matches!(
            token_kind(&pieces[i]),
            Some(Kind::LParen | Kind::LBrack | Kind::LBrace)
        ) {
            d += 1;
        }
    }
    out
}

/// An index or slice, `a[i]`, which is never broken.
fn index(pieces: &[Piece], i: usize) -> bool {
    let prev = token_kind(&pieces[prev_token(pieces, i)]);
    matches!(prev, Some(Kind::Ident | Kind::RParen | Kind::RBrack))
}

fn next_token(pieces: &[Piece], i: usize) -> usize {
    (i + 1..pieces.len())
        .find(|&j| token_kind(&pieces[j]).is_some())
        .unwrap_or(pieces.len())
}

fn prev_token(pieces: &[Piece], i: usize) -> usize {
    (0..i)
        .rev()
        .find(|&j| token_kind(&pieces[j]).is_some())
        .unwrap_or(i)
}

/// The binding power of a binary operator, looser lower, as the parser ranks them. `|` is
/// left out: it also separates case arms and raised errors. A record field's `=` is not one.
fn binary(pieces: &[Piece], i: usize) -> Option<u8> {
    let kind = token_kind(&pieces[i])?;
    let prev = (i > 0).then(|| prev_token(pieces, i)).filter(|&p| p != i);
    let prev_kind = prev.and_then(|p| token_kind(&pieces[p]));
    Some(match kind {
        Kind::Or => 1,
        Kind::And => 3,
        Kind::Eq => {
            let before = prev
                .filter(|&p| p > 0)
                .map(|p| token_kind(&pieces[prev_token(pieces, p)]));
            let field = prev_kind == Some(Kind::Ident)
                && matches!(before, None | Some(Some(Kind::LBrace | Kind::Semi)));
            if field {
                return None;
            }
            5
        }
        Kind::Neq | Kind::Lt | Kind::Gt | Kind::Le | Kind::Ge => 5,
        Kind::Caret => 9,
        Kind::Amp => 11,
        Kind::Shl | Kind::Shr => 15,
        Kind::Plus => 17,
        Kind::Minus if !unary_minus(prev_kind) => 17,
        Kind::Star | Kind::Slash | Kind::Percent => 19,
        Kind::StarStar => 23,
        _ => return None,
    })
}

/// Whether `|` at `i` separates the errors of a `raises` clause.
fn in_raises(src: &str, pieces: &[Piece], i: usize) -> bool {
    for j in (0..i).rev() {
        match token_kind(&pieces[j]) {
            Some(Kind::Raises) => return true,
            // `raises E when a | b` in a spec block: the rest is an expression.
            Some(Kind::Ident) if &src[pieces[j].start..pieces[j].end] == "when" => return false,
            Some(Kind::Ident | Kind::Pipe | Kind::Dot) | None => {}
            Some(_) => return false,
        }
    }
    false
}

/// Whether the `,` at `i` separates the names of a `use`, `requires`, or `supports`.
fn in_names(src: &str, pieces: &[Piece], i: usize) -> bool {
    for j in (0..i).rev() {
        match token_kind(&pieces[j]) {
            Some(Kind::Use | Kind::Requires) => return true,
            Some(Kind::Ident) if &src[pieces[j].start..pieces[j].end] == "supports" => return true,
            Some(Kind::Ident | Kind::Dot | Kind::Comma) | None => {}
            Some(_) => return false,
        }
    }
    false
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Open {
    /// Parens, brackets, and `case` braces: every inner line shares one indent.
    Flat,
    /// Blocks, including the body after `-> {`.
    Block,
}

struct Group {
    content: usize,
    close: usize,
    open: Open,
    square: bool,
    /// A spec block's braces, whose `raises` lines are clauses, not a header's.
    spec: bool,
}

/// An `if` still waiting for its `else`.
struct OpenIf {
    /// The indent of the line with the `if`. An `else` that starts a line lines up with it.
    indent: usize,
    /// How many groups are open around it.
    depth: usize,
}

struct Printer<'a> {
    src: &'a str,
    out: String,
    groups: Vec<Group>,
    line_indent: usize,
    prev_indent: usize,
    decl_indent: usize,
    /// Column of the `raises` keyword. A following `|` line is two past it.
    raises_indent: usize,
    prev_line_last: Option<Kind>,
    line_last: Option<Kind>,
    prev_clause: Option<Kind>,
    line_clause: Option<Kind>,
    prev_kind: Option<Kind>,
    in_raises: bool,
    /// Previous token was a prefix (`-`, `~`, `@`) that sticks to the next token.
    tight: bool,
    /// The first token of the line being printed.
    line_head: String,
    /// The last few tokens, for `forall x : T . e`, whose `.` is spaced.
    recent: Vec<(Kind, String)>,
    /// The token just printed is a `forall`'s `.`.
    forall_dot: bool,
    col: usize,
    /// Output offset of each piece.
    starts: Vec<usize>,
    ifs: Vec<OpenIf>,
    /// The indent of a `use`, `requires`, or `supports` line whose names go on.
    list_indent: Option<usize>,
    /// The indent of a `for` whose `do` is still to come. Its `invariant` lines are two past
    /// it, and a `do` that starts a line lines up with it.
    for_indent: Option<usize>,
}

impl Printer<'_> {
    fn emit(&mut self, piece: &Piece) {
        let breaks = breaks(piece, self.prev_kind);
        let kind = token_kind(piece);
        if breaks > 0 {
            self.out.push_str(&"\n".repeat(breaks as usize));
            self.col = 0;
            if kind.is_some() {
                self.prev_line_last = self.line_last;
                self.prev_indent = self.line_indent;
                self.prev_clause = self.line_clause;
                self.line_last = None;
                self.line_clause = None;
            }
        }
        let bol = self.col == 0;
        if bol {
            let word = match piece.kind {
                PieceKind::Token(_) => &self.src[piece.start..piece.end],
                PieceKind::Comment => "",
            };
            let indent = self.indent_for(kind, breaks >= 2, word);
            if kind.is_some() {
                self.line_indent = indent;
            }
            self.push_indent(indent);
        } else if self.needs_space(piece, kind) {
            self.out.push(' ');
            self.col += 1;
        }
        self.starts.push(self.out.len());
        match piece.kind {
            PieceKind::Comment => self.emit_comment(piece),
            PieceKind::Token(_) => {
                let text = &self.src[piece.start..piece.end];
                if bol {
                    self.line_head = text.to_string();
                }
                let kind_now = kind.expect("token");
                self.forall_dot = kind_now == Kind::Dot && self.before_forall_dot();
                self.recent.push((kind_now, text.to_string()));
                if self.recent.len() > 4 {
                    self.recent.remove(0);
                }
                self.out.push_str(text);
                self.col += text.len();
                let kind = kind.expect("token");
                self.tight = matches!(kind, Kind::Tilde | Kind::At)
                    || (kind == Kind::Minus && unary_minus(self.prev_kind));
                self.on_token(kind, bol);
                self.line_last = Some(kind);
                self.prev_kind = Some(kind);
                if bol && clause(kind) {
                    self.line_clause = Some(kind);
                }
            }
        }
    }

    fn push_indent(&mut self, indent: usize) {
        self.out.push_str(&" ".repeat(indent));
        self.col += indent;
    }

    fn indent_for(&self, kind: Option<Kind>, blank: bool, word: &str) -> usize {
        let Some(kind) = kind else {
            return self.structural();
        };
        if matches!(kind, Kind::RBrace | Kind::RParen | Kind::RBrack) {
            return self.groups.last().map(|g| g.close).unwrap_or(0);
        }
        if kind == Kind::Is {
            return self.decl_indent;
        }
        if let (Some(indent), Some(Kind::Comma)) = (self.list_indent, self.prev_kind) {
            return indent + 2;
        }
        if let Some(indent) = self.for_indent {
            if kind == Kind::Do {
                return indent;
            }
            if kind == Kind::Ident && word == "invariant" {
                return indent + 2;
            }
        }
        if kind == Kind::Else {
            if let Some(open) = self.open_if() {
                return self.ifs[open].indent;
            }
        }
        if kind == Kind::Raises && self.groups.last().is_some_and(|g| g.spec) {
            return self.structural();
        }
        if kind == Kind::Raises {
            return self.decl_indent + 2;
        }
        if kind == Kind::Pipe && self.in_raises {
            return self.raises_indent + 2;
        }
        if kind == Kind::Then {
            if self.prev_clause.is_some_and(|prev| sibling(prev, kind)) {
                return self.prev_indent;
            }
            return self.prev_indent + 2;
        }
        if kind == Kind::LBrace && self.prev_kind == Some(Kind::Of) {
            return self.prev_indent;
        }
        // A branch's body on its own line belongs to the branch, even `fail`.
        if !blank && matches!(self.prev_line_last, Some(Kind::Then | Kind::Else)) {
            return self.prev_indent + 2;
        }
        if self.groups.last().is_some_and(|g| g.open == Open::Flat) {
            return self.groups.last().map(|g| g.content).unwrap_or(0);
        }
        if self.continues(kind, blank, word) {
            if self.prev_clause.is_some_and(|prev| prev == kind) {
                return self.prev_indent;
            }
            return self.prev_indent + 2;
        }
        self.structural()
    }

    fn structural(&self) -> usize {
        self.groups.last().map(|g| g.content).unwrap_or(0)
    }

    fn continues(&self, kind: Kind, blank: bool, word: &str) -> bool {
        // `if` starts expressions too, so the line before decides, as for any other token.
        // `guard` and `hook` are names elsewhere, but a line they start declares one.
        if blank
            || (fresh(kind) && kind != Kind::If)
            || (kind == Kind::Ident && matches!(word, "guard" | "hook"))
        {
            return false;
        }
        !matches!(
            self.prev_line_last,
            None | Some(Kind::Semi | Kind::LBrace | Kind::RBrace)
        )
    }

    fn on_token(&mut self, kind: Kind, bol: bool) {
        if bol
            && (matches!(kind, Kind::Use | Kind::Requires)
                || (kind == Kind::Ident && self.line_head == "supports"))
        {
            self.list_indent = Some(self.line_indent);
        } else if !matches!(kind, Kind::Ident | Kind::Dot | Kind::Comma) {
            self.list_indent = None;
        }
        if matches!(
            kind,
            Kind::Function
                | Kind::Type
                | Kind::ErrorKw
                | Kind::ErrorsKw
                | Kind::Event
                | Kind::Interface
                | Kind::Module
                | Kind::Deploy
        ) || (bol && kind == Kind::Ident && matches!(self.line_head.as_str(), "guard" | "hook"))
        {
            self.decl_indent = self.line_indent;
        }
        if kind == Kind::Raises && !self.groups.last().is_some_and(|g| g.spec) {
            self.in_raises = true;
            self.raises_indent = self.line_indent;
        }
        if kind == Kind::Is {
            self.in_raises = false;
        }
        match kind {
            Kind::If => self.ifs.push(OpenIf {
                indent: self.line_indent,
                depth: self.groups.len(),
            }),
            Kind::For if bol => self.for_indent = Some(self.line_indent),
            Kind::Do => self.for_indent = None,
            Kind::Else => {
                if let Some(open) = self.open_if() {
                    self.ifs.remove(open);
                }
            }
            // A statement's `if`s are done with it.
            Kind::Semi => {
                let depth = self.groups.len();
                self.ifs.retain(|open| open.depth < depth);
            }
            _ => {}
        }
        match kind {
            Kind::LParen | Kind::LBrack => self.groups.push(Group {
                content: self.line_indent + 2,
                close: self.line_indent,
                open: Open::Flat,
                square: kind == Kind::LBrack,
                spec: false,
            }),
            Kind::LBrace => self.groups.push(self.brace(bol)),
            Kind::RParen | Kind::RBrack | Kind::RBrace => {
                self.groups.pop();
                let depth = self.groups.len();
                self.ifs.retain(|open| open.depth <= depth);
            }
            _ => {}
        }
    }

    /// The innermost open `if` of this group, which an `else` belongs to.
    fn open_if(&self) -> Option<usize> {
        let depth = self.groups.len();
        self.ifs.iter().rposition(|open| open.depth == depth)
    }

    fn brace(&self, bol: bool) -> Group {
        if self.prev_kind == Some(Kind::Arrow) {
            if bol {
                Group {
                    content: self.line_indent + 2,
                    close: self.line_indent,
                    open: Open::Block,
                    square: false,
                    spec: false,
                }
            } else {
                Group {
                    content: self.line_indent + 4,
                    close: self.line_indent + 2,
                    open: Open::Block,
                    square: false,
                    spec: false,
                }
            }
        } else if self.prev_kind == Some(Kind::Of) {
            if bol {
                Group {
                    content: self.line_indent,
                    close: self.line_indent,
                    open: Open::Flat,
                    square: false,
                    spec: false,
                }
            } else {
                Group {
                    content: self.line_indent + 2,
                    close: self.line_indent,
                    open: Open::Flat,
                    square: false,
                    spec: false,
                }
            }
        } else {
            Group {
                content: self.line_indent + 2,
                close: self.line_indent,
                open: Open::Block,
                square: false,
                spec: self.line_head == "spec",
            }
        }
    }

    fn needs_space(&self, piece: &Piece, kind: Option<Kind>) -> bool {
        if piece.kind == PieceKind::Comment || self.prev_kind.is_none() {
            return piece.kind != PieceKind::Comment || self.prev_kind.is_some();
        }
        let Some(next) = kind else {
            return true;
        };
        let prev = self.prev_kind.expect("prev");
        if next == Kind::Dot && self.before_forall_dot() {
            return true;
        }
        if prev == Kind::Dot && self.forall_dot {
            return true;
        }
        if matches!(
            next,
            Kind::Comma | Kind::Semi | Kind::RParen | Kind::RBrack | Kind::Dot
        ) {
            return false;
        }
        if self.tight
            || matches!(
                prev,
                Kind::LParen | Kind::LBrack | Kind::Dot | Kind::Tilde | Kind::At
            )
        {
            return false;
        }
        if next == Kind::LParen && (prev == Kind::RParen || call_like(prev)) {
            return false;
        }
        if next == Kind::LBrack && matches!(prev, Kind::Ident | Kind::RParen | Kind::RBrack) {
            return false;
        }
        if (next == Kind::Colon || prev == Kind::Colon)
            && self.groups.last().is_some_and(|g| g.square)
        {
            return false;
        }
        if prev == Kind::LBrace && next == Kind::RBrace {
            return false;
        }
        true
    }

    /// The tokens so far end `forall x : T`, so a `.` next separates the body.
    fn before_forall_dot(&self) -> bool {
        matches!(
            self.recent.as_slice(),
            [.., (Kind::Ident, forall), (Kind::Ident, _), (Kind::Colon, _), (Kind::Ident, _)]
                if forall == "forall"
        )
    }

    fn emit_comment(&mut self, piece: &Piece) {
        let text = &self.src[piece.start..piece.end];
        let delta = self.col as isize - column(self.src, piece.start) as isize;
        for (i, line) in text.split('\n').enumerate() {
            if i == 0 {
                self.out.push_str(line);
                self.col += line.len();
                continue;
            }
            self.out.push('\n');
            let spaces = line.bytes().take_while(|b| *b == b' ').count();
            let shifted = (spaces as isize + delta).max(0) as usize;
            self.out.push_str(&" ".repeat(shifted));
            self.out.push_str(&line[spaces..]);
            self.col = shifted + line.len() - spaces;
        }
    }
}

fn breaks(piece: &Piece, prev: Option<Kind>) -> u32 {
    let mut n = piece.newlines_before;
    if n == 0 {
        return 0;
    }
    if n > 2 {
        n = 2;
    }
    if n > 1 && (prev == Some(Kind::LBrace) || token_kind(piece) == Some(Kind::RBrace)) {
        n = 1;
    }
    n
}

fn token_kind(piece: &Piece) -> Option<Kind> {
    match piece.kind {
        PieceKind::Token(kind) => Some(kind),
        PieceKind::Comment => None,
    }
}

fn call_like(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::Ident
            | Kind::Assert
            | Kind::List
            | Kind::Deploy
            | Kind::AtKw
            | Kind::Nonreentrant
            | Kind::Create
    )
}

/// A line that continues an expression or clause. The next continuation lines up with it.
fn sibling(prev: Kind, kind: Kind) -> bool {
    prev == kind
        || matches!(
            (prev, kind),
            (Kind::With, Kind::Then) | (Kind::Then, Kind::With)
        )
}

fn clause(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::Plus
            | Kind::Minus
            | Kind::Star
            | Kind::Slash
            | Kind::Percent
            | Kind::Amp
            | Kind::Pipe
            | Kind::Caret
            | Kind::Shl
            | Kind::Shr
            | Kind::Eq
            | Kind::Neq
            | Kind::Lt
            | Kind::Gt
            | Kind::Le
            | Kind::Ge
            | Kind::And
            | Kind::Or
            | Kind::DotDot
            | Kind::With
            | Kind::Then
    )
}

fn fresh(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::External
            | Kind::View
            | Kind::Pure
            | Kind::Private
            | Kind::Payable
            | Kind::Nonreentrant
            | Kind::Function
            | Kind::Type
            | Kind::ErrorKw
            | Kind::ErrorsKw
            | Kind::Event
            | Kind::Interface
            | Kind::Module
            | Kind::Import
            | Kind::Use
            | Kind::Contract
            | Kind::Upgradeable
            | Kind::Migrate
            | Kind::Deploy
            | Kind::Upgrade
            | Kind::Const
            | Kind::Var
            | Kind::If
            | Kind::For
            | Kind::Emit
            | Kind::Defer
            | Kind::SkipKw
            | Kind::Assert
            | Kind::Fail
    )
}

fn unary_minus(prev: Option<Kind>) -> bool {
    !matches!(
        prev,
        Some(
            Kind::Ident
                | Kind::Int
                | Kind::WeiLit
                | Kind::DurationLit
                | Kind::String
                | Kind::True
                | Kind::False
                | Kind::Unit
                | Kind::RParen
                | Kind::RBrack
                | Kind::RBrace
        )
    )
}

fn column(src: &str, pos: usize) -> usize {
    src[..pos].rfind('\n').map(|i| pos - i - 1).unwrap_or(pos)
}

fn verify(src: &str, out: &str) -> Result<(), Error> {
    let before = lex::pieces(src)?;
    let after = lex::pieces(out)?;
    if before.len() != after.len() {
        return Err(error(0, 0, "formatter changed the token sequence"));
    }
    for (a, b) in before.iter().zip(&after) {
        match (a.kind, b.kind) {
            (PieceKind::Comment, PieceKind::Comment) => {
                if !same_comment(&src[a.start..a.end], &out[b.start..b.end]) {
                    return Err(error(0, 0, "formatter changed a comment"));
                }
            }
            (PieceKind::Token(x), PieceKind::Token(y)) if x == y => {
                if src[a.start..a.end] != out[b.start..b.end] {
                    return Err(error(0, 0, "formatter changed a token"));
                }
            }
            _ => return Err(error(0, 0, "formatter changed the token sequence")),
        }
    }
    Ok(())
}

#[cfg(test)]
fn first_diff(src: &str, out: &str) -> String {
    let mut msg = String::new();
    let mut n = 0;
    for (i, (a, b)) in src.lines().zip(out.lines()).enumerate() {
        if a != b {
            msg.push_str(&format!("{:>4} |{a}\n    |{b}\n", i + 1));
            n += 1;
            if n == 8 {
                break;
            }
        }
    }
    if src.lines().count() != out.lines().count() {
        msg.push_str(&format!(
            "lines {} -> {}\n",
            src.lines().count(),
            out.lines().count()
        ));
    }
    msg
}

fn same_comment(a: &str, b: &str) -> bool {
    let a: Vec<_> = a.split('\n').collect();
    let b: Vec<_> = b.split('\n').collect();
    a.len() == b.len()
        && a.iter()
            .zip(b)
            .all(|(x, y)| x.trim_start() == y.trim_start())
}

#[cfg(test)]
mod tests {
    use super::format_source;
    use crate::lex::PieceKind;
    use std::path::PathBuf;

    fn lithe_files() -> Vec<PathBuf> {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let mut out = Vec::new();
        for dir in ["examples", "std", "bench", "fuzz", "ports"] {
            walk(&root.join(dir), &mut out);
        }
        out.sort();
        out
    }

    fn walk(dir: &std::path::Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                walk(&path, out);
            } else if path.extension().is_some_and(|ext| ext == "lithe") {
                out.push(path);
            }
        }
    }

    #[test]
    fn repo_sources_are_canonical() {
        let mut bad = Vec::new();
        for path in lithe_files() {
            let src = std::fs::read_to_string(&path).expect("read");
            let out = format_source(&src, crate::DEFAULT_WIDTH)
                .unwrap_or_else(|err| panic!("{}: {err}", path.display()));
            if out != src {
                bad.push(format!(
                    "{}\n{}",
                    path.display(),
                    super::first_diff(&src, &out)
                ));
            }
            for piece in crate::lex::pieces(&out).expect("lex") {
                let from = super::line_start(&out, piece.start);
                let line = out[from..].lines().next().unwrap_or("");
                if piece.kind != PieceKind::Comment && super::width(line) > crate::DEFAULT_WIDTH {
                    bad.push(format!(
                        "{}: over {}: {line}",
                        path.display(),
                        crate::DEFAULT_WIDTH
                    ));
                }
            }
        }
        assert!(bad.is_empty(), "{}", bad.join("\n"));
    }

    #[test]
    fn messy_source_gets_the_canonical_style() {
        let cases = [
            (
                "function  f(const  n:uint)is{\n\n\n  n+1\n\n}\n",
                "function f(const n : uint) is {\n  n + 1\n}\n",
            ),
            (
                "event E of record {\n  indexed a : uint;\n  bb : uint;\n\n  ccc : uint;\n  d : uint; e : uint;\n  ff : uint;\n  g : uint;\n}\n",
                "event E of record {\n  indexed a : uint;\n  bb        : uint;\n\n  ccc : uint;\n  d : uint; e : uint;\n  ff : uint;\n  g  : uint;\n}\n",
            ),
            (
                "function f(const n : uint)\nraises Err\nis\nn\n",
                "function f(const n : uint)\n  raises Err\nis\n  n\n",
            ),
            (
                "function f() raises A | B | C\n| D\nis { skip }\n",
                "function f() raises A | B | C | D\nis { skip }\n",
            ),
            (
                "function f(const s : S) : uint is\n  case s of {\n  |A{x;y=_}->x\n  | B {  x = why ;_ } -> why\n  | C|D{ x }->1\n  }\n",
                "function f(const s : S) : uint is\n  case s of {\n    | A { x; y = _ } -> x\n    | B { x = why; _ } -> why\n    | C | D { x } -> 1\n  }\n",
            ),
            (
                "type T is\n| A of uint\n| B\n",
                "type T is\n  | A of uint\n  | B\n",
            ),
            (
                "const s : string := \"a\\nb\\t\"\n",
                "const s : string := \"a\\nb\\t\"\n",
            ),
            (
                "const b : bytes := Evm.code(p) [1 : n + 1]\ndefer create (code) then { skip }\n",
                "const b : bytes := Evm.code(p)[1:n + 1]\ndefer create(code) then { skip }\n",
            ),
            (
                "const n : int := 1_000 + -2\n",
                "const n : int := 1_000 + -2\n",
            ),
            (
                "(* outer (* inner *)\n   still *)\nconst n : uint := 1\n",
                "(* outer (* inner *)\n   still *)\nconst n : uint := 1\n",
            ),
            (
                "function f() is {\n  (* kept\n     here *)\n  skip\n}\n",
                "function f() is {\n  (* kept\n     here *)\n  skip\n}\n",
            ),
            (
                "external function f(const id : uint)\nguarded g(id)\nraises E\nis { skip }\nuse M with {\nguard g(const id : uint)\nraises E\nis { skip }\n}\n",
                "use M with {\n  guard g(const id : uint)\n    raises E\n  is { skip }\n}\n\nexternal function f(const id : uint)\n  guarded g(id)\n  raises E\nis { skip }\n",
            ),
            (
                "use M exposing I with { hook h(const id : uint)\nraises E\nis {\nskip\n} hook g is skip; }\n",
                "use M exposing I with {\n  hook h(const id : uint)\n    raises E\n  is {\n    skip\n  }\n  hook g is skip;\n}\n",
            ),
            (
                "view function f() : uint is\n  1\n\n(* after a function's value *)\nuse M with {\n  hook g is skip;\n  guard e is f;\n}\n",
                "(* after a function's value *)\nuse M with {\n  hook g is skip;\n  guard e is f;\n}\n\nview function f() : uint is\n  1\n",
            ),
            (
                "pure function f(const n : uint) : string raises Bad is\n  if n = 1 then\n    \"a\"\n      else if n = 2 then\n        \"b\"\n          else\nfail Bad\n",
                "pure function f(const n : uint) : string raises Bad is\n  if n = 1 then\n    \"a\"\n  else if n = 2 then\n    \"b\"\n  else\n    fail Bad\n",
            ),
            (
                "external function f(const n : uint) : uint is {\n  skip;\n} with if n = 1 then\n  1\n    else if n = 2 then\n      2\n        else\n          3\n",
                "external function f(const n : uint) : uint is {\n  skip;\n} with if n = 1 then\n  1\nelse if n = 2 then\n  2\nelse\n  3\n",
            ),
            (
                "function f(const n : uint) is {\n  const x : uint := if n = 1 then\n    1\n      else if n = 2 then\n        2\n          else\n            3;\n  skip;\n}\n",
                "function f(const n : uint) is {\n  const x : uint := if n = 1 then\n    1\n  else if n = 2 then\n    2\n  else\n    3;\n  skip;\n}\n",
            ),
            (
                "function f(const n : option(uint)) : uint is case n of {\n  Some(v) -> if v = 1 then\n    1\n      else\n        2\n  | None -> 0\n}\n",
                "function f(const n : option(uint)) : uint is case n of {\n  Some(v) -> if v = 1 then\n    1\n  else\n    2\n  | None -> 0\n}\n",
            ),
            (
                "function f(const a : bool; const b : bool) : uint is\n  if a\n    then 1\n      else if b\n        then 2\n          else 3\n",
                "function f(const a : bool; const b : bool) : uint is\n  if a\n    then 1\n  else if b\n    then 2\n  else 3\n",
            ),
            (
                "function f(const a : bool) is {\n  if a then {\n    skip;\n  }\n      else if a then {\n    skip;\n  }\n  else {\n    skip;\n  }\n}\n",
                "function f(const a : bool) is {\n  if a then {\n    skip;\n  }\n  else if a then {\n    skip;\n  }\n  else {\n    skip;\n  }\n}\n",
            ),
            (
                "function f(const n : uint) is {\n  for i : uint in 0 .. n bound 9\ninvariant i <= n\n      invariant i < 10\n        do {\nskip;\n  }\n}\n",
                "function f(const n : uint) is {\n  for i : uint in 0 .. n bound 9\n    invariant i <= n\n    invariant i < 10\n  do {\n    skip;\n  }\n}\n",
            ),
        ];
        for (src, want) in cases {
            let out = format_source(src, 100).unwrap_or_else(|err| panic!("{err}\n{src}"));
            assert_eq!(out, want, "from {src:?}");
        }
    }

    #[test]
    fn headers_take_the_canonical_layout() {
        let cases = [
            (
                "contract C is {\n  storage is record { n : uint; }\n  use A;\n  (* lithe-ignore reentry: on purpose *)\n  use B exposing IB;\n  use C, D;\n  supports IA;\n  (* kept *)\n  use E;\n  use F delegated with {\n    hook h is skip;\n  }\n  use G; (* after *)\n  use H; use I;\n  external function f() is { skip }\n}\n",
                "contract C is {\n  supports IA;\n\n  use A, C, D, H, I;\n  (* kept *)\n  use E;\n  use G; (* after *)\n\n  (* lithe-ignore reentry: on purpose *)\n  use B exposing IB;\n\n  use F delegated with {\n    hook h is skip;\n  }\n\n  storage is record { n : uint; }\n  external function f() is { skip }\n}\n",
            ),
            (
                "module M is {\n  storage s at \"m\" is record { n : uint; }\n  requires X;\n  requires Y, Z;\n}\n",
                "module M is {\n  requires X, Y, Z;\n\n  storage s at \"m\" is record { n : uint; }\n}\n",
            ),
            (
                "(* A file of top-level declarations. *)\n\nimport \"std/evm\";\n\nmodule M is {\n  requires A;\n}\n\nexternal function f() is { skip }\n\nuse M exposing { function g(); }\nuse A;\n",
                "(* A file of top-level declarations. *)\n\nimport \"std/evm\";\n\nuse A;\n\nuse M exposing { function g(); }\n\nmodule M is {\n  requires A;\n}\n\nexternal function f() is { skip }\n",
            ),
            (
                "contract C is {\n  use A;\n}\n",
                "contract C is {\n  use A;\n}\n",
            ),
            (
                "contract C is {\n  use Alpha;\n  use Beta;\n  use Gamma;\n  use Delta;\n  use Epsilon;\n  use Zeta;\n  use Eta;\n  use Theta;\n}\n",
                "contract C is {\n  use Alpha, Beta, Gamma, Delta,\n    Epsilon, Zeta, Eta, Theta;\n}\n",
            ),
        ];
        for (src, want) in cases {
            let width = if src.contains("Theta") { 34 } else { 100 };
            let out = format_source(src, width).unwrap_or_else(|err| panic!("{err}\n{src}"));
            assert_eq!(out, want, "from {src:?}");
            assert_eq!(format_source(&out, width).expect("again"), out);
        }
    }

    #[test]
    fn a_use_goes_where_fmt_puts_it() {
        let cases = [
            (
                "contract C is {\n  use A;\n\n  use B exposing I;\n}\n",
                "contract C is {\n  use A, M;\n\n  use B exposing I;\n}\n",
            ),
            (
                "contract C is {\n  supports I;\n\n  use B exposing I;\n}\n",
                "contract C is {\n  supports I;\n\n  use M;\n\n  use B exposing I;\n}\n",
            ),
            (
                "contract C is {\n  storage is record { n : uint; }\n}\n",
                "contract C is {\n  use M;\n\n  storage is record { n : uint; }\n}\n",
            ),
            ("contract C is {\n}\n", "contract C is {\n  use M;\n}\n"),
            (
                "import \"std/evm\";\n\nexternal function f() is { skip }\n",
                "import \"std/evm\";\n\nuse M;\n\nexternal function f() is { skip }\n",
            ),
        ];
        for (src, want) in cases {
            let (at, text) = super::add_use(src, src.len() / 2, "M").expect("a place");
            let out = format!("{}{text}{}", &src[..at], &src[at..]);
            assert_eq!(out, want, "from {src:?}");
            assert_eq!(format_source(&out, 100).expect("fmt"), out);
        }
    }

    #[test]
    fn long_lines_wrap() {
        let pad = "x".repeat(60);
        let cases = [
            format!("function f() is {{\n  assert(account <> Address.zero, ERC20InvalidSender(Address.zero), {pad});\n}}\n"),
            format!("const h : bytes32 := Crypto.keccak256(Abi.encodePacked(marker, deployer, salt, {pad}));\n"),
            format!("function f() is {{\n  emit E {{ operator = Evm.sender(); from = from; to = to; {pad} = 1; }};\n}}\n"),
            format!("function f(const a : uint; const b : uint; const {pad} : uint) : (uint, uint) is {{ skip }}\n"),
            format!("function f(const a : uint) : uint raises A | B | {pad}\n  | C\nis {{ skip }}\n"),
            format!("function f() raises A | B | C | {pad} | {pad} is {{ skip }}\n"),
            format!("function f(const a : uint; const b : uint) : uint is Math.mulDivUp(a, b, {pad})\n"),
            format!("const ok : bool := a = b and c <> d or {pad} < 1 and b + 1 > 2\n"),
            format!("const n : uint := case x of {{ Some(v) -> v + 1 | None -> {pad} }}\n"),
            format!("const s : string := \"{pad}{pad}\"\n(* {pad}{pad} *)\n"),
            format!("function f(const a : bool) : uint is if a then 1 else {pad}\n"),
        ];
        let wants = [
            "function f() is {\n  assert(\n    account <> Address.zero,\n    ERC20InvalidSender(Address.zero),\n    X\n  );\n}\n",
            "const h : bytes32 := Crypto.keccak256(Abi.encodePacked(\n  marker,\n  deployer,\n  salt,\n  X\n));\n",
            "function f() is {\n  emit E {\n    operator = Evm.sender();\n    from = from;\n    to = to;\n    X = 1;\n  };\n}\n",
            "function f(\n  const a : uint;\n  const b : uint;\n  const X : uint\n) : (uint, uint) is { skip }\n",
            "function f(const a : uint) : uint\n  raises A | B | X | C\nis { skip }\n",
            "function f()\n  raises A | B | C | X\n    | X\nis { skip }\n",
            "function f(const a : uint; const b : uint) : uint is\n  Math.mulDivUp(a, b, X)\n",
            "const ok : bool := a = b and c <> d\n  or X < 1 and b + 1 > 2\n",
            "const n : uint := case x of {\n  Some(v) -> v + 1\n  | None -> X\n}\n",
            "const s : string := \"XX\"\n(* XX *)\n",
            "function f(const a : bool) : uint is\n  if a then 1 else X\n",
        ];
        for (src, want) in cases.iter().zip(wants) {
            let out = format_source(src, 100).unwrap_or_else(|err| panic!("{err}\n{src}"));
            assert_eq!(out, want.replace('X', &pad), "from {src:?}");
        }
        let long = "y".repeat(55);
        let wide = "map(address, map(address, map(address, map(address, uint))))";
        let src = format!("type T is record {{\n  {long} : uint;\n  b : {wide};\n}}\n");
        assert_eq!(format_source(&src, 100).expect("format"), src);
        let lhs = format!("storage.r[0x{}1].members[someone]", "0".repeat(63));
        let out = format_source(&format!("{lhs} := flag = p;\n"), 100).expect("format");
        assert_eq!(out, format!("{lhs} :=\n  flag = p;\n"));
    }
}
