//! `lithe lsp`: a language server on stdin and stdout. It reports errors and `lithe lint`'s
//! findings as you type, with their fixes as quick fixes, formats as `lithe fmt` does, and
//! answers hover, go to definition, references, highlights, outline, completion, and
//! signature help from the last version of each file that checked.

use std::collections::HashMap;
use std::io::{BufRead, Write};
use std::path::{Path, PathBuf};

use lithe::{Index, Kind, Span};

pub fn run() -> ! {
    let code = serve(&mut std::io::stdin().lock(), &mut std::io::stdout().lock());
    std::process::exit(code)
}

const CAPABILITIES: &str = r#"{"capabilities":{"textDocumentSync":{"openClose":true,"change":1,"save":true},"hoverProvider":true,"definitionProvider":true,"referencesProvider":true,"documentHighlightProvider":true,"documentSymbolProvider":true,"completionProvider":{"triggerCharacters":["."]},"signatureHelpProvider":{"triggerCharacters":["(",","]},"documentFormattingProvider":true,"codeActionProvider":{"codeActionKinds":["quickfix"]}},"serverInfo":{"name":"lithe"}}"#;

struct Doc {
    text: String,
    /// From the last version that checked, so answers survive a half-typed line.
    index: Option<Index>,
    /// The findings for `text` as it is.
    lints: Vec<lithe::Lint>,
    /// Why `text` does not compile, if it does not.
    error: Option<lithe::Error>,
}

/// Answers messages until `exit` or the end of input, and returns the exit status.
fn serve(input: &mut impl BufRead, output: &mut impl Write) -> i32 {
    let mut docs: HashMap<String, Doc> = HashMap::new();
    let mut shutdown = false;
    while let Some(msg) = read(input) {
        let method = msg.get("method").and_then(Json::str).unwrap_or("");
        let params = msg.get("params");
        let doc = params.and_then(|p| p.get("textDocument"));
        let uri = doc.and_then(|d| d.get("uri")).and_then(Json::str);
        let text = match method {
            "textDocument/didOpen" => doc.and_then(|d| d.get("text")),
            "textDocument/didChange" => params
                .and_then(|p| p.get("contentChanges"))
                .and_then(Json::last)
                .and_then(|change| change.get("text")),
            _ => None,
        }
        .and_then(Json::str);
        match method {
            "initialize" => reply(output, &msg, CAPABILITIES),
            "shutdown" => {
                shutdown = true;
                reply(output, &msg, "null");
            }
            "exit" => return if shutdown { 0 } else { 1 },
            "textDocument/didOpen" | "textDocument/didChange" => {
                if let (Some(uri), Some(text)) = (uri, text) {
                    let doc = docs.entry(uri.to_string()).or_insert(Doc {
                        text: String::new(),
                        index: None,
                        lints: Vec::new(),
                        error: None,
                    });
                    doc.text = text.to_string();
                    update(output, uri, doc);
                }
            }
            // A saved file can change what the open files that import it report.
            "textDocument/didSave" => {
                for (uri, doc) in &mut docs {
                    update(output, uri, doc);
                }
            }
            "textDocument/didClose" => {
                if let Some(uri) = uri {
                    docs.remove(uri);
                    notify_diagnostics(output, uri, &[]);
                }
            }
            "textDocument/hover"
            | "textDocument/definition"
            | "textDocument/references"
            | "textDocument/documentHighlight"
            | "textDocument/documentSymbol"
            | "textDocument/completion"
            | "textDocument/signatureHelp" => {
                let found = uri.zip(params).and_then(|(uri, params)| {
                    let doc = docs.get(uri)?;
                    answer(method, uri, doc, doc.index.as_ref()?, params)
                });
                reply(output, &msg, found.as_deref().unwrap_or("null"));
            }
            "textDocument/formatting" => {
                let found = uri.and_then(|uri| format(uri, &docs.get(uri)?.text));
                reply(output, &msg, found.as_deref().unwrap_or("null"));
            }
            "textDocument/codeAction" => {
                let found = uri
                    .zip(params)
                    .and_then(|(uri, params)| fixes(uri, docs.get(uri)?, params));
                reply(output, &msg, found.as_deref().unwrap_or("[]"));
            }
            "" => {}
            _ if msg.get("id").is_some() => send(
                output,
                &format!(
                    r#"{{"jsonrpc":"2.0","id":{},"error":{{"code":-32601,"message":{}}}}}"#,
                    id(&msg),
                    quote(&format!("unsupported method `{method}`"))
                ),
            ),
            _ => {}
        }
    }
    1
}

fn update(output: &mut impl Write, uri: &str, doc: &mut Doc) {
    let analysis = lithe::analyze(&file_path(uri), &doc.text);
    if analysis.index.is_some() {
        doc.index = analysis.index;
    }
    doc.lints = analysis.lints;
    doc.error = analysis.error;
    publish(output, uri, doc);
}

/// The whole document as `lithe fmt` writes it, with the width `lithe.toml` sets.
fn format(uri: &str, text: &str) -> Option<String> {
    let width = lithe::format_width(&file_path(uri)).unwrap_or(lithe::DEFAULT_WIDTH);
    let out = lithe::format_source(text, width).ok()?;
    if out == text {
        return Some("[]".to_string());
    }
    Some(format!(
        r#"[{{"range":{{"start":{{"line":0,"character":0}},"end":{}}},"newText":{}}}]"#,
        byte_pos(text, text.len()),
        quote(&out)
    ))
}

/// `lithe lint --fix`'s edit for each finding on the lines asked about.
fn fixes(uri: &str, doc: &Doc, params: &Json) -> Option<String> {
    let range = params.get("range")?;
    let first = range.get("start")?.get("line")?.num()? as u32 + 1;
    let last = range.get("end")?.get("line")?.num()? as u32 + 1;
    let actions: Vec<String> = doc
        .lints
        .iter()
        .filter(|lint| (first..=last).contains(&lint.line))
        .filter_map(|lint| {
            let (start, end, new) = lint.fix?;
            let title = lint.message.lines().next().unwrap_or(lint.rule);
            Some(format!(
                r#"{{"title":{},"kind":"quickfix","isPreferred":true,"diagnostics":[{}],"edit":{{"changes":{{{}:[{{"range":{{"start":{},"end":{}}},"newText":{}}}]}}}}}}"#,
                quote(&format!("Fix: {title}")),
                lint_diagnostic(&doc.text, lint),
                quote(uri),
                byte_pos(&doc.text, start),
                byte_pos(&doc.text, end),
                quote(new)
            ))
        })
        .collect();
    let mut actions = actions;
    actions.extend(
        doc.error
            .as_ref()
            .filter(|err| (first..=last).contains(&err.line))
            .and_then(|err| import_fix(uri, &doc.text, err)),
    );
    Some(format!("[{}]", actions.join(",")))
}

/// For a name that another file declares: adding its import. The error says which file.
fn import_fix(uri: &str, text: &str, err: &lithe::Error) -> Option<String> {
    let (_, rest) = err.message.split_once("` is declared in `")?;
    let path = rest.split('`').next()?;
    if !lithe::is_module_path(path) {
        return None;
    }
    let at = import_at(text);
    let before = &text[..at];
    let blank = if before
        .trim_end()
        .lines()
        .last()
        .is_some_and(|l| l.trim_start().starts_with("import "))
    {
        ""
    } else {
        "\n"
    };
    let new = format!("import \"{path}\";\n{blank}");
    Some(format!(
        r#"{{"title":{},"kind":"quickfix","isPreferred":true,"diagnostics":[{}],"edit":{{"changes":{{{}:[{{"range":{{"start":{at},"end":{at}}},"newText":{}}}]}}}}}}"#,
        quote(&format!("Import `{path}`")),
        error_diagnostic(text, err),
        quote(uri),
        quote(&new),
        at = byte_pos(text, at),
    ))
}

/// Where a new import goes: after the file's last import, or before its first declaration.
fn import_at(text: &str) -> usize {
    let mut offset = 0;
    let mut depth = 0i32;
    let mut after_imports = None;
    let mut first_code = None;
    for line in text.split_inclusive('\n') {
        let trimmed = line.trim();
        if depth == 0 {
            if trimmed.starts_with("import ") {
                after_imports = Some(offset + line.len());
            } else if !trimmed.is_empty() && !trimmed.starts_with("(*") && first_code.is_none() {
                first_code = Some(offset);
            }
        }
        depth += line.matches("(*").count() as i32 - line.matches("*)").count() as i32;
        offset += line.len();
    }
    after_imports.or(first_code).unwrap_or(0)
}

/// A byte offset of `text` as an LSP position.
fn byte_pos(text: &str, mut at: usize) -> String {
    at = at.min(text.len());
    while !text.is_char_boundary(at) {
        at -= 1;
    }
    let line_start = text[..at].rfind('\n').map_or(0, |i| i + 1);
    format!(
        r#"{{"line":{},"character":{}}}"#,
        text[..line_start].matches('\n').count(),
        text[line_start..at].encode_utf16().count()
    )
}

fn answer(method: &str, uri: &str, doc: &Doc, index: &Index, params: &Json) -> Option<String> {
    let text = &doc.text;
    if method == "textDocument/documentSymbol" {
        let roots: Vec<String> = (0..index.defs.len())
            .filter(|&d| {
                outline(index, text, d)
                    && !index.defs[d]
                        .parent
                        .is_some_and(|p| outline(index, text, p))
            })
            .map(|d| symbol(index, text, d))
            .collect();
        return Some(format!("[{}]", roots.join(",")));
    }
    let (line, col) = position(text, params.get("position")?)?;
    match method {
        "textDocument/completion" if import_string(text, line, col).is_some() => {
            let (start, typed) = import_string(text, line, col)?;
            let range = format!(
                r#"{{"start":{{"line":{},"character":{start}}},"end":{{"line":{},"character":{}}}}}"#,
                line - 1,
                line - 1,
                start + typed.len()
            );
            let items: Vec<String> = module_paths(&file_path(uri))
                .into_iter()
                .filter(|path| path.starts_with(&typed))
                .map(|path| {
                    format!(
                        r#"{{"label":{},"kind":9,"textEdit":{{"range":{range},"newText":{}}}}}"#,
                        quote(&path),
                        quote(&path)
                    )
                })
                .collect();
            return Some(format!("[{}]", items.join(",")));
        }
        "textDocument/completion" => {
            let items: Vec<String> = index
                .completions(text, line, col)
                .iter()
                .map(|c| {
                    let snippet = c.snippet.as_ref().map_or(String::new(), |s| {
                        format!(r#","insertText":{},"insertTextFormat":2"#, quote(s))
                    });
                    format!(
                        r#"{{"label":{},"kind":{},"detail":{},"documentation":{{"kind":"markdown","value":{}}}{snippet}}}"#,
                        quote(&c.label),
                        completion_kind(c.kind),
                        quote(&c.detail),
                        quote(&c.doc)
                    )
                })
                .collect();
            return Some(format!("[{}]", items.join(",")));
        }
        "textDocument/signatureHelp" => {
            let sig = index.signature(text, line, col)?;
            let params: Vec<String> = sig
                .params
                .iter()
                .map(|p| format!(r#"{{"label":{}}}"#, quote(p)))
                .collect();
            return Some(format!(
                r#"{{"signatures":[{{"label":{},"documentation":{{"kind":"markdown","value":{}}},"parameters":[{}]}}],"activeSignature":0,"activeParameter":{}}}"#,
                quote(&sig.label),
                quote(&sig.doc),
                params.join(","),
                sig.active
            ));
        }
        _ => {}
    }
    if method == "textDocument/definition" {
        if let Some(found) = import_target(uri, text, line, col) {
            return Some(found);
        }
    }
    let r = index.at(0, text, line, col)?;
    let def = &index.defs[r.def];
    match method {
        "textDocument/hover" => Some(format!(
            r#"{{"contents":{{"kind":"markdown","value":{}}},"range":{}}}"#,
            quote(index.hover(r)),
            range(text, r.at)
        )),
        "textDocument/definition" => location(index, uri, text, def.at?),
        "textDocument/references" => {
            let with_decl = params
                .get("context")
                .and_then(|c| c.get("includeDeclaration"))
                .is_none_or(|d| matches!(d, Json::Lit(true)));
            let found: Vec<String> = index
                .references(r.def)
                .filter(|x| index.live(text, x) && (with_decl || Some(x.at) != def.at))
                .filter_map(|x| location(index, uri, text, x.at))
                .collect();
            Some(format!("[{}]", found.join(",")))
        }
        "textDocument/documentHighlight" => {
            let found: Vec<String> = index
                .references(r.def)
                .filter(|x| x.at.file == 0 && index.live(text, x))
                .map(|x| format!(r#"{{"range":{},"kind":1}}"#, range(text, x.at)))
                .collect();
            Some(format!("[{}]", found.join(",")))
        }
        _ => None,
    }
}

/// Inside an `import "..."` path: where the path starts, as a 0-based character, and what
/// is typed of it before the position.
fn import_string(text: &str, line: u32, col: u32) -> Option<(usize, String)> {
    let src = text.lines().nth(line.checked_sub(1)? as usize)?;
    if !src.trim_start().starts_with("import") {
        return None;
    }
    let open = src.find('"')?;
    let at = (col as usize).checked_sub(1)?;
    if at <= open || src[open + 1..at.min(src.len())].contains('"') {
        return None;
    }
    let typed = src.get(open + 1..at)?.to_string();
    Some((src[..open + 1].encode_utf16().count(), typed))
}

/// Every module a file can import: the standard library's, and the files of its project
/// beside and below it.
fn module_paths(file: &Path) -> Vec<String> {
    let mut out: Vec<String> = lithe::std_modules().into_iter().map(String::from).collect();
    let Some(dir) = file.parent() else {
        return out;
    };
    let mut found = Vec::new();
    lithe::lithe_files(dir, &mut found).ok();
    for path in found {
        if path == file || path.to_string_lossy().ends_with(".spec.lithe") {
            continue;
        }
        let Ok(rel) = path
            .with_extension("")
            .strip_prefix(dir)
            .map(Path::to_path_buf)
        else {
            continue;
        };
        let module = format!("./{}", rel.to_string_lossy().replace('\\', "/"));
        if lithe::is_module_path(&module) {
            out.push(module);
        }
    }
    out.sort();
    out
}

/// The file an `import "..."` line names, when the position is on its path.
fn import_target(uri: &str, text: &str, line: u32, col: u32) -> Option<String> {
    let src = text.lines().nth(line.checked_sub(1)? as usize)?;
    if !src.trim_start().starts_with("import") {
        return None;
    }
    let open = src.find('"')?;
    let close = open + 1 + src[open + 1..].find('"')?;
    if !(open as u32 + 1..=close as u32 + 1).contains(&col) {
        return None;
    }
    let rel = &src[open + 1..close];
    let path = match lithe::std_text(rel) {
        Some(std) => std_copy(&format!("{rel}.lithe"), std)?,
        None => lithe::import_path(&file_path(uri), rel)
            .canonicalize()
            .ok()?,
    };
    path.exists().then(|| {
        format!(
            r#"{{"uri":{},"range":{{"start":{{"line":0,"character":0}},"end":{{"line":0,"character":0}}}}}}"#,
            quote(&file_uri(&path))
        )
    })
}

/// A standard library file, written out once so an editor can open it.
fn std_copy(rel: &str, text: &str) -> Option<PathBuf> {
    let path = std::env::temp_dir()
        .join(concat!("lithe-", env!("CARGO_PKG_VERSION")))
        .join(rel);
    if std::fs::read_to_string(&path).ok().as_deref() != Some(text) {
        std::fs::create_dir_all(path.parent()?).ok()?;
        std::fs::write(&path, text).ok()?;
    }
    Some(path)
}

/// Whether a definition belongs in the outline of the indexed file.
fn outline(index: &Index, text: &str, d: usize) -> bool {
    let def = &index.defs[d];
    !matches!(
        def.kind,
        Kind::Local | Kind::Param | Kind::Builtin | Kind::Keyword
    ) && def
        .at
        .is_some_and(|at| at.file == 0 && index.at(0, text, at.line, at.col).is_some())
}

fn symbol(index: &Index, text: &str, d: usize) -> String {
    let def = &index.defs[d];
    let children: Vec<String> = (0..index.defs.len())
        .filter(|&c| index.defs[c].parent == Some(d) && outline(index, text, c))
        .map(|c| symbol(index, text, c))
        .collect();
    let at = range(text, def.at.expect("an outlined definition has a place"));
    format!(
        r#"{{"name":{},"detail":{},"kind":{},"range":{at},"selectionRange":{at},"children":[{}]}}"#,
        quote(&def.name),
        quote(&def.detail),
        symbol_kind(def.kind),
        children.join(",")
    )
}

fn symbol_kind(kind: Kind) -> u8 {
    match kind {
        Kind::Module => 2,
        Kind::Contract => 5,
        Kind::Method => 6,
        Kind::Field => 8,
        Kind::ErrorSet => 10,
        Kind::Interface => 11,
        Kind::Error => 14,
        Kind::Storage => 19,
        Kind::Variant => 22,
        Kind::Type => 23,
        Kind::Event => 24,
        Kind::Local | Kind::Param => 13,
        Kind::Function | Kind::External | Kind::Builtin | Kind::Keyword => 12,
    }
}

fn completion_kind(kind: Kind) -> u8 {
    match kind {
        Kind::Method => 2,
        Kind::Function | Kind::External | Kind::Builtin => 3,
        Kind::Field => 5,
        Kind::Local | Kind::Param | Kind::Storage => 6,
        Kind::Interface => 8,
        Kind::Module => 9,
        Kind::Contract => 7,
        Kind::ErrorSet => 13,
        Kind::Keyword => 14,
        Kind::Variant => 20,
        Kind::Error => 21,
        Kind::Type => 22,
        Kind::Event => 23,
    }
}

/// Where a span is, as an LSP location. The indexed file is the open document; a standard
/// library file is written out once so the editor can open it.
fn location(index: &Index, uri: &str, text: &str, at: Span) -> Option<String> {
    let (uri, text) = if at.file == 0 {
        (uri.to_string(), text)
    } else {
        let file = index.files.get(at.file)?;
        let path = match &file.std {
            Some(rel) => std_copy(rel, &file.text)?,
            None => PathBuf::from(&file.path),
        };
        (file_uri(&path), file.text.as_str())
    };
    Some(format!(
        r#"{{"uri":{},"range":{}}}"#,
        quote(&uri),
        range(text, at)
    ))
}

fn file_uri(path: &Path) -> String {
    let path = path.to_string_lossy().replace('\\', "/");
    let mut out = String::from(if path.starts_with('/') {
        "file://"
    } else {
        "file:///"
    });
    for byte in path.bytes() {
        match byte {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'/' | b'-' | b'_' | b'.' | b'~' | b':' => {
                out.push(byte as char)
            }
            _ => out.push_str(&format!("%{byte:02X}")),
        }
    }
    out
}

/// An LSP position, counted in UTF-16 units, as a 1-based line and byte column.
fn position(text: &str, pos: &Json) -> Option<(u32, u32)> {
    let line = pos.get("line")?.num()?;
    let units = pos.get("character")?.num()?;
    let src = text.split('\n').nth(line)?;
    let (mut seen, mut byte) = (0, 0);
    for ch in src.chars() {
        if seen >= units {
            break;
        }
        seen += ch.len_utf16();
        byte += ch.len_utf8();
    }
    Some((line as u32 + 1, byte as u32 + 1))
}

/// A 1-based line and byte column, and a length in bytes, as an LSP range.
fn range(text: &str, at: Span) -> String {
    let row = at.line.saturating_sub(1);
    let src = text.split('\n').nth(row as usize).unwrap_or("");
    let src = src.strip_suffix('\r').unwrap_or(src);
    let fit = |mut i: usize| {
        i = i.min(src.len());
        while !src.is_char_boundary(i) {
            i -= 1;
        }
        src[..i].encode_utf16().count()
    };
    let start = at.col.saturating_sub(1) as usize;
    format!(
        r#"{{"start":{{"line":{row},"character":{}}},"end":{{"line":{row},"character":{}}}}}"#,
        fit(start),
        fit(start + at.len as usize)
    )
}

// simplify: an error carries no file, so one inside an imported file is shown at its line
// and column in the importing file. Needs a source path on `lithe::Error`.
fn publish(output: &mut impl Write, uri: &str, doc: &Doc) {
    let mut items: Vec<String> = doc
        .lints
        .iter()
        .map(|lint| lint_diagnostic(&doc.text, lint))
        .collect();
    items.extend(
        doc.error
            .as_ref()
            .map(|err| error_diagnostic(&doc.text, err)),
    );
    notify_diagnostics(output, uri, &items);
}

fn error_diagnostic(text: &str, err: &lithe::Error) -> String {
    format!(
        r#"{{"range":{},"severity":1,"source":"lithe","message":{}}}"#,
        word(text, err.line, err.column),
        quote(&err.message)
    )
}

/// A finding as a warning, tagged unnecessary when it is unused code, so editors fade it.
fn lint_diagnostic(text: &str, lint: &lithe::Lint) -> String {
    let tags = if lint.rule.starts_with("unused-") {
        r#","tags":[1]"#
    } else {
        ""
    };
    // A fix covers exactly what the finding is about: the name, or the `var` to change.
    let at = match lint.fix {
        Some((start, end, _)) if end > start => format!(
            r#"{{"start":{},"end":{}}}"#,
            byte_pos(text, start),
            byte_pos(text, end)
        ),
        _ => word(text, lint.line, lint.col),
    };
    format!(
        r#"{{"range":{at},"severity":2,"source":"lithe","code":{},"message":{}{tags}}}"#,
        quote(lint.rule),
        quote(&lint.message)
    )
}

fn notify_diagnostics(output: &mut impl Write, uri: &str, items: &[String]) {
    send(
        output,
        &format!(
            r#"{{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{{"uri":{},"diagnostics":[{}]}}}}"#,
            quote(uri),
            items.join(",")
        ),
    );
}

/// The range of the word at a 1-based line and byte column, or of the one character there.
fn word(text: &str, line: u32, column: u32) -> String {
    let src = text
        .lines()
        .nth(line.saturating_sub(1) as usize)
        .unwrap_or("");
    let mut start = (column.saturating_sub(1) as usize).min(src.len());
    while !src.is_char_boundary(start) {
        start -= 1;
    }
    let rest = &src[start..];
    let len = match rest.find(|c: char| !(c.is_alphanumeric() || c == '_')) {
        Some(0) => rest.chars().next().map_or(0, char::len_utf8),
        Some(n) => n,
        None => rest.len(),
    };
    let at = Span {
        file: 0,
        line: line.max(1),
        col: start as u32 + 1,
        len: len as u32,
    };
    range(text, at)
}

/// The path a `file://` URI names. Other schemes name no file, so their imports do not resolve.
fn file_path(uri: &str) -> PathBuf {
    let Some(rest) = uri.strip_prefix("file://") else {
        return PathBuf::from(uri);
    };
    let bytes = rest.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let escaped = (bytes[i] == b'%')
            .then(|| rest.get(i + 1..i + 3))
            .flatten()
            .and_then(|hex| u8::from_str_radix(hex, 16).ok());
        match escaped {
            Some(byte) => {
                out.push(byte);
                i += 3;
            }
            None => {
                out.push(bytes[i]);
                i += 1;
            }
        }
    }
    let path = String::from_utf8_lossy(&out).into_owned();
    // `file:///C:/x` names `C:/x` on Windows.
    match path.as_bytes() {
        [b'/', drive, b':', ..] if drive.is_ascii_alphabetic() => PathBuf::from(&path[1..]),
        _ => PathBuf::from(path),
    }
}

fn read(input: &mut impl BufRead) -> Option<Json> {
    loop {
        let mut len = None;
        loop {
            let mut line = String::new();
            if input.read_line(&mut line).ok()? == 0 {
                return None;
            }
            let line = line.trim_end();
            if line.is_empty() {
                break;
            }
            if let Some((name, value)) = line.split_once(':') {
                if name.eq_ignore_ascii_case("content-length") {
                    len = value.trim().parse().ok();
                }
            }
        }
        let mut body = vec![0; len?];
        input.read_exact(&mut body).ok()?;
        if let Some(msg) = parse(&String::from_utf8_lossy(&body)) {
            return Some(msg);
        }
    }
}

fn send(output: &mut impl Write, body: &str) {
    let _ = write!(output, "Content-Length: {}\r\n\r\n{body}", body.len());
    let _ = output.flush();
}

fn reply(output: &mut impl Write, msg: &Json, result: &str) {
    send(
        output,
        &format!(r#"{{"jsonrpc":"2.0","id":{},"result":{result}}}"#, id(msg)),
    );
}

fn id(msg: &Json) -> String {
    match msg.get("id") {
        Some(Json::Num(n)) => n.clone(),
        Some(Json::Str(s)) => quote(s),
        _ => "null".to_string(),
    }
}

fn quote(text: &str) -> String {
    let mut out = String::from("\"");
    for ch in text.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            ch if ch < ' ' => out.push_str(&format!("\\u{:04x}", ch as u32)),
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

/// Just enough JSON for LSP messages. Numbers keep their text, so an `id` is echoed exactly.
enum Json {
    /// `true` or `false`; `null` is `Lit(false)`.
    Lit(bool),
    Num(String),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

impl Json {
    fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Obj(fields) => fields.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }

    fn str(&self) -> Option<&str> {
        match self {
            Json::Str(s) => Some(s),
            _ => None,
        }
    }

    fn num(&self) -> Option<usize> {
        match self {
            Json::Num(n) => n.parse().ok(),
            _ => None,
        }
    }

    fn last(&self) -> Option<&Json> {
        match self {
            Json::Arr(items) => items.last(),
            _ => None,
        }
    }
}

type Chars<'a> = std::iter::Peekable<std::str::Chars<'a>>;

fn parse(text: &str) -> Option<Json> {
    value(&mut text.chars().peekable())
}

fn value(it: &mut Chars) -> Option<Json> {
    while it.next_if(|c| c.is_whitespace()).is_some() {}
    match it.next()? {
        '{' => {
            let mut fields = Vec::new();
            loop {
                while it.next_if(|c| c.is_whitespace() || *c == ',').is_some() {}
                match it.next()? {
                    '}' => return Some(Json::Obj(fields)),
                    '"' => {
                        let key = string(it)?;
                        while it.next_if(|c| c.is_whitespace()).is_some() {}
                        it.next_if_eq(&':')?;
                        fields.push((key, value(it)?));
                    }
                    _ => return None,
                }
            }
        }
        '[' => {
            let mut items = Vec::new();
            loop {
                while it.next_if(|c| c.is_whitespace() || *c == ',').is_some() {}
                if it.next_if_eq(&']').is_some() {
                    return Some(Json::Arr(items));
                }
                items.push(value(it)?);
            }
        }
        '"' => string(it).map(Json::Str),
        first => {
            let mut word = first.to_string();
            while let Some(c) = it.next_if(|c| c.is_ascii_alphanumeric() || "+-.".contains(*c)) {
                word.push(c);
            }
            match word.as_str() {
                "null" | "false" => Some(Json::Lit(false)),
                "true" => Some(Json::Lit(true)),
                _ if first == '-' || first.is_ascii_digit() => Some(Json::Num(word)),
                _ => None,
            }
        }
    }
}

fn string(it: &mut Chars) -> Option<String> {
    let mut out = String::new();
    loop {
        match it.next()? {
            '"' => return Some(out),
            '\\' => match it.next()? {
                'n' => out.push('\n'),
                't' => out.push('\t'),
                'r' => out.push('\r'),
                'b' => out.push('\u{8}'),
                'f' => out.push('\u{c}'),
                'u' => {
                    let mut units = vec![hex4(it)?];
                    if (0xD800..0xDC00).contains(&units[0])
                        && it.next_if_eq(&'\\').is_some()
                        && it.next_if_eq(&'u').is_some()
                    {
                        units.push(hex4(it)?);
                    }
                    out.extend(
                        char::decode_utf16(units)
                            .map(|ch| ch.unwrap_or(char::REPLACEMENT_CHARACTER)),
                    );
                }
                ch => out.push(ch),
            },
            ch => out.push(ch),
        }
    }
}

fn hex4(it: &mut Chars) -> Option<u16> {
    let digits: String = it.by_ref().take(4).collect();
    u16::from_str_radix(&digits, 16).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn frame(body: &str) -> String {
        format!("Content-Length: {}\r\n\r\n{body}", body.len())
    }

    fn open(uri: &str, text: &str) -> String {
        frame(&format!(
            r#"{{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{{"textDocument":{{"uri":{},"languageId":"lithe","version":1,"text":{}}}}}}}"#,
            quote(uri),
            quote(text)
        ))
    }

    fn session(messages: &[String]) -> (i32, Vec<String>) {
        let input = messages.concat();
        let mut output = Vec::new();
        let code = serve(&mut input.as_bytes(), &mut output);
        let output = String::from_utf8(output).unwrap();
        let bodies = output
            .split("Content-Length: ")
            .skip(1)
            .map(|part| part.split_once("\r\n\r\n").unwrap().1.to_string())
            .collect();
        (code, bodies)
    }

    #[test]
    fn serves_diagnostics() {
        let root = std::env::current_dir().unwrap();
        let vault = root.join("examples/imports/vault.lithe");
        let vault_uri = format!("file://{}", vault.display()).replace(' ', "%20");
        let broken = "storage is record { count : uint; }\n\
                      external view function get() : uint is\n  (* é *) nope\n";
        let (code, bodies) = session(&[
            frame(
                r#"{"jsonrpc":"2.0","id":"a1","method":"initialize","params":{"capabilities":{}}}"#,
            ),
            frame(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#),
            open(&vault_uri, &std::fs::read_to_string(&vault).unwrap()),
            open("file:///tmp/broken.lithe", broken),
            frame(
                r#"{"jsonrpc":"2.0","id":7,"method":"textDocument/prepareCallHierarchy","params":{}}"#,
            ),
            frame(r#"{"jsonrpc":"2.0","id":8,"method":"shutdown"}"#),
            frame(r#"{"jsonrpc":"2.0","method":"exit"}"#),
        ]);
        assert_eq!(code, 0);
        assert!(bodies[0].starts_with(r#"{"jsonrpc":"2.0","id":"a1","result":{"capabilities""#));
        assert!(
            bodies[1].ends_with(r#""diagnostics":[]}}"#),
            "imports resolve beside the file: {}",
            bodies[1]
        );
        assert!(
            bodies[2].contains(r#""range":{"start":{"line":2,"character":10},"end":{"line":2,"character":14}},"severity":1"#),
            "{}",
            bodies[2]
        );
        assert!(bodies[3].contains(r#""id":7,"error":{"code":-32601"#));
        assert_eq!(bodies[4], r#"{"jsonrpc":"2.0","id":8,"result":null}"#);
    }

    fn request(id: u32, method: &str, uri: &str, line: u32, character: u32) -> String {
        frame(&format!(
            r#"{{"jsonrpc":"2.0","id":{id},"method":"textDocument/{method}","params":{{"textDocument":{{"uri":{}}},"position":{{"line":{line},"character":{character}}}}}}}"#,
            quote(uri)
        ))
    }

    #[test]
    fn answers_from_the_last_version_that_checked() {
        let path = std::env::current_dir()
            .unwrap()
            .join("examples/counter.lithe");
        let uri = format!("file://{}", path.display()).replace(' ', "%20");
        let good = std::fs::read_to_string(&path).unwrap();
        // A half-typed line: the file no longer checks, but the index from before still answers.
        let edited = good.replacen(
            "    storage.count := storage.count + n;",
            "    storage.count := storage.count + n;\n    storage.\n    add(",
            1,
        );
        let change = frame(&format!(
            r#"{{"jsonrpc":"2.0","method":"textDocument/didChange","params":{{"textDocument":{{"uri":{},"version":2}},"contentChanges":[{{"text":{}}}]}}}}"#,
            quote(&uri),
            quote(&edited)
        ));
        let (_, bodies) = session(&[
            frame(r#"{"jsonrpc":"2.0","id":0,"method":"initialize","params":{}}"#),
            open(&uri, &good),
            request(1, "hover", &uri, 64, 20),
            request(2, "definition", &uri, 61, 23),
            request(3, "references", &uri, 7, 3),
            request(4, "documentSymbol", &uri, 0, 0),
            request(8, "hover", &uri, 17, 5),
            change,
            request(5, "completion", &uri, 31, 12),
            request(6, "signatureHelp", &uri, 32, 8),
            request(7, "hover", &uri, 30, 13),
        ]);
        let reply = |id: u32| {
            bodies
                .iter()
                .find(|b| b.starts_with(&format!(r#"{{"jsonrpc":"2.0","id":{id},"#)))
                .unwrap_or_else(|| panic!("no reply {id}: {bodies:?}"))
        };
        let hover = reply(1);
        assert!(hover.contains("reset()` `0xd826f88f"), "{hover}");
        assert!(hover.contains("increment(uint256)` `0x7cf5dab0"), "{hover}");
        assert!(reply(2).contains(
            r#""range":{"start":{"line":26,"character":9},"end":{"line":26,"character":12}}"#
        ));
        assert_eq!(reply(3).matches(r#""uri""#).count(), 8, "{}", reply(3));
        assert!(reply(4).contains(r#""name":"storage""#) && reply(4).contains(r#""name":"count""#));
        let completion = reply(5);
        assert!(
            completion.contains(r#""label":"count""#) && completion.contains(r#""label":"owner""#)
        );
        assert!(
            reply(6).contains(r#""parameters":[{"label":"const n : uint"}]"#),
            "{}",
            reply(6)
        );
        let stored = reply(7);
        assert!(
            stored.contains("**Written by** `reset`, `increment`"),
            "{stored}"
        );
        let variant = reply(8);
        assert!(
            variant.contains("variant of `owner_action`") && variant.contains("`reset()`"),
            "{variant}"
        );
    }

    #[test]
    fn list_lengths_name_their_constants() {
        let dir = std::env::temp_dir().join(format!("lithe-lsp-sizes-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("main.lithe");
        let text = "pure function slots() : uint is 3\n\nmodule Grid is {\n  pure function cells() : uint is 4\n  pure function zero() : list(uint, cells()) is [0, 0, 0, 0]\n}\n\nuse Grid;\n\nstorage is record { ring : list(uint, slots() * 2); }\n\nexternal pure function board() : list(uint, Grid.cells()) is Grid.zero()\n";
        std::fs::write(&path, text).unwrap();
        let index = lithe::analyze(&path, text).index.expect("index");
        let named = |line: u32, col: u32| {
            let r = index
                .at(0, text, line, col)
                .unwrap_or_else(|| panic!("no ref at {line}:{col}"));
            let def = &index.defs[r.def];
            (def.name.clone(), def.at.map(|at| at.line))
        };
        assert_eq!(named(10, 39), ("slots".to_string(), Some(1)));
        assert_eq!(named(12, 50), ("cells".to_string(), Some(4)));
        assert_eq!(named(12, 45).0, "Grid");
        assert_eq!(named(5, 37), ("cells".to_string(), Some(4)));
        std::fs::remove_dir_all(&dir).unwrap();
    }

    /// Every example and standard library file indexes, and each builtin call in it resolves
    /// to its declaration.
    #[test]
    fn every_repo_file_indexes() {
        let root = std::env::current_dir().unwrap();
        let mut files = Vec::new();
        for dir in ["examples", "std", "bench"] {
            lithe::lithe_files(&root.join(dir), &mut files).unwrap();
        }
        for path in files {
            let name = path.to_string_lossy();
            if name.contains("reject") || name.ends_with(".spec.lithe") {
                continue;
            }
            let text = std::fs::read_to_string(&path).unwrap();
            let Some(index) = lithe::analyze(&path, &text).index else {
                continue;
            };
            for r in &index.refs {
                let def = &index.defs[r.def];
                if let (Kind::Builtin, Some(at)) = (def.kind, def.at) {
                    assert!(
                        index.files[at.file].std.is_some(),
                        "{}: {}",
                        path.display(),
                        def.name
                    );
                }
            }
        }
    }

    #[test]
    fn answers_for_builtins_and_imports() {
        let dir = std::env::temp_dir().join(format!("lithe-lsp-imports-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("lib")).unwrap();
        std::fs::write(
            dir.join("lib/fees.lithe"),
            "pure function fee(const x : uint) : uint is x\n",
        )
        .unwrap();
        let path = dir.join("main.lithe");
        let uri = format!("file://{}", path.display()).replace(' ', "%20");
        let good = "import \"std/evm\";\n\nstorage is record { a : address; }\n\nexternal function f() is { storage.a := Evm.sender(); }\n";
        std::fs::write(&path, good).unwrap();
        let missing = good.replace("import \"std/evm\";\n\n", "");
        let change = |text: &str| {
            frame(&format!(
                r#"{{"jsonrpc":"2.0","method":"textDocument/didChange","params":{{"textDocument":{{"uri":{},"version":2}},"contentChanges":[{{"text":{}}}]}}}}"#,
                quote(&uri),
                quote(text)
            ))
        };
        let action = frame(&format!(
            r#"{{"jsonrpc":"2.0","id":6,"method":"textDocument/codeAction","params":{{"textDocument":{{"uri":{}}},"range":{{"start":{{"line":2,"character":0}},"end":{{"line":2,"character":0}}}},"context":{{"diagnostics":[]}}}}}}"#,
            quote(&uri)
        ));
        let typing = "import \"std/tok\";\n";
        let (_, bodies) = session(&[
            frame(r#"{"jsonrpc":"2.0","id":0,"method":"initialize","params":{}}"#),
            open(&uri, good),
            request(1, "hover", &uri, 4, 47),
            request(2, "definition", &uri, 4, 47),
            request(3, "definition", &uri, 0, 10),
            request(4, "completion", &uri, 4, 44),
            change(&missing),
            action,
            change(typing),
            request(5, "completion", &uri, 0, 15),
            change("import \"./\";\n"),
            request(7, "completion", &uri, 0, 10),
        ]);
        let reply = |id: u32| {
            bodies
                .iter()
                .find(|b| b.starts_with(&format!(r#"{{"jsonrpc":"2.0","id":{id},"#)))
                .unwrap_or_else(|| panic!("no reply {id}: {bodies:?}"))
        };
        let hover = reply(1);
        assert!(
            hover.contains("intrinsic view function sender() : address")
                && hover.contains("the caller of the current frame"),
            "{hover}"
        );
        assert!(reply(2).contains("std/evm.lithe"), "{}", reply(2));
        assert!(reply(3).contains("std/evm.lithe"), "{}", reply(3));
        let members = reply(4);
        assert!(
            members.contains(r#""label":"sender""#)
                && members.contains(r#""label":"block_number""#),
            "{members}"
        );
        let fix = reply(6);
        assert!(
            fix.contains("Import `std/evm`")
                && fix.contains(r#""newText":"import \"std/evm\";\n\n""#),
            "{fix}"
        );
        let paths = reply(5);
        assert!(
            paths.contains(r#""label":"std/token/erc20""#) && !paths.contains(".lithe"),
            "{paths}"
        );
        assert!(reply(7).contains(r#""label":"./lib/fees""#), "{}", reply(7));
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn answers_for_exposed_modules_and_storage_parameters() {
        let root = std::env::current_dir().unwrap();
        let uri = |rel: &str| format!("file://{}", root.join(rel).display()).replace(' ', "%20");
        let (votes, nested) = (
            uri("examples/votes.lithe"),
            uri("examples/nested_storage.lithe"),
        );
        let text = |rel: &str| std::fs::read_to_string(root.join(rel)).unwrap();
        let (_, bodies) = session(&[
            frame(r#"{"jsonrpc":"2.0","id":0,"method":"initialize","params":{}}"#),
            open(&votes, &text("examples/votes.lithe")),
            open(&nested, &text("examples/nested_storage.lithe")),
            request(1, "hover", &votes, 35, 14),
            request(2, "hover", &votes, 8, 22),
            request(3, "hover", &nested, 38, 29),
            request(4, "definition", &nested, 49, 5),
        ]);
        let reply = |id: u32| {
            bodies
                .iter()
                .find(|b| b.starts_with(&format!(r#"{{"jsonrpc":"2.0","id":{id},"#)))
                .unwrap_or_else(|| panic!("no reply {id}: {bodies:?}"))
        };
        let declared = reply(1);
        assert!(
            declared.contains("runs `ERC20`'s external `mint`")
                && declared.contains("`mint(address,uint256)` · selector `0x40c10f19`"),
            "{declared}"
        );
        assert!(reply(2).contains("**Exposed as**"), "{}", reply(2));
        assert!(
            reply(3).contains("storage points : list(checkpoint)"),
            "{}",
            reply(3)
        );
        assert!(
            reply(4).contains(r#""start":{"line":46,"character":22}"#),
            "{}",
            reply(4)
        );
    }

    #[test]
    fn lints_fixes_and_formats_unsaved_text() {
        let uri = "file:///tmp/lithe-lsp-test/probe.lithe";
        let src = "storage is record {  n : uint; }\n\nexternal function go(const a : uint) is {\n  var b : uint := a;\n  (* lithe-ignore unused-binding: kept *)\n  const kept : uint := 1;\n  storage.n := b;\n}\n";
        let (_, bodies) = session(&[
            frame(r#"{"jsonrpc":"2.0","id":0,"method":"initialize","params":{}}"#),
            open(uri, src),
            frame(&format!(
                r#"{{"jsonrpc":"2.0","id":1,"method":"textDocument/codeAction","params":{{"textDocument":{{"uri":{}}},"range":{{"start":{{"line":3,"character":0}},"end":{{"line":3,"character":0}}}},"context":{{"diagnostics":[]}}}}}}"#,
                quote(uri)
            )),
            frame(&format!(
                r#"{{"jsonrpc":"2.0","id":2,"method":"textDocument/formatting","params":{{"textDocument":{{"uri":{}}},"options":{{"tabSize":2,"insertSpaces":true}}}}}}"#,
                quote(uri)
            )),
        ]);
        // The ignore, unsaved, silences its line; `var b` is still reported.
        assert!(
            bodies[1].contains(r#""code":"prefer-const""#) && !bodies[1].contains("unused-binding"),
            "{}",
            bodies[1]
        );
        assert!(
            bodies[2].contains(r#""newText":"const""#)
                && bodies[2]
                    .contains(r#""start":{"line":3,"character":2},"end":{"line":3,"character":5}"#),
            "{}",
            bodies[2]
        );
        assert!(
            bodies[3].contains(r#""newText":"storage is record { n : uint; }"#),
            "{}",
            bodies[3]
        );
    }

    #[test]
    fn parses_json_and_uris() {
        let msg = parse(r#"{"a":[1, {"b":"x\"\u00e9\ud83d\ude00\n"}], "c":-2.5e3}"#).unwrap();
        let b = msg.get("a").and_then(Json::last).and_then(|v| v.get("b"));
        assert_eq!(b.and_then(Json::str), Some("x\"é😀\n"));
        assert!(matches!(msg.get("c"), Some(Json::Num(n)) if n == "-2.5e3"));
        assert_eq!(
            file_path("file:///c%3A/My%20Dir/a.lithe"),
            PathBuf::from("c:/My Dir/a.lithe")
        );
    }
}
