//! `bourbaki-lsp`: языковой сервер (LSP) для конспектов `.bk`.
//!
//! Умеет две вещи:
//! * ошибки проверки показываются в редакторе (на каждое открытие и изменение файла);
//! * наведение на имя (теорема, схема, теория, сокращение, знак) показывает, что это.
//!
//! Устроен просто: крейт `lsp-server` (тот же, что у rust-analyzer) читает и пишет
//! сообщения, а JSON разбирается вручную через `serde_json`. Изменение текста проверяет
//! файл заново целиком (вместе с импортами): это доли секунды. Если правки приходят
//! быстрее, проверяется только последний текст. `#expand` и `#unfold` в редакторе
//! пропускаются, их можно запустить из терминала (`bourbaki check`).

use bourbaki_engine::Konspekt;
use bourbaki_engine::konspekt::Report;
use lsp_server::{Connection, Message, Notification, Response};
use serde_json::{Value, json};
use std::collections::HashMap;
use std::path::PathBuf;

/// file:///a/b%20c.bk -> /a/b c.bk
fn uri_to_path(uri: &str) -> PathBuf {
    let raw = uri.strip_prefix("file://").unwrap_or(uri);
    let bytes = raw.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        let hex = (bytes[i] == b'%' && i + 2 < bytes.len())
            .then(|| u8::from_str_radix(&raw[i + 1..i + 3], 16).ok())
            .flatten();
        if let Some(b) = hex {
            out.push(b);
            i += 3;
            continue;
        }
        out.push(bytes[i]);
        i += 1;
    }
    PathBuf::from(String::from_utf8_lossy(&out).into_owned())
}

/// Строка файла (с 1) -> диапазон LSP на всю строку (без отступа).
fn line_range(text: &str, line: usize) -> Value {
    let l = line.saturating_sub(1);
    let s = text.lines().nth(l).unwrap_or("");
    // позиции в LSP по умолчанию в единицах UTF-16
    let indent: usize = s
        .chars()
        .take_while(|c| c.is_whitespace())
        .map(char::len_utf16)
        .sum();
    let end: usize = s.trim_end().chars().map(char::len_utf16).sum();
    json!({
        "start": {"line": l, "character": indent},
        "end": {"line": l, "character": end.max(indent)},
    })
}

/// Номер строки (с 1), на которой стоит `import` файла `file`; 1, если не нашлось.
fn import_line(text: &str, file: &str) -> usize {
    let name = std::path::Path::new(file)
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    text.lines()
        .position(|l| l.trim_start().starts_with("import") && !name.is_empty() && l.contains(&name))
        .map(|i| i + 1)
        .unwrap_or(1)
}

/// Номер строки (с 1) с заголовком теоремы `full` (полное имя, например ch1.C8).
fn theorem_line(text: &str, full: &str) -> usize {
    let short = full.rsplit('.').next().unwrap_or(full);
    text.lines()
        .position(|l| {
            let mut w = l.split_whitespace();
            matches!(w.next(), Some("theorem" | "lemma"))
                && w.next()
                    .is_some_and(|n| n.split(['{', '(', ':']).next() == Some(short))
        })
        .map(|i| i + 1)
        .unwrap_or(1)
}

/// Проверить документ и вернуть диагностику и состояние (для подсказок).
/// `#expand` и `#unfold` в редакторе не выполняются: они бывают очень долгими.
fn check(uri: &str, text: &str) -> (Vec<Value>, Konspekt) {
    let path = uri_to_path(uri);
    let mut k = Konspekt::new();
    k.skip_expand = true;
    let r: Report = k.check_source(text, &path);
    let me = path.display().to_string();
    let mut diags = Vec::new();
    for e in &r.errors {
        // ошибка в импортированном файле показывается на строке его import
        let (line, msg) = if e.file == me {
            (e.line.max(1), e.msg.clone())
        } else {
            (
                import_line(text, &e.file),
                format!("{}:{}: {}", e.file, e.line, e.msg),
            )
        };
        diags.push(json!({
            "range": line_range(text, line),
            "severity": 1,
            "source": "bourbaki",
            "message": msg,
        }));
    }
    for name in &r.sorry {
        diags.push(json!({
            "range": line_range(text, theorem_line(text, name)),
            "severity": 2,
            "source": "bourbaki",
            "message": format!("{name} опирается на sorry"),
        }));
    }
    (diags, k)
}

/// Слово под курсором (символ `character` в единицах UTF-16).
fn word_at(text: &str, line: usize, character: usize) -> Option<String> {
    let s = text.lines().nth(line)?;
    let chars: Vec<char> = s.chars().collect();
    // перевести UTF-16 позицию в номер символа
    let mut u16pos = 0;
    let mut idx = chars.len();
    for (i, c) in chars.iter().enumerate() {
        if u16pos >= character {
            idx = i;
            break;
        }
        u16pos += c.len_utf16();
    }
    let is_word = |c: char| !c.is_whitespace() && !"(){}[],;:|^".contains(c);
    let mut a = idx.min(chars.len());
    while a > 0 && is_word(chars[a - 1]) {
        a -= 1;
    }
    let mut b = idx.min(chars.len());
    while b < chars.len() && is_word(chars[b]) {
        b += 1;
    }
    (a < b).then(|| chars[a..b].iter().collect())
}

/// Открытые документы: текст, последняя проверка и очередь на проверку.
#[derive(Default)]
struct Docs {
    texts: HashMap<String, String>,
    checked: HashMap<String, Konspekt>,
    dirty: Vec<String>,
}

/// Обработать одно сообщение. `true` значит: пора выходить.
fn handle(
    conn: &Connection,
    msg: Message,
    docs: &mut Docs,
) -> Result<bool, Box<dyn std::error::Error + Sync + Send>> {
    match msg {
        Message::Request(req) => {
            if conn.handle_shutdown(&req)? {
                return Ok(true);
            }
            if req.method == "textDocument/hover" {
                let p = &req.params;
                let uri = p["textDocument"]["uri"].as_str().unwrap_or("");
                let line = p["position"]["line"].as_u64().unwrap_or(0) as usize;
                let ch = p["position"]["character"].as_u64().unwrap_or(0) as usize;
                let result = match (docs.texts.get(uri), docs.checked.get(uri)) {
                    (Some(text), Some(k)) => word_at(text, line, ch).and_then(|w| k.describe(&w)),
                    _ => None,
                }
                .map(|d| json!({"contents": {"kind": "markdown", "value": format!("```\n{d}\n```")}}))
                .unwrap_or(Value::Null);
                conn.sender
                    .send(Message::Response(Response::new_ok(req.id, result)))?;
            } else {
                conn.sender.send(Message::Response(Response::new_err(
                    req.id,
                    lsp_server::ErrorCode::MethodNotFound as i32,
                    format!("не умею {}", req.method),
                )))?;
            }
        }
        Message::Notification(n) => {
            let p = &n.params;
            let uri = p["textDocument"]["uri"].as_str().unwrap_or("").to_string();
            let text = match n.method.as_str() {
                "textDocument/didOpen" => p["textDocument"]["text"].as_str().map(String::from),
                "textDocument/didChange" => p["contentChanges"]
                    .as_array()
                    .and_then(|a| a.last())
                    .and_then(|c| c["text"].as_str())
                    .map(String::from),
                "textDocument/didClose" => {
                    docs.texts.remove(&uri);
                    docs.checked.remove(&uri);
                    docs.dirty.retain(|u| *u != uri);
                    None
                }
                _ => None,
            };
            if let Some(text) = text {
                docs.texts.insert(uri.clone(), text);
                if !docs.dirty.contains(&uri) {
                    docs.dirty.push(uri);
                }
            }
        }
        Message::Response(_) => {}
    }
    Ok(false)
}

fn main() -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    let (conn, io) = Connection::stdio();
    conn.initialize(json!({
        "textDocumentSync": 1,
        "hoverProvider": true,
    }))?;
    let mut docs = Docs::default();
    'main: while let Ok(msg) = conn.receiver.recv() {
        if handle(&conn, msg, &mut docs)? {
            break;
        }
        // пока проверяли, могли прийти ещё правки: берём все, проверяем только последний текст
        while let Ok(msg) = conn.receiver.try_recv() {
            if handle(&conn, msg, &mut docs)? {
                break 'main;
            }
        }
        for uri in std::mem::take(&mut docs.dirty) {
            let Some(text) = docs.texts.get(&uri) else {
                continue;
            };
            let (diags, k) = check(&uri, text);
            docs.checked.insert(uri.clone(), k);
            conn.sender.send(Message::Notification(Notification::new(
                "textDocument/publishDiagnostics".into(),
                json!({"uri": uri, "diagnostics": diags}),
            )))?;
        }
    }
    // поток записи кончается, только когда закрыт канал: сначала отпустить соединение
    drop(conn);
    io.join()?;
    Ok(())
}
