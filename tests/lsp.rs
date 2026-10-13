//! Языковой сервер: настоящий процесс `bourbaki-lsp`, разговор по stdin/stdout.

use serde_json::{Value, json};
use std::io::{BufRead, BufReader, Write};
use std::process::{Command, Stdio};

fn send(w: &mut impl Write, v: Value) {
    let s = v.to_string();
    write!(w, "Content-Length: {}\r\n\r\n{s}", s.len()).unwrap();
    w.flush().unwrap();
}

fn recv(r: &mut impl BufRead) -> Value {
    let mut len = 0;
    loop {
        let mut line = String::new();
        r.read_line(&mut line).unwrap();
        let line = line.trim();
        if line.is_empty() {
            break;
        }
        if let Some(n) = line.strip_prefix("Content-Length: ") {
            len = n.parse().unwrap();
        }
    }
    let mut buf = vec![0; len];
    r.read_exact(&mut buf).unwrap();
    serde_json::from_slice(&buf).unwrap()
}

#[test]
fn diagnostics_and_hover() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_bourbaki-lsp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut w = child.stdin.take().unwrap();
    let mut r = BufReader::new(child.stdout.take().unwrap());
    send(
        &mut w,
        json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"capabilities": {}}}),
    );
    let init = recv(&mut r);
    assert_eq!(init["result"]["capabilities"]["hoverProvider"], true);
    send(
        &mut w,
        json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
    );

    let dir = std::env::current_dir().unwrap().join("konspekt");
    let uri = format!("file://{}/scratch.bk", dir.display());
    // вторая теорема ошибочна: S1 так не применяется
    let text = "import \"01_logic.bk\"\nopen base\nin Logical\ntheorem t {A : rel} : A ⇒ A by ch1.C8\ntheorem u {A : rel} : A ⇒ (A ∨ A) by S1\n";
    send(
        &mut w,
        json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
        "textDocument": {"uri": uri, "languageId": "bourbaki", "version": 1, "text": text}}}),
    );
    let d = recv(&mut r);
    assert_eq!(d["method"], "textDocument/publishDiagnostics");
    let diags = d["params"]["diagnostics"].as_array().unwrap();
    assert_eq!(diags.len(), 1, "{d}");
    assert_eq!(diags[0]["range"]["start"]["line"], 4);
    assert!(diags[0]["message"].as_str().unwrap().contains("S1"));

    // исправили: ошибок нет
    let fixed = text.replace("by S1", "by S2");
    send(
        &mut w,
        json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
        "textDocument": {"uri": uri, "version": 2}, "contentChanges": [{"text": fixed}]}}),
    );
    let d = recv(&mut r);
    assert_eq!(
        d["params"]["diagnostics"].as_array().unwrap().len(),
        0,
        "{d}"
    );

    // наведение на ch1.C8 показывает формулировку
    send(
        &mut w,
        json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/hover", "params": {
        "textDocument": {"uri": uri}, "position": {"line": 3, "character": 33}}}),
    );
    let h = recv(&mut r);
    let v = h["result"]["contents"]["value"].as_str().unwrap();
    assert!(v.contains("theorem ch1.C8") && v.contains("A ⇒ A"), "{v}");

    // сама прелюдия открывается без ошибок ("имя S1 уже занято" было бы ошибкой)
    let prelude = std::fs::read_to_string(dir.join("00_prelude.bk")).unwrap();
    let puri = format!("file://{}/00_prelude.bk", dir.display());
    send(
        &mut w,
        json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
        "textDocument": {"uri": puri, "languageId": "bourbaki", "version": 1, "text": prelude}}}),
    );
    let d = recv(&mut r);
    assert_eq!(
        d["params"]["diagnostics"].as_array().unwrap().len(),
        0,
        "{d}"
    );

    // sorry показывается предупреждением на строке своей теоремы
    let with_sorry = format!("{fixed}theorem v {{A : rel}} : A by sorry\n");
    send(
        &mut w,
        json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
        "textDocument": {"uri": uri, "version": 3}, "contentChanges": [{"text": with_sorry}]}}),
    );
    let d = recv(&mut r);
    let diags = d["params"]["diagnostics"].as_array().unwrap();
    assert_eq!(diags.len(), 1, "{d}");
    assert_eq!(diags[0]["severity"], 2);
    assert_eq!(diags[0]["range"]["start"]["line"], 5);

    send(
        &mut w,
        json!({"jsonrpc": "2.0", "id": 3, "method": "shutdown"}),
    );
    let _ = recv(&mut r);
    send(&mut w, json!({"jsonrpc": "2.0", "method": "exit"}));
    assert!(child.wait().unwrap().success());
}
