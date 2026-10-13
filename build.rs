//! Сборка "книги" для `cargo doc`: каждый файл `konspekt/*.bk` превращается в страницу
//! документации. Комментарии `--` в начале строки становятся текстом (в нём работает
//! LaTeX: `$...$` и `$$...$$`), всё остальное показывается как код.

use std::fmt::Write as _;
use std::fs;
use std::path::Path;

/// Экранировать формулу для markdown: тогда markdown не тронет `_`, `*`, `\{` и т.п.,
/// и KaTeX получит формулу ровно в том виде, в каком она написана.
fn escape_math(m: &str) -> String {
    let mut out = String::new();
    for c in m.chars() {
        if c.is_ascii_punctuation() && c != '$' {
            out.push('\\');
        }
        out.push(c);
    }
    out
}

/// Строка текста: формулы между `$` экранируются, остальное как есть.
fn prose(line: &str) -> String {
    let mut out = String::new();
    let mut rest = line;
    while let Some(i) = rest.find('$') {
        out.push_str(&rest[..i]);
        let after = &rest[i..];
        let delim = if after.starts_with("$$") { "$$" } else { "$" };
        let body = &after[delim.len()..];
        match body.find(delim) {
            Some(j) => {
                out.push_str(delim);
                out.push_str(&escape_math(&body[..j]));
                out.push_str(delim);
                rest = &body[j + delim.len()..];
            }
            None => {
                out.push_str(after);
                rest = "";
            }
        }
    }
    out.push_str(rest);
    out
}

enum Block {
    None,
    Prose,
    Code,
    Pre,
}

fn convert(src: &str) -> String {
    let mut out = String::new();
    let mut state = Block::None;
    let close = |out: &mut String, state: &mut Block| {
        match state {
            Block::Code | Block::Pre => out.push_str("```\n\n"),
            Block::Prose => out.push('\n'),
            Block::None => {}
        }
        *state = Block::None;
    };
    let lines: Vec<&str> = src.lines().collect();
    for (i, line) in lines.iter().enumerate() {
        if let Some(c) = line.strip_prefix("--") {
            let c = c.strip_prefix(' ').unwrap_or(c);
            if c.trim().is_empty() {
                close(&mut out, &mut state);
            } else if c.starts_with(' ') {
                // отступ внутри комментария: пример кода, показывается как есть
                if !matches!(state, Block::Pre) {
                    close(&mut out, &mut state);
                    out.push_str("```text\n");
                    state = Block::Pre;
                }
                let _ = writeln!(out, "{}", c.trim_start());
            } else {
                if !matches!(state, Block::Prose) {
                    close(&mut out, &mut state);
                    state = Block::Prose;
                }
                // каждая строка комментария остаётся отдельной строкой
                let _ = writeln!(out, "{}  ", prose(c));
            }
        } else if line.trim().is_empty() {
            // пустая строка внутри кода остаётся, если дальше снова код
            let next_code = lines[i + 1..]
                .iter()
                .find(|l| !l.trim().is_empty())
                .is_some_and(|l| !l.starts_with("--"));
            if matches!(state, Block::Code) && next_code {
                out.push('\n');
            } else {
                close(&mut out, &mut state);
            }
        } else {
            if !matches!(state, Block::Code) {
                close(&mut out, &mut state);
                out.push_str("```text\n");
                state = Block::Code;
            }
            let _ = writeln!(out, "{line}");
        }
    }
    close(&mut out, &mut state);
    out
}

fn main() {
    println!("cargo::rerun-if-changed=konspekt");
    let out_dir = std::env::var("OUT_DIR").unwrap();
    let book = Path::new(&out_dir).join("book");
    fs::create_dir_all(&book).unwrap();
    let mut files: Vec<_> = fs::read_dir("konspekt")
        .unwrap()
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "bk"))
        .collect();
    files.sort();
    let mut mods = String::new();
    for p in files {
        println!("cargo::rerun-if-changed={}", p.display());
        let stem = p.file_stem().unwrap().to_string_lossy().into_owned();
        // 01_logic -> logic: номер задаёт порядок, имя модуля без него
        let name = stem.trim_start_matches(|c: char| c.is_ascii_digit() || c == '_');
        let name = if name.is_empty() { stem.as_str() } else { name };
        let md = format!(
            "{}\n*Исходный файл: `konspekt/{stem}.bk`.*\n",
            convert(&fs::read_to_string(&p).unwrap())
        );
        fs::write(book.join(format!("{stem}.md")), md).unwrap();
        let _ = writeln!(
            mods,
            "#[doc = include_str!(concat!(env!(\"OUT_DIR\"), \"/book/{stem}.md\"))]\npub mod {name} {{}}\n"
        );
    }
    fs::write(book.join("mods.rs"), mods).unwrap();
}
