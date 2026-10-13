//! `bourbaki`: проверка конспектов `.bk`.
//!
//! ```text
//! bourbaki check файл.bk [файл2.bk ...]   проверить
//! bourbaki expand файл.bk ТЕОРЕМА         раскрыть теорему до S1-S7 и C1 и выписать
//! ```
//! Флаг `--prefix` печатает формулы в польской записи.

use ariadne::{Color, Config, IndexType, Label, Report, ReportKind, Source};
use bourbaki_engine::Konspekt;
use bourbaki_engine::konspekt::CheckError;
use bourbaki_engine::syntax::{Style, set_style};
use std::path::Path;
use std::process::ExitCode;

fn usage() -> ExitCode {
    eprintln!(
        "использование:\n  bourbaki check ФАЙЛ.bk...\n  bourbaki expand ФАЙЛ.bk ТЕОРЕМА\n  флаг --prefix: печатать в польской записи"
    );
    ExitCode::from(2)
}

/// Цвет только в терминале и без NO_COLOR.
fn color() -> bool {
    use std::io::IsTerminal;
    std::io::stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none()
}

/// Показать ошибку с куском исходника (если файл можно прочитать).
fn show_error(e: &CheckError) {
    let Ok(src) = std::fs::read_to_string(&e.file) else {
        eprintln!("ошибка: {e}");
        return;
    };
    if e.line == 0 {
        eprintln!("ошибка: {e}");
        return;
    }
    // байтовый диапазон строки e.line (с 1), без отступа
    let mut start = 0;
    for (i, l) in src.split_inclusive('\n').enumerate() {
        if i + 1 == e.line {
            let indent = l.len() - l.trim_start().len();
            let span = start + indent..start + l.trim_end().len();
            let name = e.file.as_str();
            let r = Report::build(ReportKind::Error, (name, span.clone()))
                .with_config(
                    Config::default()
                        .with_index_type(IndexType::Byte)
                        .with_color(color()),
                )
                .with_message(&e.msg)
                .with_label(
                    Label::new((name, span))
                        .with_message("здесь")
                        .with_color(Color::Red),
                )
                .finish();
            let _ = r.eprint((name, Source::from(src.as_str())));
            return;
        }
        start += l.len();
    }
    eprintln!("ошибка: {e}");
}

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    if let Some(i) = args.iter().position(|a| a == "--prefix") {
        set_style(Style::Prefix);
        args.remove(i);
    }
    let Some(cmd) = args.first().cloned() else {
        return usage();
    };
    let mut k = Konspekt::new();
    match cmd.as_str() {
        "check" if args.len() >= 2 => {
            let mut ok = true;
            for f in &args[1..] {
                let r = k.check_file(Path::new(f));
                for o in &r.output {
                    println!("{o}");
                }
                for e in &r.errors {
                    show_error(e);
                }
                println!(
                    "{}: теорем {}, с sorry {}, ошибок {}",
                    r.file,
                    r.checked.len(),
                    r.sorry.len(),
                    r.errors.len()
                );
                ok &= r.is_ok();
            }
            if ok {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            }
        }
        "expand" if args.len() == 3 => {
            let r = k.check_file(Path::new(&args[1]));
            if !r.is_ok() {
                r.errors.iter().for_each(show_error);
                return ExitCode::FAILURE;
            }
            match k.expand(&args[2]) {
                Ok(t) => {
                    let d = t.demonstration();
                    match d.verify() {
                        Ok(()) => {
                            print!("{d}");
                            println!("{} строк, проверено.", d.len());
                            ExitCode::SUCCESS
                        }
                        Err(e) => {
                            println!("раскрытие не прошло проверку: {e}");
                            ExitCode::FAILURE
                        }
                    }
                }
                Err(e) => {
                    show_error(&e);
                    ExitCode::FAILURE
                }
            }
        }
        _ => usage(),
    }
}
