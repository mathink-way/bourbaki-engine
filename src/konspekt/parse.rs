//! Разбор текста `.bk` в структуры из [`super::ast`].
//!
//! Формат построчный, ключевые слова английские. Комментарий: `--` до конца строки.
//! Подробное описание формата в `docs/FORMAT.md`.

use super::ast::*;
use crate::sign::Kind;
use crate::syntax::Notation;

/// Ошибка разбора: номер строки и сообщение.
pub type ParseError = (usize, String);

fn strip_comment(s: &str) -> &str {
    match s.find("--") {
        Some(i) => s[..i].trim_end(),
        None => s.trim_end(),
    }
}

fn first_word(s: &str) -> (&str, &str) {
    let s = s.trim_start();
    match s.find(char::is_whitespace) {
        Some(i) => (&s[..i], s[i..].trim_start()),
        None => (s, ""),
    }
}

/// Найти слово `w` как отдельное слово; вернуть (до, после).
fn split_word<'a>(s: &'a str, w: &str) -> Option<(&'a str, &'a str)> {
    let mut start = 0;
    while let Some(i) = s[start..].find(w) {
        let at = start + i;
        let before_ok = at == 0 || s[..at].ends_with(char::is_whitespace);
        let end = at + w.len();
        let after_ok = end == s.len() || s[end..].starts_with(char::is_whitespace);
        if before_ok && after_ok {
            return Some((s[..at].trim_end(), s[end..].trim_start()));
        }
        start = end;
    }
    None
}

/// То же, но последнее вхождение.
fn rsplit_word<'a>(s: &'a str, w: &str) -> Option<(&'a str, &'a str)> {
    let mut best = None;
    let mut start = 0;
    while let Some((a, b)) = split_word(&s[start..], w) {
        let at = start + a.len();
        best = Some((s[..at].trim_end(), b));
        start = s.len() - b.len();
    }
    best
}

/// Разобрать весь файл.
pub fn parse_document(src: &str) -> Result<Vec<Located>, ParseError> {
    let lines: Vec<&str> = src.lines().collect();
    let mut i = 0;
    let mut out = Vec::new();
    while i < lines.len() {
        let no = i + 1;
        let text = strip_comment(lines[i]).trim();
        i += 1;
        if text.is_empty() {
            continue;
        }
        let (w, rest) = first_word(text);
        let e = |m: String| (no, m);
        let item = match w {
            "import" => Item::Import(rest.trim().trim_matches('"').to_string()),
            "namespace" => Item::Namespace(nonempty(rest, "имя пространства имён").map_err(e)?),
            "end" => Item::End,
            "open" => Item::Open(nonempty(rest, "имя пространства имён").map_err(e)?),
            "alias" => {
                let (n, t) = rest
                    .split_once(":=")
                    .ok_or_else(|| e("alias имя := полное.имя".into()))?;
                Item::Alias {
                    name: n.trim().to_string(),
                    target: t.trim().to_string(),
                }
            }
            "sign" => parse_sign(rest).map_err(e)?,
            "abbrev" => parse_abbrev(rest).map_err(e)?,
            "scheme" | "schema" => parse_scheme(rest).map_err(e)?,
            "theory" => {
                let (decl, next) = parse_theory(rest, &lines, i, no)?;
                i = next;
                Item::Theory(decl)
            }
            "in" => Item::In(nonempty(rest, "имя теории").map_err(e)?),
            "model" => {
                let (decl, next) = parse_model(rest, &lines, i, no)?;
                i = next;
                Item::Model(decl)
            }
            "transfer" => {
                let usage = "transfer ТЕОРЕМА via МОДЕЛЬ [as НОВОЕ_ИМЯ]";
                let (thm, r) = split_word(rest, "via").ok_or_else(|| e(usage.into()))?;
                let (model, name) = match split_word(r, "as") {
                    Some((m, n)) => (m, Some(nonempty(n, "новое имя").map_err(e)?)),
                    None => (r, None),
                };
                Item::Transfer {
                    theorem: nonempty(thm, "имя теоремы").map_err(e)?,
                    model: nonempty(model, "имя модели").map_err(e)?,
                    name,
                }
            }
            "theorem" | "lemma" => {
                let (decl, next) = parse_theorem(rest, &lines, i, no)?;
                i = next;
                Item::Theorem(decl)
            }
            "#set" | "#format" => {
                let n = match rest.trim() {
                    "infix" => Notation::Infix,
                    "prefix" => Notation::Prefix,
                    other => {
                        return Err(e(format!("{w} infix или {w} prefix, а не \"{other}\"")));
                    }
                };
                if w == "#set" {
                    Item::Set(n)
                } else {
                    Item::Format(n)
                }
            }
            "#formation" => Item::Formation(nonempty(rest, "формула").map_err(e)?),
            "#log" => Item::Log,
            "#show" => Item::Show(rest.to_string()),
            "#signs" => Item::Signs(rest.to_string()),
            "#print" => Item::Print(rest.trim().to_string()),
            "#expand" => Item::Expand {
                name: rest.trim().to_string(),
                full: false,
            },
            "#unfold" => Item::Expand {
                name: rest.trim().to_string(),
                full: true,
            },
            _ => return Err(e(format!("непонятное начало строки \"{w}\""))),
        };
        out.push(Located { line: no, item });
    }
    Ok(out)
}

fn nonempty(s: &str, what: &str) -> Result<String, String> {
    let s = s.trim();
    if s.is_empty() {
        Err(format!("нужно {what}"))
    } else {
        Ok(s.to_string())
    }
}

/// `[a, b]` в начале строки: имена для набора.
fn take_aliases(s: &str) -> Result<(Vec<String>, &str), String> {
    let s = s.trim_start();
    if let Some(r) = s.strip_prefix('[') {
        let end = r.find(']').ok_or("не закрыта ] в списке имён для набора")?;
        let al = r[..end]
            .split(|c: char| c == ',' || c.is_whitespace())
            .filter(|x| !x.is_empty())
            .map(|x| x.to_string())
            .collect();
        Ok((al, &r[end + 1..]))
    } else {
        Ok((vec![], s))
    }
}

fn kind_word(w: &str) -> Option<Kind> {
    match w {
        "rel" => Some(Kind::Relational),
        "term" => Some(Kind::Substantive),
        _ => None,
    }
}

/// `sign ∈ [\in] : rel 2 infix`
fn parse_sign(rest: &str) -> Result<Item, String> {
    let (name, rest) = first_word(rest);
    let (aliases, rest) = take_aliases(rest)?;
    let rest = rest
        .trim_start()
        .strip_prefix(':')
        .ok_or("после имени знака нужно \":\" и вид (rel или term)")?;
    let words: Vec<&str> = rest.split_whitespace().collect();
    let kind = words
        .first()
        .and_then(|w| kind_word(w))
        .ok_or("вид знака: rel (реляционный) или term (субстантивный)")?;
    let weight: usize = words
        .get(1)
        .and_then(|w| w.parse().ok())
        .ok_or("после вида нужен вес знака (число)")?;
    let infix = match words.get(2) {
        None => false,
        Some(&"infix") => true,
        Some(w) => return Err(format!("непонятное \"{w}\" (может быть только infix)")),
    };
    Ok(Item::Sign {
        name: name.to_string(),
        aliases,
        kind,
        weight,
        infix,
    })
}

/// Группа `{A B : rel 1}` или `(A B : term)`.
fn parse_group(inner: &str) -> Result<MetaDecl, String> {
    let (names, sort) = inner
        .split_once(':')
        .ok_or_else(|| format!("в группе \"{inner}\" нет \":\""))?;
    let names: Vec<String> = names.split_whitespace().map(|s| s.to_string()).collect();
    if names.is_empty() {
        return Err(format!("в группе \"{inner}\" нет имён"));
    }
    let words: Vec<&str> = sort.split_whitespace().collect();
    let kind = words
        .first()
        .and_then(|w| kind_word(w))
        .ok_or_else(|| format!("в группе \"{inner}\": вид rel или term"))?;
    let weight = match words.get(1) {
        Some(w) => w
            .parse()
            .map_err(|_| format!("в группе \"{inner}\": вес должен быть числом"))?,
        None => 0,
    };
    Ok(MetaDecl {
        names,
        kind,
        weight,
    })
}

/// Найти парную скобку к открывающей в позиции 0.
fn matching(s: &str, open: char, close: char) -> Option<usize> {
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        if c == open {
            depth += 1;
        } else if c == close {
            depth -= 1;
            if depth == 0 {
                return Some(i);
            }
        }
    }
    None
}

/// `abbrev ⊂ [\subset] (A B : term) infix := (∀z)(z ∈ A ⇒ z ∈ B)`, `abbrev ExA (...) nofold := ...`
fn parse_abbrev(rest: &str) -> Result<Item, String> {
    let (name, rest) = first_word(rest);
    let (aliases, mut rest) = take_aliases(rest)?;
    let mut params = Vec::new();
    let mut infix = false;
    let mut nofold = false;
    loop {
        rest = rest.trim_start();
        if rest.starts_with('(') {
            let end = matching(rest, '(', ')').ok_or("не закрыта скобка параметров")?;
            params.push(parse_group(&rest[1..end])?);
            rest = &rest[end + 1..];
        } else if let Some(r) = rest.strip_prefix(":=") {
            return Ok(Item::Abbrev {
                name: name.to_string(),
                aliases,
                params,
                body: r.trim().to_string(),
                infix,
                nofold,
            });
        } else {
            let (w, r) = first_word(rest);
            if w == "infix" {
                infix = true;
                rest = r;
            } else if w == "nofold" {
                nofold = true;
                rest = r;
            } else {
                return Err(format!(
                    "в abbrev ожидалось (параметры), infix, nofold или :=, а стоит \"{w}\""
                ));
            }
        }
    }
}

/// `{A B : rel} {R : rel 1}` подряд; возвращает группы и остаток.
fn take_meta_groups(mut rest: &str) -> Result<(Vec<MetaDecl>, &str), String> {
    let mut metas = Vec::new();
    loop {
        rest = rest.trim_start();
        if rest.starts_with('{') {
            let end = matching(rest, '{', '}').ok_or("не закрыта { в объявлении метапеременных")?;
            metas.push(parse_group(&rest[1..end])?);
            rest = &rest[end + 1..];
        } else {
            return Ok((metas, rest));
        }
    }
}

/// `scheme S1 {A : rel} : (A ∨ A) ⇒ A`
fn parse_scheme(rest: &str) -> Result<Item, String> {
    let (name, rest) = first_word(rest);
    let (metas, rest) = take_meta_groups(rest)?;
    let pattern = rest
        .trim_start()
        .strip_prefix(':')
        .ok_or("в схеме после метапеременных нужно \":\" и образец")?;
    Ok(Item::Scheme {
        name: name.to_string(),
        metas,
        pattern: pattern.trim().to_string(),
    })
}

fn parse_theory(
    rest: &str,
    lines: &[&str],
    mut i: usize,
    no: usize,
) -> Result<(TheoryDecl, usize), ParseError> {
    let rest = rest.trim();
    let (head, inline) = match rest.find('{') {
        Some(k) => (&rest[..k], Some(&rest[k + 1..])),
        None => return Err((no, "после имени теории нужна {".into())),
    };
    let words: Vec<&str> = head.split_whitespace().collect();
    let name = words
        .first()
        .ok_or((no, "нет имени теории".to_string()))?
        .to_string();
    let extends = match words.get(1) {
        Some(&"extends") => Some(
            words
                .get(2)
                .ok_or((no, "после extends нужно имя теории".to_string()))?
                .to_string(),
        ),
        Some(w) => return Err((no, format!("непонятное \"{w}\" в заголовке теории"))),
        None => None,
    };
    let mut decl = TheoryDecl {
        name,
        extends,
        signs: vec![],
        schemes: vec![],
        axioms: vec![],
        line: no,
    };
    let mut body: Vec<(usize, String)> = Vec::new();
    let mut closed = false;
    if let Some(inl) = inline {
        let inl = inl.trim();
        if let Some(inner) = inl.strip_suffix('}') {
            closed = true;
            if !inner.trim().is_empty() {
                body.push((no, inner.trim().to_string()));
            }
        } else if !inl.is_empty() {
            body.push((no, inl.to_string()));
        }
    }
    while !closed {
        if i >= lines.len() {
            return Err((no, "теория не закрыта }".into()));
        }
        let t = strip_comment(lines[i]).trim();
        i += 1;
        if t == "}" {
            closed = true;
        } else if !t.is_empty() {
            body.push((i, t.to_string()));
        }
    }
    for (ln, t) in body {
        let (w, r) = first_word(&t);
        match w {
            "signs" => decl
                .signs
                .extend(r.split_whitespace().map(|s| s.to_string())),
            "schemes" => decl
                .schemes
                .extend(r.split_whitespace().map(|s| s.to_string())),
            "axiom" => {
                let (name, f) = r
                    .split_once(':')
                    .ok_or((ln, "axiom ИМЯ : формула".to_string()))?;
                decl.axioms
                    .push((name.trim().to_string(), f.trim().to_string()));
            }
            _ => {
                return Err((
                    ln,
                    format!("внутри теории ожидалось signs/schemes/axiom, а стоит \"{w}\""),
                ));
            }
        }
    }
    Ok((decl, i))
}

/// `model M : Source -> Target [with a := T; ...] {` и строки `ИМЯ by ...` до `}`.
fn parse_model(
    rest: &str,
    lines: &[&str],
    mut i: usize,
    no: usize,
) -> Result<(ModelDecl, usize), ParseError> {
    let e = |m: String| (no, m);
    let usage = "model M : Source -> Target with a := T; b := U {";
    let head = rest
        .trim()
        .strip_suffix('{')
        .ok_or_else(|| e(format!("в конце заголовка модели нужна {{: {usage}")))?;
    let (name, r) = head
        .split_once(':')
        .ok_or_else(|| e(format!("после имени модели нужно \":\": {usage}")))?;
    let (theories, with) = match split_word(r, "with") {
        Some((t, w)) => (t, Some(w)),
        None => (r.trim(), None),
    };
    let (source, target) = theories
        .split_once("->")
        .or_else(|| theories.split_once('→'))
        .ok_or_else(|| e(format!("нужно \"Source -> Target\": {usage}")))?;
    let mut subst = Vec::new();
    if let Some(w) = with {
        for item in w.split(';').map(|s| s.trim()).filter(|s| !s.is_empty()) {
            let (x, t) = item
                .split_once(":=")
                .ok_or_else(|| e(format!("в модели ожидалось \"a := T\", а стоит \"{item}\"")))?;
            subst.push((x.trim().to_string(), t.trim().to_string()));
        }
    }
    let mut decl = ModelDecl {
        name: nonempty(name, "имя модели").map_err(e)?,
        source: nonempty(source, "теория-источник").map_err(e)?,
        target: nonempty(target, "теория-цель").map_err(e)?,
        subst,
        obligations: vec![],
        line: no,
    };
    loop {
        if i >= lines.len() {
            return Err(e("модель не закрыта }".into()));
        }
        let ln = i + 1;
        let t = strip_comment(lines[i]).trim();
        i += 1;
        if t.is_empty() {
            continue;
        }
        if t == "}" {
            return Ok((decl, i));
        }
        let (ax, j) = split_word(t, "by").ok_or_else(|| {
            (
                ln,
                "в модели строки вида \"ИМЯ_АКСИОМЫ by обоснование\"".to_string(),
            )
        })?;
        let just = parse_just(j).map_err(|m| (ln, m))?;
        decl.obligations.push((ax.trim().to_string(), just, ln));
    }
}

fn parse_theorem(
    rest: &str,
    lines: &[&str],
    i: usize,
    no: usize,
) -> Result<(TheoremDecl, usize), ParseError> {
    let e = |m: String| (no, m);
    let rest = rest.trim();
    let name_end = rest
        .find(|c: char| c.is_whitespace() || c == '{' || c == '(' || c == ':')
        .unwrap_or(rest.len());
    let name = rest[..name_end].to_string();
    if name.is_empty() {
        return Err(e("нет имени теоремы".into()));
    }
    let mut rest = &rest[name_end..];
    let mut metas = Vec::new();
    let mut hyps = Vec::new();
    loop {
        rest = rest.trim_start();
        if rest.starts_with('{') {
            let end = matching(rest, '{', '}').ok_or_else(|| e("не закрыта {".into()))?;
            metas.push(parse_group(&rest[1..end]).map_err(e)?);
            rest = &rest[end + 1..];
        } else if rest.starts_with('(') {
            let end =
                matching(rest, '(', ')').ok_or_else(|| e("не закрыта ( у гипотезы".into()))?;
            let (label, f) = rest[1..end]
                .split_once(':')
                .ok_or_else(|| e("гипотеза пишется как (h : формула)".into()))?;
            hyps.push((label.trim().to_string(), f.trim().to_string()));
            rest = &rest[end + 1..];
        } else if let Some(r) = rest.strip_prefix(':') {
            rest = r;
            break;
        } else {
            return Err(e(format!(
                "в заголовке теоремы ожидалось {{метапеременные}}, (гипотеза) или \":\", а стоит \"{rest}\""
            )));
        }
    }
    let rest = rest.trim();
    // доказательство в одну строку: theorem T ... : φ by ...
    let (stmt, one_liner) = if let Some(s) = rest.strip_suffix('{') {
        (s.trim(), None)
    } else if let Some((s, j)) = split_word(rest, "by") {
        (s, Some(j))
    } else {
        return Err(e(
            "после утверждения нужна { (доказательство по строкам) или by (в одну строку)".into(),
        ));
    };
    let (statement, theory) = match rsplit_word(stmt, "in") {
        Some((s, t)) if !t.contains(char::is_whitespace) && !t.is_empty() => {
            (s.to_string(), Some(t.to_string()))
        }
        _ => (stmt.to_string(), None),
    };
    let (proof, next) = match one_liner {
        Some(j) => {
            let just = parse_just(j).map_err(e)?;
            (
                vec![Line {
                    label: None,
                    formula: Some(statement.clone()),
                    just,
                    block: vec![],
                    line: no,
                }],
                i,
            )
        }
        None => parse_block(lines, i)?,
    };
    Ok((
        TheoremDecl {
            name,
            metas,
            hyps,
            statement,
            theory,
            proof,
            line: no,
        },
        next,
    ))
}

/// Строки доказательства до закрывающей `}`; возвращает их и номер следующей строки.
fn parse_block(lines: &[&str], mut i: usize) -> Result<(Vec<Line>, usize), ParseError> {
    let start = i;
    let mut out = Vec::new();
    loop {
        if i >= lines.len() {
            return Err((start, "блок доказательства не закрыт }".into()));
        }
        let no = i + 1;
        let t = strip_comment(lines[i]).trim();
        i += 1;
        if t.is_empty() {
            continue;
        }
        if t == "}" {
            return Ok((out, i));
        }
        let (mut line, opens) = parse_proof_line(t).map_err(|m| (no, m))?;
        line.line = no;
        if opens {
            let (block, next) = parse_block(lines, i)?;
            line.block = block;
            i = next;
        }
        out.push(line);
    }
}

fn is_label(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
}

fn parse_proof_line(t: &str) -> Result<(Line, bool), String> {
    let mut t = t.trim();
    let opens = t.ends_with('{');
    if opens {
        t = t[..t.len() - 1].trim_end();
    }
    let (head, just_text) =
        split_word(t, "by").ok_or("строка доказательства: \"формула by обоснование\"")?;
    // необязательная метка: "3." или "h."
    let (label, f) = match head.split_once(". ") {
        Some((l, rest)) if is_label(l.trim()) => (Some(l.trim().to_string()), rest.trim()),
        _ => (None, head.trim()),
    };
    let formula = if f == "_" || f.is_empty() {
        None
    } else {
        Some(f.to_string())
    };
    let just = parse_just(just_text)?;
    Ok((
        Line {
            label,
            formula,
            just,
            block: vec![],
            line: 0,
        },
        opens,
    ))
}

fn parse_assigns(s: &str) -> Result<Vec<Assign>, String> {
    let mut out = Vec::new();
    for item in s.split(';').map(|s| s.trim()).filter(|s| !s.is_empty()) {
        let (lhs, rhs) = item
            .split_once(":=")
            .ok_or_else(|| format!("после with ожидалось \"A := ...\", а стоит \"{item}\""))?;
        let lhs = lhs.trim();
        let (n, letters) = match lhs.find(['(', '{']) {
            Some(k) => {
                let inner = lhs[k + 1..].trim_end_matches([')', '}']);
                let ls = inner
                    .split(|c: char| c == ',' || c.is_whitespace())
                    .filter(|x| !x.is_empty())
                    .map(|x| x.to_string())
                    .collect();
                (lhs[..k].trim(), ls)
            }
            None => (lhs, vec![]),
        };
        out.push(Assign {
            name: n.to_string(),
            letters,
            value: rhs.trim().to_string(),
        });
    }
    Ok(out)
}

/// Разобрать то, что стоит после `by`.
pub fn parse_just(j: &str) -> Result<Just, String> {
    let (main, with) = match split_word(j, "with") {
        Some((m, w)) => (m, Some(w)),
        None => (j.trim(), None),
    };
    let toks: Vec<&str> = main.split_whitespace().collect();
    let rule = *toks.first().ok_or("после by нужно обоснование")?;
    let args: Vec<String> = toks[1..].iter().map(|s| s.to_string()).collect();
    let one_ref = |what: &str| -> Result<String, String> {
        match args.len() {
            0 => Ok("^".to_string()),
            1 => Ok(args[0].clone()),
            _ => Err(format!("{what} ссылается на одну строку")),
        }
    };
    let no_with = |what: &str| -> Result<(), String> {
        if with.is_some() {
            Err(format!("у {what} нет параметров with"))
        } else {
            Ok(())
        }
    };
    match rule {
        "sorry" => Ok(Just::Sorry),
        "taut" => {
            no_with("taut")?;
            Ok(Just::Taut(args))
        }
        "axiom" => Ok(Just::Axiom(args.first().cloned())),
        "chain" => {
            no_with("chain")?;
            Ok(Just::Chain(args))
        }
        "assume" | "C14" => Ok(Just::Assume(args.first().cloned())),
        "contra" | "C15" => Ok(Just::Contra(args.first().cloned())),
        "mp" | "C1" => {
            no_with("mp")?;
            if args.len() != 2 {
                return Err(format!(
                    "mp ссылается на две строки, а здесь {}",
                    args.len()
                ));
            }
            Ok(Just::MP(args[0].clone(), args[1].clone()))
        }
        "gen" | "C27" => {
            let x = with.ok_or("обобщение: by gen 3 with x")?.trim().to_string();
            Ok(Just::Generalize {
                letter: x,
                from: one_ref("gen")?,
            })
        }
        "subst" | "C3" => {
            let w = with.ok_or("подстановка: by subst 3 with x := T")?;
            let (x, t) = w
                .split_once(":=")
                .ok_or("подстановка: by subst 3 with x := T")?;
            Ok(Just::Subst {
                letter: x.trim().to_string(),
                term: t.trim().to_string(),
                from: one_ref("subst")?,
            })
        }
        _ => Ok(Just::Use {
            name: rule.to_string(),
            assigns: match with {
                Some(w) => parse_assigns(w)?,
                None => vec![],
            },
            refs: args,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn user_c8_parses() {
        let src = "theorem C8 {P : rel} : P ⇒ P in Logical {
   1. P ⇒ (P ∨ P)    by S2 with A := P; B := P
   2. (P ∨ P) ⇒ P    by S1 with A := P
   3. ((P ∨ P) ⇒ P) ⇒ ((P ⇒ (P ∨ P)) ⇒ (P ⇒ P))    by S4 with A := P ∨ P; B := P; C := ¬P
   4. (P ⇒ (P ∨ P)) ⇒ (P ⇒ P)    by mp 2 3
   5. P ⇒ P    by mp 1 4
}";
        let doc = parse_document(src).unwrap();
        let Item::Theorem(t) = &doc[0].item else {
            panic!()
        };
        assert_eq!(t.name, "C8");
        assert_eq!(t.theory.as_deref(), Some("Logical"));
        assert_eq!(t.statement, "P ⇒ P");
        assert_eq!(t.proof.len(), 5);
        assert_eq!(t.proof[3].label.as_deref(), Some("4"));
        assert_eq!(t.proof[3].just, Just::MP("2".into(), "3".into()));
        let Just::Use { name, assigns, .. } = &t.proof[2].just else {
            panic!()
        };
        assert_eq!(name, "S4");
        assert_eq!(assigns[2].value, "¬P");
    }

    #[test]
    fn labels_are_optional() {
        let (l, _) = parse_proof_line("A ⇒ A by C8").unwrap();
        assert_eq!(l.label, None);
        assert_eq!(l.formula.as_deref(), Some("A ⇒ A"));
        let (l, _) = parse_proof_line("h. A by axiom").unwrap();
        assert_eq!(l.label.as_deref(), Some("h"));
        let (l, opens) = parse_proof_line("_ by assume h {").unwrap();
        assert_eq!(l.formula, None);
        assert!(opens);
    }

    #[test]
    fn justifications() {
        assert_eq!(parse_just("sorry").unwrap(), Just::Sorry);
        assert_eq!(
            parse_just("mp 1 ^").unwrap(),
            Just::MP("1".into(), "^".into())
        );
        assert_eq!(
            parse_just("gen ^ with x").unwrap(),
            Just::Generalize {
                letter: "x".into(),
                from: "^".into()
            }
        );
        assert_eq!(
            parse_just("gen with x").unwrap(),
            Just::Generalize {
                letter: "x".into(),
                from: "^".into()
            }
        );
        assert_eq!(
            parse_just("contra g").unwrap(),
            Just::Contra(Some("g".into()))
        );
        let Just::Use {
            name,
            assigns,
            refs,
        } = parse_just("C6 1 ^ with A := x ∈ y").unwrap()
        else {
            panic!()
        };
        assert_eq!(name, "C6");
        assert_eq!(assigns.len(), 1);
        assert_eq!(refs, vec!["1", "^"]);
        let Just::Use { assigns, .. } = parse_just("S5 with R(x) := x ∈ y; T := z").unwrap()
        else {
            panic!()
        };
        assert_eq!(assigns[0].letters, vec!["x"]);
        assert_eq!(assigns[1].name, "T");
        assert!(parse_just("mp 1").is_err());
    }

    #[test]
    fn one_line_theorems_and_namespaces() {
        let src = "namespace ch1\ntheorem C11 {A : rel} : A ⇒ ¬¬A by C10 with A := ¬A\nend\nalias dn := ch1.C11\n#set prefix";
        let doc = parse_document(src).unwrap();
        assert_eq!(doc[0].item, Item::Namespace("ch1".into()));
        let Item::Theorem(t) = &doc[1].item else {
            panic!()
        };
        assert_eq!(t.proof.len(), 1);
        assert_eq!(doc[2].item, Item::End);
        assert_eq!(
            doc[3].item,
            Item::Alias {
                name: "dn".into(),
                target: "ch1.C11".into()
            }
        );
        assert_eq!(doc[4].item, Item::Set(Notation::Prefix));
    }

    #[test]
    fn blocks_nest() {
        let src = "theorem T {A : rel} : A ⇒ A {
  A ⇒ A by assume h {
     A by h
  }
}";
        let doc = parse_document(src).unwrap();
        let Item::Theorem(t) = &doc[0].item else {
            panic!()
        };
        assert_eq!(t.proof[0].block.len(), 1);
        assert_eq!(t.proof[0].just, Just::Assume(Some("h".into())));
    }
}
