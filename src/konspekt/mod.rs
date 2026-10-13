//! Конспект: тексты `.bk` с теориями и доказательствами в стиле Бурбаки и их проверка.
//!
//! ```
//! let mut k = bourbaki_engine::Konspekt::with_prelude();
//! let report = k.check_str(r#"
//! in Logical
//! theorem C8 {P : rel} : P ⇒ P {
//!   P ⇒ (P ∨ P)                                   by S2 with A := P; B := P
//!   (P ∨ P) ⇒ P                                   by S1 with A := P
//!   ((P ∨ P) ⇒ P) ⇒ ((P ⇒ (P ∨ P)) ⇒ (P ⇒ P))     by S4 with A := P ∨ P; B := P; C := ¬P
//!   (P ⇒ (P ∨ P)) ⇒ (P ⇒ P)                       by mp 2 3
//!   P ⇒ P                                         by mp 1 ^
//! }
//! "#);
//! assert!(report.is_ok(), "{report}");
//! // раскрыть до явных аксиом, схем и C1 и проверить независимо
//! let full = k.expand("C8").unwrap();
//! full.demonstration().verify().unwrap();
//! ```
//!
//! Устройство: [`ast`] (конспект как данные), [`parse`] (текст в данные),
//! [`check`] (проверка по строкам и раскрытие до атомов).
//!
//! # Имена
//!
//! `namespace A ... end` добавляет к объявленным именам приставку `A.`. Имя ищется так:
//! сначала в текущем пространстве и объемлющих (`A.B.x`, `A.x`, `x`), затем в открытых
//! через `open`. Если в открытых пространствах нашлось два разных `x`, это ошибка
//! (пишите полное имя). `alias x := A.B.y` даёт второе имя тому же объекту.
//! Знаки и сокращения (запись формул) общие для всех.

pub mod ast;
pub mod check;
pub mod model;
pub mod parse;

use crate::formative::Relation;
use crate::proof::Theorem;
use crate::sign::{Fixity, Kind, SpecialSign};
use crate::syntax::{self, Abbrev, Notation, Scope, Style};
use crate::theory::{PatternScheme, Th, Theory};
use ast::*;
use check::CheckedTheorem;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::path::{Path, PathBuf};
use std::rc::Rc;

/// Прелюдия: схемы S1-S7 и теории Logical, Quantified, Egalitarian.
pub const PRELUDE: &str = include_str!("../../konspekt/00_prelude.bk");

/// Слова, которые нельзя использовать как имена знаков для набора.
const RESERVED: &[&str] = &[
    "in", "by", "with", "or", "and", "not", "implies", "iff", "exists", "forall", "tau",
];

/// Ошибка проверки с местом в файле.
#[derive(Clone, Debug, PartialEq)]
pub struct CheckError {
    pub file: String,
    pub line: usize,
    pub msg: String,
}

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}", self.file, self.line, self.msg)
    }
}

impl std::error::Error for CheckError {}

/// Итог проверки файла.
#[derive(Clone, Debug, Default)]
pub struct Report {
    pub file: String,
    /// Проверенные теоремы (полное имя, формулировка).
    pub checked: Vec<(String, String)>,
    /// Теоремы, опирающиеся на `sorry`.
    pub sorry: Vec<String>,
    pub errors: Vec<CheckError>,
    /// Вывод по порядку: проверенные теоремы и команды `#show`, `#signs`, `#expand`, ...
    pub output: Vec<String>,
}

impl Report {
    pub fn is_ok(&self) -> bool {
        self.errors.is_empty()
    }
}

impl fmt::Display for Report {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for o in &self.output {
            writeln!(f, "{o}")?;
        }
        for e in &self.errors {
            writeln!(f, "ошибка: {e}")?;
        }
        write!(
            f,
            "{}: теорем {}, с sorry {}, ошибок {}",
            self.file,
            self.checked.len(),
            self.sorry.len(),
            self.errors.len()
        )
    }
}

/// Где искать имена: текущее пространство имён и открытые (`open`).
/// Теорема запоминает их, чтобы при раскрытии имена в доказательстве значили то же самое.
#[derive(Clone, Default, Debug)]
pub(crate) struct Names {
    pub ns: Vec<String>,
    pub opens: Vec<String>,
    /// Запись формул, в которой теорема написана.
    pub notation: Notation,
}

/// То, что действует до конца файла: пространства имён, `open`, `in`, `#set`.
#[derive(Clone, Default)]
struct FileState {
    ns: Vec<String>,
    ns_groups: Vec<usize>,
    opens: Vec<String>,
    current: Option<String>,
    notation: Notation,
    format_once: Option<Notation>,
}

/// Состояние конспекта: всё объявленное и доказанное (по полным именам).
pub struct Konspekt {
    pub scope: Scope,
    pub schemes: HashMap<String, Rc<PatternScheme>>,
    pub theories: HashMap<String, Th>,
    pub theorems: HashMap<String, Rc<CheckedTheorem>>,
    /// Модели (C5).
    pub models: HashMap<String, Rc<model::Model>>,
    /// Имена явных аксиом.
    pub axiom_names: HashMap<String, Relation>,
    /// Второе имя -> полное имя.
    pub aliases: HashMap<String, String>,
    /// Теория по умолчанию (`in Теория`), полное имя.
    pub current: Option<String>,
    ns: Vec<String>,
    ns_groups: Vec<usize>,
    opens: Vec<String>,
    /// `#format`: запись для следующей теоремы.
    format_once: Option<Notation>,
    /// Пространства имён, открытые в начале каждого файла (`with_prelude` открывает `base`).
    default_opens: Vec<String>,
    /// Прелюдия загружена из встроенного текста (`with_prelude`): её импорт пропускается.
    prelude_loaded: bool,
    /// Режим редактора: `#expand` и `#unfold` не выполняются (они бывают очень долгими).
    pub skip_expand: bool,
    loaded: HashSet<PathBuf>,
    file: String,
    dir: PathBuf,
}

impl Default for Konspekt {
    fn default() -> Self {
        Konspekt::new()
    }
}

impl Konspekt {
    /// Пустой конспект (без схем и теорий).
    pub fn new() -> Konspekt {
        // печать узнаёт только сокращения этого конспекта
        syntax::set_print_abbrevs(vec![]);
        Konspekt {
            scope: Scope::default(),
            schemes: HashMap::new(),
            theories: HashMap::new(),
            theorems: HashMap::new(),
            models: HashMap::new(),
            axiom_names: HashMap::new(),
            aliases: HashMap::new(),
            current: None,
            ns: vec![],
            ns_groups: vec![],
            opens: vec![],
            format_once: None,
            default_opens: vec![],
            prelude_loaded: false,
            skip_expand: false,
            loaded: HashSet::new(),
            file: "<текст>".into(),
            dir: PathBuf::from("."),
        }
    }

    /// Конспект с прелюдией (`konspekt/00_prelude.bk`: схемы S1-S7 и теории Logical,
    /// Quantified, Egalitarian в пространстве имён `base`). Для удобства `base` открыто
    /// в начале каждого проверяемого текста; файлы конспекта всё равно пишут
    /// `import "00_prelude.bk"` и `open base` сами, а этот импорт тогда пропускается.
    pub fn with_prelude() -> Konspekt {
        let mut k = Konspekt::new();
        let r = k.check_named(PRELUDE, "00_prelude.bk");
        assert!(r.is_ok(), "прелюдия не проверилась:\n{r}");
        k.prelude_loaded = true;
        k.default_opens = vec!["base".into()];
        k.opens = k.default_opens.clone();
        k
    }

    /// Начальное состояние файла: ничего не объявлено, открыто только `default_opens`.
    fn fresh_state(&self) -> FileState {
        FileState {
            opens: self.default_opens.clone(),
            ..Default::default()
        }
    }

    pub(crate) fn file_name(&self) -> String {
        self.file.clone()
    }

    pub(crate) fn name_taken(&self, n: &str) -> bool {
        self.scope.signs.iter().any(|s| s.name() == n)
            || self.scope.abbrevs.iter().any(|a| a.name == n)
            || self.scope.sign_aliases.iter().any(|(a, _)| a == n)
    }

    fn state(&self) -> FileState {
        FileState {
            ns: self.ns.clone(),
            ns_groups: self.ns_groups.clone(),
            opens: self.opens.clone(),
            current: self.current.clone(),
            notation: self.scope.notation,
            format_once: self.format_once,
        }
    }

    fn restore(&mut self, s: FileState) {
        self.ns = s.ns;
        self.ns_groups = s.ns_groups;
        self.opens = s.opens;
        self.current = s.current;
        self.format_once = s.format_once;
        self.set_notation(s.notation);
    }

    fn set_notation(&mut self, n: Notation) {
        self.scope.notation = n;
        syntax::set_style(match n {
            Notation::Infix => Style::Infix,
            Notation::Prefix => Style::Prefix,
        });
    }

    /// Полное имя для объявления в текущем пространстве имён.
    fn full(&self, name: &str) -> String {
        if self.ns.is_empty() {
            name.to_string()
        } else {
            format!("{}.{name}", self.ns.join("."))
        }
    }

    fn exists(&self, full: &str) -> bool {
        self.theorems.contains_key(full)
            || self.schemes.contains_key(full)
            || self.theories.contains_key(full)
            || self.axiom_names.contains_key(full)
            || self.models.contains_key(full)
            || self.aliases.contains_key(full)
    }

    pub(crate) fn names(&self) -> Names {
        Names {
            ns: self.ns.clone(),
            opens: self.opens.clone(),
            notation: self.scope.notation,
        }
    }

    fn resolve(&self, name: &str, has: &dyn Fn(&str) -> bool) -> Result<Option<String>, String> {
        self.resolve_in(&self.names(), name, has)
    }

    /// Найти полное имя по записанному: пространство имён и объемлющие, затем `open`.
    fn resolve_in(
        &self,
        names: &Names,
        name: &str,
        has: &dyn Fn(&str) -> bool,
    ) -> Result<Option<String>, String> {
        let follow = |n: String| self.aliases.get(&n).cloned().unwrap_or(n);
        let ns = &names.ns;
        for i in (0..=ns.len()).rev() {
            let cand = if i == 0 {
                name.to_string()
            } else {
                format!("{}.{name}", ns[..i].join("."))
            };
            let c = follow(cand);
            if has(&c) {
                return Ok(Some(c));
            }
        }
        let mut found: Vec<String> = Vec::new();
        for o in &names.opens {
            let c = follow(format!("{o}.{name}"));
            if has(&c) && !found.contains(&c) {
                found.push(c);
            }
        }
        match found.len() {
            0 => Ok(None),
            1 => Ok(found.pop()),
            _ => Err(format!(
                "имя {name} неоднозначно: {} (пишите полное имя)",
                found.join(" или ")
            )),
        }
    }

    pub(crate) fn find_theorem(&self, name: &str) -> Result<Option<Rc<CheckedTheorem>>, String> {
        self.find_theorem_in(&self.names(), name)
    }

    pub(crate) fn find_theorem_in(
        &self,
        names: &Names,
        name: &str,
    ) -> Result<Option<Rc<CheckedTheorem>>, String> {
        Ok(self
            .resolve_in(names, name, &|c| self.theorems.contains_key(c))?
            .map(|n| self.theorems[&n].clone()))
    }

    pub(crate) fn find_scheme(&self, name: &str) -> Result<Option<Rc<PatternScheme>>, String> {
        self.find_scheme_in(&self.names(), name)
    }

    pub(crate) fn find_scheme_in(
        &self,
        names: &Names,
        name: &str,
    ) -> Result<Option<Rc<PatternScheme>>, String> {
        Ok(self
            .resolve_in(names, name, &|c| self.schemes.contains_key(c))?
            .map(|n| self.schemes[&n].clone()))
    }

    pub(crate) fn find_theory(&self, name: &str) -> Result<Th, String> {
        self.find_theory_in(&self.names(), name)
    }

    pub(crate) fn find_theory_in(&self, names: &Names, name: &str) -> Result<Th, String> {
        self.resolve_in(names, name, &|c| self.theories.contains_key(c))?
            .map(|n| self.theories[&n].clone())
            .ok_or_else(|| format!("нет теории {name}"))
    }

    pub(crate) fn find_axiom_in(&self, names: &Names, name: &str) -> Result<Relation, String> {
        self.resolve_in(names, name, &|c| self.axiom_names.contains_key(c))?
            .map(|n| self.axiom_names[&n].clone())
            .ok_or_else(|| format!("нет аксиомы с именем {name}"))
    }

    /// Проверенная теорема (имя ищется как в тексте: с учётом `open` и алиасов).
    pub fn theorem(&self, name: &str) -> Option<Rc<CheckedTheorem>> {
        self.find_theorem(name).ok().flatten()
    }

    /// Раскрыть теорему до явных аксиом, схем и C1.
    pub fn expand(&self, name: &str) -> Result<Theorem, CheckError> {
        let t = self.theorem(name).ok_or_else(|| CheckError {
            file: self.file.clone(),
            line: 0,
            msg: format!("нет теоремы {name}"),
        })?;
        t.expand(self)
    }

    /// Проверить текст.
    pub fn check_str(&mut self, src: &str) -> Report {
        self.check_named(src, "<текст>")
    }

    /// Проверить файл (импорты ищутся относительно его папки).
    pub fn check_file(&mut self, path: &Path) -> Report {
        match std::fs::read_to_string(path) {
            // прелюдия уже загружена (with_prelude): второй раз её не проверяем
            Ok(src) if src == PRELUDE && self.prelude_loaded => Report {
                file: path.display().to_string(),
                output: vec!["прелюдия уже загружена".into()],
                ..Default::default()
            },
            Ok(src) => {
                let saved = std::mem::replace(
                    &mut self.dir,
                    path.parent().map(|p| p.to_path_buf()).unwrap_or_default(),
                );
                if let Ok(c) = path.canonicalize() {
                    self.loaded.insert(c);
                }
                let r = self.check_named(&src, &path.display().to_string());
                self.dir = saved;
                r
            }
            Err(e) => Report {
                file: path.display().to_string(),
                errors: vec![CheckError {
                    file: path.display().to_string(),
                    line: 0,
                    msg: format!("не прочитать файл: {e}"),
                }],
                ..Default::default()
            },
        }
    }

    /// Проверить текст так, как будто он лежит в файле `path` (импорты ищутся рядом).
    /// Нужно редактору: текст в окне ещё не сохранён.
    pub fn check_source(&mut self, src: &str, path: &Path) -> Report {
        let saved = std::mem::replace(
            &mut self.dir,
            path.parent().map(|p| p.to_path_buf()).unwrap_or_default(),
        );
        if let Ok(c) = path.canonicalize() {
            self.loaded.insert(c);
        }
        let r = self.check_named(src, &path.display().to_string());
        self.dir = saved;
        r
    }

    /// Что значит имя (для подсказок редактора): теорема, схема, теория, аксиома,
    /// модель, сокращение или знак.
    pub fn describe(&self, name: &str) -> Option<String> {
        // имя ищется так, как будто открыты все пространства имён
        let mut opens: Vec<String> = Vec::new();
        for k in self
            .theorems
            .keys()
            .chain(self.schemes.keys())
            .chain(self.theories.keys())
            .chain(self.axiom_names.keys())
            .chain(self.models.keys())
        {
            if let Some((ns, _)) = k.rsplit_once('.') {
                if !opens.iter().any(|o| o == ns) {
                    opens.push(ns.to_string());
                }
            }
        }
        let names = Names {
            ns: vec![],
            opens,
            notation: self.scope.notation,
        };
        syntax::set_print_abbrevs(self.scope.abbrevs.clone());
        if let Ok(Some(t)) = self.find_theorem_in(&names, name) {
            return Some(self.print_theorem(&t));
        }
        if let Ok(Some(sch)) = self.find_scheme_in(&names, name) {
            return Some(format!(
                "scheme {} : {}",
                crate::theory::Scheme::name(sch.as_ref()),
                sch.pattern()
            ));
        }
        if let Ok(th) = self.find_theory_in(&names, name) {
            let parent = th.name().to_string();
            return Some(format!(
                "theory {parent}: знаков {}, схем {}, явных аксиом {}",
                th.signs().len(),
                th.schemes().len(),
                th.axioms().len()
            ));
        }
        if let Ok(a) = self.find_axiom_in(&names, name) {
            return Some(format!("axiom {name} : {a}"));
        }
        if let Ok(Some(m)) = self
            .resolve_in(&names, name, &|c| self.models.contains_key(c))
            .map(|n| n.map(|n| self.models[&n].clone()))
        {
            return Some(format!(
                "model {} : {} -> {}",
                m.name,
                m.source.name(),
                m.target.name()
            ));
        }
        let base = name.split('_').next().unwrap_or(name);
        if let Some(a) = self
            .scope
            .abbrevs
            .iter()
            .rev()
            .find(|a| a.name == name || a.name == base || a.aliases.iter().any(|x| x == name))
        {
            let shown = syntax::show_expr(&a.body);
            return Some(format!(
                "abbrev {} (параметров {}, связывает букв {}) := {shown}",
                a.name,
                a.params.len(),
                a.binders.len()
            ));
        }
        if let Some(s) = self.scope.signs.iter().find(|s| s.name() == name) {
            let kind = if s.is_relational() { "rel" } else { "term" };
            return Some(format!("sign {} : {kind} {}", s.name(), s.weight()));
        }
        None
    }

    fn print_theorem(&self, t: &CheckedTheorem) -> String {
        let mut s = format!("theorem {}", t.name);
        for m in &t.metas {
            let kind = if m.is_relational() { "rel" } else { "term" };
            if m.weight() == 0 {
                s.push_str(&format!(" {{{} : {kind}}}", m.name()));
            } else {
                s.push_str(&format!(" {{{} : {kind} {}}}", m.name(), m.weight()));
            }
        }
        for (l, h) in &t.hyps {
            s.push_str(&format!(" ({l} : {h})"));
        }
        s.push_str(&format!(" : {} in {}", t.statement, t.base.name()));
        s
    }

    fn check_named(&mut self, src: &str, name: &str) -> Report {
        let saved_file = std::mem::replace(&mut self.file, name.to_string());
        let saved_state = self.state();
        self.restore(self.fresh_state());
        let mut report = Report {
            file: name.to_string(),
            ..Default::default()
        };
        match parse::parse_document(src) {
            Ok(items) => {
                for it in items {
                    if let Err(e) = self.item(&it, &mut report) {
                        report.errors.push(e);
                    }
                }
            }
            Err((line, msg)) => report.errors.push(CheckError {
                file: name.to_string(),
                line,
                msg,
            }),
        }
        self.file = saved_file;
        self.restore(saved_state);
        report
    }

    /// Проверить одну теорему, собранную как данные, и добавить её в конспект.
    pub fn check_theorem(&mut self, decl: &TheoremDecl) -> Result<(), CheckError> {
        self.add_theorem(decl).map(|_| ())
    }

    fn add_theorem(&mut self, decl: &TheoremDecl) -> Result<Rc<CheckedTheorem>, CheckError> {
        let full = self.full(&decl.name);
        if self.exists(&full) {
            return Err(self.error(decl.line, format!("имя {full} уже занято")));
        }
        let mut d = decl.clone();
        d.name = full.clone();
        // теория и пространство имён запоминаются, чтобы раскрытие понимало имена так же
        let theory = decl.theory.clone().or_else(|| self.current.clone()).ok_or_else(|| {
            self.error(decl.line, "не указано, в какой теории теорема: \"in Теория\" перед ней или в конце заголовка".into())
        })?;
        let th = self
            .find_theory(&theory)
            .map_err(|m| self.error(decl.line, m))?;
        d.theory = Some(th.name().to_string());
        let (t, _) = check::check_theorem(self, &d, false, None, &self.names())?;
        let t = Rc::new(t);
        self.theorems.insert(full, t.clone());
        Ok(t)
    }

    fn error(&self, line: usize, msg: String) -> CheckError {
        CheckError {
            file: self.file.clone(),
            line,
            msg,
        }
    }

    fn item(&mut self, it: &Located, report: &mut Report) -> Result<(), CheckError> {
        let line = it.line;
        let e = |k: &Konspekt, m: String| k.error(line, m);
        match &it.item {
            Item::Import(p) => {
                let path = self.dir.join(p);
                let canon = path
                    .canonicalize()
                    .map_err(|er| e(self, format!("не найти {}: {er}", path.display())))?;
                if self.loaded.contains(&canon) {
                    return Ok(());
                }
                let r = self.check_file(&path);
                report.errors.extend(r.errors);
                report.sorry.extend(r.sorry);
            }
            Item::Namespace(n) => {
                let parts: Vec<String> = n.split('.').map(|s| s.to_string()).collect();
                self.ns_groups.push(parts.len());
                self.ns.extend(parts);
            }
            Item::End => {
                let k = self
                    .ns_groups
                    .pop()
                    .ok_or_else(|| e(self, "end без namespace".into()))?;
                let len = self.ns.len() - k;
                self.ns.truncate(len);
            }
            Item::Open(n) => {
                if !self.opens.contains(n) {
                    self.opens.push(n.clone());
                }
            }
            Item::Alias { name, target } => {
                let full = self.full(name);
                if self.exists(&full) {
                    return Err(e(self, format!("имя {full} уже занято")));
                }
                let to = self
                    .resolve(target, &|c| {
                        self.theorems.contains_key(c)
                            || self.schemes.contains_key(c)
                            || self.theories.contains_key(c)
                            || self.axiom_names.contains_key(c)
                            || self.models.contains_key(c)
                    })
                    .map_err(|m| e(self, m))?
                    .ok_or_else(|| e(self, format!("нет ничего с именем {target}")))?;
                self.aliases.insert(full, to);
            }
            Item::Sign {
                name,
                aliases,
                kind,
                weight,
                infix,
            } => {
                if self.name_taken(name) {
                    return Err(e(self, format!("имя {name} уже занято")));
                }
                if let Some(r) = aliases.iter().find(|a| RESERVED.contains(&a.as_str())) {
                    return Err(e(
                        self,
                        format!("{r} зарезервировано, возьмите другое имя для набора"),
                    ));
                }
                if *infix && *weight != 2 {
                    return Err(e(self, "инфиксным может быть только знак веса 2".into()));
                }
                let mut s = match kind {
                    Kind::Relational => SpecialSign::relational(name, *weight),
                    Kind::Substantive => SpecialSign::substantive(name, *weight),
                };
                if *infix {
                    s = s.infix();
                }
                self.scope.signs.push(s);
                let k = self.scope.signs.len() - 1;
                for a in aliases {
                    self.scope.sign_aliases.push((a.clone(), k));
                }
            }
            Item::Abbrev {
                name,
                aliases,
                params,
                body,
                infix,
            } => {
                if self.name_taken(name) {
                    return Err(e(self, format!("имя {name} уже занято")));
                }
                if let Some(r) = aliases.iter().find(|a| RESERVED.contains(&a.as_str())) {
                    return Err(e(
                        self,
                        format!("{r} зарезервировано, возьмите другое имя для набора"),
                    ));
                }
                let ps = check::make_metas(self, params).map_err(|m| e(self, m))?;
                if *infix && (ps.len() != 2 || ps.iter().any(|p| p.weight() != 0)) {
                    return Err(e(
                        self,
                        "инфиксным может быть только сокращение с двумя параметрами веса 0".into(),
                    ));
                }
                let sc = self.scope.with_signs(&ps);
                let (expr, sort) = match sc.parse_rel(body) {
                    Ok(r) => (r.0, crate::expr::Sort::Relation),
                    Err(er1) => match sc.parse_term(body) {
                        Ok(t) => (t.0, crate::expr::Sort::Term),
                        Err(_) => return Err(e(self, format!("тело сокращения: {}", er1.0))),
                    },
                };
                let fixity = if *infix {
                    Fixity::Infix
                } else {
                    Fixity::Prefix
                };
                self.scope
                    .abbrevs
                    .push(Abbrev::new(name, ps, expr, sort, fixity, aliases.clone()));
                syntax::set_print_abbrevs(self.scope.abbrevs.clone());
            }
            Item::Scheme {
                name,
                metas,
                pattern,
            } => {
                let full = self.full(name);
                if self.exists(&full) {
                    return Err(e(self, format!("имя {full} уже занято")));
                }
                let ms = check::make_metas(self, metas).map_err(|m| e(self, m))?;
                let sc = self.scope.with_signs(&ms);
                let p = sc.parse_rel(pattern).map_err(|er| e(self, er.0))?;
                // внутреннее имя схемы короткое (S5, как в книге); полное имя только для поиска
                let s = PatternScheme::new(name, ms, p).map_err(|er| e(self, er.0))?;
                self.schemes.insert(full, Rc::new(s));
            }
            Item::Theory(d) => self.theory(d)?,
            Item::In(n) => {
                let th = self.find_theory(n).map_err(|m| e(self, m))?;
                self.current = Some(th.name().to_string());
            }
            Item::Set(n) => self.set_notation(*n),
            Item::Theorem(d) => {
                // #format действует только на эту теорему
                let saved = self.scope.notation;
                if let Some(n) = self.format_once.take() {
                    self.set_notation(n);
                }
                let t = self.add_theorem(d);
                let shown = t
                    .as_ref()
                    .map(|t| t.statement.to_string())
                    .unwrap_or_default();
                self.set_notation(saved);
                let t = t?;
                report.checked.push((t.name.clone(), shown.clone()));
                let mark = if t.sorry { "?" } else { "✓" };
                report.output.push(format!("{mark} {}: {shown}", t.name));
                if t.sorry {
                    report.sorry.push(t.name.clone());
                }
            }
            Item::Model(d) => {
                self.model(d)?;
                let m = &self.models[&self.full(&d.name)];
                let subst: Vec<String> =
                    m.subst.iter().map(|(x, t)| format!("{x} := {t}")).collect();
                report.output.push(format!(
                    "{} модель {}: {} -> {}{} (аксиом {})",
                    if m.sorry { "?" } else { "✓" },
                    m.name,
                    m.source.name(),
                    m.target.name(),
                    if subst.is_empty() {
                        String::new()
                    } else {
                        format!(" with {}", subst.join("; "))
                    },
                    m.obligations.len()
                ));
                if m.sorry {
                    report.sorry.push(m.name.clone());
                }
            }
            Item::Transfer {
                theorem,
                model,
                name,
            } => {
                let t = self.transfer(theorem, model, name, line)?;
                report
                    .checked
                    .push((t.name.clone(), t.statement.to_string()));
                let mark = if t.sorry { "?" } else { "✓" };
                report.output.push(format!(
                    "{mark} {}: {}    [C5: {theorem} via {model}]",
                    t.name, t.statement
                ));
                if t.sorry {
                    report.sorry.push(t.name.clone());
                }
            }
            Item::Format(n) => self.format_once = Some(*n),
            Item::Log => report.output.push(self.log(line)),
            Item::Formation(f) => {
                let ex = match self.scope.parse_rel(f) {
                    Ok(r) => r.0,
                    Err(er) => self.scope.parse_term(f).map_err(|_| e(self, er.0))?.0,
                };
                let lines =
                    crate::formative::formative_construction(&ex).map_err(|er| e(self, er.0))?;
                let mut s = format!("формативная конструкция {f} ({} строк):", lines.len());
                for (i, l) in lines.iter().enumerate() {
                    // читаемая запись и строка знаков (как в книге)
                    let readable = l
                        .assembly
                        .parse()
                        .map(|(x, _)| syntax::show_expr(&x))
                        .unwrap_or_default();
                    s.push_str(&format!("\n  {}. {readable}    знаки: {l}", i + 1));
                }
                report.output.push(s);
            }
            Item::Print(n) => {
                let t = self
                    .find_theorem(n)
                    .map_err(|m| e(self, m))?
                    .ok_or_else(|| e(self, format!("нет теоремы {n}")))?;
                report.output.push(self.print_theorem(&t));
            }
            Item::Show(f) => {
                let r = self
                    .scope
                    .parse_rel(f)
                    .or_else(|_| self.scope.parse_term(f).map(|t| Relation(t.0)));
                let r = r.map_err(|er| e(self, er.0))?;
                let saved = syntax::style();
                let mut s = format!("{r}");
                let other = if saved == Style::Prefix {
                    Style::Infix
                } else {
                    Style::Prefix
                };
                syntax::set_style(other);
                s = format!(
                    "{s}\n    {}: {r}",
                    if other == Style::Prefix {
                        "префиксно"
                    } else {
                        "инфиксно"
                    }
                );
                syntax::set_style(saved);
                report.output.push(s);
            }
            Item::Signs(f) => {
                let ex = match self.scope.parse_rel(f) {
                    Ok(r) => r.0,
                    Err(er) => self.scope.parse_term(f).map_err(|_| e(self, er.0))?.0,
                };
                let a = crate::assembly::Assembly::from_expr(&ex).map_err(|er| e(self, er.0))?;
                report.output.push(format!("{f}:\n{}", a.render()));
            }
            Item::Expand { name, .. } if self.skip_expand => {
                report
                    .output
                    .push(format!("#expand {name} пропущено (режим редактора)"));
            }
            Item::Expand { name, full } => {
                let t = self.expand(name).map_err(|er| e(self, er.msg))?;
                let d = t.demonstration();
                d.verify().map_err(|er| {
                    e(
                        self,
                        format!("раскрытие {name} не прошло проверку: {}", er.0),
                    )
                })?;
                let mut s = format!(
                    "{name} раскрыто до явных аксиом, схем и C1: {} строк, проверено",
                    d.len()
                );
                if *full {
                    if d.len() <= 2000 {
                        s = format!("{s}\n{d}");
                    } else {
                        s = format!("{s} (слишком длинно, чтобы выписать)");
                    }
                }
                report.output.push(s);
            }
        }
        Ok(())
    }

    /// Текст для `#log`.
    fn log(&self, line: usize) -> String {
        let or_dash = |s: String| if s.is_empty() { "-".to_string() } else { s };
        let mut thms: Vec<&String> = self.theorems.keys().collect();
        thms.sort();
        let here = self.ns.join(".");
        let local = self
            .theorems
            .keys()
            .filter(|n| here.is_empty() || n.starts_with(&format!("{here}.")))
            .count();
        format!(
            "#log {}:{line}\n  namespace: {}\n  open: {}\n  теория (in): {}\n  запись: {}{}\n  теорем всего: {}, в этом пространстве: {local}\n  знаки: {}\n  сокращения: {}",
            self.file,
            or_dash(here),
            or_dash(self.opens.join(", ")),
            self.current.clone().unwrap_or_else(|| "-".into()),
            match self.scope.notation {
                Notation::Infix => "infix",
                Notation::Prefix => "prefix",
            },
            match self.format_once {
                Some(Notation::Infix) => " (следующая теорема: infix)",
                Some(Notation::Prefix) => " (следующая теорема: prefix)",
                None => "",
            },
            thms.len(),
            or_dash(
                self.scope
                    .signs
                    .iter()
                    .map(|s| s.name().to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            or_dash(
                self.scope
                    .abbrevs
                    .iter()
                    .map(|a| a.name.clone())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        )
    }

    fn theory(&mut self, d: &TheoryDecl) -> Result<(), CheckError> {
        let e = |k: &Konspekt, m: String| k.error(d.line, m);
        let full = self.full(&d.name);
        if self.exists(&full) {
            return Err(e(self, format!("имя {full} уже занято")));
        }
        let mut schemes_in: Vec<(String, *const ())> = Vec::new();
        let (mut b, mut signs) = match &d.extends {
            Some(p) => {
                let parent = self.find_theory(p).map_err(|m| e(self, m))?;
                for s in parent.schemes() {
                    schemes_in.push((s.name().to_string(), Rc::as_ptr(s) as *const ()));
                }
                (parent.extend(&full), parent.signs().to_vec())
            }
            None => (Theory::build(&full), vec![]),
        };
        for n in &d.signs {
            let s = self
                .scope
                .signs
                .iter()
                .find(|s| s.name() == n)
                .or_else(|| {
                    self.scope
                        .sign_aliases
                        .iter()
                        .find(|(a, _)| a == n)
                        .map(|(_, k)| &self.scope.signs[*k])
                })
                .ok_or_else(|| e(self, format!("нет знака {n} (объявите: sign {n} : rel 2)")))?
                .clone();
            b = b.sign(&s);
            signs.push(s);
        }
        for n in &d.schemes {
            let s = self
                .find_scheme(n)
                .map_err(|m| e(self, m))?
                .ok_or_else(|| e(self, format!("нет схемы {n}")))?;
            for need in s.theory_signs() {
                if !signs.contains(&need) {
                    return Err(e(
                        self,
                        format!("схеме {n} нужен знак {need}, а в теории {} его нет", d.name),
                    ));
                }
            }
            // две разные схемы с одним коротким именем в одной теории не различить
            let short = crate::theory::Scheme::name(s.as_ref()).to_string();
            if let Some(old) = schemes_in.iter().find(|(n, _)| *n == short) {
                if old.1 != Rc::as_ptr(&s) as *const () {
                    return Err(e(
                        self,
                        format!("в теории {} уже есть другая схема с именем {short}", d.name),
                    ));
                }
            }
            schemes_in.push((short, Rc::as_ptr(&s) as *const ()));
            b = b.scheme(s);
        }
        for (name, f) in &d.axioms {
            let r = self.scope.parse_rel(f).map_err(|er| e(self, er.0))?;
            let an = self.full(name);
            if self.exists(&an) {
                return Err(e(self, format!("имя {an} уже занято")));
            }
            self.axiom_names.insert(an, r.clone());
            b = b.axiom(&r);
        }
        let th = b.done().map_err(|er| e(self, er.0))?;
        self.theories.insert(full, th);
        Ok(())
    }
}
