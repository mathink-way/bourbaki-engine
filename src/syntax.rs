//! Запись и чтение термов и соотношений.
//!
//! Сокращающие символы (⇒, ∧, ⇔, ∃, ∀ и любые свои) "не принадлежат формальной
//! математике" (§ 1, n° 1): это способ записи. Внутри всегда только □ τ ∨ ¬, буквы и
//! специальные знаки. Печать узнаёт сокращения по форме знакосочетания.
//!
//! # Префиксная и инфиксная запись
//!
//! Бурбаки пишут знакосочетания префиксно (`∨¬AB`, `∈xy`), а сокращения инфиксно.
//! Здесь можно и так и так, в одной строке вперемешку:
//!
//! | префиксно (как в книге) | инфиксно          |
//! |-------------------------|-------------------|
//! | `∨ ¬A B`                | `¬A ∨ B`, `A ⇒ B` |
//! | `∈ x y`                 | `x ∈ y`           |
//! | `m x y`                 | `m(x, y)`         |
//! | `τx ∈ x y`              | `τx(x ∈ y)`       |
//!
//! Печатать можно в трёх видах ([`Style`]): инфиксно с сокращениями, префиксно (только
//! примитивные знаки) и "знаками" (строка знакосочетания с □).
//!
//! # Ввод значков
//!
//! | значок | можно набрать                                  |
//! |--------|------------------------------------------------|
//! | `¬`    | `~`, `not`, `\neg`, `\lnot`, `\not`            |
//! | `∨`    | `or`, `\lor`, `\vee`, `\or`                    |
//! | `∧`    | `and`, `\land`, `\wedge`, `\and`               |
//! | `⇒`    | `=>`, `->`, `implies`, `\to`, `\imp`, `\implies`, `\Rightarrow` |
//! | `⇔`    | `<=>`, `<->`, `iff`, `\iff`, `\Leftrightarrow` |
//! | `∃`    | `exists`, `\exists`, `\ex`                      |
//! | `∀`    | `forall`, `\forall`, `\all`                     |
//! | `τ`    | `tau`, `\tau`                                   |
//!
//! ASCII-вариантов `\/`, `/\`, `&` нет: они путаются с a/b, a\b.
//!
//! Слова (`or`, `and`, ...) это один значок, а не буквы: `A or B` это A ∨ B.
//! Специальным знакам и сокращениям можно дать свои имена для набора, например `\in`.
//!
//! Подстановка: `(T|x) R`. Кванторы связывают сильно: `(∃x)(A ⇒ B)` требует скобок.

use crate::error::{Error, Result};
use crate::expr::{Expr, Shape, Sort};
use crate::formative::{Abs, Relation, Term};
use crate::sign::{Fixity, Kind, Letter, SpecialSign};
use crate::theory::Arg;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::fmt;

// ---------------------------------------------------------------------------
// Сокращения и область видимости имён
// ---------------------------------------------------------------------------

/// Сокращающий символ с параметрами, например `A ⊂ B := (∀z)(z ∈ A ⇒ z ∈ B)`.
/// Параметры хранятся как специальные знаки внутри тела; раскрытие это
/// подстановка вместо этих знаков.
///
/// Параметр веса k (`(R : rel 1)`) делает сокращение связывающим: в записи
/// `Coll_x(x ∈ a)` буква x связывается, и R получает тело x ∈ a с выделенной x
/// (как R{x} у Бурбаки). Связываемых букв столько, каков наибольший вес параметра;
/// параметр веса k выделяет первые k из них.
#[derive(Clone)]
pub struct Abbrev {
    pub name: String,
    pub params: Vec<SpecialSign>,
    pub body: Expr,
    pub sort: Sort,
    pub fixity: Fixity,
    pub aliases: Vec<String>,
    /// Буквы-подсказки для печати связываемых букв (их число = наибольший вес параметра).
    pub binders: Vec<Letter>,
    /// Сворачивать ли при печати (`abbrev ... nofold` не сворачивается: например,
    /// (∃x)(A ∧ R) слишком часто встречается, чтобы всякий раз печатать его как ExA).
    pub fold: bool,
}

impl Abbrev {
    /// Сокращение; подсказки для связываемых букв берутся из тела: в теле
    /// `(∃y)(∀x)(x ∈ y ⇔ R(x))` параметр R применён к букве x, она и будет подсказкой.
    pub fn new(
        name: &str,
        params: Vec<SpecialSign>,
        body: Expr,
        sort: Sort,
        fixity: Fixity,
        aliases: Vec<String>,
    ) -> Abbrev {
        // параметры переименовываются в знаки, которых нет нигде больше: иначе параметр A
        // совпал бы с метапеременной A теоремы, и печать не отличила бы одно от другого
        let fresh: Vec<SpecialSign> = params
            .iter()
            .map(|p| {
                let n = format!("{name}#{}", p.name());
                if p.is_relational() {
                    SpecialSign::relational(&n, p.weight())
                } else {
                    SpecialSign::substantive(&n, p.weight())
                }
            })
            .collect();
        let map: Vec<(SpecialSign, Expr)> = params
            .iter()
            .zip(&fresh)
            .map(|(p, f)| {
                (
                    p.clone(),
                    Expr::special(f.clone(), (0..p.weight() as u32).map(Expr::bx).collect()),
                )
            })
            .collect();
        let body = body.replace_signs(&map);
        let params = fresh;
        let n = params.iter().map(|p| p.weight()).max().unwrap_or(0);
        let mut binders: Vec<Letter> = Vec::new();
        if n > 0 {
            if let Some(p) = params.iter().find(|p| p.weight() == n) {
                binders = binder_hints(&body, p, &mut Vec::new()).unwrap_or_default();
            }
            if binders.len() != n {
                binders = ["x", "y", "z", "u", "v", "w"]
                    .iter()
                    .cycle()
                    .take(n)
                    .map(|l| Letter::new(l))
                    .collect();
            }
        }
        Abbrev {
            name: name.to_string(),
            params,
            body,
            sort,
            fixity,
            aliases,
            binders,
            fold: true,
        }
    }

    /// Связывающее ли сокращение (есть параметры веса больше 0).
    pub fn binds(&self) -> bool {
        !self.binders.is_empty()
    }

    /// Раскрыть: подставить аргументы вместо параметров (для параметра веса k аргумент
    /// это тело с k дырами).
    pub fn expand(&self, args: &[Expr]) -> Expr {
        let map: Vec<(SpecialSign, Expr)> = self
            .params
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        self.body.replace_signs(&map)
    }

    /// Раскрыть запись `имя_x(...)`: в аргументах для параметров веса k первые k
    /// связываемых букв становятся дырами.
    pub fn expand_bound(&self, letters: &[Letter], args: Vec<Expr>) -> Expr {
        let args: Vec<Expr> = args
            .into_iter()
            .zip(&self.params)
            .map(|(a, p)| a.abstract_letters(&letters[..p.weight()]))
            .collect();
        self.expand(&args)
    }

    fn param_sort(&self, i: usize) -> Sort {
        if self.params[i].is_relational() {
            Sort::Relation
        } else {
            Sort::Term
        }
    }
}

/// Найти вхождение p(□..) в теле и вернуть подсказки τ, связывающих его аргументы.
fn binder_hints(e: &Expr, p: &SpecialSign, stack: &mut Vec<Letter>) -> Option<Vec<Letter>> {
    match e.shape() {
        Shape::Letter(_) | Shape::Bx(_) => None,
        Shape::Not(a) => binder_hints(a, p, stack),
        Shape::Or(a, b) => binder_hints(a, p, stack).or_else(|| binder_hints(b, p, stack)),
        Shape::Tau(h, b) => {
            stack.push(h.clone());
            let r = binder_hints(b, p, stack);
            stack.pop();
            r
        }
        Shape::Special(s, args) => {
            if s == p {
                let hs: Option<Vec<Letter>> = args
                    .iter()
                    .map(|a| match a.shape() {
                        Shape::Bx(j) if (*j as usize) < stack.len() => {
                            Some(stack[stack.len() - 1 - *j as usize].clone())
                        }
                        _ => None,
                    })
                    .collect();
                if hs.is_some() {
                    return hs;
                }
            }
            args.iter().find_map(|a| binder_hints(a, p, stack))
        }
    }
}

/// Что известно разбору: специальные знаки (вместе с метапеременными), их имена для набора,
/// сокращения.
#[derive(Clone, Default)]
pub struct Scope {
    /// Как читать формулы: инфиксно или префиксно (`#set infix` / `#set prefix`).
    pub notation: Notation,
    pub signs: Vec<SpecialSign>,
    /// Дополнительные имена знаков: (имя, номер знака).
    pub sign_aliases: Vec<(String, usize)>,
    pub abbrevs: Vec<Abbrev>,
}

impl Scope {
    pub fn from_signs(signs: &[SpecialSign]) -> Scope {
        Scope {
            signs: signs.to_vec(),
            ..Default::default()
        }
    }

    pub fn with_signs(&self, more: &[SpecialSign]) -> Scope {
        let mut s = self.clone();
        for m in more {
            if !s.signs.contains(m) {
                s.signs.push(m.clone());
            }
        }
        s
    }

    pub fn parse_rel(&self, src: &str) -> Result<Relation> {
        let mut p = Parser::new(self, src)?;
        let r = p.rel()?;
        p.finish()?;
        Ok(r)
    }

    pub fn parse_term(&self, src: &str) -> Result<Term> {
        let mut p = Parser::new(self, src)?;
        let t = p.term()?;
        p.finish()?;
        Ok(t)
    }
}

/// Запись формул. Одна на файл (переключается `#set infix` / `#set prefix`), чтобы
/// запись читалась однозначно.
///
/// * `Infix`: бинарные связки и инфиксные знаки между операндами (`A ∨ B`, `x ∈ y`),
///   остальные знаки как вызов (`m(x, y)`, `R(x)`), `¬`, кванторы и `τ` впереди.
/// * `Prefix` (польская запись Бурбаки): всё впереди, скобки не нужны
///   (`∨ ¬ A B`, `∈ x y`, `m x y`, `∀x ⇒ R x S x`). Скобки можно ставить для группировки.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum Notation {
    #[default]
    Infix,
    Prefix,
}

// ---------------------------------------------------------------------------
// Печать
// ---------------------------------------------------------------------------

/// Вид печати.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Style {
    /// Инфиксно, с сокращениями ⇒ ∧ ⇔ ∃ ∀ и своими.
    Infix,
    /// Префиксно (польская запись), с сокращениями: `⇒ A B`, `∈ x y`, `∀x R`.
    Prefix,
    /// Строка знаков с □ (связи не рисуются; для рисунка есть `Assembly::render`).
    Signs,
}

thread_local! {
    static STYLE: Cell<Style> = const { Cell::new(Style::Infix) };
    static ABBREVS: RefCell<Vec<Abbrev>> = const { RefCell::new(Vec::new()) };
    /// Уже узнанные сокращения (сбрасывается при смене списка сокращений).
    static RECOGNIZED: RefCell<HashMap<(Expr, Sort), Option<Recognized>>> = RefCell::new(HashMap::new());
}

/// Выбрать вид печати (для текущего потока).
pub fn set_style(s: Style) {
    STYLE.with(|c| c.set(s));
}

pub fn style() -> Style {
    STYLE.with(|c| c.get())
}

/// Сокращения, которые печать будет узнавать (вместе с встроенными ⇒ ∧ ⇔ ∃ ∀).
pub fn set_print_abbrevs(a: Vec<Abbrev>) {
    ABBREVS.with(|c| *c.borrow_mut() = a);
    RECOGNIZED.with(|c| c.borrow_mut().clear());
}

#[derive(Clone, Copy, PartialEq)]
enum Cls {
    /// Не нуждается в скобках нигде.
    Atom,
    /// x ∈ y: без скобок внутри ∨, ⇒, но в скобках под ¬ и квантором.
    Infix,
    /// A ∨ B, A ⇒ B, ...
    Binary,
    /// (∃x)R.
    Quant,
}

fn paren(s: String) -> String {
    format!("({s})")
}

/// Печать соотношения.
pub fn show_rel(e: &Expr) -> String {
    match style() {
        Style::Infix => rel(e).0,
        Style::Prefix => pre_rel(e),
        Style::Signs => signs_or_prefix(e),
    }
}

/// Печать терма.
pub fn show_term(e: &Expr) -> String {
    match style() {
        Style::Infix => term(e).0,
        Style::Prefix => pre_term(e),
        Style::Signs => signs_or_prefix(e),
    }
}

/// Печать чего угодно (для отладки).
pub fn show_expr(e: &Expr) -> String {
    if !e.is_closed() {
        return format!("<тело с □: {}>", show_open(e));
    }
    match e.sort() {
        Some(Sort::Term) => show_term(e),
        Some(Sort::Relation) => show_rel(e),
        None => match crate::assembly::Assembly::from_expr(e) {
            Ok(a) => format!("<не терм и не соотношение: {a}>"),
            Err(_) => "<не терм и не соотношение>".into(),
        },
    }
}

fn signs_or_prefix(e: &Expr) -> String {
    match crate::assembly::Assembly::from_expr(e) {
        Ok(a) => a.to_string(),
        Err(_) => format!("<{} знаков> {}", e.len(), raw_prefix(e)),
    }
}

/// Польская запись только примитивами (без сокращений).
fn raw_prefix(e: &Expr) -> String {
    match e.shape() {
        Shape::Letter(l) => l.to_string(),
        Shape::Bx(_) => "□".into(),
        Shape::Not(a) => format!("¬ {}", raw_prefix(a)),
        Shape::Or(a, b) => format!("∨ {} {}", raw_prefix(a), raw_prefix(b)),
        Shape::Tau(h, b) => {
            let (x, inst) = open(h, b, e);
            format!("τ{x} {}", raw_prefix(&inst))
        }
        Shape::Special(s, args) => {
            let mut out = s.name().to_string();
            for a in args {
                out.push(' ');
                out.push_str(&raw_prefix(a));
            }
            out
        }
    }
}

fn pre_app(name: &str, args: &[(Expr, Sort)]) -> String {
    let mut out = name.to_string();
    for (a, sort) in args {
        out.push(' ');
        out.push_str(&match sort {
            Sort::Term => pre_term(a),
            Sort::Relation => pre_rel(a),
        });
    }
    out
}

/// Польская запись с сокращениями: `⇒ A B`, `∀x R`, `⊂ X Y`.
fn pre_rel(e: &Expr) -> String {
    if let Some((_, name, args)) = user_abbrev_args(e, Sort::Relation) {
        return pre_app(&name, &args);
    }
    if let Shape::Not(a) = e.shape() {
        if let Some((_, name, args)) = user_abbrev_args(a, Sort::Relation) {
            return format!("¬ {}", pre_app(&name, &args));
        }
    }
    let r = Relation(e.clone());
    match quant_reading(&r) {
        Some((true, h, body)) => {
            let (x, inst) = open(&h, &body, e);
            return format!("∀{x} {}", pre_rel(&inst));
        }
        Some((false, h, body)) => {
            let (x, inst) = open(&h, &body, e);
            return format!("∃{x} {}", pre_rel(&inst));
        }
        None => {}
    }
    if let Some((a, b)) = r.as_iff() {
        return format!("⇔ {} {}", pre_rel(a.expr()), pre_rel(b.expr()));
    }
    if let Some((a, b)) = and_reading(&r) {
        return format!("∧ {} {}", pre_rel(a.expr()), pre_rel(b.expr()));
    }
    if let Some((a, b)) = r.as_implies() {
        let left = a.not();
        // (A ∧ B) ∨ C читаем так, только если C не похоже на импликацию
        let and_or = and_reading(&left).is_some() && b.as_implies().is_none();
        if !and_or && (forall_reading(&left).is_none() || exists_reading(a.expr()).is_some()) {
            return format!("⇒ {} {}", pre_rel(a.expr()), pre_rel(b.expr()));
        }
    }
    match e.shape() {
        Shape::Not(a) => format!("¬ {}", pre_rel(a)),
        Shape::Or(a, b) => format!("∨ {} {}", pre_rel(a), pre_rel(b)),
        Shape::Special(s, args) => {
            let args: Vec<(Expr, Sort)> = args.iter().map(|a| (a.clone(), Sort::Term)).collect();
            pre_app(s.name(), &args)
        }
        _ => raw_prefix(e),
    }
}

fn pre_term(e: &Expr) -> String {
    if let Some((_, name, args)) = user_abbrev_args(e, Sort::Term) {
        return pre_app(&name, &args);
    }
    match e.shape() {
        Shape::Tau(h, b) => {
            let (x, inst) = open(h, b, e);
            format!("τ{x} {}", pre_rel(&inst))
        }
        Shape::Special(s, args) => {
            let args: Vec<(Expr, Sort)> = args.iter().map(|a| (a.clone(), Sort::Term)).collect();
            pre_app(s.name(), &args)
        }
        _ => raw_prefix(e),
    }
}

fn show_open(e: &Expr) -> String {
    let x = Letter::new("x").fresh(|l| e.contains_letter(l));
    show_expr(&e.instantiate(&Expr::letter(x)))
}

fn open(hint: &Letter, body: &Expr, whole: &Expr) -> (Letter, Expr) {
    let x = hint.fresh(|l| whole.contains_letter(l));
    let inst = body.instantiate(&Expr::letter(x.clone()));
    (x, inst)
}

fn quant(sym: &str, x: &Letter, body: &Expr) -> (String, Cls) {
    let (s, c) = rel(body);
    let s = if matches!(c, Cls::Atom | Cls::Quant) {
        s
    } else {
        paren(s)
    };
    (format!("({sym}{x}){s}"), Cls::Quant)
}

/// Попробовать узнать своё сокращение: имя для печати (с связываемыми буквами,
/// `Coll_x`) и аргументы (у параметров веса k дыры заполнены этими буквами).
/// Узнанное сокращение: само сокращение, имя для печати, аргументы с сортами.
type Recognized = (Abbrev, String, Vec<(Expr, Sort)>);

fn user_abbrev_args(e: &Expr, want: Sort) -> Option<Recognized> {
    let key = (e.clone(), want);
    if let Some(r) = RECOGNIZED.with(|c| c.borrow().get(&key).cloned()) {
        return r;
    }
    let r = user_abbrev_args_uncached(e, want);
    RECOGNIZED.with(|c| c.borrow_mut().insert(key, r.clone()));
    r
}

fn user_abbrev_args_uncached(e: &Expr, want: Sort) -> Option<Recognized> {
    ABBREVS.with(|c| {
        for a in c.borrow().iter().rev() {
            if a.sort != want || !a.fold {
                continue;
            }
            let mut got = Vec::new();
            if a.body.match_into(e, &a.params, &mut got) && got.len() == a.params.len() {
                // связываемые буквы: подсказки, свежие для всего знакосочетания
                let mut xs: Vec<Letter> = Vec::new();
                for h in &a.binders {
                    let x = h.fresh(|l| e.contains_letter(l) || xs.contains(l));
                    xs.push(x);
                }
                let fill: Vec<Expr> = xs.iter().map(|x| Expr::letter(x.clone())).collect();
                let args: Vec<(Expr, Sort)> = a
                    .params
                    .iter()
                    .enumerate()
                    .map(|(i, p)| {
                        let v = &got.iter().find(|(s, _)| s == p).unwrap().1;
                        (v.fill_holes(&fill[..p.weight()]), a.param_sort(i))
                    })
                    .collect();
                let name = match xs.len() {
                    0 => a.name.clone(),
                    1 => format!("{}_{}", a.name, xs[0]),
                    _ => format!(
                        "{}_{{{}}}",
                        a.name,
                        xs.iter()
                            .map(|x| x.to_string())
                            .collect::<Vec<_>>()
                            .join(",")
                    ),
                };
                return Some((a.clone(), name, args));
            }
        }
        None
    })
}

fn user_abbrev(e: &Expr, want: Sort) -> Option<(String, Cls)> {
    let (a, name, args) = user_abbrev_args(e, want)?;
    Some(show_app(&name, a.fixity, &args, a.sort))
}

/// Как прочитать соотношение в виде (∃x)R: из всех чтений берём то, у которого тело
/// короче (в (∃y)(∃x)R(x, y) есть и чтение (∃x)R(x, τy(...)), оно хуже).
fn exists_reading(e: &Expr) -> Option<(Letter, Expr)> {
    e.exists_readings().into_iter().min_by_key(|(_, b)| b.len())
}

/// Квантор впереди: (∀x)R (true) или (∃x)R (false), тело и подсказка. Если подходят оба
/// чтения (в (∃x)(∀y)R есть и чтение (∀y)R(τx(...), y)), берём то, что короче пишется.
fn quant_reading(r: &Relation) -> Option<(bool, Letter, Expr)> {
    let all = forall_reading(r).map(|a| (true, a.hint, a.body));
    let ex = exists_reading(r.expr()).map(|(h, b)| (false, h, b));
    match (all, ex) {
        (Some(a), Some(e)) => {
            // оба чтения: печатаем оба тела и берём более короткую запись
            // (так (∀x)(x ∉ ∅) не превращается в (∃X)(∀x)(x ∉ X))
            let shown = |(_, h, b): &(bool, Letter, Expr)| {
                let (_, inst) = open(h, b, r.expr());
                rel(&inst).0.chars().count()
            };
            Some(if shown(&e) < shown(&a) { e } else { a })
        }
        (a, e) => a.or(e),
    }
}

/// Читать ли ¬(∃x)¬R как (∀x)R. Не читаем, если тело имеет вид (не A) или (не B):
/// тогда исходное ¬(∃x)(A ∧ B) понятнее.
fn forall_reading(r: &Relation) -> Option<Abs> {
    let a = r.as_forall()?;
    let neg_and = matches!(Relation(a.body.clone()).as_or(), Some((p, q)) if p.as_not().is_some() && q.as_not().is_some());
    (!neg_and).then_some(a)
}

/// Читать ли ¬((¬A) ∨ (¬B)) как A ∧ B. Не читаем, если ¬A или ¬B выглядит как (∀x)R:
/// тогда это скорее отрицание дизъюнкции кванторов.
fn and_reading(r: &Relation) -> Option<(Relation, Relation)> {
    let (a, b) = r.as_and()?;
    (forall_reading(&a.not()).is_none() && forall_reading(&b.not()).is_none()).then_some((a, b))
}

fn rel(e: &Expr) -> (String, Cls) {
    if let Some(r) = user_abbrev(e, Sort::Relation) {
        return r;
    }
    // ¬ перед своим сокращением: ¬Coll_x(R), а не чтение кванторами
    if let Shape::Not(a) = e.shape() {
        if let Some((s, c)) = user_abbrev(a, Sort::Relation) {
            let s = if c == Cls::Atom { s } else { paren(s) };
            return (format!("¬{s}"), Cls::Atom);
        }
    }
    let r = Relation(e.clone());
    match quant_reading(&r) {
        Some((true, h, body)) => {
            let (x, inst) = open(&h, &body, e);
            return quant("∀", &x, &inst);
        }
        Some((false, h, body)) => {
            let (x, inst) = open(&h, &body, e);
            return quant("∃", &x, &inst);
        }
        None => {}
    }
    if let Some((a, b)) = r.as_iff() {
        return (bin(a.expr(), "⇔", b.expr()), Cls::Binary);
    }
    if let Some((a, b)) = and_reading(&r) {
        return (bin(a.expr(), "∧", b.expr()), Cls::Binary);
    }
    if let Some((a, b)) = r.as_implies() {
        // (A ∧ B) ∨ C и ((∀x)R) ∨ C литерально тоже имеют вид ∨¬XY; читать их как X ⇒ Y неудобно
        let left = a.not();
        // (A ∧ B) ∨ C читаем так, только если C не похоже на импликацию
        let and_or = and_reading(&left).is_some() && b.as_implies().is_none();
        if !and_or && (forall_reading(&left).is_none() || exists_reading(a.expr()).is_some()) {
            return (bin(a.expr(), "⇒", b.expr()), Cls::Binary);
        }
    }
    match e.shape() {
        Shape::Not(a) => {
            let (s, c) = rel(a);
            let s = if matches!(c, Cls::Atom | Cls::Quant) {
                s
            } else {
                paren(s)
            };
            (format!("¬{s}"), Cls::Atom)
        }
        Shape::Or(a, b) => (bin(a, "∨", b), Cls::Binary),
        Shape::Special(s, args) => {
            let args: Vec<(Expr, Sort)> = args.iter().map(|a| (a.clone(), Sort::Term)).collect();
            show_app(s.name(), s.fixity(), &args, Sort::Relation)
        }
        _ => (format!("<не соотношение: {}>", show_expr(e)), Cls::Atom),
    }
}

fn bin(a: &Expr, op: &str, b: &Expr) -> String {
    let w = |x: &Expr| {
        let (s, c) = rel(x);
        // квантор связывает сильно: (∀x)R ⇒ S читается однозначно
        if c == Cls::Binary { paren(s) } else { s }
    };
    format!("{} {op} {}", w(a), w(b))
}

fn show_app(name: &str, fixity: Fixity, args: &[(Expr, Sort)], result: Sort) -> (String, Cls) {
    let one = |(x, sort): &(Expr, Sort), as_operand: bool| -> String {
        let (s, c) = match sort {
            Sort::Term => term(x),
            Sort::Relation => rel(x),
        };
        if as_operand && c != Cls::Atom {
            paren(s)
        } else {
            s
        }
    };
    if fixity == Fixity::Infix && args.len() == 2 {
        let s = format!("{} {name} {}", one(&args[0], true), one(&args[1], true));
        // инфиксное сокращение над соотношениями ведёт себя как связка
        let cls = if args[0].1 == Sort::Relation && result == Sort::Relation {
            Cls::Binary
        } else {
            Cls::Infix
        };
        return (s, cls);
    }
    if args.is_empty() {
        return (name.to_string(), Cls::Atom);
    }
    let parts: Vec<String> = args.iter().map(|a| one(a, false)).collect();
    (format!("{name}({})", parts.join(", ")), Cls::Atom)
}

fn term(e: &Expr) -> (String, Cls) {
    if let Some(r) = user_abbrev(e, Sort::Term) {
        return r;
    }
    match e.shape() {
        Shape::Letter(l) => (l.to_string(), Cls::Atom),
        Shape::Tau(h, body) => {
            let (x, inst) = open(h, body, e);
            (format!("τ{x}({})", rel(&inst).0), Cls::Atom)
        }
        Shape::Special(s, args) => {
            let args: Vec<(Expr, Sort)> = args.iter().map(|a| (a.clone(), Sort::Term)).collect();
            show_app(s.name(), s.fixity(), &args, Sort::Term)
        }
        Shape::Bx(_) => ("□".into(), Cls::Atom),
        _ => (format!("<не терм: {}>", show_expr(e)), Cls::Atom),
    }
}

impl fmt::Display for Relation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&show_rel(&self.0))
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&show_term(&self.0))
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

impl fmt::Debug for Relation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

/// R{x} печатается как само R с буквой x.
impl fmt::Display for Abs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let x = self.hint.fresh(|l| self.body.contains_letter(l));
        write!(f, "{}{{{x}}}", self.apply(&Term::letter(&x)))
    }
}

impl fmt::Debug for Abs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

impl fmt::Display for Arg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Arg::Rel(r) => write!(f, "{r}"),
            Arg::Term(t) => write!(f, "{t}"),
            Arg::Abs(a) => write!(f, "{a}"),
            Arg::Body { holes: 0, body } => write!(f, "{}", show_expr(body)),
            Arg::Body { holes, body } => {
                let mut xs: Vec<Letter> = Vec::new();
                for _ in 0..*holes {
                    let x = Letter::new("x").fresh(|l| body.contains_letter(l) || xs.contains(l));
                    xs.push(x);
                }
                let args: Vec<Expr> = xs.iter().map(|l| Expr::letter(l.clone())).collect();
                write!(f, "{}", show_expr(&body.fill_holes(&args)))
            }
        }
    }
}

impl fmt::Debug for Arg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

// ---------------------------------------------------------------------------
// Разбор
// ---------------------------------------------------------------------------

#[derive(Clone, PartialEq, Debug)]
enum Tok {
    Not,
    Or,
    And,
    Imp,
    Iff,
    Exists,
    Forall,
    Tau,
    LP,
    RP,
    LB,
    RB,
    Comma,
    Bar,
    Dot,
    Sign(usize),
    Abbrev(usize),
    /// Связывающее сокращение с буквами: `Coll_x`, `S_{x,y}`.
    Binder(usize, Vec<Letter>),
    Letter(String),
    Eof,
}

const OPS: &[(&str, Tok)] = &[
    ("¬", Tok::Not),
    ("~", Tok::Not),
    ("⌉", Tok::Not),
    ("∨", Tok::Or),
    ("∧", Tok::And),
    ("⇒", Tok::Imp),
    ("=>", Tok::Imp),
    ("→", Tok::Imp),
    ("->", Tok::Imp),
    ("⇔", Tok::Iff),
    ("<=>", Tok::Iff),
    ("↔", Tok::Iff),
    ("<->", Tok::Iff),
    ("∃", Tok::Exists),
    ("∀", Tok::Forall),
    ("τ", Tok::Tau),
    ("(", Tok::LP),
    (")", Tok::RP),
    ("{", Tok::LB),
    ("}", Tok::RB),
    (",", Tok::Comma),
    ("|", Tok::Bar),
    (".", Tok::Dot),
];

const WORDS: &[(&str, Tok)] = &[
    ("not", Tok::Not),
    ("or", Tok::Or),
    ("and", Tok::And),
    ("implies", Tok::Imp),
    ("iff", Tok::Iff),
    ("exists", Tok::Exists),
    ("forall", Tok::Forall),
    ("tau", Tok::Tau),
];

const COMMANDS: &[(&str, Tok)] = &[
    ("neg", Tok::Not),
    ("lnot", Tok::Not),
    ("not", Tok::Not),
    ("lor", Tok::Or),
    ("vee", Tok::Or),
    ("or", Tok::Or),
    ("land", Tok::And),
    ("wedge", Tok::And),
    ("and", Tok::And),
    ("to", Tok::Imp),
    ("imp", Tok::Imp),
    ("implies", Tok::Imp),
    ("Rightarrow", Tok::Imp),
    ("iff", Tok::Iff),
    ("Leftrightarrow", Tok::Iff),
    ("exists", Tok::Exists),
    ("ex", Tok::Exists),
    ("forall", Tok::Forall),
    ("all", Tok::Forall),
    ("tau", Tok::Tau),
];

fn is_word_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// После `_` у связывающего сокращения: одна буква (`_x`) или список (`_{x,y}`).
/// Возвращает буквы и длину прочитанного (без `_`).
fn binder_letters(rest: &str, a: &Abbrev, src: &str) -> Result<(Vec<Letter>, usize)> {
    let (names, used): (Vec<&str>, usize) = if let Some(r) = rest.strip_prefix('{') {
        let end = r
            .find('}')
            .ok_or_else(|| Error(format!("не закрыта }} после {}_{{ в \"{src}\"", a.name)))?;
        (
            r[..end]
                .split(|c: char| c == ',' || c.is_whitespace())
                .filter(|x| !x.is_empty())
                .collect(),
            end + 2,
        )
    } else {
        let mut n = rest
            .char_indices()
            .find(|(_, c)| !(c.is_ascii_alphanumeric() || *c == '_'))
            .map(|(i, _)| i)
            .unwrap_or(rest.len());
        while rest[n..].starts_with('\'') {
            n += 1;
        }
        (vec![&rest[..n]], n)
    };
    let mut ls: Vec<Letter> = Vec::new();
    for n in names {
        if !Letter::is_valid(n) {
            return Err(Error(format!(
                "после {}_ должна стоять буква, а стоит \"{n}\" (в \"{src}\")",
                a.name
            )));
        }
        let l = Letter::new(n);
        if ls.contains(&l) {
            return Err(Error(format!("буква {n} связывается дважды в \"{src}\"")));
        }
        ls.push(l);
    }
    if ls.len() != a.binders.len() {
        return Err(Error(format!(
            "{} связывает {} букв, а написано {} (в \"{src}\")",
            a.name,
            a.binders.len(),
            ls.len()
        )));
    }
    Ok((ls, used))
}

fn lex(src: &str, scope: &Scope) -> Result<Vec<(Tok, usize)>> {
    // все имена знаков и сокращений (с их псевдонимами)
    let mut names: Vec<(String, Tok)> = Vec::new();
    for (k, s) in scope.signs.iter().enumerate() {
        names.push((s.name().to_string(), Tok::Sign(k)));
    }
    for (a, k) in &scope.sign_aliases {
        names.push((a.clone(), Tok::Sign(*k)));
    }
    for (k, a) in scope.abbrevs.iter().enumerate() {
        names.push((a.name.clone(), Tok::Abbrev(k)));
        for al in &a.aliases {
            names.push((al.clone(), Tok::Abbrev(k)));
        }
    }
    let lookup_word = |w: &str| -> Option<Tok> {
        names
            .iter()
            .rev()
            .find(|(n, _)| n == w)
            .map(|(_, t)| t.clone())
            .or_else(|| WORDS.iter().find(|(n, _)| *n == w).map(|(_, t)| t.clone()))
    };
    let mut out = Vec::new();
    let mut i = 0;
    while i < src.len() {
        let rest = &src[i..];
        let c = rest.chars().next().unwrap();
        if c.is_whitespace() {
            i += c.len_utf8();
            continue;
        }
        // \команда
        if c == '\\' {
            let w: String = rest[1..]
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric())
                .collect();
            if !w.is_empty() {
                let tok = lookup_word(&format!("\\{w}")).or_else(|| {
                    COMMANDS
                        .iter()
                        .find(|(n, _)| *n == w)
                        .map(|(_, t)| t.clone())
                });
                if let Some(t) = tok {
                    out.push((t, i));
                    i += 1 + w.len();
                    continue;
                }
                return Err(Error(format!("неизвестная команда \\{w} в \"{src}\"")));
            }
        }
        // самый длинный символ: встроенный или имя знака/сокращения не из букв
        let mut best: Option<(usize, Tok)> = None;
        for (s, t) in OPS {
            if rest.starts_with(s) && best.as_ref().is_none_or(|(l, _)| s.len() > *l) {
                best = Some((s.len(), t.clone()));
            }
        }
        for (n, t) in &names {
            if !n.chars().all(is_word_char)
                && rest.starts_with(n.as_str())
                && best.as_ref().is_none_or(|(l, _)| n.len() > *l)
            {
                best = Some((n.len(), t.clone()));
            }
        }
        if let Some((l, t)) = best {
            // связывающее сокращение с именем не из букв: ℰ_x, ∁_{x}
            if let Tok::Abbrev(k) = t {
                let a = &scope.abbrevs[k];
                if a.binds() {
                    let after = &src[i + l..];
                    let Some(r) = after.strip_prefix('_') else {
                        return Err(Error(format!(
                            "{} связывает букву: пишите {}_x(...) (в \"{src}\")",
                            a.name, a.name
                        )));
                    };
                    let (ls, used) = binder_letters(r, a, src)?;
                    out.push((Tok::Binder(k, ls), i));
                    i += l + 1 + used;
                    continue;
                }
            }
            out.push((t, i));
            i += l;
            continue;
        }
        if c.is_alphabetic() {
            let start = i;
            while i < src.len() && src[i..].chars().next().is_some_and(is_word_char) {
                i += src[i..].chars().next().unwrap().len_utf8();
            }
            while i < src.len() && src.as_bytes()[i] == b'\'' {
                i += 1;
            }
            let w = &src[start..i];
            // Coll_x, S_{x,y}: связывающее сокращение и буквы
            let binder = w
                .char_indices()
                .filter(|(_, c)| *c == '_')
                .find_map(|(j, _)| match lookup_word(&w[..j]) {
                    Some(Tok::Abbrev(k)) if scope.abbrevs[k].binds() => Some((k, j)),
                    _ => None,
                });
            if let Some(t) = lookup_word(w) {
                if let Tok::Abbrev(k) = t {
                    if scope.abbrevs[k].binds() {
                        let a = &scope.abbrevs[k];
                        if src[i..].starts_with("_{") {
                            let (ls, used) = binder_letters(&src[i + 1..], a, src)?;
                            out.push((Tok::Binder(k, ls), start));
                            i += 1 + used;
                            continue;
                        }
                        return Err(Error(format!(
                            "{} связывает букву: пишите {}_x(...) (в \"{src}\")",
                            a.name, a.name
                        )));
                    }
                }
                out.push((t, start));
            } else if let Some((k, j)) = binder {
                let a = &scope.abbrevs[k];
                let (ls, used) = binder_letters(&src[start + j + 1..], a, src)?;
                out.push((Tok::Binder(k, ls), start));
                i = start + j + 1 + used;
            } else if Letter::is_valid(w) {
                out.push((Tok::Letter(w.to_string()), start));
            } else {
                return Err(Error(format!("неизвестное слово \"{w}\" в \"{src}\"")));
            }
            continue;
        }
        return Err(Error(format!(
            "непонятный символ \"{c}\" на позиции {i} в \"{src}\""
        )));
    }
    out.push((Tok::Eof, src.len()));
    Ok(out)
}

/// Что за "оператор" стоит в записи: специальный знак или сокращение.
#[derive(Clone)]
enum Op {
    Sign(SpecialSign),
    Abbrev(Abbrev),
    /// Связывающее сокращение с буквами.
    Bound(Abbrev, Vec<Letter>),
}

impl Op {
    fn name(&self) -> &str {
        match self {
            Op::Sign(s) => s.name(),
            Op::Abbrev(a) | Op::Bound(a, _) => &a.name,
        }
    }
    fn arity(&self) -> usize {
        match self {
            Op::Sign(s) => s.weight(),
            Op::Abbrev(a) | Op::Bound(a, _) => a.params.len(),
        }
    }
    fn result(&self) -> Sort {
        match self {
            Op::Sign(s) => {
                if s.kind() == Kind::Relational {
                    Sort::Relation
                } else {
                    Sort::Term
                }
            }
            Op::Abbrev(a) | Op::Bound(a, _) => a.sort,
        }
    }
    fn param(&self, i: usize) -> Sort {
        match self {
            Op::Sign(_) => Sort::Term,
            Op::Abbrev(a) | Op::Bound(a, _) => a.param_sort(i),
        }
    }
    fn fixity(&self) -> Fixity {
        match self {
            Op::Sign(s) => s.fixity(),
            Op::Abbrev(a) | Op::Bound(a, _) => a.fixity,
        }
    }
    fn build(&self, args: Vec<Expr>) -> Result<Expr> {
        match self {
            Op::Sign(s) => {
                let terms: Vec<Term> = args.into_iter().map(Term).collect();
                Ok(match s.kind() {
                    Kind::Relational => Relation::special(s, &terms)?.0,
                    Kind::Substantive => Term::special(s, &terms)?.0,
                })
            }
            Op::Abbrev(a) => Ok(a.expand(&args)),
            Op::Bound(a, ls) => Ok(a.expand_bound(ls, args)),
        }
    }
}

struct Parser<'a> {
    toks: Vec<(Tok, usize)>,
    pos: usize,
    scope: &'a Scope,
    src: &'a str,
}

impl<'a> Parser<'a> {
    fn new(scope: &'a Scope, src: &'a str) -> Result<Parser<'a>> {
        Ok(Parser {
            toks: lex(src, scope)?,
            pos: 0,
            scope,
            src,
        })
    }

    fn finish(&self) -> Result<()> {
        if *self.peek() != Tok::Eof {
            return self.err("конец записи");
        }
        Ok(())
    }

    fn peek(&self) -> &Tok {
        &self.toks[self.pos].0
    }

    fn bump(&mut self) -> Tok {
        let t = self.toks[self.pos].0.clone();
        if t != Tok::Eof {
            self.pos += 1;
        }
        t
    }

    fn eat(&mut self, t: Tok) -> bool {
        if *self.peek() == t {
            self.bump();
            true
        } else {
            false
        }
    }

    fn err<T>(&self, what: &str) -> Result<T> {
        let at = self.toks[self.pos].1;
        Err(Error(format!(
            "ожидалось {what} на позиции {at} в \"{}\"",
            self.src
        )))
    }

    fn expect(&mut self, t: Tok, what: &str) -> Result<()> {
        if self.eat(t) { Ok(()) } else { self.err(what) }
    }

    fn attempt<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        let save = self.pos;
        let r = f(self);
        if r.is_err() {
            self.pos = save;
        }
        r
    }

    fn op_at(&self) -> Option<Op> {
        match self.peek() {
            Tok::Sign(k) => Some(Op::Sign(self.scope.signs[*k].clone())),
            Tok::Abbrev(k) => Some(Op::Abbrev(self.scope.abbrevs[*k].clone())),
            Tok::Binder(k, ls) => Some(Op::Bound(self.scope.abbrevs[*k].clone(), ls.clone())),
            _ => None,
        }
    }

    fn letter(&mut self) -> Result<Letter> {
        if let Tok::Letter(name) = self.peek().clone() {
            self.bump();
            Ok(Letter::new(&name))
        } else {
            self.err("буква")
        }
    }

    fn prefix_mode(&self) -> bool {
        self.scope.notation == Notation::Prefix
    }

    fn infix_err<T>(&self, op: &str) -> Result<T> {
        Err(Error(format!(
            "в инфиксной записи {op} ставится между операндами (A {op} B); польская запись включается #set prefix (в \"{}\")",
            self.src
        )))
    }

    fn prefix_err<T>(&self, op: &str) -> Result<T> {
        Err(Error(format!(
            "в префиксной записи {op} ставится перед операндами ({op} A B); инфиксная запись включается #set infix (в \"{}\")",
            self.src
        )))
    }

    fn rel(&mut self) -> Result<Relation> {
        if self.prefix_mode() {
            let r = self.unary()?;
            match self.peek() {
                Tok::Or => return self.prefix_err("∨"),
                Tok::And => return self.prefix_err("∧"),
                Tok::Imp => return self.prefix_err("⇒"),
                Tok::Iff => return self.prefix_err("⇔"),
                _ => {}
            }
            if let Some(op) = self.op_at() {
                if op.fixity() == Fixity::Infix {
                    return self.prefix_err(op.name());
                }
            }
            return Ok(r);
        }
        let a = self.imp()?;
        if self.eat(Tok::Iff) {
            let b = self.rel()?;
            return Ok(a.iff(&b));
        }
        Ok(a)
    }

    fn imp(&mut self) -> Result<Relation> {
        let a = self.or()?;
        if self.eat(Tok::Imp) {
            let b = self.imp()?;
            return Ok(a.implies(&b));
        }
        Ok(a)
    }

    /// Инфиксное сокращение над соотношениями (например A ⊻ B) на уровне ∨.
    fn rel_infix_op(&self) -> Option<Op> {
        let op = self.op_at()?;
        (op.fixity() == Fixity::Infix
            && op.arity() == 2
            && op.param(0) == Sort::Relation
            && op.result() == Sort::Relation)
            .then_some(op)
    }

    fn or(&mut self) -> Result<Relation> {
        let mut a = self.and()?;
        loop {
            if self.eat(Tok::Or) {
                let b = self.and()?;
                a = a.or(&b);
            } else if let Some(op) = self.rel_infix_op() {
                self.bump();
                let b = self.and()?;
                a = Relation(op.build(vec![a.0, b.0])?);
            } else {
                return Ok(a);
            }
        }
    }

    fn and(&mut self) -> Result<Relation> {
        let mut a = self.unary()?;
        while self.eat(Tok::And) {
            let b = self.unary()?;
            a = a.and(&b);
        }
        Ok(a)
    }

    fn quantifier(&mut self, q: Tok, x: Letter) -> Result<Relation> {
        let body = self.unary()?;
        Ok(if q == Tok::Exists {
            body.exists(&x)
        } else {
            body.forall(&x)
        })
    }

    fn unary(&mut self) -> Result<Relation> {
        match self.peek().clone() {
            Tok::Not => {
                self.bump();
                Ok(self.unary()?.not())
            }
            // префиксная запись связок: ∨ A B, ⇒ A B, ...
            t @ (Tok::Or | Tok::And | Tok::Imp | Tok::Iff) => {
                if !self.prefix_mode() {
                    let sym = match t {
                        Tok::Or => "∨",
                        Tok::And => "∧",
                        Tok::Imp => "⇒",
                        _ => "⇔",
                    };
                    return self.infix_err(sym);
                }
                self.bump();
                let a = self.unary()?;
                let b = self.unary()?;
                Ok(match t {
                    Tok::Or => a.or(&b),
                    Tok::And => a.and(&b),
                    Tok::Imp => a.implies(&b),
                    _ => a.iff(&b),
                })
            }
            q @ (Tok::Exists | Tok::Forall) => {
                self.bump();
                let x = self.letter()?;
                let _ = self.eat(Tok::Dot) || self.eat(Tok::Comma);
                self.quantifier(q, x)
            }
            _ => self.primary(),
        }
    }

    /// Аргумент нужного сорта в префиксной (польской) записи.
    fn tight(&mut self, sort: Sort) -> Result<Expr> {
        Ok(match sort {
            Sort::Relation => self.unary()?.0,
            Sort::Term => self.term_primary()?.0,
        })
    }

    /// Аргумент в записи s(a, b): полная запись нужного сорта.
    fn loose(&mut self, sort: Sort) -> Result<Expr> {
        Ok(match sort {
            Sort::Relation => self.rel()?.0,
            Sort::Term => self.term()?.0,
        })
    }

    /// Применение знака/сокращения: в инфиксной записи `s(a, b)`, в префиксной `s a b`.
    fn apply_prefix(&mut self, op: &Op) -> Result<Expr> {
        let n = op.arity();
        if n == 0 {
            return op.build(vec![]);
        }
        if !self.prefix_mode() {
            let close = match self.peek() {
                Tok::LP => Tok::RP,
                Tok::LB => Tok::RB,
                _ => {
                    let args: Vec<&str> = ["a", "b", "c", "d"].into_iter().take(n).collect();
                    return Err(Error(format!(
                        "в инфиксной записи знак {} пишется как {}({}) (в \"{}\")",
                        op.name(),
                        op.name(),
                        args.join(", "),
                        self.src
                    )));
                }
            };
            self.bump();
            let mut args = Vec::new();
            for i in 0..n {
                if i > 0 {
                    self.expect(Tok::Comma, ",")?;
                }
                args.push(self.loose(op.param(i))?);
            }
            self.expect(close, "закрывающая скобка")?;
            return op.build(args);
        }
        let mut args = Vec::new();
        for i in 0..n {
            args.push(self.tight(op.param(i))?);
        }
        op.build(args)
    }

    fn primary(&mut self) -> Result<Relation> {
        if *self.peek() == Tok::LP {
            // (∃x) R
            if let Ok((q, x)) = self.attempt(|p| {
                p.bump();
                let q = p.bump();
                if q != Tok::Exists && q != Tok::Forall {
                    return p.err("квантор");
                }
                let x = p.letter()?;
                p.expect(Tok::RP, ")")?;
                Ok((q, x))
            }) {
                return self.quantifier(q, x);
            }
            // (T|x) R
            if let Ok(r) = self.attempt(|p| {
                p.bump();
                let t = p.term()?;
                p.expect(Tok::Bar, "|")?;
                let x = p.letter()?;
                p.expect(Tok::RP, ")")?;
                let r = p.unary()?;
                Ok(r.subst(&x, &t))
            }) {
                return Ok(r);
            }
            // (R)
            if let Ok(r) = self.attempt(|p| {
                p.bump();
                let r = p.rel()?;
                p.expect(Tok::RP, ")")?;
                Ok(r)
            }) {
                return Ok(r);
            }
        }
        // знак или сокращение, дающие соотношение, в начале: префиксная запись
        if let Some(op) = self.op_at() {
            if op.result() == Sort::Relation {
                if !self.prefix_mode() && op.fixity() == Fixity::Infix {
                    return self.infix_err(op.name());
                }
                self.bump();
                return Ok(Relation(self.apply_prefix(&op)?));
            }
        }
        // T s U с инфиксным знаком (или сокращением) от термов
        let t = self.term()?;
        if let Some(op) = self.op_at() {
            if self.prefix_mode() {
                return self.prefix_err(op.name());
            }
            if op.fixity() == Fixity::Infix
                && op.arity() == 2
                && op.result() == Sort::Relation
                && op.param(0) == Sort::Term
            {
                self.bump();
                let u = self.term()?;
                return Ok(Relation(op.build(vec![t.0, u.0])?));
            }
            return Err(Error(format!(
                "после терма {t} стоит {}, а ожидался инфиксный знак, дающий соотношение (в \"{}\")",
                op.name(),
                self.src
            )));
        }
        self.err("соотношение")
    }

    fn term(&mut self) -> Result<Term> {
        let mut t = self.term_primary()?;
        if self.prefix_mode() {
            return Ok(t);
        }
        while let Some(op) = self.op_at() {
            if op.fixity() == Fixity::Infix
                && op.arity() == 2
                && op.result() == Sort::Term
                && op.param(0) == Sort::Term
            {
                self.bump();
                let u = self.term_primary()?;
                t = Term(op.build(vec![t.0, u.0])?);
            } else {
                break;
            }
        }
        Ok(t)
    }

    fn term_primary(&mut self) -> Result<Term> {
        match self.peek().clone() {
            Tok::Letter(_) => Ok(Term::letter(&self.letter()?)),
            Tok::Tau => {
                self.bump();
                let x = self.letter()?;
                let _ = self.eat(Tok::Dot);
                let r = self.unary()?;
                Ok(Term::tau(&x, &r))
            }
            Tok::Sign(_) | Tok::Abbrev(_) | Tok::Binder(..) => {
                let op = self.op_at().unwrap();
                if op.result() != Sort::Term {
                    return self.err("терм");
                }
                if !self.prefix_mode() && op.fixity() == Fixity::Infix {
                    return self.infix_err(op.name());
                }
                self.bump();
                Ok(Term(self.apply_prefix(&op)?))
            }
            Tok::LP => {
                if let Ok(t) = self.attempt(|p| {
                    p.bump();
                    let t = p.term()?;
                    p.expect(Tok::Bar, "|")?;
                    let x = p.letter()?;
                    p.expect(Tok::RP, ")")?;
                    let u = p.term_primary()?;
                    Ok(u.subst(&x, &t))
                }) {
                    return Ok(t);
                }
                self.bump();
                let t = self.term()?;
                self.expect(Tok::RP, ")")?;
                Ok(t)
            }
            _ => self.err("терм"),
        }
    }
}

/// Разобрать соотношение (знаки берутся из списка `signs`).
pub fn parse_relation(signs: &[SpecialSign], src: &str) -> Result<Relation> {
    Scope::from_signs(signs).parse_rel(src)
}

/// Разобрать терм.
pub fn parse_term(signs: &[SpecialSign], src: &str) -> Result<Term> {
    Scope::from_signs(signs).parse_term(src)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scope() -> Scope {
        let mut s = Scope::from_signs(&[
            SpecialSign::relational("∈", 2).infix(),
            SpecialSign::substantive("m", 2),
            SpecialSign::relational("R", 1),
        ]);
        s.sign_aliases.push(("\\in".into(), 0));
        s
    }

    fn prefix_scope() -> Scope {
        Scope {
            notation: Notation::Prefix,
            ..scope()
        }
    }

    #[test]
    fn roundtrip_infix() {
        let s = scope();
        for src in [
            "x ∈ y ⇒ y ∈ x",
            "(∃x)(x ∈ y)",
            "(∀x)(∃y)(x ∈ y ∧ y ∈ x)",
            "τx(x ∈ y) ∈ y",
            "m(x, y) ∈ m(y, x)",
            "¬(x ∈ y) ∨ (x ∈ y ⇔ y ∈ x)",
            "R(m(x, y)) ⇒ R(x)",
        ] {
            let r = s.parse_rel(src).unwrap();
            assert_eq!(s.parse_rel(&r.to_string()).unwrap(), r, "{src} -> {r}");
        }
    }

    #[test]
    fn roundtrip_prefix() {
        let s = prefix_scope();
        set_style(Style::Prefix);
        for src in [
            "∨ ∈ x y ¬ ∈ y x",
            "∀x ∃y ∧ ∈ x y ∈ y x",
            "∈ τx ∈ x y y",
            "⇒ R m x y R x",
            "⇔ ∈ x y ¬ ¬ ∈ x y",
        ] {
            let r = s.parse_rel(src).unwrap();
            assert_eq!(s.parse_rel(&r.to_string()).unwrap(), r, "{src} -> {r}");
        }
        set_style(Style::Infix);
    }

    #[test]
    fn prefix_means_the_same_assembly() {
        let (i, p) = (scope(), prefix_scope());
        for (a, b) in [
            ("m(x, y) ∈ x", "∈ m x y x"),
            ("x ∈ y ∨ ¬(y ∈ x)", "∨ ∈ x y ¬ ∈ y x"),
            ("τx(x ∈ y) ∈ y", "∈ τx ∈ x y y"),
            ("x ∈ y ∨ (y ∈ x ∨ x ∈ x)", "or ∈ x y or ∈ y x ∈ x x"),
            ("R(x)", "R x"),
            ("R(x)", "R(x)"),
        ] {
            assert_eq!(
                i.parse_rel(a).unwrap(),
                p.parse_rel(b).unwrap(),
                "{a} / {b}"
            );
        }
    }

    #[test]
    fn one_notation_at_a_time() {
        let (i, p) = (scope(), prefix_scope());
        // в инфиксной записи префиксная форма бинарных знаков запрещена
        for bad in [
            "∨ ∈ x y ∈ y x",
            "∈ x y",
            "m x y ∈ x",
            r"\lor (∈ x y) (∈ x y)",
        ] {
            let e = i.parse_rel(bad).unwrap_err();
            assert!(e.0.contains("инфиксной"), "{bad}: {e}");
        }
        // и наоборот
        for bad in ["x ∈ y", "∈ x y ∨ ∈ y x", "∈ m(x, y) x"] {
            assert!(p.parse_rel(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn words_and_commands() {
        let s = scope();
        let a = s.parse_rel(r"x \in y \to not y \in x").unwrap();
        let b = s.parse_rel("x ∈ y ⇒ ¬(y ∈ x)").unwrap();
        assert_eq!(a, b);
        assert_eq!(
            s.parse_rel("x ∈ y or y ∈ x").unwrap(),
            s.parse_rel(r"x ∈ y \lor y ∈ x").unwrap()
        );
        assert!(s.parse_rel(r"x \nonsense y").is_err());
    }

    #[test]
    fn substitution_notation() {
        let s = scope();
        assert_eq!(
            s.parse_rel("(m(a, b)|x) x ∈ y").unwrap(),
            s.parse_rel("m(a, b) ∈ y").unwrap()
        );
    }

    #[test]
    fn errors_are_readable() {
        let s = scope();
        let e = s.parse_rel("x ∈").unwrap_err();
        assert!(e.0.contains("ожидалось"), "{e}");
    }
}
