//! Проверка доказательств по строкам.
//!
//! Две скорости, один и тот же код:
//!
//! * **быстрая проверка** (по умолчанию): каждая строка проверяется на своём уровне.
//!   Схема: подставить параметры в образец и сравнить. Теорема: подставить в её
//!   формулировку (не в доказательство!) и сравнить. C14: проверить блок в 𝒯 + A.
//!   Время линейно по длине написанного.
//! * **раскрытие до атомов** (`expand = true`): то же, но каждая строка сопровождается
//!   настоящей теоремой ядра [`crate::proof::Theorem`], т.е. доказательством из явных
//!   аксиом, схем и C1. Применение теоремы подставляет в её раскрытое доказательство,
//!   C14 перестраивает доказательство как у Бурбаки. Это медленно и делается по запросу.

use super::ast::*;
use super::{CheckError, Konspekt};
use crate::expr::Expr;
use crate::formative::{Relation, Term};
use crate::logic;
use crate::proof::Theorem;
use crate::quant;
use crate::sign::{Kind, Letter, SpecialSign};
use crate::syntax::Scope;
use crate::theory::{Arg, Th};
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Проверенная теорема конспекта.
pub struct CheckedTheorem {
    pub name: String,
    /// Теория, в которой сформулирована теорема.
    pub base: Th,
    /// Метапеременные (специальные знаки этой теоремы).
    pub metas: Vec<SpecialSign>,
    /// Гипотезы (метка, соотношение).
    pub hyps: Vec<(String, Relation)>,
    pub statement: Relation,
    /// 𝒯 + метапеременные + гипотезы как явные аксиомы.
    pub lemma_th: Th,
    /// В доказательстве (или в использованных теоремах) есть `sorry`.
    pub sorry: bool,
    pub(super) decl: TheoremDecl,
    pub(super) names: super::Names,
    pub(super) expanded: RefCell<Option<Theorem>>,
    /// Откуда теорема: доказана по строкам или перенесена моделью (C5).
    pub(super) origin: Origin,
}

/// Происхождение теоремы конспекта.
pub(super) enum Origin {
    Proof,
    /// `transfer`: теорема `source` перенесена в другую теорию моделью `model`.
    Transfer {
        source: std::rc::Rc<CheckedTheorem>,
        model: std::rc::Rc<super::model::Model>,
    },
}

impl CheckedTheorem {
    /// Раскрыть доказательство до явных аксиом, схем и C1 (результат кэшируется).
    pub fn expand(&self, k: &Konspekt) -> Result<Theorem, CheckError> {
        if let Some(t) = self.expanded.borrow().as_ref() {
            return Ok(t.clone());
        }
        let thm = match &self.origin {
            Origin::Proof => {
                let (_, thm) = check_theorem(
                    k,
                    &self.decl,
                    true,
                    Some(self.lemma_th.clone()),
                    &self.names,
                )?;
                thm.expect("в режиме раскрытия теорема строится")
            }
            Origin::Transfer { source, model } => model.expand_transfer(k, source, self)?,
        };
        *self.expanded.borrow_mut() = Some(thm.clone());
        Ok(thm)
    }
}

#[derive(Clone)]
struct Fact {
    rel: Relation,
    thm: Option<Theorem>,
}

struct Ctx<'a> {
    k: &'a Konspekt,
    names: super::Names,
    th: Th,
    scope: Scope,
    frames: Vec<Vec<(String, Fact)>>,
    /// Сколько строк уже проверено в каждом открытом блоке (для автонумерации и `^`).
    done: Vec<usize>,
    expand: bool,
    sorry: bool,
    line: usize,
}

static FRESH: AtomicUsize = AtomicUsize::new(0);

fn fresh_like(m: &SpecialSign) -> SpecialSign {
    let n = FRESH.fetch_add(1, Ordering::Relaxed);
    let name = format!("{}#{n}", m.name());
    match m.kind() {
        Kind::Relational => SpecialSign::relational(&name, m.weight()),
        Kind::Substantive => SpecialSign::substantive(&name, m.weight()),
    }
}

/// Метапеременная как тело: A ↦ A, R ↦ R(□₀).
fn meta_body(m: &SpecialSign) -> Expr {
    Expr::special(m.clone(), (0..m.weight() as u32).map(Expr::bx).collect())
}

pub(super) fn make_metas(k: &Konspekt, decls: &[MetaDecl]) -> Result<Vec<SpecialSign>, String> {
    let mut out: Vec<SpecialSign> = Vec::new();
    for d in decls {
        for n in &d.names {
            if k.name_taken(n) {
                return Err(format!("имя {n} уже занято знаком или сокращением"));
            }
            if out.iter().any(|m| m.name() == n) {
                return Err(format!("метапеременная {n} объявлена дважды"));
            }
            if !Letter::is_valid(n) && n.chars().any(|c| c.is_whitespace()) {
                return Err(format!("плохое имя метапеременной {n}"));
            }
            out.push(match d.kind {
                Kind::Relational => SpecialSign::relational(n, d.weight),
                Kind::Substantive => SpecialSign::substantive(n, d.weight),
            });
        }
    }
    Ok(out)
}

/// Проверить теорему. В режиме `expand` вернуть и её раскрытие.
pub(super) fn check_theorem(
    k: &Konspekt,
    decl: &TheoremDecl,
    expand: bool,
    lemma_th: Option<Th>,
    names: &super::Names,
) -> Result<(CheckedTheorem, Option<Theorem>), CheckError> {
    let err = |line: usize, msg: String| CheckError {
        file: k.file_name(),
        line,
        msg,
    };
    let theory_name = decl
        .theory
        .clone()
        .or_else(|| k.current.clone())
        .ok_or_else(|| {
            err(
                decl.line,
                "не указано, в какой теории теорема: \"in Теория\" перед ней или в конце заголовка"
                    .into(),
            )
        })?;
    let base = k
        .find_theory_in(names, &theory_name)
        .map_err(|m| err(decl.line, m))?;
    let metas = make_metas(k, &decl.metas).map_err(|m| err(decl.line, m))?;
    let mut scope = k.scope.with_signs(&metas);
    scope.notation = names.notation;
    let parse = |s: &str| scope.parse_rel(s).map_err(|e| err(decl.line, e.0));
    let mut hyps = Vec::new();
    for (l, f) in &decl.hyps {
        hyps.push((l.clone(), parse(f)?));
    }
    let statement = parse(&decl.statement)?;
    let lemma_th = match lemma_th {
        Some(t) => t,
        None => {
            let mut b = base.extend(&decl.name);
            for m in &metas {
                b = b.sign(m);
            }
            for (_, h) in &hyps {
                b = b.axiom(h);
            }
            b.done().map_err(|e| err(decl.line, e.0))?
        }
    };
    lemma_th
        .check_signs(statement.expr())
        .map_err(|e| err(decl.line, e.0))?;
    let mut frame = Vec::new();
    for (l, h) in &hyps {
        let thm = if expand {
            Some(Theorem::axiom(&lemma_th, h).map_err(|e| err(decl.line, e.0))?)
        } else {
            None
        };
        frame.push((
            l.clone(),
            Fact {
                rel: h.clone(),
                thm,
            },
        ));
    }
    let mut ctx = Ctx {
        k,
        names: names.clone(),
        th: lemma_th.clone(),
        scope,
        frames: vec![frame],
        done: vec![],
        expand,
        sorry: false,
        line: decl.line,
    };
    // `_` в последней строке доказательства означает "утверждение теоремы"
    let mut proof = decl.proof.clone();
    if let Some(last) = proof.last_mut() {
        if last.formula.is_none() {
            last.formula = Some(decl.statement.clone());
        }
    }
    let facts = ctx.lines(&proof)?;
    let last = facts
        .last()
        .map(|(_, f)| f.clone())
        .ok_or_else(|| err(decl.line, "пустое доказательство".into()))?;
    if last.rel != statement {
        let at = decl.proof.last().map(|l| l.line).unwrap_or(decl.line);
        return Err(err(
            at,
            format!(
                "последняя строка {} не совпадает с утверждением теоремы {}",
                last.rel, statement
            ),
        ));
    }
    let checked = CheckedTheorem {
        name: decl.name.clone(),
        base,
        metas,
        hyps,
        statement,
        lemma_th,
        sorry: ctx.sorry,
        decl: decl.clone(),
        names: names.clone(),
        expanded: RefCell::new(None),
        origin: Origin::Proof,
    };
    Ok((checked, last.thm))
}

/// Проверить одну строку `rel by just` в теории `th` (для обязательств модели).
/// Возвращает её раскрытие (если `expand`) и признак `sorry`.
pub(super) fn check_fact(
    k: &Konspekt,
    th: &Th,
    names: &super::Names,
    rel: &Relation,
    just: &Just,
    line: usize,
    expand: bool,
) -> Result<(Option<Theorem>, bool), CheckError> {
    let mut scope = k.scope.clone();
    scope.notation = names.notation;
    let mut ctx = Ctx {
        k,
        names: names.clone(),
        th: th.clone(),
        scope,
        frames: vec![vec![]],
        done: vec![0],
        expand,
        sorry: false,
        line,
    };
    let l = Line {
        label: None,
        formula: None,
        just: just.clone(),
        block: vec![],
        line,
    };
    let f = ctx.line_given(&l, Some(rel.clone()))?;
    Ok((f.thm, ctx.sorry))
}

impl Ctx<'_> {
    fn err(&self, msg: impl Into<String>) -> CheckError {
        CheckError {
            file: self.k.file_name(),
            line: self.line,
            msg: msg.into(),
        }
    }

    fn lift<T>(&self, r: crate::error::Result<T>) -> Result<T, CheckError> {
        r.map_err(|e| self.err(e.0))
    }

    fn lookup(&self, label: &str) -> Option<Fact> {
        // ^, ^^, ...: предыдущая строка, две назад, ... (до начала блока: его гипотеза)
        if !label.is_empty() && label.chars().all(|c| c == '^') {
            let n = label.len();
            let done = *self.done.last()?;
            if n <= done {
                return self.lookup_in_block(&(done - n + 1).to_string());
            }
            if n == done + 1 && self.frames.len() >= 2 {
                return self.frames[self.frames.len() - 2]
                    .last()
                    .map(|(_, f)| f.clone());
            }
            return None;
        }
        for f in self.frames.iter().rev() {
            if let Some((_, fact)) = f.iter().rev().find(|(l, _)| l == label) {
                return Some(fact.clone());
            }
        }
        None
    }

    fn lookup_in_block(&self, label: &str) -> Option<Fact> {
        self.frames
            .last()?
            .iter()
            .find(|(l, _)| l == label)
            .map(|(_, f)| f.clone())
    }

    fn get(&self, label: &str) -> Result<Fact, CheckError> {
        self.lookup(label)
            .ok_or_else(|| self.err(format!("нет строки или гипотезы с меткой {label}")))
    }

    fn parse_rel(&self, s: &str) -> Result<Relation, CheckError> {
        let r = self.lift(self.scope.parse_rel(s))?;
        self.lift(self.th.check_signs(r.expr()))?;
        Ok(r)
    }

    fn parse_term(&self, s: &str) -> Result<Term, CheckError> {
        let t = self.lift(self.scope.parse_term(s))?;
        self.lift(self.th.check_signs(t.expr()))?;
        Ok(t)
    }

    fn need_formula(&self, given: &Option<Relation>, what: &str) -> Result<Relation, CheckError> {
        given.clone().ok_or_else(|| {
            self.err(format!(
                "для {what} формулу строки нужно написать (не \"_\")"
            ))
        })
    }

    fn lines(&mut self, lines: &[Line]) -> Result<Vec<(String, Fact)>, CheckError> {
        self.frames.push(Vec::new());
        self.done.push(0);
        let res = (|| {
            for (i, l) in lines.iter().enumerate() {
                let no = (i + 1).to_string();
                if let Some(lab) = &l.label {
                    if lab.chars().all(|c| c.is_ascii_digit()) && *lab != no {
                        self.line = l.line;
                        return Err(self.err(format!("метка {lab} у строки номер {no} этого блока (номера ставятся сами, их можно не писать)")));
                    }
                }
                let f = self.line(l)?;
                let frame = self.frames.last_mut().unwrap();
                frame.push((no, f.clone()));
                if let Some(lab) = &l.label {
                    frame.push((lab.clone(), f));
                }
                *self.done.last_mut().unwrap() += 1;
            }
            Ok(())
        })();
        self.done.pop();
        let frame = self.frames.pop().unwrap();
        res.map(|_| frame)
    }

    /// Проверить блок в теории `t` с гипотезой `hyp` (метка `label`).
    fn block(
        &mut self,
        t: Th,
        label: &str,
        hyp: Relation,
        lines: &[Line],
    ) -> Result<Vec<(String, Fact)>, CheckError> {
        let thm = if self.expand {
            Some(self.lift(Theorem::axiom(&t, &hyp))?)
        } else {
            None
        };
        let saved = std::mem::replace(&mut self.th, t);
        self.frames
            .push(vec![(label.to_string(), Fact { rel: hyp, thm })]);
        let res = self.lines(lines);
        self.frames.pop();
        self.th = saved;
        res
    }

    fn line(&mut self, l: &Line) -> Result<Fact, CheckError> {
        self.line = l.line;
        let given = match &l.formula {
            Some(f) => Some(self.parse_rel(f)?),
            None => None,
        };
        self.line_given(l, given)
    }

    fn line_given(&mut self, l: &Line, given: Option<Relation>) -> Result<Fact, CheckError> {
        self.line = l.line;
        if !l.block.is_empty() && !matches!(l.just, Just::Assume(_) | Just::Contra(_)) {
            return Err(self.err(
                "вложенный блок { } бывает только у [предположим] (C14) и [от противного] (C15)",
            ));
        }
        let fact = match &l.just {
            Just::Sorry => {
                self.sorry = true;
                if self.expand {
                    return Err(self.err("в доказательстве есть sorry: раскрыть до атомов нельзя"));
                }
                Fact {
                    rel: self.need_formula(&given, "sorry")?,
                    thm: None,
                }
            }
            Just::MP(a, b) => self.mp(a, b)?,
            Just::Axiom(name) => self.axiom(&given, name)?,
            Just::Assume(label) => {
                let r = self.need_formula(&given, "C14")?;
                let (a, b) = r
                    .as_implies()
                    .ok_or_else(|| self.err(format!("C14: строка {r} должна иметь вид A ⇒ B")))?;
                let t = self.th.with_hypothesis(&a);
                let frame = self.block(
                    t,
                    label.as_deref().unwrap_or("гипотеза"),
                    a.clone(),
                    &l.block,
                )?;
                self.line = l.line;
                let last = frame
                    .last()
                    .ok_or_else(|| self.err("C14: пустой блок"))?
                    .1
                    .clone();
                if last.rel != b {
                    return Err(self.err(format!(
                        "C14: блок кончается на {}, а должен на {b}",
                        last.rel
                    )));
                }
                let thm = match last.thm {
                    Some(t) => Some(self.lift(t.discharge(&self.th, &a))?),
                    None => None,
                };
                Fact { rel: r, thm }
            }
            Just::Contra(label) => {
                let r = self.need_formula(&given, "C15")?;
                let t = self.th.with_hypothesis(&r.not());
                let frame =
                    self.block(t, label.as_deref().unwrap_or("гипотеза"), r.not(), &l.block)?;
                self.line = l.line;
                let pair = frame.iter().find_map(|(_, f)| {
                    let neg = f.rel.not();
                    frame
                        .iter()
                        .find(|(_, g)| g.rel == neg)
                        .map(|(_, g)| (f.clone(), g.clone()))
                });
                let (b, nb) = pair.ok_or_else(|| {
                    self.err("C15: в блоке нет двух строк вида B и не B (противоречия)")
                })?;
                let thm = match (b.thm, nb.thm) {
                    (Some(b), Some(nb)) => {
                        Some(self.lift(logic::close_contradiction(&self.th, &r, &b, &nb))?)
                    }
                    _ => None,
                };
                Fact { rel: r, thm }
            }
            Just::Generalize { letter, from } => {
                let x = self.letter(letter)?;
                let f = self.get(from)?;
                if self.th.is_constant(&x) {
                    return Err(self.err(format!(
                        "C27: буква {x} константа теории (встречается в аксиоме или гипотезе), обобщать по ней нельзя"
                    )));
                }
                let rel = f.rel.forall(&x);
                let thm = match &f.thm {
                    Some(t) => Some(self.lift(quant::generalize(t, &x))?),
                    None => None,
                };
                Fact { rel, thm }
            }
            Just::Subst { letter, term, from } => {
                let x = self.letter(letter)?;
                let t = self.parse_term(term)?;
                let f = self.get(from)?;
                if self.th.is_constant(&x) {
                    return Err(self.err(format!(
                        "C3: буква {x} константа теории, подставлять вместо неё нельзя"
                    )));
                }
                let rel = f.rel.subst(&x, &t);
                let thm = match &f.thm {
                    Some(th) => Some(self.lift(th.subst(&x, &t))?),
                    None => None,
                };
                Fact { rel, thm }
            }
            Just::Taut => {
                let r = self.need_formula(&given, "тавтологии")?;
                if !self.th.is_logical() {
                    return Err(
                        self.err("тавтологии есть только в логической теории (схемы S1-S4)")
                    );
                }
                if let Some(cex) = self.lift(logic::tautology_counterexample(&r))? {
                    return Err(self.err(format!("{r} не тавтология: ложно при {cex}")));
                }
                let thm = if self.expand {
                    Some(self.lift(logic::taut(&self.th, &r))?)
                } else {
                    None
                };
                Fact { rel: r, thm }
            }
            Just::Use {
                name,
                assigns,
                refs,
            } => self.use_(name, assigns, refs, &given)?,
        };
        if let Some(g) = &given {
            if *g != fact.rel {
                return Err(self.err(format!("написано {g}, а получается {}", fact.rel)));
            }
        }
        Ok(fact)
    }

    fn letter(&self, s: &str) -> Result<Letter, CheckError> {
        if Letter::is_valid(s) {
            Ok(Letter::new(s))
        } else {
            Err(self.err(format!("\"{s}\" не буква")))
        }
    }

    fn mp(&self, a: &str, b: &str) -> Result<Fact, CheckError> {
        let fa = self.get(a)?;
        let fb = self.get(b)?;
        let (minor, major, concl) = if let Some((p, q)) =
            fb.rel.as_implies().filter(|(p, _)| *p == fa.rel)
        {
            let _ = p;
            (fa, fb, q)
        } else if let Some((_, q)) = fa.rel.as_implies().filter(|(p, _)| *p == fb.rel) {
            (fb, fa, q)
        } else {
            return Err(self.err(format!(
                "из {a} и {b} ничего не следует по C1: ни одна из строк не имеет вида (другая) ⇒ ...\n    {a}: {}\n    {b}: {}",
                fa.rel, fb.rel
            )));
        };
        let thm = match (&minor.thm, &major.thm) {
            (Some(x), Some(y)) => Some(self.lift(Theorem::mp(x, y))?),
            _ => None,
        };
        Ok(Fact { rel: concl, thm })
    }

    fn axiom(&self, given: &Option<Relation>, name: &Option<String>) -> Result<Fact, CheckError> {
        let r = match name {
            Some(n) => {
                let a = self
                    .k
                    .find_axiom_in(&self.names, n)
                    .map_err(|m| self.err(m))?;
                if let Some(g) = given {
                    if *g != a {
                        return Err(self.err(format!("аксиома {n} это {a}, а написано {g}")));
                    }
                }
                a.clone()
            }
            None => self.need_formula(given, "аксиомы")?,
        };
        if !self.th.has_axiom(&r) {
            return Err(self.err(format!("{r} не явная аксиома теории {}", self.th.name())));
        }
        let thm = if self.expand {
            Some(self.lift(Theorem::axiom(&self.th, &r))?)
        } else {
            None
        };
        Ok(Fact { rel: r, thm })
    }

    /// Разобрать явные подстановки `A := ...`, `R(x) := ...` для метапеременных `metas`.
    fn assignments(
        &self,
        owner: &str,
        metas: &[SpecialSign],
        assigns: &[Assign],
    ) -> Result<Vec<(SpecialSign, Expr)>, CheckError> {
        let mut out = Vec::new();
        for a in assigns {
            let m = metas
                .iter()
                .find(|m| m.name() == a.name)
                .ok_or_else(|| self.err(format!("у {owner} нет параметра {}", a.name)))?;
            if a.letters.len() != m.weight() {
                return Err(self.err(if m.weight() == 0 {
                    format!("{} без выделенных букв: пишите {} := ...", a.name, a.name)
                } else {
                    format!(
                        "у {} {} выделенных букв: пишите {}(x) := ...",
                        a.name,
                        m.weight(),
                        a.name
                    )
                }));
            }
            let letters: Vec<Letter> = a
                .letters
                .iter()
                .map(|l| self.letter(l))
                .collect::<Result<_, _>>()?;
            let e = if m.is_relational() {
                self.parse_rel(&a.value)?.0
            } else {
                self.parse_term(&a.value)?.0
            };
            if out.iter().any(|(s, _): &(SpecialSign, Expr)| s == m) {
                return Err(self.err(format!("{} подставлено дважды", a.name)));
            }
            out.push((m.clone(), e.abstract_letters(&letters)));
        }
        Ok(out)
    }

    /// Дополнить подстановку сопоставлением образцов с данными строками.
    fn infer(
        &self,
        owner: &str,
        metas: &[SpecialSign],
        mut sigma: Vec<(SpecialSign, Expr)>,
        pairs: &[(Expr, Expr)],
    ) -> Result<Vec<(SpecialSign, Expr)>, CheckError> {
        let unknown: Vec<SpecialSign> = metas
            .iter()
            .filter(|m| !sigma.iter().any(|(s, _)| s == *m))
            .cloned()
            .collect();
        if unknown.is_empty() {
            return Ok(sigma);
        }
        let fresh: Vec<SpecialSign> = unknown.iter().map(fresh_like).collect();
        let mut map = sigma.clone();
        for (m, f) in unknown.iter().zip(&fresh) {
            map.push((m.clone(), meta_body(f)));
        }
        let mut got = Vec::new();
        let replaced: Vec<(Expr, Expr)> = pairs
            .iter()
            .map(|(pat, t)| (pat.replace_signs(&map), t.clone()))
            .collect();
        if !Expr::match_many(&replaced, &fresh, &mut got) {
            // какая пара не подходит: проверить по одной, для сообщения
            for (k, (pat, target)) in pairs.iter().enumerate() {
                let mut g = Vec::new();
                if k + 1 == pairs.len() || !replaced[k].0.match_into(target, &fresh, &mut g) {
                    let shown = Relation(pat.replace_signs(&sigma));
                    return Err(self.err(format!(
                        "{owner}: {} не имеет вида {shown}",
                        Relation(target.clone())
                    )));
                }
            }
        }
        for (m, f) in unknown.iter().zip(&fresh) {
            match got.iter().find(|(s, _)| s == f) {
                Some((_, v)) => sigma.push((m.clone(), v.clone())),
                None => {
                    let how = if m.weight() == 0 {
                        format!("{} := ...", m.name())
                    } else {
                        let xs: Vec<&str> =
                            ["x", "y", "z", "u"].into_iter().take(m.weight()).collect();
                        format!("{}({}) := ...", m.name(), xs.join(", "))
                    };
                    return Err(self.err(format!(
                        "{owner}: не понять, что подставить вместо {}; укажите \"{how}\"",
                        m.name()
                    )));
                }
            }
        }
        Ok(sigma)
    }

    fn use_(
        &mut self,
        name: &str,
        assigns: &[Assign],
        refs: &[String],
        given: &Option<Relation>,
    ) -> Result<Fact, CheckError> {
        if assigns.is_empty() && refs.is_empty() {
            if let Some(f) = self.lookup(name) {
                return Ok(f);
            }
        }
        let k = self.k;
        if let Some(sch) = k
            .find_scheme_in(&self.names, name)
            .map_err(|m| self.err(m))?
        {
            let name = crate::theory::Scheme::name(sch.as_ref());
            // в теории должна быть именно эта схема, а не другая с тем же коротким именем
            let same = self
                .th
                .scheme(name)
                .is_some_and(|t| Rc::as_ptr(&t) as *const () == Rc::as_ptr(&sch) as *const ());
            if !same {
                return Err(self.err(format!(
                    "в теории {} нет схемы {}",
                    self.th.name(),
                    crate::theory::Scheme::name(sch.as_ref())
                )));
            }
            if !refs.is_empty() {
                return Err(self.err(format!(
                    "у схемы {name} нет гипотез, ссылки на строки лишние"
                )));
            }
            let metas = sch.metas().to_vec();
            let sigma = self.assignments(name, &metas, assigns)?;
            let pairs: Vec<(Expr, Expr)> = given
                .iter()
                .map(|g| (sch.pattern().expr().clone(), g.expr().clone()))
                .collect();
            let sigma = self.infer(name, &metas, sigma, &pairs)?;
            let rel = self.lift(Relation::from_expr(
                sch.pattern().expr().replace_signs(&sigma),
            ))?;
            let thm = if self.expand {
                let args: Vec<Arg> = metas
                    .iter()
                    .map(|m| Arg::Body {
                        holes: m.weight(),
                        body: sigma.iter().find(|(s, _)| s == m).unwrap().1.clone(),
                    })
                    .collect();
                Some(self.lift(Theorem::scheme(&self.th, name, args))?)
            } else {
                None
            };
            return Ok(Fact { rel, thm });
        }
        if let Some(lemma) = k
            .find_theorem_in(&self.names, name)
            .map_err(|m| self.err(m))?
        {
            if !lemma.base.is_literally_weaker(&self.th) {
                return Err(self.err(format!(
                    "теорема {name} доказана в теории {}, а здесь теория {} (она не сильнее)",
                    lemma.base.name(),
                    self.th.name()
                )));
            }
            if refs.len() != lemma.hyps.len() {
                return Err(self.err(format!(
                    "у теоремы {name} гипотез {}, а ссылок на строки {}",
                    lemma.hyps.len(),
                    refs.len()
                )));
            }
            let facts: Vec<Fact> = refs.iter().map(|r| self.get(r)).collect::<Result<_, _>>()?;
            let sigma = self.assignments(name, &lemma.metas, assigns)?;
            let mut pairs: Vec<(Expr, Expr)> = Vec::new();
            if let Some(g) = given {
                pairs.push((lemma.statement.expr().clone(), g.expr().clone()));
            }
            for ((_, h), f) in lemma.hyps.iter().zip(&facts) {
                pairs.push((h.expr().clone(), f.rel.expr().clone()));
            }
            let sigma = self.infer(name, &lemma.metas, sigma, &pairs)?;
            for ((hl, h), (r, f)) in lemma.hyps.iter().zip(refs.iter().zip(&facts)) {
                let need = Relation(h.expr().replace_signs(&sigma));
                if need != f.rel {
                    return Err(self.err(format!(
                        "гипотеза {hl} теоремы {name} это {need}, а строка {r} это {}",
                        f.rel
                    )));
                }
            }
            let rel = Relation(lemma.statement.expr().replace_signs(&sigma));
            self.lift(self.th.check_signs(rel.expr()))?;
            if lemma.sorry {
                self.sorry = true;
            }
            let thm = if self.expand {
                let full = lemma.expand(k)?;
                let hyp_thms: Vec<Theorem> = facts.iter().map(|f| f.thm.clone().unwrap()).collect();
                Some(self.lift(full.instantiate_signs(&sigma, &self.th, &hyp_thms))?)
            } else {
                None
            };
            return Ok(Fact { rel, thm });
        }
        if self.lookup(name).is_some() {
            return Err(self.err(format!(
                "{name} это строка, к ней нельзя ничего подставлять"
            )));
        }
        Err(self.err(format!(
            "неизвестно, что такое {name}: это не строка, не гипотеза, не схема и не теорема"
        )))
    }
}
