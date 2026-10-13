//! § 2, n° 2-4. Доказательства и теоремы.
//!
//! Доказательство теории 𝒯 есть последовательность соотношений, каждое из которых
//! а₁) явная аксиома, или а₂) получено схемой, или б) следует из двух предыдущих S и S ⇒ R.
//! Теорема есть соотношение, встречающееся в доказательстве.
//!
//! Ядро: значение типа [`Theorem`] можно получить только тремя способами из определения
//! ([`Theorem::axiom`], [`Theorem::scheme`], [`Theorem::mp`]) или метатеоремами,
//! доказательства которых у Бурбаки конструктивны и потому здесь запрограммированы:
//! C2/C3 (подстановка), C4 (перенос в более сильную теорию), C5 (модели),
//! C14 (критерий дедукции). Каждая теорема помнит своё доказательство и может
//! выписать его полностью ([`Theorem::demonstration`]); выписанное доказательство
//! проверяется независимо ([`Demonstration::verify`]).

use crate::error::{Error, Result};
use crate::formative::{Relation, Term};
use crate::logic;
use crate::sign::Letter;
use crate::theory::{Arg, Scheme, Th};
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

pub(crate) type Pf = Rc<PNode>;

pub(crate) struct PNode {
    rel: Relation,
    step: Step,
    /// Фильтр Блума: какие явные аксиомы использованы (для быстрого C14).
    mask: u128,
}

pub(crate) enum Step {
    Axiom,
    Scheme(Rc<dyn Scheme>, Vec<Arg>),
    MP(Pf, Pf),
}

fn axiom_bit(r: &Relation) -> u128 {
    1u128 << (r.expr().hash_value() % 128)
}

fn node(rel: Relation, step: Step) -> Pf {
    let mask = match &step {
        Step::Axiom => axiom_bit(&rel),
        Step::Scheme(..) => 0,
        Step::MP(a, b) => a.mask | b.mask,
    };
    Rc::new(PNode { rel, step, mask })
}

/// Теорема теории (вместе со своим доказательством).
#[derive(Clone)]
pub struct Theorem {
    th: Th,
    pf: Pf,
}

impl Theorem {
    pub fn relation(&self) -> &Relation {
        &self.pf.rel
    }

    pub fn theory(&self) -> &Th {
        &self.th
    }

    /// а₁) явная аксиома теории.
    pub fn axiom(th: &Th, a: &Relation) -> Result<Theorem> {
        if !th.has_axiom(a) {
            return Err(Error(format!(
                "{a} не является явной аксиомой теории {}",
                th.name()
            )));
        }
        Ok(Theorem {
            th: th.clone(),
            pf: node(a.clone(), Step::Axiom),
        })
    }

    /// i-я явная аксиома (с нуля).
    pub fn axiom_n(th: &Th, i: usize) -> Result<Theorem> {
        let a = th.axioms().get(i).ok_or_else(|| {
            Error(format!(
                "в теории {} нет аксиомы номер {}",
                th.name(),
                i + 1
            ))
        })?;
        Theorem::axiom(th, &a.clone())
    }

    /// а₂) применение схемы теории (неявная аксиома).
    pub fn scheme(th: &Th, name: &str, args: Vec<Arg>) -> Result<Theorem> {
        let s = th
            .scheme(name)
            .ok_or_else(|| Error(format!("в теории {} нет схемы {name}", th.name())))?;
        let r = s.instantiate(th, &args)?;
        th.check_signs(r.expr())?;
        Ok(Theorem {
            th: th.clone(),
            pf: node(r, Step::Scheme(s, args)),
        })
    }

    /// б) и критерий C1 (силлогизм): из A и A ⇒ B получаем B.
    ///
    /// Удобство: если теоремы из разных теорий и одна теория сильнее другой (буквально,
    /// например вторая получена присоединением гипотезы), то слабая теорема сначала
    /// переносится в сильную теорию по C4.
    pub fn mp(minor: &Theorem, major: &Theorem) -> Result<Theorem> {
        let (a, b) = major
            .relation()
            .as_implies()
            .ok_or_else(|| Error(format!("C1: {} не имеет вида A ⇒ B", major.relation())))?;
        if a != *minor.relation() {
            return Err(Error(format!(
                "C1: посылка {} не совпадает с {}",
                a,
                minor.relation()
            )));
        }
        let (m1, m2) = unify(minor, major)?;
        Ok(Theorem {
            th: m1.th.clone(),
            pf: node(b, Step::MP(m1.pf, m2.pf)),
        })
    }

    /// C4 в простейшем случае: 𝒯' содержит знаки, схемы и явные аксиомы 𝒯.
    pub fn lift(&self, to: &Th) -> Result<Theorem> {
        if self.th.is_literally_weaker(to) {
            Ok(Theorem {
                th: to.clone(),
                pf: self.pf.clone(),
            })
        } else {
            Err(Error(format!(
                "нельзя перенести теорему из {} в {}: вторая теория не сильнее буквально (используйте lift_with)",
                self.th.name(),
                to.name()
            )))
        }
    }

    /// C4 в общем виде: знаки и схемы 𝒯 есть в 𝒯', а для каждой явной аксиомы 𝒯,
    /// использованной в доказательстве, `prove_axiom` даёт её доказательство в 𝒯'.
    /// Доказательство перестраивается так же, как у Бурбаки: аксиомы заменяются их доказательствами.
    pub fn lift_with(
        &self,
        to: &Th,
        prove_axiom: &mut dyn FnMut(&Relation) -> Result<Theorem>,
    ) -> Result<Theorem> {
        for s in self.th.signs() {
            if !to.signs().contains(s) {
                return Err(Error(format!("C4: знака {s} нет в теории {}", to.name())));
            }
        }
        let mut memo: HashMap<*const PNode, Pf> = HashMap::new();
        let pf = lift_rec(&self.pf, to, prove_axiom, &mut memo)?;
        Ok(Theorem { th: to.clone(), pf })
    }

    /// C2: если A теорема 𝒯, T терм, x буква, то (T|x)A теорема теории (T|x)𝒯.
    pub fn subst_c2(&self, x: &Letter, t: &Term) -> Result<Theorem> {
        let new_th = self.th.substitute(x, t);
        let mut memo: HashMap<*const PNode, Pf> = HashMap::new();
        let pf = subst_rec(&self.pf, x, t, &new_th, &mut memo)?;
        Ok(Theorem { th: new_th, pf })
    }

    /// C3: если x не константа 𝒯, то (T|x)A теорема той же теории 𝒯.
    pub fn subst(&self, x: &Letter, t: &Term) -> Result<Theorem> {
        if self.th.is_constant(x) {
            return Err(Error(format!(
                "C3: буква {x} константа теории {} (встречается в явной аксиоме), подставлять нельзя; см. C2/C5",
                self.th.name()
            )));
        }
        self.th.check_signs(t.expr())?;
        let r = self.subst_c2(x, t)?;
        Ok(Theorem {
            th: self.th.clone(),
            pf: r.pf,
        })
    }

    /// C14 (критерий дедукции): если B теорема теории 𝒯' = 𝒯 + A, то A ⇒ B теорема 𝒯.
    /// Доказательство в 𝒯' переделывается в доказательство в 𝒯 строка за строкой, как у Бурбаки.
    pub fn discharge(&self, base: &Th, a: &Relation) -> Result<Theorem> {
        let ext = base.with_hypothesis(a);
        if !self.th.is_literally_weaker(&ext) {
            return Err(Error(format!(
                "C14: теорема доказана в {}, а это не {} + ({a})",
                self.th.name(),
                base.name()
            )));
        }
        let mut memo: HashMap<*const PNode, Theorem> = HashMap::new();
        discharge_rec(&self.pf, base, a, axiom_bit(a), &mut memo)
    }

    /// Подстановка вместо специальных знаков (метапеременных) во всё доказательство.
    ///
    /// Теорема с метапеременными A, B доказана в теории 𝒯 ∪ {A, B} (метапеременные там
    /// специальные знаки, гипотезы леммы там явные аксиомы). Заменив в каждой строке
    /// доказательства знак A соотношением, получаем доказательство в `to`: явные аксиомы 𝒯
    /// знаков A, B не содержат, экземпляр схемы переходит в экземпляр той же схемы,
    /// силлогизм в силлогизм. Гипотезы леммы заменяются доказательствами из `hyps`.
    pub fn instantiate_signs(
        &self,
        map: &[(crate::sign::SpecialSign, crate::expr::Expr)],
        to: &Th,
        hyps: &[Theorem],
    ) -> Result<Theorem> {
        for s in self.th.signs() {
            if !to.signs().contains(s) && !map.iter().any(|(m, _)| m == s) {
                return Err(Error(format!("знака {s} нет в теории {}", to.name())));
            }
        }
        let hyps: Vec<Theorem> = hyps.iter().map(|h| h.lift(to)).collect::<Result<_>>()?;
        let mut memo: HashMap<*const PNode, Pf> = HashMap::new();
        let pf = inst_rec(&self.pf, map, to, &hyps, &mut memo)?;
        Ok(Theorem { th: to.clone(), pf })
    }

    /// Выписать доказательство целиком (повторы соотношений выписываются один раз).
    pub fn demonstration(&self) -> Demonstration {
        let mut lines = Vec::new();
        let mut index: HashMap<Relation, usize> = HashMap::new();
        linearize(&self.pf, &mut lines, &mut index);
        Demonstration {
            theory: self.th.clone(),
            lines,
        }
    }

    /// Число различных шагов в доказательстве.
    pub fn proof_size(&self) -> usize {
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![self.pf.clone()];
        while let Some(p) = stack.pop() {
            if !seen.insert(Rc::as_ptr(&p)) {
                continue;
            }
            if let Step::MP(a, b) = &p.step {
                stack.push(a.clone());
                stack.push(b.clone());
            }
        }
        seen.len()
    }
}

impl fmt::Display for Theorem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "⊢[{}] {}", self.th.name(), self.relation())
    }
}

impl fmt::Debug for Theorem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

/// Привести две теоремы к одной теории (более сильной из двух), используя C4.
pub(crate) fn unify(a: &Theorem, b: &Theorem) -> Result<(Theorem, Theorem)> {
    if Rc::ptr_eq(&a.th, &b.th) || a.th.same(&b.th) {
        return Ok((
            a.clone(),
            Theorem {
                th: a.th.clone(),
                pf: b.pf.clone(),
            },
        ));
    }
    if a.th.is_literally_weaker(&b.th) {
        return Ok((a.lift(&b.th)?, b.clone()));
    }
    if b.th.is_literally_weaker(&a.th) {
        return Ok((a.clone(), b.lift(&a.th)?));
    }
    Err(Error(format!(
        "теоремы из несравнимых теорий {} и {}",
        a.th.name(),
        b.th.name()
    )))
}

/// Самая сильная из теорий данных теорем (они должны быть сравнимы).
pub fn common_theory(ts: &[&Theorem]) -> Result<Th> {
    let mut th = ts
        .first()
        .ok_or_else(|| Error("нет теорем".into()))?
        .th
        .clone();
    for t in &ts[1..] {
        if t.th.is_literally_weaker(&th) {
            continue;
        }
        if th.is_literally_weaker(&t.th) {
            th = t.th.clone();
        } else {
            return Err(Error(format!(
                "теоремы из несравнимых теорий {} и {}",
                th.name(),
                t.th.name()
            )));
        }
    }
    Ok(th)
}

fn lift_rec(
    p: &Pf,
    to: &Th,
    prove_axiom: &mut dyn FnMut(&Relation) -> Result<Theorem>,
    memo: &mut HashMap<*const PNode, Pf>,
) -> Result<Pf> {
    if let Some(r) = memo.get(&Rc::as_ptr(p)) {
        return Ok(r.clone());
    }
    let r = match &p.step {
        Step::Axiom => {
            if to.has_axiom(&p.rel) {
                p.clone()
            } else {
                let t = prove_axiom(&p.rel)?;
                if t.relation() != &p.rel {
                    return Err(Error(format!(
                        "C4: вместо {} доказано {}",
                        p.rel,
                        t.relation()
                    )));
                }
                t.lift(to)?.pf
            }
        }
        Step::Scheme(s, args) => {
            let s2 = to
                .scheme(s.name())
                .ok_or_else(|| Error(format!("C4: в {} нет схемы {}", to.name(), s.name())))?;
            let inst = s2.instantiate(to, args)?;
            if inst != p.rel {
                return Err(Error(format!(
                    "C4: схема {} в {} даёт другое соотношение",
                    s.name(),
                    to.name()
                )));
            }
            p.clone()
        }
        Step::MP(a, b) => node(
            p.rel.clone(),
            Step::MP(
                lift_rec(a, to, prove_axiom, memo)?,
                lift_rec(b, to, prove_axiom, memo)?,
            ),
        ),
    };
    memo.insert(Rc::as_ptr(p), r.clone());
    Ok(r)
}

fn inst_rec(
    p: &Pf,
    map: &[(crate::sign::SpecialSign, crate::expr::Expr)],
    to: &Th,
    hyps: &[Theorem],
    memo: &mut HashMap<*const PNode, Pf>,
) -> Result<Pf> {
    if let Some(r) = memo.get(&Rc::as_ptr(p)) {
        return Ok(r.clone());
    }
    let rel = Relation(p.rel.expr().replace_signs(map));
    let r = match &p.step {
        Step::Axiom => {
            if to.has_axiom(&rel) {
                node(rel, Step::Axiom)
            } else if let Some(h) = hyps.iter().find(|h| *h.relation() == rel) {
                h.pf.clone()
            } else {
                return Err(Error(format!(
                    "после подстановки {rel} не аксиома теории {} и не дано как гипотеза",
                    to.name()
                )));
            }
        }
        Step::Scheme(s, args) => {
            let s2 = to
                .scheme(s.name())
                .ok_or_else(|| Error(format!("в теории {} нет схемы {}", to.name(), s.name())))?;
            let args2: Vec<Arg> = args.iter().map(|a| a.replace_signs(map)).collect();
            let inst = s2.instantiate(to, &args2)?;
            if inst != rel {
                return Err(Error(format!(
                    "схема {} после подстановки даёт {inst}, а нужно {rel}",
                    s.name()
                )));
            }
            node(rel, Step::Scheme(s2, args2))
        }
        Step::MP(a, b) => node(
            rel,
            Step::MP(
                inst_rec(a, map, to, hyps, memo)?,
                inst_rec(b, map, to, hyps, memo)?,
            ),
        ),
    };
    memo.insert(Rc::as_ptr(p), r.clone());
    Ok(r)
}

fn subst_rec(
    p: &Pf,
    x: &Letter,
    t: &Term,
    th: &Th,
    memo: &mut HashMap<*const PNode, Pf>,
) -> Result<Pf> {
    if let Some(r) = memo.get(&Rc::as_ptr(p)) {
        return Ok(r.clone());
    }
    let rel = p.rel.subst(x, t);
    let r = match &p.step {
        Step::Axiom => node(rel, Step::Axiom),
        Step::Scheme(s, args) => {
            let args2: Vec<Arg> = args.iter().map(|a| a.subst(x, t)).collect();
            let inst = s.instantiate(th, &args2)?;
            if inst != rel {
                return Err(Error(format!(
                    "правило {} не выдерживает подстановку ({t}|{x}), значит это не схема",
                    s.name()
                )));
            }
            node(rel, Step::Scheme(s.clone(), args2))
        }
        Step::MP(a, b) => node(
            rel,
            Step::MP(subst_rec(a, x, t, th, memo)?, subst_rec(b, x, t, th, memo)?),
        ),
    };
    memo.insert(Rc::as_ptr(p), r.clone());
    Ok(r)
}

fn discharge_rec(
    p: &Pf,
    base: &Th,
    a: &Relation,
    bit: u128,
    memo: &mut HashMap<*const PNode, Theorem>,
) -> Result<Theorem> {
    if let Some(r) = memo.get(&Rc::as_ptr(p)) {
        return Ok(r.clone());
    }
    let as_base = || Theorem {
        th: base.clone(),
        pf: p.clone(),
    };
    let r = if p.mask & bit == 0 {
        // A не используется: Bᵢ теорема 𝒯, и A ⇒ Bᵢ по C9
        logic::c9(base, a, &as_base())?
    } else {
        match &p.step {
            Step::Axiom if p.rel == *a => logic::c8(base, a)?,
            Step::Axiom | Step::Scheme(..) => logic::c9(base, a, &as_base())?,
            Step::MP(s, sr) => {
                let u = discharge_rec(s, base, a, bit, memo)?;
                let v = discharge_rec(sr, base, a, bit, memo)?;
                logic::deduction_mp_step(base, a, &u, &v)?
            }
        }
    };
    memo.insert(Rc::as_ptr(p), r.clone());
    Ok(r)
}

fn linearize(p: &Pf, lines: &mut Vec<Line>, index: &mut HashMap<Relation, usize>) -> usize {
    if let Some(&i) = index.get(&p.rel) {
        return i;
    }
    let why = match &p.step {
        Step::Axiom => Why::Axiom,
        Step::Scheme(s, args) => Why::Scheme {
            name: s.name().to_string(),
            params: s.params().to_string(),
            args: args.clone(),
        },
        Step::MP(a, b) => {
            let i = linearize(a, lines, index);
            let j = linearize(b, lines, index);
            Why::MP(i, j)
        }
    };
    lines.push(Line {
        relation: p.rel.clone(),
        why,
    });
    index.insert(p.rel.clone(), lines.len() - 1);
    lines.len() - 1
}

/// Выписанное доказательство в смысле § 2, n° 2.
pub struct Demonstration {
    pub theory: Th,
    pub lines: Vec<Line>,
}

pub struct Line {
    pub relation: Relation,
    pub why: Why,
}

pub enum Why {
    /// а₁) явная аксиома.
    Axiom,
    /// а₂) схема с параметрами.
    Scheme {
        name: String,
        params: String,
        args: Vec<Arg>,
    },
    /// б) из строк i (S) и j (S ⇒ R).
    MP(usize, usize),
}

impl Demonstration {
    /// Проверка по определению, независимо от того, как доказательство было построено.
    pub fn verify(&self) -> Result<()> {
        let th = &self.theory;
        for (k, line) in self.lines.iter().enumerate() {
            let r = &line.relation;
            th.check_signs(r.expr())
                .map_err(|e| Error(format!("строка {}: {e}", k + 1)))?;
            match &line.why {
                Why::Axiom => {
                    if !th.has_axiom(r) {
                        return Err(Error(format!("строка {}: {r} не явная аксиома", k + 1)));
                    }
                }
                Why::Scheme { name, args, .. } => {
                    let s = th
                        .scheme(name)
                        .ok_or_else(|| Error(format!("строка {}: нет схемы {name}", k + 1)))?;
                    if s.instantiate(th, args)? != *r {
                        return Err(Error(format!(
                            "строка {}: схема {name} даёт не это соотношение",
                            k + 1
                        )));
                    }
                }
                Why::MP(i, j) => {
                    if *i >= k || *j >= k {
                        return Err(Error(format!("строка {}: ссылка вперёд", k + 1)));
                    }
                    if self.lines[*j].relation != self.lines[*i].relation.implies(r) {
                        return Err(Error(format!(
                            "строка {}: строка {} не есть (строка {}) ⇒ (эта)",
                            k + 1,
                            j + 1,
                            i + 1
                        )));
                    }
                }
            }
        }
        Ok(())
    }

    pub fn len(&self) -> usize {
        self.lines.len()
    }

    pub fn is_empty(&self) -> bool {
        self.lines.is_empty()
    }
}

impl fmt::Display for Demonstration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Доказательство в теории {}:", self.theory.name())?;
        for (k, line) in self.lines.iter().enumerate() {
            let why = match &line.why {
                Why::Axiom => "явная аксиома".to_string(),
                Why::Scheme { name, params, args } => {
                    let names: Vec<&str> = params.split(',').map(|s| s.trim()).collect();
                    let parts: Vec<String> = args
                        .iter()
                        .enumerate()
                        .map(|(i, a)| format!("{} := {a}", names.get(i).copied().unwrap_or("?")))
                        .collect();
                    format!("{name}: {}", parts.join("; "))
                }
                Why::MP(i, j) => format!("из {} и {}", i + 1, j + 1),
            };
            writeln!(f, "{:>4}. {}    [{why}]", k + 1, line.relation)?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// C5: модели (применение результатов одной теории в другой).
// ---------------------------------------------------------------------------

/// C5 (§ 2, n° 4), своими словами. Заменим константы a₁, ..., aₕ теории 𝒯 термами
/// T₁, ..., Tₕ теории 𝒯'. Если знаки и схемы 𝒯 есть в 𝒯' и образ каждой явной аксиомы 𝒯
/// есть теорема 𝒯', то образ всякой теоремы 𝒯 есть теорема 𝒯'. Набор термов Tᵢ
/// называют моделью 𝒯 в 𝒯'.
pub struct Interpretation {
    from: Th,
    to: Th,
    subst: Vec<(Letter, Term)>,
    proofs: HashMap<Relation, Theorem>,
}

impl Interpretation {
    /// Что нужно доказать в 𝒯', чтобы получилась модель: (T₁|a₁)...(Tₕ|aₕ)Aᵢ для каждой аксиомы.
    pub fn obligations(from: &Th, subst: &[(Letter, Term)]) -> Vec<Relation> {
        from.axioms()
            .iter()
            .map(|a| apply_subst(a, subst))
            .collect()
    }

    /// Построить модель. `proofs` должны содержать теоремы 𝒯' для всех обязательств.
    pub fn new(
        from: &Th,
        to: &Th,
        subst: Vec<(Letter, Term)>,
        proofs: Vec<Theorem>,
    ) -> Result<Interpretation> {
        for s in from.signs() {
            if !to.signs().contains(s) {
                return Err(Error(format!("C5: знака {s} нет в {}", to.name())));
            }
        }
        for s in from.schemes() {
            if !to.has_scheme(s.name()) {
                return Err(Error(format!("C5: схемы {} нет в {}", s.name(), to.name())));
            }
        }
        let mut map = HashMap::new();
        for p in proofs {
            let p = p.lift(to)?;
            map.insert(p.relation().clone(), p);
        }
        for ob in Interpretation::obligations(from, &subst) {
            if !map.contains_key(&ob) {
                return Err(Error(format!("C5: не доказано в {}: {ob}", to.name())));
            }
        }
        Ok(Interpretation {
            from: from.clone(),
            to: to.clone(),
            subst,
            proofs: map,
        })
    }

    /// Перенести теорему 𝒯 в 𝒯': h раз C2, затем C4.
    pub fn apply(&self, thm: &Theorem) -> Result<Theorem> {
        let mut t = thm.lift(&self.from)?;
        // (T₁|a₁)(T₂|a₂)...(Tₕ|aₕ)A: первой выполняется подстановка вместо aₕ
        for (a, term) in self.subst.iter().rev() {
            t = t.subst_c2(a, term)?;
        }
        let proofs = &self.proofs;
        t.lift_with(&self.to, &mut |ax: &Relation| {
            proofs
                .get(ax)
                .cloned()
                .ok_or_else(|| Error(format!("C5: нет доказательства для {ax}")))
        })
    }

    pub fn from(&self) -> &Th {
        &self.from
    }
    pub fn to(&self) -> &Th {
        &self.to
    }
}

fn apply_subst(a: &Relation, subst: &[(Letter, Term)]) -> Relation {
    let mut r = a.clone();
    for (x, t) in subst.iter().rev() {
        r = r.subst(x, t);
    }
    r
}
