//! § 1, n° 3-4. Термы, соотношения, формативные конструкции, формативные критерии.
//!
//! По определению терм (соотношение) есть знакосочетание первого (второго) рода,
//! встречающееся в некоторой формативной конструкции. Значения типов [`Term`] и
//! [`Relation`] можно получить только конструкторами ниже, и каждый из них есть
//! один из формативных критериев CF1-CF12. Поэтому:
//!
//! * формативную конструкцию не нужно выписывать при каждом шаге: критерий гарантирует,
//!   что она существует (это и есть их смысл у Бурбаки);
//! * если нужно "раскрыть всё", её можно выписать явно: [`Term::formative_construction`],
//!   [`Relation::formative_construction`], а затем проверить буквально по определению
//!   (условия а)-д)): [`check_formative_construction`].

use crate::assembly::Assembly;
use crate::error::{Error, Result};
use crate::expr::{Expr, Shape, Sort};
use crate::sign::{Kind, Letter, Sign, SpecialSign};
use std::collections::{BTreeSet, HashMap};

/// Терм (знакосочетание первого рода из формативной конструкции).
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Term(pub(crate) Expr);

/// Соотношение (знакосочетание второго рода из формативной конструкции).
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Relation(pub(crate) Expr);

/// Соотношение R с выделенной буквой x, у Бурбаки R{x}. Хранится как тело, где на
/// месте x стоят □ (ещё не связанные). Отсюда получаются (T|x)R, τ_x(R), (∃x)R, (∀x)R.
#[derive(Clone)]
pub struct Abs {
    pub(crate) hint: Letter,
    pub(crate) body: Expr,
}

impl Term {
    /// а) буква есть терм.
    pub fn letter(x: &Letter) -> Term {
        Term(Expr::letter(x.clone()))
    }

    /// Сокращение: `Term::var("x")`.
    pub fn var(name: &str) -> Term {
        Term::letter(&Letter::new(name))
    }

    /// CF3: если R соотношение, x буква, то τ_x(R) терм.
    pub fn tau(x: &Letter, r: &Relation) -> Term {
        Term(Expr::tau(x.clone(), r.0.abstract_letter(x)))
    }

    /// CF4 (субстантивный знак): s T₁...Tₙ терм.
    pub fn special(s: &SpecialSign, args: &[Term]) -> Result<Term> {
        if s.kind() != Kind::Substantive {
            return Err(Error(format!(
                "знак {s} реляционный: s T₁...Tₙ будет соотношением, а не термом"
            )));
        }
        check_weight(s, args.len())?;
        Ok(Term(Expr::special(
            s.clone(),
            args.iter().map(|t| t.0.clone()).collect(),
        )))
    }

    /// CF8: (T|x)U терм.
    pub fn subst(&self, x: &Letter, t: &Term) -> Term {
        Term(self.0.subst(x, &t.0))
    }

    pub fn expr(&self) -> &Expr {
        &self.0
    }

    /// Проверить сорт произвольного выражения (например, разобранного из строки).
    pub fn from_expr(e: Expr) -> Result<Term> {
        match e.sort() {
            Some(Sort::Term) => Ok(Term(e)),
            _ => Err(Error(format!("{e:?} не терм"))),
        }
    }

    pub fn contains(&self, x: &Letter) -> bool {
        self.0.contains_letter(x)
    }

    pub fn letters(&self) -> BTreeSet<Letter> {
        self.0.letters()
    }

    /// Литеральная строка Бурбаки со связями.
    pub fn assembly(&self) -> Result<Assembly> {
        Assembly::from_expr(&self.0)
    }

    /// Явная формативная конструкция, в которой встречается этот терм.
    pub fn formative_construction(&self) -> Result<Vec<FormLine>> {
        formative_construction(&self.0)
    }

    /// Если терм есть буква, вернуть её.
    pub fn as_letter(&self) -> Option<&Letter> {
        if let Shape::Letter(l) = self.0.shape() {
            Some(l)
        } else {
            None
        }
    }
}

impl Relation {
    /// CF1: если A и B соотношения, то ∨AB соотношение ("A или B").
    pub fn or(&self, b: &Relation) -> Relation {
        Relation(Expr::or(self.0.clone(), b.0.clone()))
    }

    /// CF2: если A соотношение, то ¬A соотношение ("не A").
    pub fn not(&self) -> Relation {
        Relation(Expr::not(self.0.clone()))
    }

    /// CF4 (реляционный знак): s T₁...Tₙ соотношение.
    pub fn special(s: &SpecialSign, args: &[Term]) -> Result<Relation> {
        if s.kind() != Kind::Relational {
            return Err(Error(format!(
                "знак {s} субстантивный: s T₁...Tₙ будет термом, а не соотношением"
            )));
        }
        check_weight(s, args.len())?;
        Ok(Relation(Expr::special(
            s.clone(),
            args.iter().map(|t| t.0.clone()).collect(),
        )))
    }

    /// CF5: A ⇒ B, т.е. ∨¬AB.
    pub fn implies(&self, b: &Relation) -> Relation {
        self.not().or(b)
    }

    /// CF7, CF8: (T|x)R соотношение.
    pub fn subst(&self, x: &Letter, t: &Term) -> Relation {
        Relation(self.0.subst(x, &t.0))
    }

    /// CF9 (§ 3, n° 4): "A и B" есть ¬((¬A) ∨ (¬B)).
    pub fn and(&self, b: &Relation) -> Relation {
        self.not().or(&b.not()).not()
    }

    /// CF10 (§ 3, n° 5): A ⇔ B есть "(A ⇒ B) и (B ⇒ A)".
    pub fn iff(&self, b: &Relation) -> Relation {
        self.implies(b).and(&b.implies(self))
    }

    /// CF11 (§ 4, n° 1): (∃x)R есть (τ_x(R)|x)R.
    pub fn exists(&self, x: &Letter) -> Relation {
        Abs::new(x, self).exists()
    }

    /// CF11: (∀x)R есть ¬(∃x)(¬R).
    pub fn forall(&self, x: &Letter) -> Relation {
        Abs::new(x, self).forall()
    }

    /// CF12 (§ 4, n° 4): (∃_A x)R есть (∃x)(A и R).
    pub fn exists_in(&self, x: &Letter, a: &Relation) -> Relation {
        a.and(self).exists(x)
    }

    /// CF12: (∀_A x)R есть ¬(∃_A x)(¬R).
    pub fn forall_in(&self, x: &Letter, a: &Relation) -> Relation {
        self.not().exists_in(x, a).not()
    }

    /// Выделить букву: R ↦ R{x}.
    pub fn abstract_over(&self, x: &Letter) -> Abs {
        Abs::new(x, self)
    }

    pub fn expr(&self) -> &Expr {
        &self.0
    }

    pub fn from_expr(e: Expr) -> Result<Relation> {
        match e.sort() {
            Some(Sort::Relation) => Ok(Relation(e)),
            _ => Err(Error(format!("{e:?} не соотношение"))),
        }
    }

    pub fn contains(&self, x: &Letter) -> bool {
        self.0.contains_letter(x)
    }

    pub fn letters(&self) -> BTreeSet<Letter> {
        self.0.letters()
    }

    pub fn assembly(&self) -> Result<Assembly> {
        Assembly::from_expr(&self.0)
    }

    pub fn formative_construction(&self) -> Result<Vec<FormLine>> {
        formative_construction(&self.0)
    }

    // ---- разбор по форме (для печати и для критериев) ----

    pub fn as_not(&self) -> Option<Relation> {
        if let Shape::Not(a) = self.0.shape() {
            Some(Relation(a.clone()))
        } else {
            None
        }
    }

    pub fn as_or(&self) -> Option<(Relation, Relation)> {
        if let Shape::Or(a, b) = self.0.shape() {
            Some((Relation(a.clone()), Relation(b.clone())))
        } else {
            None
        }
    }

    /// A ⇒ B, т.е. ∨¬AB.
    pub fn as_implies(&self) -> Option<(Relation, Relation)> {
        let (na, b) = self.as_or()?;
        Some((na.as_not()?, b))
    }

    /// A и B, т.е. ¬∨¬A¬B.
    pub fn as_and(&self) -> Option<(Relation, Relation)> {
        let (na, nb) = self.as_not()?.as_or()?;
        Some((na.as_not()?, nb.as_not()?))
    }

    pub fn as_iff(&self) -> Option<(Relation, Relation)> {
        let (l, r) = self.as_and()?;
        let (a, b) = l.as_implies()?;
        let (b2, a2) = r.as_implies()?;
        (a == a2 && b == b2).then_some((a, b))
    }

    /// Прочитать как (∃x)R. Если прочтений несколько (бывает в вырожденных случаях),
    /// берётся первое; литерально это одно и то же знакосочетание.
    pub fn as_exists(&self) -> Option<Abs> {
        self.0
            .exists_readings()
            .into_iter()
            .next()
            .map(|(hint, body)| Abs { hint, body })
    }

    /// Прочитать как (∀x)R = ¬(∃x)¬R.
    pub fn as_forall(&self) -> Option<Abs> {
        let inner = self.as_not()?;
        inner
            .0
            .exists_readings()
            .into_iter()
            .find_map(|(hint, body)| match body.shape() {
                Shape::Not(b) => Some(Abs {
                    hint,
                    body: b.clone(),
                }),
                _ => None,
            })
    }
}

impl Abs {
    pub fn new(x: &Letter, r: &Relation) -> Abs {
        Abs {
            hint: x.clone(),
            body: r.0.abstract_letter(x),
        }
    }

    /// Буква, которой это соотношение было записано.
    pub fn letter(&self) -> &Letter {
        &self.hint
    }

    /// (T|x)R.
    pub fn apply(&self, t: &Term) -> Relation {
        Relation(self.body.instantiate(&t.0))
    }

    /// Само R{x} (с буквой x на месте □).
    pub fn relation(&self) -> Relation {
        self.apply(&Term::letter(&self.hint))
    }

    /// CF3: τ_x(R).
    pub fn tau(&self) -> Term {
        Term(Expr::tau(self.hint.clone(), self.body.clone()))
    }

    /// (∃x)R = (τ_x(R)|x)R.
    pub fn exists(&self) -> Relation {
        self.apply(&self.tau())
    }

    /// (∀x)R = ¬(∃x)(¬R).
    pub fn forall(&self) -> Relation {
        self.not().exists().not()
    }

    /// x ↦ ¬R{x}.
    pub fn not(&self) -> Abs {
        Abs {
            hint: self.hint.clone(),
            body: Expr::not(self.body.clone()),
        }
    }

    /// x ↦ (R{x} ⇔ S{x}) (буква та же).
    pub fn iff(&self, s: &Abs) -> Abs {
        let x = self
            .hint
            .fresh(|l| self.body.contains_letter(l) || s.body.contains_letter(l));
        let xr = self.apply(&Term::letter(&x));
        let xs = s.apply(&Term::letter(&x));
        Abs {
            hint: self.hint.clone(),
            body: xr.iff(&xs).0.abstract_letter(&x),
        }
    }

    /// Подстановка в R{x} вместо других букв (x уже не буква, а □, её не задеть).
    pub fn subst(&self, y: &Letter, t: &Term) -> Abs {
        Abs {
            hint: self.hint.clone(),
            body: self.body.subst(y, &t.0),
        }
    }

    pub fn contains(&self, y: &Letter) -> bool {
        self.body.contains_letter(y)
    }

    pub fn body(&self) -> &Expr {
        &self.body
    }
}

impl PartialEq for Abs {
    fn eq(&self, o: &Abs) -> bool {
        self.body == o.body
    }
}
impl Eq for Abs {}
impl std::hash::Hash for Abs {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.body.hash(h)
    }
}

fn check_weight(s: &SpecialSign, n: usize) -> Result<()> {
    if s.weight() != n {
        return Err(Error(format!(
            "у знака {s} вес {}, а дано {n} аргументов",
            s.weight()
        )));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Явные формативные конструкции.
// ---------------------------------------------------------------------------

/// Почему строка формативной конструкции допустима: какое из условий а)-д) выполнено.
#[derive(Clone, Debug)]
pub enum Formation {
    /// а) буква.
    Letter,
    /// б) ¬B, где B (вторая ссылка) соотношение выше.
    Not(usize),
    /// в) ∨BC.
    Or(usize, usize),
    /// г) τ_x(B).
    Tau(Letter, usize),
    /// д) sA₁...Aₙ.
    Special(SpecialSign, Vec<usize>),
}

#[derive(Clone, Debug)]
pub struct FormLine {
    pub assembly: Assembly,
    pub sort: Sort,
    pub why: Formation,
}

impl std::fmt::Display for FormLine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let why = match &self.why {
            Formation::Letter => "а) буква".to_string(),
            Formation::Not(i) => format!("б) ¬ от {}", i + 1),
            Formation::Or(i, j) => format!("в) ∨ от {} и {}", i + 1, j + 1),
            Formation::Tau(x, i) => format!("г) τ_{x} от {}", i + 1),
            Formation::Special(s, idx) => {
                format!(
                    "д) {s} от {}",
                    idx.iter()
                        .map(|i| (i + 1).to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        };
        write!(f, "{}    [{why}]", self.assembly)
    }
}

/// Выписать формативную конструкцию, в которой встречается данный терм или соотношение.
/// Повторяющиеся знакосочетания выписываются один раз.
pub fn formative_construction(e: &Expr) -> Result<Vec<FormLine>> {
    if e.sort().is_none() {
        return Err(Error(format!("{e:?} не терм и не соотношение")));
    }
    let mut lines = Vec::new();
    let mut index = HashMap::new();
    let mut taken = e.letters();
    visit(e, &mut lines, &mut index, &mut taken)?;
    Ok(lines)
}

fn visit(
    e: &Expr,
    lines: &mut Vec<FormLine>,
    index: &mut HashMap<Expr, usize>,
    taken: &mut BTreeSet<Letter>,
) -> Result<usize> {
    if let Some(&i) = index.get(e) {
        return Ok(i);
    }
    let (why, sort) = match e.shape() {
        Shape::Letter(_) => (Formation::Letter, Sort::Term),
        Shape::Bx(_) => return Err(Error("□ без τ".into())),
        Shape::Not(a) => (
            Formation::Not(visit(a, lines, index, taken)?),
            Sort::Relation,
        ),
        Shape::Or(a, b) => {
            let i = visit(a, lines, index, taken)?;
            let j = visit(b, lines, index, taken)?;
            (Formation::Or(i, j), Sort::Relation)
        }
        Shape::Tau(h, body) => {
            let x = h.fresh(|l| taken.contains(l));
            taken.insert(x.clone());
            let inst = body.instantiate(&Expr::letter(x.clone()));
            (
                Formation::Tau(x, visit(&inst, lines, index, taken)?),
                Sort::Term,
            )
        }
        Shape::Special(s, args) => {
            let mut idx = Vec::new();
            for a in args {
                idx.push(visit(a, lines, index, taken)?);
            }
            let sort = if s.is_relational() {
                Sort::Relation
            } else {
                Sort::Term
            };
            (Formation::Special(s.clone(), idx), sort)
        }
    };
    lines.push(FormLine {
        assembly: Assembly::from_expr(e)?,
        sort,
        why,
    });
    index.insert(e.clone(), lines.len() - 1);
    Ok(lines.len() - 1)
}

/// Проверить буквально по определению (§ 1, n° 3), что последовательность знакосочетаний
/// есть формативная конструкция теории со специальными знаками `signs`.
/// Возвращает сорт каждой строки (первого рода = терм, второго = соотношение).
pub fn check_formative_construction(seq: &[Assembly], signs: &[SpecialSign]) -> Result<Vec<Sort>> {
    let mut sorts = Vec::with_capacity(seq.len());
    for (k, a) in seq.iter().enumerate() {
        for s in a.signs() {
            if let Sign::Special(sp) = s {
                if !signs.contains(sp) {
                    return Err(Error(format!(
                        "строка {}: знак {sp} не принадлежит теории",
                        k + 1
                    )));
                }
            }
        }
        let sort = classify(a, &seq[..k], &sorts).ok_or_else(|| {
            Error(format!(
                "строка {}: \"{a}\" не удовлетворяет ни одному из условий а)-д)",
                k + 1
            ))
        })?;
        sorts.push(sort);
    }
    Ok(sorts)
}

fn classify(a: &Assembly, prev: &[Assembly], sorts: &[Sort]) -> Option<Sort> {
    let first = a.signs().first()?;
    // а)
    if a.len() == 1 && first.is_letter() {
        return Some(Sort::Term);
    }
    let rels: Vec<usize> = (0..prev.len())
        .filter(|&j| sorts[j] == Sort::Relation)
        .collect();
    match first {
        Sign::Not => {
            let not = Assembly::sign(Sign::Not);
            rels.iter()
                .any(|&j| prev[j].len() + 1 == a.len() && Assembly::concat(&[&not, &prev[j]]) == *a)
                .then_some(Sort::Relation)
        }
        Sign::Or => {
            let or = Assembly::sign(Sign::Or);
            for &j in &rels {
                for &l in &rels {
                    if prev[j].len() + prev[l].len() + 1 == a.len()
                        && Assembly::concat(&[&or, &prev[j], &prev[l]]) == *a
                    {
                        return Some(Sort::Relation);
                    }
                }
            }
            None
        }
        Sign::Tau => {
            for &j in &rels {
                if prev[j].len() + 1 != a.len() {
                    continue;
                }
                for x in prev[j].letters() {
                    if prev[j].tau(&x) == *a {
                        return Some(Sort::Term);
                    }
                }
            }
            None
        }
        Sign::Special(s) => {
            let terms: Vec<usize> = (0..prev.len())
                .filter(|&j| sorts[j] == Sort::Term)
                .collect();
            let ok = split_special(a, 1, s.weight(), &terms, prev, 0);
            ok.then_some(if s.is_relational() {
                Sort::Relation
            } else {
                Sort::Term
            })
        }
        _ => None,
    }
}

/// Можно ли остаток строки a с позиции `pos` разрезать на `left` термов из `prev`,
/// так чтобы связи строки были ровно связями кусков.
fn split_special(
    a: &Assembly,
    pos: usize,
    left: usize,
    terms: &[usize],
    prev: &[Assembly],
    links_so_far: usize,
) -> bool {
    if left == 0 {
        return pos == a.len() && links_so_far == a.links().len();
    }
    for &j in terms {
        let b = &prev[j];
        if pos + b.len() > a.len() {
            continue;
        }
        let signs_ok = a.signs()[pos..pos + b.len()] == *b.signs();
        let links_ok = b
            .links()
            .iter()
            .all(|(i, k)| a.links().contains(&(i + pos, k + pos)));
        if signs_ok
            && links_ok
            && split_special(
                a,
                pos + b.len(),
                left - 1,
                terms,
                prev,
                links_so_far + b.links().len(),
            )
        {
            return true;
        }
    }
    false
}
