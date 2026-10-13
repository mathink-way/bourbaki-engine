//! § 2, n° 1 и n° 4. Теории: специальные знаки, явные аксиомы, схемы.
//!
//! Теория 𝒯 задаётся
//! 1° списком специальных знаков (с весами);
//! 2° явными аксиомами, буквы в них называются константами теории;
//! 3° схемами: правилами, которые выдают неявные аксиомы.
//!
//! "Наследование": [`Theory::extend`] строит теорию с теми же знаками, аксиомами и схемами
//! плюс новые. Она сильнее исходной (§ 2, n° 4), и по C4 все теоремы старой теории
//! переносятся в новую: [`crate::proof::Theorem::lift`] (а `mp` делает это сам).

use crate::error::{Error, Result};
use crate::expr::Expr;
use crate::formative::{Abs, Relation, Term};
use crate::sign::{Letter, SpecialSign};
use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeSet, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

pub type Th = Rc<Theory>;

/// Параметр схемы: соотношение, терм или соотношение с выделенной буквой R{x}.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Arg {
    Rel(Relation),
    Term(Term),
    Abs(Abs),
    /// Знакосочетание с `holes` дырами (для метапеременной веса `holes`, например R{x, y}).
    Body {
        holes: usize,
        body: Expr,
    },
}

impl Arg {
    /// Подстановка (T|y) в параметр. Нужна для C2: если 𝒜 получено схемой, то (T|y)𝒜
    /// получается той же схемой из подставленных параметров (условие б) определения схемы).
    pub fn subst(&self, y: &Letter, t: &Term) -> Arg {
        match self {
            Arg::Rel(r) => Arg::Rel(r.subst(y, t)),
            Arg::Term(u) => Arg::Term(u.subst(y, t)),
            Arg::Abs(a) => Arg::Abs(a.subst(y, t)),
            Arg::Body { holes, body } => Arg::Body {
                holes: *holes,
                body: body.subst(y, t.expr()),
            },
        }
    }

    pub fn expr(&self) -> &Expr {
        match self {
            Arg::Rel(r) => r.expr(),
            Arg::Term(t) => t.expr(),
            Arg::Abs(a) => a.body(),
            Arg::Body { body, .. } => body,
        }
    }

    /// Подстановка вместо знаков внутри параметра (для переноса доказательств с метапеременными).
    pub fn replace_signs(&self, map: &[(SpecialSign, Expr)]) -> Arg {
        match self {
            Arg::Rel(r) => Arg::Rel(Relation(r.expr().replace_signs(map))),
            Arg::Term(t) => Arg::Term(Term(t.expr().replace_signs(map))),
            Arg::Abs(a) => Arg::Abs(Abs {
                hint: a.hint.clone(),
                body: a.body().replace_signs(map),
            }),
            Arg::Body { holes, body } => Arg::Body {
                holes: *holes,
                body: body.replace_signs(map),
            },
        }
    }
}

impl From<Relation> for Arg {
    fn from(r: Relation) -> Arg {
        Arg::Rel(r)
    }
}
impl From<Term> for Arg {
    fn from(t: Term) -> Arg {
        Arg::Term(t)
    }
}
impl From<Abs> for Arg {
    fn from(a: Abs) -> Arg {
        Arg::Abs(a)
    }
}

/// Схема (§ 2, n° 1): правило, выдающее соотношения (неявные аксиомы) по параметрам.
///
/// Чтобы правило было схемой, оно должно выдерживать подстановку: если 𝒜 получено
/// правилом, то и (T|x)𝒜 получается им же. Для S1-S7 это верно (и проверено у Бурбаки);
/// для своих схем движок проверяет это на каждом конкретном шаге, где оно используется.
pub trait Scheme {
    fn name(&self) -> &str;
    /// Имена параметров через запятую, например "A, B, C" или "R{x}, T".
    fn params(&self) -> &str;
    fn instantiate(&self, th: &Theory, args: &[Arg]) -> Result<Relation>;
}

fn want_n(name: &str, args: &[Arg], n: usize) -> Result<()> {
    if args.len() != n {
        return Err(Error(format!(
            "схеме {name} нужно {n} параметров, дано {}",
            args.len()
        )));
    }
    Ok(())
}

fn rel<'a>(name: &str, args: &'a [Arg], i: usize) -> Result<&'a Relation> {
    match &args[i] {
        Arg::Rel(r) => Ok(r),
        _ => Err(Error(format!(
            "схема {name}: параметр {} должен быть соотношением",
            i + 1
        ))),
    }
}

fn term<'a>(name: &str, args: &'a [Arg], i: usize) -> Result<&'a Term> {
    match &args[i] {
        Arg::Term(t) => Ok(t),
        _ => Err(Error(format!(
            "схема {name}: параметр {} должен быть термом",
            i + 1
        ))),
    }
}

fn abs<'a>(name: &str, args: &'a [Arg], i: usize) -> Result<&'a Abs> {
    match &args[i] {
        Arg::Abs(a) => Ok(a),
        _ => Err(Error(format!(
            "схема {name}: параметр {} должен быть соотношением с выделенной буквой R{{x}}",
            i + 1
        ))),
    }
}

/// S1: (A или A) ⇒ A.
pub struct S1;
/// S2: A ⇒ (A или B).
pub struct S2;
/// S3: (A или B) ⇒ (B или A).
pub struct S3;
/// S4: (A ⇒ B) ⇒ ((C или A) ⇒ (C или B)).
pub struct S4;
/// S5: (T|x)R ⇒ (∃x)R.
pub struct S5;
/// S6: (T = U) ⇒ (R{T} ⇔ R{U}).
pub struct S6;
/// S7: ((∀x)(R ⇔ S)) ⇒ (τ_x(R) = τ_x(S)).
pub struct S7;

impl Scheme for S1 {
    fn name(&self) -> &str {
        "S1"
    }
    fn params(&self) -> &str {
        "A"
    }
    fn instantiate(&self, _th: &Theory, args: &[Arg]) -> Result<Relation> {
        want_n("S1", args, 1)?;
        let a = rel("S1", args, 0)?;
        Ok(a.or(a).implies(a))
    }
}

impl Scheme for S2 {
    fn name(&self) -> &str {
        "S2"
    }
    fn params(&self) -> &str {
        "A, B"
    }
    fn instantiate(&self, _th: &Theory, args: &[Arg]) -> Result<Relation> {
        want_n("S2", args, 2)?;
        let (a, b) = (rel("S2", args, 0)?, rel("S2", args, 1)?);
        Ok(a.implies(&a.or(b)))
    }
}

impl Scheme for S3 {
    fn name(&self) -> &str {
        "S3"
    }
    fn params(&self) -> &str {
        "A, B"
    }
    fn instantiate(&self, _th: &Theory, args: &[Arg]) -> Result<Relation> {
        want_n("S3", args, 2)?;
        let (a, b) = (rel("S3", args, 0)?, rel("S3", args, 1)?);
        Ok(a.or(b).implies(&b.or(a)))
    }
}

impl Scheme for S4 {
    fn name(&self) -> &str {
        "S4"
    }
    fn params(&self) -> &str {
        "A, B, C"
    }
    fn instantiate(&self, _th: &Theory, args: &[Arg]) -> Result<Relation> {
        want_n("S4", args, 3)?;
        let (a, b, c) = (
            rel("S4", args, 0)?,
            rel("S4", args, 1)?,
            rel("S4", args, 2)?,
        );
        Ok(a.implies(b).implies(&c.or(a).implies(&c.or(b))))
    }
}

impl Scheme for S5 {
    fn name(&self) -> &str {
        "S5"
    }
    fn params(&self) -> &str {
        "R{x}, T"
    }
    fn instantiate(&self, _th: &Theory, args: &[Arg]) -> Result<Relation> {
        want_n("S5", args, 2)?;
        let (r, t) = (abs("S5", args, 0)?, term("S5", args, 1)?);
        Ok(r.apply(t).implies(&r.exists()))
    }
}

impl Scheme for S6 {
    fn name(&self) -> &str {
        "S6"
    }
    fn params(&self) -> &str {
        "R{x}, T, U"
    }
    fn instantiate(&self, th: &Theory, args: &[Arg]) -> Result<Relation> {
        want_n("S6", args, 3)?;
        let (r, t, u) = (
            abs("S6", args, 0)?,
            term("S6", args, 1)?,
            term("S6", args, 2)?,
        );
        Ok(th.eq(t, u)?.implies(&r.apply(t).iff(&r.apply(u))))
    }
}

impl Scheme for S7 {
    fn name(&self) -> &str {
        "S7"
    }
    fn params(&self) -> &str {
        "R{x}, S{x}"
    }
    fn instantiate(&self, th: &Theory, args: &[Arg]) -> Result<Relation> {
        want_n("S7", args, 2)?;
        let (r, s) = (abs("S7", args, 0)?, abs("S7", args, 1)?);
        Ok(r.iff(s).forall().implies(&th.eq(&r.tau(), &s.tau())?))
    }
}

/// Схема, заданная образцом (как в тексте книги): соотношение, в котором метапеременные
/// есть специальные знаки (A, B веса 0; R{x} веса 1). Экземпляр получается подстановкой
/// вместо этих знаков.
///
/// Условие б) определения схемы (устойчивость к подстановке (T|x)) выполняется само,
/// если в образце нет свободных букв: (T|x) проходит внутрь параметров.
pub struct PatternScheme {
    name: String,
    metas: Vec<SpecialSign>,
    pattern: Relation,
    params: String,
}

impl PatternScheme {
    pub fn new(name: &str, metas: Vec<SpecialSign>, pattern: Relation) -> Result<PatternScheme> {
        let free = pattern.letters();
        if !free.is_empty() {
            let names: Vec<String> = free.iter().map(|l| l.to_string()).collect();
            return Err(Error(format!(
                "в образце схемы {name} есть свободные буквы {}: правило не выдержит подстановку (T|x), \
                 значит это не схема. Сделайте их метапеременными",
                names.join(", ")
            )));
        }
        let params = metas
            .iter()
            .map(|m| {
                if m.weight() == 0 {
                    m.name().to_string()
                } else {
                    let xs: Vec<String> = (0..m.weight())
                        .map(|i| format!("x{}", "'".repeat(i)))
                        .collect();
                    format!("{}({})", m.name(), xs.join(", "))
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        Ok(PatternScheme {
            name: name.into(),
            metas,
            pattern,
            params,
        })
    }

    pub fn metas(&self) -> &[SpecialSign] {
        &self.metas
    }

    pub fn pattern(&self) -> &Relation {
        &self.pattern
    }

    /// Знаки образца, кроме метапеременных (они должны быть в теории).
    pub fn theory_signs(&self) -> Vec<SpecialSign> {
        self.pattern
            .expr()
            .special_signs()
            .into_iter()
            .filter(|s| !self.metas.contains(s))
            .collect()
    }
}

/// Превратить параметр в тело с дырами для метапеременной `m`.
pub fn arg_body(m: &SpecialSign, a: &Arg) -> Result<Expr> {
    let want_rel = m.is_relational();
    let ok = |e: &Expr, rel: bool| -> Result<Expr> {
        if m.weight() == 0 {
            let sort = e.sort();
            let need = if want_rel {
                crate::expr::Sort::Relation
            } else {
                crate::expr::Sort::Term
            };
            if sort != Some(need) || rel != want_rel {
                return Err(Error(format!(
                    "вместо {m} нужен {}",
                    if want_rel {
                        "соотношение"
                    } else {
                        "терм"
                    }
                )));
            }
        }
        Ok(e.clone())
    };
    match a {
        Arg::Rel(r) => ok(r.expr(), true),
        Arg::Term(t) => ok(t.expr(), false),
        Arg::Abs(x) => {
            if m.weight() != 1 {
                return Err(Error(format!(
                    "у {m} вес {}, а дано соотношение с одной выделенной буквой",
                    m.weight()
                )));
            }
            Ok(x.body().clone())
        }
        Arg::Body { holes, body } => {
            if *holes != m.weight() {
                return Err(Error(format!(
                    "у {m} вес {}, а у подставляемого {holes} выделенных букв",
                    m.weight()
                )));
            }
            Ok(body.clone())
        }
    }
}

impl Scheme for PatternScheme {
    fn name(&self) -> &str {
        &self.name
    }
    fn params(&self) -> &str {
        &self.params
    }
    fn instantiate(&self, _th: &Theory, args: &[Arg]) -> Result<Relation> {
        want_n(&self.name, args, self.metas.len())?;
        let mut map = Vec::with_capacity(args.len());
        for (m, a) in self.metas.iter().zip(args) {
            map.push((
                m.clone(),
                arg_body(m, a).map_err(|e| Error(format!("схема {}: {e}", self.name)))?,
            ));
        }
        let r = self.pattern.expr().replace_signs(&map);
        Relation::from_expr(r).map_err(|e| Error(format!("схема {}: {e}", self.name)))
    }
}

/// Математическая теория.
pub struct Theory {
    name: String,
    signs: Vec<SpecialSign>,
    equality: Option<SpecialSign>,
    axioms: Vec<Relation>,
    axiom_set: HashSet<Relation>,
    schemes: Vec<Rc<dyn Scheme>>,
    parent: Option<Th>,
    fingerprint: u64,
}

/// Сборка теории по шагам.
pub struct TheoryBuilder {
    name: String,
    signs: Vec<SpecialSign>,
    equality: Option<SpecialSign>,
    axioms: Vec<Relation>,
    schemes: Vec<Rc<dyn Scheme>>,
    parent: Option<Th>,
}

impl TheoryBuilder {
    /// Добавить специальный знак.
    pub fn sign(mut self, s: &SpecialSign) -> Self {
        if !self.signs.contains(s) {
            self.signs.push(s.clone());
        }
        self
    }

    /// Добавить схему (если схема с таким именем уже есть, ничего не меняется).
    pub fn scheme(mut self, s: Rc<dyn Scheme>) -> Self {
        if !self.schemes.iter().any(|t| t.name() == s.name()) {
            self.schemes.push(s);
        }
        self
    }

    /// Логическая теория (§ 3, n° 1): схемы S1-S4.
    pub fn logical(self) -> Self {
        self.scheme(Rc::new(S1))
            .scheme(Rc::new(S2))
            .scheme(Rc::new(S3))
            .scheme(Rc::new(S4))
    }

    /// Кванторная теория (§ 4, n° 2): S1-S5.
    pub fn quantified(self) -> Self {
        self.logical().scheme(Rc::new(S5))
    }

    /// Эгалитарная теория (§ 5, n° 1): реляционный знак `=` веса 2 и схемы S1-S7.
    pub fn egalitarian(mut self, eq: &SpecialSign) -> Self {
        assert!(
            eq.is_relational() && eq.weight() == 2,
            "знак равенства должен быть реляционным веса 2"
        );
        self.equality = Some(eq.clone());
        self.sign(eq)
            .quantified()
            .scheme(Rc::new(S6))
            .scheme(Rc::new(S7))
    }

    /// Добавить явную аксиому.
    pub fn axiom(mut self, a: &Relation) -> Self {
        if !self.axioms.contains(a) {
            self.axioms.push(a.clone());
        }
        self
    }

    /// Добавить явную аксиому, записанную текстом (знаки берутся из уже добавленных).
    pub fn axiom_str(self, src: &str) -> Result<Self> {
        let a = crate::syntax::parse_relation(&self.signs, src)?;
        Ok(self.axiom(&a))
    }

    pub fn done(self) -> Result<Th> {
        let th = Theory::assemble(
            self.name,
            self.signs,
            self.equality,
            self.axioms,
            self.schemes,
            self.parent,
        );
        for a in &th.axioms {
            th.check_signs(a.expr())?;
        }
        Ok(Rc::new(th))
    }
}

impl Theory {
    fn assemble(
        name: String,
        signs: Vec<SpecialSign>,
        equality: Option<SpecialSign>,
        axioms: Vec<Relation>,
        schemes: Vec<Rc<dyn Scheme>>,
        parent: Option<Th>,
    ) -> Theory {
        let axiom_set: HashSet<Relation> = axioms.iter().cloned().collect();
        // отпечаток "как множества": порядок аксиом и знаков не важен
        let mut fp = 0u64;
        let mut mix = |tag: u8, x: &dyn Fn(&mut DefaultHasher)| {
            let mut h = DefaultHasher::new();
            tag.hash(&mut h);
            x(&mut h);
            fp = fp.wrapping_add(h.finish());
        };
        for s in &signs {
            mix(0, &|h| s.hash(h));
        }
        for a in &axiom_set {
            mix(1, &|h| a.hash(h));
        }
        for s in &schemes {
            mix(2, &|h| s.name().hash(h));
        }
        if let Some(e) = &equality {
            mix(3, &|h| e.hash(h));
        }
        Theory {
            name,
            signs,
            equality,
            axioms,
            axiom_set,
            schemes,
            parent,
            fingerprint: fp,
        }
    }

    /// Начать новую теорию (без знаков, аксиом и схем).
    pub fn build(name: &str) -> TheoryBuilder {
        TheoryBuilder {
            name: name.into(),
            signs: vec![],
            equality: None,
            axioms: vec![],
            schemes: vec![],
            parent: None,
        }
    }

    /// "Наследование": теория со всем, что есть в `self`, плюс то, что добавит строитель.
    pub fn extend(self: &Rc<Self>, name: &str) -> TheoryBuilder {
        TheoryBuilder {
            name: name.into(),
            signs: self.signs.clone(),
            equality: self.equality.clone(),
            axioms: self.axioms.clone(),
            schemes: self.schemes.clone(),
            parent: Some(self.clone()),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn signs(&self) -> &[SpecialSign] {
        &self.signs
    }
    pub fn axioms(&self) -> &[Relation] {
        &self.axioms
    }
    pub fn schemes(&self) -> &[Rc<dyn Scheme>] {
        &self.schemes
    }
    pub fn parent(&self) -> Option<&Th> {
        self.parent.as_ref()
    }
    pub fn equality(&self) -> Option<&SpecialSign> {
        self.equality.as_ref()
    }

    pub fn has_axiom(&self, a: &Relation) -> bool {
        self.axiom_set.contains(a)
    }

    pub fn scheme(&self, name: &str) -> Option<Rc<dyn Scheme>> {
        self.schemes.iter().find(|s| s.name() == name).cloned()
    }

    pub fn has_scheme(&self, name: &str) -> bool {
        self.scheme(name).is_some()
    }

    /// Логическая теория: есть S1-S4.
    ///
    /// Проверяется не только имя: схема с именем S1 должна давать те же экземпляры, что и
    /// S1 книги (иначе `taut` принял бы тавтологию в теории со "своей" S1).
    pub fn is_logical(&self) -> bool {
        let fresh = |n: &str| {
            Arg::Rel(Relation(crate::expr::Expr::special(
                SpecialSign::relational(&format!("{n}#проверка"), 0),
                vec![],
            )))
        };
        let args = [fresh("A"), fresh("B"), fresh("C")];
        let builtin: [(&str, Rc<dyn Scheme>, usize); 4] = [
            ("S1", Rc::new(S1), 1),
            ("S2", Rc::new(S2), 2),
            ("S3", Rc::new(S3), 2),
            ("S4", Rc::new(S4), 3),
        ];
        builtin.iter().all(|(n, b, k)| match self.scheme(n) {
            Some(s) => match (
                s.instantiate(self, &args[..*k]),
                b.instantiate(self, &args[..*k]),
            ) {
                (Ok(x), Ok(y)) => x == y,
                _ => false,
            },
            None => false,
        })
    }

    /// Константы теории: буквы, встречающиеся в явных аксиомах.
    pub fn constants(&self) -> BTreeSet<Letter> {
        self.axioms.iter().flat_map(|a| a.letters()).collect()
    }

    pub fn is_constant(&self, x: &Letter) -> bool {
        self.axioms.iter().any(|a| a.contains(x))
    }

    /// Буква, похожая на `hint`, не константа и не встречается в `avoid`.
    pub fn fresh_letter(&self, hint: &str, avoid: &[&Expr]) -> Letter {
        Letter::new(hint)
            .fresh(|l| self.is_constant(l) || avoid.iter().any(|e| e.contains_letter(l)))
    }

    /// Все специальные знаки выражения принадлежат теории.
    pub fn check_signs(&self, e: &Expr) -> Result<()> {
        for s in e.special_signs() {
            if !self.signs.contains(&s) {
                return Err(Error(format!(
                    "знак {s} не принадлежит теории {}",
                    self.name
                )));
            }
        }
        Ok(())
    }

    /// Соотношение T = U (только в эгалитарной теории).
    pub fn eq(&self, t: &Term, u: &Term) -> Result<Relation> {
        let e = self
            .equality
            .as_ref()
            .ok_or_else(|| Error(format!("теория {} не эгалитарная", self.name)))?;
        Relation::special(e, &[t.clone(), u.clone()])
    }

    /// Теория, получаемая присоединением аксиомы A (метод вспомогательной гипотезы, § 3, n° 3).
    pub fn with_hypothesis(self: &Rc<Self>, a: &Relation) -> Th {
        if self.has_axiom(a) {
            return self.clone();
        }
        let mut axioms = self.axioms.clone();
        axioms.push(a.clone());
        Rc::new(Theory::assemble(
            format!("{} + ({})", self.name, a),
            self.signs.clone(),
            self.equality.clone(),
            axioms,
            self.schemes.clone(),
            Some(self.clone()),
        ))
    }

    /// (T|x)𝒯 (§ 2, n° 3): знаки и схемы те же, явные аксиомы (T|x)Aᵢ.
    /// Если x не константа, это та же самая теория.
    pub fn substitute(self: &Rc<Self>, x: &Letter, t: &Term) -> Th {
        let new_signs: Vec<SpecialSign> = t
            .expr()
            .special_signs()
            .into_iter()
            .filter(|s| !self.signs.contains(s))
            .collect();
        if !self.is_constant(x) && new_signs.is_empty() {
            return self.clone();
        }
        let mut signs = self.signs.clone();
        signs.extend(new_signs);
        Rc::new(Theory::assemble(
            format!("({}|{x}){}", t, self.name),
            signs,
            self.equality.clone(),
            self.axioms.iter().map(|a| a.subst(x, t)).collect(),
            self.schemes.clone(),
            Some(self.clone()),
        ))
    }

    /// Достаточное условие "𝒯' сильнее 𝒯" (§ 2, n° 4) без доказательств: знаки и схемы 𝒯
    /// есть в 𝒯', а явные аксиомы 𝒯 буквально являются явными аксиомами 𝒯'.
    pub fn is_literally_weaker(&self, other: &Theory) -> bool {
        if std::ptr::eq(self, other) {
            return true;
        }
        if let Some(e) = &self.equality {
            if other.equality.as_ref() != Some(e) {
                return false;
            }
        }
        self.signs.iter().all(|s| other.signs.contains(s))
            && self.schemes.iter().all(|s| other.has_scheme(s.name()))
            && self.axioms.iter().all(|a| other.has_axiom(a))
    }

    /// Теории совпадают (те же знаки, аксиомы как множество, схемы).
    pub fn same(&self, other: &Theory) -> bool {
        std::ptr::eq(self, other)
            || (self.fingerprint == other.fingerprint
                && self.is_literally_weaker(other)
                && other.is_literally_weaker(self))
    }

    pub fn parse_rel(&self, src: &str) -> Result<Relation> {
        crate::syntax::parse_relation(&self.signs, src)
    }

    pub fn parse_term(&self, src: &str) -> Result<Term> {
        crate::syntax::parse_term(&self.signs, src)
    }

    /// R{x} из текста: `th.parse_abs("x", "x ∈ y")`.
    pub fn parse_abs(&self, x: &str, src: &str) -> Result<Abs> {
        Ok(self.parse_rel(src)?.abstract_over(&Letter::new(x)))
    }
}

impl fmt::Display for Theory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Теория {}", self.name)?;
        if let Some(p) = &self.parent {
            writeln!(f, "  наследует: {}", p.name)?;
        }
        let signs: Vec<String> = self.signs.iter().map(|s| format!("{s:?}")).collect();
        writeln!(
            f,
            "  знаки: {}",
            if signs.is_empty() {
                "нет".into()
            } else {
                signs.join(", ")
            }
        )?;
        let sch: Vec<&str> = self.schemes.iter().map(|s| s.name()).collect();
        writeln!(
            f,
            "  схемы: {}",
            if sch.is_empty() {
                "нет".into()
            } else {
                sch.join(", ")
            }
        )?;
        if self.axioms.is_empty() {
            writeln!(f, "  явных аксиом нет")?;
        } else {
            writeln!(f, "  явные аксиомы:")?;
            for a in &self.axioms {
                writeln!(f, "    {a}")?;
            }
            let c: Vec<String> = self.constants().iter().map(|l| l.to_string()).collect();
            writeln!(f, "  константы: {}", c.join(", "))?;
        }
        Ok(())
    }
}

impl fmt::Debug for Theory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Theory({})", self.name)
    }
}
