//! § 4. Кванторные теории: (∃x)R есть (τ_x(R)|x)R, (∀x)R есть ¬(∃x)¬R, схема S5.
//!
//! Здесь нет новых "правил вывода": кванторы это сокращения, а всё, что про них
//! доказывается, выводится из S1-S5 критериями C26-C30 и методами из § 3.

use crate::error::{Error, Result};
use crate::formative::{Abs, Relation, Term};
use crate::logic::{assume, c6, c11, c12, c16, mp};
use crate::proof::Theorem;
use crate::sign::Letter;
use crate::theory::{Arg, Th};

/// S5: (T|x)R ⇒ (∃x)R.
pub fn s5(th: &Th, r: &Abs, t: &Term) -> Result<Theorem> {
    Theorem::scheme(th, "S5", vec![Arg::Abs(r.clone()), Arg::Term(t.clone())])
}

/// Введение ∃: из (T|x)R получить (∃x)R.
pub fn exists_intro(r: &Abs, t: &Term, thm: &Theorem) -> Result<Theorem> {
    mp(thm, &s5(thm.theory(), r, t)?)
}

/// C27 (обобщение): если R теорема и x не константа, то (∀x)R теорема.
pub fn generalize(thm: &Theorem, x: &Letter) -> Result<Theorem> {
    let th = thm.theory().clone();
    if th.is_constant(x) {
        return Err(Error(format!(
            "C27: {x} константа теории {}; из R не следует (∀{x})R",
            th.name()
        )));
    }
    let r = thm.relation().clone();
    let abs = Abs::new(x, &r);
    let t = abs.not().tau(); // τ_x(не R)
    let inst = thm.subst(x, &t)?; // (τ_x(не R)|x)R по C3
    let res = mp(&inst, &c11(&th, inst.relation())?)?; // не не (τ_x(не R)|x)R
    debug_assert_eq!(*res.relation(), abs.forall());
    Ok(res)
}

/// C30: (∀x)R ⇒ (T|x)R.
pub fn c30(th: &Th, r: &Abs, t: &Term) -> Result<Theorem> {
    let rt = r.apply(t);
    let s = s5(th, &r.not(), t)?; // не (T|x)R ⇒ (∃x) не R
    let c = mp(&s, &c12(th, &rt.not(), &r.not().exists())?)?; // (∀x)R ⇒ не не (T|x)R
    c6(&c, &c16(th, &rt)?)
}

/// Удаление ∀: из (∀x)R получить (T|x)R (R восстанавливается из записи автоматически).
pub fn spec(thm: &Theorem, t: &Term) -> Result<Theorem> {
    let r = thm
        .relation()
        .as_forall()
        .ok_or_else(|| Error(format!("{} не имеет вида (∀x)R", thm.relation())))?;
    spec_as(thm, &r, t)
}

/// Удаление ∀ с явно указанным R{x}.
pub fn spec_as(thm: &Theorem, r: &Abs, t: &Term) -> Result<Theorem> {
    if *thm.relation() != r.forall() {
        return Err(Error(format!(
            "{} не есть (∀x)R для данного R",
            thm.relation()
        )));
    }
    mp(thm, &c30(thm.theory(), r, t)?)
}

/// Удаление ∃ (метод вспомогательной константы с термом τ_x(R), § 4, n° 1):
/// из (∃x)R и доказательства B в 𝒯 + R (x не константа 𝒯 и не встречается в B) получить B.
/// Замыкание получает теорию 𝒯 + R и гипотезу R ("пусть x такой предмет, что R").
pub fn exists_elim(
    ex: &Theorem,
    x: &Letter,
    r: &Relation,
    f: impl FnOnce(&Th, Theorem) -> Result<Theorem>,
) -> Result<Theorem> {
    let th = ex.theory().clone();
    let abs = Abs::new(x, r);
    if *ex.relation() != abs.exists() {
        return Err(Error(format!("{} не есть (∃{x}){r}", ex.relation())));
    }
    if th.is_constant(x) {
        return Err(Error(format!("{x} константа теории {}", th.name())));
    }
    let rb = assume(&th, r, f)?; // R ⇒ B
    let b = rb.relation().as_implies().unwrap().1;
    if b.contains(x) {
        return Err(Error(format!("буква {x} встречается в заключении {b}")));
    }
    let inst = rb.subst(x, &abs.tau())?; // (∃x)R ⇒ B
    mp(ex, &inst)
}

/// C31 для ∃: если R ⇒ S теорема и x не константа, то (∃x)R ⇒ (∃x)S теорема.
pub fn exists_mono(rs: &Theorem, x: &Letter) -> Result<Theorem> {
    let th = rs.theory().clone();
    let (r, s) = rs
        .relation()
        .as_implies()
        .ok_or_else(|| Error("ожидалось R ⇒ S".into()))?;
    let er = r.exists(x);
    let abs_s = Abs::new(x, &s);
    assume(&th, &er, |_t, h| {
        exists_elim(&h, x, &r, |_t2, hr| {
            let s_thm = mp(&hr, rs)?;
            exists_intro(&abs_s, &Term::letter(x), &s_thm)
        })
    })
}

/// C31 для ∀: если R ⇒ S теорема и x не константа, то (∀x)R ⇒ (∀x)S теорема.
pub fn forall_mono(rs: &Theorem, x: &Letter) -> Result<Theorem> {
    let th = rs.theory().clone();
    let (r, _s) = rs
        .relation()
        .as_implies()
        .ok_or_else(|| Error("ожидалось R ⇒ S".into()))?;
    let ar = r.forall(x);
    let abs_r = Abs::new(x, &r);
    assume(&th, &ar, |_t, h| {
        let r_thm = spec_as(&h, &abs_r, &Term::letter(x))?;
        let s_thm = mp(&r_thm, rs)?;
        generalize(&s_thm, x)
    })
}

/// C29: соотношения "не (∃x)R" и (∀x)(не R) эквивалентны.
pub fn c29(th: &Th, x: &Letter, r: &Relation) -> Result<Theorem> {
    // (∀x)(не R) = не (∃x)(не не R)
    let fwd = exists_mono(&c11(th, r)?, x)?; // (∃x)R ⇒ (∃x) не не R
    let bwd = exists_mono(&c16(th, r)?, x)?; // (∃x) не не R ⇒ (∃x)R
    let p = r.exists(x);
    let q = r.not().not().exists(x);
    let goal = p.not().iff(&q.not());
    crate::logic::tauto(th, &[&fwd, &bwd], &goal)
}
