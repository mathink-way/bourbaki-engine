//! § 5. Эгалитарные теории: знак = веса 2, схемы S6 и S7.

use crate::error::{Error, Result};
use crate::formative::{Abs, Relation, Term};
use crate::logic::c8;
use crate::logic::{c11, iff_intro, iff_mp, mp};
use crate::proof::Theorem;
use crate::quant::{generalize, spec_as};
use crate::theory::{Arg, Th};

/// S6: (T = U) ⇒ (R{T} ⇔ R{U}).
pub fn s6(th: &Th, r: &Abs, t: &Term, u: &Term) -> Result<Theorem> {
    Theorem::scheme(
        th,
        "S6",
        vec![
            Arg::Abs(r.clone()),
            Arg::Term(t.clone()),
            Arg::Term(u.clone()),
        ],
    )
}

/// S7: ((∀x)(R ⇔ S)) ⇒ (τ_x(R) = τ_x(S)).
pub fn s7(th: &Th, r: &Abs, s: &Abs) -> Result<Theorem> {
    Theorem::scheme(th, "S7", vec![Arg::Abs(r.clone()), Arg::Abs(s.clone())])
}

fn eq_parts(th: &Th, r: &Relation) -> Result<(Term, Term)> {
    let e = th
        .equality()
        .ok_or_else(|| Error("теория не эгалитарная".into()))?;
    if let crate::expr::Shape::Special(s, args) = r.expr().shape() {
        if s == e {
            return Ok((Term(args[0].clone()), Term(args[1].clone())));
        }
    }
    Err(Error(format!("{r} не имеет вида T = U")))
}

/// Теорема 1: T = T (для всякого терма T).
///
/// Доказательство как в книге: S обозначает x = x. Для всякого R по C27 (∀x)(R ⇔ R),
/// поэтому по S7 τ_x(R) = τ_x(R). Берём R := не S; получаем (τ_x(не S)|x)S, т.е. (∀x)S
/// (после C11), и по C30 (T|x)S.
pub fn eq_refl(th: &Th, t: &Term) -> Result<Theorem> {
    let x = th.fresh_letter("x", &[t.expr()]);
    let xt = Term::letter(&x);
    let s = th.eq(&xt, &xt)?;
    let r = s.not();
    let rr = iff_intro(&c8(th, &r)?, &c8(th, &r)?)?; // R ⇔ R
    let g = generalize(&rr, &x)?; // (∀x)(R ⇔ R)
    let abs_r = Abs::new(&x, &r);
    let e = mp(&g, &s7(th, &abs_r, &abs_r)?)?; // τ_x(не S) = τ_x(не S)
    let all = mp(&e, &c11(th, e.relation())?)?; // (∀x)S
    spec_as(&all, &Abs::new(&x, &s), t)
}

/// Теорема 2 (симметрия): из T = U получить U = T.
pub fn eq_symm(tu: &Theorem) -> Result<Theorem> {
    let th = tu.theory().clone();
    let (t, u) = eq_parts(&th, tu.relation())?;
    let x = th.fresh_letter("x", &[t.expr(), u.expr()]);
    let r = Abs::new(&x, &th.eq(&Term::letter(&x), &t)?); // R{x}: x = T
    let iff = mp(tu, &s6(&th, &r, &t, &u)?)?; // (T = T) ⇔ (U = T)
    iff_mp(&iff, &eq_refl(&th, &t)?)
}

/// Теорема 3 (транзитивность): из T = U и U = V получить T = V.
pub fn eq_trans(tu: &Theorem, uv: &Theorem) -> Result<Theorem> {
    let th = crate::proof::common_theory(&[tu, uv])?;
    let (t, u) = eq_parts(&th, tu.relation())?;
    let (u2, v) = eq_parts(&th, uv.relation())?;
    if u != u2 {
        return Err(Error(format!(
            "транзитивность: {u:?} и {u2:?} разные термы"
        )));
    }
    let x = th.fresh_letter("x", &[t.expr(), u.expr(), v.expr()]);
    let r = Abs::new(&x, &th.eq(&t, &Term::letter(&x))?); // R{x}: T = x
    let iff = mp(uv, &s6(&th, &r, &u, &v)?)?; // (T = U) ⇔ (T = V)
    iff_mp(&iff, tu)
}

/// Замена равного равным (S6): из T = U и R{T} получить R{U}.
pub fn rewrite(tu: &Theorem, r: &Abs, rt: &Theorem) -> Result<Theorem> {
    let th = crate::proof::common_theory(&[tu, rt])?;
    let (t, u) = eq_parts(&th, tu.relation())?;
    let iff = mp(tu, &s6(&th, r, &t, &u)?)?;
    iff_mp(&iff, rt)
}
