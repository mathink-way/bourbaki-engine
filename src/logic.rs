//! § 3. Логические теории: схемы S1-S4 и критерии C6-C25.
//!
//! Каждый критерий здесь есть функция, которая строит доказательство так, как это
//! сделано в книге (те же применения схем и C1 в том же порядке). Функции принимают
//! соотношения-параметры (жирные A, B, C у Бурбаки) и уже доказанные теоремы.
//!
//! Методы доказательства из § 3, n° 3 оформлены как функции с замыканием:
//! * [`assume`]: метод вспомогательной гипотезы (C14);
//! * [`by_contradiction`]: приведение к абсурду (C15);
//! * [`c18`]: разбор случаев;
//! * [`aux_constant`]: метод вспомогательной константы (C19).
//!
//! Плюс "хитрость" в духе формативных критериев: [`taut`] доказывает любую тавтологию
//! (упражнение 7 к главе I, конструктивное доказательство полноты по Кальмару).

use crate::error::{Error, Result};
use crate::expr::Shape;
use crate::formative::Relation;
use crate::proof::{Theorem, common_theory, unify};
use crate::sign::Letter;
use crate::theory::{Arg, Th};

// ---- схемы S1-S4 ----

/// S1: (A или A) ⇒ A.
pub fn s1(th: &Th, a: &Relation) -> Result<Theorem> {
    Theorem::scheme(th, "S1", vec![Arg::Rel(a.clone())])
}

/// S2: A ⇒ (A или B).
pub fn s2(th: &Th, a: &Relation, b: &Relation) -> Result<Theorem> {
    Theorem::scheme(th, "S2", vec![Arg::Rel(a.clone()), Arg::Rel(b.clone())])
}

/// S3: (A или B) ⇒ (B или A).
pub fn s3(th: &Th, a: &Relation, b: &Relation) -> Result<Theorem> {
    Theorem::scheme(th, "S3", vec![Arg::Rel(a.clone()), Arg::Rel(b.clone())])
}

/// S4: (A ⇒ B) ⇒ ((C или A) ⇒ (C или B)).
pub fn s4(th: &Th, a: &Relation, b: &Relation, c: &Relation) -> Result<Theorem> {
    Theorem::scheme(
        th,
        "S4",
        vec![
            Arg::Rel(a.clone()),
            Arg::Rel(b.clone()),
            Arg::Rel(c.clone()),
        ],
    )
}

/// C1 (силлогизм): из A и A ⇒ B получаем B.
pub fn mp(a: &Theorem, ab: &Theorem) -> Result<Theorem> {
    Theorem::mp(a, ab)
}

fn imp(t: &Theorem) -> Result<(Relation, Relation)> {
    t.relation()
        .as_implies()
        .ok_or_else(|| Error(format!("ожидалась импликация, а не {}", t.relation())))
}

// ---- § 3, n° 2. Первые следствия ----

/// C6: из A ⇒ B и B ⇒ C получаем A ⇒ C.
pub fn c6(ab: &Theorem, bc: &Theorem) -> Result<Theorem> {
    let (a, b) = imp(ab)?;
    let (b2, c) = imp(bc)?;
    if b != b2 {
        return Err(Error(format!("C6: {b} и {b2} не совпадают")));
    }
    let (ab, bc) = unify(ab, bc)?;
    let th = ab.theory().clone();
    // S4 с заменой A на B, B на C, C на "не A": (B ⇒ C) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))
    let ax = s4(&th, &b, &c, &a.not())?;
    mp(&ab, &mp(&bc, &ax)?)
}

/// C7: B ⇒ (A или B).
pub fn c7(th: &Th, a: &Relation, b: &Relation) -> Result<Theorem> {
    c6(&s2(th, b, a)?, &s3(th, b, a)?)
}

/// C8: A ⇒ A.
pub fn c8(th: &Th, a: &Relation) -> Result<Theorem> {
    c6(&s2(th, a, a)?, &s1(th, a)?)
}

/// C9: если B теорема, то A ⇒ B теорема.
pub fn c9(th: &Th, a: &Relation, b: &Theorem) -> Result<Theorem> {
    // B ⇒ ((не A) или B) по C7, т.е. B ⇒ (A ⇒ B)
    mp(b, &c7(th, &a.not(), b.relation())?)
}

/// C10: A или (не A).
pub fn c10(th: &Th, a: &Relation) -> Result<Theorem> {
    mp(&c8(th, a)?, &s3(th, &a.not(), a)?)
}

/// C11: A ⇒ (не не A). Это C10 для "не A".
pub fn c11(th: &Th, a: &Relation) -> Result<Theorem> {
    c10(th, &a.not())
}

/// C12: (A ⇒ B) ⇒ ((не B) ⇒ (не A)).
pub fn c12(th: &Th, a: &Relation, b: &Relation) -> Result<Theorem> {
    let nn_b = b.not().not();
    let t3 = mp(&c11(th, b)?, &s4(th, b, &nn_b, &a.not())?)?; // ((не A) или B) ⇒ ((не A) или (не не B))
    let t4 = s3(th, &a.not(), &nn_b)?; // ((не A) или (не не B)) ⇒ ((не не B) или (не A))
    c6(&t3, &t4)
}

/// C13: если A ⇒ B теорема, то (B ⇒ C) ⇒ (A ⇒ C) теорема.
pub fn c13(ab: &Theorem, c: &Relation) -> Result<Theorem> {
    let th = ab.theory().clone();
    let (a, b) = imp(ab)?;
    let (na, nb) = (a.not(), b.not());
    let t1 = mp(ab, &c12(&th, &a, &b)?)?; // (не B) ⇒ (не A)
    let t3 = mp(&t1, &s4(&th, &nb, &na, c)?)?; // (C или не B) ⇒ (C или не A)
    let t4 = s3(&th, &nb, c)?; // (не B или C) ⇒ (C или не B)
    let t5 = s3(&th, c, &na)?; // (C или не A) ⇒ (не A или C)
    c6(&c6(&t4, &t3)?, &t5)
}

/// Из B и "не B" выводится любое C (§ 3, n° 1: противоречивая теория доказывает всё).
pub fn ex_falso(b: &Theorem, nb: &Theorem, c: &Relation) -> Result<Theorem> {
    if *nb.relation() != b.relation().not() {
        return Err(Error(format!(
            "{} не есть отрицание {}",
            nb.relation(),
            b.relation()
        )));
    }
    let (b, nb) = unify(b, nb)?;
    let th = b.theory().clone();
    let bc = mp(&nb, &s2(&th, nb.relation(), c)?)?; // не B ⇒ (не B или C) = B ⇒ C
    mp(&b, &bc)
}

/// Шаг доказательства C14 для строки, полученной по C1 из Bⱼ и Bⱼ ⇒ Bᵢ:
/// из A ⇒ Bⱼ и A ⇒ (Bⱼ ⇒ Bᵢ) получить A ⇒ Bᵢ (дословно как в книге).
pub(crate) fn deduction_mp_step(
    base: &Th,
    a: &Relation,
    u: &Theorem,
    v: &Theorem,
) -> Result<Theorem> {
    let (_, sr) = imp(v)?;
    let (_, r) = sr
        .as_implies()
        .ok_or_else(|| Error("C14: ожидалось A ⇒ (S ⇒ R)".into()))?;
    let w = c13(u, &r)?; // (Bⱼ ⇒ Bᵢ) ⇒ (A ⇒ Bᵢ)
    let z = c6(v, &w)?; // A ⇒ (A ⇒ Bᵢ), т.е. (не A) или (A ⇒ Bᵢ)
    let ar = a.implies(&r);
    let na = a.not();
    let y = mp(&z, &s3(base, &na, &ar)?)?; // (A ⇒ Bᵢ) или (не A)
    let k = s2(base, &na, &r)?; // (не A) ⇒ (A ⇒ Bᵢ)
    let q = mp(&k, &s4(base, &na, &ar, &ar)?)?;
    let d = mp(&y, &q)?; // (A ⇒ Bᵢ) или (A ⇒ Bᵢ)
    mp(&d, &s1(base, &ar)?)
}

// ---- § 3, n° 3. Методы доказательства ----

/// I. Метод вспомогательной гипотезы (C14). "Предположим, что A справедливо":
/// замыкание получает теорию 𝒯 + A и саму гипотезу A как теорему и должно доказать B.
/// Результат: A ⇒ B в 𝒯.
pub fn assume(
    base: &Th,
    a: &Relation,
    f: impl FnOnce(&Th, Theorem) -> Result<Theorem>,
) -> Result<Theorem> {
    let t = base.with_hypothesis(a);
    let h = Theorem::axiom(&t, a)?;
    let b = f(&t, h)?;
    b.discharge(base, a)
}

/// II. Метод приведения к абсурду (C15). "Предположим, что A ложно": замыкание получает
/// теорию 𝒯 + (не A) и гипотезу "не A" и должно вернуть пару теорем B и "не B".
/// Результат: A в 𝒯.
pub fn by_contradiction(
    base: &Th,
    a: &Relation,
    f: impl FnOnce(&Th, Theorem) -> Result<(Theorem, Theorem)>,
) -> Result<Theorem> {
    let na = a.not();
    let t = base.with_hypothesis(&na);
    let h = Theorem::axiom(&t, &na)?;
    let (b, nb) = f(&t, h)?;
    close_contradiction(base, a, &b, &nb)
}

/// Конец доказательства C15: B и "не B" доказаны в 𝒯 + (не A); получить A в 𝒯.
pub fn close_contradiction(base: &Th, a: &Relation, b: &Theorem, nb: &Theorem) -> Result<Theorem> {
    let na = a.not();
    let a_in_t = ex_falso(b, nb, a)?;
    let na_a = a_in_t.discharge(base, &na)?; // (не A) ⇒ A
    let t2 = mp(&na_a, &s4(base, &na, a, a)?)?; // (A или не A) ⇒ (A или A)
    let t3 = mp(&c10(base, a)?, &t2)?;
    mp(&t3, &s1(base, a)?)
}

/// C16: (не не A) ⇒ A.
///
/// В книге доказывается приведением к абсурду. Здесь прямой вывод (короче в сотни раз,
/// потому что C14 не применяется): по C11 и S4 из "A или не A" получаем "A или не не не A",
/// а по S3 это "(не не не A) или A", т.е. (не не A) ⇒ A.
pub fn c16(th: &Th, a: &Relation) -> Result<Theorem> {
    let nnna = a.not().not().not();
    let t2 = mp(&c11(th, &a.not())?, &s4(th, &a.not(), &nnna, a)?)?; // (A или не A) ⇒ (A или не не не A)
    let t3 = mp(&c10(th, a)?, &t2)?;
    mp(&t3, &s3(th, a, &nnna)?)
}

/// C17: ((не B) ⇒ (не A)) ⇒ (A ⇒ B).
///
/// Прямой вывод: по C12 ((не B) ⇒ (не A)) ⇒ ((не не A) ⇒ (не не B)), затем внутри
/// подставляем A ⇒ не не A (C11) и не не B ⇒ B (C16).
pub fn c17(th: &Th, a: &Relation, b: &Relation) -> Result<Theorem> {
    let t1 = c12(th, &b.not(), &a.not())?;
    let t2 = pre_inner(&t1, &c11(th, a)?)?;
    post_inner(&t2, &c16(th, b)?)
}

/// Из X ⇒ (P ⇒ Q) и Q ⇒ R получить X ⇒ (P ⇒ R) (C6 "под гипотезой X").
pub fn post_inner(xpq: &Theorem, qr: &Theorem) -> Result<Theorem> {
    let (_, pq) = imp(xpq)?;
    let (p, _) = pq
        .as_implies()
        .ok_or_else(|| Error(format!("ожидалось X ⇒ (P ⇒ Q), а не {}", xpq.relation())))?;
    let (q, r) = imp(qr)?;
    let th = common_theory(&[xpq, qr])?;
    let t = mp(qr, &s4(&th, &q, &r, &p.not())?)?; // (P ⇒ Q) ⇒ (P ⇒ R)
    c6(xpq, &t)
}

/// Из X ⇒ (P ⇒ Q) и O ⇒ P получить X ⇒ (O ⇒ Q).
pub fn pre_inner(xpq: &Theorem, op: &Theorem) -> Result<Theorem> {
    let (_, pq) = imp(xpq)?;
    let (_, q) = pq
        .as_implies()
        .ok_or_else(|| Error(format!("ожидалось X ⇒ (P ⇒ Q), а не {}", xpq.relation())))?;
    c6(xpq, &c13(op, &q)?)
}

/// Из L ⇒ X, L ⇒ Y и X ⇒ (Y ⇒ Z) получить L ⇒ Z (без снятия гипотез).
pub fn imp_mp2(lx: &Theorem, ly: &Theorem, xyz: &Theorem) -> Result<Theorem> {
    let th = common_theory(&[lx, ly, xyz])?;
    let (l, _) = imp(lx)?;
    let lyz = c6(lx, xyz)?; // L ⇒ (Y ⇒ Z)
    deduction_mp_step(&th, &l, ly, &lyz)
}

/// (не G) ⇒ ((не H) ⇒ не (G или H)).
pub fn neg_or_lemma(th: &Th, g: &Relation, h: &Relation) -> Result<Theorem> {
    let a1 = s4(th, g, h, h)?; // (G ⇒ H) ⇒ ((H или G) ⇒ (H или H))
    let a2 = pre_inner(&a1, &s3(th, g, h)?)?; // (G ⇒ H) ⇒ ((G или H) ⇒ (H или H))
    let a3 = post_inner(&a2, &s1(th, h)?)?; // (G ⇒ H) ⇒ ((G или H) ⇒ H)
    let a4 = c6(&a3, &c12(th, &g.or(h), h)?)?; // (G ⇒ H) ⇒ (не H ⇒ не (G или H))
    c6(&s2(th, &g.not(), h)?, &a4) // не G ⇒ (G ⇒ H) по S2
}

/// A ⇒ (B ⇒ (A и B)).
pub fn and_intro_imp(th: &Th, a: &Relation, b: &Relation) -> Result<Theorem> {
    let l = neg_or_lemma(th, &a.not(), &b.not())?; // не не A ⇒ (не не B ⇒ (A и B))
    let l2 = pre_inner(&l, &c11(th, b)?)?;
    c6(&c11(th, a)?, &l2)
}

/// III. Метод разделения случаев (C18): из "A или B", A ⇒ C, B ⇒ C получаем C.
pub fn c18(a_or_b: &Theorem, ac: &Theorem, bc: &Theorem) -> Result<Theorem> {
    let th = common_theory(&[a_or_b, ac, bc])?;
    let (a, b) = a_or_b
        .relation()
        .as_or()
        .ok_or_else(|| Error(format!("C18: {} не имеет вида A или B", a_or_b.relation())))?;
    let (_, c) = imp(ac)?;
    let t1 = mp(ac, &s4(&th, &a, &c, &b)?)?; // (B или A) ⇒ (B или C)
    let t2 = mp(bc, &s4(&th, &b, &c, &c)?)?; // (C или B) ⇒ (C или C)
    let chain = c6(
        &c6(&c6(&c6(&s3(&th, &a, &b)?, &t1)?, &s3(&th, &b, &c)?)?, &t2)?,
        &s1(&th, &c)?,
    )?;
    mp(a_or_b, &chain)
}

/// IV. Метод вспомогательной константы (C19). x не константа 𝒯 и не встречается в B;
/// `witness` есть теорема (T|x)A; замыкание доказывает B в 𝒯 + A. Результат: B в 𝒯.
pub fn aux_constant(
    base: &Th,
    x: &Letter,
    a: &Relation,
    witness: &Theorem,
    f: impl FnOnce(&Th, Theorem) -> Result<Theorem>,
) -> Result<Theorem> {
    if base.is_constant(x) {
        return Err(Error(format!("C19: {x} константа теории {}", base.name())));
    }
    let ab = assume(base, a, f)?;
    let (_, b) = imp(&ab)?;
    if b.contains(x) {
        return Err(Error(format!("C19: буква {x} встречается в {b}")));
    }
    // witness = (T|x)A; находим T подстановкой в A ⇒ B по C3
    let wa = witness.relation();
    let t = find_instance(a, x, wa).ok_or_else(|| {
        Error(format!(
            "C19: {wa} не получается из {a} подстановкой вместо {x}"
        ))
    })?;
    let inst = ab.subst(x, &t)?; // (T|x)A ⇒ B
    mp(witness, &inst)
}

/// Найти терм T с (T|x)A = W (сопоставление по образцу).
pub(crate) fn find_instance(
    a: &Relation,
    x: &Letter,
    w: &Relation,
) -> Option<crate::formative::Term> {
    use crate::expr::Expr;
    fn go(p: &Expr, w: &Expr, x: &Letter, found: &mut Option<Expr>) -> bool {
        match (p.shape(), w.shape()) {
            (Shape::Letter(l), _) if l == x => match found {
                Some(t) => t == w,
                None => {
                    *found = Some(w.clone());
                    true
                }
            },
            _ if !p.contains_letter(x) => p == w,
            (Shape::Not(a), Shape::Not(b)) => go(a, b, x, found),
            (Shape::Or(a1, b1), Shape::Or(a2, b2)) => go(a1, a2, x, found) && go(b1, b2, x, found),
            (Shape::Tau(_, a), Shape::Tau(_, b)) => go(a, b, x, found),
            (Shape::Special(s, xs), Shape::Special(t, ys)) => {
                s == t && xs.len() == ys.len() && xs.iter().zip(ys).all(|(a, b)| go(a, b, x, found))
            }
            _ => false,
        }
    }
    let mut found = None;
    if go(a.expr(), w.expr(), x, &mut found) {
        let t = found.unwrap_or_else(|| Expr::letter(x.clone()));
        if t.is_closed() {
            return Some(crate::formative::Term(t));
        }
    }
    None
}

// ---- § 3, n° 4. Конъюнкция ----

/// C20: если A и B теоремы, то "A и B" теорема.
pub fn and_intro(ta: &Theorem, tb: &Theorem) -> Result<Theorem> {
    let th = common_theory(&[ta, tb])?;
    let l = and_intro_imp(&th, ta.relation(), tb.relation())?;
    mp(tb, &mp(ta, &l)?)
}

/// C21: (A и B) ⇒ A.
pub fn and_left(th: &Th, a: &Relation, b: &Relation) -> Result<Theorem> {
    let o = a.not().or(&b.not());
    let t3 = c6(&s2(th, &a.not(), &b.not())?, &c11(th, &o)?)?; // не A ⇒ не (A и B)
    mp(&t3, &c17(th, &a.and(b), a)?)
}

/// C21: (A и B) ⇒ B.
pub fn and_right(th: &Th, a: &Relation, b: &Relation) -> Result<Theorem> {
    let o = a.not().or(&b.not());
    let t3 = c6(&c7(th, &a.not(), &b.not())?, &c11(th, &o)?)?; // не B ⇒ не (A и B)
    mp(&t3, &c17(th, &a.and(b), b)?)
}

fn and_parts(t: &Theorem) -> Result<(Relation, Relation)> {
    t.relation()
        .as_and()
        .ok_or_else(|| Error(format!("ожидалась конъюнкция, а не {}", t.relation())))
}

/// Из "A и B" получить A.
pub fn and_elim_l(t: &Theorem) -> Result<Theorem> {
    let (a, b) = and_parts(t)?;
    mp(t, &and_left(t.theory(), &a, &b)?)
}

/// Из "A и B" получить B.
pub fn and_elim_r(t: &Theorem) -> Result<Theorem> {
    let (a, b) = and_parts(t)?;
    mp(t, &and_right(t.theory(), &a, &b)?)
}

// ---- § 3, n° 5. Эквивалентность ----

/// Из A ⇒ B и B ⇒ A получить A ⇔ B.
pub fn iff_intro(ab: &Theorem, ba: &Theorem) -> Result<Theorem> {
    and_intro(ab, ba)
}

/// Из A ⇔ B и A получить B.
pub fn iff_mp(iff: &Theorem, a: &Theorem) -> Result<Theorem> {
    mp(a, &and_elim_l(iff)?)
}

/// Из A ⇔ B и B получить A.
pub fn iff_mpr(iff: &Theorem, b: &Theorem) -> Result<Theorem> {
    mp(b, &and_elim_r(iff)?)
}

/// A ⇔ A.
pub fn iff_refl(th: &Th, a: &Relation) -> Result<Theorem> {
    let t = c8(th, a)?;
    iff_intro(&t, &t)
}

/// Из A ⇔ B получить B ⇔ A.
pub fn iff_symm(t: &Theorem) -> Result<Theorem> {
    iff_intro(&and_elim_r(t)?, &and_elim_l(t)?)
}

/// C22: из A ⇔ B и B ⇔ C получить A ⇔ C.
pub fn c22(ab: &Theorem, bc: &Theorem) -> Result<Theorem> {
    let fwd = c6(&and_elim_l(ab)?, &and_elim_l(bc)?)?;
    let bwd = c6(&and_elim_r(bc)?, &and_elim_r(ab)?)?;
    iff_intro(&fwd, &bwd)
}

// ---- Упражнение 7: тавтологии ----

fn atoms(e: &Relation, out: &mut Vec<Relation>) {
    match e.expr().shape() {
        Shape::Not(_) => atoms(&e.as_not().unwrap(), out),
        Shape::Or(..) => {
            let (a, b) = e.as_or().unwrap();
            atoms(&a, out);
            atoms(&b, out);
        }
        _ => {
            if !out.contains(e) {
                out.push(e.clone());
            }
        }
    }
}

fn eval(e: &Relation, atoms: &[Relation], vals: &[bool]) -> bool {
    if let Some(i) = atoms.iter().position(|a| a == e) {
        return vals[i];
    }
    if let Some(a) = e.as_not() {
        return !eval(&a, atoms, vals);
    }
    let (a, b) = e.as_or().expect("атомы покрывают всё");
    eval(&a, atoms, vals) || eval(&b, atoms, vals)
}

/// Логически неприводимые составляющие соотношения (упр. 6): максимальные части,
/// не начинающиеся с ¬ и ∨.
pub fn logical_components(r: &Relation) -> Vec<Relation> {
    let mut out = Vec::new();
    atoms(r, &mut out);
    out
}

/// Является ли соотношение тавтологией (упр. 7: при всякой расстановке значений
/// составляющим оно получает значение "истинно").
pub fn is_tautology(r: &Relation) -> bool {
    matches!(tautology_counterexample(r), Ok(None))
}

/// Составляющие, если раскрывать ¬ и ∨ не глубже `depth` уровней (глубже части считаются
/// составляющими целиком). Подстановка в тавтологию даёт тавтологию, поэтому если
/// соотношение тавтология относительно таких крупных составляющих, оно тавтология.
fn atoms_upto(e: &Relation, depth: usize, out: &mut Vec<Relation>) -> bool {
    let open = depth > 0;
    match e.expr().shape() {
        Shape::Not(_) if open => atoms_upto(&e.as_not().unwrap(), depth - 1, out),
        Shape::Or(..) if open => {
            let (a, b) = e.as_or().unwrap();
            let x = atoms_upto(&a, depth - 1, out);
            let y = atoms_upto(&b, depth - 1, out);
            x && y
        }
        sh => {
            if !out.contains(e) {
                out.push(e.clone());
            }
            !matches!(sh, Shape::Not(_) | Shape::Or(..))
        }
    }
}

fn truth_table(r: &Relation, at: &[Relation]) -> Option<String> {
    for m in 0..1u64 << at.len() {
        let vals: Vec<bool> = (0..at.len()).map(|i| m >> i & 1 == 1).collect();
        if !eval(r, at, &vals) {
            let cex: Vec<String> = at
                .iter()
                .zip(&vals)
                .map(|(a, v)| format!("{a} := {}", if *v { "истина" } else { "ложь" }))
                .collect();
            return Some(cex.join(", "));
        }
    }
    None
}

/// Найти составляющие, относительно которых соотношение тавтология: сначала самые
/// крупные (неглубокое раскрытие), потом всё мельче. `Ok(Ok(составляющие))`, если
/// тавтология; `Ok(Err(контрпример))`, если нет даже при полном раскрытии; ошибка, если
/// составляющих больше `limit`.
pub fn tautology_atoms(
    r: &Relation,
    limit: usize,
) -> Result<std::result::Result<Vec<Relation>, String>> {
    let mut depth = 1;
    loop {
        let mut at = Vec::new();
        let complete = atoms_upto(r, depth, &mut at);
        if at.len() > limit {
            return Err(Error(format!(
                "слишком много логических составляющих ({})",
                at.len()
            )));
        }
        match truth_table(r, &at) {
            None => return Ok(Ok(at)),
            Some(cex) if complete => return Ok(Err(cex)),
            Some(_) => depth *= 2,
        }
    }
}

/// Проверка тавтологии: `Ok(None)` если тавтология, иначе расстановка значений
/// составляющим, при которой соотношение ложно.
///
/// Это та же таблица истинности, но строки перебираются с отсечением (метод Куайна):
/// значения составляющим даются по одной, начиная с самых внешних, и как только значение
/// всего соотношения уже определено, остальные не перебираются. Соотношение хранится
/// деревом с общими частями, так что повторяющиеся куски вычисляются один раз.
pub fn tautology_counterexample(r: &Relation) -> Result<Option<String>> {
    let mut g = PropGraph::default();
    let root = g.build(r.expr());
    if g.atoms.len() > 200 {
        return Err(Error(format!(
            "слишком много логических составляющих ({})",
            g.atoms.len()
        )));
    }
    let mut assign: Vec<Option<bool>> = vec![None; g.atoms.len()];
    Ok(g.search(root, &mut assign).map(|cex| {
        cex.iter()
            .enumerate()
            .filter_map(|(i, v)| {
                v.map(|v| {
                    format!(
                        "{} := {}",
                        Relation(g.atoms[i].clone()),
                        if v { "истина" } else { "ложь" }
                    )
                })
            })
            .collect::<Vec<_>>()
            .join(", ")
    }))
}

/// Соотношение как схема из ¬ и ∨ над составляющими (с общими частями).
#[derive(Default)]
struct PropGraph {
    nodes: Vec<PNode>,
    ids: std::collections::HashMap<crate::expr::Expr, usize>,
    atoms: Vec<crate::expr::Expr>,
}

#[derive(Clone, Copy)]
enum PNode {
    Atom(usize),
    Not(usize),
    Or(usize, usize),
}

impl PropGraph {
    fn build(&mut self, e: &crate::expr::Expr) -> usize {
        if let Some(&id) = self.ids.get(e) {
            return id;
        }
        let node = match e.shape() {
            Shape::Not(a) => PNode::Not(self.build(a)),
            Shape::Or(a, b) => {
                let x = self.build(a);
                let y = self.build(b);
                PNode::Or(x, y)
            }
            _ => {
                self.atoms.push(e.clone());
                PNode::Atom(self.atoms.len() - 1)
            }
        };
        self.nodes.push(node);
        let id = self.nodes.len() - 1;
        self.ids.insert(e.clone(), id);
        id
    }

    /// Трёхзначное значение (None: ещё не определено) при частичной расстановке.
    fn value(
        &self,
        id: usize,
        assign: &[Option<bool>],
        memo: &mut Vec<Option<Option<bool>>>,
    ) -> Option<bool> {
        if let Some(v) = memo[id] {
            return v;
        }
        let v = match self.nodes[id] {
            PNode::Atom(i) => assign[i],
            PNode::Not(a) => self.value(a, assign, memo).map(|v| !v),
            PNode::Or(a, b) => match self.value(a, assign, memo) {
                Some(true) => Some(true),
                x => match (x, self.value(b, assign, memo)) {
                    (_, Some(true)) => Some(true),
                    (Some(false), Some(false)) => Some(false),
                    _ => None,
                },
            },
        };
        memo[id] = Some(v);
        v
    }

    /// Первая (самая внешняя) составляющая без значения, от которой зависит результат.
    fn pick(
        &self,
        id: usize,
        assign: &[Option<bool>],
        memo: &mut Vec<Option<Option<bool>>>,
    ) -> Option<usize> {
        let mut queue = std::collections::VecDeque::from([id]);
        let mut seen = vec![false; self.nodes.len()];
        while let Some(n) = queue.pop_front() {
            if seen[n] || self.value(n, assign, memo).is_some() {
                continue;
            }
            seen[n] = true;
            match self.nodes[n] {
                PNode::Atom(i) => return Some(i),
                PNode::Not(a) => queue.push_back(a),
                PNode::Or(a, b) => {
                    queue.push_back(a);
                    queue.push_back(b);
                }
            }
        }
        None
    }

    fn search(&self, root: usize, assign: &mut Vec<Option<bool>>) -> Option<Vec<Option<bool>>> {
        let mut memo = vec![None; self.nodes.len()];
        match self.value(root, assign, &mut memo) {
            Some(true) => return None,
            Some(false) => return Some(assign.clone()),
            None => {}
        }
        let i = self
            .pick(root, assign, &mut memo)
            .expect("неопределённое значение без свободных составляющих");
        for v in [true, false] {
            assign[i] = Some(v);
            if let Some(cex) = self.search(root, assign) {
                assign[i] = None;
                return Some(cex);
            }
        }
        assign[i] = None;
        None
    }
}

/// Доказать тавтологию в логической теории: строится настоящее доказательство из S1-S4
/// (упр. 7 ж), конструкция Кальмара). Размер растёт как 2ⁿ, n = число составляющих,
/// поэтому составляющие берутся самые крупные из тех, при которых это тавтология.
pub fn taut(th: &Th, f: &Relation) -> Result<Theorem> {
    if !th.is_logical() {
        return Err(Error(format!(
            "теория {} не логическая (нет S1-S4)",
            th.name()
        )));
    }
    th.check_signs(f.expr())?;
    let at = match tautology_atoms(f, 12) {
        Ok(Ok(at)) => at,
        Ok(Err(cex)) => {
            return Err(Error(format!("{f} не тавтология: контрпример {cex}")));
        }
        Err(_) => {
            return Err(Error(
                "слишком много логических составляющих, доказательство будет огромным".into(),
            ));
        }
    };
    let mut vals = vec![false; at.len()];
    prove_ctx(th, f, &at, 0, &mut vals)
}

/// Тавтологическое следствие: из теорем H₁,...,Hₖ получить G, если
/// H₁ ⇒ (H₂ ⇒ ... ⇒ G) тавтология.
pub fn tauto(th: &Th, hyps: &[&Theorem], goal: &Relation) -> Result<Theorem> {
    let mut f = goal.clone();
    for h in hyps.iter().rev() {
        f = h.relation().implies(&f);
    }
    let mut th = th.clone();
    if !hyps.is_empty() {
        let h = common_theory(hyps)?;
        if th.is_literally_weaker(&h) {
            th = h;
        } else if !h.is_literally_weaker(&th) {
            return Err(Error(format!(
                "теории {} и {} несравнимы",
                th.name(),
                h.name()
            )));
        }
    }
    let mut t = taut(&th, &f)?;
    for h in hyps {
        t = mp(h, &t)?;
    }
    Ok(t)
}

fn lits(atoms: &[Relation], vals: &[bool], k: usize) -> Vec<Relation> {
    (0..k)
        .map(|i| {
            if vals[i] {
                atoms[i].clone()
            } else {
                atoms[i].not()
            }
        })
        .collect()
}

/// Контексты L₁ = l₁, Lₘ = Lₘ₋₁ и lₘ.
fn ctx_chain(lits: &[Relation]) -> Vec<Relation> {
    let mut v: Vec<Relation> = vec![lits[0].clone()];
    for l in &lits[1..] {
        let next = v.last().unwrap().and(l);
        v.push(next);
    }
    v
}

fn prove_ctx(
    th: &Th,
    f: &Relation,
    at: &[Relation],
    k: usize,
    vals: &mut Vec<bool>,
) -> Result<Theorem> {
    let n = at.len();
    if k == n {
        let ls = lits(at, vals, n);
        let ctxs = ctx_chain(&ls);
        let mut kal = Kalmar {
            th,
            at,
            vals,
            ls: &ls,
            ctxs: &ctxs,
            access: vec![None; n],
        };
        let (t, v) = kal.prove(f)?;
        debug_assert!(v);
        return Ok(t); // Lₙ ⇒ F
    }
    vals[k] = true;
    let tp = prove_ctx(th, f, at, k + 1, vals)?;
    vals[k] = false;
    let tn = prove_ctx(th, f, at, k + 1, vals)?;
    let p = &at[k];
    if k == 0 {
        // tp: p ⇒ F, tn: не p ⇒ F
        c18(&c10(th, p)?, &tp, &tn)
    } else {
        let ctx = ctx_chain(&lits(at, vals, k)).pop().unwrap();
        elim_atom(th, &ctx, p, f, &tp, &tn)
    }
}

/// (p ⇒ F) ⇒ ((не p ⇒ F) ⇒ F): разбор случаев как теорема (через C14 и C18).
fn cases_lemma(th: &Th, p: &Relation, f: &Relation) -> Result<Theorem> {
    let np = p.not();
    assume(th, &p.implies(f), |t1, h1| {
        assume(t1, &np.implies(f), |t2, h2| c18(&c10(t2, p)?, &h1, &h2))
    })
}

/// Из (L и p) ⇒ F и (L и не p) ⇒ F получить L ⇒ F.
fn elim_atom(
    th: &Th,
    ctx: &Relation,
    p: &Relation,
    f: &Relation,
    tp: &Theorem,
    tn: &Theorem,
) -> Result<Theorem> {
    let lp = post_inner(&and_intro_imp(th, ctx, p)?, tp)?; // L ⇒ (p ⇒ F)
    let ln = post_inner(&and_intro_imp(th, ctx, &p.not())?, tn)?; // L ⇒ (не p ⇒ F)
    imp_mp2(&lp, &ln, &cases_lemma(th, p, f)?)
}

struct Kalmar<'a> {
    th: &'a Th,
    at: &'a [Relation],
    vals: &'a [bool],
    ls: &'a [Relation],
    ctxs: &'a [Relation],
    access: Vec<Option<Theorem>>,
}

impl Kalmar<'_> {
    /// Lₘ ⇒ lᵢ.
    fn access(&mut self, m: usize, i: usize) -> Result<Theorem> {
        if m == 1 {
            return c8(self.th, &self.ls[0]);
        }
        let prev = &self.ctxs[m - 2];
        let l = &self.ls[m - 1];
        if i == m - 1 {
            and_right(self.th, prev, l)
        } else {
            let rest = self.access(m - 1, i)?;
            c6(&and_left(self.th, prev, l)?, &rest)
        }
    }

    /// Lₙ ⇒ F', где F' = F, если F истинно при данной расстановке, иначе F' = не F.
    fn prove(&mut self, e: &Relation) -> Result<(Theorem, bool)> {
        let n = self.at.len();
        if let Some(i) = self.at.iter().position(|a| a == e) {
            if self.access[i].is_none() {
                self.access[i] = Some(self.access(n, i)?);
            }
            return Ok((self.access[i].clone().unwrap(), self.vals[i]));
        }
        if let Some(g) = e.as_not() {
            let (tg, vg) = self.prove(&g)?;
            return if vg {
                Ok((c6(&tg, &c11(self.th, &g)?)?, false)) // L ⇒ не не G
            } else {
                Ok((tg, true)) // L ⇒ не G, а это и есть L ⇒ F
            };
        }
        let (g, h) = e.as_or().expect("атомы покрывают всё");
        let (tg, vg) = self.prove(&g)?;
        if vg {
            return Ok((c6(&tg, &s2(self.th, &g, &h)?)?, true));
        }
        let (th_, vh) = self.prove(&h)?;
        if vh {
            return Ok((c6(&th_, &c7(self.th, &g, &h)?)?, true));
        }
        let lem = neg_or_lemma(self.th, &g, &h)?;
        Ok((imp_mp2(&tg, &th_, &lem)?, false))
    }
}
