//! Тур по ядру главы I: `cargo run --example tour`.
//! Каждый раздел печатает то, что сделано, и (где коротко) раскрывает всё до знаков.

use bourbaki_engine::equality::{eq_refl, eq_symm, eq_trans};
use bourbaki_engine::formative::check_formative_construction;
use bourbaki_engine::logic::{assume, c6, c8, mp, s1, s2, taut};
use bourbaki_engine::quant::{generalize, spec};
use bourbaki_engine::*;

fn title(s: &str) {
    println!("\n══════ {s} ══════\n");
}

fn main() -> Result<()> {
    // --------------------------------------------------------------------
    title("§ 1. Знакосочетания");
    let eps = SpecialSign::relational("∈", 2).infix();
    let eq = SpecialSign::relational("=", 2).infix();
    let sets = Theory::build("Мн").sign(&eps).egalitarian(&eq).done()?;
    println!("{sets}");

    // пример со стр. 31: τ ∨ ¬ ∈ □ A' ∈ □ A''
    let asm = Assembly::new(
        vec![
            Sign::Tau,
            Sign::Or,
            Sign::Not,
            Sign::Special(eps.clone()),
            Sign::Box,
            Sign::Letter(Letter::new("A'")),
            Sign::Special(eps.clone()),
            Sign::Box,
            Sign::Letter(Letter::new("A''")),
        ],
        [(0, 4), (0, 7)],
    )?;
    println!("Знакосочетание со стр. 31:\n{}\n", asm.render());
    let (e, sort) = asm.parse()?;
    println!("По Приложению (критерий 2) это {sort}: {e:?}");

    // формативная конструкция со стр. 35
    let t = sets.parse_term("τA(A ∈ A' ⇒ A ∈ A'')")?;
    println!("\nЯвная формативная конструкция для {t}:");
    let fc = t.formative_construction()?;
    for (k, l) in fc.iter().enumerate() {
        println!("  {:>2}. {l}", k + 1);
    }
    let seq: Vec<Assembly> = fc.iter().map(|l| l.assembly.clone()).collect();
    check_formative_construction(&seq, sets.signs())?;
    println!("  проверено по определению (условия а)-д)).");

    // кванторы как сокращения
    let r = sets.parse_rel("(∃x)(x ∈ y)")?;
    println!("\n{r} есть на самом деле:\n{}", r.assembly()?.render());
    let big = sets.parse_rel("(∀x)(∀y)(∃z)(x ∈ z ∧ y ∈ z)")?;
    println!("\nА {big} это строка из {} знаков.", big.expr().len());

    // --------------------------------------------------------------------
    title("§ 2-3. Схемы и доказательства руками");
    let p = SpecialSign::relational("P", 0);
    let q = SpecialSign::relational("Q", 0);
    let logic = Theory::build("L").sign(&p).sign(&q).logical().done()?;
    let a = logic.parse_rel("P")?;
    let b = logic.parse_rel("Q")?;
    println!("Знаки P, Q веса 0: по условию д) это соотношения, удобно для чистой логики.\n");

    // C8 руками: A ⇒ (A или A) по S2, (A или A) ⇒ A по S1, затем C6
    let t1 = s2(&logic, &a, &a)?;
    let t2 = s1(&logic, &a)?;
    let aa = c6(&t1, &t2)?;
    println!("C8 руками: {aa}");
    print!("{}", aa.demonstration());

    // метод вспомогательной гипотезы
    let t = assume(&logic, &a, |t, h| mp(&h, &s2(t, &a, &b)?))?;
    println!(
        "\nC14: {t}  (доказательство после снятия гипотезы: {} строк)",
        t.demonstration().len()
    );

    // тавтология
    let f = logic.parse_rel("(P ⇒ Q) ⇔ (¬Q ⇒ ¬P)")?;
    let tt = taut(&logic, &f)?;
    let d = tt.demonstration();
    d.verify()?;
    println!(
        "Тавтология {f}: доказательство из S1-S4 на {} строк, проверено.",
        d.len()
    );

    // --------------------------------------------------------------------
    title("§ 4-5. Кванторы и равенство");
    let x = Letter::new("x");
    let refl = eq_refl(&sets, &sets.parse_term("τu(u ∈ v)")?)?;
    println!("Теорема 1: {refl}");
    println!("  (строк в доказательстве: {})", refl.demonstration().len());
    let g = generalize(&c8(&sets, &sets.parse_rel("x ∈ y")?)?, &x)?;
    println!("C27: {g}");

    // --------------------------------------------------------------------
    title("Наследование и модели (§ 2, n° 4: C4, C5)");
    let m = SpecialSign::substantive("m", 2);
    let unit = Theory::build("Единица")
        .sign(&m)
        .egalitarian(&eq)
        .axiom_str("(∀x)(m(e, x) = x)")?
        .axiom_str("(∀x)(m(x, e) = x)")?
        .done()?;
    println!("{unit}");
    let y = Letter::new("y");
    let e = Term::var("e");
    let hyp = unit.parse_rel("(∀x)(m(y, x) = x)")?;
    let uniq = generalize(
        &assume(&unit, &hyp, |t, h| {
            let left = spec(&h, &e)?; // m(y, e) = e
            let right = spec(&Theorem::axiom_n(t, 1)?, &Term::letter(&y))?; // m(y, e) = y
            eq_trans(&eq_symm(&right)?, &left)
        })?,
        &y,
    )?;
    println!("Теорема о единственности левой единицы:\n  {uniq}");
    let d = uniq.demonstration();
    d.verify()?;
    println!("  полное доказательство: {} строк, проверено.", d.len());

    let monoid = unit
        .extend("Моноид")
        .axiom_str("(∀x)(∀y)(∀z)(m(m(x, y), z) = m(x, m(y, z)))")?
        .done()?;
    println!("\nНаследование: {}", uniq.lift(&monoid)?);

    let other = Theory::build("Т'")
        .sign(&m)
        .egalitarian(&eq)
        .axiom_str("(∀x)(m(u, x) = x)")?
        .axiom_str("(∀x)(m(x, u) = x)")?
        .done()?;
    let subst = vec![(Letter::new("e"), Term::var("u"))];
    let proofs: Vec<Theorem> = Interpretation::obligations(&unit, &subst)
        .iter()
        .map(|r| Theorem::axiom(&other, r))
        .collect::<Result<_>>()?;
    let model = Interpretation::new(&unit, &other, subst, proofs)?;
    let applied = model.apply(&uniq)?;
    applied.demonstration().verify()?;
    println!("Модель e := u (C5): {applied}");
    Ok(())
}
