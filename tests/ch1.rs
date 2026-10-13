use bourbaki_engine::equality::*;
use bourbaki_engine::formative::check_formative_construction;
use bourbaki_engine::logic::*;
use bourbaki_engine::quant::*;
use bourbaki_engine::*;

fn set_signs() -> (SpecialSign, SpecialSign) {
    (
        SpecialSign::relational("∈", 2).infix(),
        SpecialSign::relational("=", 2).infix(),
    )
}

fn logic_th() -> Th {
    // логическая теория с тремя "пропозициональными" знаками веса 0
    Theory::build("L")
        .sign(&SpecialSign::relational("P", 0))
        .sign(&SpecialSign::relational("Q", 0))
        .sign(&SpecialSign::relational("R", 0))
        .logical()
        .done()
        .unwrap()
}

fn set_th() -> Th {
    let (eps, eq) = set_signs();
    Theory::build("Мн")
        .sign(&eps)
        .egalitarian(&eq)
        .done()
        .unwrap()
}

fn check(t: &Theorem) {
    let d = t.demonstration();
    d.verify()
        .unwrap_or_else(|e| panic!("доказательство {t} не прошло проверку: {e}\n{d}"));
}

#[test]
fn book_example_p31() {
    // τ ∨ ¬ ∈ □ A' ∈ □ A''  со связями от τ к обоим □
    let (eps, _) = set_signs();
    let a1 = Letter::new("A'");
    let a2 = Letter::new("A''");
    let signs = vec![
        Sign::Tau,
        Sign::Or,
        Sign::Not,
        Sign::Special(eps.clone()),
        Sign::Box,
        Sign::Letter(a1.clone()),
        Sign::Special(eps.clone()),
        Sign::Box,
        Sign::Letter(a2.clone()),
    ];
    let asm = Assembly::new(signs, [(0, 4), (0, 7)]).unwrap();
    assert!(asm.is_balanced());
    let (e, sort) = asm.parse().unwrap();
    assert_eq!(sort, Sort::Term);
    // это τ_A(A ∈ A' ⇒ A ∈ A'')
    let th = set_th();
    let t = th.parse_term("τA(A ∈ A' ⇒ A ∈ A'')").unwrap();
    assert_eq!(t.expr(), &e);
    assert_eq!(Assembly::from_expr(&e).unwrap(), asm);
    // формативная конструкция со стр. 35 проходит проверку
    let fc = t.formative_construction().unwrap();
    let seq: Vec<Assembly> = fc.iter().map(|l| l.assembly.clone()).collect();
    let sorts = check_formative_construction(&seq, th.signs()).unwrap();
    assert_eq!(*sorts.last().unwrap(), Sort::Term);
    println!("{}", asm.render());
}

#[test]
fn garbage_is_rejected() {
    let a = Assembly::new(vec![Sign::Or, Sign::Or], []).unwrap();
    assert!(a.parse().is_err());
    // □ без связи
    let (eps, _) = set_signs();
    let b = Assembly::new(
        vec![Sign::Tau, Sign::Special(eps), Sign::Box, Sign::Box],
        [(0, 2)],
    )
    .unwrap();
    assert!(b.parse().is_err());
    // плохая формативная конструкция
    let x = Assembly::letter(&Letter::new("x"));
    let nx = Assembly::concat(&[&Assembly::sign(Sign::Not), &x]);
    assert!(check_formative_construction(&[x, nx], &[]).is_err());
}

#[test]
fn substitution_criteria() {
    let th = set_th();
    let a = th.parse_rel("x ∈ y ∨ (∃z)(z ∈ x)").unwrap();
    let x = Letter::new("x");
    let x2 = Letter::new("x'");
    let b = th.parse_term("τu(u ∈ u)").unwrap();
    // CS1: (B|x)A = (B|x')(x'|x)A
    let lhs = a.subst(&x, &b);
    let rhs = a.subst(&x, &Term::letter(&x2)).subst(&x2, &b);
    assert_eq!(lhs, rhs);
    // CS3: τ_x(A) = τ_x'(A')
    let t1 = Term::tau(&x, &a);
    let t2 = Term::tau(&x2, &a.subst(&x, &Term::letter(&x2)));
    assert_eq!(t1, t2);
    // литеральная подстановка в строку совпадает с подстановкой в дереве
    let asm = a.assembly().unwrap().subst(&x, &b.assembly().unwrap());
    assert_eq!(asm.parse().unwrap().0, lhs.expr().clone());
}

#[test]
fn first_criteria() {
    let th = logic_th();
    let p = th.parse_rel("P").unwrap();
    let q = th.parse_rel("Q").unwrap();
    let r = th.parse_rel("R").unwrap();
    for t in [
        c8(&th, &p).unwrap(),
        c10(&th, &p).unwrap(),
        c11(&th, &p).unwrap(),
        c12(&th, &p, &q).unwrap(),
        c16(&th, &p).unwrap(),
        c17(&th, &p, &q).unwrap(),
        and_left(&th, &p, &q).unwrap(),
        and_right(&th, &p, &q).unwrap(),
    ] {
        check(&t);
    }
    assert_eq!(
        c8(&th, &p).unwrap().relation(),
        &th.parse_rel("P ⇒ P").unwrap()
    );
    assert_eq!(
        c16(&th, &p).unwrap().relation(),
        &th.parse_rel("¬¬P ⇒ P").unwrap()
    );
    // C14
    let t = assume(&th, &p, |t, h| {
        let pq = mp(&h, &s2(t, &p, &q)?)?;
        Ok(pq)
    })
    .unwrap();
    assert_eq!(t.relation(), &th.parse_rel("P ⇒ P ∨ Q").unwrap());
    check(&t);
    // C18
    let t = assume(&th, &p.or(&q), |t, h| {
        let pr = c9(t, &p, &c8(t, &r)?.lift(t)?);
        let _ = pr;
        let pp = s2(t, &p, &q)?;
        let qp = c7(t, &p, &q)?;
        c18(&h, &pp, &qp)
    })
    .unwrap();
    check(&t);
}

#[test]
fn tautologies_c24() {
    let th = logic_th();
    for src in [
        "¬¬P ⇔ P",
        "(P ⇒ Q) ⇔ (¬Q ⇒ ¬P)",
        "(P ∧ P) ⇔ P",
        "(P ∧ Q) ⇔ (Q ∧ P)",
        "(P ∧ (Q ∧ R)) ⇔ ((P ∧ Q) ∧ R)",
        "(P ∨ Q) ⇔ ¬(¬P ∧ ¬Q)",
        "(P ∧ (Q ∨ R)) ⇔ ((P ∧ Q) ∨ (P ∧ R))",
        "(P ∨ (Q ∧ R)) ⇔ ((P ∨ Q) ∧ (P ∨ R))",
        "(P ∧ ¬Q) ⇔ ¬(P ⇒ Q)",
        "(P ⇒ Q) ⇒ ((Q ⇒ R) ⇒ (P ⇒ R))",
    ] {
        let f = th.parse_rel(src).unwrap();
        let t = taut(&th, &f).unwrap_or_else(|e| panic!("{src}: {e}"));
        assert_eq!(t.relation(), &f);
        check(&t);
    }
    assert!(taut(&th, &th.parse_rel("P ⇒ Q").unwrap()).is_err());
}

#[test]
fn quantifiers() {
    let th = set_th();
    let x = Letter::new("x");
    let r = th.parse_rel("x ∈ y").unwrap();
    // ∃ и ∀ печатаются и читаются обратно
    let ex = r.exists(&x);
    assert_eq!(ex.to_string(), "(∃x)(x ∈ y)");
    assert_eq!(th.parse_rel(&ex.to_string()).unwrap(), ex);
    let all = th.parse_rel("(∀x)(∃z)(x ∈ z ⇒ z ∈ y)").unwrap();
    assert_eq!(th.parse_rel(&all.to_string()).unwrap(), all);
    // C27 + C30
    let refl = th.parse_rel("x ∈ y ⇒ x ∈ y").unwrap();
    let t = generalize(&taut(&th, &refl).unwrap(), &x).unwrap();
    let s = spec(&t, &th.parse_term("τu(u ∈ u)").unwrap()).unwrap();
    check(&s);
    // C29
    let c = c29(&th, &x, &r).unwrap();
    check(&c);
    // ∃-введение и ∃-удаление: (∃x)(x ∈ y ∧ x ∈ z) ⇒ (∃x)(x ∈ y)
    let both = th.parse_rel("x ∈ y ∧ x ∈ z").unwrap();
    let t = assume(&th, &both.exists(&x), |_t, h| {
        exists_elim(&h, &x, &both, |_t2, hb| {
            let l = and_elim_l(&hb)?;
            exists_intro(&r.abstract_over(&x), &Term::letter(&x), &l)
        })
    })
    .unwrap();
    assert_eq!(
        t.relation().to_string(),
        "(∃x)(x ∈ y ∧ x ∈ z) ⇒ (∃x)(x ∈ y)"
    );
    check(&t);
}

#[test]
fn equality_theorems() {
    let th = set_th();
    let t = th.parse_term("τu(u ∈ v)").unwrap();
    let r = eq_refl(&th, &t).unwrap();
    assert_eq!(
        r.relation(),
        &th.parse_rel("τu(u ∈ v) = τu(u ∈ v)").unwrap()
    );
    check(&r);
    let h = th.parse_rel("a = b").unwrap();
    let s = assume(&th, &h, |_t, hab| eq_symm(&hab)).unwrap();
    assert_eq!(s.relation(), &th.parse_rel("a = b ⇒ b = a").unwrap());
    check(&s);
}

#[test]
fn constants_block_generalization() {
    let (eps, eq) = set_signs();
    let th = Theory::build("T")
        .sign(&eps)
        .egalitarian(&eq)
        .axiom_str("a ∈ b")
        .unwrap()
        .done()
        .unwrap();
    let ax = Theorem::axiom_n(&th, 0).unwrap();
    assert!(generalize(&ax, &Letter::new("a")).is_err());
    assert!(ax.subst(&Letter::new("a"), &Term::var("c")).is_err());
    // C2: в теории (c|a)T это можно
    let t2 = ax.subst_c2(&Letter::new("a"), &Term::var("c")).unwrap();
    assert_eq!(t2.relation(), &th.parse_rel("c ∈ b").unwrap());
    check(&t2);
}

#[test]
fn inheritance_and_models() {
    let eq = SpecialSign::relational("=", 2).infix();
    let m = SpecialSign::substantive("m", 2);
    let unit = Theory::build("Единица")
        .sign(&m)
        .egalitarian(&eq)
        .axiom_str("(∀x)(m(e, x) = x)")
        .unwrap()
        .axiom_str("(∀x)(m(x, e) = x)")
        .unwrap()
        .done()
        .unwrap();
    // (∀y)((∀x)(m(y, x) = x) ⇒ y = e)
    let y = Letter::new("y");
    let hyp = unit.parse_rel("(∀x)(m(y, x) = x)").unwrap();
    let e = Term::var("e");
    let thm = generalize(
        &assume(&unit, &hyp, |t, h| {
            let a = spec(&h, &e)?; // m(y, e) = e
            let b = spec(&Theorem::axiom_n(t, 1)?, &Term::letter(&y))?; // m(y, e) = y
            eq_trans(&eq_symm(&b)?, &a)
        })
        .unwrap(),
        &y,
    )
    .unwrap();
    assert_eq!(
        thm.relation(),
        &unit.parse_rel("(∀y)((∀x)(m(y, x) = x) ⇒ y = e)").unwrap()
    );
    check(&thm);

    // наследование: моноид = единица + ассоциативность; теорема переносится сама
    let monoid = unit
        .extend("Моноид")
        .axiom_str("(∀x)(∀y)(∀z)(m(m(x, y), z) = m(x, m(y, z)))")
        .unwrap()
        .done()
        .unwrap();
    let lifted = thm.lift(&monoid).unwrap();
    check(&lifted);

    // модель: другая теория с единицей u
    let other = Theory::build("Другая")
        .sign(&m)
        .egalitarian(&eq)
        .axiom_str("(∀x)(m(u, x) = x)")
        .unwrap()
        .axiom_str("(∀x)(m(x, u) = x)")
        .unwrap()
        .axiom_str("u = u")
        .unwrap()
        .done()
        .unwrap();
    let subst = vec![(Letter::new("e"), Term::var("u"))];
    let proofs = Interpretation::obligations(&unit, &subst)
        .iter()
        .map(|r| Theorem::axiom(&other, r).unwrap())
        .collect();
    let model = Interpretation::new(&unit, &other, subst, proofs).unwrap();
    let applied = model.apply(&thm).unwrap();
    assert_eq!(
        applied.relation(),
        &other.parse_rel("(∀y)((∀x)(m(y, x) = x) ⇒ y = u)").unwrap()
    );
    check(&applied);
}
