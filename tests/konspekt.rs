//! Тесты языка конспектов: всё из `konspekt/*.bk` проверяется и раскрывается до атомов,
//! а неверные доказательства отвергаются с понятной ошибкой.

use bourbaki_engine::Konspekt;
use bourbaki_engine::syntax::{Style, set_style};
use std::path::Path;

const FILES: &[&str] = &[
    "konspekt/01_logic.bk",
    "konspekt/02_quant_eq.bk",
    "konspekt/03_notation.bk",
    "konspekt/04_equiv.bk",
    "konspekt/05_quant.bk",
    "konspekt/06_typed.bk",
    "konspekt/07_equality.bk",
    "konspekt/10_sets.bk",
];

fn with_logic() -> Konspekt {
    let mut k = Konspekt::with_prelude();
    let r = k.check_file(Path::new("konspekt/02_quant_eq.bk"));
    assert!(r.is_ok(), "{r}");
    k
}

/// Проверить текст и вернуть первую ошибку (или panic, если ошибок нет).
fn first_error(k: &mut Konspekt, src: &str) -> String {
    let r = k.check_str(src);
    assert!(!r.is_ok(), "ожидалась ошибка, а всё проверилось:\n{r}");
    r.errors[0].msg.clone()
}

fn ok(k: &mut Konspekt, src: &str) {
    let r = k.check_str(src);
    assert!(r.is_ok(), "{r}");
}

#[test]
fn all_files_check() {
    for f in FILES {
        let mut k = Konspekt::with_prelude();
        let r = k.check_file(Path::new(f));
        assert!(r.is_ok(), "{r}");
        assert!(r.sorry.is_empty(), "в {f} остались sorry: {:?}", r.sorry);
    }
}

/// Раскрытие новых глав. Все теоремы раскрываются (это проверялось отдельно, некоторые
/// дают сотни тысяч строк и минуты работы); в тесте только те, что раскрываются быстро.
#[test]
fn later_chapters_expand_and_verify() {
    let mut k = Konspekt::with_prelude();
    let r = k.check_file(Path::new("konspekt/10_sets.bk"));
    assert!(r.is_ok(), "{r}");
    for n in [
        "ch1.C26",
        "ch1.C28",
        "ch1.CS8_example",
        "ch1.C30_2",
        "ch1.C34",
        "ch1.C38",
        "ch1.C43",
        "ch1.C44",
        "ch1.C45",
        "ch2.ext",
        "ch2.mem_E",
        "ch2.coll_example",
        "ch2.mem_set2",
        "ch2.pair_inj",
        "ch2.mem_P",
    ] {
        let t = k.expand(n).unwrap_or_else(|e| panic!("{n}: {e}"));
        t.demonstration()
            .verify()
            .unwrap_or_else(|e| panic!("раскрытие {n} не прошло проверку: {e}"));
        assert_eq!(t.relation(), &k.theorem(n).unwrap().statement, "{n}");
    }
}

#[test]
fn every_theorem_expands_and_verifies() {
    let mut k = Konspekt::with_prelude();
    let r = k.check_file(Path::new("konspekt/03_notation.bk"));
    assert!(r.is_ok(), "{r}");
    let mut names: Vec<String> = k.theorems.keys().cloned().collect();
    names.sort();
    assert!(names.len() >= 25, "мало теорем: {names:?}");
    for n in names {
        let t = k.expand(&n).unwrap_or_else(|e| panic!("{n}: {e}"));
        let d = t.demonstration();
        d.verify()
            .unwrap_or_else(|e| panic!("раскрытие {n} не прошло проверку: {e}"));
        assert_eq!(t.relation(), &k.theorem(&n).unwrap().statement, "{n}");
    }
}

#[test]
fn user_c8_with_numbers() {
    let mut k = Konspekt::with_prelude();
    ok(
        &mut k,
        "theorem C8 {P : rel} : P ⇒ P in Logical {
   1. P ⇒ (P ∨ P)    by S2 with A := P; B := P
   2. (P ∨ P) ⇒ P    by S1 with A := P
   3. ((P ∨ P) ⇒ P) ⇒ ((P ⇒ (P ∨ P)) ⇒ (P ⇒ P))    by S4 with A := P ∨ P; B := P; C := ¬P
   4. (P ⇒ (P ∨ P)) ⇒ (P ⇒ P)    by mp 2 3
   5. P ⇒ P    by mp 1 4
}",
    );
    assert_eq!(k.expand("C8").unwrap().demonstration().len(), 5);
}

#[test]
fn numbers_and_carets_are_automatic() {
    let mut k = with_logic();
    ok(
        &mut k,
        "in Logical
theorem C8 {P : rel} : P ⇒ P {
   P ⇒ (P ∨ P)                                   by S2
   (P ∨ P) ⇒ P                                   by S1
   ((P ∨ P) ⇒ P) ⇒ ((P ⇒ (P ∨ P)) ⇒ (P ⇒ P))     by S4 with C := ¬P
   _                                             by mp 2 ^
   P ⇒ P                                         by mp 1 ^
}",
    );
    // номер, не совпадающий с настоящим, это ошибка
    let e = first_error(
        &mut k,
        "in Logical
theorem bad {P : rel} : P ⇒ P {
   1. P ⇒ P   by ch1.C8
   7. P ⇒ P   by ^
}",
    );
    assert!(e.contains("метка 7"), "{e}");
}

#[test]
fn caret_at_block_start_is_the_hypothesis() {
    let mut k = Konspekt::with_prelude();
    ok(
        &mut k,
        "in Logical
theorem t {A B : rel} : A ⇒ (A ∨ B) {
  A ⇒ (A ∨ B) by assume {
    A        by ^
    s2. A ⇒ (A ∨ B)  by S2
    A ∨ B    by mp 1 s2
  }
}",
    );
}

#[test]
fn applying_a_theorem_is_one_step() {
    let mut k = with_logic();
    ok(
        &mut k,
        "open ch1
in Logical
theorem ex1 {A B : rel} : (A ∨ B) ⇒ (A ∨ B) by C8 with A := A ∨ B
theorem ex2 {A B : rel} : (A ∨ B) ⇒ (A ∨ B) by C8
theorem ex3 {A B : rel} : (A ∨ B) ⇒ (A ∨ B) by imp_refl",
    );
}

#[test]
fn namespaces_and_aliases() {
    let mut k = with_logic();
    // без open короткое имя не видно
    let e = first_error(&mut k, "in Logical\ntheorem t {A : rel} : A ⇒ A by C8");
    assert!(e.contains("неизвестно"), "{e}");
    // полное имя видно
    ok(&mut k, "in Logical\ntheorem t1 {A : rel} : A ⇒ A by ch1.C8");
    // внутри своего пространства короткое имя видно
    ok(
        &mut k,
        "namespace ch1\nin Logical\ntheorem t2 {A : rel} : A ⇒ A by C8\nend",
    );
    assert!(k.theorem("ch1.t2").is_some());
    // два разных C8 в открытых пространствах: неоднозначно
    ok(
        &mut k,
        "namespace other\nin Logical\ntheorem C8 {A : rel} : A ⇒ A by ch1.C8\nend",
    );
    let e = first_error(
        &mut k,
        "open ch1\nopen other\nin Logical\ntheorem t3 {A : rel} : A ⇒ A by C8",
    );
    assert!(e.contains("неоднозначно"), "{e}");
    // алиас на то же самое не мешает
    ok(
        &mut k,
        "alias my_refl := ch1.C8\nin Logical\ntheorem t4 {A : rel} : A ⇒ A by my_refl",
    );
    // занятое имя
    let e = first_error(&mut k, "alias ch1.C8 := ch1.C6");
    assert!(e.contains("занято"), "{e}");
}

#[test]
fn wrong_scheme_instance_is_explained() {
    let mut k = with_logic();
    let e = first_error(
        &mut k,
        "in Logical\ntheorem bad {A B : rel} : A ⇒ (B ∨ A) by S2 with A := A; B := B",
    );
    assert!(e.contains("написано") && e.contains("получается"), "{e}");
}

#[test]
fn wrong_mp_is_explained() {
    let mut k = with_logic();
    let e = first_error(
        &mut k,
        "in Logical\ntheorem bad {A B : rel} (h1 : A) (h2 : B) : A by mp h1 h2",
    );
    assert!(e.contains("C1"), "{e}");
}

#[test]
fn last_line_must_be_the_statement() {
    let mut k = with_logic();
    let e = first_error(
        &mut k,
        "in Logical\ntheorem bad {A B : rel} : B ⇒ B {\n  A ⇒ A by ch1.C8\n}",
    );
    assert!(e.contains("не совпадает с утверждением"), "{e}");
}

#[test]
fn not_a_tautology() {
    let mut k = with_logic();
    let e = first_error(
        &mut k,
        "in Logical\ntheorem bad {A B : rel} : A ⇒ B by taut",
    );
    assert!(e.contains("не тавтология"), "{e}");
}

#[test]
fn generalization_over_constant_is_refused() {
    let mut k = with_logic();
    // x встречается в гипотезе, значит x константа теории 𝒯 + гипотеза
    let e = first_error(
        &mut k,
        "in Egalitarian\ntheorem bad (h : x = y) : (∀x)(x = y) by gen h with x",
    );
    assert!(e.contains("константа"), "{e}");
}

#[test]
fn weaker_theory_cannot_use_stronger_theorems() {
    let mut k = with_logic();
    let e = first_error(
        &mut k,
        "in Logical\ntheorem bad {T : term} : T = T by ch1.T1",
    );
    assert!(!e.is_empty());
}

#[test]
fn scheme_with_free_letter_is_not_a_scheme() {
    let mut k = Konspekt::with_prelude();
    let e = first_error(&mut k, "scheme Bad {A : rel} : A ⇒ (x = x)");
    assert!(e.contains("свободные буквы"), "{e}");
}

#[test]
fn sorry_is_tracked() {
    let mut k = with_logic();
    let r = k.check_str(
        "in Logical
theorem later {A : rel} : A ⇒ A by sorry
theorem uses {B : rel} : B ⇒ B by later",
    );
    assert!(r.is_ok(), "{r}");
    assert_eq!(r.sorry, vec!["later", "uses"]);
    assert!(k.expand("uses").is_err());
}

#[test]
fn contradiction_needs_a_pair() {
    let mut k = with_logic();
    let e = first_error(
        &mut k,
        "in Logical
theorem bad {A : rel} : A {
  A by contra g {
    ¬A by g
  }
}",
    );
    assert!(e.contains("противоречия"), "{e}");
}

#[test]
fn deduction_block_must_end_with_consequent() {
    let mut k = with_logic();
    let e = first_error(
        &mut k,
        "in Logical
theorem bad {A B : rel} : A ⇒ B {
  A ⇒ B by assume h {
    A by h
  }
}",
    );
    assert!(e.contains("C14"), "{e}");
}

#[test]
fn notation_is_one_per_file() {
    let mut k = with_logic();
    // по умолчанию инфиксно: префиксная форма ∨ запрещена
    let e = first_error(
        &mut k,
        "in Logical\ntheorem bad {A B : rel} : ∨ ¬A A by ch1.C8",
    );
    assert!(e.contains("инфиксной"), "{e}");
    // в префиксном режиме наоборот
    ok(
        &mut k,
        "#set prefix\nin Logical\ntheorem good {A : rel} : ∨ ¬ A A by ch1.C8",
    );
    let e = first_error(
        &mut k,
        "#set prefix\nin Logical\ntheorem bad2 {A : rel} : A ⇒ A by ch1.C8",
    );
    assert!(e.contains("префиксной"), "{e}");
    // режим не протекает в следующий файл: здесь снова инфиксно
    ok(
        &mut k,
        "in Logical\ntheorem good2 {A : rel} : A ⇒ A by ch1.C8",
    );
}

#[test]
fn prefix_reads_unambiguously() {
    // or A or B C = or A (or B C)
    let mut k = Konspekt::with_prelude();
    k.scope.notation = bourbaki_engine::syntax::Notation::Prefix;
    k.scope
        .signs
        .push(bourbaki_engine::SpecialSign::relational("P", 0));
    k.scope
        .signs
        .push(bourbaki_engine::SpecialSign::relational("Q", 0));
    k.scope
        .signs
        .push(bourbaki_engine::SpecialSign::relational("R", 0));
    let a = k.scope.parse_rel("or P or Q R").unwrap();
    let b = k.scope.parse_rel(r"\lor P (∨ Q R)").unwrap();
    assert_eq!(a, b);
    k.scope.notation = bourbaki_engine::syntax::Notation::Infix;
    assert_eq!(a, k.scope.parse_rel("P ∨ (Q ∨ R)").unwrap());
    assert_eq!(
        k.scope.parse_rel("P or Q or R").unwrap(),
        k.scope.parse_rel("(P ∨ Q) ∨ R").unwrap()
    );
}

#[test]
fn backslash_commands() {
    let k = Konspekt::with_prelude();
    let s = &k.scope;
    let a = s
        .parse_rel(r"\forall x \exists y (x = y \land \neg y = x \to x \eq y)")
        .unwrap();
    let b = s.parse_rel("(∀x)(∃y)(x = y ∧ ¬(y = x) ⇒ x = y)").unwrap();
    assert_eq!(a, b);
}

#[test]
fn print_styles() {
    let k = Konspekt::with_prelude();
    let r = k.scope.parse_rel("x = y ⇒ y = x").unwrap();
    set_style(Style::Prefix);
    assert_eq!(r.to_string(), "⇒ = x y = y x");
    set_style(Style::Signs);
    assert_eq!(r.to_string(), "∨ ¬ = x y = y x");
    let ex = k.scope.parse_rel("(∃x)(x = y)").unwrap();
    assert_eq!(ex.to_string(), "= τ = □ y y");
    set_style(Style::Infix);
    assert_eq!(r.to_string(), "x = y ⇒ y = x");
    assert_eq!(ex.to_string(), "(∃x)(x = y)");
}

#[test]
fn abbreviations_expand_and_fold_back() {
    let mut k = with_logic();
    ok(
        &mut k,
        "sign ∈ : rel 2 infix\nabbrev ⊂ (X Y : term) infix := (∀z)(z ∈ X ⇒ z ∈ Y)",
    );
    let a = k.scope.parse_rel("a ⊂ b").unwrap();
    let b = k.scope.parse_rel("(∀t)(t ∈ a ⇒ t ∈ b)").unwrap();
    assert_eq!(a, b, "сокращение раскрывается в то же знакосочетание");
    assert_eq!(b.to_string(), "a ⊂ b", "и печать узнаёт его обратно");
    let e = first_error(&mut k, "abbrev ⊂ (X Y : term) := X = Y");
    assert!(e.contains("занято"), "{e}");
    let e = first_error(&mut k, "sign ⊆ [in] : rel 2 infix");
    assert!(e.contains("зарезервировано"), "{e}");
}

#[test]
fn theorems_can_be_built_as_data() {
    use bourbaki_engine::konspekt::ast::*;
    let mut k = with_logic();
    let decl = TheoremDecl {
        name: "C9_data".into(),
        metas: vec![MetaDecl::rel(&["A", "B"])],
        hyps: vec![("h".into(), "B".into())],
        statement: "A ⇒ B".into(),
        theory: Some("Logical".into()),
        proof: vec![
            Line::new(
                "B ⇒ (¬A ∨ B)",
                Just::Use {
                    name: "ch1.C7".into(),
                    assigns: vec![],
                    refs: vec![],
                },
            ),
            Line::new("A ⇒ B", Just::mp("h", "^")),
        ],
        line: 0,
    };
    k.check_theorem(&decl).unwrap();
    let bad = TheoremDecl {
        name: "bad".into(),
        proof: vec![Line::new("A ⇒ B", Just::Taut)],
        ..decl
    };
    assert!(k.check_theorem(&bad).is_err());
}

#[test]
fn checking_is_fast_expansion_is_on_demand() {
    let start = std::time::Instant::now();
    let mut k = Konspekt::with_prelude();
    for f in FILES {
        let r = k.check_file(Path::new(f));
        assert!(r.is_ok(), "{r}");
    }
    let t = start.elapsed();
    assert!(
        t.as_secs_f64() < 5.0,
        "проверка всего конспекта заняла {t:?}"
    );
}

#[test]
fn no_ascii_connectives() {
    let k = Konspekt::with_prelude();
    for bad in [r"x = y \/ y = x", r"x = y /\ y = x", "x = y & y = x"] {
        assert!(k.scope.parse_rel(bad).is_err(), "{bad}");
    }
    assert!(k.scope.parse_rel(r"x = y \lor y = x").is_ok());
}

#[test]
fn formation_log_and_format() {
    let mut k = with_logic();
    let r = k.check_str(
        "namespace demo\nin Logical\n#log\n#format prefix\ntheorem p {A : rel} : ⇒ A A by ch1.C8\ntheorem q {A : rel} : A ⇒ A by ch1.C8\n#formation (∃x)(x = y)\nend",
    );
    assert!(r.is_ok(), "{r}");
    let out = r.output.join("\n");
    assert!(
        out.contains("namespace: demo") && out.contains("теория (in): base.Logical"),
        "{out}"
    );
    // #format действует только на следующую теорему
    assert!(
        out.contains("demo.p: ⇒ A A") && out.contains("demo.q: A ⇒ A"),
        "{out}"
    );
    assert!(
        out.contains("г) τ_x от 3") && out.contains("5 строк"),
        "{out}"
    );
    // и после неё снова инфиксная запись
    let e = first_error(
        &mut k,
        "in Logical\n#format prefix\ntheorem r {A : rel} : A ⇒ A by ch1.C8",
    );
    assert!(e.contains("префиксной"), "{e}");
}

fn with_sets() -> Konspekt {
    let mut k = with_logic();
    ok(
        &mut k,
        "sign ∈ : rel 2 infix\nabbrev Coll (R : rel 1) := (∃y)(∀x)(x ∈ y ⇔ R(x))\nabbrev Two (R : rel 2) := (∀x)(∀y)(R(x, y) ⇒ R(y, x))\nabbrev ExA (A R : rel 1) := (∃x)(A(x) ∧ R(x))",
    );
    k
}

#[test]
fn binder_abbreviations() {
    let k = with_sets();
    let s = &k.scope;
    let a = s.parse_rel("Coll_x(x ∈ a)").unwrap();
    // связанная буква ничего не значит
    assert_eq!(a, s.parse_rel("Coll_z(z ∈ a)").unwrap());
    assert_eq!(a, s.parse_rel("(∃y)(∀x)(x ∈ y ⇔ x ∈ a)").unwrap());
    assert_eq!(a.to_string(), "Coll_x(x ∈ a)");
    // параметр веса 0 не связывается: x в первом аргументе свободна
    let e = s.parse_rel("ExA_x(x ∈ X, x = y)").unwrap();
    assert_eq!(e, s.parse_rel("(∃z)(z ∈ X ∧ z = y)").unwrap());
    assert_eq!(e.to_string(), "ExA_x(x ∈ X, x = y)");
    let t = s.parse_rel("Two_{x,y}(x ∈ y)").unwrap();
    assert_eq!(t.to_string(), "Two_{x,y}(x ∈ y)");
    set_style(Style::Prefix);
    assert_eq!(a.to_string(), "Coll_x ∈ x a");
    set_style(Style::Infix);
    for (bad, why) in [
        ("Coll(x ∈ a)", "связывает"),
        ("Two_x(x ∈ y)", "связывает 2"),
        ("Two_{x,x}(x ∈ x)", "дважды"),
    ] {
        let e = s.parse_rel(bad).unwrap_err().0;
        assert!(e.contains(why), "{bad}: {e}");
    }
}

#[test]
fn bound_metavariables_are_inferred() {
    let mut k = with_logic();
    // R(x) := ... не написано: видно из (∃x)R(x) и (∀x)R(x)
    ok(
        &mut k,
        "open ch1\nin Egalitarian\ntheorem a : z = y ⇒ (∃x)(z = x) by S5\ntheorem b : (∀x)(x = y) ⇒ z = y by C30",
    );
    // в S6 R стоит только как R(T): подстановку надо написать
    let e = first_error(
        &mut k,
        "in Egalitarian\ntheorem c {T U : term} : T = U ⇒ (T = T ⇔ U = T) by S6",
    );
    assert!(e.contains("R(x) := ..."), "{e}");
    // найденная подстановка проверяется буквально
    let e = first_error(
        &mut k,
        "in Egalitarian\ntheorem d : z = y ⇒ (∃x)(x = z) by S5",
    );
    assert!(e.contains("S5"), "{e}");
}

#[test]
fn underscore_in_last_line_is_the_statement() {
    let mut k = with_logic();
    ok(
        &mut k,
        "in Logical\ntheorem t {A B : rel} (h : B) : A ⇒ B {\n  B ⇒ (¬A ∨ B)   by ch1.C7\n  _ by mp h ^\n}",
    );
}

const MODEL: &str = "open ch1
sign ∈ : rel 2 infix
theory G extends Egalitarian {
  signs ∈
  axiom G1 : e ∈ s
}
theory H extends Egalitarian {
  signs ∈
  axiom H1 : (∀x)(x ∈ c)
}
in G
theorem g_ex : (∃x)(x ∈ s) {
  e ∈ s                   by axiom G1
  e ∈ s ⇒ (∃x)(x ∈ s)     by S5
  (∃x)(x ∈ s)             by mp 1 2
}
theorem g_imp {A : rel} (h : A ⇒ e ∈ s) : A ⇒ (∃x)(x ∈ s) {
  e ∈ s ⇒ (∃x)(x ∈ s)     by S5
  _                       by C6 h ^
}
in H
theorem cc : c ∈ c {
  (∀x)(x ∈ c)            by axiom H1
  (∀x)(x ∈ c) ⇒ c ∈ c    by C30
  c ∈ c                  by mp 1 2
}
";

#[test]
fn models_transfer_theorems() {
    let mut k = with_logic();
    let src = format!(
        "{MODEL}model M : G -> H with e := c; s := c {{\n  G1 by cc\n}}\ntransfer g_ex via M\ntransfer g_imp via M as h_imp\ntheorem use_it : (∃x)(x ∈ c) by M.g_ex"
    );
    let r = k.check_str(&src);
    assert!(r.is_ok(), "{r}");
    assert_eq!(
        k.theorem("M.g_ex").unwrap().statement.to_string(),
        "(∃x)(x ∈ c)"
    );
    assert_eq!(
        k.theorem("h_imp").unwrap().hyps[0].1.to_string(),
        "A ⇒ c ∈ c",
        "гипотезы переносятся образом"
    );
    // раскрытие строит доказательство в H так, как в доказательстве C5
    for n in ["M.g_ex", "h_imp", "use_it"] {
        let t = k.expand(n).unwrap();
        assert_eq!(t.theory().name(), if n == "use_it" { "use_it" } else { n });
        t.demonstration().verify().unwrap();
    }
}

#[test]
fn bad_models_are_refused() {
    let base = |extra: &str| {
        let mut k = with_logic();
        let r = k.check_str(&format!("{MODEL}{extra}"));
        assert!(!r.is_ok(), "ожидалась ошибка:\n{r}");
        r.errors[0].msg.clone()
    };
    // аксиома G1 не доказана
    let e = base("model M : G -> H with e := c; s := c {\n}");
    assert!(e.contains("не доказан образ аксиомы"), "{e}");
    // доказательство не того
    let e = base("model M : G -> H with e := c; s := y {\n  G1 by cc\n}");
    assert!(
        e.contains("написано") || e.contains("получается") || e.contains("c ∈ y"),
        "{e}"
    );
    // терм содержит заменяемую букву
    let e = base("model M : G -> H with e := s; s := c {\n  G1 by cc\n}");
    assert!(e.contains("тоже заменяет"), "{e}");
    // знака ∈ нет в Egalitarian
    let e = base("model N : G -> Egalitarian {\n}");
    assert!(e.contains("знака ∈"), "{e}");
    // переносить можно только теоремы теории-источника (или слабее)
    let e = base("model M : G -> H with e := c; s := c {\n  G1 by cc\n}\ntransfer cc via M as x");
    assert!(e.contains("модель теории G"), "{e}");
}

#[test]
fn describe_names() {
    let mut k = Konspekt::with_prelude();
    let r = k.check_file(Path::new("konspekt/10_sets.bk"));
    assert!(r.is_ok(), "{r}");
    assert!(k.describe("C8").unwrap().contains("A ⇒ A"));
    assert!(
        k.describe("ch2.C51")
            .unwrap()
            .contains("Coll_x(P(x) ∧ x ∈ A)")
    );
    assert!(k.describe("S5").unwrap().starts_with("scheme S5"));
    assert!(k.describe("Coll_x").unwrap().starts_with("abbrev Coll"));
    assert!(k.describe("Set").unwrap().contains("явных аксиом 4"));
    assert!(k.describe("нет_такого").is_none());
}

#[test]
fn prelude_lives_in_base() {
    // без open base короткие имена из прелюдии не видны
    let mut k = Konspekt::new();
    let r = k.check_file(Path::new("konspekt/00_prelude.bk"));
    assert!(r.is_ok(), "{r}");
    let e = first_error(&mut k, "in Logical");
    assert!(e.contains("нет теории Logical"), "{e}");
    ok(
        &mut k,
        "in base.Logical\ntheorem t {A : rel} : A ⇒ (A ∨ A) by base.S2",
    );
    // прелюдию можно импортировать сколько угодно раз
    let mut k = Konspekt::with_prelude();
    let r = k.check_file(Path::new("konspekt/00_prelude.bk"));
    assert!(r.is_ok(), "{r}");
}

#[test]
fn fake_schemes_are_not_the_books_schemes() {
    let mut k = with_logic();
    // своя "S1" с другим образцом: taut в такой теории запрещён, хотя имена S1-S4 есть
    ok(
        &mut k,
        "namespace fake\nscheme S1 {A : rel} : A ∨ ¬A\ntheory L { schemes S1 base.S2 base.S3 base.S4 }\nend",
    );
    let e = first_error(&mut k, "in fake.L\ntheorem t {A : rel} : A ⇒ A by taut");
    assert!(e.contains("тавтологии"), "{e}");
    // и две разные схемы S1 в одной теории не уживаются
    let e = first_error(&mut k, "theory M { schemes base.S1 fake.S1 }");
    assert!(e.contains("уже есть другая схема"), "{e}");
}

#[test]
fn imports_do_not_leak_file_state() {
    // 03_notation.bk открывает ch1 и уходит в namespace sets; после импорта этого не видно
    let mut k = with_logic();
    let r = k.check_str("import \"konspekt/03_notation.bk\"\n#log");
    assert!(r.is_ok(), "{r}");
    let log = r.output.join("\n");
    assert!(
        log.contains("namespace: -") && log.contains("open: base\n"),
        "{log}"
    );
    // а объявленное там доступно под полными именами
    ok(
        &mut k,
        "in sets.Sets\ntheorem t {X : term} : X ⊂ X by sets.subset_refl",
    );
}
