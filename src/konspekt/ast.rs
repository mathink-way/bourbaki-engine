//! Конспект как данные.
//!
//! Текст `.bk` разбирается в эти структуры, а проверка работает только с ними.
//! Поэтому доказательство можно собрать и прямо на Rust (формулы остаются строками
//! и разбираются при проверке, в контексте теоремы):
//!
//! ```
//! use bourbaki_engine::konspekt::ast::*;
//! let c8 = TheoremDecl {
//!     name: "C8".into(),
//!     metas: vec![MetaDecl::rel(&["A"])],
//!     hyps: vec![],
//!     statement: "A ⇒ A".into(),
//!     theory: Some("Logical".into()),
//!     proof: vec![
//!         Line::new("A ⇒ (A ∨ A)", Just::scheme("S2", &[("A", "A"), ("B", "A")])),
//!         Line::new("(A ∨ A) ⇒ A", Just::scheme("S1", &[("A", "A")])),
//!         Line::new("((A ∨ A) ⇒ A) ⇒ ((A ⇒ (A ∨ A)) ⇒ (A ⇒ A))",
//!                   Just::scheme("S4", &[("A", "A ∨ A"), ("B", "A"), ("C", "¬A")])),
//!         Line::new("(A ⇒ (A ∨ A)) ⇒ (A ⇒ A)", Just::mp("2", "^")),
//!         Line::new("A ⇒ A", Just::mp("1", "^")),
//!     ],
//!     line: 0,
//! };
//! let mut k = bourbaki_engine::Konspekt::with_prelude();
//! k.check_theorem(&c8).unwrap();
//! ```

use crate::sign::Kind;
use crate::syntax::Notation;

/// Объявление метапеременных: `{A B : rel}`, `{R : rel 1}`, `{T : term}`.
/// Метапеременная веса n это специальный знак веса n (R{x} у Бурбаки есть R веса 1).
#[derive(Clone, Debug, PartialEq)]
pub struct MetaDecl {
    pub names: Vec<String>,
    pub kind: Kind,
    pub weight: usize,
}

impl MetaDecl {
    pub fn rel(names: &[&str]) -> MetaDecl {
        MetaDecl {
            names: names.iter().map(|s| s.to_string()).collect(),
            kind: Kind::Relational,
            weight: 0,
        }
    }
    pub fn term(names: &[&str]) -> MetaDecl {
        MetaDecl {
            names: names.iter().map(|s| s.to_string()).collect(),
            kind: Kind::Substantive,
            weight: 0,
        }
    }
}

/// Параметр правила: `A := P ∨ P` или `R(x) := x ∈ y`.
#[derive(Clone, Debug, PartialEq)]
pub struct Assign {
    pub name: String,
    /// Выделенные буквы (для метапеременной веса > 0).
    pub letters: Vec<String>,
    pub value: String,
}

/// Обоснование строки доказательства (то, что после `by`).
///
/// Ссылки на строки: номер строки в блоке (`3`), метка (`h1`), `^` (предыдущая строка),
/// `^^` (две назад) и т.д.
#[derive(Clone, Debug, PartialEq)]
pub enum Just {
    /// Схема, теорема (тогда `refs` это строки с её гипотезами) или ссылка на строку.
    /// `by S4 with A := B; B := C`, `by C6 1 ^`, `by h`.
    Use {
        name: String,
        assigns: Vec<Assign>,
        refs: Vec<String>,
    },
    /// Силлогизм C1: `by mp 2 3`.
    MP(String, String),
    /// Явная аксиома теории: `by axiom` или `by axiom A1`.
    Axiom(Option<String>),
    /// C14, метод вспомогательной гипотезы: строка `A ⇒ B`, блок доказывает B в 𝒯 + A.
    Assume(Option<String>),
    /// C15, приведение к абсурду: строка `A`, блок в 𝒯 + (не A) содержит B и не B.
    Contra(Option<String>),
    /// C27: из R получить (∀x)R, x не константа. `by gen ^ with x`.
    Generalize { letter: String, from: String },
    /// C3: из R получить (T|x)R, x не константа. `by subst ^ with x := T`.
    Subst {
        letter: String,
        term: String,
        from: String,
    },
    /// Упр. 7: тавтология (проверка таблицей истинности). `by taut a b`: строка следует
    /// из строк a, b по тавтологии, то есть a ⇒ (b ⇒ строка) тавтология (затем C1 дважды).
    Taut(Vec<String>),
    /// Цепочка равенств (теоремы 2 и 3 § 5): `by chain a b c`, строка T = U получается из
    /// равенств a, b, c, соединяющих T с U (каждое можно читать в любую сторону).
    Chain(Vec<String>),
    /// `by sorry`: пропуск, как в Lean.
    Sorry,
}

impl Just {
    pub fn scheme(name: &str, assigns: &[(&str, &str)]) -> Just {
        Just::Use {
            name: name.into(),
            assigns: assigns
                .iter()
                .map(|(n, v)| Assign {
                    name: n.to_string(),
                    letters: vec![],
                    value: v.to_string(),
                })
                .collect(),
            refs: vec![],
        }
    }
    pub fn mp(a: &str, b: &str) -> Just {
        Just::MP(a.into(), b.into())
    }
}

/// Строка доказательства: `[метка.] формула by обоснование` и, для C14/C15, вложенный блок.
/// Строки нумеруются автоматически (1, 2, ... внутри блока); метка нужна только для имени.
#[derive(Clone, Debug, PartialEq)]
pub struct Line {
    pub label: Option<String>,
    /// `None`, если вместо формулы написано `_` (тогда её выводит проверка).
    pub formula: Option<String>,
    pub just: Just,
    pub block: Vec<Line>,
    /// Номер строки в файле (0, если строка собрана в коде).
    pub line: usize,
}

impl Line {
    pub fn new(formula: &str, just: Just) -> Line {
        Line {
            label: None,
            formula: Some(formula.into()),
            just,
            block: vec![],
            line: 0,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct TheoremDecl {
    pub name: String,
    pub metas: Vec<MetaDecl>,
    /// Гипотезы: (метка, формула).
    pub hyps: Vec<(String, String)>,
    pub statement: String,
    pub theory: Option<String>,
    pub proof: Vec<Line>,
    pub line: usize,
}

#[derive(Clone, Debug, PartialEq)]
pub struct TheoryDecl {
    pub name: String,
    pub extends: Option<String>,
    pub signs: Vec<String>,
    pub schemes: Vec<String>,
    /// (имя, формула).
    pub axioms: Vec<(String, String)>,
    pub line: usize,
}

/// Модель (C5): `model M : Source -> Target with a := T; b := U { A1 by ... }`.
/// Вместо констант a, b теории Source подставляются термы T, U теории Target;
/// для каждой явной аксиомы Source строка `ИМЯ by обоснование` доказывает
/// её образ в Target.
#[derive(Clone, Debug, PartialEq)]
pub struct ModelDecl {
    pub name: String,
    pub source: String,
    pub target: String,
    /// (буква, терм).
    pub subst: Vec<(String, String)>,
    /// (имя аксиомы, обоснование, строка файла).
    pub obligations: Vec<(String, Just, usize)>,
    pub line: usize,
}

/// Элемент файла.
#[derive(Clone, Debug, PartialEq)]
pub enum Item {
    Import(String),
    /// `namespace A.B`: следующие имена получают приставку `A.B.`
    Namespace(String),
    /// `end`: закрыть последний `namespace`.
    End,
    /// `open A`: короткие имена из `A` доступны без приставки.
    Open(String),
    /// `alias имя := полное.имя`
    Alias {
        name: String,
        target: String,
    },
    Sign {
        name: String,
        aliases: Vec<String>,
        kind: Kind,
        weight: usize,
        infix: bool,
    },
    Abbrev {
        name: String,
        aliases: Vec<String>,
        params: Vec<MetaDecl>,
        body: String,
        infix: bool,
        /// `nofold`: при печати не сворачивать.
        nofold: bool,
    },
    Scheme {
        name: String,
        metas: Vec<MetaDecl>,
        pattern: String,
    },
    Theory(TheoryDecl),
    /// `in Теория`: теория по умолчанию.
    In(String),
    /// `#set infix` / `#set prefix`.
    Set(Notation),
    Theorem(TheoremDecl),
    /// `#show φ`: напечатать формулу.
    Show(String),
    /// `#signs φ`: нарисовать знакосочетание со связями.
    Signs(String),
    /// `#print имя`: напечатать формулировку теоремы.
    Print(String),
    /// `#expand имя` (размер раскрытия) и `#unfold имя` (выписать все строки).
    Expand {
        name: String,
        full: bool,
    },
    Model(ModelDecl),
    /// `transfer THM via M [as NEW]`: перенести теорему моделью (C5).
    Transfer {
        theorem: String,
        model: String,
        name: Option<String>,
    },
    /// `#formation φ`: формативная конструкция (§ 1, n° 4) по строкам с CF-обоснованием.
    Formation(String),
    /// `#log`: где мы (пространство имён, теория, `open`, запись, сколько доказано).
    Log,
    /// `#format infix|prefix`: запись только для следующей теоремы.
    Format(Notation),
}

/// Элемент с номером строки в файле.
#[derive(Clone, Debug, PartialEq)]
pub struct Located {
    pub line: usize,
    pub item: Item,
}
