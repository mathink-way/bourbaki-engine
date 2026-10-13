//! # bourbaki-engine
//!
//! Глава I "Теории множеств" Н. Бурбаки ("Описание формальной математики") как программа.
//!
//! Модули следуют параграфам книги:
//!
//! | модуль        | что                                                                 |
//! |---------------|---------------------------------------------------------------------|
//! | [`sign`]      | § 1, n° 1: знаки □, τ, ∨, ¬, буквы, специальные знаки               |
//! | [`assembly`]  | § 1, n° 1-2, Приложение: знакосочетания со связями, (B\|x)A, τ_x(A)  |
//! | [`formative`] | § 1, n° 3-4: термы, соотношения, формативные конструкции, CF1-CF12   |
//! | [`theory`]    | § 2, n° 1, 4: теории, схемы S1-S7, наследование                     |
//! | [`proof`]     | § 2, n° 2-4: доказательства, теоремы, C1-C5 (модели)                 |
//! | [`logic`]     | § 3: логические теории, C6-C22, методы доказательства, тавтологии    |
//! | [`quant`]     | § 4: кванторы, C27-C31                                               |
//! | [`equality`]  | § 5: равенство, теоремы 1-3                                          |
//! | [`syntax`]    | сокращающие символы: печать и чтение                                 |
//! | [`konspekt`]  | язык конспектов `.bk`: проверка доказательств по строкам             |
//! | [`book`]      | сам конспект главы I (проверенный)                                   |

// `not`, `or`, `and` названы как у Бурбаки, а не как операторы Rust.
#![allow(
    clippy::should_implement_trait,
    clippy::collapsible_if,
    clippy::needless_range_loop
)]

pub mod assembly;
pub mod book;
pub mod equality;
pub mod error;
pub mod expr;
pub mod formative;
pub mod konspekt;
pub mod logic;
pub mod proof;
pub mod quant;
pub mod sign;
pub mod syntax;
pub mod theory;

pub use assembly::Assembly;
pub use error::{Error, Result};
pub use expr::{Expr, Sort};
pub use formative::{Abs, Relation, Term};
pub use konspekt::{Konspekt, Report};
pub use proof::{Demonstration, Interpretation, Theorem};
pub use sign::{Kind, Letter, Sign, SpecialSign};
pub use theory::{Arg, Scheme, Th, Theory};
