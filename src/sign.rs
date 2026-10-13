//! § 1, n° 1. Знаки теории.
//!
//! 1° логические знаки □, τ, ∨, ¬ (у Бурбаки отрицание пишется ⌉);
//! 2° буквы: латинские буквы со штрихами A, A', x'', ...;
//! 3° специальные знаки, зависящие от теории (в теории множеств: =, ∈, ⊃).
//!
//! Каждому знаку приписан вес: □ и буквы имеют вес 0, τ и ¬ вес 1, ∨ вес 2,
//! у специального знака вес задаётся вместе с теорией (§ 1, n° 3).

use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

/// Буква. Латинская буква, затем (для удобства) цифры или `_`, затем штрихи: `x`, `A'`, `x1''`.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Letter(Rc<str>);

impl Letter {
    pub fn new(name: &str) -> Letter {
        assert!(
            Letter::is_valid(name),
            "\"{name}\" не годится как буква: нужна латинская буква, потом цифры и штрихи"
        );
        Letter(name.into())
    }

    pub fn is_valid(name: &str) -> bool {
        let mut chars = name.chars();
        match chars.next() {
            Some(c) if c.is_ascii_alphabetic() => {}
            _ => return false,
        }
        let core = name[1..].trim_end_matches('\'');
        core.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
    }

    pub fn name(&self) -> &str {
        &self.0
    }

    /// Та же буква со штрихом: x -> x'.
    pub fn primed(&self) -> Letter {
        Letter(format!("{}'", self.0).into())
    }

    /// Первая из букв `self, self', self'', ...`, которая не занята.
    /// Так выбирается новая буква, которой ещё нет в знакосочетании (§ 1, n° 1).
    pub fn fresh(&self, mut taken: impl FnMut(&Letter) -> bool) -> Letter {
        let mut l = self.clone();
        while taken(&l) {
            l = l.primed();
        }
        l
    }
}

impl From<&str> for Letter {
    fn from(s: &str) -> Letter {
        Letter::new(s)
    }
}

impl From<&Letter> for Letter {
    fn from(l: &Letter) -> Letter {
        l.clone()
    }
}

impl fmt::Display for Letter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl fmt::Debug for Letter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// Реляционный или субстантивный специальный знак (§ 1, n° 3).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Kind {
    /// Даёт соотношения: `∈`, `=`.
    Relational,
    /// Даёт термы: `⊃` (пара) в теории множеств.
    Substantive,
}

/// Как печатать знак веса 2: `∈xy` (как у Бурбаки) или `x ∈ y`. На тождественность не влияет.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Fixity {
    Prefix,
    Infix,
}

struct SignData {
    name: String,
    weight: usize,
    kind: Kind,
    fixity: Fixity,
}

/// Специальный знак теории: имя, вес, реляционный/субстантивный.
#[derive(Clone)]
pub struct SpecialSign(Rc<SignData>);

impl SpecialSign {
    fn mk(name: &str, weight: usize, kind: Kind, fixity: Fixity) -> SpecialSign {
        assert!(!name.is_empty(), "у знака должно быть имя");
        assert!(
            !name
                .chars()
                .any(|c| c.is_whitespace() || "()|,.".contains(c)),
            "имя знака \"{name}\" не должно содержать пробелов и знаков ( ) | , ."
        );
        SpecialSign(Rc::new(SignData {
            name: name.to_string(),
            weight,
            kind,
            fixity,
        }))
    }

    pub fn relational(name: &str, weight: usize) -> SpecialSign {
        SpecialSign::mk(name, weight, Kind::Relational, Fixity::Prefix)
    }

    pub fn substantive(name: &str, weight: usize) -> SpecialSign {
        SpecialSign::mk(name, weight, Kind::Substantive, Fixity::Prefix)
    }

    /// Печатать (и разбирать) знак веса 2 между аргументами: `x ∈ y`.
    pub fn infix(self) -> SpecialSign {
        assert_eq!(self.0.weight, 2, "инфиксным может быть только знак веса 2");
        SpecialSign::mk(&self.0.name, 2, self.0.kind, Fixity::Infix)
    }

    pub fn name(&self) -> &str {
        &self.0.name
    }
    pub fn weight(&self) -> usize {
        self.0.weight
    }
    pub fn kind(&self) -> Kind {
        self.0.kind
    }
    pub fn fixity(&self) -> Fixity {
        self.0.fixity
    }
    pub fn is_relational(&self) -> bool {
        self.0.kind == Kind::Relational
    }
}

impl PartialEq for SpecialSign {
    fn eq(&self, o: &SpecialSign) -> bool {
        Rc::ptr_eq(&self.0, &o.0)
            || (self.0.name == o.0.name && self.0.weight == o.0.weight && self.0.kind == o.0.kind)
    }
}
impl Eq for SpecialSign {}

impl Hash for SpecialSign {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.0.name.hash(h);
        self.0.weight.hash(h);
        self.0.kind.hash(h);
    }
}

impl fmt::Display for SpecialSign {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0.name)
    }
}

impl fmt::Debug for SpecialSign {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let k = match self.0.kind {
            Kind::Relational => "рел.",
            Kind::Substantive => "суб.",
        };
        write!(f, "{} ({k}, вес {})", self.0.name, self.0.weight)
    }
}

/// Один знак знакосочетания.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Sign {
    Box,
    Tau,
    Or,
    Not,
    Letter(Letter),
    Special(SpecialSign),
}

impl Sign {
    /// Вес знака (Приложение, n° 4): n(□) = 0, n(τ) = n(¬) = 1, n(∨) = 2, n(буквы) = 0.
    pub fn weight(&self) -> usize {
        match self {
            Sign::Box | Sign::Letter(_) => 0,
            Sign::Tau | Sign::Not => 1,
            Sign::Or => 2,
            Sign::Special(s) => s.weight(),
        }
    }

    pub fn is_letter(&self) -> bool {
        matches!(self, Sign::Letter(_))
    }
}

impl fmt::Display for Sign {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sign::Box => f.write_str("□"),
            Sign::Tau => f.write_str("τ"),
            Sign::Or => f.write_str("∨"),
            Sign::Not => f.write_str("¬"),
            Sign::Letter(l) => write!(f, "{l}"),
            Sign::Special(s) => write!(f, "{s}"),
        }
    }
}
