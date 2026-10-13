//! Перебор всех двузначных "логик" (раньше это был отдельный питон-скрипт).
//!
//! Модель задаётся таблицами ¬ и ∨ на {0, 1}, A ⇒ B есть (¬A) ∨ B, 1 значит "истинно".
//! Требуем: S1-S4 истинны при всех значениях, а C1 (силлогизм) сохраняет истинность.
//! Утверждение: из 4 · 16 = 64 таблиц годится ровно одна, классическая.
//!
//! Это направление "корректность в двузначной модели определяет таблицы".
//! Обратное направление (всякая тавтология выводится из S1-S4, упр. 7) проверяется
//! в `tautologies_are_theorems` ниже и в `logic::taut`.

use bourbaki_engine::logic::{is_tautology, taut};
use bourbaki_engine::{Konspekt, Theory};
use std::path::Path;

#[derive(Clone, Copy, Debug, PartialEq)]
struct Model {
    neg: [u8; 2],
    or: [[u8; 2]; 2],
}

impl Model {
    fn imp(&self, a: u8, b: u8) -> u8 {
        self.or[self.neg[a as usize] as usize][b as usize]
    }
    fn or(&self, a: u8, b: u8) -> u8 {
        self.or[a as usize][b as usize]
    }
    fn valid(&self) -> bool {
        let bits = [0u8, 1];
        let s1 = bits.iter().all(|&a| self.imp(self.or(a, a), a) == 1);
        let s2 = bits
            .iter()
            .all(|&a| bits.iter().all(|&b| self.imp(a, self.or(a, b)) == 1));
        let s3 = bits.iter().all(|&a| {
            bits.iter()
                .all(|&b| self.imp(self.or(a, b), self.or(b, a)) == 1)
        });
        let s4 = bits.iter().all(|&a| {
            bits.iter().all(|&b| {
                bits.iter()
                    .all(|&c| self.imp(self.imp(a, b), self.imp(self.or(c, a), self.or(c, b))) == 1)
            })
        });
        let mp = bits.iter().all(|&a| {
            bits.iter()
                .all(|&b| !(a == 1 && self.imp(a, b) == 1) || b == 1)
        });
        s1 && s2 && s3 && s4 && mp
    }
    fn trivial(&self) -> bool {
        let mut vals = std::collections::HashSet::new();
        for a in 0..2u8 {
            vals.insert(a);
            vals.insert(self.neg[a as usize]);
            for b in 0..2u8 {
                vals.insert(self.or(a, b));
            }
        }
        vals.len() == 1
    }
}

fn all_models() -> Vec<Model> {
    let mut out = Vec::new();
    for n in 0..4u8 {
        for o in 0..16u8 {
            out.push(Model {
                neg: [n & 1, n >> 1 & 1],
                or: [[o & 1, o >> 1 & 1], [o >> 2 & 1, o >> 3 & 1]],
            });
        }
    }
    out
}

#[test]
fn only_classical_logic_survives() {
    let valid: Vec<Model> = all_models()
        .into_iter()
        .filter(|m| m.valid() && !m.trivial())
        .collect();
    assert_eq!(valid.len(), 1, "{valid:?}");
    assert_eq!(
        valid[0],
        Model {
            neg: [1, 0],
            or: [[0, 1], [1, 1]]
        }
    );
}

#[test]
fn tautologies_are_theorems() {
    // упр. 7: тавтология выводится из S1-S4 (строится доказательство и проверяется)
    let th = Theory::build("L")
        .sign(&bourbaki_engine::SpecialSign::relational("P", 0))
        .sign(&bourbaki_engine::SpecialSign::relational("Q", 0))
        .logical()
        .done()
        .unwrap();
    for src in [
        "P ∨ ¬P",
        "((P ⇒ Q) ⇒ P) ⇒ P",
        "¬(P ∧ ¬P)",
        "(P ⇒ Q) ∨ (Q ⇒ P)",
    ] {
        let r = th.parse_rel(src).unwrap();
        let t = taut(&th, &r).unwrap();
        t.demonstration().verify().unwrap();
    }
}

#[test]
fn every_logic_theorem_of_the_konspekt_is_a_tautology() {
    // корректность: всё доказанное в § 3 (без гипотез) истинно в классической модели
    let mut k = Konspekt::with_prelude();
    let r = k.check_file(Path::new("konspekt/01_logic.bk"));
    assert!(r.is_ok(), "{r}");
    let mut n = 0;
    for t in k.theorems.values() {
        if t.hyps.is_empty() && t.base.name() == "base.Logical" {
            assert!(is_tautology(&t.statement), "{} не тавтология", t.name);
            n += 1;
        }
    }
    assert!(n >= 10);
}
