//! C5 в языке: модели и перенос теорем (§ 2, n° 4).
//!
//! ```text
//! model M : Source -> Target with a := T; b := U {
//!   A1 by ...        -- образ аксимы A1 (a, b заменены на T, U) есть теорема Target
//!   A2 by ...
//! }
//! transfer thm via M as thm'
//! ```
//!
//! По C5, если образы всех явных аксиом Source теоремы Target (и знаки, схемы Source
//! есть в Target), то образ всякой теоремы Source теорема Target. Быстрая проверка
//! проверяет только обязательства; раскрытие строит доказательство в Target так же, как
//! у Бурбаки: подстановки C2 во всё доказательство и замена аксиом их доказательствами (C4).

use super::ast::*;
use super::check::{self, CheckedTheorem, Origin};
use super::{CheckError, Konspekt, Names};
use crate::formative::{Relation, Term};
use crate::proof::{Interpretation, Theorem};
use crate::sign::Letter;
use crate::theory::Th;
use std::cell::RefCell;
use std::rc::Rc;

/// Проверенная модель.
pub struct Model {
    pub name: String,
    pub source: Th,
    pub target: Th,
    /// Вместо буквы подставляется терм (одновременно; термы этих букв не содержат).
    pub subst: Vec<(Letter, Term)>,
    /// (имя аксиомы, её образ в Target, обоснование, строка файла).
    pub obligations: Vec<(String, Relation, Just, usize)>,
    /// Какое-то обязательство доказано через `sorry`.
    pub sorry: bool,
    names: Names,
    expanded: RefCell<Option<Vec<Theorem>>>,
}

impl Model {
    /// Образ соотношения: буквы заменены термами.
    pub fn image(&self, r: &Relation) -> Relation {
        image(&self.subst, r)
    }

    /// Раскрытые доказательства обязательств (теоремы Target).
    fn obligation_proofs(&self, k: &Konspekt) -> Result<Vec<Theorem>, CheckError> {
        if let Some(v) = self.expanded.borrow().as_ref() {
            return Ok(v.clone());
        }
        let mut out = Vec::new();
        for (_, r, just, line) in &self.obligations {
            let (thm, _) = check::check_fact(k, &self.target, &self.names, r, just, *line, true)?;
            out.push(thm.expect("в режиме раскрытия теорема строится"));
        }
        *self.expanded.borrow_mut() = Some(out.clone());
        Ok(out)
    }

    /// Раскрыть перенесённую теорему `me` (образ `source`) до явных аксиом, схем и C1.
    pub(super) fn expand_transfer(
        &self,
        k: &Konspekt,
        source: &CheckedTheorem,
        me: &CheckedTheorem,
    ) -> Result<Theorem, CheckError> {
        let err = |m: String| CheckError {
            file: k.file_name(),
            line: me.decl.line,
            msg: m,
        };
        let full = source.expand(k)?;
        // теория источника: Source + метапеременные + гипотезы теоремы
        let mut b = self
            .source
            .extend(&format!("{}@{}", source.name, self.source.name()));
        for m in &source.metas {
            b = b.sign(m);
        }
        for (_, h) in &source.hyps {
            b = b.axiom(h);
        }
        let from = b.done().map_err(|e| err(e.0))?;
        let full = full.lift(&from).map_err(|e| err(e.0))?;
        let mut proofs = self.obligation_proofs(k)?;
        for (_, h) in &me.hyps {
            proofs.push(Theorem::axiom(&me.lemma_th, h).map_err(|e| err(e.0))?);
        }
        let i = Interpretation::new(&from, &me.lemma_th, self.subst.clone(), proofs)
            .map_err(|e| err(e.0))?;
        i.apply(&full).map_err(|e| err(e.0))
    }
}

fn image(subst: &[(Letter, Term)], r: &Relation) -> Relation {
    let pairs: Vec<(Letter, crate::expr::Expr)> = subst
        .iter()
        .map(|(x, t)| (x.clone(), t.expr().clone()))
        .collect();
    Relation(r.expr().subst_many(&pairs))
}

impl Konspekt {
    pub(super) fn model(&mut self, d: &ModelDecl) -> Result<(), CheckError> {
        let e = |k: &Konspekt, line: usize, m: String| k.error(line, m);
        let full = self.full(&d.name);
        if self.exists(&full) {
            return Err(e(self, d.line, format!("имя {full} уже занято")));
        }
        let source = self
            .find_theory(&d.source)
            .map_err(|m| e(self, d.line, m))?;
        let target = self
            .find_theory(&d.target)
            .map_err(|m| e(self, d.line, m))?;
        for s in source.signs() {
            if !target.signs().contains(s) {
                return Err(e(
                    self,
                    d.line,
                    format!(
                        "C5: знака {s} теории {} нет в {}",
                        source.name(),
                        target.name()
                    ),
                ));
            }
        }
        for s in source.schemes() {
            if !target.has_scheme(s.name()) {
                return Err(e(
                    self,
                    d.line,
                    format!(
                        "C5: схемы {} теории {} нет в {}",
                        s.name(),
                        source.name(),
                        target.name()
                    ),
                ));
            }
        }
        let mut subst: Vec<(Letter, Term)> = Vec::new();
        for (x, t) in &d.subst {
            if !Letter::is_valid(x) {
                return Err(e(self, d.line, format!("\"{x}\" не буква")));
            }
            let x = Letter::new(x);
            if subst.iter().any(|(y, _)| *y == x) {
                return Err(e(self, d.line, format!("буква {x} заменяется дважды")));
            }
            let t = self
                .scope
                .parse_term(t)
                .map_err(|er| e(self, d.line, er.0))?;
            target
                .check_signs(t.expr())
                .map_err(|er| e(self, d.line, er.0))?;
            subst.push((x, t));
        }
        // одновременная подстановка совпадает с последовательной C2, если термы
        // не содержат заменяемых букв
        for (_, t) in &subst {
            if let Some((y, _)) = subst.iter().find(|(y, _)| t.expr().contains_letter(y)) {
                return Err(e(
                    self,
                    d.line,
                    format!(
                        "терм {t} содержит букву {y}, которую модель тоже заменяет; переименуйте букву"
                    ),
                ));
            }
        }
        let names = self.names();
        let mut obligations = Vec::new();
        let mut sorry = false;
        for (name, just, line) in &d.obligations {
            let ax = self
                .find_axiom_in(&names, name)
                .map_err(|m| e(self, *line, m))?;
            if !source.has_axiom(&ax) {
                return Err(e(
                    self,
                    *line,
                    format!("{name} не явная аксиома теории {}", source.name()),
                ));
            }
            let img = image(&subst, &ax);
            let (_, s) = check::check_fact(self, &target, &names, &img, just, *line, false)?;
            sorry |= s;
            obligations.push((name.clone(), img, just.clone(), *line));
        }
        for a in source.axioms() {
            let img = image(&subst, a);
            if !obligations.iter().any(|(_, r, _, _)| *r == img) {
                return Err(e(
                    self,
                    d.line,
                    format!(
                        "C5: не доказан образ аксиомы {a} теории {}: {img}",
                        source.name()
                    ),
                ));
            }
        }
        self.models.insert(
            full.clone(),
            Rc::new(Model {
                name: full,
                source,
                target,
                subst,
                obligations,
                sorry,
                names,
                expanded: RefCell::new(None),
            }),
        );
        Ok(())
    }

    pub(super) fn find_model(&self, name: &str) -> Result<Rc<Model>, String> {
        self.resolve(name, &|c| self.models.contains_key(c))?
            .map(|n| self.models[&n].clone())
            .ok_or_else(|| format!("нет модели {name}"))
    }

    /// `transfer THM via M [as NEW]`.
    pub(super) fn transfer(
        &mut self,
        theorem: &str,
        model: &str,
        name: &Option<String>,
        line: usize,
    ) -> Result<Rc<CheckedTheorem>, CheckError> {
        let e = |k: &Konspekt, m: String| k.error(line, m);
        let src = self
            .find_theorem(theorem)
            .map_err(|m| e(self, m))?
            .ok_or_else(|| e(self, format!("нет теоремы {theorem}")))?;
        let m = self.find_model(model).map_err(|er| e(self, er))?;
        if !src.base.is_literally_weaker(&m.source) {
            return Err(e(
                self,
                format!(
                    "теорема {} доказана в теории {}, а модель {} это модель теории {}",
                    src.name,
                    src.base.name(),
                    m.name,
                    m.source.name()
                ),
            ));
        }
        // по умолчанию M.имя: образ теоремы живёт "внутри" модели
        let short = name.clone().unwrap_or_else(|| {
            let m_short = m.name.rsplit('.').next().unwrap_or(&m.name);
            let t_short = src.name.rsplit('.').next().unwrap_or(&src.name);
            format!("{m_short}.{t_short}")
        });
        let full = self.full(&short);
        if self.exists(&full) {
            return Err(e(
                self,
                format!("имя {full} уже занято (дайте другое: transfer ... as НОВОЕ_ИМЯ)"),
            ));
        }
        let hyps: Vec<(String, Relation)> = src
            .hyps
            .iter()
            .map(|(l, h)| (l.clone(), m.image(h)))
            .collect();
        let statement = m.image(&src.statement);
        let mut b = m.target.extend(&full);
        for s in &src.metas {
            b = b.sign(s);
        }
        for (_, h) in &hyps {
            b = b.axiom(h);
        }
        let lemma_th = b.done().map_err(|er| e(self, er.0))?;
        lemma_th
            .check_signs(statement.expr())
            .map_err(|er| e(self, er.0))?;
        let decl = TheoremDecl {
            name: full.clone(),
            metas: src.decl.metas.clone(),
            hyps: vec![],
            statement: String::new(),
            theory: Some(m.target.name().to_string()),
            proof: vec![],
            line,
        };
        let t = Rc::new(CheckedTheorem {
            name: full.clone(),
            base: m.target.clone(),
            metas: src.metas.clone(),
            hyps,
            statement,
            lemma_th,
            sorry: src.sorry || m.sorry,
            decl,
            names: self.names(),
            expanded: RefCell::new(None),
            origin: Origin::Transfer {
                source: src.clone(),
                model: m.clone(),
            },
        });
        self.theorems.insert(full, t.clone());
        Ok(t)
    }
}
