//! § 1, n° 1-2 и Приложение к главе I: знакосочетания буквально.
//!
//! Знакосочетание есть последовательность знаков, где некоторые знаки, отличные от букв,
//! соединены линиями (связями). Здесь оно так и хранится: `Vec<Sign>` плюс множество пар
//! позиций. Можно написать любую строку, в том числе бессмысленную (например `∨ ∨`).
//!
//! Операции из текста:
//! * `AB` (запись рядом): [`Assembly::concat`];
//! * `(B|x)A`: [`Assembly::subst`];
//! * `τ_x(A)`: [`Assembly::tau`].
//!
//! Вопрос "является ли строка термом или соотношением" решается алгоритмом из
//! Приложения (критерии 1 и 2): [`Assembly::is_balanced`] и [`Assembly::parse`].

use crate::error::{Error, Result};
use crate::expr::{Expr, Shape, Sort};
use crate::sign::{Kind, Letter, Sign};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Assembly {
    signs: Vec<Sign>,
    /// Связи: пары позиций (i, j), i < j.
    links: BTreeSet<(usize, usize)>,
}

/// Больше этого число знаков не разворачиваем в строку (и так понятно, что строка огромна).
pub const MAX_LITERAL_LEN: u128 = 200_000;

impl Assembly {
    pub fn new(
        signs: Vec<Sign>,
        links: impl IntoIterator<Item = (usize, usize)>,
    ) -> Result<Assembly> {
        let mut set = BTreeSet::new();
        for (i, j) in links {
            let (a, b) = (i.min(j), i.max(j));
            if a == b || b >= signs.len() {
                return Err(Error(format!(
                    "связь ({i}, {j}) указывает за пределы строки или на один и тот же знак"
                )));
            }
            if signs[a].is_letter() || signs[b].is_letter() {
                return Err(Error(
                    "связями соединяются только знаки, отличные от букв".into(),
                ));
            }
            set.insert((a, b));
        }
        Ok(Assembly { signs, links: set })
    }

    pub fn empty() -> Assembly {
        Assembly {
            signs: vec![],
            links: BTreeSet::new(),
        }
    }

    pub fn sign(s: Sign) -> Assembly {
        Assembly {
            signs: vec![s],
            links: BTreeSet::new(),
        }
    }

    pub fn letter(x: &Letter) -> Assembly {
        Assembly::sign(Sign::Letter(x.clone()))
    }

    pub fn signs(&self) -> &[Sign] {
        &self.signs
    }

    pub fn links(&self) -> &BTreeSet<(usize, usize)> {
        &self.links
    }

    pub fn len(&self) -> usize {
        self.signs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.signs.is_empty()
    }

    /// Запись знакосочетаний рядом: AB, AB C, ...
    pub fn concat(parts: &[&Assembly]) -> Assembly {
        let mut signs = Vec::new();
        let mut links = BTreeSet::new();
        for p in parts {
            let off = signs.len();
            signs.extend(p.signs.iter().cloned());
            links.extend(p.links.iter().map(|(i, j)| (i + off, j + off)));
        }
        Assembly { signs, links }
    }

    pub fn contains_letter(&self, x: &Letter) -> bool {
        self.signs
            .iter()
            .any(|s| matches!(s, Sign::Letter(l) if l == x))
    }

    pub fn letters(&self) -> BTreeSet<Letter> {
        self.signs
            .iter()
            .filter_map(|s| {
                if let Sign::Letter(l) = s {
                    Some(l.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    /// (B|x)A: каждый экземпляр буквы x заменить знакосочетанием B (со всеми его связями).
    pub fn subst(&self, x: &Letter, b: &Assembly) -> Assembly {
        let mut signs = Vec::new();
        let mut links = BTreeSet::new();
        let mut pos = Vec::with_capacity(self.signs.len());
        for s in &self.signs {
            match s {
                Sign::Letter(l) if l == x => {
                    let off = signs.len();
                    pos.push(usize::MAX);
                    signs.extend(b.signs.iter().cloned());
                    links.extend(b.links.iter().map(|(i, j)| (i + off, j + off)));
                }
                _ => {
                    pos.push(signs.len());
                    signs.push(s.clone());
                }
            }
        }
        // связи никогда не касаются букв, поэтому pos[i] определено
        links.extend(self.links.iter().map(|&(i, j)| (pos[i], pos[j])));
        Assembly { signs, links }
    }

    /// τ_x(A): пишем τ слева от A, каждый экземпляр x заменяем на □ и связываем его с этим τ.
    /// Результат не содержит x.
    pub fn tau(&self, x: &Letter) -> Assembly {
        let mut signs = vec![Sign::Tau];
        let mut links: BTreeSet<(usize, usize)> =
            self.links.iter().map(|(i, j)| (i + 1, j + 1)).collect();
        for (k, s) in self.signs.iter().enumerate() {
            if matches!(s, Sign::Letter(l) if l == x) {
                links.insert((0, k + 1));
                signs.push(Sign::Box);
            } else {
                signs.push(s.clone());
            }
        }
        Assembly { signs, links }
    }

    /// Знакосочетание первого рода (§ 1, n° 3): начинается с τ или субстантивного знака
    /// или сводится к одной букве. Иначе второго рода.
    pub fn is_first_kind(&self) -> bool {
        match self.signs.first() {
            Some(Sign::Tau) => true,
            Some(Sign::Special(s)) => s.kind() == Kind::Substantive,
            Some(Sign::Letter(_)) => self.signs.len() == 1,
            _ => false,
        }
    }

    /// Приложение, n° 3-4: слово A* (A без связей) равновесно, т.е.
    /// l(A) = n(A) + 1 и l(B) ≤ n(B) для всякого истинного начального сегмента B.
    pub fn is_balanced(&self) -> bool {
        balanced_end(&self.signs, 0) == Some(self.signs.len())
    }

    /// Приложение, критерий 2: решить, является ли знакосочетание термом или соотношением,
    /// и если да, построить его дерево. Ошибка объясняет, какое условие нарушено.
    pub fn parse(&self) -> Result<(Expr, Sort)> {
        parse_rec(&self.signs, &self.links)
    }

    /// Развернуть дерево в литеральную строку Бурбаки (знаки и связи).
    pub fn from_expr(e: &Expr) -> Result<Assembly> {
        if e.len() > MAX_LITERAL_LEN {
            return Err(Error(format!(
                "знакосочетание слишком длинное, чтобы выписывать его знак за знаком: {} знаков",
                e.len()
            )));
        }
        if !e.is_closed() {
            return Err(Error("в выражении есть □ без своего τ".into()));
        }
        let mut signs = Vec::with_capacity(e.len() as usize);
        let mut links = BTreeSet::new();
        emit(e, &mut signs, &mut links, &mut Vec::new());
        Ok(Assembly { signs, links })
    }

    /// Картинка как в книге: связи рисуются линиями над строкой.
    ///
    /// ```text
    /// ┌───────┬─────┐
    /// τ ∨ ¬ ∈ □ A' ∈ □ A''
    /// ```
    pub fn render(&self) -> String {
        let toks: Vec<String> = self.signs.iter().map(|s| s.to_string()).collect();
        let mut cols = Vec::with_capacity(toks.len());
        let mut line = String::new();
        let mut col = 0usize;
        for (k, t) in toks.iter().enumerate() {
            if k > 0 {
                line.push(' ');
                col += 1;
            }
            cols.push(col);
            line.push_str(t);
            col += t.chars().count();
        }
        let width = col.max(1);
        // одна "линия" на левый конец: τ со всеми своими □
        let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        for &(i, j) in &self.links {
            groups.entry(i).or_default().push(j);
        }
        let mut spans: Vec<(usize, usize, Vec<usize>)> = groups
            .into_iter()
            .map(|(i, js)| {
                let mut drops: Vec<usize> = std::iter::once(cols[i])
                    .chain(js.iter().map(|&j| cols[j]))
                    .collect();
                drops.sort_unstable();
                (drops[0], *drops.last().unwrap(), drops)
            })
            .collect();
        if spans.is_empty() {
            return line;
        }
        // короткие линии ниже, длинные выше
        spans.sort_by_key(|(l, r, _)| r - l);
        let mut levels: Vec<Vec<(usize, usize)>> = Vec::new();
        let mut level_of = Vec::new();
        for (l, r, _) in &spans {
            let lv = (0..)
                .find(|&k| k >= levels.len() || levels[k].iter().all(|&(a, b)| b < *l || *r < a))
                .unwrap();
            if lv == levels.len() {
                levels.push(Vec::new());
            }
            levels[lv].push((*l, *r));
            level_of.push(lv);
        }
        let n = levels.len();
        let mut grid = vec![vec![' '; width]; n];
        for ((l, r, drops), &lv) in spans.iter().zip(&level_of) {
            let row = n - 1 - lv;
            for c in *l..=*r {
                grid[row][c] = '─';
            }
            for &c in drops {
                grid[row][c] = if c == *l {
                    '┌'
                } else if c == *r {
                    '┐'
                } else {
                    '┬'
                };
            }
        }
        for ((_, _, drops), &lv) in spans.iter().zip(&level_of) {
            let row = n - 1 - lv;
            for rr in row + 1..n {
                for &c in drops {
                    grid[rr][c] = match grid[rr][c] {
                        ' ' => '│',
                        '─' => '┼',
                        other => other,
                    };
                }
            }
        }
        let mut out = String::new();
        for row in grid {
            let s: String = row.into_iter().collect();
            out.push_str(s.trim_end());
            out.push('\n');
        }
        out.push_str(&line);
        out
    }
}

impl fmt::Display for Assembly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (k, s) in self.signs.iter().enumerate() {
            if k > 0 {
                f.write_str(" ")?;
            }
            write!(f, "{s}")?;
        }
        Ok(())
    }
}

/// Конец равновесного сегмента, начинающегося с позиции `start` (Приложение, лемма 1).
/// Счётчик `need` = 1 + n(B) - l(B) для уже прочитанного начала B.
fn balanced_end(signs: &[Sign], start: usize) -> Option<usize> {
    let mut need: i64 = 1;
    let mut i = start;
    while i < signs.len() {
        need += signs[i].weight() as i64 - 1;
        i += 1;
        if need == 0 {
            return Some(i);
        }
    }
    None
}

fn show(signs: &[Sign]) -> String {
    signs
        .iter()
        .map(|s| s.to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

fn parse_rec(signs: &[Sign], links: &BTreeSet<(usize, usize)>) -> Result<(Expr, Sort)> {
    if signs.is_empty() {
        return Err(Error(
            "пустое знакосочетание не терм и не соотношение".into(),
        ));
    }
    if balanced_end(signs, 0) != Some(signs.len()) {
        return Err(Error(format!(
            "знакосочетание \"{}\" не равновесно (Приложение, критерий 1)",
            show(signs)
        )));
    }
    for &(i, j) in links {
        if signs[i].is_letter() || signs[j].is_letter() {
            return Err(Error(format!(
                "в \"{}\" связь присоединена к букве",
                show(signs)
            )));
        }
    }
    match &signs[0] {
        Sign::Letter(l) => Ok((Expr::letter(l.clone()), Sort::Term)),
        Sign::Box => Err(Error(format!(
            "\"{}\" начинается с □, не связанного ни с каким τ",
            show(signs)
        ))),
        Sign::Tau => {
            // A = τB; антецедент: B, где □, связанные с начальным τ, заменены буквой x
            let x = Letter::new("x")
                .fresh(|l| signs.iter().any(|s| matches!(s, Sign::Letter(m) if m == l)));
            let mut body: Vec<Sign> = signs[1..].to_vec();
            let mut rest = BTreeSet::new();
            for &(i, j) in links {
                if i == 0 {
                    if signs[j] != Sign::Box {
                        return Err(Error(format!(
                            "в \"{}\" начальный τ связан не с □",
                            show(signs)
                        )));
                    }
                    body[j - 1] = Sign::Letter(x.clone());
                } else {
                    rest.insert((i - 1, j - 1));
                }
            }
            let (r, sort) = parse_rec(&body, &rest)?;
            if sort != Sort::Relation {
                return Err(Error(format!(
                    "антецедент τ в \"{}\" должен быть соотношением",
                    show(signs)
                )));
            }
            Ok((Expr::tau(x.clone(), r.abstract_letter(&x)), Sort::Term))
        }
        f => {
            if links.iter().any(|&(i, _)| i == 0) {
                return Err(Error(format!(
                    "в \"{}\" начальный знак {f} связан с чем-то",
                    show(signs)
                )));
            }
            let p = f.weight();
            let mut segs = Vec::with_capacity(p);
            let mut start = 1;
            for _ in 0..p {
                let end = balanced_end(signs, start).ok_or_else(|| {
                    Error(format!(
                        "\"{}\": не хватает антецедентов для {f}",
                        show(signs)
                    ))
                })?;
                segs.push((start, end));
                start = end;
            }
            if start != signs.len() {
                return Err(Error(format!(
                    "\"{}\": лишние знаки после антецедентов {f}",
                    show(signs)
                )));
            }
            let mut seg_links = vec![BTreeSet::new(); p];
            for &(i, j) in links {
                let si = segs.iter().position(|&(a, b)| a <= i && i < b).unwrap();
                let sj = segs.iter().position(|&(a, b)| a <= j && j < b).unwrap();
                if si != sj {
                    return Err(Error(format!(
                        "\"{}\" не вполне равновесно: связь соединяет разные антецеденты",
                        show(signs)
                    )));
                }
                let off = segs[si].0;
                seg_links[si].insert((i - off, j - off));
            }
            let mut subs = Vec::with_capacity(p);
            for (k, &(a, b)) in segs.iter().enumerate() {
                subs.push(parse_rec(&signs[a..b], &seg_links[k])?);
            }
            let need = |want: Sort, what: &str| -> Result<()> {
                if subs.iter().all(|(_, s)| *s == want) {
                    Ok(())
                } else {
                    Err(Error(format!(
                        "\"{}\": после {f} должны стоять {what}",
                        show(signs)
                    )))
                }
            };
            match f {
                Sign::Not => {
                    need(Sort::Relation, "соотношения")?;
                    Ok((Expr::not(subs[0].0.clone()), Sort::Relation))
                }
                Sign::Or => {
                    need(Sort::Relation, "соотношения")?;
                    Ok((
                        Expr::or(subs[0].0.clone(), subs[1].0.clone()),
                        Sort::Relation,
                    ))
                }
                Sign::Special(s) => {
                    need(Sort::Term, "термы")?;
                    let sort = match s.kind() {
                        Kind::Relational => Sort::Relation,
                        Kind::Substantive => Sort::Term,
                    };
                    Ok((
                        Expr::special(s.clone(), subs.into_iter().map(|(e, _)| e).collect()),
                        sort,
                    ))
                }
                _ => unreachable!(),
            }
        }
    }
}

fn emit(
    e: &Expr,
    signs: &mut Vec<Sign>,
    links: &mut BTreeSet<(usize, usize)>,
    binders: &mut Vec<usize>,
) {
    match e.shape() {
        Shape::Letter(l) => signs.push(Sign::Letter(l.clone())),
        Shape::Bx(k) => {
            let pos = signs.len();
            signs.push(Sign::Box);
            let t = binders[binders.len() - 1 - *k as usize];
            links.insert((t, pos));
        }
        Shape::Not(a) => {
            signs.push(Sign::Not);
            emit(a, signs, links, binders);
        }
        Shape::Or(a, b) => {
            signs.push(Sign::Or);
            emit(a, signs, links, binders);
            emit(b, signs, links, binders);
        }
        Shape::Tau(_, b) => {
            binders.push(signs.len());
            signs.push(Sign::Tau);
            emit(b, signs, links, binders);
            binders.pop();
        }
        Shape::Special(s, args) => {
            signs.push(Sign::Special(s.clone()));
            for a in args {
                emit(a, signs, links, binders);
            }
        }
    }
}
