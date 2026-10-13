//! Внутреннее представление термов и соотношений.
//!
//! Бурбаки работает со строками знаков, где от τ к □ проведены связи. Строки быстро
//! разрастаются: `(∃x)R` по определению есть `(τ_x(R)|x)R`, и R копируется целиком.
//! Поэтому внутри движка знакосочетание хранится деревом с общими поддеревьями,
//! а связь "□ соединён с τ" кодируется числом: □ помнит, какой по счёту τ снаружи
//! (индекс де Брёйна). Это та же самая информация, что и линия над строкой.
//!
//! Важное следствие: тождественность знакосочетаний (литеральное совпадение строк со
//! связями) здесь просто структурное равенство деревьев. Например τ_x(A) и τ_x'(A')
//! из CS3 дают одно и то же дерево, буква x в нём уже не участвует.
//!
//! Литеральная строка всегда восстанавливается: [`crate::assembly::Assembly::from_expr`].

use crate::sign::{Kind, Letter, SpecialSign};
use std::collections::BTreeSet;
use std::hash::{BuildHasherDefault, Hash, Hasher};

/// Быстрый хеш для адресов и коротких ключей (как FxHash в rustc): стандартный SipHash
/// защищён от атак, здесь это не нужно, а времени он съедал больше всего остального.
#[derive(Default, Clone, Copy)]
pub struct FxHasher {
    hash: u64,
}

impl FxHasher {
    fn add(&mut self, w: u64) {
        self.hash = (self.hash.rotate_left(5) ^ w).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
}

impl Hasher for FxHasher {
    fn write(&mut self, bytes: &[u8]) {
        for chunk in bytes.chunks(8) {
            let mut b = [0u8; 8];
            b[..chunk.len()].copy_from_slice(chunk);
            self.add(u64::from_le_bytes(b));
        }
    }
    fn write_u8(&mut self, i: u8) {
        self.add(i as u64);
    }
    fn write_u32(&mut self, i: u32) {
        self.add(i as u64);
    }
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }
    fn finish(&self) -> u64 {
        self.hash
    }
}

type FxBuild = BuildHasherDefault<FxHasher>;
type HashMap<K, V> = std::collections::HashMap<K, V, FxBuild>;
type HashSet<K> = std::collections::HashSet<K, FxBuild>;
type DefaultHasher = FxHasher;
use std::rc::Rc;

/// Терм или соотношение (§ 1, n° 3).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Sort {
    Term,
    Relation,
}

/// Вид вершины дерева. Каждая вершина соответствует одному знаку строки Бурбаки.
#[derive(Clone)]
pub enum Shape {
    Letter(Letter),
    /// □, связанный с k-м снаружи τ (k = 0: ближайший).
    Bx(u32),
    Not(Expr),
    Or(Expr, Expr),
    /// τ, связанный со всеми □ внутри тела, указывающими на него.
    /// Буква-подсказка нужна только для печати и в тождественности не участвует.
    Tau(Letter, Expr),
    Special(SpecialSign, Vec<Expr>),
}

pub struct Node {
    shape: Shape,
    hash: u64,
    /// Число знаков в литеральной строке (может быть астрономическим).
    len: u128,
    /// 1 + максимальный "висячий" индекс □; 0 означает: висячих □ нет.
    loose: u32,
    /// Грубый отпечаток множества букв (64-битный фильтр Блума).
    mask: u64,
    /// То же для специальных знаков.
    smask: u64,
}

#[derive(Clone)]
pub struct Expr(Rc<Node>);

fn sign_bit(s: &SpecialSign) -> u64 {
    let mut h = DefaultHasher::default();
    s.hash(&mut h);
    1u64 << (h.finish() % 64)
}

pub(crate) fn letter_bit(l: &Letter) -> u64 {
    let mut h = DefaultHasher::default();
    l.hash(&mut h);
    1u64 << (h.finish() % 64)
}

type Memo = HashMap<(*const Node, u32), Expr>;

/// Ключ вершины для общего хранилища: вид вершины и адреса детей (дети уже из хранилища).
#[derive(PartialEq, Eq, Hash)]
enum Key {
    Letter(Letter),
    Bx(u32),
    Not(usize),
    Or(usize, usize),
    Tau(Letter, usize),
    Special(SpecialSign, Vec<usize>),
}

thread_local! {
    /// Общее хранилище вершин: одинаковые знакосочетания строятся один раз и дальше
    /// совпадают как указатели. Тогда сравнения и обходы с памятью работают по-настоящему
    /// на дереве с общими частями, а не на копиях одного и того же.
    static INTERN: std::cell::RefCell<(HashMap<Key, std::rc::Weak<Node>>, usize)> =
        std::cell::RefCell::new((HashMap::default(), 0));
}

/// Память `fill_holes`: адреса (тела, аргументов) → (они сами, чтобы адреса жили, и результат).
type FillCache = HashMap<Vec<usize>, (Vec<Expr>, Expr)>;

thread_local! {
    static FILL_CACHE: std::cell::RefCell<FillCache> =
        std::cell::RefCell::new(HashMap::default());
}

fn intern_key(shape: &Shape) -> Key {
    let p = |e: &Expr| Rc::as_ptr(&e.0) as usize;
    match shape {
        Shape::Letter(l) => Key::Letter(l.clone()),
        Shape::Bx(k) => Key::Bx(*k),
        Shape::Not(a) => Key::Not(p(a)),
        Shape::Or(a, b) => Key::Or(p(a), p(b)),
        Shape::Tau(h, b) => Key::Tau(h.clone(), p(b)),
        Shape::Special(s, args) => Key::Special(s.clone(), args.iter().map(p).collect()),
    }
}

impl Expr {
    fn mk(shape: Shape) -> Expr {
        let key = intern_key(&shape);
        if let Some(e) = INTERN.with(|t| t.borrow().0.get(&key).and_then(|w| w.upgrade())) {
            return Expr(e);
        }
        let e = Expr::mk_new(shape);
        INTERN.with(|t| {
            let mut t = t.borrow_mut();
            t.0.insert(key, Rc::downgrade(&e.0));
            t.1 += 1;
            // время от времени выбросить записи об уже удалённых вершинах
            if t.1 > 1 << 16 && t.1 > t.0.len() {
                t.0.retain(|_, w| w.strong_count() > 0);
                t.1 = 0;
            }
        });
        e
    }

    fn mk_new(shape: Shape) -> Expr {
        let mut h = DefaultHasher::default();
        let (len, loose, mask, smask) = match &shape {
            Shape::Letter(l) => {
                0u8.hash(&mut h);
                l.hash(&mut h);
                (1u128, 0u32, letter_bit(l), 0u64)
            }
            Shape::Bx(k) => {
                1u8.hash(&mut h);
                k.hash(&mut h);
                (1, k + 1, 0, 0)
            }
            Shape::Not(a) => {
                2u8.hash(&mut h);
                a.0.hash.hash(&mut h);
                (a.0.len.saturating_add(1), a.0.loose, a.0.mask, a.0.smask)
            }
            Shape::Or(a, b) => {
                3u8.hash(&mut h);
                a.0.hash.hash(&mut h);
                b.0.hash.hash(&mut h);
                (
                    a.0.len.saturating_add(b.0.len).saturating_add(1),
                    a.0.loose.max(b.0.loose),
                    a.0.mask | b.0.mask,
                    a.0.smask | b.0.smask,
                )
            }
            Shape::Tau(_, b) => {
                4u8.hash(&mut h);
                b.0.hash.hash(&mut h);
                (
                    b.0.len.saturating_add(1),
                    b.0.loose.saturating_sub(1),
                    b.0.mask,
                    b.0.smask,
                )
            }
            Shape::Special(s, args) => {
                5u8.hash(&mut h);
                s.hash(&mut h);
                let (mut len, mut loose, mut mask, mut smask) = (1u128, 0u32, 0u64, sign_bit(s));
                for a in args {
                    a.0.hash.hash(&mut h);
                    len = len.saturating_add(a.0.len);
                    loose = loose.max(a.0.loose);
                    mask |= a.0.mask;
                    smask |= a.0.smask;
                }
                (len, loose, mask, smask)
            }
        };
        Expr(Rc::new(Node {
            shape,
            hash: h.finish(),
            len,
            loose,
            mask,
            smask,
        }))
    }

    pub fn letter(l: Letter) -> Expr {
        Expr::mk(Shape::Letter(l))
    }
    pub fn bx(k: u32) -> Expr {
        Expr::mk(Shape::Bx(k))
    }
    pub fn not(a: Expr) -> Expr {
        Expr::mk(Shape::Not(a))
    }
    pub fn or(a: Expr, b: Expr) -> Expr {
        Expr::mk(Shape::Or(a, b))
    }
    pub fn tau(hint: Letter, body: Expr) -> Expr {
        Expr::mk(Shape::Tau(hint, body))
    }
    pub fn special(s: SpecialSign, args: Vec<Expr>) -> Expr {
        Expr::mk(Shape::Special(s, args))
    }

    pub fn shape(&self) -> &Shape {
        &self.0.shape
    }

    /// Длина литеральной строки знаков (насыщается на u128::MAX).
    pub fn len(&self) -> u128 {
        self.0.len
    }

    pub fn is_empty(&self) -> bool {
        false
    }

    /// Число различных вершин дерева с общими частями.
    pub fn dag_size(&self) -> usize {
        let mut seen = HashSet::default();
        let mut stack = vec![self.clone()];
        while let Some(e) = stack.pop() {
            if !seen.insert(Rc::as_ptr(&e.0)) {
                continue;
            }
            match e.shape() {
                Shape::Letter(_) | Shape::Bx(_) => {}
                Shape::Not(a) | Shape::Tau(_, a) => stack.push(a.clone()),
                Shape::Or(a, b) => {
                    stack.push(a.clone());
                    stack.push(b.clone());
                }
                Shape::Special(_, args) => stack.extend(args.iter().cloned()),
            }
        }
        seen.len()
    }

    pub(crate) fn hash_value(&self) -> u64 {
        self.0.hash
    }

    /// Нет □ без своего τ.
    pub fn is_closed(&self) -> bool {
        self.0.loose == 0
    }

    pub fn ptr_eq(&self, o: &Expr) -> bool {
        Rc::ptr_eq(&self.0, &o.0)
    }

    /// Встречается ли буква x.
    pub fn contains_letter(&self, x: &Letter) -> bool {
        let bit = letter_bit(x);
        let mut seen = HashSet::default();
        self.contains_rec(x, bit, &mut seen)
    }

    fn contains_rec(&self, x: &Letter, bit: u64, seen: &mut HashSet<*const Node>) -> bool {
        if self.0.mask & bit == 0 || !seen.insert(Rc::as_ptr(&self.0)) {
            return false;
        }
        match self.shape() {
            Shape::Letter(l) => l == x,
            Shape::Bx(_) => false,
            Shape::Not(a) | Shape::Tau(_, a) => a.contains_rec(x, bit, seen),
            Shape::Or(a, b) => a.contains_rec(x, bit, seen) || b.contains_rec(x, bit, seen),
            Shape::Special(_, args) => args.iter().any(|a| a.contains_rec(x, bit, seen)),
        }
    }

    /// Все буквы, встречающиеся в знакосочетании.
    pub fn letters(&self) -> BTreeSet<Letter> {
        let mut out = BTreeSet::new();
        let mut seen = HashSet::default();
        self.letters_rec(&mut out, &mut seen);
        out
    }

    fn letters_rec(&self, out: &mut BTreeSet<Letter>, seen: &mut HashSet<*const Node>) {
        if !seen.insert(Rc::as_ptr(&self.0)) {
            return;
        }
        match self.shape() {
            Shape::Letter(l) => {
                out.insert(l.clone());
            }
            Shape::Bx(_) => {}
            Shape::Not(a) | Shape::Tau(_, a) => a.letters_rec(out, seen),
            Shape::Or(a, b) => {
                a.letters_rec(out, seen);
                b.letters_rec(out, seen);
            }
            Shape::Special(_, args) => args.iter().for_each(|a| a.letters_rec(out, seen)),
        }
    }

    /// Все специальные знаки, встречающиеся в знакосочетании.
    pub fn special_signs(&self) -> Vec<SpecialSign> {
        let mut out: Vec<SpecialSign> = Vec::new();
        let mut seen = HashSet::default();
        let mut stack = vec![self.clone()];
        while let Some(e) = stack.pop() {
            if !seen.insert(Rc::as_ptr(&e.0)) {
                continue;
            }
            match e.shape() {
                Shape::Letter(_) | Shape::Bx(_) => {}
                Shape::Not(a) | Shape::Tau(_, a) => stack.push(a.clone()),
                Shape::Or(a, b) => {
                    stack.push(a.clone());
                    stack.push(b.clone());
                }
                Shape::Special(s, args) => {
                    if !out.contains(s) {
                        out.push(s.clone());
                    }
                    stack.extend(args.iter().cloned());
                }
            }
        }
        out
    }

    /// Общий обход "перестрой дерево": `f` либо сразу даёт ответ для вершины, либо `None`
    /// (тогда спускаемся к детям). `depth` = число τ, под которыми мы находимся.
    fn transform(
        &self,
        depth: u32,
        memo: &mut Memo,
        f: &mut dyn FnMut(&Expr, u32) -> Option<Expr>,
    ) -> Expr {
        if let Some(r) = f(self, depth) {
            return r;
        }
        let key = (Rc::as_ptr(&self.0), depth);
        if let Some(r) = memo.get(&key) {
            return r.clone();
        }
        let r = match self.shape() {
            Shape::Letter(_) | Shape::Bx(_) => self.clone(),
            Shape::Not(a) => {
                let a2 = a.transform(depth, memo, f);
                if a2.ptr_eq(a) {
                    self.clone()
                } else {
                    Expr::not(a2)
                }
            }
            Shape::Or(a, b) => {
                let a2 = a.transform(depth, memo, f);
                let b2 = b.transform(depth, memo, f);
                if a2.ptr_eq(a) && b2.ptr_eq(b) {
                    self.clone()
                } else {
                    Expr::or(a2, b2)
                }
            }
            Shape::Tau(h, b) => {
                let b2 = b.transform(depth + 1, memo, f);
                if b2.ptr_eq(b) {
                    self.clone()
                } else {
                    Expr::tau(h.clone(), b2)
                }
            }
            Shape::Special(s, args) => {
                let new: Vec<Expr> = args.iter().map(|a| a.transform(depth, memo, f)).collect();
                if new.iter().zip(args).all(|(n, o)| n.ptr_eq(o)) {
                    self.clone()
                } else {
                    Expr::special(s.clone(), new)
                }
            }
        };
        memo.insert(key, r.clone());
        r
    }

    /// (T|x)A: каждое вхождение буквы x заменить на T (§ 1, n° 1).
    pub fn subst(&self, x: &Letter, t: &Expr) -> Expr {
        assert!(
            t.is_closed(),
            "подставлять можно только знакосочетание без висячих □"
        );
        let bit = letter_bit(x);
        let mut f = |e: &Expr, _d: u32| -> Option<Expr> {
            if e.0.mask & bit == 0 {
                return Some(e.clone());
            }
            match e.shape() {
                Shape::Letter(l) => Some(if l == x { t.clone() } else { e.clone() }),
                _ => None,
            }
        };
        self.transform(0, &mut HashMap::default(), &mut f)
    }

    /// Одновременная подстановка A(x₁,...,xₙ)[T₁,...,Tₙ] (обозначение Бурбаки `A{x,y}[B,C]`).
    pub fn subst_many(&self, pairs: &[(Letter, Expr)]) -> Expr {
        let mask = pairs.iter().fold(0u64, |m, (x, _)| m | letter_bit(x));
        let mut f = |e: &Expr, _d: u32| -> Option<Expr> {
            if e.0.mask & mask == 0 {
                return Some(e.clone());
            }
            match e.shape() {
                Shape::Letter(l) => Some(
                    pairs
                        .iter()
                        .find(|(x, _)| x == l)
                        .map(|(_, t)| t.clone())
                        .unwrap_or_else(|| e.clone()),
                ),
                _ => None,
            }
        };
        self.transform(0, &mut HashMap::default(), &mut f)
    }

    /// Заменить букву x на □, связанный с (будущим) внешним τ. Тело для τ_x(A).
    pub fn abstract_letter(&self, x: &Letter) -> Expr {
        let bit = letter_bit(x);
        let mut f = |e: &Expr, d: u32| -> Option<Expr> {
            if e.0.mask & bit == 0 {
                return Some(e.clone());
            }
            match e.shape() {
                Shape::Letter(l) => Some(if l == x { Expr::bx(d) } else { e.clone() }),
                _ => None,
            }
        };
        self.transform(0, &mut HashMap::default(), &mut f)
    }

    /// Обратная операция: все □ внешнего τ заменить на знакосочетание t.
    /// Так получается (T|x)A из тела A с выделенной буквой x.
    pub fn instantiate(&self, t: &Expr) -> Expr {
        assert!(
            t.is_closed(),
            "подставлять можно только знакосочетание без висячих □"
        );
        let mut f = |e: &Expr, d: u32| -> Option<Expr> {
            if e.0.loose <= d {
                return Some(e.clone());
            }
            match e.shape() {
                Shape::Bx(k) => Some(if *k == d { t.clone() } else { e.clone() }),
                _ => None,
            }
        };
        self.transform(0, &mut HashMap::default(), &mut f)
    }

    /// Сдвинуть висячие □ на `k` (нужно, когда знакосочетание с висячими □ переносится
    /// под `k` дополнительных τ).
    pub fn shift(&self, k: u32) -> Expr {
        if k == 0 || self.is_closed() {
            return self.clone();
        }
        let mut f = |e: &Expr, d: u32| -> Option<Expr> {
            if e.0.loose <= d {
                return Some(e.clone());
            }
            match e.shape() {
                Shape::Bx(m) => Some(Expr::bx(m + k)),
                _ => None,
            }
        };
        self.transform(0, &mut HashMap::default(), &mut f)
    }

    /// Тело с n "дырами": буква `xs[i]` заменяется на дыру номер i.
    /// Это R{x₁,...,xₙ} у Бурбаки: соотношение с выделенными буквами.
    pub fn abstract_letters(&self, xs: &[Letter]) -> Expr {
        let mask = xs.iter().fold(0u64, |m, x| m | letter_bit(x));
        let mut f = |e: &Expr, d: u32| -> Option<Expr> {
            if e.0.mask & mask == 0 {
                return Some(e.clone());
            }
            match e.shape() {
                Shape::Letter(l) => Some(match xs.iter().position(|x| x == l) {
                    Some(i) => Expr::bx(d + i as u32),
                    None => e.clone(),
                }),
                _ => None,
            }
        };
        self.transform(0, &mut HashMap::default(), &mut f)
    }

    /// Заполнить дыры тела знакосочетаниями `args` (они могут содержать висячие □,
    /// которые относятся к τ снаружи места вставки; при вставке под τ тела они сдвигаются).
    pub fn fill_holes(&self, args: &[Expr]) -> Expr {
        if self.is_closed() || args.is_empty() {
            return self.clone();
        }
        // одно и то же тело с одними и теми же аргументами (а вершины общие, так что это
        // просто одни и те же указатели) заполняется один раз
        let key: Vec<usize> = std::iter::once(self)
            .chain(args)
            .map(|e| Rc::as_ptr(&e.0) as usize)
            .collect();
        if let Some(r) = FILL_CACHE.with(|c| c.borrow().get(&key).map(|(_, r)| r.clone())) {
            return r;
        }
        let r = self.fill_holes_uncached(args);
        FILL_CACHE.with(|c| {
            let mut c = c.borrow_mut();
            if c.len() > 100_000 {
                c.clear();
            }
            // вместе с результатом храним сами тело и аргументы: пока запись жива, их
            // адреса не достанутся другим вершинам
            let mut keep = vec![self.clone()];
            keep.extend(args.iter().cloned());
            c.insert(key, (keep, r.clone()));
        });
        r
    }

    fn fill_holes_uncached(&self, args: &[Expr]) -> Expr {
        let n = args.len() as u32;
        // сдвинутые аргументы для каждой глубины считаются один раз
        let mut shifted: HashMap<(usize, u32), Expr> = HashMap::default();
        let mut f = |e: &Expr, d: u32| -> Option<Expr> {
            if e.0.loose <= d {
                return Some(e.clone());
            }
            match e.shape() {
                Shape::Bx(m) if *m >= d && *m < d + n => {
                    let i = (*m - d) as usize;
                    Some(
                        shifted
                            .entry((i, d))
                            .or_insert_with(|| args[i].shift(d))
                            .clone(),
                    )
                }
                Shape::Bx(_) => Some(e.clone()),
                _ => None,
            }
        };
        self.transform(0, &mut HashMap::default(), &mut f)
    }

    /// Обратное к `fill_holes`: каждое вхождение `xs[i]` стало дырой i. `None`, если
    /// после этого остались висячие □ (тело зависело бы от букв, связанных снаружи).
    pub fn abstract_exprs(&self, xs: &[Expr]) -> Option<Expr> {
        const FAR: u32 = 1 << 30;
        let mut f = |e: &Expr, d: u32| -> Option<Expr> {
            xs.iter()
                .position(|x| *e == x.shift(d))
                .map(|i| Expr::bx(d + FAR + i as u32))
        };
        let marked = self.transform(0, &mut HashMap::default(), &mut f);
        marked.remap_loose(&|m| m.checked_sub(FAR))
    }

    /// Подстановка вместо специальных знаков: каждое вхождение `s T₁...Tₙ` заменяется
    /// телом с дырами, заполненными (уже обработанными) T₁...Tₙ.
    ///
    /// Так применяются схемы-образцы и теоремы с метапеременными: метапеременная A
    /// есть знак веса 0, R{x} знак веса 1. Подстановка одновременная: в подставленное
    /// повторно не заглядываем.
    pub fn replace_signs(&self, map: &[(SpecialSign, Expr)]) -> Expr {
        if map.is_empty() {
            return self.clone();
        }
        fn go(
            e: &Expr,
            map: &[(SpecialSign, Expr)],
            memo: &mut HashMap<*const Node, Expr>,
        ) -> Expr {
            if let Some(r) = memo.get(&Rc::as_ptr(&e.0)) {
                return r.clone();
            }
            let r = match e.shape() {
                Shape::Letter(_) | Shape::Bx(_) => e.clone(),
                Shape::Not(a) => {
                    let a2 = go(a, map, memo);
                    if a2.ptr_eq(a) {
                        e.clone()
                    } else {
                        Expr::not(a2)
                    }
                }
                Shape::Or(a, b) => {
                    let a2 = go(a, map, memo);
                    let b2 = go(b, map, memo);
                    if a2.ptr_eq(a) && b2.ptr_eq(b) {
                        e.clone()
                    } else {
                        Expr::or(a2, b2)
                    }
                }
                Shape::Tau(h, b) => {
                    let b2 = go(b, map, memo);
                    if b2.ptr_eq(b) {
                        e.clone()
                    } else {
                        Expr::tau(h.clone(), b2)
                    }
                }
                Shape::Special(s, args) => {
                    let new: Vec<Expr> = args.iter().map(|a| go(a, map, memo)).collect();
                    if let Some((_, body)) = map.iter().find(|(t, _)| t == s) {
                        body.fill_holes(&new)
                    } else if new.iter().zip(args).all(|(n, o)| n.ptr_eq(o)) {
                        e.clone()
                    } else {
                        Expr::special(s.clone(), new)
                    }
                }
            };
            memo.insert(Rc::as_ptr(&e.0), r.clone());
            r
        }
        go(self, map, &mut HashMap::default())
    }

    /// Встречается ли знак.
    pub fn contains_sign(&self, s: &SpecialSign) -> bool {
        self.special_signs().contains(s)
    }

    /// Переименовать висячие □: □ с номером m (считая от корня) становится □ с номером
    /// `f(m)`. Если `f` вернула `None` хоть раз, результат `None`.
    pub fn remap_loose(&self, f: &dyn Fn(u32) -> Option<u32>) -> Option<Expr> {
        if self.is_closed() {
            return Some(self.clone());
        }
        let failed = std::cell::Cell::new(false);
        let mut g = |e: &Expr, d: u32| -> Option<Expr> {
            if e.0.loose <= d {
                return Some(e.clone());
            }
            match e.shape() {
                Shape::Bx(m) => Some(match f(m - d) {
                    Some(n) => Expr::bx(n + d),
                    None => {
                        failed.set(true);
                        e.clone()
                    }
                }),
                _ => None,
            }
        };
        let r = self.transform(0, &mut HashMap::default(), &mut g);
        (!failed.get()).then_some(r)
    }

    /// Сопоставление с образцом: найти знакосочетания вместо знаков `metas`, при которых
    /// `self` (образец) превращается в `target` (замкнутое). Найденное дописывается в `got`.
    ///
    /// Метапеременная веса 0 (A) сопоставляется с замкнутым подвыражением. Метапеременная
    /// веса k (R) в образце обычно стоит как R(□ᵢ₁, ..., □ᵢₖ), где □ связаны кванторами
    /// образца и различны (образец Миллера, например R(x) в (∃x)R(x)); тогда тело R это
    /// подвыражение цели, в котором эти □ стали дырами. Прочие вхождения (R(T)) проверяются
    /// после того, как R найдено в другом месте.
    pub fn match_into(
        &self,
        target: &Expr,
        metas: &[SpecialSign],
        got: &mut Vec<(SpecialSign, Expr)>,
    ) -> bool {
        Expr::match_many(&[(self.clone(), target.clone())], metas, got)
    }

    /// То же для нескольких пар (образец, цель) сразу: метапеременные общие, и догадки
    /// (см. [`Expr::match_into`]) проверяются по всем парам вместе.
    pub fn match_many(
        pairs: &[(Expr, Expr)],
        metas: &[SpecialSign],
        got: &mut Vec<(SpecialSign, Expr)>,
    ) -> bool {
        Expr::match_pairs(pairs, metas, got, true)
    }

    fn match_pairs(
        pairs: &[(Expr, Expr)],
        metas: &[SpecialSign],
        got: &mut Vec<(SpecialSign, Expr)>,
        guess: bool,
    ) -> bool {
        if pairs.iter().any(|(p, t)| !p.skeleton_fits(t, metas, 6)) {
            return false;
        }
        let mut deferred: Vec<Deferred> = Vec::new();
        let t0 = std::time::Instant::now();
        for (p, t) in pairs {
            if !p.match_rec(t, metas, got, &mut deferred, 0) {
                return false;
            }
        }
        let t1 = t0.elapsed().as_secs_f64();
        let r = solve(metas, got, deferred, guess) != Solve::Fail;
        if guess && t0.elapsed().as_secs_f64() > 0.2 && std::env::var_os("BOURBAKI_DBG").is_some() {
            let n: usize = pairs.iter().map(|(p, t)| p.dag_size() + t.dag_size()).sum();
            eprintln!(
                "match: {t1:.3} + solve {:.3}, узлов {n}",
                t0.elapsed().as_secs_f64() - t1
            );
        }
        r
    }

    /// Быстрая проверка формы на `depth` уровней вглубь: вершина с метапеременной
    /// подходит к чему угодно. Отсекает заведомо неподходящие цели до сопоставления.
    fn skeleton_fits(&self, t: &Expr, metas: &[SpecialSign], depth: u32) -> bool {
        if depth == 0 {
            return true;
        }
        match (self.shape(), t.shape()) {
            (Shape::Special(s, _), _) if metas.contains(s) => true,
            (Shape::Letter(a), Shape::Letter(b)) => a == b,
            (Shape::Bx(a), Shape::Bx(b)) => a == b,
            (Shape::Not(a), Shape::Not(b)) | (Shape::Tau(_, a), Shape::Tau(_, b)) => {
                a.skeleton_fits(b, metas, depth - 1)
            }
            (Shape::Or(a1, b1), Shape::Or(a2, b2)) => {
                a1.skeleton_fits(a2, metas, depth - 1) && b1.skeleton_fits(b2, metas, depth - 1)
            }
            (Shape::Special(s, xs), Shape::Special(u, ys)) => {
                s == u
                    && xs.len() == ys.len()
                    && xs
                        .iter()
                        .zip(ys)
                        .all(|(a, b)| a.skeleton_fits(b, metas, depth - 1))
            }
            _ => false,
        }
    }

    /// τ-подвыражения с глубиной (числом τ над ними), без повторов, не больше `limit`.
    fn pattern_taus(&self, depth: u32, out: &mut Vec<(Expr, u32)>) {
        self.taus_rec(depth, None, out, &mut HashSet::default(), 64);
    }

    /// τ-подвыражения ровно на глубине `want` (не больше 64 разных).
    fn taus_at(&self, depth: u32, want: u32) -> Vec<Expr> {
        let mut out = Vec::new();
        self.taus_rec(depth, Some(want), &mut out, &mut HashSet::default(), 64);
        // сначала τ ровно на нужной глубине, потом замкнутые τ глубже
        out.sort_by_key(|(_, d)| *d != want);
        let mut uniq: Vec<Expr> = Vec::new();
        for (t, _) in out {
            if !uniq.contains(&t) {
                uniq.push(t);
            }
        }
        uniq
    }

    fn taus_rec(
        &self,
        depth: u32,
        want: Option<u32>,
        out: &mut Vec<(Expr, u32)>,
        seen: &mut HashSet<(*const Node, u32)>,
        limit: usize,
    ) {
        // глубже нужной глубины годятся только замкнутые τ (они от глубины не зависят),
        // поэтому там глубина не различается
        let deep = want.is_some_and(|w| depth > w);
        let key = if deep { u32::MAX } else { depth };
        if out.len() >= limit || !seen.insert((Rc::as_ptr(&self.0), key)) {
            return;
        }
        match self.shape() {
            Shape::Letter(_) | Shape::Bx(_) => {}
            Shape::Tau(_, b) => {
                if want.is_none_or(|w| w == depth) || (deep && self.is_closed()) {
                    out.push((self.clone(), depth));
                }
                b.taus_rec(depth + 1, want, out, seen, limit);
            }
            Shape::Not(a) => a.taus_rec(depth, want, out, seen, limit),
            Shape::Or(a, b) => {
                a.taus_rec(depth, want, out, seen, limit);
                b.taus_rec(depth, want, out, seen, limit);
            }
            Shape::Special(_, args) => args
                .iter()
                .for_each(|a| a.taus_rec(depth, want, out, seen, limit)),
        }
    }

    fn match_rec(
        &self,
        target: &Expr,
        metas: &[SpecialSign],
        got: &mut Vec<(SpecialSign, Expr)>,
        deferred: &mut Vec<Deferred>,
        depth: u32,
    ) -> bool {
        let mask = metas.iter().fold(0, |m, s| m | sign_bit(s));
        self.match_go(
            target,
            metas,
            mask,
            got,
            deferred,
            depth,
            &mut HashSet::default(),
        )
    }

    /// `memo`: уже сопоставленные пары (образец, цель, глубина). Внутри одного обхода
    /// найденное только пополняется, поэтому повторное сопоставление той же пары ничего не
    /// даст; без памяти обход дерева с общими частями экспоненциален.
    #[allow(clippy::too_many_arguments)]
    fn match_go(
        &self,
        target: &Expr,
        metas: &[SpecialSign],
        mask: u64,
        got: &mut Vec<(SpecialSign, Expr)>,
        deferred: &mut Vec<Deferred>,
        depth: u32,
        memo: &mut HashSet<(*const Node, *const Node, u32)>,
    ) -> bool {
        // в образце нет метапеременных: остаётся буквальное сравнение (оно с памятью,
        // а обход дерева без памяти экспоненциален на вложенных кванторах)
        if self.0.smask & mask == 0 {
            return self == target;
        }
        // при depth >= loose образца ход сопоставления от depth не зависит (все □ образца
        // связаны внутри него), поэтому такие пары сливаются в одну
        let key = (
            Rc::as_ptr(&self.0),
            Rc::as_ptr(&target.0),
            depth.min(self.0.loose),
        );
        if memo.contains(&key) {
            return true;
        }
        let r = match (self.shape(), target.shape()) {
            (Shape::Special(s, args), _) if metas.contains(s) => {
                // образец Миллера: аргументы это различные □, связанные внутри образца
                let mut holes: Vec<u32> = Vec::new();
                for a in args {
                    match a.shape() {
                        Shape::Bx(j) if *j < depth && !holes.contains(j) => holes.push(*j),
                        _ => {
                            deferred.push((self.clone(), target.clone(), depth));
                            return true;
                        }
                    }
                }
                // □ цели с номером j (из holes[i]) становится дырой i
                let Some(body) =
                    target.remap_loose(&|m| holes.iter().position(|j| *j == m).map(|i| i as u32))
                else {
                    return false; // тело зависело бы от буквы, связанной в образце
                };
                match got.iter().find(|(t, _)| t == s) {
                    Some((_, v)) => *v == body,
                    None => {
                        got.push((s.clone(), body));
                        true
                    }
                }
            }
            (Shape::Letter(a), Shape::Letter(b)) => a == b,
            (Shape::Bx(a), Shape::Bx(b)) => a == b,
            (Shape::Not(a), Shape::Not(b)) => {
                a.match_go(b, metas, mask, got, deferred, depth, memo)
            }
            (Shape::Or(a1, b1), Shape::Or(a2, b2)) => {
                a1.match_go(a2, metas, mask, got, deferred, depth, memo)
                    && b1.match_go(b2, metas, mask, got, deferred, depth, memo)
            }
            (Shape::Tau(_, a), Shape::Tau(_, b)) => {
                a.match_go(b, metas, mask, got, deferred, depth + 1, memo)
            }
            (Shape::Special(s, xs), Shape::Special(t, ys)) => {
                s == t
                    && xs.len() == ys.len()
                    && xs
                        .iter()
                        .zip(ys)
                        .all(|(a, b)| a.match_go(b, metas, mask, got, deferred, depth, memo))
            }
            _ => false,
        };
        if r {
            memo.insert(key);
        }
        r
    }

    /// Все замкнутые подтермы вида τ(...) в порядке "сверху вниз, слева направо".
    pub fn closed_taus(&self, limit: usize) -> Vec<Expr> {
        let mut out = Vec::new();
        let mut seen_nodes = HashSet::default();
        let mut seen = HashSet::default();
        self.closed_taus_rec(&mut out, &mut seen_nodes, &mut seen, limit);
        out
    }

    fn closed_taus_rec(
        &self,
        out: &mut Vec<Expr>,
        nodes: &mut HashSet<*const Node>,
        seen: &mut HashSet<Expr>,
        limit: usize,
    ) {
        if out.len() >= limit || !nodes.insert(Rc::as_ptr(&self.0)) {
            return;
        }
        if let Shape::Tau(..) = self.shape() {
            if self.is_closed() && seen.insert(self.clone()) {
                out.push(self.clone());
            }
        }
        match self.shape() {
            Shape::Letter(_) | Shape::Bx(_) => {}
            Shape::Not(a) | Shape::Tau(_, a) => a.closed_taus_rec(out, nodes, seen, limit),
            Shape::Or(a, b) => {
                a.closed_taus_rec(out, nodes, seen, limit);
                b.closed_taus_rec(out, nodes, seen, limit);
            }
            Shape::Special(_, args) => args
                .iter()
                .for_each(|a| a.closed_taus_rec(out, nodes, seen, limit)),
        }
    }

    /// Все способы прочитать соотношение как (∃x)R, т.е. как (τ_x(R)|x)R (§ 4, n° 1).
    /// Возвращает пары (буква-подсказка, тело R с □ на месте x).
    pub fn exists_readings(&self) -> Vec<(Letter, Expr)> {
        let mut out = Vec::new();
        for t in self.closed_taus(64) {
            if let Shape::Tau(h, body) = t.shape() {
                if body.instantiate(&t) == *self {
                    out.push((h.clone(), body.clone()));
                }
            }
        }
        out
    }

    /// Сорт выражения по правилам формативной конструкции; `None`, если это не терм
    /// и не соотношение (например, `∨` с термом внутри).
    pub fn sort(&self) -> Option<Sort> {
        if !self.is_closed() {
            return None;
        }
        fn go(
            e: &Expr,
            depth: u32,
            memo: &mut HashMap<(*const Node, u32), Option<Sort>>,
        ) -> Option<Sort> {
            let key = (Rc::as_ptr(&e.0), depth);
            if let Some(r) = memo.get(&key) {
                return *r;
            }
            let rel = |s: Option<Sort>| s == Some(Sort::Relation);
            let r = match e.shape() {
                Shape::Letter(_) => Some(Sort::Term),
                Shape::Bx(k) => (*k < depth).then_some(Sort::Term),
                Shape::Not(a) => rel(go(a, depth, memo)).then_some(Sort::Relation),
                Shape::Or(a, b) => {
                    (rel(go(a, depth, memo)) && rel(go(b, depth, memo))).then_some(Sort::Relation)
                }
                Shape::Tau(_, b) => rel(go(b, depth + 1, memo)).then_some(Sort::Term),
                Shape::Special(s, args) => {
                    let ok = args.len() == s.weight()
                        && args.iter().all(|a| go(a, depth, memo) == Some(Sort::Term));
                    ok.then_some(match s.kind() {
                        Kind::Relational => Sort::Relation,
                        Kind::Substantive => Sort::Term,
                    })
                }
            };
            memo.insert(key, r);
            r
        }
        go(self, 0, &mut HashMap::default())
    }

    fn eq_rec(&self, o: &Expr, memo: &mut HashSet<(*const Node, *const Node)>) -> bool {
        if Rc::ptr_eq(&self.0, &o.0) {
            return true;
        }
        if self.0.hash != o.0.hash || self.0.len != o.0.len {
            return false;
        }
        let key = (Rc::as_ptr(&self.0), Rc::as_ptr(&o.0));
        if memo.contains(&key) {
            return true;
        }
        let r = match (self.shape(), o.shape()) {
            (Shape::Letter(a), Shape::Letter(b)) => a == b,
            (Shape::Bx(a), Shape::Bx(b)) => a == b,
            (Shape::Not(a), Shape::Not(b)) => a.eq_rec(b, memo),
            (Shape::Or(a1, b1), Shape::Or(a2, b2)) => a1.eq_rec(a2, memo) && b1.eq_rec(b2, memo),
            (Shape::Tau(_, a), Shape::Tau(_, b)) => a.eq_rec(b, memo),
            (Shape::Special(s, x), Shape::Special(t, y)) => {
                s == t && x.len() == y.len() && x.iter().zip(y).all(|(a, b)| a.eq_rec(b, memo))
            }
            _ => false,
        };
        if r {
            memo.insert(key);
        }
        r
    }
}

/// Отложенное при сопоставлении вхождение метапеременной: (образец R(T..), цель, глубина).
type Deferred = (Expr, Expr, u32);

#[derive(PartialEq)]
enum Solve {
    /// Всё сошлось.
    Done,
    /// Противоречие.
    Fail,
    /// Остались метапеременные, которые не удалось найти.
    Stuck,
}

/// Разобрать отложенные вхождения R(T₁..Tₙ): когда R уже найдено, подставить и сравнить.
/// Если R нигде не стоит в виде Миллера (так бывает в (∃x)R = R(τx R(x)): вхождение
/// Миллера спрятано внутри аргумента), перебрать τ-подвыражения цели как кандидатов.
fn solve(
    metas: &[SpecialSign],
    got: &mut Vec<(SpecialSign, Expr)>,
    mut deferred: Vec<Deferred>,
    guess: bool,
) -> Solve {
    // предохранитель: если знак метапеременной встречается и в цели, подстановка
    // может порождать отложенные вхождения без конца
    let mut rounds = 0;
    loop {
        rounds += 1;
        if rounds > 256 {
            return Solve::Fail;
        }
        if deferred.is_empty() {
            return Solve::Done;
        }
        let mut progress = false;
        let mut rest = Vec::new();
        for (p, t, d) in std::mem::take(&mut deferred) {
            let Shape::Special(s, args) = p.shape() else {
                unreachable!()
            };
            match got.iter().find(|(m, _)| m == s).map(|(_, v)| v.clone()) {
                Some(body) => {
                    progress = true;
                    // все метапеременные вхождения уже известны: подставить и сравнить
                    // (сравнение идёт по общим частям дерева, сопоставление обходило бы
                    // дерево целиком, а оно бывает экспоненциально большим)
                    let inst = p.replace_signs(got);
                    let open = metas
                        .iter()
                        .filter(|m| !got.iter().any(|(g, _)| g == *m))
                        .fold(0, |acc, m| acc | sign_bit(m));
                    if inst.0.smask & open == 0 {
                        if inst != t {
                            return Solve::Fail;
                        }
                    } else if !body
                        .fill_holes(args)
                        .match_rec(&t, metas, got, &mut deferred, d)
                    {
                        return Solve::Fail;
                    }
                }
                None => rest.push((p, t, d)),
            }
        }
        deferred.extend(rest);
        if !progress {
            break;
        }
    }
    if !guess {
        return Solve::Stuck;
    }
    for (p, t, d) in &deferred {
        let Shape::Special(s, args) = p.shape() else {
            unreachable!()
        };
        let mut pts = Vec::new();
        for a in args {
            a.pattern_taus(*d, &mut pts);
        }
        // сначала самые глубокие τ образца: там вхождения Миллера дают естественное тело
        pts.sort_by_key(|(_, pd)| std::cmp::Reverse(*pd));
        for (pt, pd) in pts.iter().filter(|(pt, _)| pt.contains_sign(s)) {
            for tt in t
                .taus_at(*d, *pd)
                .iter()
                .filter(|tt| pt.skeleton_fits(tt, metas, 6))
            {
                let mut g2 = got.clone();
                let mut d2 = deferred.clone();
                if pt.match_rec(tt, metas, &mut g2, &mut d2, *pd)
                    && g2.iter().any(|(m, _)| m == s)
                    && solve(metas, &mut g2, d2, true) == Solve::Done
                {
                    *got = g2;
                    return Solve::Done;
                }
            }
        }
    }
    // последняя догадка: аргументы R(T) уже известны, тогда тело R это цель, в которой
    // все вхождения T стали дырой (так находится R в S6: T = U ⇒ (R(T) ⇔ R(U)))
    for (p, t, _) in &deferred {
        let Shape::Special(s, args) = p.shape() else {
            unreachable!()
        };
        let known: Vec<Expr> = args.iter().map(|a| a.replace_signs(got)).collect();
        if known
            .iter()
            .any(|a| metas.iter().any(|m| a.contains_sign(m)))
        {
            continue;
        }
        let Some(body) = t.abstract_exprs(&known) else {
            continue;
        };
        let mut g2 = got.clone();
        g2.push((s.clone(), body));
        if solve(metas, &mut g2, deferred.clone(), true) == Solve::Done {
            *got = g2;
            return Solve::Done;
        }
    }
    Solve::Stuck
}

/// Тождественность знакосочетаний: литеральное совпадение строк со связями.
impl PartialEq for Expr {
    fn eq(&self, o: &Expr) -> bool {
        self.eq_rec(o, &mut HashSet::default())
    }
}
impl Eq for Expr {}

impl Hash for Expr {
    fn hash<H: Hasher>(&self, h: &mut H) {
        h.write_u64(self.0.hash);
    }
}

impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&crate::syntax::show_expr(self))
    }
}

impl std::fmt::Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Sort::Term => "терм",
            Sort::Relation => "соотношение",
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn l(s: &str) -> Expr {
        Expr::letter(Letter::new(s))
    }
    fn eps() -> SpecialSign {
        SpecialSign::relational("∈", 2)
    }
    fn mem(a: Expr, b: Expr) -> Expr {
        Expr::special(eps(), vec![a, b])
    }

    #[test]
    fn tau_does_not_contain_its_letter() {
        // τ_x(x ∈ y) не содержит x (§ 1, n° 1)
        let t = Expr::tau(
            Letter::new("x"),
            mem(l("x"), l("y")).abstract_letter(&Letter::new("x")),
        );
        assert!(!t.contains_letter(&Letter::new("x")));
        assert!(t.contains_letter(&Letter::new("y")));
        assert_eq!(t.len(), 4); // τ ∈ □ y
    }

    #[test]
    fn identity_ignores_letter_names_under_tau() {
        // CS3: τ_x(A) и τ_x'(A') тождественны
        let a = Expr::tau(
            Letter::new("x"),
            mem(l("x"), l("y")).abstract_letter(&Letter::new("x")),
        );
        let b = Expr::tau(
            Letter::new("z"),
            mem(l("z"), l("y")).abstract_letter(&Letter::new("z")),
        );
        assert_eq!(a, b);
    }

    #[test]
    fn subst_and_instantiate_agree() {
        let x = Letter::new("x");
        let r = mem(l("x"), l("y"));
        let body = r.abstract_letter(&x);
        assert_eq!(body.instantiate(&l("z")), r.subst(&x, &l("z")));
    }

    #[test]
    fn fill_holes_shifts_under_binders() {
        // тело: τu(□₀ ∈ u), вставляем аргумент с висячим □ (он ссылается на внешний τ)
        let u = Letter::new("u");
        let body = Expr::tau(
            u.clone(),
            Expr::special(eps(), vec![Expr::bx(1), Expr::bx(0)]),
        );
        let filled = body.fill_holes(&[Expr::bx(0)]);
        // под одним τ внешний □₀ становится □₁
        let expect = Expr::tau(u, Expr::special(eps(), vec![Expr::bx(1), Expr::bx(0)]));
        assert_eq!(filled, expect);
        assert_eq!(Expr::bx(0).shift(2), Expr::bx(2));
    }

    #[test]
    fn replace_signs_is_simultaneous() {
        let a = SpecialSign::relational("A", 0);
        let b = SpecialSign::relational("B", 0);
        let ea = Expr::special(a.clone(), vec![]);
        let eb = Expr::special(b.clone(), vec![]);
        let e = Expr::or(ea.clone(), eb.clone());
        // A := B, B := A меняет местами
        let r = e.replace_signs(&[(a, eb.clone()), (b, ea.clone())]);
        assert_eq!(r, Expr::or(eb, ea));
    }

    #[test]
    fn replace_sign_of_weight_one_under_tau() {
        // (∃x)R(x) с R := (□₀ ∈ y) даёт (∃x)(x ∈ y)
        let r = SpecialSign::relational("R", 1);
        let x = Letter::new("x");
        let rx = Expr::special(r.clone(), vec![l("x")]);
        let ex = |body: Expr| {
            let b = body.abstract_letter(&x);
            b.instantiate(&Expr::tau(x.clone(), b.clone()))
        };
        let pattern = ex(rx);
        let got = pattern.replace_signs(&[(r, mem(Expr::bx(0), l("y")))]);
        assert_eq!(got, ex(mem(l("x"), l("y"))));
    }

    #[test]
    fn matching_finds_assignment() {
        let a = SpecialSign::relational("A", 0);
        let ea = Expr::special(a.clone(), vec![]);
        let pat = Expr::or(Expr::not(ea.clone()), ea);
        let p = mem(l("x"), l("y"));
        let target = Expr::or(Expr::not(p.clone()), p.clone());
        let mut got = Vec::new();
        assert!(pat.match_into(&target, std::slice::from_ref(&a), &mut got));
        assert_eq!(got, vec![(a.clone(), p)]);
        let bad = Expr::or(Expr::not(mem(l("x"), l("y"))), mem(l("y"), l("x")));
        assert!(!pat.match_into(&bad, &[a], &mut Vec::new()));
    }

    #[test]
    fn sorts() {
        assert_eq!(l("x").sort(), Some(Sort::Term));
        assert_eq!(mem(l("x"), l("y")).sort(), Some(Sort::Relation));
        assert_eq!(Expr::not(l("x")).sort(), None);
        assert_eq!(Expr::bx(0).sort(), None);
    }

    #[test]
    fn length_does_not_explode_in_memory() {
        // (∃x₁)...(∃xₙ)(x₁ ∈ ... ) удваивает длину строки на каждом кванторе,
        // а дерево с общими частями растёт линейно
        let mut r = mem(l("a"), l("b"));
        for i in 0..40 {
            let x = Letter::new(&format!("x{i}"));
            r = Expr::or(r, mem(l(&format!("x{i}")), l("a")));
            let b = r.abstract_letter(&x);
            r = b.instantiate(&Expr::tau(x, b.clone()));
        }
        assert!(r.len() > 1u128 << 40);
    }
}
