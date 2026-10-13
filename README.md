# bourbaki-engine

**English** | [Русский](README.ru.md)

Chapter I of N. Bourbaki's *Theory of Sets* as a program. You write proofs the way the
book writes them; the program checks every line and, on request, unfolds it all the way
down to explicit axioms, schemes and modus ponens. There are no types: only what Bourbaki
has, namely assemblies with τ and □, terms, relations, theories, schemes and proofs.

```
theorem C8 {A : rel} : A ⇒ A {
  A ⇒ (A ∨ A)                                  by S2 with A := A; B := A
  (A ∨ A) ⇒ A                                  by S1 with A := A
  ((A ∨ A) ⇒ A) ⇒ ((A ⇒ (A ∨ A)) ⇒ (A ⇒ A))    by S4 with A := A ∨ A; B := A; C := ¬A
  (A ⇒ (A ∨ A)) ⇒ (A ⇒ A)                      by mp 2 3
  A ⇒ A                                        by mp 1 ^
}
```

Lines are numbered automatically and `^` is the previous line. From then on `by C8` is a
single step in any proof, and substitutions can be omitted when they are visible from
the line itself.

> The language keywords are English; the detailed documentation, the comments in the
> notes (`konspekt/`) and the error messages are in Russian, following the Russian
> translation of the book (Moscow: Mir, 1965). This README is a complete overview in
> English.

## Contents

* [Quick start](#quick-start)
* [The language in two minutes](#the-language-in-two-minutes)
* [What is formalized](#what-is-formalized)
* [Editor support](#editor-support)
* [How it works](#how-it-works)
* [Repository layout](#repository-layout)
* [Development](#development)
* [Status and limitations](#status-and-limitations)
* [License and the book](#license-and-the-book)

## Quick start

You need Rust 1.85 or newer (via `rustup`).

```
git clone https://github.com/mathink-way/bourbaki-engine && cd bourbaki-engine
cargo install --path .                            # installs bourbaki and bourbaki-lsp
bourbaki check konspekt/*.bk                      # check all the notes
bourbaki expand konspekt/02_quant_eq.bk ch1.T1    # unfold a theorem down to S1-S7 and C1
bourbaki check file.bk --prefix                   # print in Bourbaki's Polish notation
```

Without installing: `cargo run --release -- check konspekt/01_logic.bk`.

A file of your own starts like this:

```
import "00_prelude.bk"     -- schemes S1-S7, theories Logical, Quantified, Egalitarian (namespace base)
import "01_logic.bk"       -- criteria C6-C21 (namespace ch1)
open base
open ch1
in Logical

theorem my_first {A B : rel} (h : B) : A ⇒ B {
  B ⇒ (¬A ∨ B)   by C7
  A ⇒ B          by mp h ^
}
```

Import paths are relative to the file. An import does not paste text: the imported file
is checked once, in its own fresh state, and its declarations become available under
their full names (`ch1.C7`, `base.S1`).

## The language in two minutes

| what                                    | how                                                            |
|-----------------------------------------|----------------------------------------------------------------|
| metavariables (the book's bold letters) | `{A B : rel}`, `{T : term}`, `{R : rel 1}` (that is R{x}, written `R(x)`) |
| hypotheses                              | `theorem T {A B : rel} (h : A ⇒ B) : ...`                       |
| a scheme                                | `by S5`, `by S4 with A := P; B := Q; C := ¬P`                   |
| a proven theorem                        | `by C6 1 ^` (the references are the lines proving its hypotheses) |
| modus ponens (C1)                       | `by mp 2 3`                                                    |
| C14, auxiliary hypothesis               | `A ⇒ B by assume h { ... }`                                    |
| C15, reductio ad absurdum               | `A by contra g { ... }`                                        |
| C27 generalization, C3 substitution     | `by gen ^ with x`, `by subst ^ with x := T`                    |
| tautology (exercise 7 of § 3)           | `by taut`                                                      |
| a gap                                   | `by sorry` (the theorem is marked)                             |
| new signs and abbreviations             | `sign ∈ [\in] : rel 2 infix`, `abbrev ⊂ (X Y : term) infix := (∀z)(z ∈ X ⇒ z ∈ Y)` |
| abbreviations binding a letter          | `abbrev Coll (R : rel 1) := (∃y)(∀x)(x ∈ y ⇔ R(x))`, used as `Coll_x(x ∈ a)` |
| theories                                | `theory Set extends Egalitarian { signs ∈ ; schemes S8 ; axiom A1 : ... }` |
| models (C5)                             | `model M : G -> H with a := T { A1 by ... }`, `transfer thm via M` |
| names                                   | `namespace ch1 ... end`, `open ch1`, `alias imp_trans := ch1.C6` |
| notation                                | `#set infix` (default) or `#set prefix` (Polish: `∨ ¬ A B`)      |
| commands                                | `#show`, `#signs`, `#formation`, `#print`, `#expand`, `#log`, `#format` |

Symbols can be typed as words or LaTeX commands:
`\forall x \exists y (x \in y \to y \in x)` is `(∀x)(∃y)(x ∈ y ⇒ y ∈ x)`.
Full reference (in Russian): [docs/FORMAT.md](docs/FORMAT.md).

## What is formalized

The notes live in `konspekt/`. *Konspekt* is the Russian word for a student's written-up
summary of a book or a lecture course; the Rust API uses the same word (`Konspekt` is the
state of a checked set of notes).

| file                | contents                                                               |
|---------------------|------------------------------------------------------------------------|
| `00_prelude.bk`     | schemes S1-S7, theories Logical, Quantified, Egalitarian (`base`)        |
| `01_logic.bk`       | § 3: C6-C21                                                            |
| `02_quant_eq.bk`    | C30, theorems 1-3 on equality                                          |
| `03_notation.bk`    | custom signs, abbreviations, Polish notation                           |
| `04_equiv.bk`       | § 3, n° 5: C22-C25                                                     |
| `05_quant.bk`       | § 4: C26-C34                                                           |
| `06_typed.bk`       | typed quantifiers, C35-C42                                             |
| `07_equality.bk`    | § 5: C43-C47, "single-valued" and "functional" relations               |
| `10_sets.bk`        | chapter II, skeleton: ∈, pairs, S8, A1-A4, C48-C51, Russell's paradox, {x, y}, ∅, 𝔓 |

All of chapter I is checked. Full unfolding down to the axioms has been verified for every
theorem except C51 and the results built on it (it does not fit into 6 GB of memory, see
the limitations).

## Editor support

`bourbaki-lsp` is a language server: errors are underlined on every change, and hovering
over a name shows the theorem, scheme, abbreviation or sign. Any LSP-capable editor
works. Ready-made extensions with syntax highlighting: [VS Code](vscode/README.md) and
[Zed](zed/README.md) (installation instructions are inside, in Russian).

## How it works

1. **Assemblies are trees with shared subtrees** (□ are de Bruijn indices). Literally,
   (∃x)R grows exponentially; the tree grows linearly. Identity of assemblies is equality
   of trees, so (∃x)R(x) and (∃y)R(y) are the same object, as in the book.
2. **Metavariables are special signs.** A theorem about A is proven in 𝒯 + the sign A;
   replacing the sign by a relation turns a proof into a proof. So applying a theorem means
   substituting into its statement, not re-checking its proof.
3. **Metatheorems** (C14, C15, C27, C3, tautologies, C5) are checked by their conditions;
   their constructive proofs from the book run only when a proof is unfolded.
4. **Unfolded proofs are checked independently** by `Demonstration::verify`, which knows
   nothing but the definition of a proof from § 2.

Details (in Russian): [docs/HOW_IT_WORKS.md](docs/HOW_IT_WORKS.md).

## Repository layout

```
konspekt/        the notes (.bk), checked by the tests
docs/            FORMAT.md (file format), HOW_IT_WORKS.md (internals), DOCS.md (LaTeX in docs)
src/             kernel: expr.rs (assemblies), formative.rs (formative criteria), theory.rs
                 (theories, schemes), proof.rs (theorems, proofs), logic.rs / quant.rs / equality.rs
src/konspekt/    the language: parse.rs, check.rs, model.rs (C5), mod.rs (names, imports, commands)
src/main.rs      the bourbaki command;  src/bin/bourbaki-lsp.rs  the language server
tests/           tests, including the whole konspekt and a real LSP session
vscode/          VS Code extension (highlighting + language server)
zed/             Zed extension and highlighting grammar
examples/        a tour of the kernel in Rust: cargo run --example tour
```

## Development

```
cargo test                      # all tests (notes, unfoldings, LSP)
cargo clippy --all-targets
cargo doc --open                # API docs; the "book" module renders the notes, math via KaTeX
```

LaTeX works in the comments of the notes and in rustdoc, see [docs/DOCS.md](docs/DOCS.md).

## Status and limitations

* All of chapter I and the beginning of chapter II. This is a study project, made to get a
  hands-on feel for the book, not an industrial proof assistant.
* Unfolded proofs of late criteria are huge (C40 and C42 exceed 100,000 lines); C51 does
  not fit into 6 GB. Fast checking is unaffected.
* For schemes like S6, where R occurs only as R(T), the substitution must be written.
* No step-by-step unfolding yet. The VS Code extension has not been tried inside VS Code
  itself yet (it packages, and its grammar was tested with `vscode-textmate`).

## License and the book

The code and texts of this repository are licensed under MIT ([LICENSE](LICENSE)).

The repository does not contain the text of the book. The notes are an independent
retelling: formal statements, the numbering of criteria (C1-C51, S1-S8) and page
references to the Russian translation (N. Bourbaki, *Теория множеств*, Moscow: Mir, 1965).
Mathematical statements and ideas are not protected by copyright, while the text of the book
and of its translation is; therefore no scans and no long quotations are included. This
project is not affiliated with the Bourbaki association or any rights holder.
