// Грамматика tree-sitter для конспектов .bk. Только для подсветки в Zed:
// настоящий разбор и проверку делает bourbaki-lsp. Поэтому грамматика плоская:
// файл это последовательность лексем.

module.exports = grammar({
  name: 'bourbaki',

  extras: $ => [/\s/],

  word: $ => $.identifier,

  rules: {
    source_file: $ => repeat($._token),

    _token: $ => choice(
      $.comment,
      $.keyword,
      $.rule,
      $.command,
      $.string,
      $.number,
      $.identifier,
      $.operator,
      $.punctuation,
      $.other,
    ),

    comment: _ => token(seq('--', /.*/)),

    keyword: _ => choice(
      'import', 'namespace', 'end', 'open', 'alias', 'sign', 'abbrev', 'scheme',
      'theory', 'extends', 'in', 'theorem', 'lemma', 'by', 'with', 'model',
      'transfer', 'via', 'as', 'signs', 'schemes', 'axiom', 'rel', 'term', 'infix',
    ),

    rule: _ => choice('mp', 'gen', 'subst', 'taut', 'assume', 'contra', 'sorry'),

    command: _ => /#[a-z]+/,

    string: _ => /"[^"\n]*"/,

    number: _ => /[0-9]+/,

    identifier: _ => /[\p{L}_][\p{L}\p{N}_'.]*/,

    operator: _ => /[¬∨∧⇒⇔∃∀τ=∈∉⊂≠→↔~<>^|:]+/,

    punctuation: _ => /[(){}\[\],;.]/,

    // любой другой значок (свои знаки: ⊃, ×, ∁, ...)
    other: _ => token(prec(-1, /[^\s]/)),
  },
});
