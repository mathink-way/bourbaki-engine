# Zed: подсветка и проверка конспектов `.bk`

Что есть:

* `bourbaki-lsp` (в корне проекта, `src/bin/bourbaki-lsp.rs`): языковой сервер. Ошибки
  проверки подчёркиваются в тексте при каждом изменении, наведение на имя (теорема,
  схема, теория, сокращение, знак) показывает, что это.
* `bourbaki/`: расширение Zed. Запускает `bourbaki-lsp` из PATH и подключает подсветку.
* `tree-sitter-bourbaki/`: грамматика подсветки (только лексемы: ключевые слова,
  правила `mp`/`gen`/..., команды `#...`, комментарии). Настоящий разбор делает сервер.

## Установка

```
cargo install --path .              # в корне bourbaki-engine: ставит bourbaki и bourbaki-lsp
rustup target add wasm32-wasip1     # Zed собирает расширение под wasm
```

Zed берёт грамматику подсветки из git-репозитория по коммиту
(`[grammars.bourbaki]` в `bourbaki/extension.toml`). Есть два пути.

**Проект уже на GitHub** (удобнее): в `bourbaki/extension.toml` написать

```
[grammars.bourbaki]
repository = "https://github.com/mathink-way/bourbaki-engine"
rev = "<коммит, в котором есть zed/tree-sitter-bourbaki>"
path = "zed/tree-sitter-bourbaki"
```

**Без GitHub**: `sh zed/setup.sh` кладёт копию грамматики в отдельный локальный
git-репозиторий (`~/.local/share/bourbaki/`) и сам записывает его путь (`file://...`) и
коммит в `extension.toml`.

Потом в Zed: палитра команд, `zed: install dev extension`, папка `zed/bourbaki`.

## Проверка

1. `cargo test --test lsp`: тест запускает настоящий `bourbaki-lsp` и разговаривает с ним
   как редактор (ошибка на нужной строке, исправление, наведение, `sorry`, прелюдия).
2. В Zed открыть `konspekt/01_logic.bk`: справа внизу язык `Bourbaki`, ключевые слова
   подсвечены; испортить строку (`by mp 1 4` на `by mp 1 3` в C8), она подчеркнётся;
   навести на `C6`, всплывёт формулировка.
3. Если что-то не так: `zed: open log`. Нет подсветки, но ошибки подчёркиваются, значит
   Zed не нашёл грамматику (см. `[grammars.bourbaki]`). Подсветка есть, ошибок нет, значит
   не запустился сервер (`which bourbaki-lsp`).

## Что проверено

Сервер (тест выше), грамматика (`tree-sitter generate`, все `konspekt/*.bk` разбираются без
ошибок), код расширения собирается. В самом Zed пока не проверялось.

После изменения `grammar.js` нужно заново выполнить `tree-sitter generate` в
`zed/tree-sitter-bourbaki` (npm-пакет `tree-sitter-cli`) и закоммитить `src/`.
