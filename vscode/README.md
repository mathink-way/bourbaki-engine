# VS Code: подсветка и проверка конспектов `.bk`

Расширение подключает к файлам `.bk` подсветку (`syntaxes/bourbaki.tmLanguage.json`) и
языковой сервер `bourbaki-lsp`: ошибки проверки подчёркиваются при каждом изменении,
наведение на имя показывает теорему, схему, сокращение или знак.

## Установка

```
cargo install --path .                    # в корне bourbaki-engine: ставит bourbaki-lsp
cd vscode
npm install
npx @vscode/vsce package                  # получится bourbaki-0.1.0.vsix
code --install-extension bourbaki-0.1.0.vsix
```

(Или в самом VS Code: палитра команд, `Extensions: Install from VSIX...`.)

Сервер ищется так: настройка `bourbaki.serverPath`, затем `~/.cargo/bin/bourbaki-lsp`,
затем `bourbaki-lsp` из PATH. Если VS Code пишет, что сервер не запустился, укажите путь
в настройках явно.

## Проверка

Открыть `konspekt/01_logic.bk`: справа внизу язык `Bourbaki`, ключевые слова подсвечены;
испортить строку (`by mp 1 4` на `by mp 1 3` в C8), она подчеркнётся; навести на `C6`,
всплывёт формулировка. Логи сервера: вкладка Output, канал `Bourbaki`.

Проверено: пакет собирается (`vsce package`), подсветка размечает файлы конспекта
(проверено библиотекой `vscode-textmate`, на которой работает VS Code). В самом VS Code
не запускалось.
