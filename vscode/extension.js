// Расширение VS Code: подсветка .bk и запуск языкового сервера bourbaki-lsp.
const fs = require("fs");
const os = require("os");
const path = require("path");
const vscode = require("vscode");
const { LanguageClient } = require("vscode-languageclient/node");

let client;

// Где взять сервер: настройка bourbaki.serverPath, затем ~/.cargo/bin (VS Code, запущенный
// из Dock, часто не видит PATH терминала), затем просто имя из PATH.
function serverPath() {
  const configured = vscode.workspace.getConfiguration("bourbaki").get("serverPath");
  if (configured) return configured;
  const exe = process.platform === "win32" ? "bourbaki-lsp.exe" : "bourbaki-lsp";
  const cargo = path.join(os.homedir(), ".cargo", "bin", exe);
  return fs.existsSync(cargo) ? cargo : exe;
}

function activate(context) {
  const command = serverPath();
  client = new LanguageClient(
    "bourbaki",
    "Bourbaki",
    { command, args: [] },
    { documentSelector: [{ scheme: "file", language: "bourbaki" }] }
  );
  client.start().catch((e) => {
    vscode.window.showErrorMessage(
      `Не удалось запустить ${command}: ${e}. Выполните "cargo install --path ." в папке bourbaki-engine или укажите bourbaki.serverPath.`
    );
  });
  context.subscriptions.push({ dispose: () => client && client.stop() });
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
