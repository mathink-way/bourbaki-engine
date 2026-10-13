//! Расширение Zed: запускает `bourbaki-lsp` для файлов `.bk`.
//! Сервер берётся из PATH (`cargo install --path .` в папке bourbaki-engine).

use zed_extension_api::{self as zed, LanguageServerId, Result};

struct Bourbaki;

impl zed::Extension for Bourbaki {
    fn new() -> Self {
        Bourbaki
    }

    fn language_server_command(
        &mut self,
        _id: &LanguageServerId,
        worktree: &zed::Worktree,
    ) -> Result<zed::Command> {
        let path = worktree.which("bourbaki-lsp").ok_or_else(|| {
            "bourbaki-lsp не найден в PATH: выполните `cargo install --path .` в папке bourbaki-engine"
                .to_string()
        })?;
        Ok(zed::Command {
            command: path,
            args: vec![],
            env: Default::default(),
        })
    }
}

zed::register_extension!(Bourbaki);
