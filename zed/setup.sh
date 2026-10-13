#!/bin/sh
# Готовит расширение Zed к установке ("zed: install dev extension").
# Zed берёт грамматику подсветки из git-репозитория по коммиту, поэтому копия грамматики
# кладётся в отдельный локальный репозиторий, а его путь и коммит пишутся в extension.toml.
set -e
here=$(cd "$(dirname "$0")" && pwd)
dst="$HOME/.local/share/bourbaki/tree-sitter-bourbaki"
mkdir -p "$dst"
cp -R "$here/tree-sitter-bourbaki/." "$dst/"
cd "$dst"
[ -d .git ] || git init -q
git add -A
git -c user.name=bourbaki -c user.email=bourbaki@localhost commit -q -m grammar || true
rev=$(git rev-parse HEAD)
cd "$here/bourbaki"
sed -i.bak \
  -e "s|^repository = .*|repository = \"file://$dst\"|" \
  -e "s|^rev = .*|rev = \"$rev\"|" extension.toml
rm -f extension.toml.bak
echo "грамматика: $dst @ $rev"
echo "дальше: в Zed команда 'zed: install dev extension', папка $here/bourbaki"
