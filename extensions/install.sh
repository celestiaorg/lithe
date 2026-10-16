#!/bin/sh
set -eu
cd "$(dirname "$0")"
./sync-grammar.sh

rm -rf ~/.recur/bundles/Lithe
mkdir -p ~/.recur/bundles
cp -R recur/bundles/Lithe ~/.recur/bundles/
echo "installed ~/.recur/bundles/Lithe"

for dir in ~/.vscode/extensions ~/.cursor/extensions; do
  [ -d "$dir" ] || continue
  [ -d vscode/node_modules ] || (cd vscode && npm ci --omit=dev)
  rm -rf "$dir/lithe.lithe"
  cp -R vscode "$dir/lithe.lithe"
  echo "installed $dir/lithe.lithe"
done
