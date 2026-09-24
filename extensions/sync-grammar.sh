#!/bin/sh
set -eu
cd "$(dirname "$0")"
for dest in \
  recur/bundles/Lithe/syntaxes/lithe.tmLanguage.json \
  vscode/syntaxes/lithe.tmLanguage.json
do
  rm -f "$dest"
  cp lithe.tmLanguage.json "$dest"
done
