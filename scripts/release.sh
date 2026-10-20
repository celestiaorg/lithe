#!/bin/sh
# Opens the PR that releases a version. Merging it makes release.yml tag v<version> on that
# commit and publish the binaries.
#   scripts/release.sh            asks for the version
#   scripts/release.sh patch      or minor, major, or an exact 0.2.3
set -eu

if [ -t 1 ] && [ -z "${NO_COLOR:-}" ]; then
  bold=$(printf '\033[1m') dim=$(printf '\033[2m') green=$(printf '\033[32m')
  red=$(printf '\033[31m') reset=$(printf '\033[0m')
else
  bold='' dim='' green='' red='' reset=''
fi
ok() { printf '%s✓%s %s\n' "$green" "$reset" "$*"; }
fail() { printf '%serror%s: %s\n' "$red" "$reset" "$*" >&2; exit 1; }
quiet() { out=$("$@" 2>&1) || { printf '%s\n' "$out" >&2; fail "$* failed"; }; }

cd "$(git rev-parse --show-toplevel)"
[ -z "$(git status --porcelain)" ] || fail "the working tree has changes; commit or set them aside first"
quiet git fetch origin main
current=$(git show origin/main:Cargo.toml | sed -n 's/^version = "\(.*\)"$/\1/p' | head -1)
IFS=. read -r major minor patch <<EOF
$current
EOF
next_patch=$major.$minor.$((patch + 1))
next_minor=$major.$((minor + 1)).0
next_major=$((major + 1)).0.0

choice=${1:-}
if [ -z "$choice" ]; then
  [ -t 0 ] || fail "usage: scripts/release.sh <patch|minor|major|x.y.z>"
  printf '%sCurrent version%s %s\n\n' "$bold" "$reset" "$current"
  printf '  1) patch  %s\n  2) minor  %s\n  3) major  %s\n\n' "$next_patch" "$next_minor" "$next_major"
  printf 'Release which? [1] or a version: '
  read -r choice || true
fi
case ${choice:-1} in
  1 | patch) version=$next_patch ;;
  2 | minor) version=$next_minor ;;
  3 | major) version=$next_major ;;
  *) version=${choice#v} ;;
esac
echo "$version" | grep -Eq '^[0-9]+\.[0-9]+\.[0-9]+$' || fail "$version isn't a major.minor.patch version"
[ "$version" != "$current" ] || fail "main is already at $version"
branch=release-v$version
! git ls-remote --exit-code --tags origin "refs/tags/v$version" >/dev/null || fail "v$version is already released"
! git rev-parse --verify --quiet "refs/heads/$branch" >/dev/null || fail "branch $branch already exists"

printf '\n%sReleasing lithe %s → %s%s\n\n' "$bold" "$current" "$version" "$reset"
start=$(git rev-parse --abbrev-ref HEAD)
quiet git switch --create "$branch" origin/main
ok "Branched $branch from origin/main"

docs=docs/src/pages/guide/getting-started.mdx
sed -i.bak "1,/^version = /s/^version = \".*\"/version = \"$version\"/" Cargo.toml
sed -i.bak -e "s/sh -s -- [0-9][0-9.]*/sh -s -- $version/" -e "s/--tag v[0-9][0-9.]*/--tag v$version/" install.sh "$docs"
rm Cargo.toml.bak install.sh.bak "$docs.bak"
quiet cargo update --workspace
(cd playground && quiet cargo update --package lithe)
ok "Set $version in:"
git diff --stat | sed '$d'

quiet git commit --message "Release v$version" Cargo.toml Cargo.lock playground/Cargo.lock install.sh "$docs"
ok "Committed $(git rev-parse --short HEAD) Release v$version"

printf '\nPush %s and open the PR? [Y/n] ' "$branch"
read -r answer || { answer=n; echo; }
case $answer in
  "" | [Yy]*) ;;
  *)
    quiet git switch "$start"
    quiet git branch --delete --force "$branch"
    fail "stopped; back on $start"
    ;;
esac
quiet git push --set-upstream origin "$branch"
ok "Pushed $branch"
url=$(gh pr create --base main --head "$branch" --title "Release v$version" \
  --body "Merging this tags \`v$version\` and publishes the release.")
ok "Opened $url"

printf '\nMerging it tags %sv%s%s and publishes the binaries:\n' "$bold" "$version" "$reset"
printf '    %shttps://github.com/celestiaorg/lithe/actions/workflows/release.yml%s\n' "$dim" "$reset"
