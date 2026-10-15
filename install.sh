#!/bin/sh
# Installs the Lithe compiler: the latest release, or the version given as the first argument.
#   curl -fsSL https://raw.githubusercontent.com/celestiaorg/lithe/main/install.sh | sh
#   curl -fsSL https://raw.githubusercontent.com/celestiaorg/lithe/main/install.sh | sh -s -- 0.2.0
set -eu

repo=https://github.com/celestiaorg/lithe/releases
version=${1:-}
version=${version#v}
if [ -n "$version" ]; then base=$repo/download/v$version; else base=$repo/latest/download; fi
base=${LITHE_DOWNLOAD_URL:-$base}

fail() { echo "lithe install: $*" >&2; exit 1; }

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64 | Linux-amd64) target=x86_64-unknown-linux-musl ;;
  Linux-aarch64 | Linux-arm64) target=aarch64-unknown-linux-musl ;;
  Darwin-arm64) target=aarch64-apple-darwin ;;
  Darwin-x86_64) target=x86_64-apple-darwin ;;
  *) fail "no release for $(uname -s) $(uname -m); build from source: https://github.com/celestiaorg/lithe" ;;
esac

if command -v sha256sum >/dev/null; then sha256='sha256sum'
elif command -v shasum >/dev/null; then sha256='shasum -a 256'
else fail "needs sha256sum or shasum"; fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fetch() { curl -fsSL -o "$tmp/$1" "$base/$1" || fail "cannot download $base/$1${version:+ (is $version a release?)}"; }
fetch SHA256SUMS
fetch "lithe-$target"

expected=$(awk -v f="lithe-$target" '$2 == f || $2 == "*" f { print $1 }' "$tmp/SHA256SUMS")
actual=$(cd "$tmp" && $sha256 "lithe-$target" | awk '{ print $1 }')
[ -n "$expected" ] || fail "SHA256SUMS has no lithe-$target"
[ "$expected" = "$actual" ] || fail "checksum mismatch for lithe-$target: expected $expected, got $actual"

dir=${LITHE_HOME:-$HOME/.lithe}/bin
mkdir -p "$dir"
chmod +x "$tmp/lithe-$target"
mv "$tmp/lithe-$target" "$dir/lithe"
echo "Installed $("$dir/lithe" --version) to $dir/lithe"

case ":$PATH:" in
  *":$dir:"*) ;;
  *) echo "Add it to your PATH:"; echo "  export PATH=\"$dir:\$PATH\"" ;;
esac
