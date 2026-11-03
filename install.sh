#!/bin/sh
# Installs the Lithe compiler: the latest release, or the version given as the first argument.
#   curl -fsSL https://lithe-lang.org/install.sh | sh
#   curl -fsSL https://lithe-lang.org/install.sh | sh -s -- 0.3.0
# LITHE_HOME moves the install from ~/.lithe; LITHE_NO_MODIFY_PATH=1 leaves shell profiles alone.
set -eu

repo=https://github.com/celestiaorg/lithe/releases
version=${1:-}
version=${version#v}
if [ -n "$version" ]; then base=$repo/download/v$version; else base=$repo/latest/download; fi
base=${LITHE_DOWNLOAD_URL:-$base}

if [ -t 1 ] && [ -z "${NO_COLOR:-}" ]; then
  bold=$(printf '\033[1m') dim=$(printf '\033[2m') green=$(printf '\033[32m')
  yellow=$(printf '\033[33m') red=$(printf '\033[31m') reset=$(printf '\033[0m')
  case ${COLORTERM:-} in
    truecolor | 24bit) leaf=$(printf '\033[38;2;16;245;170m') ;;
    *) leaf=$(printf '\033[38;5;49m') ;;
  esac
else
  bold='' dim='' green='' yellow='' red='' reset='' leaf=''
fi
logo() {
  case "${LC_ALL:-${LC_CTYPE:-${LANG:-}}}" in *[Uu][Tt][Ff]-8* | *[Uu][Tt][Ff]8*) ;; *) return 0 ;; esac
  [ "$(tput cols 2>/dev/null || echo 0)" -ge 80 ] || return 0
  cat <<EOF
▐██▙▖               ${leaf}  ▗▟${reset}  ▐██▙▖         ▗▟█▙▖
▐███▌               ${leaf}▗▟█▛${reset}  ▐███▌         ▐███▌
▐███▌               ${leaf}█▀▘ ${reset}  ▐███▌         ▐███▌
▐███▌                ▄▟▌  ▐███████████  ▐█████████████▄▄       ▄▄██████████▙▄▖
▐███▌               ▟██▌  ▐████████▛▀   ▐████████████████▖   ▄████████████████▄
▐███▌               ███▌  ▐███▌         ▐███▌         ▜███  ▗███▛          ▜███▖
▐███▌               ███▌  ▐███▌         ▐███▌         ▐███  ▐███   ▗▟██████████▌
▐███▌               ███▌  ▐███▌         ▐███▌         ▐███  ▐███  ▐████████████
 ████▄              ███▌  ▝███▙▖        ▐███▌         ▐███  ▝███▙
  ▜██████████████▄  ▜██▌   ▝█████████▄  ▐███▌         ▐███   ▝██████████████▙▖
    ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀  ▀▀▘     ▝▀▀▀▀▀▀▀▀▀ ▝▀▀▀▘         ▝▀▀▀▘    ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀
EOF
  echo
}
ok() { printf '%s✓%s %s\n' "$green" "$reset" "$*"; }
warn() { printf '%s!%s %s\n' "$yellow" "$reset" "$*"; }
fail() { printf '%serror%s: %s\n' "$red" "$reset" "$*" >&2; exit 1; }
tilde() { case $1 in "$HOME"/*) echo "~${1#"$HOME"}" ;; *) echo "$1" ;; esac; }

arch=$(uname -m)
# A shell under Rosetta reports x86_64 on Apple silicon.
[ "$(sysctl -n sysctl.proc_translated 2>/dev/null || true)" = 1 ] && arch=arm64
case "$(uname -s)-$arch" in
  Linux-x86_64 | Linux-amd64) target=x86_64-unknown-linux-musl platform="Linux x86-64" ;;
  Linux-aarch64 | Linux-arm64) target=aarch64-unknown-linux-musl platform="Linux ARM64" ;;
  Darwin-arm64) target=aarch64-apple-darwin platform="macOS (Apple silicon)" ;;
  Darwin-x86_64) target=x86_64-apple-darwin platform="macOS (Intel)" ;;
  *) fail "no prebuilt lithe for $(uname -s) $(uname -m). Build it from source: https://github.com/celestiaorg/lithe" ;;
esac

command -v curl >/dev/null || fail "the installer needs curl"
if command -v sha256sum >/dev/null; then sha256='sha256sum'
elif command -v shasum >/dev/null; then sha256='shasum -a 256'
else fail "the installer needs sha256sum or shasum"; fi

[ -t 1 ] && logo
printf '%sInstalling lithe %s%s for %s\n\n' "$bold" "${version:-(latest)}" "$reset" "$platform"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
if ! status=$(curl -fsL -o "$tmp/SHA256SUMS" -w '%{http_code}' "$base/SHA256SUMS"); then
  case $status in
    404) if [ -n "$version" ]; then fail "lithe $version is not a release. Releases: $repo"; else fail "no lithe release found at $base"; fi ;;
    000) fail "cannot reach $base. Check your internet connection." ;;
    *) fail "download from $base failed (HTTP $status)" ;;
  esac
fi
bin=lithe-$target
if [ -t 2 ]; then progress=--progress-bar; else progress=-s; fi
curl -fL $progress -o "$tmp/$bin" "$base/$bin" || fail "download of $base/$bin failed"

expected=$(awk -v f="$bin" '$2 == f || $2 == "*" f { print $1 }' "$tmp/SHA256SUMS")
actual=$(cd "$tmp" && $sha256 "$bin" | awk '{ print $1 }')
[ -n "$expected" ] || fail "this release has no build for $platform ($target)"
[ "$expected" = "$actual" ] || fail "the download is corrupt (checksum mismatch); nothing was installed. Try again."
ok "Verified checksum"

dir=${LITHE_HOME:-$HOME/.lithe}/bin
dest=$dir/lithe
old=''
[ -x "$dest" ] && old=$("$dest" --version 2>/dev/null | sed 's/^lithe //' || true)
mkdir -p "$dir"
chmod +x "$tmp/$bin"
mv "$tmp/$bin" "$dest"
new=$("$dest" --version | sed 's/^lithe //')
if [ -n "$old" ] && [ "$old" != "$new" ]; then
  ok "Updated lithe $old → $bold$new$reset in $(tilde "$dest")"
else
  ok "Installed lithe $bold$new$reset to $(tilde "$dest")"
fi

reload=''
case ":$PATH:" in
  *":$dir:"*)
    found=$(command -v lithe || true)
    [ "$found" = "$dest" ] || warn "$(tilde "$found") comes first on your PATH, so \`lithe\` runs that one instead"
    ;;
  *)
    case $(basename "${SHELL:-sh}") in
      zsh) rc=${ZDOTDIR:-$HOME}/.zshrc line="export PATH=\"$dir:\$PATH\"" ;;
      bash) rc=$HOME/.bashrc line="export PATH=\"$dir:\$PATH\""
        [ "$(uname -s)" = Darwin ] && rc=$HOME/.bash_profile ;;
      fish) rc=$HOME/.config/fish/config.fish line="fish_add_path $dir" ;;
      *) rc=$HOME/.profile line="export PATH=\"$dir:\$PATH\"" ;;
    esac
    if [ -n "${LITHE_NO_MODIFY_PATH:-}" ]; then
      warn "$(tilde "$dir") is not on your PATH. Add it with:"
      printf '    %s\n' "$line"
    else
      if grep -qsF "$line" "$rc"; then
        ok "$(tilde "$rc") already adds $(tilde "$dir") to your PATH"
      else
        mkdir -p "$(dirname "$rc")"
        printf '\n# lithe\n%s\n' "$line" >>"$rc"
        ok "Added $(tilde "$dir") to your PATH in $(tilde "$rc")"
      fi
      reload="source $(tilde "$rc")"
    fi
    ;;
esac

printf '\n'
if [ -n "$reload" ]; then
  printf 'Open a new terminal, or run %s%s%s, then:\n' "$bold" "$reload" "$reset"
else
  printf 'Try it:\n'
fi
printf '    lithe --version\n\n'
printf 'Get started: %shttps://lithe-lang.org/guide/getting-started%s\n' "$dim" "$reset"
