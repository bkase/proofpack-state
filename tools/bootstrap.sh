#!/usr/bin/env bash
# Fetch and verify the pinned Bend toolchain into .toolchain/.
# Reproducibility: the archive's sha256 must equal the one in toolchain.lock.json,
# which was itself copied from the pinned revision's flake.nix.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
lock="$root/toolchain.lock.json"
ver="$(sed -n 's/.*"version": "\([^"]*\)".*/\1/p' "$lock" | head -1)"

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)  key=aarch64-darwin ;;
  Darwin-x86_64) key=x86_64-darwin ;;
  Linux-aarch64) key=aarch64-linux ;;
  Linux-x86_64)  key=x86_64-linux ;;
  *) echo "bootstrap: unsupported host $(uname -s)-$(uname -m)" >&2; exit 2 ;;
esac

url="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["artifacts"][sys.argv[2]]["url"])' "$lock" "$key")"
want="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["artifacts"][sys.argv[2]]["sha256"])' "$lock" "$key")"

dest="$root/.toolchain/bend-$ver"
if [ -x "$dest/bend/bin/bend" ]; then
  echo "bootstrap: bend $ver already present at $dest"
  exit 0
fi

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
echo "bootstrap: fetching $url"
curl -fsSL -o "$tmp/bend.tar.gz" "$url"

got="$(shasum -a 256 "$tmp/bend.tar.gz" | cut -d' ' -f1)"
if [ "$got" != "$want" ]; then
  echo "bootstrap: sha256 mismatch" >&2
  echo "  want $want" >&2
  echo "  got  $got" >&2
  exit 1
fi
echo "bootstrap: sha256 ok ($got)"

mkdir -p "$dest"
tar -xzf "$tmp/bend.tar.gz" -C "$dest"
"$dest/bend/bin/bend" version
echo "bootstrap: installed at $dest"
