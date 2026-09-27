#!/usr/bin/env bash
# Build the Git fixtures the tests run against, deterministically.
#
#   source/      the full case: a merge, a tag to a tag, a symlink, a
#                zero-byte blob, a non-UTF-8 file name, a gitlink, and a
#                history whose old blobs are unreachable from the current tree
#   receiver/    a partial copy of source holding only part of the objects
#   empty/       a repository with one empty root commit
#
# Fixed identity and dates, so object ids are the same on every machine and a
# test can name one.
#
# This script never deletes anything. If the output directory already exists
# it stops and says so; remove it yourself to rebuild.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
out="${1:-${PP_FIXTURES:-$root/repos}}"

if [ -e "$out" ]; then
  echo "fixtures: $out already exists; delete it yourself to rebuild" >&2
  exit 0
fi
mkdir -p "$out"

export GIT_AUTHOR_NAME=ProofPack GIT_AUTHOR_EMAIL=pp@example.invalid
export GIT_COMMITTER_NAME=ProofPack GIT_COMMITTER_EMAIL=pp@example.invalid
export GIT_AUTHOR_DATE="2026-01-01T00:00:00+0000"
export GIT_COMMITTER_DATE="2026-01-01T00:00:00+0000"
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null

g() { git -C "$out/source" "$@"; }

git init -q -b main "$out/source"
g config user.name ProofPack
g config user.email pp@example.invalid

# --- root commit: a nested tree, a zero-byte blob, a symlink --------------
mkdir -p "$out/source/lib/deep"
printf 'alpha\n' > "$out/source/a.txt"
: > "$out/source/empty.bin"
printf 'deep\n' > "$out/source/lib/deep/d.txt"
ln -sf a.txt "$out/source/link"
g add -A
g commit -q -m "root"

# --- a commit whose blob is later replaced, so history keeps a blob the
#     current tree does not need ------------------------------------------
printf 'alpha v2\n' > "$out/source/a.txt"
g add -A
g commit -q -m "second"

# --- a side branch and a merge, for diamond sharing and merge parents -----
g checkout -q -b side HEAD~1
printf 'side\n' > "$out/source/s.txt"
g add -A
g commit -q -m "side"
g checkout -q main
g merge -q --no-ff -m "merge" side

# --- a file name that is not valid UTF-8 ----------------------------------
# Added through the index rather than the filesystem: APFS rejects a name that
# is not valid UTF-8, but a Git tree entry name is raw bytes and the parser
# has to handle it (SPEC 8.4).
rawblob="$(printf 'raw\n' | g hash-object -w --stdin)"
g update-index --add --cacheinfo "100644,$rawblob,$(printf 'na\xffme.txt')"
g commit -q -m "non-utf8 name"

# --- a gitlink: a submodule entry recorded without the submodule present ---
sub="$(printf 'tree 4b825dc642cb6eb9a060e54bf8d69288fbee4904\nauthor ProofPack <pp@example.invalid> 1767225600 +0000\ncommitter ProofPack <pp@example.invalid> 1767225600 +0000\n\nsubmodule head\n' | g hash-object -w -t commit --literally --stdin)"
g update-index --add --cacheinfo 160000,"$sub",vendor/sub
g write-tree > /dev/null
g commit -q -m "gitlink"

# --- tags: lightweight, annotated, tag-to-tag, tag-to-tree, tag-to-blob ---
g tag light
g tag -a -m "annotated" annot "$(g rev-parse HEAD)"
g tag -a -m "tag of a tag" chained "$(g rev-parse annot)"
g tag -a -m "tag of a tree" treetag "$(g rev-parse HEAD^{tree})"
g tag -a -m "tag of a blob" blobtag "$(g rev-parse HEAD:a.txt)"

# --- receiver: a store holding only the objects of an older commit --------
# Bare, so nothing is checked out and the fetch can write refs/heads/main
# directly. A receiver is an object store, not a worktree (SPEC 8.1).
git init -q --bare -b main "$out/receiver"
git -C "$out/receiver" fetch -q --no-tags "$out/source" \
  "$(g rev-parse HEAD~3)":refs/heads/main

# --- empty: one commit with an empty tree ---------------------------------
git init -q -b main "$out/empty"
git -C "$out/empty" config user.name ProofPack
git -C "$out/empty" config user.email pp@example.invalid
git -C "$out/empty" commit -q --allow-empty -m "empty"

echo "fixtures built in $out"
for r in source receiver empty; do
  printf '  %-9s %s objects, main %s\n' "$r" \
    "$(git -C "$out/$r" cat-file --batch-all-objects --batch-check \
        --unordered 2>/dev/null | wc -l | tr -d ' ')" \
    "$(git -C "$out/$r" rev-parse --short main)"
done
