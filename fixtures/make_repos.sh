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
# This script never deletes anything. It builds each of the three
# repositories only if that repository is absent, so running it again
# completes a partial set instead of refusing the whole directory -- a
# half-built set is worse than none, because the differential then runs its
# weaker cases and still reports success. To rebuild one from scratch, delete
# that repository yourself and run this again.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
out="${1:-${PP_FIXTURES:-$root/repos}}"

mkdir -p "$out"

# The identity of a correctly built `source`, and the version of this script
# that produces it. Object ids here are deterministic -- fixed identity, fixed
# dates -- so a `source` whose main points anywhere else was built by an older
# version of this script and is missing cases: the non-UTF-8 file name, the
# gitlink and the five tags were all added after the first version. Naming the
# expected id turns that into a refusal instead of a differential that quietly
# runs only its weaker half.
fixture_version=2
fixture_head=1aa22346fa57065a53320af0d443640086306138

export GIT_AUTHOR_NAME=ProofPack GIT_AUTHOR_EMAIL=pp@example.invalid
export GIT_COMMITTER_NAME=ProofPack GIT_COMMITTER_EMAIL=pp@example.invalid
export GIT_AUTHOR_DATE="2026-01-01T00:00:00+0000"
export GIT_COMMITTER_DATE="2026-01-01T00:00:00+0000"
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null

g() { git -C "$out/source" "$@"; }

if [ -e "$out/source" ]; then
  have="$(git -C "$out/source" rev-parse -q --verify refs/heads/main || true)"
  if [ "$have" != "$fixture_head" ]; then
    echo "fixtures: $out/source is stale." >&2
    echo "  its main is ${have:-absent}, and v$fixture_version builds" \
      "$fixture_head." >&2
    echo "  delete $out/source (and $out/receiver, derived from it) and run" \
      "this again." >&2
    exit 1
  fi
  echo "  source     already present and current, left alone"
else
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
fi

# --- receiver: a store holding only the objects of an older commit --------
# Bare, so nothing is checked out and the fetch can write refs/heads/main
# directly. A receiver is an object store, not a worktree (SPEC 8.1).
if [ -e "$out/receiver" ]; then
  echo "  receiver   already present, left alone"
else
  git init -q --bare -b main "$out/receiver"
  git -C "$out/receiver" fetch -q --no-tags "$out/source" \
    "$(g rev-parse HEAD~3)":refs/heads/main
fi

# --- empty: one commit with an empty tree ---------------------------------
if [ -e "$out/empty" ]; then
  echo "  empty      already present, left alone"
else
  git init -q -b main "$out/empty"
  git -C "$out/empty" config user.name ProofPack
  git -C "$out/empty" config user.email pp@example.invalid
  git -C "$out/empty" commit -q --allow-empty -m "empty"
fi

built="$(git -C "$out/source" rev-parse refs/heads/main)"
if [ "$built" != "$fixture_head" ]; then
  echo "fixtures: built source main $built, expected $fixture_head." >&2
  echo "  this script changed what it builds; update fixture_head and" \
    "fixture_version." >&2
  exit 1
fi
printf 'proofpack-fixtures v%s\nsource %s\n' \
  "$fixture_version" "$fixture_head" > "$out/FIXTURE"

echo "fixtures built in $out"
for r in source receiver empty; do
  printf '  %-9s %s objects, main %s\n' "$r" \
    "$(git -C "$out/$r" cat-file --batch-all-objects --batch-check \
        --unordered 2>/dev/null | wc -l | tr -d ' ')" \
    "$(git -C "$out/$r" rev-parse --short main)"
done
