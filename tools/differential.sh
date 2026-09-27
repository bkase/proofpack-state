#!/usr/bin/env bash
# The Git differential (SPEC 11.1's third independent comparison).
#
# `pp` is checked against competent Git plumbing over the same roots and the
# same semantics. The two sides are computed differently on purpose:
#
#   full       pp walks commit -> parent, commit -> tree, tree -> subtree and
#              tree -> blob itself, from raw `cat-file --batch` bodies.
#              Git's side is `rev-list --objects`, its own reachability
#              engine -- bitmap-assisted where a bitmap exists.
#
#   tree-data  pp drops the commit -> commit edges and closes what is left.
#              Git's side is `rev-parse` for the commit and its root tree,
#              plus `ls-tree -r -t` for everything under it, with gitlink
#              entries excluded because SPEC 8.2 records a submodule
#              reference without traversing into another repository.
#
# The production parser never generates both sides (SPEC 11.1).
set -uo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
repos="${PP_FIXTURES:-$root/fixtures/repos}"
pp="$root/build/pp"

if [ ! -x "$pp" ]; then
  echo "differential: build/pp is missing; run tools/bend pp.bend -o build/pp" >&2
  exit 2
fi
if [ ! -d "$repos/source" ]; then
  echo "differential: no fixtures at $repos; run fixtures/make_repos.sh" >&2
  exit 2
fi

fail=0

field() {  # field <json> <dotted path>
  python3 -c '
import json,sys
d = json.loads(sys.argv[1])
for k in sys.argv[2].split("."):
    d = d[k]
print(d)' "$1" "$2"
}

check() {  # check <label> <expected> <got>
  printf '  %-46s ' "$1"
  if [ "$2" = "$3" ]; then
    echo "ok ($3)"
  else
    echo "MISMATCH expected $2, got $3"
    fail=1
  fi
}

for repo in source receiver empty; do
  r="$repos/$repo"
  [ -d "$r" ] || continue
  echo "$repo:"

  # --- full: against git rev-list --objects ------------------------------
  want=$(git -C "$r" rev-list --objects --no-object-names refs/heads/main \
    | sort -u | wc -l | tr -d ' ')
  wantb=$(git -C "$r" rev-list --objects --no-object-names refs/heads/main \
    | sort -u | git -C "$r" cat-file --batch-check \
    | awk '{s+=$3} END {printf "%d", s}')
  got=$("$pp" git stats --repo "$r" --root refs/heads/main --mode full)
  check "full closure, object count" "$want" \
    "$(field "$got" result.required.objects)"
  check "full closure, logical payload bytes" "$wantb" \
    "$(field "$got" result.required.logical_payload_bytes)"

  # --- tree-data: against rev-parse + ls-tree -r -t ----------------------
  tdlist=$(mktemp)
  { git -C "$r" rev-parse refs/heads/main
    git -C "$r" rev-parse "refs/heads/main^{tree}"
    git -C "$r" ls-tree -r -t --full-tree refs/heads/main \
      | awk '$2 != "commit" { print $3 }'
  } | sort -u > "$tdlist"
  want=$(wc -l < "$tdlist" | tr -d ' ')
  wantb=$(git -C "$r" cat-file --batch-check < "$tdlist" \
    | awk '{s+=$3} END {printf "%d", s}')
  got=$("$pp" git stats --repo "$r" --root refs/heads/main --mode tree-data)
  check "tree-data closure, object count" "$want" \
    "$(field "$got" result.required.objects)"
  check "tree-data closure, logical payload bytes" "$wantb" \
    "$(field "$got" result.required.logical_payload_bytes)"
  rm -f "$tdlist"

  # --- inventory: against cat-file --batch-all-objects --------------------
  want=$(git -C "$r" cat-file --batch-all-objects --batch-check --unordered \
    | wc -l | tr -d ' ')
  got=$("$pp" git inventory --repo "$r" --root refs/heads/main \
    --have-repo "$r")
  check "inventory, observed total" "$want" \
    "$(field "$got" result.observed.observed_total)"

  # --- the certificate accepts this repository's own closure -------------
  got=$("$pp" git verify --repo "$r" --root refs/heads/main)
  check "closure certificate accepted" "True" \
    "$(field "$got" result.certificate_accepted)"
done

# --- missing: the source's requirement minus what the receiver reports ----
if [ -d "$repos/receiver" ]; then
  echo "source against receiver:"
  S="$repos/source"; R="$repos/receiver"
  for mode in full tree-data; do
    got=$("$pp" git missing --repo "$S" --root refs/heads/main \
      --mode "$mode" --have-repo "$R")
    req=$(field "$got" result.required.objects)
    mis=$(field "$got" result.missing.objects)
    rdy=$(field "$got" result.ready_at_observation)
    # `missing` is exactly what `--output oids` lists, and readiness is an
    # empty missing set -- law M-02, checked against the running binary.
    n=$("$pp" git missing --repo "$S" --root refs/heads/main \
      --mode "$mode" --have-repo "$R" --output oids \
      | python3 -c 'import json,sys; print(len(json.load(sys.stdin)["result"]["missing_objects"]))')
    check "$mode: the missing list has the missing count" "$mis" "$n"
    if [ "$mis" = "0" ]; then want=True; else want=False; fi
    check "$mode: readiness is an empty missing set" "$want" "$rdy"
    # Every missing object must really be absent from the receiver.
    absent=$("$pp" git missing --repo "$S" --root refs/heads/main \
      --mode "$mode" --have-repo "$R" --output oids \
      | python3 -c 'import json,sys; print("\n".join(json.load(sys.stdin)["result"]["missing_objects"]))' \
      | while read -r o; do
          git -C "$R" cat-file -e "$o" 2>/dev/null && echo present
        done | grep -c present)
    check "$mode: no reported-missing object is present" "0" "$absent"
    printf '  %-46s %s required, %s missing\n' "$mode" "$req" "$mis"
  done
fi

echo
if [ "$fail" -eq 0 ]; then
  echo "differential: pp agrees with git plumbing on every case"
else
  echo "differential: MISMATCHES found"
fi
exit "$fail"
