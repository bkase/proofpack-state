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
# The full set, or nothing. The cases below are not all reachable from
# `source` alone -- missing, readiness and the backend comparisons all need a
# receiver -- and a differential that runs half its cases and still says
# "agrees on every case" is worse than one that refuses to start. The stamp
# carries the identity `fixtures/make_repos.sh` builds, so a set left over
# from an older version of that script is caught too.
for r in source receiver empty; do
  if [ ! -d "$repos/$r" ]; then
    echo "differential: $repos/$r is missing; run fixtures/make_repos.sh" >&2
    exit 2
  fi
done
if [ ! -f "$repos/FIXTURE" ]; then
  echo "differential: $repos has no FIXTURE stamp; it predates the current" \
    "fixtures/make_repos.sh. Move it aside and run that script." >&2
  exit 2
fi
want_head="$(awk '$1 == "source" { print $2 }' "$repos/FIXTURE")"
have_head="$(git -C "$repos/source" rev-parse -q --verify refs/heads/main \
  || true)"
if [ "$want_head" != "$have_head" ]; then
  echo "differential: $repos/source is ${have_head:-absent}, but its stamp" \
    "says $want_head; the fixtures are inconsistent." >&2
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
  # An empty side is never a legitimate expectation here: every case compares
  # a count, a byte total, an exit status, a class name or a JSON object. If
  # one side is empty the command that produced it failed, and comparing
  # empty to empty would report "ok" for a case that never ran.
  if [ -z "$2" ] || [ -z "$3" ]; then
    echo "NO RESULT expected '$2', got '$3'"
    fail=1
    return
  fi
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
  # This section closes over a root, so a fixture without one has no case
  # here -- it is still exercised below as an inventory. Skipping it loudly
  # rather than running git against a missing ref keeps the empty results
  # that would follow from being compared to each other.
  if ! git -C "$r" rev-parse --verify -q refs/heads/main > /dev/null; then
    echo "$repo: no refs/heads/main, not a closure case"
    continue
  fi
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

# --- native against Metal over identical plans (SPEC 11.1) ----------------
# `pp` already cross-checks the leaf-job plan against the tree reduction on
# every query and reports `actual_backend: "disagreed"` if they differ. This
# checks the stronger thing: the whole result is identical whichever backend
# ran it, and a forced Metal run fails rather than falls back when no GPU is
# available.
if [ -d "$repos/receiver" ]; then
  echo "backends:"
  S="$repos/source"; R="$repos/receiver"
  base="git missing --repo $S --root refs/heads/main --have-repo $R"
  c=$("$pp" $base --backend cpu   | python3 -c 'import json,sys; print(json.dumps(json.load(sys.stdin)["result"],sort_keys=True))')
  m=$("$pp" $base --backend metal | python3 -c 'import json,sys; print(json.dumps(json.load(sys.stdin)["result"],sort_keys=True))')
  if [ "$c" = "$m" ]; then
    printf '  %-46s %s\n' "cpu and metal return identical results" "ok"
  else
    printf '  %-46s\n    cpu:   %s\n    metal: %s\n' \
      "cpu and metal return identical results MISMATCH" "$c" "$m"
    fail=1
  fi
  act=$("$pp" $base --backend metal | python3 -c 'import json,sys; print(json.load(sys.stdin)["execution"]["actual_backend"])')
  disp=$("$pp" $base --backend metal | python3 -c 'import json,sys; print(json.load(sys.stdin)["execution"]["gpu_dispatches"])')
  if [ "$act" = "metal" ]; then
    check "forced metal actually dispatched" "1" "$disp"
  else
    printf '  %-46s %s\n' "forced metal" \
      "no GPU in this process (actual: $act); skipped"
  fi
  "$pp" --gpu off $base --backend metal > /dev/null 2>&1
  check "forced metal without a GPU fails, exit 2" "2" "$?"
  "$pp" --gpu off $base --backend cpu > /dev/null 2>&1
  check "cpu without a GPU still answers, exit 0" "0" "$?"
  "$pp" --gpu off git ready --repo "$S" --root refs/heads/main \
    --have-repo "$R" > /dev/null 2>&1
  check "ready is still a complete negative, exit 1" "1" "$?"
fi

# --- the derived store: round-trip, and rejection of corruption -----------
# SPEC 1.1's "import once": a stored generation must answer exactly what the
# import answered, and SPEC 6.5 requires structural validation on load with a
# checksum explicitly not a substitute.
store="$(mktemp -d)"
bad="$(mktemp -d)"
echo "store:"
"$pp" git import --repo "$repos/source" --root refs/heads/main \
  --as src --store "$store" > /dev/null
for mode in full tree-data; do
  a=$("$pp" git stats --repo "$repos/source" --root refs/heads/main \
    --mode "$mode" | python3 -c 'import json,sys; print(json.dumps(json.load(sys.stdin)["result"],sort_keys=True))')
  b=$("$pp" git stats --graph src --store "$store" --mode "$mode" \
    | python3 -c 'import json,sys; print(json.dumps(json.load(sys.stdin)["result"],sort_keys=True))')
  check "$mode: a stored generation answers identically" "$a" "$b"
done

cls() {  # cls <graph> -- the error class a corrupt file is rejected with
  "$pp" git stats --graph "$1" --store "$bad" 2>/dev/null \
    | python3 -c 'import json,sys
d = json.load(sys.stdin).get("error")
print(d["class"] if d else "ACCEPTED")'
}
# Each corruption is derived from the file rather than pinned to one
# fixture's object count or OID -- a pinned `sed` silently becomes a no-op on
# any other fixture, and a no-op corruption is a test that passes for the
# wrong reason. The derivation therefore refuses to write a file it did not
# actually change.
corrupt() {  # corrupt <mode> <in> <out>
  python3 -c '
import sys
mode, src, dst = sys.argv[1], sys.argv[2], sys.argv[3]
lines = open(src).read().split("\n")
out = list(lines)
first = next(i for i, l in enumerate(lines) if l.startswith("object "))
if mode == "count":
    i = next(i for i, l in enumerate(lines) if l.startswith("objects "))
    out[i] = "objects %d" % (int(lines[i].split()[1]) + 1)
elif mode == "hex":
    f = lines[first].split()
    f[1] = "Z" * len(f[1])
    out[first] = " ".join(f)
elif mode == "succ":
    f = lines[first].split()
    out[first] = " ".join(f[:4] + [str(int(f[4]) + 1)] + f[5:] + ["999999"])
elif mode == "magic":
    out[0] = "not a proofpack store"
else:
    sys.exit("unknown corruption " + mode)
if out == lines:
    sys.exit("corruption " + mode + " changed nothing")
open(dst, "w").write("\n".join(out))
' "$1" "$2" "$3"
}
for c in count hex succ magic; do
  if corrupt "$c" "$store/src.pps" "$bad/$c.pps"; then
    check "a corrupt store is rejected ($c)" "CorruptIndex" "$(cls $c)"
  else
    echo "  could not build the $c corruption -- the store format moved"
    fail=1
  fi
done
check "an absent graph is UnknownRoot" "UnknownRoot" \
  "$("$pp" git stats --graph nope --store "$store" 2>/dev/null \
     | python3 -c 'import json,sys; print(json.load(sys.stdin)["error"]["class"])')"

echo
if [ "$fail" -eq 0 ]; then
  echo "differential: pp agrees with git plumbing on every case"
else
  echo "differential: MISMATCHES found"
fi
exit "$fail"
