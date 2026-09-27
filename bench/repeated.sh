#!/usr/bin/env bash
# The repeated Git-state workload of SPEC 11.4, measured the way SPEC 11.3
# requires: interleaved trials in both orders, medians rather than single
# runs, and an A-versus-A control so the reader can see the noise floor.
#
# One requirement, many inventories -- the shape a cache-placement or
# worker-readiness question actually has. Two ways of answering it, computing
# the same answer:
#
#   baseline   competent Git plumbing, per cell: `rev-list --objects` for the
#              requirement (bitmap-assisted where a bitmap exists),
#              `cat-file --batch-all-objects` for the inventory, `comm` for
#              the difference, and `cat-file --batch-check` over the
#              difference for the logical payload bytes. Git re-traverses for
#              every cell, which is what a tool that only wraps `rev-list`
#              would do.
#
#   pp         one `pp git matrix` that loads the stored generation once and
#              answers every cell from it. The import is timed separately and
#              reported, never folded in: SPEC 11.3 requires preprocessing to
#              be counted.
#
# Usage: bench/repeated.sh <source-repo> [<receivers-dir>] [<cells>] [<trials>]
set -uo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
pp="$root/build/pp"
src="${1:?usage: bench/repeated.sh <source-repo> [<receivers-dir>] [<cells>] [<trials>]}"
recv="${2:-}"
cells="${3:-8}"
trials="${4:-5}"

[ -x "$pp" ] || { echo "bench: build/pp is missing" >&2; exit 2; }

work="$(mktemp -d)"
store="$work/store"

if [ -z "$recv" ]; then
  recv="$work/receivers"
  mkdir -p "$recv"
  echo "building $cells receivers from $src ..."
  i=0
  while [ "$i" -lt "$cells" ]; do
    r="$recv/r$i"
    git init -q --bare -b main "$r"
    git -C "$r" fetch -q --no-tags "$src" \
      "$(git -C "$src" rev-parse "refs/heads/main~$((i * 37))")":refs/heads/main \
      2>/dev/null || true
    i=$((i + 1))
  done
fi

haves=()
for r in "$recv"/*; do
  [ -d "$r" ] || continue
  haves+=(--have-repo "$r")
done
n=$(( ${#haves[@]} / 2 ))

now() { python3 -c 'import time; print(time.time())'; }

run_baseline() {
  for r in "$recv"/*; do
    [ -d "$r" ] || continue
    git -C "$src" rev-list --objects --no-object-names refs/heads/main \
      | sort -u > "$work/want"
    git -C "$r" cat-file --batch-all-objects --batch-check --unordered \
      2>/dev/null | awk '{print $1}' | sort -u > "$work/have"
    comm -23 "$work/want" "$work/have" > "$work/miss"
    wc -l < "$work/miss" > /dev/null
    git -C "$src" cat-file --batch-check < "$work/miss" \
      | awk '{s+=$3} END {printf "%d", s}' > /dev/null
  done
}

run_pp() {
  "$pp" git matrix --graph bench --store "$store" "${haves[@]}" \
    > "$work/matrix.json"
}

timeit() {  # timeit <fn>
  local t0 t1
  t0=$(now); "$1" > /dev/null 2>&1; t1=$(now)
  python3 -c "print('%.4f' % ($t1 - $t0))"
}

echo
echo "source     $src"
echo "objects    $(git -C "$src" rev-list --objects --no-object-names \
  refs/heads/main | sort -u | wc -l | tr -d ' ') reachable from refs/heads/main"
echo "cells      $n"
echo "trials     $trials interleaved pairs, both orders"
echo

t0=$(now)
"$pp" git import --repo "$src" --root refs/heads/main --as bench \
  --store "$store" > /dev/null
t1=$(now)
imp=$(python3 -c "print('%.2f' % ($t1 - $t0))")
echo "import     $imp s, once, $(du -h "$store"/bench.pps | cut -f1) on disk"
echo

# Warm both sides once so neither pays the first page fault.
run_baseline > /dev/null 2>&1
run_pp > /dev/null 2>&1

b=(); p=(); aa=()
i=0
while [ "$i" -lt "$trials" ]; do
  if [ $((i % 2)) -eq 0 ]; then
    b+=("$(timeit run_baseline)"); p+=("$(timeit run_pp)")
  else
    p+=("$(timeit run_pp)"); b+=("$(timeit run_baseline)")
  fi
  aa+=("$(timeit run_baseline)")
  i=$((i + 1))
done

python3 - "$work/matrix.json" "$n" "$imp" "${#b[@]}" "${b[@]}" "${p[@]}" \
  "${aa[@]}" <<'PY'
import json, statistics, sys
mj, n, imp, k = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
vals = [float(x) for x in sys.argv[5:]]
b, p, aa = vals[:k], vals[k:2 * k], vals[2 * k:]


def line(name, xs):
    print("  %-10s median %.3f s   min %.3f   max %.3f   per cell %.4f s"
          % (name, statistics.median(xs), min(xs), max(xs),
             statistics.median(xs) / n))


print("wall clock for %d cells:" % n)
line("baseline", b)
line("pp", p)
line("A-vs-A", aa)
bm, pm, am = statistics.median(b), statistics.median(p), statistics.median(aa)
noise = abs(am - bm) / bm * 100
print()
print("  the A-vs-A control differs from the baseline by %.1f%%, which is the"
      % noise)
print("  noise floor on this machine; a claim smaller than that is not a"
      " claim.")
print()
ratio = pm / bm
if abs(ratio - 1) * 100 <= noise:
    print("  pp is %.2fx the baseline, inside the noise floor: at parity."
          % ratio)
elif ratio < 1:
    print("  pp is %.2fx the baseline per cell." % ratio)
    print("  With the %.2f s import counted once, pp is ahead from cell %.0f."
          % (imp, imp / (bm / n - pm / n)))
else:
    print("  pp is %.2fx the baseline per cell -- slower. There is no"
          % ratio)
    print("  performance claim to make on this workload, and SPEC 11.4 says")
    print("  to ship the useful native product and say so rather than")
    print("  fabricate one.")

d = json.load(open(mj))["result"]
print()
print("answer     %s objects required, %s logical payload bytes"
      % (d["required"]["objects"], d["required"]["logical_payload_bytes"]))
print("           %s cells, %s distinct inventories after deduplication"
      % (d["cells"], d["distinct_inventories"]))
PY
echo
echo "workspace  $work"
