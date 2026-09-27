#!/usr/bin/env bash
# The repeated Git-state workload of SPEC 11.4, measured the way SPEC 11.3
# requires: fixed inputs, interleaved trials in both orders, medians rather
# than single runs, an A-versus-A control so the reader can see the noise
# floor, and preprocessing counted rather than hidden.
#
# The workload is one requirement against many inventories -- the shape a
# cache-placement or worker-readiness question actually has. Two ways of
# answering it, computing the same answer:
#
#   baseline   competent Git plumbing, per cell: `rev-list --objects` for the
#              requirement (bitmap-assisted where a bitmap exists),
#              `cat-file --batch-all-objects` for the inventory, `comm` for
#              the difference, and `cat-file --batch-check` over the
#              difference for the logical payload bytes. Git re-traverses the
#              requirement for every cell, which is what a tool that wraps
#              `rev-list` has to do.
#
#   pp         one `pp git matrix` that loads the stored generation once and
#              answers every cell from it.
#
# A single ratio at a single cell count would be worthless here, because the
# two sides have different shapes: pp pays a fixed cost to load the generation
# and a small cost per cell, the baseline pays no fixed cost and a large cost
# per cell. So this sweeps the cell count, reports both shapes, and reports
# where they cross -- and it checks that pp's answers match git's before it
# reports any timing at all, because a fast wrong answer is worth nothing.
#
# Usage: bench/repeated.sh <source-repo> <receivers-dir> [<trials>]
set -uo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
pp="$root/build/pp"
src="${1:?usage: bench/repeated.sh <source-repo> <receivers-dir> [<trials>]}"
recv="${2:?usage: bench/repeated.sh <source-repo> <receivers-dir> [<trials>]}"
trials="${3:-5}"

[ -x "$pp" ] || { echo "bench: build/pp is missing" >&2; exit 2; }
[ -d "$recv" ] || { echo "bench: no receivers at $recv" >&2; exit 2; }

cells=()
for r in "$recv"/r*; do
  [ -d "$r" ] || continue
  cells+=("$r")
done
n_all=${#cells[@]}
[ "$n_all" -ge 2 ] || { echo "bench: need at least two receivers" >&2; exit 2; }

work="$(mktemp -d)"
store="$work/store"
now() { python3 -c 'import time; print(time.time())'; }

# --- the requirement, once, for the baseline and for the check -------------
git -C "$src" rev-list --objects --no-object-names refs/heads/main \
  | sort -u > "$work/want"
req=$(wc -l < "$work/want" | tr -d ' ')

run_baseline() {  # run_baseline <n>
  local i=0
  while [ "$i" -lt "$1" ]; do
    git -C "$src" rev-list --objects --no-object-names refs/heads/main \
      | sort -u > "$work/w.$i"
    git -C "${cells[$i]}" cat-file --batch-all-objects --batch-check \
      --unordered 2>/dev/null | awk '{print $1}' | sort -u > "$work/h.$i"
    comm -23 "$work/w.$i" "$work/h.$i" > "$work/m.$i"
    wc -l < "$work/m.$i" > /dev/null
    git -C "$src" cat-file --batch-check < "$work/m.$i" \
      | awk '{s+=$3} END {printf "%d", s+0}' > /dev/null
    i=$((i + 1))
  done
}

pp_args() {  # pp_args <n>
  local i=0
  while [ "$i" -lt "$1" ]; do printf '%s\n' --have-repo "${cells[$i]}"
    i=$((i + 1)); done
}

run_pp() {  # run_pp <n> [<outfile>]
  local a=(); while IFS= read -r x; do a+=("$x"); done < <(pp_args "$1")
  "$pp" git matrix --graph bench --store "$store" "${a[@]}" \
    > "${2:-/dev/null}"
}

timeit() {  # timeit <fn> <n>
  local t0 t1; t0=$(now); "$1" "$2" > /dev/null 2>&1; t1=$(now)
  python3 -c "print('%.4f' % ($t1 - $t0))"
}

echo
echo "source      $src"
echo "requirement $req objects reachable from refs/heads/main"
echo "receivers   $n_all in $recv"
echo "trials      $trials interleaved pairs per cell count, both orders"
echo

t0=$(now)
"$pp" git import --repo "$src" --root refs/heads/main --as bench \
  --store "$store" > /dev/null || { echo "bench: import failed" >&2; exit 2; }
t1=$(now)
imp=$(python3 -c "print('%.2f' % ($t1 - $t0))")
echo "import      $imp s, once, $(du -h "$store"/bench.pps | cut -f1) on disk"

# --- correctness first ----------------------------------------------------
# Every cell's missing count and byte total, against git's own difference.
# Reporting a speed without this would be reporting the speed of an unknown
# computation.
run_pp "$n_all" "$work/matrix.json"
bad=0
i=0
while [ "$i" -lt "$n_all" ]; do
  git -C "${cells[$i]}" cat-file --batch-all-objects --batch-check \
    --unordered 2>/dev/null | awk '{print $1}' | sort -u > "$work/have"
  comm -23 "$work/want" "$work/have" > "$work/miss"
  gn=$(wc -l < "$work/miss" | tr -d ' ')
  gb=$(git -C "$src" cat-file --batch-check < "$work/miss" \
    | awk '{s+=$3} END {printf "%d", s+0}')
  read -r pn pb <<<"$(python3 -c "
import json, sys
r = json.load(open('$work/matrix.json'))['result']['rows'][$i]['answer']
print(r['missing']['objects'], r['missing']['logical_payload_bytes'])")"
  if [ "$gn" != "$pn" ] || [ "$gb" != "$pb" ]; then
    echo "  cell $i MISMATCH  git $gn/$gb  pp $pn/$pb"
    bad=1
  fi
  i=$((i + 1))
done
if [ "$bad" -ne 0 ]; then
  echo "bench: pp disagrees with git plumbing; no timing reported" >&2
  exit 1
fi
echo "agreement   all $n_all cells match git's own difference, objects and bytes"
echo

# --- the sweep ------------------------------------------------------------
ns=()
k=1
while [ "$k" -le "$n_all" ]; do ns+=("$k"); k=$((k * 2)); done
[ "${ns[-1]}" -eq "$n_all" ] || ns+=("$n_all")

rows=""
for n in "${ns[@]}"; do
  run_baseline "$n" > /dev/null 2>&1   # warm both sides at this size
  run_pp "$n" > /dev/null 2>&1
  bs=(); ps=()
  i=0
  while [ "$i" -lt "$trials" ]; do
    if [ $((i % 2)) -eq 0 ]; then
      bs+=("$(timeit run_baseline "$n")"); ps+=("$(timeit run_pp "$n")")
    else
      ps+=("$(timeit run_pp "$n")"); bs+=("$(timeit run_baseline "$n")")
    fi
    i=$((i + 1))
  done
  rows="$rows$n|${bs[*]}|${ps[*]}"$'\n'
done

# --- A versus A: the same side twice, to show what noise alone looks like --
aa=(); i=0
while [ "$i" -lt "$trials" ]; do
  aa+=("$(timeit run_baseline "$n_all")"); i=$((i + 1))
done

printf '%s' "$rows" | python3 -c '
import statistics as st, sys
rows = []
for line in sys.stdin.read().strip().split("\n"):
    n, b, p = line.split("|")
    rows.append((int(n), [float(x) for x in b.split()],
                 [float(x) for x in p.split()]))
aa = [float(x) for x in sys.argv[1].split()]
imp = float(sys.argv[2])

print("wall clock, median of interleaved trials:")
print("  %6s %12s %12s %10s" % ("cells", "baseline", "pp", "pp/baseline"))
for n, b, p in rows:
    bm, pm = st.median(b), st.median(p)
    print("  %6d %10.3f s %10.3f s %9.2fx" % (n, bm, pm, pm / bm))

big = rows[-1]
bm = st.median(big[1])
am = st.median(aa)
noise = abs(am - bm) / bm * 100
print()
print("  A-vs-A control at %d cells: %.3f s against %.3f s, %.1f%% apart."
      % (big[0], am, bm, noise))
print("  That is the noise floor; a difference smaller than it is not a"
      " result.")

# Shapes: fit each side as fixed + marginal * n from the smallest and
# largest cell counts measured.
lo, hi = rows[0], rows[-1]
def shape(lo_ts, hi_ts):
    a, b = st.median(lo_ts), st.median(hi_ts)
    marg = (b - a) / (hi[0] - lo[0])
    return a - marg * lo[0], marg
bf, bmarg = shape(lo[1], hi[1])
pf, pmarg = shape(lo[2], hi[2])
print()
print("what each side is made of:")
print("  baseline  %.3f s fixed + %.4f s per cell" % (bf, bmarg))
print("  pp        %.3f s fixed + %.4f s per cell" % (pf, pmarg))

print()
if pmarg < bmarg:
    cross = (pf - bf) / (bmarg - pmarg)
    print("  pp costs %.1f%% less per cell, and %.2f s more to start."
          % ((bmarg - pmarg) / bmarg * 100, pf - bf))
    print("  Predicted crossing at %.1f cells; counting the %.2f s import"
          " too, %.1f cells." % (cross, imp,
                                 (pf - bf + imp) / (bmarg - pmarg)))
    obs = [(n, st.median(p) / st.median(b)) for n, b, p in rows]
    under = [n for n, r in obs if r < 1]
    if under:
        over = [n for n, r in obs if r >= 1]
        left = max(over) if over else 0
        print("  Measured: pp is ahead from %d cells on (behind at %d)."
              % (min(under), left))
        n, r = obs[-1]
        print("  At %d cells pp is %.2fx the baseline -- %.1fx faster."
              % (n, r, 1 / r))
    else:
        print("  Measured: pp is still behind at every cell count tried, so"
              " the crossing")
        print("  above is a prediction and not a result. No speed claim.")
else:
    print("  pp costs no less per cell than the baseline, so there is no"
          " cell count")
    print("  at which it wins this workload. No speed claim to make.")
' "${aa[*]}" "$imp"

echo
echo "workspace   $work"
