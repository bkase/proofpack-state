#!/usr/bin/env bash
# The release gate (SPEC 10.3). Runs, in order:
#
#   1. every module typechecks through one root-level entry
#   2. `bend PROOF.bend` -- fails while any law in LAWS.bend is open or false
#   3. `bend PROOF.bend --verdict` -- rechecks every law with the proven BendTT
#      kernel and fails if anything reaches unsafe or foreign code, when Lean
#      is available
#   4. the executable checks in tests.bend
#   5. the Git differential against independent plumbing
#   6. a build of `pp` itself
#
# Every step writes its output under build/gate/ so the run is an artifact
# rather than a transcript.
set -uo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
out="$root/build/gate"
mkdir -p "$out"
export PATH="$HOME/.elan/bin:$PATH"

fail=0
step() {
  local name="$1"; shift
  printf '%-34s ' "$name"
  if "$@" > "$out/$name.log" 2>&1; then
    echo ok
  else
    echo FAILED
    fail=1
    sed 's/^/    /' "$out/$name.log" | head -20
  fi
}

step typecheck            "$root/tools/check.sh"
step proof                "$root/tools/bend" PROOF.bend
step bendtt               "$root/tools/bend" PROOF.bend -o "$out/PROOF.bendtt"

printf '%-34s ' "proof-verdict"
if command -v lean > /dev/null; then
  if "$root/tools/bend" PROOF.bend --verdict > "$out/proof-verdict.log" 2>&1; then
    echo "ok ($(lean --version | head -1))"
  else
    echo FAILED; fail=1; sed 's/^/    /' "$out/proof-verdict.log" | head -20
  fi
else
  echo "skipped (no lean on PATH; --verdict needs the BendTT kernel)"
fi

step build-tests          "$root/tools/bend" tests.bend -o "$root/build/tests"
step tests                "$root/build/tests"
step build-pp             "$root/tools/bend" pp.bend -o "$root/build/pp"
step git-differential     "$root/tools/differential.sh"

echo
if [ "$fail" -eq 0 ]; then
  echo "gate: all steps passed; logs in $out"
else
  echo "gate: FAILED; logs in $out"
fi
exit "$fail"
