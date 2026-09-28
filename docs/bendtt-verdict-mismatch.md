# `bend --verdict` reports a TypeScript/BendTT-kernel mismatch on a conversion check over a large term

Bend 2.0.32. `bend file.bend` accepts the file, `bend file.bend -o file.bendtt`
translates it, and `bend file.bend --verdict` then refuses it with:

```
SOME PROOFS FAIL
Sorry - this is a mismatch between the TypeScript implementation, and the
formalized BendTT kernel. Your proofs may or may not be correct, and we
cannot validate them yet. This will be addressed in a future update.
Meanwhile, feel free to open an issue to report this bug.
```

It is size-triggered and deterministic, and the boundary is sharp: the same
file with one fewer list element is accepted.

**This is not a soundness bug.** `--verdict` refuses to validate a file rather
than accepting a false one, so it is an incompleteness/coverage gap, not a
"⊥ zero day", and it is not eligible for the $10k bounty on proving a
falsehood. It matters because a project that uses `--verdict` as its release
gate cannot pass the gate, with no indication of which definition is at fault.

## Environment

| | |
|---|---|
| Bend | 2.0.32 (`bendlang/bend` `4f856f61392425f25f5798e8773c50a18cc3ae51`) |
| Artifact | `bend-2.0.32-darwin-arm64.tar.gz`, sha256 `d7debc002f59264f648dc94e45c2a9fab23e4b1ee0a390bf2acd8b1673e0cf55` |
| Lean | 4.34.0 (`leanprover/lean4:v4.34.0`, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`) |
| Host | macOS, `Darwin arm64` |

## Minimal reproduction

`docs/repro/verdict-mismatch-fails-851.bend` — self-contained, imports only
`Base`:

```bend
import Base

def and_both(+p: Bool, +q: Bool,
  +a: {p == True{} : Bool}, +b: {q == True{} : Bool})
  -> {Bool.and(p, q) == True{} : Bool}:
  match p:
    case True{}:
      b
    case False{}:
      a

def ones(+k: Nat) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      Con{1, ones(j)}

def allone(+xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(U32.is_eq(h, 1), allone(t))

law ones_ok:
  for +k: Nat
  {allone(ones(k)) == True{} : Bool}

def ones_ok(k):
  match k:
    case 0n:
      {==}
    case 1n+j:
      and_both(U32.is_eq(1, 1), allone(ones(j)), {==}, ones_ok(j))

def idl(xs: List<&2, U32>) -> List<&2, U32>:
  xs

def p() -> {allone(idl(ones(851n))) == True{} : Bool}:
  ones_ok(851n)
```

Run:

```sh
bend verdict-mismatch-fails-851.bend            # ALL PROOFS CHECK
bend verdict-mismatch-fails-851.bend -o out.bendtt   # succeeds, 31 KB
bend verdict-mismatch-fails-851.bend --verdict  # SOME PROOFS FAIL + the message
```

Change `851n` to `850n` in both places
(`docs/repro/verdict-mismatch-passes-850.bend`) and `--verdict` prints
`ALL PROOFS CHECK`.

`docs/repro/gen-verdict-mismatch.py` regenerates the file at any size, so the
boundary can be re-measured without editing by hand:

```sh
python3 gen-verdict-mismatch.py 851 > t.bend && bend t.bend --verdict
python3 gen-verdict-mismatch.py 428 --cells 2   # two cells per step
python3 gen-verdict-mismatch.py 4096 --no-wrapper   # the control; accepted
```

## What triggers it

Two ingredients, both required:

1. **A conversion check.** `p`'s stated type is
   `{allone(idl(ones(851n))) == True{}}`; the proof `ones_ok(851n)` has type
   `{allone(ones(851n)) == True{}}`. Those are definitionally equal but not
   syntactically equal, so the checker has to convert.
2. **A term above a size threshold.** With this payload the threshold is
   exactly 851 list cells.

Remove either and it passes.
`docs/repro/verdict-mismatch-control-no-conversion.bend` is the same file
with `idl` deleted, so the two types are *syntactically*
identical and no conversion is needed — that version is accepted at 851, and
`docs/repro/verdict-mismatch-control-no-conversion-8192.bend` is accepted at
**8192**, an order of magnitude more normalization work. So the trigger is
the conversion, not the size of the proof or of the proposition on its own.

The wrapper is only the cheapest way to force the conversion. Any of these
reproduce identically:

```bend
# via a function defined by a match on Bool
def pick(c: Bool) -> List<&2, U32>:
  match c:
    case True{}:  ones(851n)
    case False{}: Nil{}

def p() -> {allone(pick(True{})) == True{} : Bool}:
  ones_ok(851n)
```

```bend
# via a match in the proof itself, goal mentioning the scrutinee
def f(c: C) -> List<&2, U32>: ...
def p(+c: C) -> {allone(f(c)) == True{} : Bool}:
  match c: ...
```

Nesting more wrappers (`idl(idl(idl(idl(ones(k)))))`) does **not** move the
threshold, so it is not a per-redex budget being consumed.

One more control narrows it usefully.
`docs/repro/verdict-mismatch-equation-law-ok.bend` proves
`{idl(ones(4096n)) == ones(4096n) : List<&2, U32>}` by `{==}` — the *same*
reduction over a list nearly five times past the threshold — and is
**accepted**. So normalizing a term that size is not itself the problem.
What fails is converting two *types* over a term that size.

## The threshold

Deterministic. Every row below, and both controls, were run twice and gave
the same answer each time.

| payload | cells built per recursive step | last accepted | first rejected |
|---|---|---|---|
| `ones` | 1 | 850 cells (`k = 850n`) | 851 cells (`k = 851n`) |
| `twos` | 2 | 854 cells (`k = 427n`) | 856 cells (`k = 428n`) |

`twos` is the same file with `Con{1, Con{1, twos(j)}}` in the recursive arm
(`docs/repro/verdict-mismatch-{passes-twos-427,fails-twos-428}.bend`). Halving
the number of recursive steps while keeping the number of cells the same
leaves the boundary where it was, so the budget tracks the **size of the
normalized term**, not the depth of the recursion that built it. ~850–855
cons cells of `List<&2, U32>` is where it sits for these payloads.

The emitted BendTT is essentially the same size on either side of the
boundary — 31307 bytes at 850, 31337 at 851 — so nothing about the
*translation* changes at the cliff. The translation is also not what fails:
`-o out.bendtt` succeeds on the rejected file.

## Where it was found

Not synthesised. It appeared in
[ProofPack State](../README.md), which uses `bend PROOF.bend --verdict` as one
step of its release gate, when this definition was added:

```bend
def Ords.asc_leaf_diff.full(+b: S.PSet,
  +vb: {S.PSet.valid.leaf(b) == True{} : Bool})
  -> {Ol.Ords.asc(S.PSet.leaf_diff_members.full(b)) == True{} : Bool}:
  match b:
    case S.PZero{}:
      To.Ords.asc_full_leaf()
    case S.PFull{}:
      {==}
    case S.PBranch{l, h}:
      To.Ords.asc_full_leaf()
    case S.PSparse{bo}:
      Ords.asc_diff(S.PSet.range(4096n, 4095, Nil{}), bo,
        To.Ords.asc_full_leaf())
    case S.PDense{bw}:
      Ords.asc_diff_members(Wo.Words.ones(128n), bw, {==})
```

The stated type mentions `S.PSet.leaf_diff_members.full(b)`, which is defined
by a match, so every arm needs a conversion; three arms convert against
`S.PSet.range(4096n, 4095, Nil{})`, a 4096-cell list. That is the same shape
as the minimal case, well past the threshold.

Two properties of the real case made this expensive to diagnose, and are worth
fixing independently of the underlying bug:

* **The message names no definition.** A file with several hundred definitions
  gives one line of output and no location, so the only way to find the
  offending one is bisection by hand.
* **The file still translates.** `-o PROOF.bendtt` succeeds, so the usual
  "did it even compile" check does not narrow anything.

## Suggested next steps for a fix

The observable is that the TypeScript implementation and the Lean kernel
disagree on a conversion check once the term crosses a size threshold, while
agreeing below it. The two places that would explain that shape:

1. A **fuel / step budget** in one of the two conversion checkers but not the
   other (or a different budget in each), so that one gives up and the two
   answers diverge. A budget would explain the sharp, deterministic boundary
   and the fact that it tracks normalized-term size rather than recursion
   depth.
2. A **representation limit** in the term encoding handed to the kernel —
   something that saturates around a thousand nodes.

A useful first experiment: instrument whichever side reports the mismatch to
print the two terms it was comparing and the definition being checked. That
alone would turn this class of report from "bisect a few hundred definitions"
into a one-line diagnosis.

## Workaround

Do the reduction by an explicit rewrite instead of leaving it to the checker,
so the two types are syntactically equal and no conversion happens. State the
one-step reduction as its own law — that law is accepted, because proving
`{f(c) == g : T}` by `{==}` is not the same request as converting a *type* —
and rewrite with `Equal.sym` of it before supplying the proof:

```bend
law PSet.lfd_zero_eq:
  {S.PSet.leaf_diff_members.full(S.PZero{})
    == S.PSet.range(4096n, 4095, Nil{}) : List<&2, U32>}

def PSet.lfd_zero_eq():
  {==}

...
    case S.PZero{}:
      %Equal.sym(List<&2, U32>,
        S.PSet.leaf_diff_members.full(S.PZero{}),
        S.PSet.range(4096n, 4095, Nil{}), PSet.lfd_zero_eq())
        : {Ol.Ords.asc(_) == True{} : Bool}
      To.Ords.asc_full_leaf()
```

The direction matters: rewriting the other way leaves the conversion in place
and the file is still rejected. `proofs/ascdiff.bend` in this repository is the
worked example, with all four arms done this way.

The cost is that every reduction step over a large concrete term has to be
named and rewritten by hand, which is exactly the bookkeeping a conversion
check exists to avoid.
