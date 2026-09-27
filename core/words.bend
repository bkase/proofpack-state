# core/words.bend -- word-list tiles.
#
# A tile is the flat shape a leaf kernel walks: a cons list of `U32` words,
# owned by the job that reads it. docs/evidence/T01.md is why it is a list and
# why it is owned -- handing one host-built list to every lane costs an atomic
# per operand per fork level and ran ~12x slower, while a def that only
# matches its list compiles to a native tail loop with no counts at all.
#
# A missing word reads as zero: `Words.bit` past the end is False, and the
# binary operations treat a short operand as zero-padded. That is what makes
# the laws in proofs/words.bend unconditional rather than length-indexed.

import Base
import ./count.bend as C
import ./word.bend as W

# 4096 ordinals to a leaf = 128 logical U32 words (SPEC 5.2). A benchmark
# parameter, not a semantic constant: nothing below reads it.
def Words.per_leaf() -> Nat:
  128n

def Words.leaf_bits() -> Nat:
  4096n

# ---------------------------------------------------------------------------
# Reading one bit.
# ---------------------------------------------------------------------------

def Nat.is_one(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      True{}

# Bit `b` of one word, with native instructions only: `U32.shrn` is `b`
# shifts, `U32.and` and `U32.to_nat` one each. `U32.bit` is the proof-side
# twin; `Words.test_spec` in proofs/words.bend is that they agree.
def U32.test(+w: U32, b: Nat) -> Bool:
  Nat.is_one(W.U32.low(U32.shrn(w, b)))

def Words.at(ws: List<&2, U32>, i: Nat, b: Nat) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{w, t}:
      match i:
        case 0n:
          U32.test(w, b)
        case 1n+j:
          Words.at(t, j, b)

# Bit `x` of a tile: word x>>5, bit x&31.
def Words.bit(ws: List<&2, U32>, +x: U32) -> Bool:
  Words.at(ws, U32.to_nat(U32.shrn(x, 5n)), U32.to_nat(U32.and(x, 31)))

# ---------------------------------------------------------------------------
# Pointwise operations. A short operand is zero-padded, so `diff` keeps the
# rest of `a` and `and` stops.
# ---------------------------------------------------------------------------

def Words.and(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  match a:
    case Nil{}:
      Nil{}
    case Con{ah, at}:
      match b:
        case Nil{}:
          Nil{}
        case Con{bh, bt}:
          U32.and(ah, bh) <> Words.and(at, bt)

def Words.or(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  match a:
    case Nil{}:
      b
    case Con{ah, at}:
      match b:
        case Nil{}:
          Con{ah, at}
        case Con{bh, bt}:
          U32.or(ah, bh) <> Words.or(at, bt)

def Words.diff(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  match a:
    case Nil{}:
      Nil{}
    case Con{ah, at}:
      match b:
        case Nil{}:
          Con{ah, at}
        case Con{bh, bt}:
          W.U32.diff(ah, bh) <> Words.diff(at, bt)

# ---------------------------------------------------------------------------
# Reductions. These are the flat loops: one match, native arithmetic, a tail
# call. Nothing here allocates.
# ---------------------------------------------------------------------------

def Words.count.go(ws: List<&2, U32>, acc: Nat) -> Nat:
  match ws:
    case Nil{}:
      acc
    case Con{w, t}:
      Words.count.go(t, Nat.add(W.U32.popcount(w), acc))

def Words.count(ws: List<&2, U32>) -> Nat:
  Words.count.go(ws, 0n)

# The fused kernel of SPEC 7.2: popcount(required AND NOT have), accumulated
# over a tile, with no intermediate difference tile allocated.
def Words.diff_count.go(a: List<&2, U32>, b: List<&2, U32>, acc: Nat) -> Nat:
  match a:
    case Nil{}:
      acc
    case Con{ah, at}:
      match b:
        case Nil{}:
          Words.count.go(Con{ah, at}, acc)
        case Con{bh, bt}:
          Words.diff_count.go(at, bt,
            Nat.add(W.U32.popcount(W.U32.diff(ah, bh)), acc))

def Words.diff_count(a: List<&2, U32>, b: List<&2, U32>) -> Nat:
  Words.diff_count.go(a, b, 0n)

def Words.any.go(ws: List<&2, U32>, found: Bool) -> Bool:
  match ws:
    case Nil{}:
      found
    case Con{w, t}:
      match found:
        case True{}:
          True{}
        case False{}:
          Words.any.go(t, Bool.not(U32.is_zero(w)))

# True when the tile has at least one member. `IsEmpty` must not pay to count
# every result (SPEC 4.3), so this stops at the first non-zero word: the
# `True` arm drops the rest of the list instead of walking it.
def Words.any(ws: List<&2, U32>) -> Bool:
  Words.any.go(ws, False{})

# The same early exit over a difference: is anything required and not had?
def Words.diff_any.go(a: List<&2, U32>, b: List<&2, U32>, found: Bool) ->
  Bool:
  match a:
    case Nil{}:
      found
    case Con{ah, at}:
      match b:
        case Nil{}:
          Words.any.go(Con{ah, at}, found)
        case Con{bh, bt}:
          match found:
            case True{}:
              True{}
            case False{}:
              Words.diff_any.go(at, bt,
                Bool.not(U32.is_zero(W.U32.diff(ah, bh))))

def Words.diff_any(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  Words.diff_any.go(a, b, False{})

# ---------------------------------------------------------------------------
# Building tiles.
# ---------------------------------------------------------------------------

def Words.zeros(+n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      0 <> Words.zeros(p)

def Words.ones(+n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      4294967295 <> Words.ones(p)

def Words.set.at(ws: List<&2, U32>, i: Nat, b: Nat) -> List<&2, U32>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, t}:
      match i:
        case 0n:
          U32.or(w, U32.shln(1, b)) <> t
        case 1n+j:
          w <> Words.set.at(t, j, b)

def Words.set(ws: List<&2, U32>, +x: U32) -> List<&2, U32>:
  Words.set.at(ws, U32.to_nat(U32.shrn(x, 5n)), U32.to_nat(U32.and(x, 31)))

# ---------------------------------------------------------------------------
# Enumeration. Walking a tile once, low bit to high, shifting the word down as
# it goes: 32 native steps a word, no indexing and no `shrn`. The list comes
# back descending and is reversed once at the end rather than per word.
# ---------------------------------------------------------------------------

def Words.cons_if(b: Bool, x: U32, xs: List<&2, U32>) -> List<&2, U32>:
  match b:
    case False{}:
      xs
    case True{}:
      x <> xs

def Words.bits_rev(+k: Nat, +w: U32, +ord: U32, acc: List<&2, U32>) ->
  List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+j:
      Words.bits_rev(j, U32.shr(w), (ord + 1 : U32),
        Words.cons_if(Nat.is_one(W.U32.low(w)), ord, acc))

def Words.members.go(ws: List<&2, U32>, +ord: U32, acc: List<&2, U32>) ->
  List<&2, U32>:
  match ws:
    case Nil{}:
      acc
    case Con{w, t}:
      Words.members.go(t, (ord + 32 : U32), Words.bits_rev(32n, w, ord, acc))

# The ordinals a tile holds, ascending, each offset by `base`.
def Words.members(ws: List<&2, U32>, +base: U32) -> List<&2, U32>:
  List.reverse(&2, U32, Words.members.go(ws, base, Nil{}))

# The same walk over a difference, without building the difference tile.
def Words.diff_members.go(a: List<&2, U32>, b: List<&2, U32>, +ord: U32,
  acc: List<&2, U32>) -> List<&2, U32>:
  match a:
    case Nil{}:
      acc
    case Con{ah, at}:
      match b:
        case Nil{}:
          Words.members.go(Con{ah, at}, ord, acc)
        case Con{bh, bt}:
          Words.diff_members.go(at, bt, (ord + 32 : U32),
            Words.bits_rev(32n, W.U32.diff(ah, bh), ord, acc))

def Words.diff_members(a: List<&2, U32>, b: List<&2, U32>, +base: U32) ->
  List<&2, U32>:
  List.reverse(&2, U32, Words.diff_members.go(a, b, base, Nil{}))

# Are all words zero / all words all-ones? Used to re-compress a leaf after an
# operation (law S-03).
def Words.all_zero(ws: List<&2, U32>) -> Bool:
  Bool.not(Words.any(ws))

def Words.all_ones.go(ws: List<&2, U32>, ok: Bool) -> Bool:
  match ws:
    case Nil{}:
      ok
    case Con{w, t}:
      match ok:
        case False{}:
          False{}
        case True{}:
          Words.all_ones.go(t, U32.is_eq(w, 4294967295))

def Words.all_ones(ws: List<&2, U32>) -> Bool:
  Words.all_ones.go(ws, True{})
