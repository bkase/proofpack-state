# proofs/addr.bend -- how an ordinal addresses a tile.
#
# `Words.bit(ws, x)` reads word `x >> 5`, bit `x & 31`. The bit index has to be
# a bit index for any of the tile laws to hold -- `U32.shln(1, 32n)` is zero,
# so "setting bit 32" of a word sets nothing. This file proves that side
# condition away: masking with 31 always leaves a number below 32.
#
# The argument is that `and` can only clear bits, so the masked value is at
# most the mask, and the mask is 31. Stated over `Word.to_nat`, which is the
# bit vector read as a number, so it is an induction down the vector.
#
# The *other* addressing fact -- that a 128-word tile has a word for every
# ordinal below 4096, i.e. that `x >> 5 < 128` when `x < 4096` -- is not
# proved here. It needs `U32.is_lt` to agree with the order on `U32.to_nat`
# and `U32.shrn` to be division, and this release does not have either. The
# laws that would use it carry it as an explicit hypothesis instead, in the
# form "the tile has the word this ordinal lives in", which is exactly what
# the counterexample in tests.bend violates.

import Base
import ./eq.bend as E
import ../core/count.bend as C

# ---------------------------------------------------------------------------
# Ordering lemmas for the checked counter.
# ---------------------------------------------------------------------------

law Nat.upto_succ_r:
  for +u: Nat
  for +v: Nat
  for +ok: {C.Nat.upto(u, v) == True{} : Bool}
  {C.Nat.upto(u, 1n+v) == True{} : Bool}

def Nat.upto_succ_r(u, v, ok):
  match u:
    case 0n:
      {==}
    case 1n+p:
      match v:
        case 0n:
          E.Bool.noconf({C.Nat.upto(1n+p, 1n) == True{} : Bool}, ok)
        case 1n+q:
          Nat.upto_succ_r(p, q, ok)

law Nat.double_mono:
  for +x: Nat
  for +y: Nat
  for +ok: {C.Nat.upto(x, y) == True{} : Bool}
  {C.Nat.upto(Nat.double(x), Nat.double(y)) == True{} : Bool}

def Nat.double_mono(x, y, ok):
  match x:
    case 0n:
      {==}
    case 1n+p:
      match y:
        case 0n:
          E.Bool.noconf({C.Nat.upto(Nat.double(1n+p), 0n) == True{} : Bool},
            ok)
        case 1n+q:
          Nat.double_mono(p, q, ok)

# `gt` with a successor on the left is `upto` with the predecessor on the
# right -- the bridge between the bound this file produces and the bound the
# tile laws ask for.
law Nat.gt_succ:
  for +q: Nat
  for +i: Nat
  {C.Nat.gt(1n+q, i) == C.Nat.upto(i, q) : Bool}

def Nat.gt_succ(q, i):
  match q:
    case 0n:
      match i:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case 1n+r:
      match i:
        case 0n:
          {==}
        case 1n+j:
          Nat.gt_succ(r, j)

# ---------------------------------------------------------------------------
# Masking can only make a word smaller.
# ---------------------------------------------------------------------------

# The head bit, with both bits taken as parameters: Bend matches parameters,
# not the fields of a pattern, so the four-way split lives in its own def.
law Word.to_nat_and.head:
  for +p: Nat
  for +ab: Bool
  for +bb: Bool
  for +at: Word(p)
  for +bt: Word(p)
  for +ih: {C.Nat.upto(Word.to_nat(p, Word.and(p, at, bt)),
    Word.to_nat(p, bt)) == True{} : Bool}
  {C.Nat.upto(
      Word.to_nat(1n+p, WCon{Bool.and(ab, bb), Word.and(p, at, bt)}),
      Word.to_nat(1n+p, WCon{bb, bt})) == True{} : Bool}

def Word.to_nat_and.head(p, ab, bb, at, bt, ih):
  match ab bb:
    case False{} False{}:
      Nat.double_mono(Word.to_nat(p, Word.and(p, at, bt)),
        Word.to_nat(p, bt), ih)
    case True{} False{}:
      Nat.double_mono(Word.to_nat(p, Word.and(p, at, bt)),
        Word.to_nat(p, bt), ih)
    case True{} True{}:
      Nat.double_mono(Word.to_nat(p, Word.and(p, at, bt)),
        Word.to_nat(p, bt), ih)
    case False{} True{}:
      # The mask keeps this bit, the value does not have it: the masked
      # number is even and the mask is odd, so it is smaller by one more.
      Nat.upto_succ_r(Nat.double(Word.to_nat(p, Word.and(p, at, bt))),
        Nat.double(Word.to_nat(p, bt)),
        Nat.double_mono(Word.to_nat(p, Word.and(p, at, bt)),
          Word.to_nat(p, bt), ih))

law Word.to_nat_and:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {C.Nat.upto(Word.to_nat(n, Word.and(n, a, b)), Word.to_nat(n, b))
    == True{} : Bool}

def Word.to_nat_and(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          Word.to_nat_and.head(p, ab, bb, at, bt,
            Word.to_nat_and(p, at, bt))

law U32.to_nat_and:
  for +a: U32
  for +b: U32
  {C.Nat.upto(U32.to_nat(U32.and(a, b)), U32.to_nat(b)) == True{} : Bool}

def U32.to_nat_and(a, b):
  match a b:
    case U32{x} U32{y}:
      Word.to_nat_and(32n, x, y)

# ---------------------------------------------------------------------------
# The bit index of an ordinal is a bit index.
# ---------------------------------------------------------------------------

law U32.low_five_bound:
  for +x: U32
  {C.Nat.gt(32n, U32.to_nat(U32.and(x, 31))) == True{} : Bool}

def U32.low_five_bound(x):
  %E.Bool.sym(C.Nat.gt(32n, U32.to_nat(U32.and(x, 31))),
    C.Nat.upto(U32.to_nat(U32.and(x, 31)), 31n),
    Nat.gt_succ(31n, U32.to_nat(U32.and(x, 31))))
    : {_ == True{} : Bool}
  U32.to_nat_and(x, 31)
