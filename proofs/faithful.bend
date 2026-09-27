# proofs/faithful.bend -- a valid leaf and its tile hold the same ordinals.
#
# Every leaf operation converts to words, works there, and compresses back.
# For that to be sound, the conversion has to be faithful: `PSet.leaf_words`
# must produce a tile with exactly the leaf's members, for each of the four
# shapes a valid leaf can take. This is the last piece of representation
# faithfulness, and the sparse case is the one that needed addressing fact A3
# (proofs/bridge.bend).
#
# The hypothesis is the leaf's own extent: a leaf covers 4096 ordinals, and
# `PFull{}` means those 4096 rather than "everything", which is exactly what
# the counterexample in tests.bend shows.

import Base
import ./shape.bend as Sh
import ./eq.bend as E
import ./addr.bend as Ad
import ./bits.bend as PB
import ./bridge.bend as Br
import ./leaf.bend as Lf
import ./descend.bend as Dc
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/ords.bend as O
import ../core/set.bend as S

def Word.ones_w(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, Word.ones_w(p)}

law Word.get_ones:
  for +n: Nat
  for +b: Nat
  for +ok: {C.Nat.gt(n, b) == True{} : Bool}
  {W.Word.get(n, Word.ones_w(n), b) == True{} : Bool}

def Word.get_ones(n, b, ok):
  match n:
    case 0n:
      E.Bool.noconf({W.Word.get(0n, Word.ones_w(0n), b)
        == True{} : Bool}, ok)
    case 1n+p:
      match b:
        case 0n:
          {==}
        case 1n+j:
          Word.get_ones(p, j, ok)

law U32.test_ones:
  for +b: Nat
  for +ok: {C.Nat.gt(32n, b) == True{} : Bool}
  {Wo.U32.test(4294967295, b) == True{} : Bool}

def U32.test_ones(b, ok):
  Equal.trans(Bool, Wo.U32.test(4294967295, b),
    W.U32.bit(4294967295, b), True{},
    PB.U32.test_spec(4294967295, b),
    Word.get_ones(32n, b, ok))

law Words.at_ones:
  for +n: Nat
  for +i: Nat
  for +b: Nat
  for +iok: {C.Nat.gt(n, i) == True{} : Bool}
  for +bok: {C.Nat.gt(32n, b) == True{} : Bool}
  {Wo.Words.at(Wo.Words.ones(n), i, b) == True{} : Bool}

def Words.at_ones(n, i, b, iok, bok):
  match n:
    case 0n:
      E.Bool.noconf({Wo.Words.at(Wo.Words.ones(0n), i, b)
        == True{} : Bool}, iok)
    case 1n+p:
      match i:
        case 0n:
          U32.test_ones(b, bok)
        case 1n+j:
          Words.at_ones(p, j, b, iok, bok)

# ---------------------------------------------------------------------------
# The four shapes.
# ---------------------------------------------------------------------------

law PSet.leaf_faithful:
  for +s: S.PSet
  for +x: U32
  for +v: {Sh.PSet.wf.leaf(s) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {S.PSet.mem.leaf(s, x)
    == Wo.Words.bit(S.PSet.leaf_words(s), x) : Bool}

law PSet.bit_ones_in_range:
  for +x: U32
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {Wo.Words.bit(Wo.Words.ones(128n), x) == True{} : Bool}

def PSet.bit_ones_in_range(x, inr):
  Words.at_ones(128n, U32.to_nat(U32.shrn(x, 5n)),
    U32.to_nat(U32.and(x, 31)), Lf.PSet.shift_bound(x, inr),
    Ad.U32.low_five_bound(x))

law PSet.zeros_fits:
  for +x: U32
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {Wo.Words.has_word(Wo.Words.zeros(128n),
    U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}

law PSet.zeros_fits.bound:
  for +x: U32
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {C.Nat.gt(List.length(&2, U32, Wo.Words.zeros(128n)),
    U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}

def PSet.zeros_fits.bound(x, inr):
  %E.Nat.sym(List.length(&2, U32, Wo.Words.zeros(128n)), 128n,
    Lf.Words.length_zeros(128n))
    : {C.Nat.gt(_, U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}
  Lf.PSet.shift_bound(x, inr)

def PSet.zeros_fits(x, inr):
  Lf.Words.has_word_of_length(Wo.Words.zeros(128n),
    U32.to_nat(U32.shrn(x, 5n)),
    PSet.zeros_fits.bound(x, inr))

def PSet.leaf_faithful(s, x, v, inr):
  match s:
    case S.PZero{}:
      E.Bool.sym(Wo.Words.bit(Wo.Words.zeros(128n), x), False{},
        Br.Words.bit_zeros(128n, x))
    case S.PFull{}:
      E.Bool.sym(Wo.Words.bit(Wo.Words.ones(128n), x), True{},
        PSet.bit_ones_in_range(x, inr))
    case S.PDense{ws}:
      {==}
    case S.PBranch{l, h}:
      E.Bool.noconf({S.PSet.mem.leaf(S.PBranch{l, h}, x)
        == Wo.Words.bit(S.PSet.leaf_words(S.PBranch{l, h}), x) : Bool}, v)
    case S.PSparse{offs}:
      E.Bool.sym(
        Wo.Words.bit(S.PSet.spread(offs, Wo.Words.zeros(128n)), x),
        O.Ords.elem(offs, x),
        Br.PSet.sparse_matches_its_tile(offs, x,
          PSet.zeros_fits(x, inr)))
