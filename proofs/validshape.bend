# proofs/validshape.bend -- the shape the enumeration wants is the shape the
# store already checks.
#
# `PSet.valid` is what a decoded set is checked against: leaves are leaf
# shapes, a sparse leaf's offsets ascend and each is below 4096, a dense leaf
# is exactly 128 words, and above the leaf level only zero, full and branch.
# `PSet.ok` is what proofs/treeenum.bend needs: the same thing, minus the
# ascending condition, plus the statement that a leaf's members fit in the
# twelve bits a leaf covers.
#
# This file derives the second from the first, so a caller with a set that
# passed the store's own check can use the enumeration law without proving
# anything about the set's shape.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./split_add.bend as Sa
import ./shift.bend as Sf
import ./leafenum.bend as Le
import ./treeenum.bend as Te
import ./tilefit.bend as Tf
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/set.bend as S
import ../core/words.bend as Wo

# ---------------------------------------------------------------------------
# The validity walk threads an accumulator. It is a conjunction.
# ---------------------------------------------------------------------------

law PSet.valid_acc:
  for +d: Nat
  for +s: S.PSet
  for +ok: Bool
  {S.PSet.valid(d, s, ok)
    == Bool.and(ok, S.PSet.valid(d, s, True{})) : Bool}

def PSet.valid_acc(d, s, ok):
  match d:
    case 0n:
      {==}
    case 1n+p:
      match s:
        case S.PZero{}:
          E.Bool.sym(Bool.and(ok, True{}), ok,
            Te.Bool.and_true_r(ok))
        case S.PFull{}:
          E.Bool.sym(Bool.and(ok, True{}), ok,
            Te.Bool.and_true_r(ok))
        case S.PSparse{offs}:
          E.Bool.sym(Bool.and(ok, False{}), False{},
            Sa.Word.and_false_r(ok))
        case S.PDense{ws}:
          E.Bool.sym(Bool.and(ok, False{}), False{},
            Sa.Word.and_false_r(ok))
        case S.PBranch{lo, hi}:
          match ok:
            case False{}:
              {==}
            case True{}:
              {==}

law PSet.both_of_branch:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +v: {S.PSet.valid(p, hi, S.PSet.valid(p, lo, True{}))
    == True{} : Bool}
  {Bool.and(S.PSet.valid(p, lo, True{}),
    S.PSet.valid(p, hi, True{})) == True{} : Bool}

def PSet.both_of_branch(p, lo, hi, v):
  %PSet.valid_acc(p, hi, S.PSet.valid(p, lo, True{}))
    : {_ == True{} : Bool}
  v

# ---------------------------------------------------------------------------
# A sparse leaf: every offset was compared against 4096.
# ---------------------------------------------------------------------------

law PSet.valid_offs_acc:
  for +offs: List<&2, U32>
  for +last: U32
  for +first: Bool
  for +ok: Bool
  for +v: {S.PSet.valid.offs(offs, last, first, ok) == True{} : Bool}
  {ok == True{} : Bool}

def PSet.valid_offs_acc(offs, last, first, ok, v):
  match offs:
    case Nil{}:
      v
    case Con{o, t}:
      match ok:
        case False{}:
          E.Bool.noconf({False{} == True{} : Bool}, v)
        case True{}:
          {==}

law Ords.all_fit_of_valid_offs:
  for +offs: List<&2, U32>
  for +last: U32
  for +first: Bool
  for +ok: Bool
  for +v: {S.PSet.valid.offs(offs, last, first, ok) == True{} : Bool}
  {Sf.Ords.all_fit(offs, 12n) == True{} : Bool}

def Ords.offset_fits(+o: U32, +last: U32, +first: Bool,
  +lt: {U32.is_lt(o, 4096) == True{} : Bool})
  -> {Dc.U32.hi_zero(o, 12n) == True{} : Bool}:
  %Dc.U32.is_lt_shln(o, 12n, {==})
    : {_ == True{} : Bool}
  lt

# ---------------------------------------------------------------------------
# A leaf, and then the tree.
# ---------------------------------------------------------------------------

def Ords.all_fit_of_valid_offs(offs, last, first, ok, v):
  match offs:
    case Nil{}:
      {==}
    case Con{o, t}:
      match ok:
        case False{}:
          E.Bool.noconf({Sf.Ords.all_fit(Con{o, t}, 12n) == True{}
            : Bool}, v)
        case True{}:
          E.Bool.and_both(Dc.U32.hi_zero(o, 12n),
            Sf.Ords.all_fit(t, 12n),
            Ords.offset_fits(o, last, first,
              E.Bool.and_l(U32.is_lt(o, 4096),
                Bool.or(first, U32.is_gt(o, last)),
                PSet.valid_offs_acc(t, o, False{},
                  Bool.and(U32.is_lt(o, 4096),
                    Bool.or(first, U32.is_gt(o, last))), v))),
            Ords.all_fit_of_valid_offs(t, o, False{},
              Bool.and(U32.is_lt(o, 4096),
                Bool.or(first, U32.is_gt(o, last))), v))

law PSet.ok_leaf_of_valid:
  for +s: S.PSet
  for +v: {S.PSet.valid.leaf(s) == True{} : Bool}
  {Te.PSet.ok(0n, s) == True{} : Bool}

def PSet.ok_leaf_of_valid(s, v):
  match s:
    case S.PZero{}:
      {==}
    case S.PFull{}:
      {==}
    case S.PSparse{offs}:
      E.Bool.and_both(Sf.Ords.all_fit(offs, 12n),
        Sf.Ords.all_fit(offs, 12n),
        Ords.all_fit_of_valid_offs(offs, 0, True{}, True{}, v),
        Ords.all_fit_of_valid_offs(offs, 0, True{}, True{}, v))
    case S.PDense{ws}:
      E.Bool.and_both(Nat.is_eq(List.length(&2, U32, ws), 128n),
        Sf.Ords.all_fit(Wo.Words.members(ws, 0), 12n), v,
        Tf.Words.members_fit(ws, v))
    case S.PBranch{l, h}:
      E.Bool.noconf({Te.PSet.ok(0n, S.PBranch{l, h}) == True{} : Bool},
        v)

law PSet.ok_of_valid:
  for +d: Nat
  for +s: S.PSet
  for +v: {S.PSet.valid(d, s, True{}) == True{} : Bool}
  {Te.PSet.ok(d, s) == True{} : Bool}

def PSet.ok_of_valid(d, s, v):
  match d:
    case 0n:
      PSet.ok_leaf_of_valid(s, v)
    case 1n+p:
      match s:
        case S.PZero{}:
          {==}
        case S.PFull{}:
          {==}
        case S.PSparse{offs}:
          E.Bool.noconf({Te.PSet.ok(1n+p, S.PSparse{offs}) == True{}
            : Bool}, v)
        case S.PDense{ws}:
          E.Bool.noconf({Te.PSet.ok(1n+p, S.PDense{ws}) == True{}
            : Bool}, v)
        case S.PBranch{lo, hi}:
          E.Bool.and_both(Te.PSet.ok(p, lo), Te.PSet.ok(p, hi),
            PSet.ok_of_valid(p, lo,
              E.Bool.and_l(S.PSet.valid(p, lo, True{}),
                S.PSet.valid(p, hi, True{}),
                PSet.both_of_branch(p, lo, hi, v))),
            PSet.ok_of_valid(p, hi,
              E.Bool.and_r(S.PSet.valid(p, lo, True{}),
                S.PSet.valid(p, hi, True{}),
                PSet.both_of_branch(p, lo, hi, v))))

# ---------------------------------------------------------------------------
# So the enumeration law applies to any set the store accepted.
# ---------------------------------------------------------------------------

law PSet.to_list_member_of_valid:
  for +d: Nat
  for +s: S.PSet
  for +x: U32
  for +v: {S.PSet.valid(d, s, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, S.PSet.to_list(d, s), x)
    == S.PSet.member(d, s, x) : Bool}

def PSet.to_list_member_of_valid(d, s, x, v, lt, inr):
  Te.PSet.to_list_member(d, s, x, PSet.ok_of_valid(d, s, v), lt, inr)

law PSet.valid_full:
  for +d: Nat
  {S.PSet.valid(d, S.PFull{}, True{}) == True{} : Bool}

def PSet.valid_full(d):
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

law PSet.mem_full:
  for +d: Nat
  for +h: U32
  for +x: U32
  {S.PSet.mem(d, S.PFull{}, h, x) == True{} : Bool}

def PSet.mem_full(d, h, x):
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}
