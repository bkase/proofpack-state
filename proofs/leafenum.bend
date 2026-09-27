# proofs/leafenum.bend -- a leaf enumerates exactly its members.
#
# `PSet.leaf_members` is how a leaf hands over its ordinals: a sparse leaf
# gives its offset list, a dense one walks its tile, a full one counts down
# its whole 4096, and an empty one gives nothing. `PSet.mem.leaf` is the
# membership test over the same four shapes. This says they agree.
#
# It is the base case of the enumeration law, and the place the two halves of
# the representation meet: the tile walk is related to the bit test by the
# laws A5 already proved, and the full leaf's count-down by the span laws in
# proofs/span.bend.
#
# The sparse case carries a hypothesis -- that the offsets fit in twelve bits
# -- because it is false without one. A leaf holding an offset past 4096 is
# a leaf whose enumeration leaves its own interval, and `PSet.valid` is what
# rules that out on anything read from a store.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./enum.bend as En
import ./walk.bend as Wk
import ./leaf.bend as Lf
import ./descend.bend as Dc
import ./span.bend as Sn
import ./shift.bend as Sh
import ./subset.bend as Sb
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/ords.bend as O
import ../core/set.bend as S

# `Ords.elem` and `List.contains` ask the same question.
law Ords.elem_is_contains:
  for +xs: List<&2, U32>
  for +acc: Bool
  for +y: U32
  {O.Ords.elem.go(xs, y, acc)
    == Bool.or(acc, List.contains(~U32, ~U32.is_eq, xs, y)) : Bool}

def Ords.elem_is_contains(xs, acc, y):
  match xs:
    case Nil{}:
      match acc:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{h, t}:
      match acc:
        case True{}:
          {==}
        case False{}:
          Ords.elem_is_contains(t, U32.is_eq(h, y), y)

law Ords.elem_contains:
  for +xs: List<&2, U32>
  for +y: U32
  {O.Ords.elem(xs, y) == List.contains(~U32, ~U32.is_eq, xs, y) : Bool}

def Ords.elem_contains(xs, y):
  Ords.elem_is_contains(xs, False{}, y)

# Splitting a walk at its tail.
law List.contains_append:
  for +l: List<&2, U32>
  for +t: List<&2, U32>
  for +y: U32
  {List.contains(~U32, ~U32.is_eq, List.append(&2, U32, l, t), y)
    == Bool.or(List.contains(~U32, ~U32.is_eq, l, y),
         List.contains(~U32, ~U32.is_eq, t, y)) : Bool}

def List.contains_append(l, t, y):
  match l:
    case Nil{}:
      {==}
    case Con{h, r}:
      %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
          List.append(&2, U32, r, t), y),
        Bool.or(List.contains(~U32, ~U32.is_eq, r, y),
          List.contains(~U32, ~U32.is_eq, t, y)),
        List.contains_append(r, t, y))
        : {Bool.or(U32.is_eq(h, y), _)
          == Bool.or(Bool.or(U32.is_eq(h, y),
               List.contains(~U32, ~U32.is_eq, r, y)),
               List.contains(~U32, ~U32.is_eq, t, y)) : Bool}
      Sn.Bool.or_assoc(U32.is_eq(h, y),
        List.contains(~U32, ~U32.is_eq, r, y),
        List.contains(~U32, ~U32.is_eq, t, y))

# ---------------------------------------------------------------------------
# The full leaf. Its count-down and the members of a tile of ones are the
# same closed list (proofs/subset.bend), so this needs no arithmetic: the
# tile laws already say every in-range ordinal is there.
# ---------------------------------------------------------------------------

law PSet.full_leaf_enumerates:
  for +y: U32
  for +inr: {Dc.U32.hi_zero(y, 12n) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq,
    S.PSet.range(4096n, 4095, Nil{}), y) == True{} : Bool}

def PSet.full_leaf_enumerates(y, inr):
  %Ords.elem_contains(S.PSet.range(4096n, 4095, Nil{}), y)
    : {_ == True{} : Bool}
  Sb.Ords.elem_full_range(y, inr)

# ---------------------------------------------------------------------------
# The leaf, all four shapes.
#
# `PSet.ok.leaf` is what the enumeration needs of a leaf and `PSet.wf.leaf`
# does not say: a sparse leaf's offsets have to fit in the twelve bits a leaf
# covers. `PSet.valid` says it, so anything read from a store has it; the
# preservation of it through the operations is the one piece this release
# leaves open, and LAWS.pending.bend says so.
# ---------------------------------------------------------------------------

def PSet.ok.leaf(s: S.PSet) -> Bool:
  match s:
    case S.PZero{}:
      True{}
    case S.PFull{}:
      True{}
    case S.PBranch{l, h}:
      True{}
    case S.PSparse{offs}:
      Sh.Ords.all_fit(offs, 12n)
    case S.PDense{ws}:
      Nat.is_eq(List.length(&2, U32, ws), 128n)

law PSet.leaf_members_mem:
  for +s: S.PSet
  for +y: U32
  for +inr: {Dc.U32.hi_zero(y, 12n) == True{} : Bool}
  for +ok: {PSet.ok.leaf(s) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, S.PSet.leaf_members(s), y)
    == S.PSet.mem.leaf(s, y) : Bool}

def PSet.leaf_members_mem(s, y, inr, ok):
  match s:
    case S.PZero{}:
      {==}
    case S.PBranch{l, h}:
      {==}
    case S.PFull{}:
      PSet.full_leaf_enumerates(y, inr)
    case S.PSparse{offs}:
      E.Bool.sym(O.Ords.elem(offs, y),
        List.contains(~U32, ~U32.is_eq, offs, y),
        Ords.elem_contains(offs, y))
    case S.PDense{ws}:
      Equal.trans(Bool,
        List.contains(~U32, ~U32.is_eq, Wo.Words.members(ws, 0), y),
        En.Words.holds(ws, 0, y), Wo.Words.bit(ws, y),
        Equal.trans(Bool,
          List.contains(~U32, ~U32.is_eq, Wo.Words.members(ws, 0), y),
          O.Ords.elem(Wo.Words.members(ws, 0), y),
          En.Words.holds(ws, 0, y),
          E.Bool.sym(O.Ords.elem(Wo.Words.members(ws, 0), y),
            List.contains(~U32, ~U32.is_eq, Wo.Words.members(ws, 0), y),
            Ords.elem_contains(Wo.Words.members(ws, 0), y)),
          En.Words.elem_members(ws, y)),
        Wk.Words.holds_bit(ws, y,
          Lf.Nat.is_eq_reflect(List.length(&2, U32, ws), 128n, ok)))
