# proofs/subsetalg.bend -- the subset relation is transitive.
#
# With both directions of the subset bridge in hand -- a subset contains
# every member, and a set whose members are all in another is a subset --
# the relation can be reasoned about at the level it is used at. This file
# proves the first consequence: transitivity, which is what the closure
# inductions need to carry "still inside this set" from one round to the
# next.
#
# The shape of the argument is the shape every such proof will have. The
# forward direction is applied once per ordinal on a list, which is legal
# because it is a law and not a hypothesis; the converse then turns the list
# back into the decidable test the production code computes.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./shape.bend as Sh
import ./leaf.bend as Lf
import ./subset.bend as Sb
import ./treeenum.bend as Te
import ./validshape.bend as Vs
import ./nonempty.bend as Ne2
import ./subsetconv.bend as Sc
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# An ordinal a set lists is inside the universe, and is a member.
# ---------------------------------------------------------------------------

def PSet.to_list_both(+d: Nat, +a: S.PSet, +y: U32,
  +ok: {Te.PSet.ok(d, a) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +c: {List.contains(~U32, ~U32.is_eq, S.PSet.to_list(d, a), y)
    == True{} : Bool})
  -> {Bool.and(U32.is_eq(0, W.U32.diff(y, W.U32.mask(12n+d))),
       S.PSet.mem(d, a, S.PSet.half(d),
         U32.and(y, W.U32.mask(12n+d)))) == True{} : Bool}:
  %Te.Bool.or_false_r(
    Bool.and(U32.is_eq(0, W.U32.diff(y, W.U32.mask(12n+d))),
      S.PSet.mem(d, a, S.PSet.half(d),
        U32.and(y, W.U32.mask(12n+d)))))
    : {_ == True{} : Bool}
  %Te.PSet.members_contains(d, a, 0, y, Nil{}, ok,
    Te.U32.lo_zero_zero(12n+d), lt)
    : {_ == True{} : Bool}
  c

law PSet.in_range_of_to_list:
  for +d: Nat
  for +a: S.PSet
  for +y: U32
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +c: {List.contains(~U32, ~U32.is_eq, S.PSet.to_list(d, a), y)
    == True{} : Bool}
  {Dc.U32.hi_zero(y, 12n+d) == True{} : Bool}

def PSet.in_range_of_to_list(d, a, y, va, lt, c):
  Ne2.U32.hi_zero_of_test(y, 12n+d,
    E.Bool.and_l(U32.is_eq(0, W.U32.diff(y, W.U32.mask(12n+d))),
      S.PSet.mem(d, a, S.PSet.half(d),
        U32.and(y, W.U32.mask(12n+d))),
      PSet.to_list_both(d, a, y, Vs.PSet.ok_of_valid(d, a, va), lt,
        c)))

law PSet.member_of_to_list:
  for +d: Nat
  for +a: S.PSet
  for +y: U32
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +c: {List.contains(~U32, ~U32.is_eq, S.PSet.to_list(d, a), y)
    == True{} : Bool}
  {S.PSet.member(d, a, y) == True{} : Bool}

def PSet.member_of_to_list(d, a, y, va, lt, c):
  %Te.U32.and_mask_of_hi_zero(y, 12n+d,
    PSet.in_range_of_to_list(d, a, y, va, lt, c))
    : {S.PSet.mem(d, a, S.PSet.half(d), _) == True{} : Bool}
  E.Bool.and_r(U32.is_eq(0, W.U32.diff(y, W.U32.mask(12n+d))),
    S.PSet.mem(d, a, S.PSet.half(d),
      U32.and(y, W.U32.mask(12n+d))),
    PSet.to_list_both(d, a, y, Vs.PSet.ok_of_valid(d, a, va), lt, c))

# ---------------------------------------------------------------------------
# The forward direction, at any depth.
# ---------------------------------------------------------------------------

law PSet.subset_member_at:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +y: U32
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(y, 12n+d) == True{} : Bool}
  for +sub: {S.PSet.is_subset(d, a, b) == True{} : Bool}
  for +ma: {S.PSet.member(d, a, y) == True{} : Bool}
  {S.PSet.member(d, b, y) == True{} : Bool}

def PSet.subset_member_at(d, a, b, y, va, vb, lt, inv, sub, ma):
  Sb.PSet.subset_mem(d, a, b, U32.is_lt(y, S.PSet.half(d)),
    S.PSet.half(d), y, {==}, lt, inv, {==},
    Sh.PSet.valid_wf(d, a, va), Sh.PSet.valid_wf(d, b, vb),
    Lf.Nat.is_eq_reflect(S.PSet.missing_count(d, a, b), 0n, sub), ma)

# ---------------------------------------------------------------------------
# Every ordinal on a list is on the list.
# ---------------------------------------------------------------------------

def Ords.all_in(+l: List<&2, U32>, +w: List<&2, U32>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case Con{y, t}:
      Bool.and(List.contains(~U32, ~U32.is_eq, w, y),
        Ords.all_in(t, w))

law Ords.all_in_cons:
  for +l: List<&2, U32>
  for +w: List<&2, U32>
  for +h: U32
  for +ai: {Ords.all_in(l, w) == True{} : Bool}
  {Ords.all_in(l, Con{h, w}) == True{} : Bool}

law Ords.or_right:
  for +p: Bool
  for +q: Bool
  for +ok: {q == True{} : Bool}
  {Bool.or(p, q) == True{} : Bool}

def Ords.or_right(p, q, ok):
  match p:
    case True{}:
      {==}
    case False{}:
      ok

def Ords.all_in_cons(l, w, h, ai):
  match l:
    case Nil{}:
      {==}
    case Con{y, t}:
      E.Bool.and_both(
        Bool.or(U32.is_eq(h, y),
          List.contains(~U32, ~U32.is_eq, w, y)),
        Ords.all_in(t, Con{h, w}),
        Ords.or_right(U32.is_eq(h, y),
          List.contains(~U32, ~U32.is_eq, w, y),
          E.Bool.and_l(List.contains(~U32, ~U32.is_eq, w, y),
            Ords.all_in(t, w), ai)),
        Ords.all_in_cons(t, w, h,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq, w, y),
            Ords.all_in(t, w), ai)))

law Ords.all_in_self:
  for +l: List<&2, U32>
  {Ords.all_in(l, l) == True{} : Bool}

law Ords.or_left:
  for +p: Bool
  for +q: Bool
  for +ok: {p == True{} : Bool}
  {Bool.or(p, q) == True{} : Bool}

def Ords.or_left(p, q, ok):
  %E.Bool.sym(p, True{}, ok) : {Bool.or(_, q) == True{} : Bool}
  {==}

def Ords.all_in_self(l):
  match l:
    case Nil{}:
      {==}
    case Con{y, t}:
      E.Bool.and_both(
        Bool.or(U32.is_eq(y, y),
          List.contains(~U32, ~U32.is_eq, t, y)),
        Ords.all_in(t, Con{y, t}),
        Ords.or_left(U32.is_eq(y, y),
          List.contains(~U32, ~U32.is_eq, t, y),
          E.U32.is_eq_refl(y)),
        Ords.all_in_cons(t, t, y, Ords.all_in_self(t)))

# ---------------------------------------------------------------------------
# Transitivity.
# ---------------------------------------------------------------------------

law Ords.all_mem_chain:
  for +l: List<&2, U32>
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +c: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +vc: {S.PSet.valid(d, c, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ab: {S.PSet.is_subset(d, a, b) == True{} : Bool}
  for +bc: {S.PSet.is_subset(d, b, c) == True{} : Bool}
  for +ai: {Ords.all_in(l, S.PSet.to_list(d, a)) == True{} : Bool}
  {Sc.Ords.all_mem(l, d, c) == True{} : Bool}

def Ords.all_mem_chain(l, d, a, b, c, va, vb, vc, lt, ab, bc, ai):
  match l:
    case Nil{}:
      {==}
    case Con{y, t}:
      E.Bool.and_both(S.PSet.member(d, c, y),
        Sc.Ords.all_mem(t, d, c),
        PSet.subset_member_at(d, b, c, y, vb, vc, lt,
          PSet.in_range_of_to_list(d, a, y, va, lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(d, a), y), Ords.all_in(t,
                S.PSet.to_list(d, a)), ai)),
          bc,
          PSet.subset_member_at(d, a, b, y, va, vb, lt,
            PSet.in_range_of_to_list(d, a, y, va, lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(d, a), y), Ords.all_in(t,
                  S.PSet.to_list(d, a)), ai)),
            ab,
            PSet.member_of_to_list(d, a, y, va, lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(d, a), y), Ords.all_in(t,
                  S.PSet.to_list(d, a)), ai)))),
        Ords.all_mem_chain(t, d, a, b, c, va, vb, vc, lt, ab, bc,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(d, a), y),
            Ords.all_in(t, S.PSet.to_list(d, a)), ai)))

law PSet.subset_trans:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +c: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +vc: {S.PSet.valid(d, c, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ab: {S.PSet.is_subset(d, a, b) == True{} : Bool}
  for +bc: {S.PSet.is_subset(d, b, c) == True{} : Bool}
  {S.PSet.is_subset(d, a, c) == True{} : Bool}

def PSet.subset_trans(d, a, b, c, va, vb, vc, lt, ab, bc):
  Sc.PSet.subset_of_members(d, a, c, va, vc, lt,
    Ords.all_mem_chain(S.PSet.to_list(d, a), d, a, b, c, va, vb, vc,
      lt, ab, bc, Ords.all_in_self(S.PSet.to_list(d, a))))
