# proofs/setcard.bend -- a subset is no bigger, and a proper subset is smaller.
#
# `PSet.count` is the length of `PSet.to_list` (proofs/countlen.bend), that
# enumeration ascends (proofs/ascend.bend), and an ascending list inside
# another ascending list is no longer (proofs/sublist.bend). Putting the three
# together gives the two facts the fixed-point argument runs on:
#
#   * a subset's size is at most the superset's;
#   * and if the superset also holds an ordinal the subset does not -- which
#     is exactly what a non-zero fused difference count exhibits -- the
#     subset's size is strictly smaller.
#
# Both are stated over the production counts, and the hypothesis is the
# production `PSet.is_subset`, so an induction can carry it.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./sublist.bend as Sl
import ./ascend.bend as As
import ./subsetconv.bend as Sc
import ./subsetalg.bend as Sa
import ./postmono.bend as Pm
import ./validshape.bend as Vs
import ./countlen.bend as Cl
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/set.bend as S

law PSet.count_le:
  for +d: Nat
  for +b: S.PSet
  for +a: S.PSet
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ab: {S.PSet.is_subset(d, a, b) == True{} : Bool}
  {C.Nat.upto(S.PSet.count(d, a, S.PSet.half(d)),
    S.PSet.count(d, b, S.PSet.half(d))) == True{} : Bool}

def PSet.count_le(d, b, a, vb, va, lt, ab):
  %Cl.PSet.count_is_to_list_length(d, a, lt)
    : {C.Nat.upto(_, S.PSet.count(d, b, S.PSet.half(d))) == True{}
      : Bool}
  %Cl.PSet.count_is_to_list_length(d, b, lt)
    : {C.Nat.upto(List.length(&2, U32, S.PSet.to_list(d, a)), _)
      == True{} : Bool}
  Sl.Ords.length_le(S.PSet.to_list(d, b), S.PSet.to_list(d, a),
    As.Ords.asc_to_list(d, a, va, lt),
    As.Ords.asc_to_list(d, b, vb, lt),
    Pm.PSet.subset_to_list(d, a, b, va, vb, lt, ab))

def PSet.not_in_to_list(+d: Nat, +b: S.PSet, +a: S.PSet, +h: U32,
  +t: List<&2, U32>,
  +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool},
  +va: {S.PSet.valid(d, a, True{}) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +el: {Con{h, t} == S.PSet.missing(d, b, a) : List<&2, U32>})
  -> {List.contains(~U32, ~U32.is_eq, S.PSet.to_list(d, a), h)
    == False{} : Bool}:
  %E.Bool.sym(False{}, S.PSet.member(d, a, h),
    Sc.PSet.not_member(d, b, a, h, t, vb, va, lt, el))
    : {List.contains(~U32, ~U32.is_eq, S.PSet.to_list(d, a), h) == _
      : Bool}
  Vs.PSet.to_list_member_of_valid(d, a, h, va, lt,
    Sc.PSet.witness_fits(d, b, a, h, t, vb, va, lt, el))

law PSet.count_lt:
  for +d: Nat
  for +b: S.PSet
  for +a: S.PSet
  for +h: U32
  for +t: List<&2, U32>
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +el: {Con{h, t} == S.PSet.missing(d, b, a) : List<&2, U32>}
  for +ab: {S.PSet.is_subset(d, a, b) == True{} : Bool}
  {C.Nat.upto(1n+S.PSet.count(d, a, S.PSet.half(d)),
    S.PSet.count(d, b, S.PSet.half(d))) == True{} : Bool}

def PSet.count_lt(d, b, a, h, t, vb, va, lt, el, ab):
  %Cl.PSet.count_is_to_list_length(d, a, lt)
    : {C.Nat.upto(1n+_, S.PSet.count(d, b, S.PSet.half(d)))
      == True{} : Bool}
  %Cl.PSet.count_is_to_list_length(d, b, lt)
    : {C.Nat.upto(1n+List.length(&2, U32, S.PSet.to_list(d, a)), _)
      == True{} : Bool}
  Sl.Ords.length_lt(S.PSet.to_list(d, b), S.PSet.to_list(d, a), h,
    As.Ords.asc_to_list(d, a, va, lt),
    As.Ords.asc_to_list(d, b, vb, lt),
    Pm.PSet.subset_to_list(d, a, b, va, vb, lt, ab),
    Sc.PSet.in_to_list(d, b, a, h, t, vb, va, lt, el),
    PSet.not_in_to_list(d, b, a, h, t, vb, va, lt, el))

# ---------------------------------------------------------------------------
# Everything is inside the universe of its own depth.
# ---------------------------------------------------------------------------

law Ords.all_mem_full:
  for +l: List<&2, U32>
  for +d: Nat
  {Sc.Ords.all_mem(l, d, S.PFull{}) == True{} : Bool}

def Ords.all_mem_full(l, d):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(S.PSet.member(d, S.PFull{}, y),
        Sc.Ords.all_mem(u, d, S.PFull{}),
        Vs.PSet.mem_full(d, S.PSet.half(d), y),
        Ords.all_mem_full(u, d))

law PSet.subset_full:
  for +d: Nat
  for +a: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {S.PSet.is_subset(d, a, S.PFull{}) == True{} : Bool}

def PSet.subset_full(d, a, va, lt):
  Sc.PSet.subset_of_members(d, a, S.PFull{}, va,
    Vs.PSet.valid_full(d), lt,
    Ords.all_mem_full(S.PSet.to_list(d, a), d))

law PSet.count_bound:
  for +d: Nat
  for +a: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {C.Nat.upto(S.PSet.count(d, a, S.PSet.half(d)),
    S.PSet.count(d, S.PFull{}, S.PSet.half(d))) == True{} : Bool}

def PSet.count_bound(d, a, va, lt):
  PSet.count_le(d, S.PFull{}, a, Vs.PSet.valid_full(d), va, lt,
    PSet.subset_full(d, a, va, lt))
