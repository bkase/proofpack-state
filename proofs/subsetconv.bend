# proofs/subsetconv.bend -- the converse of the subset bridge.
#
# `a_subset_contains_every_member` turns a zero fused-difference count into a
# statement about an ordinal. This is the other direction: if every ordinal
# the set `a` enumerates is a member of `b`, then the count is zero and
# `PSet.is_subset` says so.
#
# The obstruction used to be that the hypothesis quantifies over ordinals and
# an ordinal-quantified hypothesis cannot be used twice. It is used once
# here, at one ordinal, and something produces that ordinal: a count that is
# not zero means the fused list is not empty, and its first ordinal is a
# member of `a` that is not a member of `b`.
#
# The hypothesis is data rather than a function -- every ordinal on a list is
# a member of `b` -- which is the form a caller can actually build, one
# ordinal at a time, out of laws.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./treeenum.bend as Te
import ./treediff.bend as Td
import ./validshape.bend as Vs
import ./fusedlen.bend as Fl
import ./nonempty.bend as Ne2
import ./countlen.bend as Cl
import ./sum.bend as Sm
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/set.bend as S

# Every ordinal on the list is a member of `b`.
def Ords.all_mem(+xs: List<&2, U32>, +d: Nat, +b: S.PSet) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{y, t}:
      Bool.and(S.PSet.member(d, b, y), Ords.all_mem(t, d, b))

def Ords.head_eq(+xs: List<&2, U32>, +h: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, t}:
      U32.is_eq(y, h)

law Ords.all_mem_at:
  for +xs: List<&2, U32>
  for +d: Nat
  for +b: S.PSet
  for +h: U32
  for +e: Bool
  for +ee: {e == Ords.head_eq(xs, h) : Bool}
  for +am: {Ords.all_mem(xs, d, b) == True{} : Bool}
  for +inx: {List.contains(~U32, ~U32.is_eq, xs, h) == True{} : Bool}
  {S.PSet.member(d, b, h) == True{} : Bool}

def Ords.contains_tail(+y: U32, +t: List<&2, U32>, +h: U32,
  +ee: {False{} == U32.is_eq(y, h) : Bool},
  +inx: {List.contains(~U32, ~U32.is_eq, Con{y, t}, h) == True{}
    : Bool})
  -> {List.contains(~U32, ~U32.is_eq, t, h) == True{} : Bool}:
  %E.Bool.sym(False{}, U32.is_eq(y, h), ee)
    : {Bool.or(_, List.contains(~U32, ~U32.is_eq, t, h))
      == True{} : Bool}
  inx

# ---------------------------------------------------------------------------
# The fused list at the root.
# ---------------------------------------------------------------------------

def Ords.all_mem_at(xs, d, b, h, e, ee, am, inx):
  match xs:
    case Nil{}:
      E.Bool.noconf({S.PSet.member(d, b, h) == True{} : Bool}, inx)
    case Con{y, t}:
      match e:
        case True{}:
          %E.U32.eq_reflect(y, h,
            E.Bool.sym(True{}, U32.is_eq(y, h), ee))
            : {S.PSet.member(d, b, _) == True{} : Bool}
          E.Bool.and_l(S.PSet.member(d, b, y),
            Ords.all_mem(t, d, b), am)
        case False{}:
          Ords.all_mem_at(t, d, b, h, Ords.head_eq(t, h), {==},
            E.Bool.and_r(S.PSet.member(d, b, y),
              Ords.all_mem(t, d, b), am),
            Ords.contains_tail(y, t, h, ee, inx))

law PSet.missing_contains:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, S.PSet.missing(d, a, b), x)
    == Bool.and(U32.is_eq(0, W.U32.diff(x, W.U32.mask(12n+d))),
         Bool.and(S.PSet.mem(d, a, S.PSet.half(d),
           U32.and(x, W.U32.mask(12n+d))),
           Bool.not(S.PSet.mem(d, b, S.PSet.half(d),
             U32.and(x, W.U32.mask(12n+d)))))) : Bool}

def PSet.missing_contains(d, a, b, x, va, vb, lt):
  %Te.Bool.or_false_r(
    Bool.and(U32.is_eq(0, W.U32.diff(x, W.U32.mask(12n+d))),
      Bool.and(S.PSet.mem(d, a, S.PSet.half(d),
        U32.and(x, W.U32.mask(12n+d))),
        Bool.not(S.PSet.mem(d, b, S.PSet.half(d),
          U32.and(x, W.U32.mask(12n+d)))))))
    : {List.contains(~U32, ~U32.is_eq, S.PSet.missing(d, a, b), x)
      == _ : Bool}
  Td.PSet.diff_members_contains(d, a, b, 0, x, Nil{}, va, vb,
    Te.U32.lo_zero_zero(12n+d), lt)

# ---------------------------------------------------------------------------
# The converse.
# ---------------------------------------------------------------------------

law PSet.subset_of_all_mem:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +m: Nat
  for +l: List<&2, U32>
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +em: {m == S.PSet.missing_count(d, a, b) : Nat}
  for +el: {l == S.PSet.missing(d, a, b) : List<&2, U32>}
  for +am: {Ords.all_mem(S.PSet.to_list(d, a), d, b) == True{}
    : Bool}
  {S.PSet.is_subset(d, a, b) == True{} : Bool}

def Ords.len(l: List<&2, U32>) -> Nat:
  List.length(&2, U32, l)

# The list cannot be empty when the count is not zero.
def PSet.empty_absurd(+d: Nat, +a: S.PSet, +b: S.PSet, +k: Nat,
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +em: {1n+k == S.PSet.missing_count(d, a, b) : Nat},
  +el: {Nil{} == S.PSet.missing(d, a, b) : List<&2, U32>})
  -> {1n+k == 0n : Nat}:
  Sm.Nat.eq_cast(S.PSet.missing_count(d, a, b), 1n+k,
    List.length(&2, U32, S.PSet.missing(d, a, b)), 0n,
    E.Nat.sym(1n+k, S.PSet.missing_count(d, a, b), em),
    E.Nat.sym(0n, List.length(&2, U32, S.PSet.missing(d, a, b)),
      Equal.cong(List<&2, U32>, Nat, Ords.len, Nil{},
        S.PSet.missing(d, a, b), el)),
    Fl.PSet.missing_count_is_length(d, a, b, lt))

# The three facts the witness carries, read off the fused list law: it is
# inside the universe, it is a member of `a`, and it is not a member of `b`.
def PSet.witness_both(+d: Nat, +a: S.PSet, +b: S.PSet, +h: U32,
  +t: List<&2, U32>,
  +va: {S.PSet.valid(d, a, True{}) == True{} : Bool},
  +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +el: {Con{h, t} == S.PSet.missing(d, a, b) : List<&2, U32>})
  -> {Bool.and(U32.is_eq(0, W.U32.diff(h, W.U32.mask(12n+d))),
       Bool.and(S.PSet.mem(d, a, S.PSet.half(d),
         U32.and(h, W.U32.mask(12n+d))),
         Bool.not(S.PSet.mem(d, b, S.PSet.half(d),
           U32.and(h, W.U32.mask(12n+d)))))) == True{} : Bool}:
  %PSet.missing_contains(d, a, b, h, va, vb, lt)
    : {_ == True{} : Bool}
  %el
    : {List.contains(~U32, ~U32.is_eq, _, h) == True{} : Bool}
  Ne2.List.contains_head(h, t)

def PSet.witness_fits(+d: Nat, +a: S.PSet, +b: S.PSet, +h: U32,
  +t: List<&2, U32>,
  +va: {S.PSet.valid(d, a, True{}) == True{} : Bool},
  +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +el: {Con{h, t} == S.PSet.missing(d, a, b) : List<&2, U32>})
  -> {Dc.U32.hi_zero(h, 12n+d) == True{} : Bool}:
  Ne2.U32.hi_zero_of_test(h, 12n+d,
    E.Bool.and_l(U32.is_eq(0, W.U32.diff(h, W.U32.mask(12n+d))),
      Bool.and(S.PSet.mem(d, a, S.PSet.half(d),
        U32.and(h, W.U32.mask(12n+d))),
        Bool.not(S.PSet.mem(d, b, S.PSet.half(d),
          U32.and(h, W.U32.mask(12n+d))))),
      PSet.witness_both(d, a, b, h, t, va, vb, lt, el)))

def PSet.member_of_a(+d: Nat, +a: S.PSet, +b: S.PSet, +h: U32,
  +t: List<&2, U32>,
  +va: {S.PSet.valid(d, a, True{}) == True{} : Bool},
  +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +el: {Con{h, t} == S.PSet.missing(d, a, b) : List<&2, U32>})
  -> {S.PSet.member(d, a, h) == True{} : Bool}:
  %Te.U32.and_mask_of_hi_zero(h, 12n+d,
    PSet.witness_fits(d, a, b, h, t, va, vb, lt, el))
    : {S.PSet.mem(d, a, S.PSet.half(d), _) == True{} : Bool}
  E.Bool.and_l(S.PSet.mem(d, a, S.PSet.half(d),
    U32.and(h, W.U32.mask(12n+d))),
    Bool.not(S.PSet.mem(d, b, S.PSet.half(d),
      U32.and(h, W.U32.mask(12n+d)))),
    E.Bool.and_r(U32.is_eq(0, W.U32.diff(h, W.U32.mask(12n+d))),
      Bool.and(S.PSet.mem(d, a, S.PSet.half(d),
        U32.and(h, W.U32.mask(12n+d))),
        Bool.not(S.PSet.mem(d, b, S.PSet.half(d),
          U32.and(h, W.U32.mask(12n+d))))),
      PSet.witness_both(d, a, b, h, t, va, vb, lt, el)))

# The witness is in the set's own enumeration.
def PSet.in_to_list(+d: Nat, +a: S.PSet, +b: S.PSet, +h: U32,
  +t: List<&2, U32>,
  +va: {S.PSet.valid(d, a, True{}) == True{} : Bool},
  +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +el: {Con{h, t} == S.PSet.missing(d, a, b) : List<&2, U32>})
  -> {List.contains(~U32, ~U32.is_eq, S.PSet.to_list(d, a), h)
    == True{} : Bool}:
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      S.PSet.to_list(d, a), h), S.PSet.member(d, a, h),
    Vs.PSet.to_list_member_of_valid(d, a, h, va, lt,
      PSet.witness_fits(d, a, b, h, t, va, vb, lt, el)))
    : {_ == True{} : Bool}
  PSet.member_of_a(d, a, b, h, t, va, vb, lt, el)

def PSet.not_member(+d: Nat, +a: S.PSet, +b: S.PSet, +h: U32,
  +t: List<&2, U32>,
  +va: {S.PSet.valid(d, a, True{}) == True{} : Bool},
  +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +el: {Con{h, t} == S.PSet.missing(d, a, b) : List<&2, U32>})
  -> {False{} == S.PSet.member(d, b, h) : Bool}:
  %Te.U32.and_mask_of_hi_zero(h, 12n+d,
    PSet.witness_fits(d, a, b, h, t, va, vb, lt, el))
    : {False{} == S.PSet.mem(d, b, S.PSet.half(d), _) : Bool}
  E.Bool.not_true(S.PSet.mem(d, b, S.PSet.half(d),
    U32.and(h, W.U32.mask(12n+d))),
    E.Bool.and_r(S.PSet.mem(d, a, S.PSet.half(d),
      U32.and(h, W.U32.mask(12n+d))),
      Bool.not(S.PSet.mem(d, b, S.PSet.half(d),
        U32.and(h, W.U32.mask(12n+d)))),
      E.Bool.and_r(U32.is_eq(0, W.U32.diff(h, W.U32.mask(12n+d))),
        Bool.and(S.PSet.mem(d, a, S.PSet.half(d),
          U32.and(h, W.U32.mask(12n+d))),
          Bool.not(S.PSet.mem(d, b, S.PSet.half(d),
            U32.and(h, W.U32.mask(12n+d))))),
        PSet.witness_both(d, a, b, h, t, va, vb, lt, el))))

# And its first ordinal is a member of `a` that is not a member of `b`.
def PSet.witness_absurd(+d: Nat, +a: S.PSet, +b: S.PSet, +h: U32,
  +t: List<&2, U32>,
  +va: {S.PSet.valid(d, a, True{}) == True{} : Bool},
  +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +el: {Con{h, t} == S.PSet.missing(d, a, b) : List<&2, U32>},
  +am: {Ords.all_mem(S.PSet.to_list(d, a), d, b) == True{} : Bool})
  -> {False{} == True{} : Bool}:
  %E.Bool.sym(False{}, S.PSet.member(d, b, h),
    PSet.not_member(d, a, b, h, t, va, vb, lt, el))
    : {_ == True{} : Bool}
  Ords.all_mem_at(S.PSet.to_list(d, a), d, b, h,
    Ords.head_eq(S.PSet.to_list(d, a), h), {==}, am,
    PSet.in_to_list(d, a, b, h, t, va, vb, lt, el))

def PSet.subset_of_all_mem(d, a, b, m, l, va, vb, lt, em, el, am):
  match m:
    case 0n:
      %em : {Nat.is_eq(_, 0n) == True{} : Bool}
      {==}
    case 1n+k:
      match l:
        case Nil{}:
          E.Nat.noconf2({S.PSet.is_subset(d, a, b) == True{} : Bool},
            k, PSet.empty_absurd(d, a, b, k, lt, em, el))
        case Con{h, t}:
          E.Bool.noconf({S.PSet.is_subset(d, a, b) == True{} : Bool},
            PSet.witness_absurd(d, a, b, h, t, va, vb, lt, el, am))

law PSet.subset_of_members:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +am: {Ords.all_mem(S.PSet.to_list(d, a), d, b) == True{}
    : Bool}
  {S.PSet.is_subset(d, a, b) == True{} : Bool}

def PSet.subset_of_members(d, a, b, va, vb, lt, am):
  PSet.subset_of_all_mem(d, a, b, S.PSet.missing_count(d, a, b),
    S.PSet.missing(d, a, b), va, vb, lt, {==}, {==}, am)
