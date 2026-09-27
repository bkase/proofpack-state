# proofs/orderlist.bend -- ascending and descending lists of ordinals.
#
# `Ords.diff` is a merge: it walks two lists in step and is only right when
# both ascend. The fused leaf difference calls it on a tile's members, so the
# tile walk's output has to be known to ascend before any of that can be
# used -- and the walk builds its list by prepending, largest last, so what
# it produces directly is a descending list that `List.reverse` turns around.
#
# These are the order predicates and the one lemma that relates them: the
# reverse of a descending list is ascending.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./order.bend as Or
import ./childtest.bend as Ct2
import ../core/count.bend as C
import ../core/word.bend as W

# Every ordinal in the list is above `h`.
def Ords.lt_all(+h: U32, +xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{y, t}:
      Bool.and(U32.is_lt(h, y), Ords.lt_all(h, t))

# Every ordinal in the list is below `h`.
def Ords.gt_all(+h: U32, +xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{y, t}:
      Bool.and(U32.is_lt(y, h), Ords.gt_all(h, t))

# Ascending, compared one step at a time. The strong form -- the head is
# below every ordinal in the tail -- follows by transitivity and is the
# lemma below; the predicate itself stays linear, because a full leaf's
# 4096 ordinals have to be checked by the kernel more than once.
def Ords.above(+h: U32, +t: List<&2, U32>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case Con{y, u}:
      U32.is_lt(h, y)

def Ords.asc(+xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Ords.above(h, t), Ords.asc(t))

def Ords.desc(+xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Ords.gt_all(h, t), Ords.desc(t))

# Every ordinal in the first list is below every ordinal in the second.
def Ords.below_all(+xs: List<&2, U32>, +ys: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(Ords.lt_all(x, ys), Ords.below_all(t, ys))

# ---------------------------------------------------------------------------
# Comparing ordinals is comparing their values.
# ---------------------------------------------------------------------------

law Nat.cmp_is_lt:
  for +m: Nat
  for +n: Nat
  {Cmp.is_lt(Nat.cmp(m, n)) == C.Nat.gt(n, m) : Bool}

def Nat.cmp_is_lt(m, n):
  match m:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      match n:
        case 0n:
          {==}
        case 1n+q:
          Nat.cmp_is_lt(p, q)

law U32.is_lt_nat:
  for +x: U32
  for +y: U32
  {U32.is_lt(x, y) == C.Nat.gt(U32.to_nat(y), U32.to_nat(x)) : Bool}

def U32.is_lt_nat(x, y):
  %E.Cmp.sym(U32.cmp(x, y),
    Nat.cmp(U32.to_nat(x), U32.to_nat(y)), Or.U32.cmp_spec(x, y))
    : {Cmp.is_lt(_) == C.Nat.gt(U32.to_nat(y), U32.to_nat(x)) : Bool}
  Nat.cmp_is_lt(U32.to_nat(x), U32.to_nat(y))

law U32.lt_of_nat:
  for +x: U32
  for +y: U32
  for +g: {C.Nat.gt(U32.to_nat(y), U32.to_nat(x)) == True{} : Bool}
  {U32.is_lt(x, y) == True{} : Bool}

def U32.lt_of_nat(x, y, g):
  %E.Bool.sym(U32.is_lt(x, y),
    C.Nat.gt(U32.to_nat(y), U32.to_nat(x)), U32.is_lt_nat(x, y))
    : {_ == True{} : Bool}
  g

# ---------------------------------------------------------------------------
# Turning a descending list around.
# ---------------------------------------------------------------------------

law Ords.below_cons:
  for +t: List<&2, U32>
  for +h: U32
  for +acc: List<&2, U32>
  for +gt: {Ords.gt_all(h, t) == True{} : Bool}
  for +ba: {Ords.below_all(t, acc) == True{} : Bool}
  {Ords.below_all(t, Con{h, acc}) == True{} : Bool}

def Ords.below_cons(t, h, acc, gt, ba):
  match t:
    case Nil{}:
      {==}
    case Con{x, u}:
      E.Bool.and_both(Ords.lt_all(x, Con{h, acc}),
          Ords.below_all(u, Con{h, acc}),
          E.Bool.and_both(U32.is_lt(x, h), Ords.lt_all(x, acc),
            E.Bool.and_l(U32.is_lt(x, h), Ords.gt_all(h, u), gt),
            E.Bool.and_l(Ords.lt_all(x, acc),
              Ords.below_all(u, acc), ba)),
          Ords.below_cons(u, h, acc,
            E.Bool.and_r(U32.is_lt(x, h), Ords.gt_all(h, u), gt),
            E.Bool.and_r(Ords.lt_all(x, acc),
              Ords.below_all(u, acc), ba)))

law Ords.asc_reverse_go:
  for +l: List<&2, U32>
  for +acc: List<&2, U32>
  for +dl: {Ords.desc(l) == True{} : Bool}
  for +aa: {Ords.asc(acc) == True{} : Bool}
  for +ba: {Ords.below_all(l, acc) == True{} : Bool}
  {Ords.asc(List.reverse.go(&2, U32, l, acc)) == True{} : Bool}

law Ords.asc_reverse:
  for +l: List<&2, U32>
  for +dl: {Ords.desc(l) == True{} : Bool}
  {Ords.asc(List.reverse(&2, U32, l)) == True{} : Bool}

law Ords.below_nil:
  for +l: List<&2, U32>
  {Ords.below_all(l, Nil{}) == True{} : Bool}

def Ords.below_nil(l):
  match l:
    case Nil{}:
      {==}
    case Con{x, t}:
      Ords.below_nil(t)

law Nat.cmp_lt_gt:
  for +m: Nat
  for +n: Nat
  for +e: {Nat.cmp(m, n) == LT{} : Cmp}
  {C.Nat.gt(n, m) == True{} : Bool}

def Nat.cmp_lt_gt(m, n, e):
  %Nat.cmp_is_lt(m, n)
    : {_ == True{} : Bool}
  %E.Cmp.sym(Nat.cmp(m, n), LT{}, e)
    : {Cmp.is_lt(_) == True{} : Bool}
  {==}

law Nat.cmp_gt_gt:
  for +m: Nat
  for +n: Nat
  for +e: {Nat.cmp(m, n) == GT{} : Cmp}
  {C.Nat.gt(m, n) == True{} : Bool}

law Nat.cmp_flip:
  for +m: Nat
  for +n: Nat
  for +e: {Nat.cmp(m, n) == GT{} : Cmp}
  {Nat.cmp(n, m) == LT{} : Cmp}

def Nat.cmp_flip(m, n, e):
  match m:
    case 0n:
      match n:
        case 0n:
          E.Cmp.noconf_eq_gt({Nat.cmp(0n, 0n) == LT{} : Cmp}, e)
        case 1n+q:
          E.Cmp.noconf_lt_gt({Nat.cmp(1n+q, 0n) == LT{} : Cmp}, e)
    case 1n+p:
      match n:
        case 0n:
          {==}
        case 1n+q:
          Nat.cmp_flip(p, q, e)

def Nat.cmp_gt_gt(m, n, e):
  %Nat.cmp_is_lt(n, m)
    : {_ == True{} : Bool}
  %E.Cmp.sym(Nat.cmp(n, m), LT{}, Nat.cmp_flip(m, n, e))
    : {Cmp.is_lt(_) == True{} : Bool}
  {==}

law U32.lt_of_cmp_lt:
  for +x: U32
  for +y: U32
  for +e: {U32.cmp(x, y) == LT{} : Cmp}
  {U32.is_lt(x, y) == True{} : Bool}

def Cmp.nat_of_u32_lt(+x: U32, +y: U32,
  +e: {U32.cmp(x, y) == LT{} : Cmp})
  -> {Nat.cmp(U32.to_nat(x), U32.to_nat(y)) == LT{} : Cmp}:
  %Or.U32.cmp_spec(x, y)
    : {_ == LT{} : Cmp}
  e

def U32.lt_of_cmp_lt(x, y, e):
  U32.lt_of_nat(x, y,
    Nat.cmp_lt_gt(U32.to_nat(x), U32.to_nat(y),
      Cmp.nat_of_u32_lt(x, y, e)))

law Nat.cmp_of_gt:
  for +m: Nat
  for +n: Nat
  for +g: {C.Nat.gt(m, n) == True{} : Bool}
  {Nat.cmp(m, n) == GT{} : Cmp}

def Nat.cmp_of_gt(m, n, g):
  match m:
    case 0n:
      E.Bool.noconf({Nat.cmp(0n, n) == GT{} : Cmp}, g)
    case 1n+p:
      match n:
        case 0n:
          {==}
        case 1n+q:
          Nat.cmp_of_gt(p, q, g)

law U32.ne_of_lt:
  for +y: U32
  for +h: U32
  for +lt: {U32.is_lt(y, h) == True{} : Bool}
  {U32.is_eq(h, y) == False{} : Bool}

law U32.ne_of_gt:
  for +h: U32
  for +y: U32
  for +lt: {U32.is_lt(h, y) == True{} : Bool}
  {U32.is_eq(h, y) == False{} : Bool}

law Ords.lt_value:
  for +x: U32
  for +y: U32
  for +lt: {U32.is_lt(x, y) == True{} : Bool}
  {C.Nat.gt(U32.to_nat(y), U32.to_nat(x)) == True{} : Bool}

def Ords.lt_value(x, y, lt):
  %U32.is_lt_nat(x, y)
    : {_ == True{} : Bool}
  lt

def U32.ne_of_lt(y, h, lt):
  %E.Cmp.sym(U32.cmp(h, y),
    Nat.cmp(U32.to_nat(h), U32.to_nat(y)), Or.U32.cmp_spec(h, y))
    : {Cmp.is_eq(_) == False{} : Bool}
  %E.Cmp.sym(Nat.cmp(U32.to_nat(h), U32.to_nat(y)), GT{},
    Nat.cmp_of_gt(U32.to_nat(h), U32.to_nat(y),
      Ords.lt_value(y, h, lt)))
    : {Cmp.is_eq(_) == False{} : Bool}
  {==}

def U32.ne_of_gt(h, y, lt):
  %E.Cmp.sym(U32.cmp(h, y),
    Nat.cmp(U32.to_nat(h), U32.to_nat(y)), Or.U32.cmp_spec(h, y))
    : {Cmp.is_eq(_) == False{} : Bool}
  %E.Cmp.sym(Nat.cmp(U32.to_nat(h), U32.to_nat(y)), LT{},
    Nat.cmp_flip(U32.to_nat(y), U32.to_nat(h),
      Nat.cmp_of_gt(U32.to_nat(y), U32.to_nat(h),
        Ords.lt_value(h, y, lt))))
    : {Cmp.is_eq(_) == False{} : Bool}
  {==}

law Ords.not_contains_of_lt_all:
  for +xs: List<&2, U32>
  for +y: U32
  for +la: {Ords.lt_all(y, xs) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, xs, y) == False{} : Bool}

def Ords.not_contains_of_lt_all(xs, y, la):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %E.Bool.sym(U32.is_eq(h, y), False{},
        U32.ne_of_lt(y, h,
          E.Bool.and_l(U32.is_lt(y, h), Ords.lt_all(y, t), la)))
        : {Bool.or(_, List.contains(~U32, ~U32.is_eq, t, y))
          == False{} : Bool}
      Ords.not_contains_of_lt_all(t, y,
        E.Bool.and_r(U32.is_lt(y, h), Ords.lt_all(y, t), la))

law Ords.not_contains_of_gt_all:
  for +xs: List<&2, U32>
  for +y: U32
  for +ga: {Ords.gt_all(y, xs) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, xs, y) == False{} : Bool}

def Ords.not_contains_of_gt_all(xs, y, ga):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %E.Bool.sym(U32.is_eq(h, y), False{},
        U32.ne_of_gt(h, y,
          E.Bool.and_l(U32.is_lt(h, y), Ords.gt_all(y, t), ga)))
        : {Bool.or(_, List.contains(~U32, ~U32.is_eq, t, y))
          == False{} : Bool}
      Ords.not_contains_of_gt_all(t, y,
        E.Bool.and_r(U32.is_lt(h, y), Ords.gt_all(y, t), ga))

law Ords.lt_all_trans:
  for +t: List<&2, U32>
  for +y: U32
  for +h: U32
  for +lt: {U32.is_lt(y, h) == True{} : Bool}
  for +la: {Ords.lt_all(h, t) == True{} : Bool}
  {Ords.lt_all(y, t) == True{} : Bool}

law Nat.le_of_gt_lt:
  for +m: Nat
  for +n: Nat
  for +g: {C.Nat.gt(n, m) == True{} : Bool}
  {C.Nat.upto(m, n) == True{} : Bool}

def Nat.le_of_gt_lt(m, n, g):
  match m:
    case 0n:
      {==}
    case 1n+p:
      match n:
        case 0n:
          E.Bool.noconf({C.Nat.upto(1n+p, 0n) == True{} : Bool}, g)
        case 1n+q:
          Nat.le_of_gt_lt(p, q, g)

def Ords.lt_all_trans(t, y, h, lt, la):
  match t:
    case Nil{}:
      {==}
    case Con{z, u}:
      E.Bool.and_both(U32.is_lt(y, z), Ords.lt_all(y, u),
        U32.lt_of_nat(y, z,
          Ct2.Nat.gt_up(U32.to_nat(h), U32.to_nat(z), U32.to_nat(y),
            Nat.le_of_gt_lt(U32.to_nat(h), U32.to_nat(z),
              Ords.lt_value(h, z,
                E.Bool.and_l(U32.is_lt(h, z), Ords.lt_all(h, u), la))),
            Ords.lt_value(y, h, lt))),
        Ords.lt_all_trans(u, y, h, lt,
          E.Bool.and_r(U32.is_lt(h, z), Ords.lt_all(h, u), la)))

law U32.lt_of_cmp_gt:
  for +x: U32
  for +y: U32
  for +e: {U32.cmp(x, y) == GT{} : Cmp}
  {U32.is_lt(y, x) == True{} : Bool}

def Cmp.nat_of_u32_gt(+x: U32, +y: U32,
  +e: {U32.cmp(x, y) == GT{} : Cmp})
  -> {Nat.cmp(U32.to_nat(x), U32.to_nat(y)) == GT{} : Cmp}:
  %Or.U32.cmp_spec(x, y)
    : {_ == GT{} : Cmp}
  e

def U32.lt_of_cmp_gt(x, y, e):
  U32.lt_of_nat(y, x,
    Nat.cmp_gt_gt(U32.to_nat(x), U32.to_nat(y),
      Cmp.nat_of_u32_gt(x, y, e)))

law U32.eq_of_cmp_eq:
  for +x: U32
  for +y: U32
  for +e: {U32.cmp(x, y) == EQ{} : Cmp}
  {x == y : U32}

def U32.is_eq_of_cmp(+x: U32, +y: U32,
  +e: {U32.cmp(x, y) == EQ{} : Cmp})
  -> {U32.is_eq(x, y) == True{} : Bool}:
  %E.Cmp.sym(U32.cmp(x, y), EQ{}, e)
    : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def U32.eq_of_cmp_eq(x, y, e):
  E.U32.eq_reflect(x, y, U32.is_eq_of_cmp(x, y, e))

law Ords.lt_all_of_asc:
  for +t: List<&2, U32>
  for +h: U32
  for +a: {Ords.asc(Con{h, t}) == True{} : Bool}
  {Ords.lt_all(h, t) == True{} : Bool}

def Ords.lt_all_of_asc(t, h, a):
  match t:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(U32.is_lt(h, y), Ords.lt_all(h, u),
        E.Bool.and_l(U32.is_lt(h, y), Ords.asc(Con{y, u}), a),
        Ords.lt_all_trans(u, h, y,
          E.Bool.and_l(U32.is_lt(h, y), Ords.asc(Con{y, u}), a),
          Ords.lt_all_of_asc(u, y,
            E.Bool.and_r(U32.is_lt(h, y), Ords.asc(Con{y, u}), a))))

law Ords.above_of_lt_all:
  for +t: List<&2, U32>
  for +h: U32
  for +la: {Ords.lt_all(h, t) == True{} : Bool}
  {Ords.above(h, t) == True{} : Bool}

def Ords.above_of_lt_all(t, h, la):
  match t:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_l(U32.is_lt(h, y), Ords.lt_all(h, u), la)

def Ords.asc_reverse_go(l, acc, dl, aa, ba):
  match l:
    case Nil{}:
      aa
    case Con{h, t}:
      Ords.asc_reverse_go(t, Con{h, acc},
        E.Bool.and_r(Ords.gt_all(h, t), Ords.desc(t), dl),
        E.Bool.and_both(Ords.above(h, acc), Ords.asc(acc),
          Ords.above_of_lt_all(acc, h,
            E.Bool.and_l(Ords.lt_all(h, acc),
              Ords.below_all(t, acc), ba)), aa),
        Ords.below_cons(t, h, acc,
          E.Bool.and_l(Ords.gt_all(h, t), Ords.desc(t), dl),
          E.Bool.and_r(Ords.lt_all(h, acc), Ords.below_all(t, acc),
            ba)))

def Ords.asc_reverse(l, dl):
  Ords.asc_reverse_go(l, Nil{}, dl, {==}, Ords.below_nil(l))

# ---------------------------------------------------------------------------
# What a comparison tells the merge.
# ---------------------------------------------------------------------------
