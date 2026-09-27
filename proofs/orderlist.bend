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

def Ords.asc(+xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Ords.lt_all(h, t), Ords.asc(t))

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

def Ords.asc_reverse_go(l, acc, dl, aa, ba):
  match l:
    case Nil{}:
      aa
    case Con{h, t}:
      Ords.asc_reverse_go(t, Con{h, acc},
        E.Bool.and_r(Ords.gt_all(h, t), Ords.desc(t), dl),
        E.Bool.and_both(Ords.lt_all(h, acc), Ords.asc(acc),
          E.Bool.and_l(Ords.lt_all(h, acc), Ords.below_all(t, acc),
            ba), aa),
        Ords.below_cons(t, h, acc,
          E.Bool.and_l(Ords.gt_all(h, t), Ords.desc(t), dl),
          E.Bool.and_r(Ords.lt_all(h, acc), Ords.below_all(t, acc),
            ba)))

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

def Ords.asc_reverse(l, dl):
  Ords.asc_reverse_go(l, Nil{}, dl, {==}, Ords.below_nil(l))
