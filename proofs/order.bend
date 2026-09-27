# proofs/order.bend -- machine-word comparison agrees with the numeric order
# (addressing fact A1, in full).
#
# `Word.cmp` walks the vector comparing the high bits first with the low bit
# as the tiebreak; `Nat.cmp` walks two unary numbers. They agree, which is
# what lets a proof move between "this ordinal is smaller" and "this number is
# smaller" -- and that is what the ascending-offsets invariant of a sparse
# leaf is stated with.
#
# The power-of-two case was enough for the set tree's descent and was proved
# earlier (proofs/descend.bend). This is the general statement.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./split.bend as Sp
import ../core/count.bend as C
import ../core/word.bend as W

# ---------------------------------------------------------------------------
# Doubling and the order.
# ---------------------------------------------------------------------------

law Nat.cmp_double_lt:
  for +ta: Nat
  for +tb: Nat
  for +na: Nat
  for +nb: Nat
  for +lt: {Nat.cmp(ta, tb) == LT{} : Cmp}
  for +ba: {C.Nat.upto(na, 1n) == True{} : Bool}
  {Nat.cmp(Nat.add(Nat.double(ta), na), Nat.add(Nat.double(tb), nb))
    == LT{} : Cmp}

law Nat.cmp_zero_lt:
  for +na: Nat
  for +qb: Nat
  for +nb: Nat
  for +ba: {C.Nat.upto(na, 1n) == True{} : Bool}
  {Nat.cmp(Nat.add(0n, na), Nat.add(Nat.double(1n+qb), nb))
    == LT{} : Cmp}

def Nat.cmp_zero_lt(na, qb, nb, ba):
  match na:
    case 0n:
      {==}
    case 1n+e:
      match e:
        case 0n:
          {==}
        case 1n+f:
          E.Bool.noconf({Nat.cmp(2n+f,
            Nat.add(Nat.double(1n+qb), nb)) == LT{} : Cmp}, ba)

def Nat.cmp_double_lt(ta, tb, na, nb, lt, ba):
  match ta:
    case 0n:
      match tb:
        case 0n:
          E.Cmp.eq_not_lt({Nat.cmp(Nat.add(0n, na), Nat.add(0n, nb))
            == LT{} : Cmp}, lt)
        case 1n+qb:
          Nat.cmp_zero_lt(na, qb, nb, ba)
    case 1n+qa:
      match tb:
        case 0n:
          E.Cmp.gt_not_lt({Nat.cmp(Nat.add(Nat.double(1n+qa), na),
            Nat.add(0n, nb)) == LT{} : Cmp}, lt)
        case 1n+qb:
          Nat.cmp_double_lt(qa, qb, na, nb, lt, ba)

law Nat.cmp_double_gt:
  for +ta: Nat
  for +tb: Nat
  for +na: Nat
  for +nb: Nat
  for +gt: {Nat.cmp(ta, tb) == GT{} : Cmp}
  for +bb: {C.Nat.upto(nb, 1n) == True{} : Bool}
  {Nat.cmp(Nat.add(Nat.double(ta), na), Nat.add(Nat.double(tb), nb))
    == GT{} : Cmp}

law Nat.cmp_zero_gt:
  for +nb: Nat
  for +qa: Nat
  for +na: Nat
  for +bb: {C.Nat.upto(nb, 1n) == True{} : Bool}
  {Nat.cmp(Nat.add(Nat.double(1n+qa), na), Nat.add(0n, nb))
    == GT{} : Cmp}

def Nat.cmp_zero_gt(nb, qa, na, bb):
  match nb:
    case 0n:
      {==}
    case 1n+e:
      match e:
        case 0n:
          {==}
        case 1n+f:
          E.Bool.noconf({Nat.cmp(Nat.add(Nat.double(1n+qa), na), 2n+f)
            == GT{} : Cmp}, bb)

def Nat.cmp_double_gt(ta, tb, na, nb, gt, bb):
  match ta:
    case 0n:
      match tb:
        case 0n:
          E.Cmp.eq_not_gt({Nat.cmp(Nat.add(0n, na), Nat.add(0n, nb))
            == GT{} : Cmp}, gt)
        case 1n+qb:
          E.Cmp.lt_not_gt({Nat.cmp(Nat.add(0n, na),
            Nat.add(Nat.double(1n+qb), nb)) == GT{} : Cmp}, gt)
    case 1n+qa:
      match tb:
        case 0n:
          Nat.cmp_zero_gt(nb, qa, na, bb)
        case 1n+qb:
          Nat.cmp_double_gt(qa, qb, na, nb, gt, bb)

law Nat.cmp_double_eq:
  for +t: Nat
  for +na: Nat
  for +nb: Nat
  {Nat.cmp(Nat.add(Nat.double(t), na), Nat.add(Nat.double(t), nb))
    == Nat.cmp(na, nb) : Cmp}

def Nat.cmp_double_eq(t, na, nb):
  match t:
    case 0n:
      {==}
    case 1n+q:
      Nat.cmp_double_eq(q, na, nb)

law Nat.cmp_eq_same:
  for +a: Nat
  for +b: Nat
  for +e: {Nat.cmp(a, b) == EQ{} : Cmp}
  {a == b : Nat}

def Nat.cmp_eq_same(a, b, e):
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          E.Cmp.lt_not_eq({0n == 1n+q : Nat}, e)
    case 1n+p:
      match b:
        case 0n:
          E.Cmp.gt_not_eq({1n+p == 0n : Nat}, e)
        case 1n+q:
          %Nat.cmp_eq_same(p, q, e) : {1n+p == 1n+_ : Nat}
          {==}

# ---------------------------------------------------------------------------
# The comparison agrees with the numeric order.
# ---------------------------------------------------------------------------

law Bool.cmp_nat:
  for +a: Bool
  for +b: Bool
  {Bool.cmp(a, b) == Nat.cmp(Dc.Bool.nat2(a), Dc.Bool.nat2(b)) : Cmp}

def Bool.cmp_nat(a, b):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

law Bool.nat2_le:
  for +a: Bool
  {C.Nat.upto(Dc.Bool.nat2(a), 1n) == True{} : Bool}

def Bool.nat2_le(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law Word.cmp_spec:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.cmp(n, a, b)
    == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}

law Word.cmp_spec.step:
  for +p: Nat
  for +ab: Bool
  for +bb: Bool
  for +at: Word(p)
  for +bt: Word(p)
  for +ih: {Word.cmp(p, at, bt)
    == Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)) : Cmp}
  for +c: Cmp
  for +ec: {c == Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)) : Cmp}
  {Word.cmp(1n+p, WCon{ab, at}, WCon{bb, bt})
    == Nat.cmp(Word.to_nat(1n+p, WCon{ab, at}),
         Word.to_nat(1n+p, WCon{bb, bt})) : Cmp}

law Word.cmp_spec.arm:
  for +ta: Nat
  for +tb: Nat
  for +ab: Bool
  for +bb: Bool
  for +c: Cmp
  for +ec: {c == Nat.cmp(ta, tb) : Cmp}
  {Word.cmp.fin(ab, bb, Nat.cmp(ta, tb))
    == Nat.cmp(Nat.add(Nat.double(ta), Dc.Bool.nat2(ab)),
         Nat.add(Nat.double(tb), Dc.Bool.nat2(bb))) : Cmp}

def Word.cmp_spec.arm(ta, tb, ab, bb, c, ec):
  match c:
    case LT{}:
      %ec : {Word.cmp.fin(ab, bb, _)
          == Nat.cmp(Nat.add(Nat.double(ta), Dc.Bool.nat2(ab)),
               Nat.add(Nat.double(tb), Dc.Bool.nat2(bb))) : Cmp}
      E.Cmp.sym(Nat.cmp(Nat.add(Nat.double(ta), Dc.Bool.nat2(ab)),
          Nat.add(Nat.double(tb), Dc.Bool.nat2(bb))), LT{},
        Nat.cmp_double_lt(ta, tb, Dc.Bool.nat2(ab), Dc.Bool.nat2(bb),
          E.Cmp.sym(c, Nat.cmp(ta, tb), ec), Bool.nat2_le(ab)))
    case GT{}:
      %ec : {Word.cmp.fin(ab, bb, _)
          == Nat.cmp(Nat.add(Nat.double(ta), Dc.Bool.nat2(ab)),
               Nat.add(Nat.double(tb), Dc.Bool.nat2(bb))) : Cmp}
      E.Cmp.sym(Nat.cmp(Nat.add(Nat.double(ta), Dc.Bool.nat2(ab)),
          Nat.add(Nat.double(tb), Dc.Bool.nat2(bb))), GT{},
        Nat.cmp_double_gt(ta, tb, Dc.Bool.nat2(ab), Dc.Bool.nat2(bb),
          E.Cmp.sym(c, Nat.cmp(ta, tb), ec), Bool.nat2_le(bb)))
    case EQ{}:
      %ec : {Word.cmp.fin(ab, bb, _)
          == Nat.cmp(Nat.add(Nat.double(ta), Dc.Bool.nat2(ab)),
               Nat.add(Nat.double(tb), Dc.Bool.nat2(bb))) : Cmp}
      %Nat.cmp_eq_same(ta, tb, E.Cmp.sym(c, Nat.cmp(ta, tb), ec))
        : {Bool.cmp(ab, bb)
          == Nat.cmp(Nat.add(Nat.double(ta), Dc.Bool.nat2(ab)),
               Nat.add(Nat.double(_), Dc.Bool.nat2(bb))) : Cmp}
      %E.Cmp.sym(Nat.cmp(Nat.add(Nat.double(ta), Dc.Bool.nat2(ab)),
      Nat.add(Nat.double(ta), Dc.Bool.nat2(bb))),
    Nat.cmp(Dc.Bool.nat2(ab), Dc.Bool.nat2(bb)),
    Nat.cmp_double_eq(ta, Dc.Bool.nat2(ab), Dc.Bool.nat2(bb)))
        : {Bool.cmp(ab, bb) == _ : Cmp}
      Bool.cmp_nat(ab, bb)

def Word.cmp_spec.step(p, ab, bb, at, bt, ih, c, ec):
  %E.Cmp.sym(Word.cmp(p, at, bt),
    Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), ih)
    : {Word.cmp.fin(ab, bb, _)
    == Nat.cmp(Word.to_nat(1n+p, WCon{ab, at}),
         Word.to_nat(1n+p, WCon{bb, bt})) : Cmp}
  %E.Nat.sym(Word.to_nat(1n+p, WCon{ab, at}),
    Nat.add(Nat.double(Word.to_nat(p, at)), Dc.Bool.nat2(ab)),
    Dc.Word.to_nat_cons3(p, ab, at))
    : {Word.cmp.fin(ab, bb,
        Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)))
      == Nat.cmp(_, Word.to_nat(1n+p, WCon{bb, bt})) : Cmp}
  %E.Nat.sym(Word.to_nat(1n+p, WCon{bb, bt}),
    Nat.add(Nat.double(Word.to_nat(p, bt)), Dc.Bool.nat2(bb)),
    Dc.Word.to_nat_cons3(p, bb, bt))
    : {Word.cmp.fin(ab, bb,
        Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)))
      == Nat.cmp(Nat.add(Nat.double(Word.to_nat(p, at)),
           Dc.Bool.nat2(ab)), _) : Cmp}
  Word.cmp_spec.arm(Word.to_nat(p, at), Word.to_nat(p, bt), ab, bb, c, ec)

def Word.cmp_spec(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          Word.cmp_spec.step(p, ab, bb, at, bt,
            Word.cmp_spec(p, at, bt),
            Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), {==})

law U32.cmp_spec:
  for +a: U32
  for +b: U32
  {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}

def U32.cmp_spec(a, b):
  match a b:
    case U32{x} U32{y}:
      Word.cmp_spec(32n, x, y)

law U32.is_lt_spec:
  for +a: U32
  for +b: U32
  {U32.is_lt(a, b) == Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) : Bool}

def U32.is_lt_spec(a, b):
  Equal.cong(Cmp, Bool, Cmp.is_lt, U32.cmp(a, b),
    Nat.cmp(U32.to_nat(a), U32.to_nat(b)), U32.cmp_spec(a, b))

law U32.is_gt_spec:
  for +a: U32
  for +b: U32
  {U32.is_gt(a, b) == Nat.is_gt(U32.to_nat(a), U32.to_nat(b)) : Bool}

def U32.is_gt_spec(a, b):
  Equal.cong(Cmp, Bool, Cmp.is_gt, U32.cmp(a, b),
    Nat.cmp(U32.to_nat(a), U32.to_nat(b)), U32.cmp_spec(a, b))
