# proofs/merge.bend -- what the merge-based difference contains.
#
# `Ords.diff` walks two ascending lists in step, emitting the ordinals of the
# first that the second does not hold. This says so: an ordinal is in the
# result exactly when it is in the first list and not in the second.
#
# Ascending is not decoration. The merge decides by comparing heads and never
# looks back, so a list out of order would have it drop ordinals it should
# keep. The three comparison answers are the three arms, and each needs one
# fact about the head it just skipped: it is not in the other list, because
# everything in that list is above it.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./orderlist.bend as Ol
import ./split_add.bend as Sa
import ./interval.bend as It
import ./childtest.bend as Ct
import ./treeenum.bend as Te
import ../core/count.bend as C
import ../core/ords.bend as O
import ../core/word.bend as W

# ---------------------------------------------------------------------------
# The three Bool identities, one per comparison answer.
# ---------------------------------------------------------------------------

law Ords.diff_lt_step:
  for +ah: U32
  for +x: U32
  for +e: Bool
  for +at: List<&2, U32>
  for +b: List<&2, U32>
  for +rest: Bool
  for +ee: {e == U32.is_eq(ah, x) : Bool}
  for +nb: {List.contains(~U32, ~U32.is_eq, b, ah) == False{} : Bool}
  for +ih: {rest == Bool.and(List.contains(~U32, ~U32.is_eq, at, x),
    Bool.not(List.contains(~U32, ~U32.is_eq, b, x))) : Bool}
  {Bool.or(U32.is_eq(ah, x), rest)
    == Bool.and(Bool.or(U32.is_eq(ah, x),
         List.contains(~U32, ~U32.is_eq, at, x)),
         Bool.not(List.contains(~U32, ~U32.is_eq, b, x))) : Bool}

def Ords.diff_lt_step(ah, x, e, at, b, rest, ee, nb, ih):
  match e:
    case True{}:
      %ee
        : {Bool.or(_, rest)
          == Bool.and(Bool.or(_,
               List.contains(~U32, ~U32.is_eq, at, x)),
               Bool.not(List.contains(~U32, ~U32.is_eq, b, x)))
          : Bool}
      %E.U32.eq_reflect(ah, x,
        E.Bool.sym(True{}, U32.is_eq(ah, x), ee))
        : {True{}
          == Bool.not(List.contains(~U32, ~U32.is_eq, b, _)) : Bool}
      %E.Bool.sym(List.contains(~U32, ~U32.is_eq, b, ah), False{}, nb)
        : {True{} == Bool.not(_) : Bool}
      {==}
    case False{}:
      %ee
        : {Bool.or(_, rest)
          == Bool.and(Bool.or(_,
               List.contains(~U32, ~U32.is_eq, at, x)),
               Bool.not(List.contains(~U32, ~U32.is_eq, b, x)))
          : Bool}
      ih

law Ords.diff_gt_step:
  for +bh: U32
  for +x: U32
  for +e: Bool
  for +a: List<&2, U32>
  for +bt: List<&2, U32>
  for +rest: Bool
  for +ee: {e == U32.is_eq(bh, x) : Bool}
  for +na: {List.contains(~U32, ~U32.is_eq, a, bh) == False{} : Bool}
  for +ih: {rest == Bool.and(List.contains(~U32, ~U32.is_eq, a, x),
    Bool.not(List.contains(~U32, ~U32.is_eq, bt, x))) : Bool}
  {rest == Bool.and(List.contains(~U32, ~U32.is_eq, a, x),
    Bool.not(Bool.or(U32.is_eq(bh, x),
      List.contains(~U32, ~U32.is_eq, bt, x)))) : Bool}

def Ords.diff_gt_zero(+bh: U32, +x: U32, +a: List<&2, U32>,
  +bt: List<&2, U32>, +rest: Bool,
  +ee: {True{} == U32.is_eq(bh, x) : Bool},
  +na: {List.contains(~U32, ~U32.is_eq, a, bh) == False{} : Bool},
  +ih: {rest == Bool.and(List.contains(~U32, ~U32.is_eq, a, x),
    Bool.not(List.contains(~U32, ~U32.is_eq, bt, x))) : Bool})
  -> {rest == False{} : Bool}:
  %E.Bool.sym(rest,
    Bool.and(List.contains(~U32, ~U32.is_eq, a, x),
      Bool.not(List.contains(~U32, ~U32.is_eq, bt, x))), ih)
    : {_ == False{} : Bool}
  %E.U32.eq_reflect(bh, x,
    E.Bool.sym(True{}, U32.is_eq(bh, x), ee))
    : {Bool.and(List.contains(~U32, ~U32.is_eq, a, _),
        Bool.not(List.contains(~U32, ~U32.is_eq, bt, _)))
      == False{} : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq, a, bh), False{}, na)
    : {Bool.and(_,
        Bool.not(List.contains(~U32, ~U32.is_eq, bt, bh)))
      == False{} : Bool}
  {==}

def Ords.diff_gt_step(bh, x, e, a, bt, rest, ee, na, ih):
  match e:
    case True{}:
      %ee
        : {rest == Bool.and(List.contains(~U32, ~U32.is_eq, a, x),
            Bool.not(Bool.or(_,
              List.contains(~U32, ~U32.is_eq, bt, x)))) : Bool}
      %E.Bool.sym(Bool.and(List.contains(~U32, ~U32.is_eq, a, x),
          False{}), False{},
        Sa.Word.and_false_r(List.contains(~U32, ~U32.is_eq, a, x)))
        : {rest == _ : Bool}
      Ords.diff_gt_zero(bh, x, a, bt, rest, ee, na, ih)
    case False{}:
      %ee
        : {rest == Bool.and(List.contains(~U32, ~U32.is_eq, a, x),
            Bool.not(Bool.or(_,
              List.contains(~U32, ~U32.is_eq, bt, x)))) : Bool}
      ih

def Ords.diff_eq_zero(+ah: U32, +x: U32, +at: List<&2, U32>,
  +bt: List<&2, U32>, +rest: Bool,
  +ee: {True{} == U32.is_eq(ah, x) : Bool},
  +nat: {List.contains(~U32, ~U32.is_eq, at, ah) == False{} : Bool},
  +ih: {rest == Bool.and(List.contains(~U32, ~U32.is_eq, at, x),
    Bool.not(List.contains(~U32, ~U32.is_eq, bt, x))) : Bool})
  -> {rest == False{} : Bool}:
  %E.Bool.sym(rest,
    Bool.and(List.contains(~U32, ~U32.is_eq, at, x),
      Bool.not(List.contains(~U32, ~U32.is_eq, bt, x))), ih)
    : {_ == False{} : Bool}
  %E.U32.eq_reflect(ah, x,
    E.Bool.sym(True{}, U32.is_eq(ah, x), ee))
    : {Bool.and(List.contains(~U32, ~U32.is_eq, at, _),
        Bool.not(List.contains(~U32, ~U32.is_eq, bt, x)))
      == False{} : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq, at, ah), False{}, nat)
    : {Bool.and(_,
        Bool.not(List.contains(~U32, ~U32.is_eq, bt, x)))
      == False{} : Bool}
  {==}

law Ords.diff_eq_step:
  for +ah: U32
  for +bh: U32
  for +x: U32
  for +e: Bool
  for +at: List<&2, U32>
  for +bt: List<&2, U32>
  for +rest: Bool
  for +eab: {ah == bh : U32}
  for +ee: {e == U32.is_eq(ah, x) : Bool}
  for +nat: {List.contains(~U32, ~U32.is_eq, at, ah) == False{}
    : Bool}
  for +ih: {rest == Bool.and(List.contains(~U32, ~U32.is_eq, at, x),
    Bool.not(List.contains(~U32, ~U32.is_eq, bt, x))) : Bool}
  {rest == Bool.and(Bool.or(U32.is_eq(ah, x),
    List.contains(~U32, ~U32.is_eq, at, x)),
    Bool.not(Bool.or(U32.is_eq(bh, x),
      List.contains(~U32, ~U32.is_eq, bt, x)))) : Bool}

def Ords.diff_eq_step(ah, bh, x, e, at, bt, rest, eab, ee, nat, ih):
  match e:
    case True{}:
      %eab
        : {rest == Bool.and(Bool.or(U32.is_eq(ah, x),
            List.contains(~U32, ~U32.is_eq, at, x)),
            Bool.not(Bool.or(U32.is_eq(_, x),
              List.contains(~U32, ~U32.is_eq, bt, x)))) : Bool}
      %ee
        : {rest == Bool.and(Bool.or(_,
            List.contains(~U32, ~U32.is_eq, at, x)),
            Bool.not(Bool.or(_,
              List.contains(~U32, ~U32.is_eq, bt, x)))) : Bool}
      Ords.diff_eq_zero(ah, x, at, bt, rest, ee, nat, ih)
    case False{}:
      %eab
        : {rest == Bool.and(Bool.or(U32.is_eq(ah, x),
            List.contains(~U32, ~U32.is_eq, at, x)),
            Bool.not(Bool.or(U32.is_eq(_, x),
              List.contains(~U32, ~U32.is_eq, bt, x)))) : Bool}
      %ee
        : {rest == Bool.and(Bool.or(_,
            List.contains(~U32, ~U32.is_eq, at, x)),
            Bool.not(Bool.or(_,
              List.contains(~U32, ~U32.is_eq, bt, x)))) : Bool}
      ih

# ---------------------------------------------------------------------------
# The merge itself.
# ---------------------------------------------------------------------------

law Ords.diff_go_contains:
  for +fuel: Nat
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +c: Cmp
  for +x: U32
  for +ec: {c == O.Ords.head_cmp(a, b) : Cmp}
  for +aa: {Ol.Ords.asc(a) == True{} : Bool}
  for +ab: {Ol.Ords.asc(b) == True{} : Bool}
  for +fu: {C.Nat.upto(O.Ords.merge_fuel(a, b), fuel) == True{}
    : Bool}
  {List.contains(~U32, ~U32.is_eq, O.Ords.diff.go(fuel, a, b, c), x)
    == Bool.and(List.contains(~U32, ~U32.is_eq, a, x),
         Bool.not(List.contains(~U32, ~U32.is_eq, b, x))) : Bool}

law Ords.lt_all_head:
  for +y: U32
  for +h: U32
  for +t: List<&2, U32>
  for +lt: {U32.is_lt(y, h) == True{} : Bool}
  for +la: {Ol.Ords.lt_all(h, t) == True{} : Bool}
  {Ol.Ords.lt_all(y, Con{h, t}) == True{} : Bool}

def Ords.lt_all_head(y, h, t, lt, la):
  E.Bool.and_both(U32.is_lt(y, h), Ol.Ords.lt_all(y, t), lt,
    Ol.Ords.lt_all_trans(t, y, h, lt, la))

law Ords.fuel_gt:
  for +at: List<&2, U32>
  for +bt: List<&2, U32>
  for +f: Nat
  for +fu: {C.Nat.upto(1n+Nat.add(1n+List.length(&2, U32, at),
    1n+List.length(&2, U32, bt)), 1n+f) == True{} : Bool}
  {C.Nat.upto(1n+Nat.add(1n+List.length(&2, U32, at),
    List.length(&2, U32, bt)), f) == True{} : Bool}

def Ords.fuel_gt(at, bt, f, fu):
  It.Nat.upto_cast(
    Nat.add(1n+List.length(&2, U32, at),
      1n+List.length(&2, U32, bt)),
    1n+Nat.add(1n+List.length(&2, U32, at),
      List.length(&2, U32, bt)), f, f,
    N.Nat.add_succ(1n+List.length(&2, U32, at),
      List.length(&2, U32, bt)), {==}, fu)

law Ords.fuel_eq:
  for +at: List<&2, U32>
  for +bt: List<&2, U32>
  for +f: Nat
  for +fu: {C.Nat.upto(1n+Nat.add(1n+List.length(&2, U32, at),
    1n+List.length(&2, U32, bt)), 1n+f) == True{} : Bool}
  {C.Nat.upto(1n+Nat.add(List.length(&2, U32, at),
    List.length(&2, U32, bt)), f) == True{} : Bool}

def Ords.fuel_eq(at, bt, f, fu):
  Ct.Nat.le_trans(1n+Nat.add(List.length(&2, U32, at),
    List.length(&2, U32, bt)),
    1n+Nat.add(1n+List.length(&2, U32, at),
      List.length(&2, U32, bt)), f,
    It.Nat.upto_cast(Nat.add(List.length(&2, U32, at),
      List.length(&2, U32, bt)),
      Nat.add(List.length(&2, U32, at), List.length(&2, U32, bt)),
      1n+Nat.add(List.length(&2, U32, at), List.length(&2, U32, bt)),
      Nat.add(1n+List.length(&2, U32, at), List.length(&2, U32, bt)),
      {==}, {==},
      It.Nat.le_up(Nat.add(List.length(&2, U32, at),
        List.length(&2, U32, bt)),
        Nat.add(List.length(&2, U32, at), List.length(&2, U32, bt)),
        It.Nat.upto_refl(Nat.add(List.length(&2, U32, at),
          List.length(&2, U32, bt))))),
    Ords.fuel_gt(at, bt, f, fu))

def Ords.diff_go_contains(fuel, a, b, c, x, ec, aa, ab, fu):
  match fuel:
    case 0n:
      E.Bool.noconf({List.contains(~U32, ~U32.is_eq,
        O.Ords.diff.go(0n, a, b, c), x)
        == Bool.and(List.contains(~U32, ~U32.is_eq, a, x),
             Bool.not(List.contains(~U32, ~U32.is_eq, b, x)))
        : Bool}, fu)
    case 1n+f:
      match a:
        case Nil{}:
          {==}
        case Con{ah, at}:
          match b:
            case Nil{}:
              E.Bool.sym(Bool.and(
                List.contains(~U32, ~U32.is_eq, Con{ah, at}, x),
                True{}),
                List.contains(~U32, ~U32.is_eq, Con{ah, at}, x),
                Te.Bool.and_true_r(
                  List.contains(~U32, ~U32.is_eq, Con{ah, at}, x)))
            case Con{bh, bt}:
              match c:
                case LT{}:
                  Ords.diff_lt_step(ah, x, U32.is_eq(ah, x), at,
                    Con{bh, bt},
                    List.contains(~U32, ~U32.is_eq,
                      O.Ords.diff.go(f, at, Con{bh, bt},
                        O.Ords.head_cmp(at, Con{bh, bt})), x),
                    {==},
                    Ol.Ords.not_contains_of_lt_all(Con{bh, bt}, ah,
                      Ords.lt_all_head(ah, bh, bt,
                        Ol.U32.lt_of_cmp_lt(ah, bh,
                          E.Cmp.sym(LT{}, U32.cmp(ah, bh), ec)),
                        Ol.Ords.lt_all_of_asc(bt, bh, ab))),
                    Ords.diff_go_contains(f, at, Con{bh, bt},
                      O.Ords.head_cmp(at, Con{bh, bt}), x, {==},
                      E.Bool.and_r(Ol.Ords.above(ah, at),
                        Ol.Ords.asc(at), aa), ab, fu))
                case GT{}:
                  Ords.diff_gt_step(bh, x, U32.is_eq(bh, x),
                    Con{ah, at}, bt,
                    List.contains(~U32, ~U32.is_eq,
                      O.Ords.diff.go(f, Con{ah, at}, bt,
                        O.Ords.head_cmp(Con{ah, at}, bt)), x),
                    {==},
                    Ol.Ords.not_contains_of_lt_all(Con{ah, at}, bh,
                      Ords.lt_all_head(bh, ah, at,
                        Ol.U32.lt_of_cmp_gt(ah, bh,
                          E.Cmp.sym(GT{}, U32.cmp(ah, bh), ec)),
                        Ol.Ords.lt_all_of_asc(at, ah, aa))),
                    Ords.diff_go_contains(f, Con{ah, at}, bt,
                      O.Ords.head_cmp(Con{ah, at}, bt), x, {==}, aa,
                      E.Bool.and_r(Ol.Ords.above(bh, bt),
                        Ol.Ords.asc(bt), ab),
                      Ords.fuel_gt(at, bt, f, fu)))
                case EQ{}:
                  Ords.diff_eq_step(ah, bh, x, U32.is_eq(ah, x), at,
                    bt,
                    List.contains(~U32, ~U32.is_eq,
                      O.Ords.diff.go(f, at, bt,
                        O.Ords.head_cmp(at, bt)), x),
                    Ol.U32.eq_of_cmp_eq(ah, bh,
                      E.Cmp.sym(EQ{}, U32.cmp(ah, bh), ec)),
                    {==},
                    Ol.Ords.not_contains_of_lt_all(at, ah,
                      Ol.Ords.lt_all_of_asc(at, ah, aa)),
                    Ords.diff_go_contains(f, at, bt,
                      O.Ords.head_cmp(at, bt), x, {==},
                      E.Bool.and_r(Ol.Ords.above(ah, at),
                        Ol.Ords.asc(at), aa),
                      E.Bool.and_r(Ol.Ords.above(bh, bt),
                        Ol.Ords.asc(bt), ab),
                      Ords.fuel_eq(at, bt, f, fu)))

law Ords.diff_contains:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +x: U32
  for +aa: {Ol.Ords.asc(a) == True{} : Bool}
  for +ab: {Ol.Ords.asc(b) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, O.Ords.diff(a, b), x)
    == Bool.and(List.contains(~U32, ~U32.is_eq, a, x),
         Bool.not(List.contains(~U32, ~U32.is_eq, b, x))) : Bool}

def Ords.diff_contains(a, b, x, aa, ab):
  Ords.diff_go_contains(O.Ords.merge_fuel(a, b), a, b,
    O.Ords.head_cmp(a, b), x, {==}, aa, ab,
    It.Nat.upto_refl(O.Ords.merge_fuel(a, b)))
