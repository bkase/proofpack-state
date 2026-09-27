# proofs/childtest.bend -- which half an ordinal is in.
#
# A branch descends by comparing the ordinal, rebased into the node, against
# the half-width. The enumeration descends by testing the ordinal's high bits
# against each child's base. This file says the two agree: the ordinal below
# the half is the one the low child claims, the ordinal at or above it is the
# one the high child claims, and no ordinal is claimed by both.
#
# The arguments are all numeric, through the interval bridge. The bit test at
# a base is a pair of bounds; the comparison against the half is a bound on
# the low part; and the node's own test puts the ordinal's distance from the
# base where the two can be compared.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./split_add.bend as Sa
import ./interval.bend as It
import ./nodeenum.bend as Ne
import ./span.bend as Sn
import ./lastord.bend as Ld
import ./halves.bend as Hv
import ../core/count.bend as C
import ../core/word.bend as W

# ---------------------------------------------------------------------------
# Numbers.
# ---------------------------------------------------------------------------

law Nat.le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +ab: {C.Nat.upto(a, b) == True{} : Bool}
  for +bc: {C.Nat.upto(b, c) == True{} : Bool}
  {C.Nat.upto(a, c) == True{} : Bool}

def Nat.le_trans(a, b, c, ab, bc):
  match a:
    case 0n:
      {==}
    case 1n+p:
      match b:
        case 0n:
          E.Bool.noconf({C.Nat.upto(1n+p, c) == True{} : Bool}, ab)
        case 1n+q:
          match c:
            case 0n:
              E.Bool.noconf({C.Nat.upto(1n+p, 0n) == True{} : Bool}, bc)
            case 1n+r:
              Nat.le_trans(p, q, r, ab, bc)

law Nat.gt_up:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +le: {C.Nat.upto(a, b) == True{} : Bool}
  for +g: {C.Nat.gt(a, c) == True{} : Bool}
  {C.Nat.gt(b, c) == True{} : Bool}

def Nat.gt_up(a, b, c, le, g):
  match a:
    case 0n:
      E.Bool.noconf({C.Nat.gt(b, c) == True{} : Bool}, g)
    case 1n+p:
      match b:
        case 0n:
          E.Bool.noconf({C.Nat.gt(0n, c) == True{} : Bool}, le)
        case 1n+q:
          match c:
            case 0n:
              {==}
            case 1n+r:
              Nat.gt_up(p, q, r, le, g)

law Nat.le_add_right:
  for +a: Nat
  for +p: Nat
  {C.Nat.upto(a, Nat.add(a, p)) == True{} : Bool}

def Nat.le_add_right(a, p):
  %N.Nat.add_comm(p, a) : {C.Nat.upto(a, _) == True{} : Bool}
  It.Nat.le_add_left(a, p)

law Nat.pow2_split:
  for +k: Nat
  {Dc.Nat.pow2(1n+k) == Nat.add(Dc.Nat.pow2(k), Dc.Nat.pow2(k)) : Nat}

def Nat.pow2_split(k):
  E.Nat.sym(Nat.add(Dc.Nat.pow2(k), Dc.Nat.pow2(k)),
    Nat.double(Dc.Nat.pow2(k)), Ld.Nat.double_is_add(Dc.Nat.pow2(k)))

# A bound at the half widens to a bound at the whole.
law Nat.gt_wider:
  for +b: Nat
  for +k: Nat
  for +x: Nat
  for +g: {C.Nat.gt(Nat.add(b, Dc.Nat.pow2(k)), x) == True{} : Bool}
  {C.Nat.gt(Nat.add(b, Dc.Nat.pow2(1n+k)), x) == True{} : Bool}

law Nat.le_cast_assoc:
  for +b: Nat
  for +p: Nat
  {C.Nat.upto(Nat.add(b, p), Nat.add(b, Nat.add(p, p))) == True{}
    : Bool}

def Nat.le_cast_assoc(b, p):
  %N.Nat.add_assoc(b, p, p)
    : {C.Nat.upto(Nat.add(b, p), _) == True{} : Bool}
  Nat.le_add_right(Nat.add(b, p), p)

def Nat.gt_wider(b, k, x, g):
  %E.Nat.sym(Dc.Nat.pow2(1n+k),
    Nat.add(Dc.Nat.pow2(k), Dc.Nat.pow2(k)), Nat.pow2_split(k))
    : {C.Nat.gt(Nat.add(b, _), x) == True{} : Bool}
  Nat.gt_up(Nat.add(b, Dc.Nat.pow2(k)),
    Nat.add(b, Nat.add(Dc.Nat.pow2(k), Dc.Nat.pow2(k))), x,
    Nat.le_cast_assoc(b, Dc.Nat.pow2(k)), g)

# The upper half's bounds put the ordinal inside the whole node.
law Nat.upper_in_whole:
  for +b: Nat
  for +k: Nat
  for +x: Nat
  for +lo: {C.Nat.upto(Nat.add(b, Dc.Nat.pow2(k)), x) == True{} : Bool}
  for +hi: {C.Nat.gt(Nat.add(Nat.add(b, Dc.Nat.pow2(k)),
    Dc.Nat.pow2(k)), x) == True{} : Bool}
  {Bool.and(C.Nat.upto(b, x),
    C.Nat.gt(Nat.add(b, Dc.Nat.pow2(1n+k)), x)) == True{} : Bool}

law Nat.whole_bound:
  for +b: Nat
  for +k: Nat
  for +x: Nat
  for +hi: {C.Nat.gt(Nat.add(Nat.add(b, Dc.Nat.pow2(k)),
    Dc.Nat.pow2(k)), x) == True{} : Bool}
  {C.Nat.gt(Nat.add(b, Dc.Nat.pow2(1n+k)), x) == True{} : Bool}

def Nat.whole_bound(b, k, x, hi):
  %E.Nat.sym(Dc.Nat.pow2(1n+k),
    Nat.add(Dc.Nat.pow2(k), Dc.Nat.pow2(k)), Nat.pow2_split(k))
    : {C.Nat.gt(Nat.add(b, _), x) == True{} : Bool}
  %N.Nat.add_assoc(b, Dc.Nat.pow2(k), Dc.Nat.pow2(k))
    : {C.Nat.gt(_, x) == True{} : Bool}
  hi

def Nat.upper_in_whole(b, k, x, lo, hi):
  E.Bool.and_both(C.Nat.upto(b, x),
    C.Nat.gt(Nat.add(b, Dc.Nat.pow2(1n+k)), x),
    Nat.le_trans(b, Nat.add(b, Dc.Nat.pow2(k)), x,
      Nat.le_add_right(b, Dc.Nat.pow2(k)), lo),
    Nat.whole_bound(b, k, x, hi))

law Nat.gt_cancel_l:
  for +j: Nat
  for +b: Nat
  for +a: Nat
  for +ok: {C.Nat.gt(Nat.add(j, a), Nat.add(j, b)) == True{} : Bool}
  {C.Nat.gt(a, b) == True{} : Bool}

def Nat.gt_cancel_l(j, b, a, ok):
  match j:
    case 0n:
      ok
    case 1n+q:
      Nat.gt_cancel_l(q, b, a, ok)

law Nat.le_of_gt_false:
  for +a: Nat
  for +b: Nat
  for +f: {C.Nat.gt(a, b) == False{} : Bool}
  {C.Nat.upto(a, b) == True{} : Bool}

def Nat.le_of_gt_false(a, b, f):
  match a:
    case 0n:
      {==}
    case 1n+p:
      match b:
        case 0n:
          E.Bool.noconf.r({C.Nat.upto(1n+p, 0n) == True{} : Bool}, f)
        case 1n+q:
          Nat.le_of_gt_false(p, q, f)

# ---------------------------------------------------------------------------
# The low part of an ordinal, against the half.
# ---------------------------------------------------------------------------

law Test.low_below:
  for +x: U32
  for +k: Nat
  for +hz: {Dc.U32.hi_zero(U32.and(x, W.U32.mask(1n+k)), k)
    == True{} : Bool}
  {C.Nat.gt(Dc.Nat.pow2(k),
    U32.to_nat(U32.and(x, W.U32.mask(1n+k)))) == True{} : Bool}

def Test.low_below(x, k, hz):
  match x:
    case U32{xw}:
      Dc.Word.to_nat_bound(32n, k,
        Word.and(32n, xw, W.Word.low_mask(32n, 1n+k)), hz)

law Test.low_above:
  for +x: U32
  for +k: Nat
  for +g: Bool
  for +nz: {Dc.U32.hi_zero(U32.and(x, W.U32.mask(1n+k)), k)
    == False{} : Bool}
  for +eg: {g == C.Nat.gt(Dc.Nat.pow2(k),
    U32.to_nat(U32.and(x, W.U32.mask(1n+k)))) : Bool}
  {C.Nat.upto(Dc.Nat.pow2(k),
    U32.to_nat(U32.and(x, W.U32.mask(1n+k)))) == True{} : Bool}

def Test.low_fits(+x: U32, +k: Nat,
  +g: {C.Nat.gt(Dc.Nat.pow2(k),
    U32.to_nat(U32.and(x, W.U32.mask(1n+k)))) == True{} : Bool})
  -> {Dc.U32.hi_zero(U32.and(x, W.U32.mask(1n+k)), k)
    == True{} : Bool}:
  match x:
    case U32{xw}:
      Dc.Word.to_nat_fits(32n, k,
        Word.and(32n, xw, W.Word.low_mask(32n, 1n+k)), g)

def Test.low_above.absurd(+x: U32, +k: Nat,
  +nz: {Dc.U32.hi_zero(U32.and(x, W.U32.mask(1n+k)), k)
    == False{} : Bool},
  +eg: {True{} == C.Nat.gt(Dc.Nat.pow2(k),
    U32.to_nat(U32.and(x, W.U32.mask(1n+k)))) : Bool})
  -> {False{} == True{} : Bool}:
  %Test.low_fits(x, k, E.Bool.sym(True{}, C.Nat.gt(Dc.Nat.pow2(k),
    U32.to_nat(U32.and(x, W.U32.mask(1n+k)))), eg))
    : {False{} == _ : Bool}
  E.Bool.sym(Dc.U32.hi_zero(U32.and(x, W.U32.mask(1n+k)), k), False{},
    nz)

def Test.low_above(x, k, g, nz, eg):
  match g:
    case True{}:
      E.Bool.noconf({C.Nat.upto(Dc.Nat.pow2(k),
        U32.to_nat(U32.and(x, W.U32.mask(1n+k)))) == True{} : Bool},
        Test.low_above.absurd(x, k, nz, eg))
    case False{}:
      Nat.le_of_gt_false(Dc.Nat.pow2(k),
        U32.to_nat(U32.and(x, W.U32.mask(1n+k))),
        E.Bool.sym(False{}, C.Nat.gt(Dc.Nat.pow2(k),
          U32.to_nat(U32.and(x, W.U32.mask(1n+k)))), eg))

law Test.low_in_node:
  for +x: U32
  for +k: Nat
  {C.Nat.gt(Dc.Nat.pow2(1n+k),
    U32.to_nat(U32.and(x, W.U32.mask(1n+k)))) == True{} : Bool}

def Test.low_in_node(x, k):
  match x:
    case U32{xw}:
      Dc.Word.to_nat_bound(32n, 1n+k,
        Word.and(32n, xw, W.Word.low_mask(32n, 1n+k)),
        Sa.Word.hi_zero_low(32n, xw, 1n+k))

# ---------------------------------------------------------------------------
# An ordinal a child claims is one the node claims.
# ---------------------------------------------------------------------------

def Test.lz_k(+base: U32, +k: Nat,
  +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool})
  -> {Sa.U32.lo_zero(base, k) == True{} : Bool}:
  Hv.Word.lo_zero_down(32n, W.U32.word(base), k, lz)

def Test.whole_of_low(+base: U32, +k: Nat, +x: U32,
  +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool},
  +elo: {U32.is_eq(base, W.U32.diff(x, W.U32.mask(k)))
    == True{} : Bool})
  -> {U32.is_eq(base, W.U32.diff(x, W.U32.mask(1n+k)))
    == True{} : Bool}:
  It.Interval.match_of_bounds(base, x, 1n+k, lz,
    E.Bool.and_l(C.Nat.upto(U32.to_nat(base), U32.to_nat(x)),
      C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
        U32.to_nat(x)),
      It.Interval.bounds_of_match(base, x, k,
        Test.lz_k(base, k, lz), elo)),
    Nat.gt_wider(U32.to_nat(base), k, U32.to_nat(x),
      E.Bool.and_r(C.Nat.upto(U32.to_nat(base), U32.to_nat(x)),
        C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
          U32.to_nat(x)),
        It.Interval.bounds_of_match(base, x, k,
          Test.lz_k(base, k, lz), elo))))

def Test.half_nat(+base: U32, +k: Nat,
  +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool},
  +lt: {C.Nat.gt(32n, k) == True{} : Bool})
  -> {Nat.add(U32.to_nat((base + U32.shln(1, k) : U32)),
       Dc.Nat.pow2(k))
     == Nat.add(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
          Dc.Nat.pow2(k)) : Nat}:
  %E.Nat.sym(U32.to_nat((base + U32.shln(1, k) : U32)),
    Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
    Hv.U32.to_nat_half_base(base, k, lz, lt))
    : {Nat.add(_, Dc.Nat.pow2(k))
      == Nat.add(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
           Dc.Nat.pow2(k)) : Nat}
  {==}

def Test.whole_bounds(+base: U32, +k: Nat, +x: U32,
  +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool},
  +lt: {C.Nat.gt(32n, k) == True{} : Bool},
  +ehi: {U32.is_eq((base + U32.shln(1, k) : U32),
    W.U32.diff(x, W.U32.mask(k))) == True{} : Bool})
  -> {Bool.and(C.Nat.upto(U32.to_nat(base), U32.to_nat(x)),
       C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(1n+k)),
         U32.to_nat(x))) == True{} : Bool}:
  Nat.upper_in_whole(U32.to_nat(base), k, U32.to_nat(x),
    It.Nat.upto_cast(U32.to_nat((base + U32.shln(1, k) : U32)),
      Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), U32.to_nat(x),
      U32.to_nat(x), Hv.U32.to_nat_half_base(base, k, lz, lt), {==},
      E.Bool.and_l(
        C.Nat.upto(U32.to_nat((base + U32.shln(1, k) : U32)),
          U32.to_nat(x)),
        C.Nat.gt(Nat.add(U32.to_nat((base + U32.shln(1, k) : U32)),
          Dc.Nat.pow2(k)), U32.to_nat(x)),
        It.Interval.bounds_of_match((base + U32.shln(1, k) : U32), x, k,
          Hv.U32.lo_zero_half_base(base, k, lz), ehi))),
    It.Nat.gt_cast(
      Nat.add(U32.to_nat((base + U32.shln(1, k) : U32)),
        Dc.Nat.pow2(k)),
      Nat.add(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
        Dc.Nat.pow2(k)), U32.to_nat(x), U32.to_nat(x),
      Test.half_nat(base, k, lz, lt), {==},
      E.Bool.and_r(
        C.Nat.upto(U32.to_nat((base + U32.shln(1, k) : U32)),
          U32.to_nat(x)),
        C.Nat.gt(Nat.add(U32.to_nat((base + U32.shln(1, k) : U32)),
          Dc.Nat.pow2(k)), U32.to_nat(x)),
        It.Interval.bounds_of_match((base + U32.shln(1, k) : U32), x, k,
          Hv.U32.lo_zero_half_base(base, k, lz), ehi))))

def Test.whole_of_high(+base: U32, +k: Nat, +x: U32,
  +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool},
  +lt: {C.Nat.gt(32n, k) == True{} : Bool},
  +ehi: {U32.is_eq((base + U32.shln(1, k) : U32),
    W.U32.diff(x, W.U32.mask(k))) == True{} : Bool})
  -> {U32.is_eq(base, W.U32.diff(x, W.U32.mask(1n+k)))
    == True{} : Bool}:
  It.Interval.match_of_bounds(base, x, 1n+k, lz,
    E.Bool.and_l(C.Nat.upto(U32.to_nat(base), U32.to_nat(x)),
      C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(1n+k)),
        U32.to_nat(x)),
      Test.whole_bounds(base, k, x, lz, lt, ehi)),
    E.Bool.and_r(C.Nat.upto(U32.to_nat(base), U32.to_nat(x)),
      C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(1n+k)),
        U32.to_nat(x)),
      Test.whole_bounds(base, k, x, lz, lt, ehi)))

# ---------------------------------------------------------------------------
# And the other way: the node's claim, split by the half.
# ---------------------------------------------------------------------------

def Test.dist(+base: U32, +k: Nat, +x: U32,
  +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool},
  +e: {U32.is_eq(base, W.U32.diff(x, W.U32.mask(1n+k)))
    == True{} : Bool})
  -> {U32.to_nat(x)
    == Nat.add(U32.to_nat(U32.and(x, W.U32.mask(1n+k))),
         U32.to_nat(base)) : Nat}:
  It.Interval.to_nat_of_match(base, x, 1n+k, lz, e)

def Test.low_of_whole(+base: U32, +k: Nat, +x: U32,
  +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool},
  +hz: {Dc.U32.hi_zero(U32.and(x, W.U32.mask(1n+k)), k)
    == True{} : Bool},
  +e: {U32.is_eq(base, W.U32.diff(x, W.U32.mask(1n+k)))
    == True{} : Bool})
  -> {U32.is_eq(base, W.U32.diff(x, W.U32.mask(k)))
    == True{} : Bool}:
  It.Interval.match_of_bounds(base, x, k, Test.lz_k(base, k, lz),
    It.Nat.upto_cast(U32.to_nat(base), U32.to_nat(base),
      Nat.add(U32.to_nat(U32.and(x, W.U32.mask(1n+k))),
        U32.to_nat(base)), U32.to_nat(x), {==},
      E.Nat.sym(U32.to_nat(x),
        Nat.add(U32.to_nat(U32.and(x, W.U32.mask(1n+k))),
          U32.to_nat(base)), Test.dist(base, k, x, lz, e)),
      It.Nat.le_add_left(U32.to_nat(base),
        U32.to_nat(U32.and(x, W.U32.mask(1n+k))))),
    It.Nat.gt_cast(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
      Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
      Nat.add(U32.to_nat(U32.and(x, W.U32.mask(1n+k))),
        U32.to_nat(base)), U32.to_nat(x), {==},
      E.Nat.sym(U32.to_nat(x),
        Nat.add(U32.to_nat(U32.and(x, W.U32.mask(1n+k))),
          U32.to_nat(base)), Test.dist(base, k, x, lz, e)),
      It.Nat.gt_add_of_lt(U32.to_nat(base),
        U32.to_nat(U32.and(x, W.U32.mask(1n+k))), Dc.Nat.pow2(k),
        Test.low_below(x, k, hz))))

law Nat.split_add_pow2:
  for +b: Nat
  for +k: Nat
  {Nat.add(b, Dc.Nat.pow2(1n+k))
    == Nat.add(Nat.add(b, Dc.Nat.pow2(k)), Dc.Nat.pow2(k)) : Nat}

def Nat.split_add_pow2(b, k):
  %E.Nat.sym(Dc.Nat.pow2(1n+k),
    Nat.add(Dc.Nat.pow2(k), Dc.Nat.pow2(k)), Nat.pow2_split(k))
    : {Nat.add(b, _)
      == Nat.add(Nat.add(b, Dc.Nat.pow2(k)), Dc.Nat.pow2(k)) : Nat}
  E.Nat.sym(Nat.add(Nat.add(b, Dc.Nat.pow2(k)), Dc.Nat.pow2(k)),
    Nat.add(b, Nat.add(Dc.Nat.pow2(k), Dc.Nat.pow2(k))),
    N.Nat.add_assoc(b, Dc.Nat.pow2(k), Dc.Nat.pow2(k)))

def Test.dist_comm(+base: U32, +k: Nat, +x: U32,
  +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool},
  +e: {U32.is_eq(base, W.U32.diff(x, W.U32.mask(1n+k)))
    == True{} : Bool})
  -> {Nat.add(U32.to_nat(base),
       U32.to_nat(U32.and(x, W.U32.mask(1n+k)))) == U32.to_nat(x)
     : Nat}:
  %E.Nat.sym(U32.to_nat(x),
    Nat.add(U32.to_nat(U32.and(x, W.U32.mask(1n+k))),
      U32.to_nat(base)), Test.dist(base, k, x, lz, e))
    : {Nat.add(U32.to_nat(base),
        U32.to_nat(U32.and(x, W.U32.mask(1n+k)))) == _ : Nat}
  N.Nat.add_comm(U32.to_nat(base),
    U32.to_nat(U32.and(x, W.U32.mask(1n+k))))

def Test.half_nat_back(+base: U32, +k: Nat,
  +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool},
  +lt: {C.Nat.gt(32n, k) == True{} : Bool})
  -> {Nat.add(U32.to_nat(base), Dc.Nat.pow2(1n+k))
     == Nat.add(U32.to_nat((base + U32.shln(1, k) : U32)),
          Dc.Nat.pow2(k)) : Nat}:
  %E.Nat.sym(U32.to_nat((base + U32.shln(1, k) : U32)),
    Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
    Hv.U32.to_nat_half_base(base, k, lz, lt))
    : {Nat.add(U32.to_nat(base), Dc.Nat.pow2(1n+k))
      == Nat.add(_, Dc.Nat.pow2(k)) : Nat}
  Nat.split_add_pow2(U32.to_nat(base), k)

def Test.high_of_whole(+base: U32, +k: Nat, +x: U32,
  +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool},
  +lt: {C.Nat.gt(32n, k) == True{} : Bool},
  +nz: {Dc.U32.hi_zero(U32.and(x, W.U32.mask(1n+k)), k)
    == False{} : Bool},
  +e: {U32.is_eq(base, W.U32.diff(x, W.U32.mask(1n+k)))
    == True{} : Bool})
  -> {U32.is_eq((base + U32.shln(1, k) : U32),
    W.U32.diff(x, W.U32.mask(k))) == True{} : Bool}:
  It.Interval.match_of_bounds((base + U32.shln(1, k) : U32), x, k,
    Hv.U32.lo_zero_half_base(base, k, lz),
    It.Nat.upto_cast(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
      U32.to_nat((base + U32.shln(1, k) : U32)),
      Nat.add(U32.to_nat(base),
        U32.to_nat(U32.and(x, W.U32.mask(1n+k)))), U32.to_nat(x),
      E.Nat.sym(U32.to_nat((base + U32.shln(1, k) : U32)),
        Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
        Hv.U32.to_nat_half_base(base, k, lz, lt)),
      Test.dist_comm(base, k, x, lz, e),
      Ne.Nat.le_add_mono_l(U32.to_nat(base), Dc.Nat.pow2(k),
        U32.to_nat(U32.and(x, W.U32.mask(1n+k))),
        Test.low_above(x, k,
          C.Nat.gt(Dc.Nat.pow2(k),
            U32.to_nat(U32.and(x, W.U32.mask(1n+k)))), nz, {==}))),
    It.Nat.gt_cast(Nat.add(U32.to_nat(base), Dc.Nat.pow2(1n+k)),
      Nat.add(U32.to_nat((base + U32.shln(1, k) : U32)),
        Dc.Nat.pow2(k)),
      Nat.add(U32.to_nat(U32.and(x, W.U32.mask(1n+k))),
        U32.to_nat(base)), U32.to_nat(x),
      Test.half_nat_back(base, k, lz, lt),
      E.Nat.sym(U32.to_nat(x),
        Nat.add(U32.to_nat(U32.and(x, W.U32.mask(1n+k))),
          U32.to_nat(base)), Test.dist(base, k, x, lz, e)),
      It.Nat.gt_add_of_lt(U32.to_nat(base),
        U32.to_nat(U32.and(x, W.U32.mask(1n+k))), Dc.Nat.pow2(1n+k),
        Test.low_in_node(x, k))))

# ---------------------------------------------------------------------------
# No ordinal is claimed by both halves.
# ---------------------------------------------------------------------------

def Test.x_is_base_plus(+base: U32, +k: Nat, +x: U32,
  +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool},
  +e: {U32.is_eq(base, W.U32.diff(x, W.U32.mask(1n+k)))
    == True{} : Bool})
  -> {U32.to_nat(x)
     == Nat.add(U32.to_nat(base),
          U32.to_nat(U32.and(x, W.U32.mask(1n+k)))) : Nat}:
  E.Nat.sym(Nat.add(U32.to_nat(base),
    U32.to_nat(U32.and(x, W.U32.mask(1n+k)))), U32.to_nat(x),
    Test.dist_comm(base, k, x, lz, e))

def Test.low_absurd(+base: U32, +k: Nat, +x: U32,
  +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool},
  +nz: {Dc.U32.hi_zero(U32.and(x, W.U32.mask(1n+k)), k)
    == False{} : Bool},
  +elo: {U32.is_eq(base, W.U32.diff(x, W.U32.mask(k)))
    == True{} : Bool})
  -> {False{} == True{} : Bool}:
  Sn.Nat.upto_gt_absurd(Dc.Nat.pow2(k),
    U32.to_nat(U32.and(x, W.U32.mask(1n+k))),
    Test.low_above(x, k,
      C.Nat.gt(Dc.Nat.pow2(k),
        U32.to_nat(U32.and(x, W.U32.mask(1n+k)))), nz, {==}),
    Nat.gt_cancel_l(U32.to_nat(base),
      U32.to_nat(U32.and(x, W.U32.mask(1n+k))), Dc.Nat.pow2(k),
      It.Nat.gt_cast(
        Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
        Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), U32.to_nat(x),
        Nat.add(U32.to_nat(base),
          U32.to_nat(U32.and(x, W.U32.mask(1n+k)))), {==},
        Test.x_is_base_plus(base, k, x, lz,
          Test.whole_of_low(base, k, x, lz, elo)),
        E.Bool.and_r(C.Nat.upto(U32.to_nat(base), U32.to_nat(x)),
          C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
            U32.to_nat(x)),
          It.Interval.bounds_of_match(base, x, k,
            Test.lz_k(base, k, lz), elo)))))

def Test.high_absurd(+base: U32, +k: Nat, +x: U32,
  +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool},
  +lt: {C.Nat.gt(32n, k) == True{} : Bool},
  +hz: {Dc.U32.hi_zero(U32.and(x, W.U32.mask(1n+k)), k)
    == True{} : Bool},
  +ehi: {U32.is_eq((base + U32.shln(1, k) : U32),
    W.U32.diff(x, W.U32.mask(k))) == True{} : Bool})
  -> {False{} == True{} : Bool}:
  Sn.Nat.upto_gt_absurd(Dc.Nat.pow2(k),
    U32.to_nat(U32.and(x, W.U32.mask(1n+k))),
    Ne.Nat.le_cancel_l(U32.to_nat(base), Dc.Nat.pow2(k),
      U32.to_nat(U32.and(x, W.U32.mask(1n+k))),
      It.Nat.upto_cast(U32.to_nat((base + U32.shln(1, k) : U32)),
        Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), U32.to_nat(x),
        Nat.add(U32.to_nat(base),
          U32.to_nat(U32.and(x, W.U32.mask(1n+k)))),
        Hv.U32.to_nat_half_base(base, k, lz, lt),
        Test.x_is_base_plus(base, k, x, lz,
          Test.whole_of_high(base, k, x, lz, lt, ehi)),
        E.Bool.and_l(
          C.Nat.upto(U32.to_nat((base + U32.shln(1, k) : U32)),
            U32.to_nat(x)),
          C.Nat.gt(Nat.add(U32.to_nat((base + U32.shln(1, k) : U32)),
            Dc.Nat.pow2(k)), U32.to_nat(x)),
          It.Interval.bounds_of_match((base + U32.shln(1, k) : U32), x,
            k, Hv.U32.lo_zero_half_base(base, k, lz), ehi)))),
    Test.low_below(x, k, hz))

# ---------------------------------------------------------------------------
# The four statements the enumeration uses.
# ---------------------------------------------------------------------------

def Test.whole_from_low(+base: U32, +k: Nat, +x: U32,
  +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool},
  +ee: {False{} == U32.is_eq(base, W.U32.diff(x, W.U32.mask(1n+k)))
    : Bool},
  +ef: {True{} == U32.is_eq(base, W.U32.diff(x, W.U32.mask(k)))
    : Bool})
  -> {False{} == True{} : Bool}:
  %Test.whole_of_low(base, k, x, lz,
    E.Bool.sym(True{}, U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
      ef))
    : {False{} == _ : Bool}
  ee

def Test.whole_from_high(+base: U32, +k: Nat, +x: U32,
  +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool},
  +lt: {C.Nat.gt(32n, k) == True{} : Bool},
  +ee: {False{} == U32.is_eq(base, W.U32.diff(x, W.U32.mask(1n+k)))
    : Bool},
  +ef: {True{} == U32.is_eq((base + U32.shln(1, k) : U32),
    W.U32.diff(x, W.U32.mask(k))) : Bool})
  -> {False{} == True{} : Bool}:
  %Test.whole_of_high(base, k, x, lz, lt,
    E.Bool.sym(True{}, U32.is_eq((base + U32.shln(1, k) : U32),
      W.U32.diff(x, W.U32.mask(k))), ef))
    : {False{} == _ : Bool}
  ee

law Test.low_matches:
  for +base: U32
  for +k: Nat
  for +x: U32
  for +e: Bool
  for +f: Bool
  for +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool}
  for +hz: {Dc.U32.hi_zero(U32.and(x, W.U32.mask(1n+k)), k)
    == True{} : Bool}
  for +ee: {e == U32.is_eq(base, W.U32.diff(x, W.U32.mask(1n+k)))
    : Bool}
  for +ef: {f == U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))) : Bool}
  {U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))) == e : Bool}

def Test.low_matches(base, k, x, e, f, lz, hz, ee, ef):
  match e:
    case True{}:
      Test.low_of_whole(base, k, x, lz, hz,
        E.Bool.sym(True{},
          U32.is_eq(base, W.U32.diff(x, W.U32.mask(1n+k))), ee))
    case False{}:
      match f:
        case True{}:
          E.Bool.noconf({U32.is_eq(base,
            W.U32.diff(x, W.U32.mask(k))) == False{} : Bool},
            Test.whole_from_low(base, k, x, lz, ee, ef))
        case False{}:
          E.Bool.sym(False{},
            U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))), ef)

law Test.low_misses:
  for +base: U32
  for +k: Nat
  for +x: U32
  for +f: Bool
  for +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool}
  for +nz: {Dc.U32.hi_zero(U32.and(x, W.U32.mask(1n+k)), k)
    == False{} : Bool}
  for +ef: {f == U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))) : Bool}
  {U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))) == False{} : Bool}

def Test.low_misses(base, k, x, f, lz, nz, ef):
  match f:
    case True{}:
      E.Bool.noconf({U32.is_eq(base, W.U32.diff(x, W.U32.mask(k)))
        == False{} : Bool},
        Test.low_absurd(base, k, x, lz, nz,
          E.Bool.sym(True{},
            U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))), ef)))
    case False{}:
      E.Bool.sym(False{},
        U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))), ef)

law Test.high_matches:
  for +base: U32
  for +k: Nat
  for +x: U32
  for +e: Bool
  for +f: Bool
  for +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, k) == True{} : Bool}
  for +nz: {Dc.U32.hi_zero(U32.and(x, W.U32.mask(1n+k)), k)
    == False{} : Bool}
  for +ee: {e == U32.is_eq(base, W.U32.diff(x, W.U32.mask(1n+k)))
    : Bool}
  for +ef: {f == U32.is_eq((base + U32.shln(1, k) : U32),
    W.U32.diff(x, W.U32.mask(k))) : Bool}
  {U32.is_eq((base + U32.shln(1, k) : U32),
    W.U32.diff(x, W.U32.mask(k))) == e : Bool}

def Test.high_matches(base, k, x, e, f, lz, lt, nz, ee, ef):
  match e:
    case True{}:
      Test.high_of_whole(base, k, x, lz, lt, nz,
        E.Bool.sym(True{},
          U32.is_eq(base, W.U32.diff(x, W.U32.mask(1n+k))), ee))
    case False{}:
      match f:
        case True{}:
          E.Bool.noconf({U32.is_eq((base + U32.shln(1, k) : U32),
            W.U32.diff(x, W.U32.mask(k))) == False{} : Bool},
            Test.whole_from_high(base, k, x, lz, lt, ee, ef))
        case False{}:
          E.Bool.sym(False{},
            U32.is_eq((base + U32.shln(1, k) : U32),
              W.U32.diff(x, W.U32.mask(k))), ef)

law Test.high_misses:
  for +base: U32
  for +k: Nat
  for +x: U32
  for +f: Bool
  for +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, k) == True{} : Bool}
  for +hz: {Dc.U32.hi_zero(U32.and(x, W.U32.mask(1n+k)), k)
    == True{} : Bool}
  for +ef: {f == U32.is_eq((base + U32.shln(1, k) : U32),
    W.U32.diff(x, W.U32.mask(k))) : Bool}
  {U32.is_eq((base + U32.shln(1, k) : U32),
    W.U32.diff(x, W.U32.mask(k))) == False{} : Bool}

def Test.high_misses(base, k, x, f, lz, lt, hz, ef):
  match f:
    case True{}:
      E.Bool.noconf({U32.is_eq((base + U32.shln(1, k) : U32),
        W.U32.diff(x, W.U32.mask(k))) == False{} : Bool},
        Test.high_absurd(base, k, x, lz, lt, hz,
          E.Bool.sym(True{},
            U32.is_eq((base + U32.shln(1, k) : U32),
              W.U32.diff(x, W.U32.mask(k))), ef)))
    case False{}:
      E.Bool.sym(False{},
        U32.is_eq((base + U32.shln(1, k) : U32),
          W.U32.diff(x, W.U32.mask(k))), ef)
