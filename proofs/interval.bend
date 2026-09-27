# proofs/interval.bend -- "in this subtree" as a bit test and as a bound.
#
# A node of the set tree covers an interval: the ordinals whose high bits are
# the node's base. The enumeration asks that as a bit test -- clear the low
# bits and compare -- and the count-down a full node enumerates with answers
# in numbers. This file is the bridge between the two readings, in both
# directions.
#
# The easy direction is arithmetic on the split that proofs/split_add.bend
# established: if the high part matches, the ordinal is the base plus
# something below 2^k. The other direction needs uniqueness -- two bases
# whose low k bits are zero and which bracket the same ordinal are the same
# base -- and that is where the division identity comes in: such a base is
# 2^k times its own shift, so the question becomes one about the shifts.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./inject.bend as Ij
import ./split.bend as Sp
import ./descend.bend as Dc
import ./split_add.bend as Sa
import ../core/count.bend as C
import ../core/word.bend as W

# ---------------------------------------------------------------------------
# Small order facts about doubling k times.
# ---------------------------------------------------------------------------

law Nat.le_add_left:
  for +a: Nat
  for +b: Nat
  {C.Nat.upto(a, Nat.add(b, a)) == True{} : Bool}

law Nat.upto_refl:
  for +a: Nat
  {C.Nat.upto(a, a) == True{} : Bool}

def Nat.upto_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.upto_refl(p)

law Nat.le_up:
  for +a: Nat
  for +b: Nat
  for +ok: {C.Nat.upto(a, b) == True{} : Bool}
  {C.Nat.upto(a, 1n+b) == True{} : Bool}

def Nat.le_up(a, b, ok):
  match a:
    case 0n:
      {==}
    case 1n+p:
      match b:
        case 0n:
          E.Bool.noconf({C.Nat.upto(p, 0n) == True{} : Bool}, ok)
        case 1n+q:
          Nat.le_up(p, q, ok)

def Nat.le_add_left(a, b):
  match b:
    case 0n:
      Nat.upto_refl(a)
    case 1n+q:
      Nat.le_up(a, Nat.add(q, a), Nat.le_add_left(a, q))

law Nat.gt_add_of_lt:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +ok: {C.Nat.gt(c, b) == True{} : Bool}
  {C.Nat.gt(Nat.add(a, c), Nat.add(b, a)) == True{} : Bool}

law Nat.gt_add_mono:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +ok: {C.Nat.gt(c, b) == True{} : Bool}
  {C.Nat.gt(Nat.add(a, c), Nat.add(a, b)) == True{} : Bool}

def Nat.gt_add_mono(a, b, c, ok):
  match a:
    case 0n:
      ok
    case 1n+p:
      Nat.gt_add_mono(p, b, c, ok)

# ---------------------------------------------------------------------------
# The easy direction.
# ---------------------------------------------------------------------------

def Nat.gt_add_of_lt(a, b, c, ok):
  %E.Nat.sym(Nat.add(b, a), Nat.add(a, b), N.Nat.add_comm(b, a))
    : {C.Nat.gt(Nat.add(a, c), _) == True{} : Bool}
  Nat.gt_add_mono(a, b, c, ok)

law Interval.bounds_of_match:
  for +base: U32
  for +x: U32
  for +k: Nat
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  for +m: {U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))) == True{} : Bool}
  {Bool.and(C.Nat.upto(U32.to_nat(base), U32.to_nat(x)),
    C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), U32.to_nat(x)))
    == True{} : Bool}

law Interval.low_bound:
  for +x: U32
  for +k: Nat
  {C.Nat.gt(Dc.Nat.pow2(k), U32.to_nat(U32.and(x, W.U32.mask(k))))
    == True{} : Bool}

def Interval.low_bound(x, k):
  match x:
    case U32{xw}:
      Dc.Word.to_nat_bound(32n, k,
        Word.and(32n, xw, W.Word.low_mask(32n, k)),
        Sa.Word.hi_zero_low(32n, xw, k))

law Interval.bounds_split:
  for +b: Nat
  for +l: Nat
  for +p: Nat
  for +ok: {C.Nat.gt(p, l) == True{} : Bool}
  {Bool.and(C.Nat.upto(b, Nat.add(l, b)),
    C.Nat.gt(Nat.add(b, p), Nat.add(l, b))) == True{} : Bool}

def Interval.bounds_split(b, l, p, ok):
  %E.Bool.sym(C.Nat.upto(b, Nat.add(l, b)), True{},
    Nat.le_add_left(b, l))
    : {Bool.and(_, C.Nat.gt(Nat.add(b, p), Nat.add(l, b)))
      == True{} : Bool}
  Nat.gt_add_of_lt(b, l, p, ok)

# The ordinal is its low part above the base.
law Interval.to_nat_of_match:
  for +base: U32
  for +x: U32
  for +k: Nat
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  for +m: {U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))) == True{} : Bool}
  {U32.to_nat(x)
    == Nat.add(U32.to_nat(U32.and(x, W.U32.mask(k))), U32.to_nat(base))
    : Nat}

def Interval.to_nat_of_match(base, x, k, lb, m):
  %E.U32.sym(base, W.U32.diff(x, W.U32.mask(k)),
    E.U32.eq_reflect(base, W.U32.diff(x, W.U32.mask(k)), m))
    : {U32.to_nat(x)
      == Nat.add(U32.to_nat(U32.and(x, W.U32.mask(k))), U32.to_nat(_))
      : Nat}
  %Sa.U32.or_split(x, k)
    : {U32.to_nat(_)
      == Nat.add(U32.to_nat(U32.and(x, W.U32.mask(k))),
           U32.to_nat(W.U32.diff(x, W.U32.mask(k)))) : Nat}
  Sa.U32.to_nat_or(U32.and(x, W.U32.mask(k)),
    W.U32.diff(x, W.U32.mask(k)), k, Sa.U32.hi_zero_low(x, k),
    Sa.U32.lo_zero_high(x, k))

def Interval.bounds_of_match(base, x, k, lb, m):
  %E.Nat.sym(U32.to_nat(x),
    Nat.add(U32.to_nat(U32.and(x, W.U32.mask(k))), U32.to_nat(base)),
    Interval.to_nat_of_match(base, x, k, lb, m))
    : {Bool.and(C.Nat.upto(U32.to_nat(base), _),
        C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), _))
      == True{} : Bool}
  Interval.bounds_split(U32.to_nat(base),
    U32.to_nat(U32.and(x, W.U32.mask(k))), Dc.Nat.pow2(k),
    Interval.low_bound(x, k))

# ---------------------------------------------------------------------------
# The other direction: two bases that bracket the same ordinal are the same
# base. This is where the division identity earns its keep -- a base whose
# low `k` bits are zero is `2^k` times its own shift, so the question becomes
# one about the shifts, and those are ordinary numbers.
# ---------------------------------------------------------------------------

law Nat.dbl_succ:
  for +k: Nat
  for +a: Nat
  {Sp.Nat.dbl(k, 1n+a) == Nat.add(Dc.Nat.pow2(k), Sp.Nat.dbl(k, a))
    : Nat}

def Nat.dbl_succ(k, a):
  match k:
    case 0n:
      {==}
    case 1n+j:
      %E.Nat.sym(Sp.Nat.dbl(j, 1n+a),
        Nat.add(Dc.Nat.pow2(j), Sp.Nat.dbl(j, a)), Nat.dbl_succ(j, a))
        : {Nat.double(_)
          == Nat.add(Nat.double(Dc.Nat.pow2(j)),
               Nat.double(Sp.Nat.dbl(j, a))) : Nat}
      E.Nat.sym(Nat.add(Nat.double(Dc.Nat.pow2(j)),
        Nat.double(Sp.Nat.dbl(j, a))),
        Nat.double(Nat.add(Dc.Nat.pow2(j), Sp.Nat.dbl(j, a))),
        Sa.Nat.double_add(Dc.Nat.pow2(j), Sp.Nat.dbl(j, a)))

law Nat.gt_double_down:
  for +b: Nat
  for +a: Nat
  for +ok: {C.Nat.gt(Nat.double(b), Nat.double(a)) == True{} : Bool}
  {C.Nat.gt(b, a) == True{} : Bool}

def Nat.gt_double_down(b, a, ok):
  match b:
    case 0n:
      ok
    case 1n+q:
      match a:
        case 0n:
          {==}
        case 1n+p:
          Nat.gt_double_down(q, p, ok)

law Nat.gt_dbl_down:
  for +k: Nat
  for +a: Nat
  for +b: Nat
  for +ok: {C.Nat.gt(Sp.Nat.dbl(k, b), Sp.Nat.dbl(k, a)) == True{} : Bool}
  {C.Nat.gt(b, a) == True{} : Bool}

def Nat.gt_dbl_down(k, a, b, ok):
  match k:
    case 0n:
      ok
    case 1n+j:
      Nat.gt_dbl_down(j, a, b,
        Nat.gt_double_down(Sp.Nat.dbl(j, b), Sp.Nat.dbl(j, a), ok))

law Nat.le_of_gt_succ2:
  for +b: Nat
  for +m: Nat
  for +g: {C.Nat.gt(1n+b, m) == True{} : Bool}
  {C.Nat.upto(m, b) == True{} : Bool}

def Nat.le_of_gt_succ2(b, m, g):
  match b:
    case 0n:
      match m:
        case 0n:
          {==}
        case 1n+p:
          g
    case 1n+q:
      match m:
        case 0n:
          {==}
        case 1n+p:
          Nat.le_of_gt_succ2(q, p, g)

law Nat.le_antisym:
  for +a: Nat
  for +b: Nat
  for +ab: {C.Nat.upto(a, b) == True{} : Bool}
  for +ba: {C.Nat.upto(b, a) == True{} : Bool}
  {a == b : Nat}

def Nat.le_antisym(a, b, ab, ba):
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          E.Bool.noconf({0n == 1n+q : Nat}, ba)
    case 1n+p:
      match b:
        case 0n:
          E.Bool.noconf({1n+p == 0n : Nat}, ab)
        case 1n+q:
          %E.Nat.sym(p, q, Nat.le_antisym(p, q, ab, ba)) : {1n+_ == 1n+q : Nat}
          {==}

law Nat.gt_of_le:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +bc: {C.Nat.upto(b, c) == True{} : Bool}
  for +ac: {C.Nat.gt(a, c) == True{} : Bool}
  {C.Nat.gt(a, b) == True{} : Bool}

def Nat.gt_of_le(a, b, c, bc, ac):
  match a:
    case 0n:
      ac
    case 1n+p:
      match b:
        case 0n:
          {==}
        case 1n+q:
          match c:
            case 0n:
              E.Bool.noconf({C.Nat.gt(p, q) == True{} : Bool}, bc)
            case 1n+r:
              Nat.gt_of_le(p, q, r, bc, ac)

# A base whose low `k` bits are zero contributes nothing below the split.
law Word.lo_zero_and_zero:
  for +n: Nat
  for +w: Word(n)
  for +k: Nat
  for +lz: {Sa.Word.lo_zero(n, w, k) == True{} : Bool}
  {Word.to_nat(n, Word.and(n, w, W.Word.low_mask(n, k))) == 0n : Nat}

def Word.lo_zero_and_zero(n, w, k, lz):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case False{}:
              match k:
                case 0n:
                  Sp.Word.and_low_mask_zero(1n+p, WCon{False{}, t})
                case 1n+j:
                  %E.Nat.sym(Word.to_nat(p, Word.and(p, t,
                      W.Word.low_mask(p, j))), 0n,
                    Word.lo_zero_and_zero(p, t, j, lz))
                    : {Nat.double(_) == 0n : Nat}
                  {==}
            case True{}:
              match k:
                case 0n:
                  Sp.Word.and_low_mask_zero(1n+p, WCon{True{}, t})
                case 1n+j:
                  E.Bool.noconf({1n+Nat.double(Word.to_nat(p,
                    Word.and(p, t, W.Word.low_mask(p, j)))) == 0n : Nat}, lz)

# So it is exactly `2^k` times its own shift.
law U32.to_nat_of_lo_zero:
  for +b: U32
  for +k: Nat
  for +lz: {Sa.U32.lo_zero(b, k) == True{} : Bool}
  {U32.to_nat(b) == Sp.Nat.dbl(k, U32.to_nat(U32.shrn(b, k))) : Nat}

def U32.to_nat_of_lo_zero(b, k, lz):
  match b:
    case U32{bw}:
      %E.U32.sym(U32.shrn(U32{bw}, k), U32{Sp.Word.shrn(32n, bw, k)},
        Sp.U32.shrn_word(U32{bw}, k))
        : {Word.to_nat(32n, bw)
          == Sp.Nat.dbl(k, U32.to_nat(_)) : Nat}
      %E.Nat.sym(Word.to_nat(32n, bw),
        Nat.add(Sp.Nat.dbl(k, Word.to_nat(32n, Sp.Word.shrn(32n, bw, k))),
          Word.to_nat(32n, Word.and(32n, bw, W.Word.low_mask(32n, k)))),
        Sp.Word.to_nat_split(32n, bw, k))
        : {_ == Sp.Nat.dbl(k,
            Word.to_nat(32n, Sp.Word.shrn(32n, bw, k))) : Nat}
      %E.Nat.sym(Word.to_nat(32n,
          Word.and(32n, bw, W.Word.low_mask(32n, k))), 0n,
        Word.lo_zero_and_zero(32n, bw, k, lz))
        : {Nat.add(Sp.Nat.dbl(k,
            Word.to_nat(32n, Sp.Word.shrn(32n, bw, k))), _)
          == Sp.Nat.dbl(k,
            Word.to_nat(32n, Sp.Word.shrn(32n, bw, k))) : Nat}
      N.Nat.add_zero(Sp.Nat.dbl(k,
        Word.to_nat(32n, Sp.Word.shrn(32n, bw, k))))

# Two numbers that the same value brackets, at the same scale, are equal.
law Nat.gt_succ_dbl:
  for +k: Nat
  for +h: Nat
  for +z: Nat
  for +ok: {C.Nat.gt(Nat.add(Sp.Nat.dbl(k, h), Dc.Nat.pow2(k)), z)
    == True{} : Bool}
  {C.Nat.gt(Sp.Nat.dbl(k, 1n+h), z) == True{} : Bool}

def Nat.gt_succ_dbl(k, h, z, ok):
  %E.Nat.sym(Sp.Nat.dbl(k, 1n+h),
    Nat.add(Dc.Nat.pow2(k), Sp.Nat.dbl(k, h)), Nat.dbl_succ(k, h))
    : {C.Nat.gt(_, z) == True{} : Bool}
  %N.Nat.add_comm(Sp.Nat.dbl(k, h), Dc.Nat.pow2(k))
    : {C.Nat.gt(_, z) == True{} : Bool}
  ok

law Nat.dbl_bracket:
  for +k: Nat
  for +b: Nat
  for +h: Nat
  for +l: Nat
  for +bl: {C.Nat.gt(Dc.Nat.pow2(k), l) == True{} : Bool}
  for +lo: {C.Nat.upto(Sp.Nat.dbl(k, b), Nat.add(l, Sp.Nat.dbl(k, h)))
    == True{} : Bool}
  for +hi: {C.Nat.gt(Nat.add(Sp.Nat.dbl(k, b), Dc.Nat.pow2(k)),
    Nat.add(l, Sp.Nat.dbl(k, h))) == True{} : Bool}
  {b == h : Nat}

def Nat.dbl_bracket(k, b, h, l, bl, lo, hi):
  Nat.le_antisym(b, h,
    Nat.le_of_gt_succ2(h, b,
      Nat.gt_dbl_down(k, b, 1n+h,
        Nat.gt_succ_dbl(k, h, Sp.Nat.dbl(k, b),
          Nat.gt_of_le(Nat.add(Sp.Nat.dbl(k, h), Dc.Nat.pow2(k)),
            Sp.Nat.dbl(k, b), Nat.add(l, Sp.Nat.dbl(k, h)), lo,
            Nat.gt_add_of_lt(Sp.Nat.dbl(k, h), l, Dc.Nat.pow2(k), bl))))),
    Nat.le_of_gt_succ2(b, h,
      Nat.gt_dbl_down(k, h, 1n+b,
        Nat.gt_succ_dbl(k, b, Sp.Nat.dbl(k, h),
          Nat.gt_of_le(Nat.add(Sp.Nat.dbl(k, b), Dc.Nat.pow2(k)),
            Sp.Nat.dbl(k, h), Nat.add(l, Sp.Nat.dbl(k, h)),
            Nat.le_add_left(Sp.Nat.dbl(k, h), l), hi)))))

# Moving a comparison along two equations.
law Nat.upto_cast:
  for +a: Nat
  for +a2: Nat
  for +c: Nat
  for +c2: Nat
  for +ea: {a == a2 : Nat}
  for +ec: {c == c2 : Nat}
  for +ok: {C.Nat.upto(a, c) == True{} : Bool}
  {C.Nat.upto(a2, c2) == True{} : Bool}

def Nat.upto_cast(a, a2, c, c2, ea, ec, ok):
  %ea : {C.Nat.upto(_, c2) == True{} : Bool}
  %ec : {C.Nat.upto(a, _) == True{} : Bool}
  ok

law Nat.gt_cast:
  for +a: Nat
  for +a2: Nat
  for +c: Nat
  for +c2: Nat
  for +ea: {a == a2 : Nat}
  for +ec: {c == c2 : Nat}
  for +ok: {C.Nat.gt(a, c) == True{} : Bool}
  {C.Nat.gt(a2, c2) == True{} : Bool}

def Nat.gt_cast(a, a2, c, c2, ea, ec, ok):
  %ea : {C.Nat.gt(_, c2) == True{} : Bool}
  %ec : {C.Nat.gt(a, _) == True{} : Bool}
  ok

# The ordinal is its low part above its high part, with no hypothesis.
law Interval.to_nat_parts:
  for +x: U32
  for +k: Nat
  {U32.to_nat(x)
    == Nat.add(U32.to_nat(U32.and(x, W.U32.mask(k))),
         U32.to_nat(W.U32.diff(x, W.U32.mask(k)))) : Nat}

def Interval.to_nat_parts(x, k):
  %Sa.U32.or_split(x, k)
    : {U32.to_nat(_)
      == Nat.add(U32.to_nat(U32.and(x, W.U32.mask(k))),
           U32.to_nat(W.U32.diff(x, W.U32.mask(k)))) : Nat}
  Sa.U32.to_nat_or(U32.and(x, W.U32.mask(k)),
    W.U32.diff(x, W.U32.mask(k)), k, Sa.U32.hi_zero_low(x, k),
    Sa.U32.lo_zero_high(x, k))

# The ordinal reads as the high part plus something below 2^k.
law Interval.to_nat_shifted:
  for +x: U32
  for +k: Nat
  {U32.to_nat(x)
    == Nat.add(U32.to_nat(U32.and(x, W.U32.mask(k))),
         Sp.Nat.dbl(k,
           U32.to_nat(U32.shrn(W.U32.diff(x, W.U32.mask(k)), k))))
    : Nat}

def Interval.to_nat_shifted(x, k):
  %U32.to_nat_of_lo_zero(W.U32.diff(x, W.U32.mask(k)), k,
    Sa.U32.lo_zero_high(x, k))
    : {U32.to_nat(x)
      == Nat.add(U32.to_nat(U32.and(x, W.U32.mask(k))), _) : Nat}
  Interval.to_nat_parts(x, k)

# The hard direction: the bounds force the bit test.
law Interval.match_of_bounds:
  for +base: U32
  for +x: U32
  for +k: Nat
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  for +lo: {C.Nat.upto(U32.to_nat(base), U32.to_nat(x)) == True{} : Bool}
  for +hi: {C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
    U32.to_nat(x)) == True{} : Bool}
  {U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))) == True{} : Bool}

def Interval.base_add_cast(+base: U32, +k: Nat,
  lb: {Sa.U32.lo_zero(base, k) == True{} : Bool})
  -> {Nat.add(U32.to_nat(base), Dc.Nat.pow2(k))
    == Nat.add(Sp.Nat.dbl(k, U32.to_nat(U32.shrn(base, k))),
         Dc.Nat.pow2(k)) : Nat}:
  %E.Nat.sym(U32.to_nat(base),
    Sp.Nat.dbl(k, U32.to_nat(U32.shrn(base, k))),
    U32.to_nat_of_lo_zero(base, k, lb))
    : {Nat.add(_, Dc.Nat.pow2(k))
      == Nat.add(Sp.Nat.dbl(k, U32.to_nat(U32.shrn(base, k))),
           Dc.Nat.pow2(k)) : Nat}
  {==}

def Interval.to_nat_eq(+base: U32, +x: U32, +k: Nat,
  +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool},
  lo: {C.Nat.upto(U32.to_nat(base), U32.to_nat(x)) == True{} : Bool},
  hi: {C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
    U32.to_nat(x)) == True{} : Bool})
  -> {U32.to_nat(base) == U32.to_nat(W.U32.diff(x, W.U32.mask(k))) : Nat}:
  %E.Nat.sym(U32.to_nat(base),
    Sp.Nat.dbl(k, U32.to_nat(U32.shrn(base, k))),
    U32.to_nat_of_lo_zero(base, k, lb))
    : {_ == U32.to_nat(W.U32.diff(x, W.U32.mask(k))) : Nat}
  %E.Nat.sym(U32.to_nat(W.U32.diff(x, W.U32.mask(k))),
    Sp.Nat.dbl(k, U32.to_nat(U32.shrn(W.U32.diff(x, W.U32.mask(k)), k))),
    U32.to_nat_of_lo_zero(W.U32.diff(x, W.U32.mask(k)), k,
      Sa.U32.lo_zero_high(x, k)))
    : {Sp.Nat.dbl(k, U32.to_nat(U32.shrn(base, k))) == _ : Nat}
  %E.Nat.sym(U32.to_nat(U32.shrn(W.U32.diff(x, W.U32.mask(k)), k)),
    U32.to_nat(U32.shrn(base, k)),
    E.Nat.sym(U32.to_nat(U32.shrn(base, k)),
      U32.to_nat(U32.shrn(W.U32.diff(x, W.U32.mask(k)), k)),
      Nat.dbl_bracket(k, U32.to_nat(U32.shrn(base, k)),
        U32.to_nat(U32.shrn(W.U32.diff(x, W.U32.mask(k)), k)),
        U32.to_nat(U32.and(x, W.U32.mask(k))),
        Interval.low_bound(x, k),
        Nat.upto_cast(U32.to_nat(base),
          Sp.Nat.dbl(k, U32.to_nat(U32.shrn(base, k))),
          U32.to_nat(x),
          Nat.add(U32.to_nat(U32.and(x, W.U32.mask(k))),
            Sp.Nat.dbl(k,
              U32.to_nat(U32.shrn(W.U32.diff(x, W.U32.mask(k)), k)))),
          U32.to_nat_of_lo_zero(base, k, lb),
          Interval.to_nat_shifted(x, k), lo),
        Nat.gt_cast(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
          Nat.add(Sp.Nat.dbl(k, U32.to_nat(U32.shrn(base, k))),
            Dc.Nat.pow2(k)),
          U32.to_nat(x),
          Nat.add(U32.to_nat(U32.and(x, W.U32.mask(k))),
            Sp.Nat.dbl(k,
              U32.to_nat(U32.shrn(W.U32.diff(x, W.U32.mask(k)), k)))),
          Interval.base_add_cast(base, k, lb),
          Interval.to_nat_shifted(x, k), hi))))
    : {Sp.Nat.dbl(k, U32.to_nat(U32.shrn(base, k)))
      == Sp.Nat.dbl(k, _) : Nat}
  {==}

def Interval.match_of_bounds(base, x, k, lb, lo, hi):
  %Ij.U32.to_nat_inj(base, W.U32.diff(x, W.U32.mask(k)),
    Interval.to_nat_eq(base, x, k, lb, lo, hi))
    : {U32.is_eq(base, _) == True{} : Bool}
  E.U32.is_eq_refl(base)
