# proofs/nodeenum.bend -- a full node enumerates exactly its interval.
#
# `PSet.members` gives a full node away by counting: it emits `2^k` ordinals
# counting down from the last one in the node's interval. This file says that
# what comes out is exactly the interval -- every ordinal whose high bits are
# the node's base, and nothing else -- by putting two bridges end to end.
#
# proofs/span.bend relates the count-down to a pair of numeric bounds, in both
# directions. proofs/interval.bend relates those bounds to the bit test that
# `PSet.mem` uses to descend, also in both directions. The work here is the
# arithmetic in between: the count-down starts at `base + 2^k - 1`, so the
# bounds it produces are off by the one that the last ordinal is short of the
# next node's base.
#
# The node's width is given as `2^k` and the count-down's start as a number,
# rather than as the `base + h + h - 1` the walk computes. Relating those to
# the depth is the caller's business: this law is about one node.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./split_add.bend as Sa
import ./decr.bend as De
import ./span.bend as Sn
import ./interval.bend as It
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# Numbers: moving a window by one.
# ---------------------------------------------------------------------------

law Nat.gt_succ_of_le:
  for +a: Nat
  for +c: Nat
  for +ok: {C.Nat.upto(a, c) == True{} : Bool}
  {C.Nat.gt(1n+c, a) == True{} : Bool}

def Nat.gt_succ_of_le(a, c, ok):
  match a:
    case 0n:
      {==}
    case 1n+p:
      match c:
        case 0n:
          E.Bool.noconf({C.Nat.gt(1n, 1n+p) == True{} : Bool}, ok)
        case 1n+q:
          Nat.gt_succ_of_le(p, q, ok)

law Nat.le_add_mono_l:
  for +j: Nat
  for +b: Nat
  for +a: Nat
  for +ok: {C.Nat.upto(b, a) == True{} : Bool}
  {C.Nat.upto(Nat.add(j, b), Nat.add(j, a)) == True{} : Bool}

def Nat.le_add_mono_l(j, b, a, ok):
  match j:
    case 0n:
      ok
    case 1n+q:
      Nat.le_add_mono_l(q, b, a, ok)

law Nat.le_cancel_l:
  for +j: Nat
  for +b: Nat
  for +a: Nat
  for +ok: {C.Nat.upto(Nat.add(j, b), Nat.add(j, a)) == True{} : Bool}
  {C.Nat.upto(b, a) == True{} : Bool}

def Nat.le_cancel_l(j, b, a, ok):
  match j:
    case 0n:
      ok
    case 1n+q:
      Nat.le_cancel_l(q, b, a, ok)

# `a + j` and `j + a`, as a rewrite on a comparison.
law Nat.le_swap_add:
  for +b: Nat
  for +j: Nat
  for +a: Nat
  for +ok: {C.Nat.upto(Nat.add(b, j), Nat.add(a, j)) == True{} : Bool}
  {C.Nat.upto(Nat.add(j, b), Nat.add(j, a)) == True{} : Bool}

def Nat.le_swap_add(b, j, a, ok):
  It.Nat.upto_cast(Nat.add(b, j), Nat.add(j, b), Nat.add(a, j),
    Nat.add(j, a), N.Nat.add_comm(b, j), N.Nat.add_comm(a, j), ok)

law Nat.le_unswap_add:
  for +b: Nat
  for +j: Nat
  for +a: Nat
  for +ok: {C.Nat.upto(Nat.add(j, b), Nat.add(j, a)) == True{} : Bool}
  {C.Nat.upto(Nat.add(b, j), Nat.add(a, j)) == True{} : Bool}

def Nat.le_unswap_add(b, j, a, ok):
  It.Nat.upto_cast(Nat.add(j, b), Nat.add(b, j), Nat.add(j, a),
    Nat.add(a, j), N.Nat.add_comm(j, b), N.Nat.add_comm(j, a), ok)

# The last ordinal of the window, as a number.
law Nat.last_of_window:
  for +bb: Nat
  for +j: Nat
  {Nat.sub(Nat.add(bb, 1n+j), 1n) == Nat.add(bb, j) : Nat}

def Nat.last_of_window(bb, j):
  %E.Nat.sym(Nat.add(bb, 1n+j), 1n+Nat.add(bb, j), N.Nat.add_succ(bb, j))
    : {Nat.sub(_, 1n) == Nat.add(bb, j) : Nat}
  De.Nat.sub_zero(Nat.add(bb, j))

# From "the count-down reaches it" to "it is in the interval".
law Nat.window_forward:
  for +p: Nat
  for +bb: Nat
  for +xx: Nat
  for +pos: {C.Nat.gt(p, 0n) == True{} : Bool}
  for +le: {C.Nat.upto(xx, Nat.sub(Nat.add(bb, p), 1n)) == True{} : Bool}
  for +g: {C.Nat.gt(Nat.add(xx, p), Nat.sub(Nat.add(bb, p), 1n))
    == True{} : Bool}
  {Bool.and(C.Nat.upto(bb, xx), C.Nat.gt(Nat.add(bb, p), xx))
    == True{} : Bool}

def Nat.window_forward(p, bb, xx, pos, le, g):
  match p:
    case 0n:
      E.Bool.noconf({Bool.and(C.Nat.upto(bb, xx),
        C.Nat.gt(Nat.add(bb, 0n), xx)) == True{} : Bool}, pos)
    case 1n+j:
      %E.Nat.sym(Nat.add(bb, 1n+j), 1n+Nat.add(bb, j),
        N.Nat.add_succ(bb, j))
        : {Bool.and(C.Nat.upto(bb, xx), C.Nat.gt(_, xx))
          == True{} : Bool}
      %E.Bool.sym(C.Nat.upto(bb, xx), True{},
        Nat.le_cancel_l(j, bb, xx,
          Nat.le_swap_add(bb, j, xx,
            It.Nat.le_of_gt_succ2(Nat.add(xx, j), Nat.add(bb, j),
              It.Nat.gt_cast(Nat.add(xx, 1n+j), 1n+Nat.add(xx, j),
                Nat.sub(Nat.add(bb, 1n+j), 1n), Nat.add(bb, j),
                N.Nat.add_succ(xx, j), Nat.last_of_window(bb, j), g)))))
        : {Bool.and(_, C.Nat.gt(1n+Nat.add(bb, j), xx)) == True{} : Bool}
      Nat.gt_succ_of_le(xx, Nat.add(bb, j),
        It.Nat.upto_cast(xx, xx, Nat.sub(Nat.add(bb, 1n+j), 1n),
          Nat.add(bb, j), {==}, Nat.last_of_window(bb, j), le))

# And back.
law Nat.window_back:
  for +p: Nat
  for +bb: Nat
  for +xx: Nat
  for +pos: {C.Nat.gt(p, 0n) == True{} : Bool}
  for +lo: {C.Nat.upto(bb, xx) == True{} : Bool}
  for +hi: {C.Nat.gt(Nat.add(bb, p), xx) == True{} : Bool}
  {Bool.and(C.Nat.upto(xx, Nat.sub(Nat.add(bb, p), 1n)),
    C.Nat.gt(Nat.add(xx, p), Nat.sub(Nat.add(bb, p), 1n)))
    == True{} : Bool}

def Nat.window_back(p, bb, xx, pos, lo, hi):
  match p:
    case 0n:
      E.Bool.noconf({Bool.and(
        C.Nat.upto(xx, Nat.sub(Nat.add(bb, 0n), 1n)),
        C.Nat.gt(Nat.add(xx, 0n), Nat.sub(Nat.add(bb, 0n), 1n)))
        == True{} : Bool}, pos)
    case 1n+j:
      %E.Nat.sym(Nat.sub(Nat.add(bb, 1n+j), 1n), Nat.add(bb, j),
        Nat.last_of_window(bb, j))
        : {Bool.and(C.Nat.upto(xx, _),
            C.Nat.gt(Nat.add(xx, 1n+j), _)) == True{} : Bool}
      %E.Nat.sym(Nat.add(xx, 1n+j), 1n+Nat.add(xx, j),
        N.Nat.add_succ(xx, j))
        : {Bool.and(C.Nat.upto(xx, Nat.add(bb, j)),
            C.Nat.gt(_, Nat.add(bb, j))) == True{} : Bool}
      %E.Bool.sym(C.Nat.upto(xx, Nat.add(bb, j)), True{},
        It.Nat.le_of_gt_succ2(Nat.add(bb, j), xx,
          It.Nat.gt_cast(Nat.add(bb, 1n+j), 1n+Nat.add(bb, j), xx, xx,
            N.Nat.add_succ(bb, j), {==}, hi)))
        : {Bool.and(_, C.Nat.gt(1n+Nat.add(xx, j), Nat.add(bb, j)))
          == True{} : Bool}
      Nat.gt_succ_of_le(Nat.add(bb, j), Nat.add(xx, j),
        Nat.le_unswap_add(bb, j, xx,
          Nat.le_add_mono_l(j, bb, xx, lo)))

law Nat.le_span_start:
  for +p: Nat
  for +bb: Nat
  for +pos: {C.Nat.gt(p, 0n) == True{} : Bool}
  {C.Nat.upto(p, 1n+Nat.sub(Nat.add(bb, p), 1n)) == True{} : Bool}

def Nat.le_span_start(p, bb, pos):
  match p:
    case 0n:
      E.Bool.noconf({C.Nat.upto(0n,
        1n+Nat.sub(Nat.add(bb, 0n), 1n)) == True{} : Bool}, pos)
    case 1n+j:
      %E.Nat.sym(Nat.sub(Nat.add(bb, 1n+j), 1n), Nat.add(bb, j),
        Nat.last_of_window(bb, j))
        : {C.Nat.upto(1n+j, 1n+_) == True{} : Bool}
      It.Nat.le_add_left(j, bb)

# ---------------------------------------------------------------------------
# The count-down and the bit test answer the same question.
# ---------------------------------------------------------------------------

def Ords.nowrap(+k: Nat, +base: U32, +ord: U32,
  +eo: {U32.to_nat(ord)
    == Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n) : Nat})
  -> {C.Nat.upto(Dc.Nat.pow2(k), 1n+U32.to_nat(ord)) == True{} : Bool}:
  %E.Nat.sym(U32.to_nat(ord),
    Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n), eo)
    : {C.Nat.upto(Dc.Nat.pow2(k), 1n+_) == True{} : Bool}
  Nat.le_span_start(Dc.Nat.pow2(k), U32.to_nat(base),
    Dc.Nat.pow2_pos(k))

law Ords.in_down_is_interval:
  for +k: Nat
  for +m: Bool
  for +v: Bool
  for +base: U32
  for +ord: U32
  for +x: U32
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  for +eo: {U32.to_nat(ord)
    == Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n) : Nat}
  for +em: {m == U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))) : Bool}
  for +ev: {v == Sn.Ords.in_down(Dc.Nat.pow2(k), ord, x) : Bool}
  {Sn.Ords.in_down(Dc.Nat.pow2(k), ord, x) == m : Bool}

# The interval, from the bit test, in the form the count-down wants.
def Ords.window_of_match(+k: Nat, +base: U32, +x: U32,
  +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool},
  +em: {True{} == U32.is_eq(base, W.U32.diff(x, W.U32.mask(k)))
    : Bool})
  -> {Bool.and(C.Nat.upto(U32.to_nat(x),
       Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n)),
       C.Nat.gt(Nat.add(U32.to_nat(x), Dc.Nat.pow2(k)),
         Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n)))
     == True{} : Bool}:
  Nat.window_back(Dc.Nat.pow2(k), U32.to_nat(base), U32.to_nat(x),
    Dc.Nat.pow2_pos(k),
    E.Bool.and_l(C.Nat.upto(U32.to_nat(base), U32.to_nat(x)),
      C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
        U32.to_nat(x)),
      It.Interval.bounds_of_match(base, x, k, lb,
        E.Bool.sym(True{},
          U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))), em))),
    E.Bool.and_r(C.Nat.upto(U32.to_nat(base), U32.to_nat(x)),
      C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
        U32.to_nat(x)),
      It.Interval.bounds_of_match(base, x, k, lb,
        E.Bool.sym(True{},
          U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))), em))))

# The interval, from the count-down.
def Ords.window_of_span(+k: Nat, +base: U32, +ord: U32, +x: U32,
  +eo: {U32.to_nat(ord)
    == Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n) : Nat},
  +ev: {True{} == Sn.Ords.in_down(Dc.Nat.pow2(k), ord, x) : Bool})
  -> {Bool.and(C.Nat.upto(U32.to_nat(base), U32.to_nat(x)),
       C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
         U32.to_nat(x))) == True{} : Bool}:
  Nat.window_forward(Dc.Nat.pow2(k), U32.to_nat(base), U32.to_nat(x),
    Dc.Nat.pow2_pos(k),
    It.Nat.upto_cast(U32.to_nat(x), U32.to_nat(x), U32.to_nat(ord),
      Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n), {==}, eo,
      E.Bool.and_l(C.Nat.upto(U32.to_nat(x), U32.to_nat(ord)),
        C.Nat.gt(Nat.add(U32.to_nat(x), Dc.Nat.pow2(k)),
          U32.to_nat(ord)),
        Sn.Ords.span_of_in_down(Dc.Nat.pow2(k), U32.is_eq(ord, x), ord,
          x, {==}, Ords.nowrap(k, base, ord, eo),
          E.Bool.sym(True{},
            Sn.Ords.in_down(Dc.Nat.pow2(k), ord, x), ev)))),
    It.Nat.gt_cast(Nat.add(U32.to_nat(x), Dc.Nat.pow2(k)),
      Nat.add(U32.to_nat(x), Dc.Nat.pow2(k)), U32.to_nat(ord),
      Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n), {==}, eo,
      E.Bool.and_r(C.Nat.upto(U32.to_nat(x), U32.to_nat(ord)),
        C.Nat.gt(Nat.add(U32.to_nat(x), Dc.Nat.pow2(k)),
          U32.to_nat(ord)),
        Sn.Ords.span_of_in_down(Dc.Nat.pow2(k), U32.is_eq(ord, x), ord,
          x, {==}, Ords.nowrap(k, base, ord, eo),
          E.Bool.sym(True{},
            Sn.Ords.in_down(Dc.Nat.pow2(k), ord, x), ev)))))

# ---------------------------------------------------------------------------
# So a full node's count-down enumerates exactly its interval.
# ---------------------------------------------------------------------------

# If the count-down reaches an ordinal the bit test rejects, nothing holds.
def Ords.match_is_absurd(+k: Nat, +base: U32, +ord: U32, +x: U32,
  +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool},
  +eo: {U32.to_nat(ord)
    == Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n) : Nat},
  +em: {False{} == U32.is_eq(base, W.U32.diff(x, W.U32.mask(k)))
    : Bool},
  +ev: {True{} == Sn.Ords.in_down(Dc.Nat.pow2(k), ord, x) : Bool})
  -> {False{} == True{} : Bool}:
  %It.Interval.match_of_bounds(base, x, k, lb,
    E.Bool.and_l(C.Nat.upto(U32.to_nat(base), U32.to_nat(x)),
      C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
        U32.to_nat(x)),
      Ords.window_of_span(k, base, ord, x, eo, ev)),
    E.Bool.and_r(C.Nat.upto(U32.to_nat(base), U32.to_nat(x)),
      C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
        U32.to_nat(x)),
      Ords.window_of_span(k, base, ord, x, eo, ev)))
    : {False{} == _ : Bool}
  em

def Ords.in_down_is_interval(k, m, v, base, ord, x, lb, eo, em, ev):
  match m:
    case True{}:
      Sn.Ords.in_down_of_span(Dc.Nat.pow2(k), U32.is_eq(ord, x), ord, x,
        {==},
        It.Nat.upto_cast(U32.to_nat(x), U32.to_nat(x),
          Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n),
          U32.to_nat(ord), {==},
          E.Nat.sym(U32.to_nat(ord),
            Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n), eo),
          E.Bool.and_l(C.Nat.upto(U32.to_nat(x),
            Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n)),
            C.Nat.gt(Nat.add(U32.to_nat(x), Dc.Nat.pow2(k)),
              Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n)),
            Ords.window_of_match(k, base, x, lb, em))),
        It.Nat.gt_cast(Nat.add(U32.to_nat(x), Dc.Nat.pow2(k)),
          Nat.add(U32.to_nat(x), Dc.Nat.pow2(k)),
          Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n),
          U32.to_nat(ord), {==},
          E.Nat.sym(U32.to_nat(ord),
            Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n), eo),
          E.Bool.and_r(C.Nat.upto(U32.to_nat(x),
            Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n)),
            C.Nat.gt(Nat.add(U32.to_nat(x), Dc.Nat.pow2(k)),
              Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n)),
            Ords.window_of_match(k, base, x, lb, em))))
    case False{}:
      match v:
        case True{}:
          E.Bool.noconf({Sn.Ords.in_down(Dc.Nat.pow2(k), ord, x)
            == False{} : Bool},
            Ords.match_is_absurd(k, base, ord, x, lb, eo, em, ev))
        case False{}:
          E.Bool.sym(False{}, Sn.Ords.in_down(Dc.Nat.pow2(k), ord, x), ev)

law Ords.range_is_an_interval:
  for +k: Nat
  for +base: U32
  for +ord: U32
  for +x: U32
  for +tail: List<&2, U32>
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  for +eo: {U32.to_nat(ord)
    == Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n) : Nat}
  {List.contains(~U32, ~U32.is_eq,
    S.PSet.range(Dc.Nat.pow2(k), ord, tail), x)
    == Bool.or(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}

def Ords.range_is_an_interval(k, base, ord, x, tail, lb, eo):
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      S.PSet.range(Dc.Nat.pow2(k), ord, tail), x),
    Bool.or(Sn.Ords.in_down(Dc.Nat.pow2(k), ord, x),
      List.contains(~U32, ~U32.is_eq, tail, x)),
    Sn.Ords.contains_range(Dc.Nat.pow2(k), ord, tail, x))
    : {_ == Bool.or(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(Sn.Ords.in_down(Dc.Nat.pow2(k), ord, x),
    U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
    Ords.in_down_is_interval(k,
      U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
      Sn.Ords.in_down(Dc.Nat.pow2(k), ord, x), base, ord, x, lb, eo,
      {==}, {==}))
    : {Bool.or(_, List.contains(~U32, ~U32.is_eq, tail, x))
      == Bool.or(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  {==}
