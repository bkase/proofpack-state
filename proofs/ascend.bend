# proofs/ascend.bend -- the tree walk emits ordinals in order.
#
# `PSet.members` walks the tree low child first, with an accumulator tail, so
# what it builds is ascending. Proving that is one induction, and the only
# bookkeeping it needs is an interval: everything a node emits lies in
# [base, base + 2^(12+d)), and the tail it was handed starts at or above the
# end of that interval.
#
# The two halves of the invariant compose exactly. The high child's interval
# starts where the low child's ends, so the tail the low child sees -- the
# high child's output -- starts at base + 2^(12+p), which is exactly the end
# of the low child's own interval. Nothing has to be widened, and no U32
# addition has to be shown not to wrap, because the bounds are carried as
# numbers.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./split_add.bend as Sa
import ./shift.bend as Sf
import ./orderlist.bend as Ol
import ./childtest.bend as Ct2
import ./interval.bend as It
import ./halves.bend as Hv
import ./subsetconv.bend as Sc
import ./subsetalg.bend as Sa2
import ./tileorder.bend as To
import ./nodeenum.bend as Ne
import ./lastord.bend as Ld
import ./leafdiff.bend as Lf2
import ./leaf.bend as Lf
import ./treeenum.bend as Te
import ./validshape.bend as Vs
import ./leafenum.bend as Le
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# The two bounds, as numbers.
# ---------------------------------------------------------------------------

# Every ordinal on the list is at or above `k`.
def Ords.lower_all(+k: Nat, +l: List<&2, U32>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case Con{y, u}:
      Bool.and(C.Nat.upto(k, U32.to_nat(y)), Ords.lower_all(k, u))

law Ords.lower_of_contains:
  for +l: List<&2, U32>
  for +k: Nat
  for +y: U32
  for +lw: {Ords.lower_all(k, l) == True{} : Bool}
  for c: {List.contains(~U32, ~U32.is_eq, l, y) == True{} : Bool}
  {C.Nat.upto(k, U32.to_nat(y)) == True{} : Bool}

law Ords.lower_down:
  for +j: Nat
  for +k: Nat
  for +l: List<&2, U32>
  for +le: {C.Nat.upto(j, k) == True{} : Bool}
  for +lw: {Ords.lower_all(k, l) == True{} : Bool}
  {Ords.lower_all(j, l) == True{} : Bool}

def Ords.lower_down(j, k, l, le, lw):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(C.Nat.upto(j, U32.to_nat(y)),
        Ords.lower_all(j, u),
        Ct2.Nat.le_trans(j, k, U32.to_nat(y), le,
          E.Bool.and_l(C.Nat.upto(k, U32.to_nat(y)),
            Ords.lower_all(k, u), lw)),
        Ords.lower_down(j, k, u, le,
          E.Bool.and_r(C.Nat.upto(k, U32.to_nat(y)),
            Ords.lower_all(k, u), lw)))

law Ords.lt_all_of_lower:
  for +l: List<&2, U32>
  for +ord: U32
  for +k: Nat
  for +lw: {Ords.lower_all(k, l) == True{} : Bool}
  for +g: {C.Nat.gt(k, U32.to_nat(ord)) == True{} : Bool}
  {Ol.Ords.lt_all(ord, l) == True{} : Bool}

def Ords.lt_all_of_lower(l, ord, k, lw, g):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(U32.is_lt(ord, y), Ol.Ords.lt_all(ord, u),
        Ol.U32.lt_of_nat(ord, y,
          Ct2.Nat.gt_up(k, U32.to_nat(y), U32.to_nat(ord),
            E.Bool.and_l(C.Nat.upto(k, U32.to_nat(y)),
              Ords.lower_all(k, u), lw), g)),
        Ords.lt_all_of_lower(u, ord, k,
          E.Bool.and_r(C.Nat.upto(k, U32.to_nat(y)),
            Ords.lower_all(k, u), lw), g))

# Every ordinal on the list is below `k`.
def Ords.upper(+k: Nat, +l: List<&2, U32>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case Con{y, u}:
      Bool.and(C.Nat.gt(k, U32.to_nat(y)), Ords.upper(k, u))

law Ords.above_append:
  for +u: List<&2, U32>
  for +tail: List<&2, U32>
  for +y: U32
  for +k: Nat
  for +au: {Ol.Ords.above(y, u) == True{} : Bool}
  for +uy: {C.Nat.gt(k, U32.to_nat(y)) == True{} : Bool}
  for +tt: {Ords.lower_all(k, tail) == True{} : Bool}
  {Ol.Ords.above(y, List.append(&2, U32, u, tail)) == True{} : Bool}

def Ords.above_append(u, tail, y, k, au, uy, tt):
  match u:
    case Nil{}:
      match tail:
        case Nil{}:
          {==}
        case Con{z, w}:
          Ol.U32.lt_of_nat(y, z,
            Ct2.Nat.gt_up(k, U32.to_nat(z), U32.to_nat(y),
              E.Bool.and_l(C.Nat.upto(k, U32.to_nat(z)),
                Ords.lower_all(k, w), tt), uy))
    case Con{z, w}:
      au

law Ords.asc_append:
  for +a: List<&2, U32>
  for +tail: List<&2, U32>
  for +k: Nat
  for +aa: {Ol.Ords.asc(a) == True{} : Bool}
  for +at: {Ol.Ords.asc(tail) == True{} : Bool}
  for +ua: {Ords.upper(k, a) == True{} : Bool}
  for +tt: {Ords.lower_all(k, tail) == True{} : Bool}
  {Ol.Ords.asc(List.append(&2, U32, a, tail)) == True{} : Bool}

def Ords.asc_append(a, tail, k, aa, at, ua, tt):
  match a:
    case Nil{}:
      at
    case Con{y, u}:
      E.Bool.and_both(
        Ol.Ords.above(y, List.append(&2, U32, u, tail)),
        Ol.Ords.asc(List.append(&2, U32, u, tail)),
        Ords.above_append(u, tail, y, k,
          E.Bool.and_l(Ol.Ords.above(y, u), Ol.Ords.asc(u), aa), 
          E.Bool.and_l(C.Nat.gt(k, U32.to_nat(y)), Ords.upper(k, u),
            ua), tt),
        Ords.asc_append(u, tail, k,
          E.Bool.and_r(Ol.Ords.above(y, u), Ol.Ords.asc(u), aa), at,
          E.Bool.and_r(C.Nat.gt(k, U32.to_nat(y)), Ords.upper(k, u),
            ua), tt))

law Ords.lower_append:
  for +a: List<&2, U32>
  for +tail: List<&2, U32>
  for +k: Nat
  for +ta: {Ords.lower_all(k, a) == True{} : Bool}
  for +tt: {Ords.lower_all(k, tail) == True{} : Bool}
  {Ords.lower_all(k, List.append(&2, U32, a, tail)) == True{} : Bool}

def Ords.lower_append(a, tail, k, ta, tt):
  match a:
    case Nil{}:
      tt
    case Con{y, u}:
      E.Bool.and_both(C.Nat.upto(k, U32.to_nat(y)),
        Ords.lower_all(k, List.append(&2, U32, u, tail)),
        E.Bool.and_l(C.Nat.upto(k, U32.to_nat(y)),
          Ords.lower_all(k, u), ta),
        Ords.lower_append(u, tail, k,
          E.Bool.and_r(C.Nat.upto(k, U32.to_nat(y)),
            Ords.lower_all(k, u), ta), tt))

# ---------------------------------------------------------------------------
# Shifting a leaf's offsets by its base.
# ---------------------------------------------------------------------------

law U32.shift_value:
  for +y: U32
  for +base: U32
  for +k: Nat
  for +hy: {Dc.U32.hi_zero(y, k) == True{} : Bool}
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  {U32.to_nat((y + base : U32))
    == Nat.add(U32.to_nat(y), U32.to_nat(base)) : Nat}

def U32.shift_value(y, base, k, hy, lb):
  match y base:
    case U32{yw} U32{bw}:
      %E.U32.sym(E.U32.pak(Word.adc(32n, yw, bw, False{}, False{})),
        E.U32.pak(Word.or(32n, yw, bw)),
        Equal.cong(Word(32n), U32, E.U32.pak,
          Word.adc(32n, yw, bw, False{}, False{}),
          Word.or(32n, yw, bw),
          Sa.Word.adc_disjoint(32n, k, yw, bw, hy, lb)))
        : {U32.to_nat(_) == Nat.add(U32.to_nat(U32{yw}),
            U32.to_nat(U32{bw})) : Nat}
      Sa.U32.to_nat_or(U32{yw}, U32{bw}, k, hy, lb)

law Nat.gt_shift:
  for +bb: Nat
  for +yy: Nat
  for +zz: Nat
  for +g: {C.Nat.gt(zz, yy) == True{} : Bool}
  {C.Nat.gt(Nat.add(zz, bb), Nat.add(yy, bb)) == True{} : Bool}

def Nat.gt_shift(bb, yy, zz, g):
  %N.Nat.add_comm(bb, zz)
    : {C.Nat.gt(_, Nat.add(yy, bb)) == True{} : Bool}
  It.Nat.gt_add_of_lt(bb, yy, zz, g)

law U32.lt_shift:
  for +y: U32
  for +z: U32
  for +base: U32
  for +k: Nat
  for +hy: {Dc.U32.hi_zero(y, k) == True{} : Bool}
  for +hz: {Dc.U32.hi_zero(z, k) == True{} : Bool}
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  for +lt: {U32.is_lt(y, z) == True{} : Bool}
  {U32.is_lt((y + base : U32), (z + base : U32)) == True{} : Bool}

def U32.lt_shift(y, z, base, k, hy, hz, lb, lt):
  Ol.U32.lt_of_nat((y + base : U32), (z + base : U32),
    %E.Nat.sym(U32.to_nat((z + base : U32)),
      Nat.add(U32.to_nat(z), U32.to_nat(base)),
      U32.shift_value(z, base, k, hz, lb))
      : {C.Nat.gt(_, U32.to_nat((y + base : U32))) == True{} : Bool}
    %E.Nat.sym(U32.to_nat((y + base : U32)),
      Nat.add(U32.to_nat(y), U32.to_nat(base)),
      U32.shift_value(y, base, k, hy, lb))
      : {C.Nat.gt(Nat.add(U32.to_nat(z), U32.to_nat(base)), _)
        == True{} : Bool}
    Nat.gt_shift(U32.to_nat(base), U32.to_nat(y), U32.to_nat(z),
      Ol.Ords.lt_value(y, z, lt)))

law Ords.above_shift:
  for +u: List<&2, U32>
  for +y: U32
  for +base: U32
  for +k: Nat
  for +hy: {Dc.U32.hi_zero(y, k) == True{} : Bool}
  for +fu: {Sf.Ords.all_fit(u, k) == True{} : Bool}
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  for +au: {Ol.Ords.above(y, u) == True{} : Bool}
  {Ol.Ords.above((y + base : U32), S.PSet.shift(u, base)) == True{}
    : Bool}

def Ords.above_shift(u, y, base, k, hy, fu, lb, au):
  match u:
    case Nil{}:
      {==}
    case Con{z, w}:
      U32.lt_shift(y, z, base, k, hy,
        E.Bool.and_l(Dc.U32.hi_zero(z, k), Sf.Ords.all_fit(w, k), fu),
        lb, au)

law Ords.asc_shift:
  for +l: List<&2, U32>
  for +base: U32
  for +k: Nat
  for +al: {Ol.Ords.asc(l) == True{} : Bool}
  for +fl: {Sf.Ords.all_fit(l, k) == True{} : Bool}
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  {Ol.Ords.asc(S.PSet.shift(l, base)) == True{} : Bool}

def Ords.asc_shift(l, base, k, al, fl, lb):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(
        Ol.Ords.above((y + base : U32), S.PSet.shift(u, base)),
        Ol.Ords.asc(S.PSet.shift(u, base)),
        Ords.above_shift(u, y, base, k,
          E.Bool.and_l(Dc.U32.hi_zero(y, k), Sf.Ords.all_fit(u, k),
            fl),
          E.Bool.and_r(Dc.U32.hi_zero(y, k), Sf.Ords.all_fit(u, k),
            fl), lb,
          E.Bool.and_l(Ol.Ords.above(y, u), Ol.Ords.asc(u), al)),
        Ords.asc_shift(u, base, k,
          E.Bool.and_r(Ol.Ords.above(y, u), Ol.Ords.asc(u), al),
          E.Bool.and_r(Dc.U32.hi_zero(y, k), Sf.Ords.all_fit(u, k),
            fl), lb))

law Ords.lower_shift:
  for +l: List<&2, U32>
  for +base: U32
  for +k: Nat
  for +fl: {Sf.Ords.all_fit(l, k) == True{} : Bool}
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  {Ords.lower_all(U32.to_nat(base), S.PSet.shift(l, base)) == True{}
    : Bool}

def Ords.lower_shift(l, base, k, fl, lb):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(
        C.Nat.upto(U32.to_nat(base), U32.to_nat((y + base : U32))),
        Ords.lower_all(U32.to_nat(base), S.PSet.shift(u, base)),
        %E.Nat.sym(U32.to_nat((y + base : U32)),
          Nat.add(U32.to_nat(y), U32.to_nat(base)),
          U32.shift_value(y, base, k,
            E.Bool.and_l(Dc.U32.hi_zero(y, k), Sf.Ords.all_fit(u, k),
              fl), lb))
          : {C.Nat.upto(U32.to_nat(base), _) == True{} : Bool}
        It.Nat.le_add_left(U32.to_nat(base), U32.to_nat(y)),
        Ords.lower_shift(u, base, k,
          E.Bool.and_r(Dc.U32.hi_zero(y, k), Sf.Ords.all_fit(u, k),
            fl), lb))

law U32.to_nat_bound:
  for +y: U32
  for +k: Nat
  for +hy: {Dc.U32.hi_zero(y, k) == True{} : Bool}
  {C.Nat.gt(Dc.Nat.pow2(k), U32.to_nat(y)) == True{} : Bool}

def U32.to_nat_bound(y, k, hy):
  match y:
    case U32{yw}:
      Dc.Word.to_nat_bound(32n, k, yw, hy)

law Ords.upper_shift:
  for +l: List<&2, U32>
  for +base: U32
  for +k: Nat
  for +fl: {Sf.Ords.all_fit(l, k) == True{} : Bool}
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  {Ords.upper(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
    S.PSet.shift(l, base)) == True{} : Bool}

def Ords.upper_shift(l, base, k, fl, lb):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(
        C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
          U32.to_nat((y + base : U32))),
        Ords.upper(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
          S.PSet.shift(u, base)),
        %E.Nat.sym(U32.to_nat((y + base : U32)),
          Nat.add(U32.to_nat(y), U32.to_nat(base)),
          U32.shift_value(y, base, k,
            E.Bool.and_l(Dc.U32.hi_zero(y, k), Sf.Ords.all_fit(u, k),
              fl), lb))
          : {C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), _)
            == True{} : Bool}
        It.Nat.gt_add_of_lt(U32.to_nat(base), U32.to_nat(y),
          Dc.Nat.pow2(k),
          U32.to_nat_bound(y, k,
            E.Bool.and_l(Dc.U32.hi_zero(y, k),
              Sf.Ords.all_fit(u, k), fl))),
        Ords.upper_shift(u, base, k,
          E.Bool.and_r(Dc.U32.hi_zero(y, k), Sf.Ords.all_fit(u, k),
            fl), lb))

def Ords.lower_of_contains.pick(+u: List<&2, U32>, +k: Nat, +y: U32,
  +z: U32, +e: Bool, +ee: {e == U32.is_eq(z, y) : Bool},
  +lz: {C.Nat.upto(k, U32.to_nat(z)) == True{} : Bool},
  ih: {List.contains(~U32, ~U32.is_eq, u, y) == True{} : Bool} ->
    {C.Nat.upto(k, U32.to_nat(y)) == True{} : Bool},
  +c: {List.contains(~U32, ~U32.is_eq, Con{z, u}, y) == True{}
    : Bool})
  -> {C.Nat.upto(k, U32.to_nat(y)) == True{} : Bool}:
  match e:
    case True{}:
      %E.U32.eq_reflect(z, y,
        E.Bool.sym(True{}, U32.is_eq(z, y), ee))
        : {C.Nat.upto(k, U32.to_nat(_)) == True{} : Bool}
      lz
    case False{}:
      ih(Sc.Ords.contains_tail(z, u, y, ee, c))

def Ords.lower_of_contains(l, k, y, lw, c):
  match l:
    case Nil{}:
      E.Bool.noconf({C.Nat.upto(k, U32.to_nat(y)) == True{} : Bool},
        c)
    case Con{z, u}:
      Ords.lower_of_contains.pick(u, k, y, z, U32.is_eq(z, y), {==},
        E.Bool.and_l(C.Nat.upto(k, U32.to_nat(z)),
          Ords.lower_all(k, u), lw),
        Ords.lower_of_contains(u, k, y,
          E.Bool.and_r(C.Nat.upto(k, U32.to_nat(z)),
            Ords.lower_all(k, u), lw)), c)

# ---------------------------------------------------------------------------
# A leaf's own ordinals.
# ---------------------------------------------------------------------------

law Ords.asc_leaf_members:
  for +s: S.PSet
  for +v: {S.PSet.valid.leaf(s) == True{} : Bool}
  {Ol.Ords.asc(S.PSet.leaf_members(s)) == True{} : Bool}

def Ords.asc_leaf_members.full()
  -> {Ol.Ords.asc(S.PSet.leaf_members(S.PFull{})) == True{} : Bool}:
  %Equal.sym(List<&2, U32>, S.PSet.leaf_members(S.PFull{}),
    S.PSet.range(4096n, 4095, Nil{}), Te.PSet.full_leaf_members())
    : {Ol.Ords.asc(_) == True{} : Bool}
  To.Ords.asc_full_leaf()

def Ords.asc_leaf_members.dense(+ws: List<&2, U32>,
  +v: {S.PSet.valid.leaf(S.PDense{ws}) == True{} : Bool})
  -> {Ol.Ords.asc(S.PSet.leaf_members(S.PDense{ws})) == True{}
    : Bool}:
  To.Ords.asc_members(ws, v)

def Ords.asc_leaf_members.sparse(+offs: List<&2, U32>,
  +v: {S.PSet.valid.leaf(S.PSparse{offs}) == True{} : Bool})
  -> {Ol.Ords.asc(S.PSet.leaf_members(S.PSparse{offs})) == True{}
    : Bool}:
  Lf2.Ords.asc_of_valid_offs(offs, 0, True{}, True{}, v)

def Ords.asc_leaf_members(s, v):
  match s:
    case S.PZero{}:
      {==}
    case S.PFull{}:
      Ords.asc_leaf_members.full()
    case S.PSparse{offs}:
      Ords.asc_leaf_members.sparse(offs, v)
    case S.PDense{ws}:
      Ords.asc_leaf_members.dense(ws, v)
    case S.PBranch{l, h}:
      E.Bool.noconf({Ol.Ords.asc(S.PSet.leaf_members(
        S.PBranch{l, h})) == True{} : Bool}, v)

# ---------------------------------------------------------------------------
# A count-down over a node's whole interval.
# ---------------------------------------------------------------------------

law Ords.lower_range:
  for +l: List<&2, U32>
  for +k: Nat
  for +base: U32
  for +ord: U32
  for +tail: List<&2, U32>
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  for +eo: {U32.to_nat(ord)
    == Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n) : Nat}
  for +lw: {Ords.lower_all(Nat.add(U32.to_nat(base),
    Dc.Nat.pow2(k)), tail) == True{} : Bool}
  for +ai: {Sa2.Ords.all_in(l,
    S.PSet.range(Dc.Nat.pow2(k), ord, tail)) == True{} : Bool}
  {Ords.lower_all(U32.to_nat(base), l) == True{} : Bool}

def Ords.lower_range.pick(+k: Nat, +base: U32, +y: U32,
  +tail: List<&2, U32>, +m: Bool,
  +em: {m == U32.is_eq(base, W.U32.diff(y, W.U32.mask(k))) : Bool},
  +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool},
  +lw: {Ords.lower_all(Nat.add(U32.to_nat(base),
    Dc.Nat.pow2(k)), tail) == True{} : Bool},
  +ou: {Bool.or(U32.is_eq(base, W.U32.diff(y, W.U32.mask(k))),
    List.contains(~U32, ~U32.is_eq, tail, y)) == True{} : Bool})
  -> {C.Nat.upto(U32.to_nat(base), U32.to_nat(y)) == True{} : Bool}:
  match m:
    case True{}:
      E.Bool.and_l(C.Nat.upto(U32.to_nat(base), U32.to_nat(y)),
        C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
          U32.to_nat(y)),
        It.Interval.bounds_of_match(base, y, k, lb,
          E.Bool.sym(True{},
            U32.is_eq(base, W.U32.diff(y, W.U32.mask(k))), em)))
    case False{}:
      Ct2.Nat.le_trans(U32.to_nat(base),
        Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), U32.to_nat(y),
        Ct2.Nat.le_add_right(U32.to_nat(base), Dc.Nat.pow2(k)),
        Ords.lower_of_contains(tail,
          Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), y, lw,
          %E.Bool.sym(False{},
            U32.is_eq(base, W.U32.diff(y, W.U32.mask(k))), em)
            : {Bool.or(_, List.contains(~U32, ~U32.is_eq, tail, y))
              == True{} : Bool}
          ou))

def Ords.lower_range(l, k, base, ord, tail, lb, eo, lw, ai):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(C.Nat.upto(U32.to_nat(base), U32.to_nat(y)),
        Ords.lower_all(U32.to_nat(base), u),
        Ords.lower_range.pick(k, base, y, tail,
          U32.is_eq(base, W.U32.diff(y, W.U32.mask(k))), {==}, lb,
          lw,
          %Ne.Ords.range_is_an_interval(k, base, ord, y, tail, lb,
            eo) : {_ == True{} : Bool}
          E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
            S.PSet.range(Dc.Nat.pow2(k), ord, tail), y),
            Sa2.Ords.all_in(u,
              S.PSet.range(Dc.Nat.pow2(k), ord, tail)), ai)),
        Ords.lower_range(u, k, base, ord, tail, lb, eo, lw,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.range(Dc.Nat.pow2(k), ord, tail), y),
            Sa2.Ords.all_in(u,
              S.PSet.range(Dc.Nat.pow2(k), ord, tail)), ai)))

law Nat.pos_add:
  for +a: Nat
  for +b: Nat
  for +g: {C.Nat.gt(b, 0n) == True{} : Bool}
  {C.Nat.gt(Nat.add(a, b), 0n) == True{} : Bool}

def Nat.pos_add(a, b, g):
  Ct2.Nat.gt_up(b, Nat.add(a, b), 0n, It.Nat.le_add_left(b, a), g)

law Ords.asc_walk_range:
  for +k: Nat
  for +base: U32
  for +ord: U32
  for +tail: List<&2, U32>
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  for +eo: {U32.to_nat(ord)
    == Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n) : Nat}
  for +at: {Ol.Ords.asc(tail) == True{} : Bool}
  for +lw: {Ords.lower_all(Nat.add(U32.to_nat(base),
    Dc.Nat.pow2(k)), tail) == True{} : Bool}
  {Bool.and(Ol.Ords.asc(S.PSet.range(Dc.Nat.pow2(k), ord, tail)),
    Ords.lower_all(U32.to_nat(base),
      S.PSet.range(Dc.Nat.pow2(k), ord, tail))) == True{} : Bool}

def Ords.asc_walk_range(k, base, ord, tail, lb, eo, at, lw):
  E.Bool.and_both(
    Ol.Ords.asc(S.PSet.range(Dc.Nat.pow2(k), ord, tail)),
    Ords.lower_all(U32.to_nat(base),
      S.PSet.range(Dc.Nat.pow2(k), ord, tail)),
    To.Ords.asc_range(Dc.Nat.pow2(k), ord, tail, at,
      Ords.lt_all_of_lower(tail, ord,
        Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), lw,
        %E.Nat.sym(U32.to_nat(ord),
          Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n), eo)
          : {C.Nat.gt(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), _)
            == True{} : Bool}
        To.Ords.gt_pred(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)),
          Nat.pos_add(U32.to_nat(base), Dc.Nat.pow2(k),
            Dc.Nat.pow2_pos(k)))),
      %E.Nat.sym(U32.to_nat(ord),
        Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)), 1n), eo)
        : {C.Nat.upto(Dc.Nat.pow2(k), 1n+_) == True{} : Bool}
      Ne.Nat.le_span_start(Dc.Nat.pow2(k), U32.to_nat(base),
        Dc.Nat.pow2_pos(k))),
    Ords.lower_range(S.PSet.range(Dc.Nat.pow2(k), ord, tail), k,
      base, ord, tail, lb, eo, lw,
      Sa2.Ords.all_in_self(S.PSet.range(Dc.Nat.pow2(k), ord, tail))))

# ---------------------------------------------------------------------------
# The walk over a whole node.
# ---------------------------------------------------------------------------

law Ords.asc_walk:
  for +d: Nat
  for +s: S.PSet
  for +base: U32
  for +tail: List<&2, U32>
  for +v: {S.PSet.valid(d, s, True{}) == True{} : Bool}
  for +lb: {Sa.U32.lo_zero(base, 12n+d) == True{} : Bool}
  for +dok: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +at: {Ol.Ords.asc(tail) == True{} : Bool}
  for +lw: {Ords.lower_all(Nat.add(U32.to_nat(base),
    Dc.Nat.pow2(12n+d)), tail) == True{} : Bool}
  {Bool.and(Ol.Ords.asc(
      S.PSet.members(d, s, base, S.PSet.half(d), tail)),
    Ords.lower_all(U32.to_nat(base),
      S.PSet.members(d, s, base, S.PSet.half(d), tail)))
    == True{} : Bool}

def Ords.asc_walk.fits(+s: S.PSet,
  +v: {S.PSet.valid(0n, s, True{}) == True{} : Bool})
  -> {Te.PSet.fits.leaf(s) == True{} : Bool}:
  E.Bool.and_r(Le.PSet.ok.leaf(s), Te.PSet.fits.leaf(s),
    Vs.PSet.ok_leaf_of_valid(s, v))

def Ords.asc_walk.leaf(+s: S.PSet, +base: U32,
  +tail: List<&2, U32>,
  +v: {S.PSet.valid(0n, s, True{}) == True{} : Bool},
  +lb: {Sa.U32.lo_zero(base, 12n) == True{} : Bool},
  +at: {Ol.Ords.asc(tail) == True{} : Bool},
  +lw: {Ords.lower_all(Nat.add(U32.to_nat(base),
    Dc.Nat.pow2(12n)), tail) == True{} : Bool})
  -> {Bool.and(Ol.Ords.asc(List.append(&2, U32,
      S.PSet.shift(S.PSet.leaf_members(s), base), tail)),
    Ords.lower_all(U32.to_nat(base), List.append(&2, U32,
      S.PSet.shift(S.PSet.leaf_members(s), base), tail)))
    == True{} : Bool}:
  E.Bool.and_both(
    Ol.Ords.asc(List.append(&2, U32,
      S.PSet.shift(S.PSet.leaf_members(s), base), tail)),
    Ords.lower_all(U32.to_nat(base), List.append(&2, U32,
      S.PSet.shift(S.PSet.leaf_members(s), base), tail)),
    Ords.asc_append(S.PSet.shift(S.PSet.leaf_members(s), base), tail,
      Nat.add(U32.to_nat(base), Dc.Nat.pow2(12n)),
      Ords.asc_shift(S.PSet.leaf_members(s), base, 12n,
        Ords.asc_leaf_members(s, v),
        Te.PSet.leaf_members_fit(s, Ords.asc_walk.fits(s, v)), lb),
      at,
      Ords.upper_shift(S.PSet.leaf_members(s), base, 12n,
        Te.PSet.leaf_members_fit(s, Ords.asc_walk.fits(s, v)), lb),
      lw),
    Ords.lower_append(S.PSet.shift(S.PSet.leaf_members(s), base),
      tail, U32.to_nat(base),
      Ords.lower_shift(S.PSet.leaf_members(s), base, 12n,
        Te.PSet.leaf_members_fit(s, Ords.asc_walk.fits(s, v)), lb),
      Ords.lower_down(U32.to_nat(base),
        Nat.add(U32.to_nat(base), Dc.Nat.pow2(12n)), tail,
        Ct2.Nat.le_add_right(U32.to_nat(base), Dc.Nat.pow2(12n)),
        lw)))

law Nat.le_succ_of_gt:
  for +a: Nat
  for +b: Nat
  for +g: {C.Nat.gt(a, b) == True{} : Bool}
  {C.Nat.upto(1n+b, a) == True{} : Bool}

def Nat.le_succ_of_gt(a, b, g):
  match a:
    case 0n:
      E.Bool.noconf({C.Nat.upto(1n+b, 0n) == True{} : Bool}, g)
    case 1n+q:
      match b:
        case 0n:
          {==}
        case 1n+j:
          Nat.le_succ_of_gt(q, j, g)

def Ords.asc_walk.full(+p: Nat, +base: U32, +tail: List<&2, U32>,
  +lb: {Sa.U32.lo_zero(base, 13n+p) == True{} : Bool},
  +dok: {C.Nat.gt(32n, 12n+p) == True{} : Bool},
  +at: {Ol.Ords.asc(tail) == True{} : Bool},
  +lw: {Ords.lower_all(Nat.add(U32.to_nat(base),
    Dc.Nat.pow2(13n+p)), tail) == True{} : Bool})
  -> {Bool.and(Ol.Ords.asc(S.PSet.range(
      Nat.add(U32.to_nat(S.PSet.half(1n+p)),
        U32.to_nat(S.PSet.half(1n+p))),
      (base + S.PSet.half(1n+p) + S.PSet.half(1n+p) - 1 : U32),
      tail)),
    Ords.lower_all(U32.to_nat(base), S.PSet.range(
      Nat.add(U32.to_nat(S.PSet.half(1n+p)),
        U32.to_nat(S.PSet.half(1n+p))),
      (base + S.PSet.half(1n+p) + S.PSet.half(1n+p) - 1 : U32),
      tail))) == True{} : Bool}:
  %E.Nat.sym(Nat.add(U32.to_nat(S.PSet.half(1n+p)),
      U32.to_nat(S.PSet.half(1n+p))), Dc.Nat.pow2(13n+p),
    Ld.U32.full_node_count(12n+p, dok))
    : {Bool.and(Ol.Ords.asc(S.PSet.range(_,
        (base + S.PSet.half(1n+p) + S.PSet.half(1n+p) - 1 : U32),
        tail)),
      Ords.lower_all(U32.to_nat(base), S.PSet.range(_,
        (base + S.PSet.half(1n+p) + S.PSet.half(1n+p) - 1 : U32),
        tail))) == True{} : Bool}
  Ords.asc_walk_range(13n+p, base,
    (base + S.PSet.half(1n+p) + S.PSet.half(1n+p) - 1 : U32), tail,
    lb,
    Ld.U32.last_ordinal_value(base, 12n+p, lb,
      Nat.le_succ_of_gt(32n, 12n+p, dok)), at, lw)

def Ords.asc_walk.branch(+p: Nat, +lo: S.PSet, +hi: S.PSet,
  +base: U32, +tail: List<&2, U32>,
  +dok: {C.Nat.gt(32n, 12n+p) == True{} : Bool},
  +ih: {Bool.and(Ol.Ords.asc(S.PSet.members(p, lo, base,
      S.PSet.half(p), S.PSet.members(p, hi,
        (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail))),
    Ords.lower_all(U32.to_nat(base), S.PSet.members(p, lo, base,
      S.PSet.half(p), S.PSet.members(p, hi,
        (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail))))
    == True{} : Bool})
  -> {Bool.and(Ol.Ords.asc(S.PSet.members(p, lo, base,
      U32.shr(S.PSet.half(1n+p)), S.PSet.members(p, hi,
        (base + S.PSet.half(1n+p) : U32),
        U32.shr(S.PSet.half(1n+p)), tail))),
    Ords.lower_all(U32.to_nat(base), S.PSet.members(p, lo, base,
      U32.shr(S.PSet.half(1n+p)), S.PSet.members(p, hi,
        (base + S.PSet.half(1n+p) : U32),
        U32.shr(S.PSet.half(1n+p)), tail))))
    == True{} : Bool}:
  %E.U32.sym(U32.shr(S.PSet.half(1n+p)), S.PSet.half(p),
    Lf.PSet.half_shr(p, S.PSet.half(1n+p), {==}, dok))
    : {Bool.and(Ol.Ords.asc(S.PSet.members(p, lo, base, _,
        S.PSet.members(p, hi, (base + S.PSet.half(1n+p) : U32), _,
          tail))),
      Ords.lower_all(U32.to_nat(base), S.PSet.members(p, lo, base, _,
        S.PSet.members(p, hi, (base + S.PSet.half(1n+p) : U32), _,
          tail)))) == True{} : Bool}
  ih

def Ords.asc_walk.hi_lower(+p: Nat, +base: U32,
  +tail: List<&2, U32>,
  +lb: {Sa.U32.lo_zero(base, 13n+p) == True{} : Bool},
  +dok: {C.Nat.gt(32n, 12n+p) == True{} : Bool},
  +lw: {Ords.lower_all(Nat.add(U32.to_nat(base),
    Dc.Nat.pow2(13n+p)), tail) == True{} : Bool})
  -> {Ords.lower_all(Nat.add(
    U32.to_nat((base + S.PSet.half(1n+p) : U32)),
    Dc.Nat.pow2(12n+p)), tail) == True{} : Bool}:
  %E.Nat.sym(U32.to_nat((base + S.PSet.half(1n+p) : U32)),
    Nat.add(U32.to_nat(base), Dc.Nat.pow2(12n+p)),
    Hv.U32.to_nat_half_base(base, 12n+p, lb, dok))
    : {Ords.lower_all(Nat.add(_, Dc.Nat.pow2(12n+p)), tail)
      == True{} : Bool}
  %E.Nat.sym(Nat.add(Nat.add(U32.to_nat(base), Dc.Nat.pow2(12n+p)),
      Dc.Nat.pow2(12n+p)),
    Nat.add(U32.to_nat(base),
      Nat.add(Dc.Nat.pow2(12n+p), Dc.Nat.pow2(12n+p))),
    N.Nat.add_assoc(U32.to_nat(base), Dc.Nat.pow2(12n+p),
      Dc.Nat.pow2(12n+p)))
    : {Ords.lower_all(_, tail) == True{} : Bool}
  %Ct2.Nat.pow2_split(12n+p)
    : {Ords.lower_all(Nat.add(U32.to_nat(base), _), tail)
      == True{} : Bool}
  lw

def Ords.asc_walk.lo_lower(+p: Nat, +base: U32,
  +inner: List<&2, U32>,
  +lb: {Sa.U32.lo_zero(base, 13n+p) == True{} : Bool},
  +dok: {C.Nat.gt(32n, 12n+p) == True{} : Bool},
  +lwi: {Ords.lower_all(
    U32.to_nat((base + S.PSet.half(1n+p) : U32)), inner) == True{}
    : Bool})
  -> {Ords.lower_all(Nat.add(U32.to_nat(base),
    Dc.Nat.pow2(12n+p)), inner) == True{} : Bool}:
  %Hv.U32.to_nat_half_base(base, 12n+p, lb, dok)
    : {Ords.lower_all(_, inner) == True{} : Bool}
  lwi

def Ords.asc_walk(d, s, base, tail, v, lb, dok, at, lw):
  match d:
    case 0n:
      Ords.asc_walk.leaf(s, base, tail, v, lb, at, lw)
    case 1n+p:
      match s:
        case S.PZero{}:
          E.Bool.and_both(Ol.Ords.asc(tail),
            Ords.lower_all(U32.to_nat(base), tail), at,
            Ords.lower_down(U32.to_nat(base),
              Nat.add(U32.to_nat(base), Dc.Nat.pow2(13n+p)), tail,
              Ct2.Nat.le_add_right(U32.to_nat(base),
                Dc.Nat.pow2(13n+p)), lw))
        case S.PSparse{offs}:
          E.Bool.noconf({Bool.and(Ol.Ords.asc(
            S.PSet.members(1n+p, S.PSparse{offs}, base,
              S.PSet.half(1n+p), tail)),
            Ords.lower_all(U32.to_nat(base),
              S.PSet.members(1n+p, S.PSparse{offs}, base,
                S.PSet.half(1n+p), tail))) == True{} : Bool}, v)
        case S.PDense{ws}:
          E.Bool.noconf({Bool.and(Ol.Ords.asc(
            S.PSet.members(1n+p, S.PDense{ws}, base,
              S.PSet.half(1n+p), tail)),
            Ords.lower_all(U32.to_nat(base),
              S.PSet.members(1n+p, S.PDense{ws}, base,
                S.PSet.half(1n+p), tail))) == True{} : Bool}, v)
        case S.PFull{}:
          Ords.asc_walk.full(p, base, tail, lb, dok, at, lw)
        case S.PBranch{lo, hi}:
          Ords.asc_walk.branch(p, lo, hi, base, tail, dok,
            Ords.asc_walk(p, lo, base,
              S.PSet.members(p, hi,
                (base + S.PSet.half(1n+p) : U32), S.PSet.half(p),
                tail),
              E.Bool.and_l(S.PSet.valid(p, lo, True{}),
                S.PSet.valid(p, hi, True{}),
                Vs.PSet.both_of_branch(p, lo, hi, v)),
              Hv.Word.lo_zero_down(32n, W.U32.word(base), 12n+p, lb),
              Dc.Nat.gt_down(32n, 11n+p, dok),
              E.Bool.and_l(Ol.Ords.asc(S.PSet.members(p, hi,
                (base + S.PSet.half(1n+p) : U32), S.PSet.half(p),
                tail)),
                Ords.lower_all(
                  U32.to_nat((base + S.PSet.half(1n+p) : U32)),
                  S.PSet.members(p, hi,
                    (base + S.PSet.half(1n+p) : U32),
                    S.PSet.half(p), tail)),
                Ords.asc_walk(p, hi,
                  (base + S.PSet.half(1n+p) : U32), tail,
                  E.Bool.and_r(S.PSet.valid(p, lo, True{}),
                    S.PSet.valid(p, hi, True{}),
                    Vs.PSet.both_of_branch(p, lo, hi, v)),
                  Hv.U32.lo_zero_half_base(base, 12n+p, lb),
                  Dc.Nat.gt_down(32n, 11n+p, dok), at,
                  Ords.asc_walk.hi_lower(p, base, tail, lb, dok,
                    lw))),
              Ords.asc_walk.lo_lower(p, base,
                S.PSet.members(p, hi,
                  (base + S.PSet.half(1n+p) : U32), S.PSet.half(p),
                  tail), lb, dok,
                E.Bool.and_r(Ol.Ords.asc(S.PSet.members(p, hi,
                  (base + S.PSet.half(1n+p) : U32), S.PSet.half(p),
                  tail)),
                  Ords.lower_all(
                    U32.to_nat((base + S.PSet.half(1n+p) : U32)),
                    S.PSet.members(p, hi,
                      (base + S.PSet.half(1n+p) : U32),
                      S.PSet.half(p), tail)),
                  Ords.asc_walk(p, hi,
                    (base + S.PSet.half(1n+p) : U32), tail,
                    E.Bool.and_r(S.PSet.valid(p, lo, True{}),
                      S.PSet.valid(p, hi, True{}),
                      Vs.PSet.both_of_branch(p, lo, hi, v)),
                    Hv.U32.lo_zero_half_base(base, 12n+p, lb),
                    Dc.Nat.gt_down(32n, 11n+p, dok), at,
                    Ords.asc_walk.hi_lower(p, base, tail, lb, dok,
                      lw))))))

law Ords.asc_to_list:
  for +d: Nat
  for +s: S.PSet
  for +v: {S.PSet.valid(d, s, True{}) == True{} : Bool}
  for +dok: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {Ol.Ords.asc(S.PSet.to_list(d, s)) == True{} : Bool}

def Ords.asc_to_list(d, s, v, dok):
  E.Bool.and_l(Ol.Ords.asc(S.PSet.members(d, s, 0, S.PSet.half(d),
    Nil{})),
    Ords.lower_all(U32.to_nat(0),
      S.PSet.members(d, s, 0, S.PSet.half(d), Nil{})),
    Ords.asc_walk(d, s, 0, Nil{}, v,
      Te.Word.lo_zero_of_zero_bits(32n, W.U32.word(0), 12n+d, {==}),
      dok, {==}, {==}))
