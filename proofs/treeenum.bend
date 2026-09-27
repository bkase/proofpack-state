# proofs/treeenum.bend -- the tree enumerates exactly its members.
#
# `PSet.to_list` walks the tree emitting ordinals; `PSet.member` walks the
# same tree answering one question. This file is the induction that says they
# agree at every node: the list a node contributes contains an ordinal exactly
# when the ordinal is inside the node's interval and the node holds it.
#
# Each arm is a different reason. A leaf shifts its own members by the base,
# so it needs the shift law and the leaf law. A full node counts down, so it
# needs the count-down to be the interval. A branch splits, so it needs the
# two halves to be disjoint and to cover -- and, since the two walks descend
# differently, it needs their descents to arrive at the same ordinal.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./split_add.bend as Sa
import ./shift.bend as Sf
import ./shape.bend as Sp2
import ./leafenum.bend as Le
import ./interval.bend as It
import ./nodeenum.bend as Ne
import ./lastord.bend as Ld
import ./halves.bend as Hv
import ./maskwidth.bend as Mw
import ./childtest.bend as Ct
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/set.bend as S

# The shape a node must have for the two walks to agree: leaves are the
# leaf shapes, with members that fit in a leaf; above the leaf level only
# zero, full and branch, which is what `PSet.valid` accepts there.
def PSet.ok(+d: Nat, +s: S.PSet) -> Bool:
  match d:
    case 0n:
      Bool.and(Le.PSet.ok.leaf(s),
        Sf.Ords.all_fit(S.PSet.leaf_members(s), 12n))
    case 1n+p:
      match s:
        case S.PZero{}:
          True{}
        case S.PFull{}:
          True{}
        case S.PSparse{offs}:
          False{}
        case S.PDense{ws}:
          False{}
        case S.PBranch{lo, hi}:
          Bool.and(PSet.ok(p, lo), PSet.ok(p, hi))

law Bool.and_true_r:
  for +a: Bool
  {Bool.and(a, True{}) == a : Bool}

def Bool.and_true_r(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law Nat.le_of_gt:
  for +a: Nat
  for +b: Nat
  for +g: {C.Nat.gt(a, b) == True{} : Bool}
  {C.Nat.upto(1n+b, a) == True{} : Bool}

def Nat.le_of_gt(a, b, g):
  match a:
    case 0n:
      E.Bool.noconf({C.Nat.upto(1n+b, 0n) == True{} : Bool}, g)
    case 1n+q:
      match b:
        case 0n:
          {==}
        case 1n+r:
          Nat.le_of_gt(q, r, g)

# ---------------------------------------------------------------------------
# A leaf.
# ---------------------------------------------------------------------------

def PSet.members_contains.leaf(+s: S.PSet, +base: U32, +x: U32,
  +tail: List<&2, U32>,
  +ok: {PSet.ok(0n, s) == True{} : Bool},
  +lz: {Sa.U32.lo_zero(base, 12n) == True{} : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
       S.PSet.members(0n, s, base, S.PSet.half(0n), tail), x)
     == Bool.or(
          Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n))),
            S.PSet.mem(0n, s, S.PSet.half(0n),
              U32.and(x, W.U32.mask(12n)))),
          List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}:
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      List.append(&2, U32, S.PSet.shift(S.PSet.leaf_members(s), base),
        tail), x),
    Bool.or(List.contains(~U32, ~U32.is_eq,
        S.PSet.shift(S.PSet.leaf_members(s), base), x),
      List.contains(~U32, ~U32.is_eq, tail, x)),
    Le.List.contains_append(
      S.PSet.shift(S.PSet.leaf_members(s), base), tail, x))
    : {_ == Bool.or(
        Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n))),
          S.PSet.mem.leaf(s, U32.and(x, W.U32.mask(12n)))),
        List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      S.PSet.shift(S.PSet.leaf_members(s), base), x),
    Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n))),
      List.contains(~U32, ~U32.is_eq, S.PSet.leaf_members(s),
        U32.and(x, W.U32.mask(12n)))),
    Sf.Ords.contains_shift(S.PSet.leaf_members(s),
      Sf.Ords.head_shift_eq(S.PSet.leaf_members(s), base, x),
      U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n))),
      Sf.Ords.head_low_eq(S.PSet.leaf_members(s), x, 12n),
      base, x, 12n, {==}, {==}, {==},
      E.Bool.and_r(Le.PSet.ok.leaf(s),
        Sf.Ords.all_fit(S.PSet.leaf_members(s), 12n), ok), lz))
    : {Bool.or(_, List.contains(~U32, ~U32.is_eq, tail, x))
      == Bool.or(
        Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n))),
          S.PSet.mem.leaf(s, U32.and(x, W.U32.mask(12n)))),
        List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      S.PSet.leaf_members(s), U32.and(x, W.U32.mask(12n))),
    S.PSet.mem.leaf(s, U32.and(x, W.U32.mask(12n))),
    Le.PSet.leaf_members_mem(s, U32.and(x, W.U32.mask(12n)),
      Sa.U32.hi_zero_low(x, 12n),
      E.Bool.and_l(Le.PSet.ok.leaf(s),
        Sf.Ords.all_fit(S.PSet.leaf_members(s), 12n), ok)))
    : {Bool.or(Bool.and(
        U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n))), _),
        List.contains(~U32, ~U32.is_eq, tail, x))
      == Bool.or(
        Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n))),
          S.PSet.mem.leaf(s, U32.and(x, W.U32.mask(12n)))),
        List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  {==}

# ---------------------------------------------------------------------------
# A full node.
# ---------------------------------------------------------------------------

def PSet.members_contains.full(+p: Nat, +base: U32, +x: U32,
  +tail: List<&2, U32>,
  +lz: {Sa.U32.lo_zero(base, 13n+p) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 12n+p) == True{} : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
       S.PSet.members(1n+p, S.PFull{}, base, S.PSet.half(1n+p), tail),
       x)
     == Bool.or(
          Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
            S.PSet.mem(1n+p, S.PFull{}, S.PSet.half(1n+p),
              U32.and(x, W.U32.mask(13n+p)))),
          List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}:
  %E.Bool.sym(Bool.and(
      U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))), True{}),
    U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
    Bool.and_true_r(U32.is_eq(base, W.U32.diff(x,
      W.U32.mask(13n+p)))))
    : {List.contains(~U32, ~U32.is_eq,
        S.PSet.range(Nat.add(U32.to_nat(U32.shln(1, 12n+p)),
          U32.to_nat(U32.shln(1, 12n+p))),
          (base + U32.shln(1, 12n+p) + U32.shln(1, 12n+p) - 1 : U32),
          tail), x)
      == Bool.or(_, List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Nat.sym(Nat.add(U32.to_nat(U32.shln(1, 12n+p)),
      U32.to_nat(U32.shln(1, 12n+p))), Dc.Nat.pow2(13n+p),
    Ld.U32.full_node_count(12n+p, lt))
    : {List.contains(~U32, ~U32.is_eq,
        S.PSet.range(_,
          (base + U32.shln(1, 12n+p) + U32.shln(1, 12n+p) - 1 : U32),
          tail), x)
      == Bool.or(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  Ne.Ords.range_is_an_interval(13n+p, base,
    (base + U32.shln(1, 12n+p) + U32.shln(1, 12n+p) - 1 : U32), x,
    tail, lz,
    Ld.U32.last_ordinal_value(base, 12n+p, lz,
      Nat.le_of_gt(32n, 12n+p, lt)))

# ---------------------------------------------------------------------------
# A branch. The two walks descend differently -- one by comparing against the
# half, one by masking one bit narrower -- so the arm is in two halves, and
# each half has to say both that the descents agree and that the other child
# contributes nothing.
# ---------------------------------------------------------------------------

def PSet.members_contains.low(+p: Nat, +base: U32, +x: U32,
  +tail: List<&2, U32>, +lo: S.PSet, +hi: S.PSet,
  +lz: {Sa.U32.lo_zero(base, 13n+p) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 12n+p) == True{} : Bool},
  +ehb: {True{} == Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)),
    12n+p) : Bool},
  +ihlo: {List.contains(~U32, ~U32.is_eq,
      S.PSet.members(p, lo, base, S.PSet.half(p),
        S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
          S.PSet.half(p), tail)), x)
    == Bool.or(
         Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+p))),
           S.PSet.mem(p, lo, S.PSet.half(p),
             U32.and(x, W.U32.mask(12n+p)))),
         List.contains(~U32, ~U32.is_eq,
           S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
             S.PSet.half(p), tail), x)) : Bool},
  +ihhi: {List.contains(~U32, ~U32.is_eq,
      S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
        S.PSet.half(p), tail), x)
    == Bool.or(
         Bool.and(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
           W.U32.diff(x, W.U32.mask(12n+p))),
           S.PSet.mem(p, hi, S.PSet.half(p),
             U32.and(x, W.U32.mask(12n+p)))),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
       S.PSet.members(p, lo, base, S.PSet.half(p),
         S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
           S.PSet.half(p), tail)), x)
     == Bool.or(
          Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
            S.PSet.mem(p, lo, S.PSet.half(p),
              U32.and(x, W.U32.mask(13n+p)))),
          List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}:
  %E.U32.sym(U32.and(x, W.U32.mask(13n+p)),
    U32.and(x, W.U32.mask(12n+p)),
    Mw.U32.mask_step(x, 12n+p,
      E.Bool.sym(True{},
        Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p), ehb)))
    : {List.contains(~U32, ~U32.is_eq,
        S.PSet.members(p, lo, base, S.PSet.half(p),
          S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
            S.PSet.half(p), tail)), x)
      == Bool.or(
           Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
             S.PSet.mem(p, lo, S.PSet.half(p), _)),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      S.PSet.members(p, lo, base, S.PSet.half(p),
        S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
          S.PSet.half(p), tail)), x),
    Bool.or(
      Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+p))),
        S.PSet.mem(p, lo, S.PSet.half(p),
          U32.and(x, W.U32.mask(12n+p)))),
      List.contains(~U32, ~U32.is_eq,
        S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
          S.PSet.half(p), tail), x)),
    ihlo)
    : {_ == Bool.or(
         Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
           S.PSet.mem(p, lo, S.PSet.half(p),
             U32.and(x, W.U32.mask(12n+p)))),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
        S.PSet.half(p), tail), x),
    Bool.or(
      Bool.and(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
        W.U32.diff(x, W.U32.mask(12n+p))),
        S.PSet.mem(p, hi, S.PSet.half(p),
          U32.and(x, W.U32.mask(12n+p)))),
      List.contains(~U32, ~U32.is_eq, tail, x)),
    ihhi)
    : {Bool.or(
        Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+p))),
          S.PSet.mem(p, lo, S.PSet.half(p),
            U32.and(x, W.U32.mask(12n+p)))), _)
      == Bool.or(
           Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
             S.PSet.mem(p, lo, S.PSet.half(p),
               U32.and(x, W.U32.mask(12n+p)))),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+p))),
    U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
    Ct.Test.low_matches(base, 12n+p, x,
      U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
      U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+p))), lz,
      E.Bool.sym(True{},
        Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p), ehb),
      {==}, {==}))
    : {Bool.or(Bool.and(_,
        S.PSet.mem(p, lo, S.PSet.half(p),
          U32.and(x, W.U32.mask(12n+p)))),
        Bool.or(
          Bool.and(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
            W.U32.diff(x, W.U32.mask(12n+p))),
            S.PSet.mem(p, hi, S.PSet.half(p),
              U32.and(x, W.U32.mask(12n+p)))),
          List.contains(~U32, ~U32.is_eq, tail, x)))
      == Bool.or(
           Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
             S.PSet.mem(p, lo, S.PSet.half(p),
               U32.and(x, W.U32.mask(12n+p)))),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
      W.U32.diff(x, W.U32.mask(12n+p))), False{},
    Ct.Test.high_misses(base, 12n+p, x,
      U32.is_eq((base + U32.shln(1, 12n+p) : U32),
        W.U32.diff(x, W.U32.mask(12n+p))), lz, lt,
      E.Bool.sym(True{},
        Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p), ehb),
      {==}))
    : {Bool.or(
        Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
          S.PSet.mem(p, lo, S.PSet.half(p),
            U32.and(x, W.U32.mask(12n+p)))),
        Bool.or(Bool.and(_,
          S.PSet.mem(p, hi, S.PSet.half(p),
            U32.and(x, W.U32.mask(12n+p)))),
          List.contains(~U32, ~U32.is_eq, tail, x)))
      == Bool.or(
           Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
             S.PSet.mem(p, lo, S.PSet.half(p),
               U32.and(x, W.U32.mask(12n+p)))),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  {==}

def PSet.members_contains.high(+p: Nat, +base: U32, +x: U32,
  +tail: List<&2, U32>, +lo: S.PSet, +hi: S.PSet,
  +lz: {Sa.U32.lo_zero(base, 13n+p) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 12n+p) == True{} : Bool},
  +ehb: {False{} == Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)),
    12n+p) : Bool},
  +ihlo: {List.contains(~U32, ~U32.is_eq,
      S.PSet.members(p, lo, base, S.PSet.half(p),
        S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
          S.PSet.half(p), tail)), x)
    == Bool.or(
         Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+p))),
           S.PSet.mem(p, lo, S.PSet.half(p),
             U32.and(x, W.U32.mask(12n+p)))),
         List.contains(~U32, ~U32.is_eq,
           S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
             S.PSet.half(p), tail), x)) : Bool},
  +ihhi: {List.contains(~U32, ~U32.is_eq,
      S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
        S.PSet.half(p), tail), x)
    == Bool.or(
         Bool.and(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
           W.U32.diff(x, W.U32.mask(12n+p))),
           S.PSet.mem(p, hi, S.PSet.half(p),
             U32.and(x, W.U32.mask(12n+p)))),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
       S.PSet.members(p, lo, base, S.PSet.half(p),
         S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
           S.PSet.half(p), tail)), x)
     == Bool.or(
          Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
            S.PSet.mem(p, hi, S.PSet.half(p),
              U32.sub(U32.and(x, W.U32.mask(13n+p)),
                U32.shln(1, 12n+p)))),
          List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}:
  %E.U32.sym(U32.sub(U32.and(x, W.U32.mask(13n+p)),
      U32.shln(1, 12n+p)),
    U32{Dc.Word.clear(32n,
      W.U32.word(U32.and(x, W.U32.mask(13n+p))), 12n+p)},
    Dc.U32.sub_shln(U32.and(x, W.U32.mask(13n+p)), 12n+p,
      Dc.Word.bit_of_not_hi_zero(32n, 12n+p,
        W.U32.word(U32.and(x, W.U32.mask(13n+p))),
        Sa.U32.hi_zero_low(x, 13n+p),
        E.Bool.sym(False{},
          Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p), ehb))))
    : {List.contains(~U32, ~U32.is_eq,
        S.PSet.members(p, lo, base, S.PSet.half(p),
          S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
            S.PSet.half(p), tail)), x)
      == Bool.or(
           Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
             S.PSet.mem(p, hi, S.PSet.half(p), _)),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.U32.sym(U32{Dc.Word.clear(32n,
      W.U32.word(U32.and(x, W.U32.mask(13n+p))), 12n+p)},
    U32.and(x, W.U32.mask(12n+p)), Mw.U32.clear_mask(x, 12n+p))
    : {List.contains(~U32, ~U32.is_eq,
        S.PSet.members(p, lo, base, S.PSet.half(p),
          S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
            S.PSet.half(p), tail)), x)
      == Bool.or(
           Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
             S.PSet.mem(p, hi, S.PSet.half(p), _)),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      S.PSet.members(p, lo, base, S.PSet.half(p),
        S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
          S.PSet.half(p), tail)), x),
    Bool.or(
      Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+p))),
        S.PSet.mem(p, lo, S.PSet.half(p),
          U32.and(x, W.U32.mask(12n+p)))),
      List.contains(~U32, ~U32.is_eq,
        S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
          S.PSet.half(p), tail), x)),
    ihlo)
    : {_ == Bool.or(
         Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
           S.PSet.mem(p, hi, S.PSet.half(p),
             U32.and(x, W.U32.mask(12n+p)))),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
        S.PSet.half(p), tail), x),
    Bool.or(
      Bool.and(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
        W.U32.diff(x, W.U32.mask(12n+p))),
        S.PSet.mem(p, hi, S.PSet.half(p),
          U32.and(x, W.U32.mask(12n+p)))),
      List.contains(~U32, ~U32.is_eq, tail, x)),
    ihhi)
    : {Bool.or(
        Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+p))),
          S.PSet.mem(p, lo, S.PSet.half(p),
            U32.and(x, W.U32.mask(12n+p)))), _)
      == Bool.or(
           Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
             S.PSet.mem(p, hi, S.PSet.half(p),
               U32.and(x, W.U32.mask(12n+p)))),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+p))),
    False{},
    Ct.Test.low_misses(base, 12n+p, x,
      U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+p))), lz,
      E.Bool.sym(False{},
        Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p), ehb),
      {==}))
    : {Bool.or(Bool.and(_,
        S.PSet.mem(p, lo, S.PSet.half(p),
          U32.and(x, W.U32.mask(12n+p)))),
        Bool.or(
          Bool.and(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
            W.U32.diff(x, W.U32.mask(12n+p))),
            S.PSet.mem(p, hi, S.PSet.half(p),
              U32.and(x, W.U32.mask(12n+p)))),
          List.contains(~U32, ~U32.is_eq, tail, x)))
      == Bool.or(
           Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
             S.PSet.mem(p, hi, S.PSet.half(p),
               U32.and(x, W.U32.mask(12n+p)))),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
      W.U32.diff(x, W.U32.mask(12n+p))),
    U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
    Ct.Test.high_matches(base, 12n+p, x,
      U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
      U32.is_eq((base + U32.shln(1, 12n+p) : U32),
        W.U32.diff(x, W.U32.mask(12n+p))), lz, lt,
      E.Bool.sym(False{},
        Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p), ehb),
      {==}, {==}))
    : {Bool.or(Bool.and(False{},
        S.PSet.mem(p, lo, S.PSet.half(p),
          U32.and(x, W.U32.mask(12n+p)))),
        Bool.or(Bool.and(_,
          S.PSet.mem(p, hi, S.PSet.half(p),
            U32.and(x, W.U32.mask(12n+p)))),
          List.contains(~U32, ~U32.is_eq, tail, x)))
      == Bool.or(
           Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
             S.PSet.mem(p, hi, S.PSet.half(p),
               U32.and(x, W.U32.mask(12n+p)))),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  {==}

def PSet.members_contains.branch(+p: Nat, +base: U32, +x: U32,
  +tail: List<&2, U32>, +lo: S.PSet, +hi: S.PSet,
  +lz: {Sa.U32.lo_zero(base, 13n+p) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 12n+p) == True{} : Bool},
  +hb: Bool,
  +ehb: {hb == Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p)
    : Bool},
  +ihlo: {List.contains(~U32, ~U32.is_eq,
      S.PSet.members(p, lo, base, S.PSet.half(p),
        S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
          S.PSet.half(p), tail)), x)
    == Bool.or(
         Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+p))),
           S.PSet.mem(p, lo, S.PSet.half(p),
             U32.and(x, W.U32.mask(12n+p)))),
         List.contains(~U32, ~U32.is_eq,
           S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
             S.PSet.half(p), tail), x)) : Bool},
  +ihhi: {List.contains(~U32, ~U32.is_eq,
      S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
        S.PSet.half(p), tail), x)
    == Bool.or(
         Bool.and(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
           W.U32.diff(x, W.U32.mask(12n+p))),
           S.PSet.mem(p, hi, S.PSet.half(p),
             U32.and(x, W.U32.mask(12n+p)))),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
       S.PSet.members(1n+p, S.PBranch{lo, hi}, base,
         S.PSet.half(1n+p), tail), x)
     == Bool.or(
          Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
            S.PSet.mem(1n+p, S.PBranch{lo, hi}, S.PSet.half(1n+p),
              U32.and(x, W.U32.mask(13n+p)))),
          List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}:
  match hb:
    case True{}:
      %E.U32.sym(U32.shr(U32.shln(1, 12n+p)), U32.shln(1, 11n+p),
        Dc.U32.shr_shln_one(11n+p, lt))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.members(p, lo, base, _,
              S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
                _, tail)), x)
          == Bool.or(
               Bool.and(U32.is_eq(base,
                 W.U32.diff(x, W.U32.mask(13n+p))),
                 S.PSet.mem(p,
                   S.PSet.pick(U32.is_lt(U32.and(x,
                     W.U32.mask(13n+p)), U32.shln(1, 12n+p)), lo, hi),
                   _,
                   S.PSet.rebase(U32.is_lt(U32.and(x,
                     W.U32.mask(13n+p)), U32.shln(1, 12n+p)),
                     U32.shln(1, 12n+p),
                     U32.and(x, W.U32.mask(13n+p))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %E.Bool.sym(U32.is_lt(U32.and(x, W.U32.mask(13n+p)),
          U32.shln(1, 12n+p)),
        Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p),
        Dc.U32.is_lt_shln(U32.and(x, W.U32.mask(13n+p)), 12n+p, lt))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.members(p, lo, base, S.PSet.half(p),
              S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
                S.PSet.half(p), tail)), x)
          == Bool.or(
               Bool.and(U32.is_eq(base,
                 W.U32.diff(x, W.U32.mask(13n+p))),
                 S.PSet.mem(p, S.PSet.pick(_, lo, hi), S.PSet.half(p),
                   S.PSet.rebase(_, U32.shln(1, 12n+p),
                     U32.and(x, W.U32.mask(13n+p))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %ehb
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.members(p, lo, base, S.PSet.half(p),
              S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
                S.PSet.half(p), tail)), x)
          == Bool.or(
               Bool.and(U32.is_eq(base,
                 W.U32.diff(x, W.U32.mask(13n+p))),
                 S.PSet.mem(p, S.PSet.pick(_, lo, hi), S.PSet.half(p),
                   S.PSet.rebase(_, U32.shln(1, 12n+p),
                     U32.and(x, W.U32.mask(13n+p))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      PSet.members_contains.low(p, base, x, tail, lo, hi, lz, lt, ehb,
        ihlo, ihhi)
    case False{}:
      %E.U32.sym(U32.shr(U32.shln(1, 12n+p)), U32.shln(1, 11n+p),
        Dc.U32.shr_shln_one(11n+p, lt))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.members(p, lo, base, _,
              S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
                _, tail)), x)
          == Bool.or(
               Bool.and(U32.is_eq(base,
                 W.U32.diff(x, W.U32.mask(13n+p))),
                 S.PSet.mem(p,
                   S.PSet.pick(U32.is_lt(U32.and(x,
                     W.U32.mask(13n+p)), U32.shln(1, 12n+p)), lo, hi),
                   _,
                   S.PSet.rebase(U32.is_lt(U32.and(x,
                     W.U32.mask(13n+p)), U32.shln(1, 12n+p)),
                     U32.shln(1, 12n+p),
                     U32.and(x, W.U32.mask(13n+p))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %E.Bool.sym(U32.is_lt(U32.and(x, W.U32.mask(13n+p)),
          U32.shln(1, 12n+p)),
        Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p),
        Dc.U32.is_lt_shln(U32.and(x, W.U32.mask(13n+p)), 12n+p, lt))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.members(p, lo, base, S.PSet.half(p),
              S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
                S.PSet.half(p), tail)), x)
          == Bool.or(
               Bool.and(U32.is_eq(base,
                 W.U32.diff(x, W.U32.mask(13n+p))),
                 S.PSet.mem(p, S.PSet.pick(_, lo, hi), S.PSet.half(p),
                   S.PSet.rebase(_, U32.shln(1, 12n+p),
                     U32.and(x, W.U32.mask(13n+p))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %ehb
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.members(p, lo, base, S.PSet.half(p),
              S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
                S.PSet.half(p), tail)), x)
          == Bool.or(
               Bool.and(U32.is_eq(base,
                 W.U32.diff(x, W.U32.mask(13n+p))),
                 S.PSet.mem(p, S.PSet.pick(_, lo, hi), S.PSet.half(p),
                   S.PSet.rebase(_, U32.shln(1, 12n+p),
                     U32.and(x, W.U32.mask(13n+p))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      PSet.members_contains.high(p, base, x, tail, lo, hi, lz, lt, ehb,
        ihlo, ihhi)

# ---------------------------------------------------------------------------
# The induction.
# ---------------------------------------------------------------------------

law PSet.members_contains:
  for +d: Nat
  for +s: S.PSet
  for +base: U32
  for +x: U32
  for +tail: List<&2, U32>
  for +ok: {PSet.ok(d, s) == True{} : Bool}
  for +lz: {Sa.U32.lo_zero(base, 12n+d) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq,
     S.PSet.members(d, s, base, S.PSet.half(d), tail), x)
   == Bool.or(
        Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+d))),
          S.PSet.mem(d, s, S.PSet.half(d),
            U32.and(x, W.U32.mask(12n+d)))),
        List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}

def PSet.members_contains(d, s, base, x, tail, ok, lz, lt):
  match d:
    case 0n:
      PSet.members_contains.leaf(s, base, x, tail, ok, lz)
    case 1n+p:
      match s:
        case S.PZero{}:
          %E.Bool.sym(Bool.and(
              U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
              False{}), False{},
            Sa.Word.and_false_r(
              U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p)))))
            : {List.contains(~U32, ~U32.is_eq, tail, x)
              == Bool.or(_, List.contains(~U32, ~U32.is_eq, tail, x))
              : Bool}
          {==}
        case S.PFull{}:
          PSet.members_contains.full(p, base, x, tail, lz, lt)
        case S.PSparse{offs}:
          E.Bool.noconf({List.contains(~U32, ~U32.is_eq,
            S.PSet.members(1n+p, S.PSparse{offs}, base,
              S.PSet.half(1n+p), tail), x)
            == Bool.or(
                 Bool.and(U32.is_eq(base,
                   W.U32.diff(x, W.U32.mask(13n+p))),
                   S.PSet.mem(1n+p, S.PSparse{offs},
                     S.PSet.half(1n+p),
                     U32.and(x, W.U32.mask(13n+p)))),
                 List.contains(~U32, ~U32.is_eq, tail, x)) : Bool},
            ok)
        case S.PDense{ws}:
          E.Bool.noconf({List.contains(~U32, ~U32.is_eq,
            S.PSet.members(1n+p, S.PDense{ws}, base,
              S.PSet.half(1n+p), tail), x)
            == Bool.or(
                 Bool.and(U32.is_eq(base,
                   W.U32.diff(x, W.U32.mask(13n+p))),
                   S.PSet.mem(1n+p, S.PDense{ws}, S.PSet.half(1n+p),
                     U32.and(x, W.U32.mask(13n+p)))),
                 List.contains(~U32, ~U32.is_eq, tail, x)) : Bool},
            ok)
        case S.PBranch{lo, hi}:
          PSet.members_contains.branch(p, base, x, tail, lo, hi, lz,
            lt, Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p),
            {==},
            PSet.members_contains(p, lo, base, x,
              S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
                S.PSet.half(p), tail),
              E.Bool.and_l(PSet.ok(p, lo), PSet.ok(p, hi), ok),
              Hv.Word.lo_zero_down(32n, W.U32.word(base), 12n+p, lz),
              Dc.Nat.gt_down(32n, 11n+p, lt)),
            PSet.members_contains(p, hi,
              (base + U32.shln(1, 12n+p) : U32), x, tail,
              E.Bool.and_r(PSet.ok(p, lo), PSet.ok(p, hi), ok),
              Hv.U32.lo_zero_half_base(base, 12n+p, lz),
              Dc.Nat.gt_down(32n, 11n+p, lt)))

# ---------------------------------------------------------------------------
# At the root: the whole list, and the membership test.
# ---------------------------------------------------------------------------

law Bool.or_false_r:
  for +a: Bool
  {Bool.or(a, False{}) == a : Bool}

def Bool.or_false_r(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law Word.lo_zero_of_zero_bits:
  for +n: Nat
  for +w: Word(n)
  for +k: Nat
  for +hz: {Dc.Word.hi_zero(n, w, 0n) == True{} : Bool}
  {Sa.Word.lo_zero(n, w, k) == True{} : Bool}

def Word.lo_zero_of_zero_bits(n, w, k, hz):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              E.Bool.and_both(Bool.not(b), Sa.Word.lo_zero(p, t, j),
                E.Bool.and_l(Bool.not(b), Dc.Word.hi_zero(p, t, 0n),
                  hz),
                Word.lo_zero_of_zero_bits(p, t, j,
                  E.Bool.and_r(Bool.not(b), Dc.Word.hi_zero(p, t, 0n),
                    hz)))

law Word.and_mask_of_hi_zero:
  for +n: Nat
  for +w: Word(n)
  for +k: Nat
  for +hz: {Dc.Word.hi_zero(n, w, k) == True{} : Bool}
  {Word.and(n, w, W.Word.low_mask(n, k)) == w : Word(n)}

def Word.and_mask_of_hi_zero(n, w, k, hz):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case False{}:
              match k:
                case 0n:
                  %E.Word.sym(p, Word.and(p, t,
                      W.Word.low_mask(p, 0n)), t,
                    Word.and_mask_of_hi_zero(p, t, 0n,
                      E.Bool.and_r(Bool.not(False{}),
                        Dc.Word.hi_zero(p, t, 0n), hz)))
                    : {WCon{False{}, _} == WCon{False{}, t}
                      : Word(1n+p)}
                  {==}
                case 1n+j:
                  %E.Word.sym(p, Word.and(p, t,
                      W.Word.low_mask(p, j)), t,
                    Word.and_mask_of_hi_zero(p, t, j, hz))
                    : {WCon{False{}, _} == WCon{False{}, t}
                      : Word(1n+p)}
                  {==}
            case True{}:
              match k:
                case 0n:
                  E.Bool.noconf({Word.and(1n+p, WCon{True{}, t},
                    W.Word.low_mask(1n+p, 0n)) == WCon{True{}, t}
                    : Word(1n+p)}, hz)
                case 1n+j:
                  %E.Word.sym(p, Word.and(p, t,
                      W.Word.low_mask(p, j)), t,
                    Word.and_mask_of_hi_zero(p, t, j, hz))
                    : {WCon{True{}, _} == WCon{True{}, t}
                      : Word(1n+p)}
                  {==}

law Word.diff_mask_of_hi_zero:
  for +n: Nat
  for +w: Word(n)
  for +k: Nat
  for +hz: {Dc.Word.hi_zero(n, w, k) == True{} : Bool}
  {Word.and(n, w, Word.not(n, W.Word.low_mask(n, k)))
    == Dc.Word.zeros(n) : Word(n)}

def Word.diff_mask_of_hi_zero(n, w, k, hz):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case False{}:
              match k:
                case 0n:
                  %E.Word.sym(p, Word.and(p, t,
                      Word.not(p, W.Word.low_mask(p, 0n))),
                    Dc.Word.zeros(p),
                    Word.diff_mask_of_hi_zero(p, t, 0n,
                      E.Bool.and_r(Bool.not(False{}),
                        Dc.Word.hi_zero(p, t, 0n), hz)))
                    : {WCon{False{}, _}
                      == WCon{False{}, Dc.Word.zeros(p)}
                      : Word(1n+p)}
                  {==}
                case 1n+j:
                  %E.Word.sym(p, Word.and(p, t,
                      Word.not(p, W.Word.low_mask(p, j))),
                    Dc.Word.zeros(p),
                    Word.diff_mask_of_hi_zero(p, t, j, hz))
                    : {WCon{False{}, _}
                      == WCon{False{}, Dc.Word.zeros(p)}
                      : Word(1n+p)}
                  {==}
            case True{}:
              match k:
                case 0n:
                  E.Bool.noconf({Word.and(1n+p, WCon{True{}, t},
                    Word.not(1n+p, W.Word.low_mask(1n+p, 0n)))
                    == Dc.Word.zeros(1n+p) : Word(1n+p)}, hz)
                case 1n+j:
                  %E.Word.sym(p, Word.and(p, t,
                      Word.not(p, W.Word.low_mask(p, j))),
                    Dc.Word.zeros(p),
                    Word.diff_mask_of_hi_zero(p, t, j, hz))
                    : {WCon{False{}, _}
                      == WCon{False{}, Dc.Word.zeros(p)}
                      : Word(1n+p)}
                  {==}

law U32.and_mask_of_hi_zero:
  for +x: U32
  for +k: Nat
  for +hz: {Dc.U32.hi_zero(x, k) == True{} : Bool}
  {U32.and(x, W.U32.mask(k)) == x : U32}

def U32.and_mask_of_hi_zero(x, k, hz):
  match x:
    case U32{xw}:
      Equal.cong(Word(32n), U32, E.U32.pak,
        Word.and(32n, xw, W.Word.low_mask(32n, k)), xw,
        Word.and_mask_of_hi_zero(32n, xw, k, hz))

law U32.diff_of_hi_zero:
  for +x: U32
  for +k: Nat
  for +hz: {Dc.U32.hi_zero(x, k) == True{} : Bool}
  {W.U32.diff(x, W.U32.mask(k)) == 0 : U32}

def U32.diff_of_hi_zero(x, k, hz):
  match x:
    case U32{xw}:
      Equal.cong(Word(32n), U32, E.U32.pak,
        Word.and(32n, xw, Word.not(32n, W.Word.low_mask(32n, k))),
        Dc.Word.zeros(32n),
        Word.diff_mask_of_hi_zero(32n, xw, k, hz))

law U32.lo_zero_zero:
  for +k: Nat
  {Sa.U32.lo_zero(0, k) == True{} : Bool}

def U32.lo_zero_zero(k):
  Word.lo_zero_of_zero_bits(32n, W.U32.word(0), k, {==})

law PSet.to_list_member:
  for +d: Nat
  for +s: S.PSet
  for +x: U32
  for +ok: {PSet.ok(d, s) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, S.PSet.to_list(d, s), x)
    == S.PSet.member(d, s, x) : Bool}

def PSet.to_list_member(d, s, x, ok, lt, inr):
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      S.PSet.members(d, s, 0, S.PSet.half(d), Nil{}), x),
    Bool.or(
      Bool.and(U32.is_eq(0, W.U32.diff(x, W.U32.mask(12n+d))),
        S.PSet.mem(d, s, S.PSet.half(d),
          U32.and(x, W.U32.mask(12n+d)))),
      List.contains(~U32, ~U32.is_eq, Nil{}, x)),
    PSet.members_contains(d, s, 0, x, Nil{}, ok,
      U32.lo_zero_zero(12n+d), lt))
    : {_ == S.PSet.mem(d, s, S.PSet.half(d), x) : Bool}
  %E.U32.sym(U32.and(x, W.U32.mask(12n+d)), x,
    U32.and_mask_of_hi_zero(x, 12n+d, inr))
    : {Bool.or(
        Bool.and(U32.is_eq(0, W.U32.diff(x, W.U32.mask(12n+d))),
          S.PSet.mem(d, s, S.PSet.half(d), _)), False{})
      == S.PSet.mem(d, s, S.PSet.half(d), x) : Bool}
  %E.U32.sym(W.U32.diff(x, W.U32.mask(12n+d)), 0,
    U32.diff_of_hi_zero(x, 12n+d, inr))
    : {Bool.or(Bool.and(U32.is_eq(0, _),
        S.PSet.mem(d, s, S.PSet.half(d), x)), False{})
      == S.PSet.mem(d, s, S.PSet.half(d), x) : Bool}
  Bool.or_false_r(S.PSet.mem(d, s, S.PSet.half(d), x))
