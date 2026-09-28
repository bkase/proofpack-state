# proofs/treediff.bend -- what the fused difference walk emits, over a tree.
#
# proofs/treeenum.bend says the enumeration walk lists exactly the members of
# a set. This is the same statement for the walk that enumerates `a \\ b`
# without building it: an ordinal is on the list exactly when it is inside
# the node's interval, the node of `a` holds it, and the node of `b` does
# not.
#
# The arms are the same arms, for the same reasons -- the leaf is the fused
# leaf law under the shift law, a full node against an empty one counts down
# its whole interval, and a branch splits, with the two walks descending
# differently and the child tests saying they agree. What is new is only that
# two operands descend together, and they descend the same way, because the
# half they compare against does not depend on either of them.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./split_add.bend as Sa
import ./shift.bend as Sf
import ./leafenum.bend as Le
import ./interval.bend as It
import ./nodeenum.bend as Ne
import ./lastord.bend as Ld
import ./halves.bend as Hv
import ./maskwidth.bend as Mw
import ./childtest.bend as Ct
import ./treeenum.bend as Te
import ./validshape.bend as Vs
import ./tilefit.bend as Tf
import ./leafdiff.bend as Lf2
import ./leaffit.bend as Lf3
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# A leaf.
# ---------------------------------------------------------------------------

def PSet.diff_contains.leaf(+a: S.PSet, +b: S.PSet, +base: U32,
  +x: U32, +tail: List<&2, U32>,
  +va: {S.PSet.valid.leaf(a) == True{} : Bool},
  +vb: {S.PSet.valid.leaf(b) == True{} : Bool},
  +oka: {Le.PSet.ok.leaf(a) == True{} : Bool},
  +lz: {Sa.U32.lo_zero(base, 12n) == True{} : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
       S.PSet.diff_members(0n, a, b, base, S.PSet.half(0n), tail), x)
     == Bool.or(
          Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n))),
            Bool.and(S.PSet.mem(0n, a, S.PSet.half(0n),
              U32.and(x, W.U32.mask(12n))),
              Bool.not(S.PSet.mem(0n, b, S.PSet.half(0n),
                U32.and(x, W.U32.mask(12n)))))),
          List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}:
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      List.append(&2, U32,
        S.PSet.shift(S.PSet.leaf_diff_members(a, b), base), tail), x),
    Bool.or(List.contains(~U32, ~U32.is_eq,
        S.PSet.shift(S.PSet.leaf_diff_members(a, b), base), x),
      List.contains(~U32, ~U32.is_eq, tail, x)),
    Le.List.contains_append(
      S.PSet.shift(S.PSet.leaf_diff_members(a, b), base), tail, x))
    : {_ == Bool.or(
        Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n))),
          Bool.and(S.PSet.mem.leaf(a, U32.and(x, W.U32.mask(12n))),
            Bool.not(S.PSet.mem.leaf(b,
              U32.and(x, W.U32.mask(12n)))))),
        List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      S.PSet.shift(S.PSet.leaf_diff_members(a, b), base), x),
    Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n))),
      List.contains(~U32, ~U32.is_eq, S.PSet.leaf_diff_members(a, b),
        U32.and(x, W.U32.mask(12n)))),
    Sf.Ords.contains_shift(S.PSet.leaf_diff_members(a, b),
      Sf.Ords.head_shift_eq(S.PSet.leaf_diff_members(a, b), base, x),
      U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n))),
      Sf.Ords.head_low_eq(S.PSet.leaf_diff_members(a, b), x, 12n),
      base, x, 12n, {==}, {==}, {==},
      Lf3.Ords.all_fit_leaf_diff(a, b, oka), lz))
    : {Bool.or(_, List.contains(~U32, ~U32.is_eq, tail, x))
      == Bool.or(
        Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n))),
          Bool.and(S.PSet.mem.leaf(a, U32.and(x, W.U32.mask(12n))),
            Bool.not(S.PSet.mem.leaf(b,
              U32.and(x, W.U32.mask(12n)))))),
        List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      S.PSet.leaf_diff_members(a, b), U32.and(x, W.U32.mask(12n))),
    Bool.and(S.PSet.mem.leaf(a, U32.and(x, W.U32.mask(12n))),
      Bool.not(S.PSet.mem.leaf(b, U32.and(x, W.U32.mask(12n))))),
    Lf2.PSet.leaf_diff_members_mem(a, b,
      U32.and(x, W.U32.mask(12n)), va, vb,
      Sa.U32.hi_zero_low(x, 12n)))
    : {Bool.or(Bool.and(
        U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n))), _),
        List.contains(~U32, ~U32.is_eq, tail, x))
      == Bool.or(
        Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n))),
          Bool.and(S.PSet.mem.leaf(a, U32.and(x, W.U32.mask(12n))),
            Bool.not(S.PSet.mem.leaf(b,
              U32.and(x, W.U32.mask(12n)))))),
        List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  {==}

# ---------------------------------------------------------------------------
# The two halves of a branch, with the lists left opaque: whatever the two
# children contribute, the node contributes the half the ordinal is in.
# ---------------------------------------------------------------------------

law PSet.split_low:
  for +p: Nat
  for +base: U32
  for +x: U32
  for +tail: List<&2, U32>
  for +dlo: Bool
  for +dhi: Bool
  for +llo: List<&2, U32>
  for +lhi: List<&2, U32>
  for +lz: {Sa.U32.lo_zero(base, 13n+p) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 12n+p) == True{} : Bool}
  for +ehb: {True{} == Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)),
    12n+p) : Bool}
  for +ihlo: {List.contains(~U32, ~U32.is_eq, llo, x)
    == Bool.or(Bool.and(U32.is_eq(base,
         W.U32.diff(x, W.U32.mask(12n+p))), dlo),
         List.contains(~U32, ~U32.is_eq, lhi, x)) : Bool}
  for +ihhi: {List.contains(~U32, ~U32.is_eq, lhi, x)
    == Bool.or(Bool.and(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
         W.U32.diff(x, W.U32.mask(12n+p))), dhi),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  {List.contains(~U32, ~U32.is_eq, llo, x)
    == Bool.or(Bool.and(U32.is_eq(base,
         W.U32.diff(x, W.U32.mask(13n+p))), dlo),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}

def PSet.split_low(p, base, x, tail, dlo, dhi, llo, lhi, lz, lt, ehb,
  ihlo, ihhi):
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq, llo, x),
    Bool.or(Bool.and(U32.is_eq(base,
      W.U32.diff(x, W.U32.mask(12n+p))), dlo),
      List.contains(~U32, ~U32.is_eq, lhi, x)), ihlo)
    : {_ == Bool.or(Bool.and(U32.is_eq(base,
         W.U32.diff(x, W.U32.mask(13n+p))), dlo),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq, lhi, x),
    Bool.or(Bool.and(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
      W.U32.diff(x, W.U32.mask(12n+p))), dhi),
      List.contains(~U32, ~U32.is_eq, tail, x)), ihhi)
    : {Bool.or(Bool.and(U32.is_eq(base,
        W.U32.diff(x, W.U32.mask(12n+p))), dlo), _)
      == Bool.or(Bool.and(U32.is_eq(base,
           W.U32.diff(x, W.U32.mask(13n+p))), dlo),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+p))),
    U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
    Ct.Test.low_matches(base, 12n+p, x,
      U32.is_eq(base, W.U32.diff(x, W.U32.mask(13n+p))),
      U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+p))), lz,
      E.Bool.sym(True{},
        Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p), ehb),
      {==}, {==}))
    : {Bool.or(Bool.and(_, dlo),
        Bool.or(Bool.and(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
          W.U32.diff(x, W.U32.mask(12n+p))), dhi),
          List.contains(~U32, ~U32.is_eq, tail, x)))
      == Bool.or(Bool.and(U32.is_eq(base,
           W.U32.diff(x, W.U32.mask(13n+p))), dlo),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
      W.U32.diff(x, W.U32.mask(12n+p))), False{},
    Ct.Test.high_misses(base, 12n+p, x,
      U32.is_eq((base + U32.shln(1, 12n+p) : U32),
        W.U32.diff(x, W.U32.mask(12n+p))), lz, lt,
      E.Bool.sym(True{},
        Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p), ehb),
      {==}))
    : {Bool.or(Bool.and(U32.is_eq(base,
        W.U32.diff(x, W.U32.mask(13n+p))), dlo),
        Bool.or(Bool.and(_, dhi),
          List.contains(~U32, ~U32.is_eq, tail, x)))
      == Bool.or(Bool.and(U32.is_eq(base,
           W.U32.diff(x, W.U32.mask(13n+p))), dlo),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  {==}

law PSet.split_high:
  for +p: Nat
  for +base: U32
  for +x: U32
  for +tail: List<&2, U32>
  for +dlo: Bool
  for +dhi: Bool
  for +llo: List<&2, U32>
  for +lhi: List<&2, U32>
  for +lz: {Sa.U32.lo_zero(base, 13n+p) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 12n+p) == True{} : Bool}
  for +ehb: {False{} == Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)),
    12n+p) : Bool}
  for +ihlo: {List.contains(~U32, ~U32.is_eq, llo, x)
    == Bool.or(Bool.and(U32.is_eq(base,
         W.U32.diff(x, W.U32.mask(12n+p))), dlo),
         List.contains(~U32, ~U32.is_eq, lhi, x)) : Bool}
  for +ihhi: {List.contains(~U32, ~U32.is_eq, lhi, x)
    == Bool.or(Bool.and(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
         W.U32.diff(x, W.U32.mask(12n+p))), dhi),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  {List.contains(~U32, ~U32.is_eq, llo, x)
    == Bool.or(Bool.and(U32.is_eq(base,
         W.U32.diff(x, W.U32.mask(13n+p))), dhi),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}

def PSet.split_high(p, base, x, tail, dlo, dhi, llo, lhi, lz, lt, ehb,
  ihlo, ihhi):
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq, llo, x),
    Bool.or(Bool.and(U32.is_eq(base,
      W.U32.diff(x, W.U32.mask(12n+p))), dlo),
      List.contains(~U32, ~U32.is_eq, lhi, x)), ihlo)
    : {_ == Bool.or(Bool.and(U32.is_eq(base,
         W.U32.diff(x, W.U32.mask(13n+p))), dhi),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq, lhi, x),
    Bool.or(Bool.and(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
      W.U32.diff(x, W.U32.mask(12n+p))), dhi),
      List.contains(~U32, ~U32.is_eq, tail, x)), ihhi)
    : {Bool.or(Bool.and(U32.is_eq(base,
        W.U32.diff(x, W.U32.mask(12n+p))), dlo), _)
      == Bool.or(Bool.and(U32.is_eq(base,
           W.U32.diff(x, W.U32.mask(13n+p))), dhi),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  %E.Bool.sym(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+p))),
    False{},
    Ct.Test.low_misses(base, 12n+p, x,
      U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+p))), lz,
      E.Bool.sym(False{},
        Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p), ehb),
      {==}))
    : {Bool.or(Bool.and(_, dlo),
        Bool.or(Bool.and(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
          W.U32.diff(x, W.U32.mask(12n+p))), dhi),
          List.contains(~U32, ~U32.is_eq, tail, x)))
      == Bool.or(Bool.and(U32.is_eq(base,
           W.U32.diff(x, W.U32.mask(13n+p))), dhi),
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
    : {Bool.or(Bool.and(False{}, dlo),
        Bool.or(Bool.and(_, dhi),
          List.contains(~U32, ~U32.is_eq, tail, x)))
      == Bool.or(Bool.and(U32.is_eq(base,
           W.U32.diff(x, W.U32.mask(13n+p))), dhi),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  {==}

# ---------------------------------------------------------------------------
# A branch, either side of the half. Both operands descend the same way, so
# one dispatcher serves the branch-against-branch arm and the full-against-
# branch arm alike: a full node is its own two halves.
# ---------------------------------------------------------------------------

def PSet.diff_contains.branch(+p: Nat, +base: U32, +x: U32,
  +tail: List<&2, U32>, +al: S.PSet, +ah: S.PSet, +bl: S.PSet,
  +bh: S.PSet,
  +lz: {Sa.U32.lo_zero(base, 13n+p) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 12n+p) == True{} : Bool},
  +hb: Bool,
  +ehb: {hb == Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p)
    : Bool},
  +ihlo: {List.contains(~U32, ~U32.is_eq,
      S.PSet.diff_members(p, al, bl, base, S.PSet.half(p),
        S.PSet.diff_members(p, ah, bh,
          (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail)),
      x)
    == Bool.or(Bool.and(U32.is_eq(base,
         W.U32.diff(x, W.U32.mask(12n+p))),
         Bool.and(S.PSet.mem(p, al, S.PSet.half(p),
           U32.and(x, W.U32.mask(12n+p))),
           Bool.not(S.PSet.mem(p, bl, S.PSet.half(p),
             U32.and(x, W.U32.mask(12n+p)))))),
         List.contains(~U32, ~U32.is_eq,
           S.PSet.diff_members(p, ah, bh,
             (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail),
           x)) : Bool},
  +ihhi: {List.contains(~U32, ~U32.is_eq,
      S.PSet.diff_members(p, ah, bh,
        (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail), x)
    == Bool.or(Bool.and(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
         W.U32.diff(x, W.U32.mask(12n+p))),
         Bool.and(S.PSet.mem(p, ah, S.PSet.half(p),
           U32.and(x, W.U32.mask(12n+p))),
           Bool.not(S.PSet.mem(p, bh, S.PSet.half(p),
             U32.and(x, W.U32.mask(12n+p)))))),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
       S.PSet.diff_members(1n+p, S.PBranch{al, ah},
         S.PBranch{bl, bh}, base, S.PSet.half(1n+p), tail), x)
     == Bool.or(Bool.and(U32.is_eq(base,
          W.U32.diff(x, W.U32.mask(13n+p))),
          Bool.and(S.PSet.mem(1n+p, S.PBranch{al, ah},
            S.PSet.half(1n+p), U32.and(x, W.U32.mask(13n+p))),
            Bool.not(S.PSet.mem(1n+p, S.PBranch{bl, bh},
              S.PSet.half(1n+p),
              U32.and(x, W.U32.mask(13n+p)))))),
          List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}:
  match hb:
    case True{}:
      %E.U32.sym(U32.shr(U32.shln(1, 12n+p)), U32.shln(1, 11n+p),
        Dc.U32.shr_shln_one(11n+p, lt))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, al, bl, base, _,
              S.PSet.diff_members(p, ah, bh,
                (base + U32.shln(1, 12n+p) : U32), _, tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.and(S.PSet.mem(p,
                 S.PSet.pick(U32.is_lt(U32.and(x,
                   W.U32.mask(13n+p)), U32.shln(1, 12n+p)), al, ah),
                 _,
                 S.PSet.rebase(U32.is_lt(U32.and(x,
                   W.U32.mask(13n+p)), U32.shln(1, 12n+p)),
                   U32.shln(1, 12n+p),
                   U32.and(x, W.U32.mask(13n+p)))),
                 Bool.not(S.PSet.mem(p,
                   S.PSet.pick(U32.is_lt(U32.and(x,
                     W.U32.mask(13n+p)), U32.shln(1, 12n+p)), bl, bh),
                   _,
                   S.PSet.rebase(U32.is_lt(U32.and(x,
                     W.U32.mask(13n+p)), U32.shln(1, 12n+p)),
                     U32.shln(1, 12n+p),
                     U32.and(x, W.U32.mask(13n+p))))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %E.Bool.sym(U32.is_lt(U32.and(x, W.U32.mask(13n+p)),
          U32.shln(1, 12n+p)),
        Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p),
        Dc.U32.is_lt_shln(U32.and(x, W.U32.mask(13n+p)), 12n+p, lt))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, al, bl, base, S.PSet.half(p),
              S.PSet.diff_members(p, ah, bh,
                (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.and(S.PSet.mem(p, S.PSet.pick(_, al, ah),
                 S.PSet.half(p),
                 S.PSet.rebase(_, U32.shln(1, 12n+p),
                   U32.and(x, W.U32.mask(13n+p)))),
                 Bool.not(S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                   S.PSet.half(p),
                   S.PSet.rebase(_, U32.shln(1, 12n+p),
                     U32.and(x, W.U32.mask(13n+p))))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %ehb
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, al, bl, base, S.PSet.half(p),
              S.PSet.diff_members(p, ah, bh,
                (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.and(S.PSet.mem(p, S.PSet.pick(_, al, ah),
                 S.PSet.half(p),
                 S.PSet.rebase(_, U32.shln(1, 12n+p),
                   U32.and(x, W.U32.mask(13n+p)))),
                 Bool.not(S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                   S.PSet.half(p),
                   S.PSet.rebase(_, U32.shln(1, 12n+p),
                     U32.and(x, W.U32.mask(13n+p))))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %E.U32.sym(U32.and(x, W.U32.mask(13n+p)),
        U32.and(x, W.U32.mask(12n+p)),
        Mw.U32.mask_step(x, 12n+p,
          E.Bool.sym(True{},
            Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p),
            ehb)))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, al, bl, base, S.PSet.half(p),
              S.PSet.diff_members(p, ah, bh,
                (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.and(S.PSet.mem(p, al, S.PSet.half(p), _),
                 Bool.not(S.PSet.mem(p, bl, S.PSet.half(p), _)))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      PSet.split_low(p, base, x, tail,
        Bool.and(S.PSet.mem(p, al, S.PSet.half(p),
          U32.and(x, W.U32.mask(12n+p))),
          Bool.not(S.PSet.mem(p, bl, S.PSet.half(p),
            U32.and(x, W.U32.mask(12n+p))))),
        Bool.and(S.PSet.mem(p, ah, S.PSet.half(p),
          U32.and(x, W.U32.mask(12n+p))),
          Bool.not(S.PSet.mem(p, bh, S.PSet.half(p),
            U32.and(x, W.U32.mask(12n+p))))),
        S.PSet.diff_members(p, al, bl, base, S.PSet.half(p),
          S.PSet.diff_members(p, ah, bh,
            (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail)),
        S.PSet.diff_members(p, ah, bh,
          (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail),
        lz, lt, ehb, ihlo, ihhi)
    case False{}:
      %E.U32.sym(U32.shr(U32.shln(1, 12n+p)), U32.shln(1, 11n+p),
        Dc.U32.shr_shln_one(11n+p, lt))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, al, bl, base, _,
              S.PSet.diff_members(p, ah, bh,
                (base + U32.shln(1, 12n+p) : U32), _, tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.and(S.PSet.mem(p,
                 S.PSet.pick(U32.is_lt(U32.and(x,
                   W.U32.mask(13n+p)), U32.shln(1, 12n+p)), al, ah),
                 _,
                 S.PSet.rebase(U32.is_lt(U32.and(x,
                   W.U32.mask(13n+p)), U32.shln(1, 12n+p)),
                   U32.shln(1, 12n+p),
                   U32.and(x, W.U32.mask(13n+p)))),
                 Bool.not(S.PSet.mem(p,
                   S.PSet.pick(U32.is_lt(U32.and(x,
                     W.U32.mask(13n+p)), U32.shln(1, 12n+p)), bl, bh),
                   _,
                   S.PSet.rebase(U32.is_lt(U32.and(x,
                     W.U32.mask(13n+p)), U32.shln(1, 12n+p)),
                     U32.shln(1, 12n+p),
                     U32.and(x, W.U32.mask(13n+p))))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %E.Bool.sym(U32.is_lt(U32.and(x, W.U32.mask(13n+p)),
          U32.shln(1, 12n+p)),
        Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p),
        Dc.U32.is_lt_shln(U32.and(x, W.U32.mask(13n+p)), 12n+p, lt))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, al, bl, base, S.PSet.half(p),
              S.PSet.diff_members(p, ah, bh,
                (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.and(S.PSet.mem(p, S.PSet.pick(_, al, ah),
                 S.PSet.half(p),
                 S.PSet.rebase(_, U32.shln(1, 12n+p),
                   U32.and(x, W.U32.mask(13n+p)))),
                 Bool.not(S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                   S.PSet.half(p),
                   S.PSet.rebase(_, U32.shln(1, 12n+p),
                     U32.and(x, W.U32.mask(13n+p))))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %ehb
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, al, bl, base, S.PSet.half(p),
              S.PSet.diff_members(p, ah, bh,
                (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.and(S.PSet.mem(p, S.PSet.pick(_, al, ah),
                 S.PSet.half(p),
                 S.PSet.rebase(_, U32.shln(1, 12n+p),
                   U32.and(x, W.U32.mask(13n+p)))),
                 Bool.not(S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                   S.PSet.half(p),
                   S.PSet.rebase(_, U32.shln(1, 12n+p),
                     U32.and(x, W.U32.mask(13n+p))))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %E.U32.sym(U32.sub(U32.and(x, W.U32.mask(13n+p)),
          U32.shln(1, 12n+p)),
        U32{Dc.Word.clear(32n,
          W.U32.word(U32.and(x, W.U32.mask(13n+p))), 12n+p)},
        Dc.U32.sub_shln(U32.and(x, W.U32.mask(13n+p)), 12n+p,
          Dc.Word.bit_of_not_hi_zero(32n, 12n+p,
            W.U32.word(U32.and(x, W.U32.mask(13n+p))),
            Sa.U32.hi_zero_low(x, 13n+p),
            E.Bool.sym(False{},
              Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p),
              ehb))))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, al, bl, base, S.PSet.half(p),
              S.PSet.diff_members(p, ah, bh,
                (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.and(S.PSet.mem(p, ah, S.PSet.half(p), _),
                 Bool.not(S.PSet.mem(p, bh, S.PSet.half(p), _)))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %E.U32.sym(U32{Dc.Word.clear(32n,
          W.U32.word(U32.and(x, W.U32.mask(13n+p))), 12n+p)},
        U32.and(x, W.U32.mask(12n+p)), Mw.U32.clear_mask(x, 12n+p))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, al, bl, base, S.PSet.half(p),
              S.PSet.diff_members(p, ah, bh,
                (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.and(S.PSet.mem(p, ah, S.PSet.half(p), _),
                 Bool.not(S.PSet.mem(p, bh, S.PSet.half(p), _)))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      PSet.split_high(p, base, x, tail,
        Bool.and(S.PSet.mem(p, al, S.PSet.half(p),
          U32.and(x, W.U32.mask(12n+p))),
          Bool.not(S.PSet.mem(p, bl, S.PSet.half(p),
            U32.and(x, W.U32.mask(12n+p))))),
        Bool.and(S.PSet.mem(p, ah, S.PSet.half(p),
          U32.and(x, W.U32.mask(12n+p))),
          Bool.not(S.PSet.mem(p, bh, S.PSet.half(p),
            U32.and(x, W.U32.mask(12n+p))))),
        S.PSet.diff_members(p, al, bl, base, S.PSet.half(p),
          S.PSet.diff_members(p, ah, bh,
            (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail)),
        S.PSet.diff_members(p, ah, bh,
          (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail),
        lz, lt, ehb, ihlo, ihhi)


def PSet.ih_full(+p: Nat, +s: S.PSet, +nb: U32, +x: U32,
  +tail: List<&2, U32>, +llo: List<&2, U32>,
  +ih: {List.contains(~U32, ~U32.is_eq, llo, x)
    == Bool.or(Bool.and(U32.is_eq(nb,
         W.U32.diff(x, W.U32.mask(12n+p))),
         Bool.and(S.PSet.mem(p, S.PFull{}, S.PSet.half(p),
           U32.and(x, W.U32.mask(12n+p))),
           Bool.not(S.PSet.mem(p, s, S.PSet.half(p),
             U32.and(x, W.U32.mask(12n+p)))))),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool})
  -> {List.contains(~U32, ~U32.is_eq, llo, x)
     == Bool.or(Bool.and(U32.is_eq(nb,
          W.U32.diff(x, W.U32.mask(12n+p))),
          Bool.not(S.PSet.mem(p, s, S.PSet.half(p),
            U32.and(x, W.U32.mask(12n+p))))),
          List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}:
  %Vs.PSet.mem_full(p, S.PSet.half(p),
    U32.and(x, W.U32.mask(12n+p)))
    : {List.contains(~U32, ~U32.is_eq, llo, x)
      == Bool.or(Bool.and(U32.is_eq(nb,
           W.U32.diff(x, W.U32.mask(12n+p))),
           Bool.and(_,
             Bool.not(S.PSet.mem(p, s, S.PSet.half(p),
               U32.and(x, W.U32.mask(12n+p)))))),
           List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
  ih

def PSet.diff_contains.fbranch(+p: Nat, +base: U32, +x: U32,
  +tail: List<&2, U32>, +bl: S.PSet, +bh: S.PSet,
  +lz: {Sa.U32.lo_zero(base, 13n+p) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 12n+p) == True{} : Bool},
  +hb: Bool,
  +ehb: {hb == Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p)
    : Bool},
  +ihlo: {List.contains(~U32, ~U32.is_eq,
      S.PSet.diff_members(p, S.PFull{}, bl, base, S.PSet.half(p),
        S.PSet.diff_members(p, S.PFull{}, bh,
          (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail)),
      x)
    == Bool.or(Bool.and(U32.is_eq(base,
         W.U32.diff(x, W.U32.mask(12n+p))),
         Bool.not(S.PSet.mem(p, bl, S.PSet.half(p),
           U32.and(x, W.U32.mask(12n+p))))),
         List.contains(~U32, ~U32.is_eq,
           S.PSet.diff_members(p, S.PFull{}, bh,
             (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail),
           x)) : Bool},
  +ihhi: {List.contains(~U32, ~U32.is_eq,
      S.PSet.diff_members(p, S.PFull{}, bh,
        (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail), x)
    == Bool.or(Bool.and(U32.is_eq((base + U32.shln(1, 12n+p) : U32),
         W.U32.diff(x, W.U32.mask(12n+p))),
         Bool.not(S.PSet.mem(p, bh, S.PSet.half(p),
           U32.and(x, W.U32.mask(12n+p))))),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
       S.PSet.diff_members(1n+p, S.PFull{},
         S.PBranch{bl, bh}, base, S.PSet.half(1n+p), tail), x)
     == Bool.or(Bool.and(U32.is_eq(base,
          W.U32.diff(x, W.U32.mask(13n+p))),
          Bool.not(S.PSet.mem(1n+p, S.PBranch{bl, bh},
            S.PSet.half(1n+p),
            U32.and(x, W.U32.mask(13n+p))))),
          List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}:
  match hb:
    case True{}:
      %E.U32.sym(U32.shr(U32.shln(1, 12n+p)), U32.shln(1, 11n+p),
        Dc.U32.shr_shln_one(11n+p, lt))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, S.PFull{}, bl, base, _,
              S.PSet.diff_members(p, S.PFull{}, bh,
                (base + U32.shln(1, 12n+p) : U32), _, tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.not(S.PSet.mem(p,
                 S.PSet.pick(U32.is_lt(U32.and(x,
                   W.U32.mask(13n+p)), U32.shln(1, 12n+p)), bl, bh),
                 _,
                 S.PSet.rebase(U32.is_lt(U32.and(x,
                   W.U32.mask(13n+p)), U32.shln(1, 12n+p)),
                   U32.shln(1, 12n+p),
                   U32.and(x, W.U32.mask(13n+p)))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %E.Bool.sym(U32.is_lt(U32.and(x, W.U32.mask(13n+p)),
          U32.shln(1, 12n+p)),
        Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p),
        Dc.U32.is_lt_shln(U32.and(x, W.U32.mask(13n+p)), 12n+p, lt))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, S.PFull{}, bl, base, S.PSet.half(p),
              S.PSet.diff_members(p, S.PFull{}, bh,
                (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.not(S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                 S.PSet.half(p),
                 S.PSet.rebase(_, U32.shln(1, 12n+p),
                   U32.and(x, W.U32.mask(13n+p)))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %ehb
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, S.PFull{}, bl, base, S.PSet.half(p),
              S.PSet.diff_members(p, S.PFull{}, bh,
                (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.not(S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                 S.PSet.half(p),
                 S.PSet.rebase(_, U32.shln(1, 12n+p),
                   U32.and(x, W.U32.mask(13n+p)))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %E.U32.sym(U32.and(x, W.U32.mask(13n+p)),
        U32.and(x, W.U32.mask(12n+p)),
        Mw.U32.mask_step(x, 12n+p,
          E.Bool.sym(True{},
            Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p),
            ehb)))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, S.PFull{}, bl, base, S.PSet.half(p),
              S.PSet.diff_members(p, S.PFull{}, bh,
                (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.not(S.PSet.mem(p, bl, S.PSet.half(p), _))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      PSet.split_low(p, base, x, tail,
        Bool.not(S.PSet.mem(p, bl, S.PSet.half(p),
          U32.and(x, W.U32.mask(12n+p)))),
        Bool.not(S.PSet.mem(p, bh, S.PSet.half(p),
          U32.and(x, W.U32.mask(12n+p)))),
        S.PSet.diff_members(p, S.PFull{}, bl, base, S.PSet.half(p),
          S.PSet.diff_members(p, S.PFull{}, bh,
            (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail)),
        S.PSet.diff_members(p, S.PFull{}, bh,
          (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail),
        lz, lt, ehb, ihlo, ihhi)
    case False{}:
      %E.U32.sym(U32.shr(U32.shln(1, 12n+p)), U32.shln(1, 11n+p),
        Dc.U32.shr_shln_one(11n+p, lt))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, S.PFull{}, bl, base, _,
              S.PSet.diff_members(p, S.PFull{}, bh,
                (base + U32.shln(1, 12n+p) : U32), _, tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.not(S.PSet.mem(p,
                 S.PSet.pick(U32.is_lt(U32.and(x,
                   W.U32.mask(13n+p)), U32.shln(1, 12n+p)), bl, bh),
                 _,
                 S.PSet.rebase(U32.is_lt(U32.and(x,
                   W.U32.mask(13n+p)), U32.shln(1, 12n+p)),
                   U32.shln(1, 12n+p),
                   U32.and(x, W.U32.mask(13n+p)))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %E.Bool.sym(U32.is_lt(U32.and(x, W.U32.mask(13n+p)),
          U32.shln(1, 12n+p)),
        Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p),
        Dc.U32.is_lt_shln(U32.and(x, W.U32.mask(13n+p)), 12n+p, lt))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, S.PFull{}, bl, base, S.PSet.half(p),
              S.PSet.diff_members(p, S.PFull{}, bh,
                (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.not(S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                 S.PSet.half(p),
                 S.PSet.rebase(_, U32.shln(1, 12n+p),
                   U32.and(x, W.U32.mask(13n+p)))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %ehb
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, S.PFull{}, bl, base, S.PSet.half(p),
              S.PSet.diff_members(p, S.PFull{}, bh,
                (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.not(S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                 S.PSet.half(p),
                 S.PSet.rebase(_, U32.shln(1, 12n+p),
                   U32.and(x, W.U32.mask(13n+p)))))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %E.U32.sym(U32.sub(U32.and(x, W.U32.mask(13n+p)),
          U32.shln(1, 12n+p)),
        U32{Dc.Word.clear(32n,
          W.U32.word(U32.and(x, W.U32.mask(13n+p))), 12n+p)},
        Dc.U32.sub_shln(U32.and(x, W.U32.mask(13n+p)), 12n+p,
          Dc.Word.bit_of_not_hi_zero(32n, 12n+p,
            W.U32.word(U32.and(x, W.U32.mask(13n+p))),
            Sa.U32.hi_zero_low(x, 13n+p),
            E.Bool.sym(False{},
              Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p),
              ehb))))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, S.PFull{}, bl, base, S.PSet.half(p),
              S.PSet.diff_members(p, S.PFull{}, bh,
                (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.not(S.PSet.mem(p, bh, S.PSet.half(p), _))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      %E.U32.sym(U32{Dc.Word.clear(32n,
          W.U32.word(U32.and(x, W.U32.mask(13n+p))), 12n+p)},
        U32.and(x, W.U32.mask(12n+p)), Mw.U32.clear_mask(x, 12n+p))
        : {List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(p, S.PFull{}, bl, base, S.PSet.half(p),
              S.PSet.diff_members(p, S.PFull{}, bh,
                (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                tail)), x)
          == Bool.or(Bool.and(U32.is_eq(base,
               W.U32.diff(x, W.U32.mask(13n+p))),
               Bool.not(S.PSet.mem(p, bh, S.PSet.half(p), _))),
               List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}
      PSet.split_high(p, base, x, tail,
        Bool.not(S.PSet.mem(p, bl, S.PSet.half(p),
          U32.and(x, W.U32.mask(12n+p)))),
        Bool.not(S.PSet.mem(p, bh, S.PSet.half(p),
          U32.and(x, W.U32.mask(12n+p)))),
        S.PSet.diff_members(p, S.PFull{}, bl, base, S.PSet.half(p),
          S.PSet.diff_members(p, S.PFull{}, bh,
            (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail)),
        S.PSet.diff_members(p, S.PFull{}, bh,
          (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail),
        lz, lt, ehb, ihlo, ihhi)


# ---------------------------------------------------------------------------
# The induction.
# ---------------------------------------------------------------------------

law PSet.diff_members_contains:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +base: U32
  for +x: U32
  for +tail: List<&2, U32>
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lz: {Sa.U32.lo_zero(base, 12n+d) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq,
     S.PSet.diff_members(d, a, b, base, S.PSet.half(d), tail), x)
   == Bool.or(
        Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(12n+d))),
          Bool.and(S.PSet.mem(d, a, S.PSet.half(d),
            U32.and(x, W.U32.mask(12n+d))),
            Bool.not(S.PSet.mem(d, b, S.PSet.half(d),
              U32.and(x, W.U32.mask(12n+d)))))),
        List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}

def PSet.diff_members_contains(d, a, b, base, x, tail, va, vb, lz,
  lt):
  match d:
    case 0n:
      PSet.diff_contains.leaf(a, b, base, x, tail, va, vb,
        E.Bool.and_l(Le.PSet.ok.leaf(a), Te.PSet.fits.leaf(a),
          Vs.PSet.ok_leaf_of_valid(a, va)), lz)
    case 1n+p:
      match a:
        case S.PSparse{o}:
          E.Bool.noconf({List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(1n+p, S.PSparse{o}, b, base,
              S.PSet.half(1n+p), tail), x)
            == Bool.or(Bool.and(U32.is_eq(base,
                 W.U32.diff(x, W.U32.mask(13n+p))),
                 Bool.and(S.PSet.mem(1n+p, S.PSparse{o},
                   S.PSet.half(1n+p),
                   U32.and(x, W.U32.mask(13n+p))),
                   Bool.not(S.PSet.mem(1n+p, b, S.PSet.half(1n+p),
                     U32.and(x, W.U32.mask(13n+p)))))),
                 List.contains(~U32, ~U32.is_eq, tail, x))
            : Bool}, va)
        case S.PDense{w}:
          E.Bool.noconf({List.contains(~U32, ~U32.is_eq,
            S.PSet.diff_members(1n+p, S.PDense{w}, b, base,
              S.PSet.half(1n+p), tail), x)
            == Bool.or(Bool.and(U32.is_eq(base,
                 W.U32.diff(x, W.U32.mask(13n+p))),
                 Bool.and(S.PSet.mem(1n+p, S.PDense{w},
                   S.PSet.half(1n+p),
                   U32.and(x, W.U32.mask(13n+p))),
                   Bool.not(S.PSet.mem(1n+p, b, S.PSet.half(1n+p),
                     U32.and(x, W.U32.mask(13n+p)))))),
                 List.contains(~U32, ~U32.is_eq, tail, x))
            : Bool}, va)
        case S.PZero{}:
          %E.Bool.sym(Bool.and(U32.is_eq(base,
              W.U32.diff(x, W.U32.mask(13n+p))), False{}), False{},
            Sa.Word.and_false_r(U32.is_eq(base,
              W.U32.diff(x, W.U32.mask(13n+p)))))
            : {List.contains(~U32, ~U32.is_eq, tail, x)
              == Bool.or(_, List.contains(~U32, ~U32.is_eq, tail, x))
              : Bool}
          {==}
        case S.PFull{}:
          match b:
            case S.PZero{}:
              Te.PSet.members_contains.full(p, base, x, tail, lz, lt)
            case S.PSparse{o}:
              E.Bool.noconf({List.contains(~U32, ~U32.is_eq,
                S.PSet.diff_members(1n+p, S.PFull{}, S.PSparse{o}, base,
                  S.PSet.half(1n+p), tail), x)
                == Bool.or(Bool.and(U32.is_eq(base,
                     W.U32.diff(x, W.U32.mask(13n+p))),
                     Bool.and(True{},
                       Bool.not(S.PSet.mem(1n+p, S.PSparse{o},
                         S.PSet.half(1n+p),
                         U32.and(x, W.U32.mask(13n+p)))))),
                     List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}, vb)
            case S.PDense{w}:
              E.Bool.noconf({List.contains(~U32, ~U32.is_eq,
                S.PSet.diff_members(1n+p, S.PFull{}, S.PDense{w}, base,
                  S.PSet.half(1n+p), tail), x)
                == Bool.or(Bool.and(U32.is_eq(base,
                     W.U32.diff(x, W.U32.mask(13n+p))),
                     Bool.and(True{},
                       Bool.not(S.PSet.mem(1n+p, S.PDense{w},
                         S.PSet.half(1n+p),
                         U32.and(x, W.U32.mask(13n+p)))))),
                     List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}, vb)
            case S.PFull{}:
              %E.Bool.sym(Bool.and(U32.is_eq(base,
                  W.U32.diff(x, W.U32.mask(13n+p))), False{}), False{},
                Sa.Word.and_false_r(U32.is_eq(base,
                  W.U32.diff(x, W.U32.mask(13n+p)))))
                : {List.contains(~U32, ~U32.is_eq, tail, x)
                  == Bool.or(_, List.contains(~U32, ~U32.is_eq, tail, x))
                  : Bool}
              {==}
            case S.PBranch{bl, bh}:
              PSet.diff_contains.fbranch(p, base, x, tail, bl, bh,
                lz, lt,
                Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p), {==},
                PSet.ih_full(p, bl, base, x,
                  S.PSet.diff_members(p, S.PFull{}, bh,
                    (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                    tail),
                  S.PSet.diff_members(p, S.PFull{}, bl, base,
                    S.PSet.half(p),
                    S.PSet.diff_members(p, S.PFull{}, bh,
                      (base + U32.shln(1, 12n+p) : U32),
                      S.PSet.half(p), tail)),
                PSet.diff_members_contains(p, S.PFull{}, bl, base, x,
                  S.PSet.diff_members(p, S.PFull{}, bh,
                    (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail),
                  Vs.PSet.valid_full(p),
                  E.Bool.and_l(S.PSet.valid(p, bl, True{}),
                    S.PSet.valid(p, bh, True{}),
                    Vs.PSet.both_of_branch(p, bl, bh, vb)),
                  Hv.Word.lo_zero_down(32n, W.U32.word(base), 12n+p, lz),
                  Dc.Nat.gt_down(32n, 11n+p, lt))),
                PSet.ih_full(p, bh, (base + U32.shln(1, 12n+p) : U32),
                  x, tail,
                  S.PSet.diff_members(p, S.PFull{}, bh,
                    (base + U32.shln(1, 12n+p) : U32),
                    S.PSet.half(p), tail),
                PSet.diff_members_contains(p, S.PFull{}, bh,
                  (base + U32.shln(1, 12n+p) : U32), x, tail,
                  Vs.PSet.valid_full(p),
                  E.Bool.and_r(S.PSet.valid(p, bl, True{}),
                    S.PSet.valid(p, bh, True{}),
                    Vs.PSet.both_of_branch(p, bl, bh, vb)),
                  Hv.U32.lo_zero_half_base(base, 12n+p, lz),
                  Dc.Nat.gt_down(32n, 11n+p, lt))))
        case S.PBranch{al, ah}:
          match b:
            case S.PZero{}:
              %E.Bool.sym(Bool.and(S.PSet.mem(1n+p,
                  S.PBranch{al, ah}, S.PSet.half(1n+p),
                  U32.and(x, W.U32.mask(13n+p))), True{}),
                S.PSet.mem(1n+p, S.PBranch{al, ah},
                  S.PSet.half(1n+p), U32.and(x, W.U32.mask(13n+p))),
                Te.Bool.and_true_r(S.PSet.mem(1n+p,
                  S.PBranch{al, ah}, S.PSet.half(1n+p),
                  U32.and(x, W.U32.mask(13n+p)))))
                : {List.contains(~U32, ~U32.is_eq,
                    S.PSet.members(1n+p, S.PBranch{al, ah}, base,
                      S.PSet.half(1n+p), tail), x)
                  == Bool.or(Bool.and(U32.is_eq(base,
                       W.U32.diff(x, W.U32.mask(13n+p))), _),
                       List.contains(~U32, ~U32.is_eq, tail, x))
                  : Bool}
              Te.PSet.members_contains(1n+p, S.PBranch{al, ah}, base,
                x, tail,
                Vs.PSet.ok_of_valid(1n+p, S.PBranch{al, ah}, va), lz,
                lt)
            case S.PSparse{o}:
              E.Bool.noconf({List.contains(~U32, ~U32.is_eq,
                S.PSet.diff_members(1n+p, S.PBranch{al, ah},
                  S.PSparse{o}, base, S.PSet.half(1n+p), tail), x)
                == Bool.or(Bool.and(U32.is_eq(base,
                     W.U32.diff(x, W.U32.mask(13n+p))),
                     Bool.and(S.PSet.mem(1n+p, S.PBranch{al, ah},
                       S.PSet.half(1n+p),
                       U32.and(x, W.U32.mask(13n+p))),
                       Bool.not(S.PSet.mem(1n+p, S.PSparse{o},
                         S.PSet.half(1n+p),
                         U32.and(x, W.U32.mask(13n+p)))))),
                     List.contains(~U32, ~U32.is_eq, tail, x))
                : Bool}, vb)
            case S.PDense{w}:
              E.Bool.noconf({List.contains(~U32, ~U32.is_eq,
                S.PSet.diff_members(1n+p, S.PBranch{al, ah},
                  S.PDense{w}, base, S.PSet.half(1n+p), tail), x)
                == Bool.or(Bool.and(U32.is_eq(base,
                     W.U32.diff(x, W.U32.mask(13n+p))),
                     Bool.and(S.PSet.mem(1n+p, S.PBranch{al, ah},
                       S.PSet.half(1n+p),
                       U32.and(x, W.U32.mask(13n+p))),
                       Bool.not(S.PSet.mem(1n+p, S.PDense{w},
                         S.PSet.half(1n+p),
                         U32.and(x, W.U32.mask(13n+p)))))),
                     List.contains(~U32, ~U32.is_eq, tail, x))
                : Bool}, vb)
            case S.PFull{}:
              %E.Bool.sym(Bool.and(S.PSet.mem(1n+p,
                  S.PBranch{al, ah}, S.PSet.half(1n+p),
                  U32.and(x, W.U32.mask(13n+p))), False{}), False{},
                Sa.Word.and_false_r(S.PSet.mem(1n+p,
                  S.PBranch{al, ah}, S.PSet.half(1n+p),
                  U32.and(x, W.U32.mask(13n+p)))))
                : {List.contains(~U32, ~U32.is_eq, tail, x)
                  == Bool.or(Bool.and(U32.is_eq(base,
                       W.U32.diff(x, W.U32.mask(13n+p))), _),
                       List.contains(~U32, ~U32.is_eq, tail, x))
                  : Bool}
              %E.Bool.sym(Bool.and(U32.is_eq(base,
                  W.U32.diff(x, W.U32.mask(13n+p))), False{}),
                False{},
                Sa.Word.and_false_r(U32.is_eq(base,
                  W.U32.diff(x, W.U32.mask(13n+p)))))
                : {List.contains(~U32, ~U32.is_eq, tail, x)
                  == Bool.or(_,
                       List.contains(~U32, ~U32.is_eq, tail, x))
                  : Bool}
              {==}
            case S.PBranch{bl, bh}:
              PSet.diff_contains.branch(p, base, x, tail, al, ah, bl,
                bh, lz, lt,
                Dc.U32.hi_zero(U32.and(x, W.U32.mask(13n+p)), 12n+p),
                {==},
                PSet.diff_members_contains(p, al, bl, base, x,
                  S.PSet.diff_members(p, ah, bh,
                    (base + U32.shln(1, 12n+p) : U32),
                    S.PSet.half(p), tail),
                  E.Bool.and_l(S.PSet.valid(p, al, True{}),
                    S.PSet.valid(p, ah, True{}),
                    Vs.PSet.both_of_branch(p, al, ah, va)),
                  E.Bool.and_l(S.PSet.valid(p, bl, True{}),
                    S.PSet.valid(p, bh, True{}),
                    Vs.PSet.both_of_branch(p, bl, bh, vb)),
                  Hv.Word.lo_zero_down(32n, W.U32.word(base), 12n+p,
                    lz),
                  Dc.Nat.gt_down(32n, 11n+p, lt)),
                PSet.diff_members_contains(p, ah, bh,
                  (base + U32.shln(1, 12n+p) : U32), x, tail,
                  E.Bool.and_r(S.PSet.valid(p, al, True{}),
                    S.PSet.valid(p, ah, True{}),
                    Vs.PSet.both_of_branch(p, al, ah, va)),
                  E.Bool.and_r(S.PSet.valid(p, bl, True{}),
                    S.PSet.valid(p, bh, True{}),
                    Vs.PSet.both_of_branch(p, bl, bh, vb)),
                  Hv.U32.lo_zero_half_base(base, 12n+p, lz),
                  Dc.Nat.gt_down(32n, 11n+p, lt)))
