# proofs/ascdiffwalk.bend -- the fused difference enumeration ascends.
#
# `PSet.diff_members` walks two trees together and emits the members of
# `a \ b` without building `a \ b`. proofs/fusedlen.bend proves it emits
# exactly those; this proves the list it emits still ascends, which is what
# makes its length a cardinality and what makes it a function of its members.
#
# The shape is proofs/ascend.bend's `Ords.asc_walk`, arm for arm: the same
# invariant (the list ascends *and* everything on it is at or above the node's
# base), the same leaf step through `Ords.asc_append`, the same full-node step
# through `PSet.range`, and the same branch step. Several arms of the fused
# walk fall back to the plain walk -- an operand that is `PZero` or above the
# leaf level short-circuits -- and those reuse `Ords.asc_walk` itself rather
# than repeating it.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./split_add.bend as Sa
import ./orderlist.bend as Ol
import ./childtest.bend as Ct2
import ./halves.bend as Hv
import ./ascend.bend as As
import ./ascdiff.bend as Ad
import ./leaffit.bend as Lft
import ./treeenum.bend as Te
import ./validshape.bend as Vs
import ./leafenum.bend as Le
import ./leaf.bend as Lf
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/set.bend as S

def Ords.asc_diff_walk.leaf(+a: S.PSet, +b: S.PSet, +base: U32,
  +tail: List<&2, U32>,
  +va: {S.PSet.valid(0n, a, True{}) == True{} : Bool},
  +vb: {S.PSet.valid(0n, b, True{}) == True{} : Bool},
  +lb: {Sa.U32.lo_zero(base, 12n) == True{} : Bool},
  +at: {Ol.Ords.asc(tail) == True{} : Bool},
  +lw: {As.Ords.lower_all(Nat.add(U32.to_nat(base),
    Dc.Nat.pow2(12n)), tail) == True{} : Bool})
  -> {Bool.and(Ol.Ords.asc(List.append(&2, U32,
      S.PSet.shift(S.PSet.leaf_diff_members(a, b), base), tail)),
    As.Ords.lower_all(U32.to_nat(base), List.append(&2, U32,
      S.PSet.shift(S.PSet.leaf_diff_members(a, b), base), tail)))
    == True{} : Bool}:
  E.Bool.and_both(
    Ol.Ords.asc(List.append(&2, U32,
      S.PSet.shift(S.PSet.leaf_diff_members(a, b), base), tail)),
    As.Ords.lower_all(U32.to_nat(base), List.append(&2, U32,
      S.PSet.shift(S.PSet.leaf_diff_members(a, b), base), tail)),
    As.Ords.asc_append(
      S.PSet.shift(S.PSet.leaf_diff_members(a, b), base), tail,
      Nat.add(U32.to_nat(base), Dc.Nat.pow2(12n)),
      As.Ords.asc_shift(S.PSet.leaf_diff_members(a, b), base, 12n,
        Ad.Ords.asc_leaf_diff_members(a, b, va, vb),
        Lft.Ords.all_fit_leaf_diff(a, b,
          E.Bool.and_l(Le.PSet.ok.leaf(a), Te.PSet.fits.leaf(a),
            Vs.PSet.ok_leaf_of_valid(a, va))), lb),
      at,
      As.Ords.upper_shift(S.PSet.leaf_diff_members(a, b), base, 12n,
        Lft.Ords.all_fit_leaf_diff(a, b,
          E.Bool.and_l(Le.PSet.ok.leaf(a), Te.PSet.fits.leaf(a),
            Vs.PSet.ok_leaf_of_valid(a, va))), lb),
      lw),
    As.Ords.lower_append(
      S.PSet.shift(S.PSet.leaf_diff_members(a, b), base), tail,
      U32.to_nat(base),
      As.Ords.lower_shift(S.PSet.leaf_diff_members(a, b), base, 12n,
        Lft.Ords.all_fit_leaf_diff(a, b,
          E.Bool.and_l(Le.PSet.ok.leaf(a), Te.PSet.fits.leaf(a),
            Vs.PSet.ok_leaf_of_valid(a, va))), lb),
      As.Ords.lower_down(U32.to_nat(base),
        Nat.add(U32.to_nat(base), Dc.Nat.pow2(12n)), tail,
        Ct2.Nat.le_add_right(U32.to_nat(base), Dc.Nat.pow2(12n)),
        lw)))

# An arm that answers the tail unchanged.
def Ords.asc_diff_walk.stop(+p: Nat, +base: U32,
  +tail: List<&2, U32>,
  +at: {Ol.Ords.asc(tail) == True{} : Bool},
  +lw: {As.Ords.lower_all(Nat.add(U32.to_nat(base),
    Dc.Nat.pow2(13n+p)), tail) == True{} : Bool})
  -> {Bool.and(Ol.Ords.asc(tail),
    As.Ords.lower_all(U32.to_nat(base), tail)) == True{} : Bool}:
  E.Bool.and_both(Ol.Ords.asc(tail),
    As.Ords.lower_all(U32.to_nat(base), tail), at,
    As.Ords.lower_down(U32.to_nat(base),
      Nat.add(U32.to_nat(base), Dc.Nat.pow2(13n+p)), tail,
      Ct2.Nat.le_add_right(U32.to_nat(base), Dc.Nat.pow2(13n+p)),
      lw))

def PSet.valid_full(+p: Nat)
  -> {S.PSet.valid(p, S.PFull{}, True{}) == True{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      {==}

# The branch step: the walk descends with the half-width shifted down, and
# `PSet.half(p)` is what that shift is.
def Ords.asc_diff_walk.branch(+p: Nat, +al: S.PSet, +ah: S.PSet,
  +bl: S.PSet, +bh: S.PSet, +base: U32, +tail: List<&2, U32>,
  +dok: {C.Nat.gt(32n, 12n+p) == True{} : Bool},
  +ih: {Bool.and(Ol.Ords.asc(S.PSet.diff_members(p, al, bl, base,
      S.PSet.half(p), S.PSet.diff_members(p, ah, bh,
        (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail))),
    As.Ords.lower_all(U32.to_nat(base),
      S.PSet.diff_members(p, al, bl, base, S.PSet.half(p),
        S.PSet.diff_members(p, ah, bh,
          (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail))))
    == True{} : Bool})
  -> {Bool.and(Ol.Ords.asc(S.PSet.diff_members(p, al, bl, base,
      U32.shr(S.PSet.half(1n+p)), S.PSet.diff_members(p, ah, bh,
        (base + S.PSet.half(1n+p) : U32),
        U32.shr(S.PSet.half(1n+p)), tail))),
    As.Ords.lower_all(U32.to_nat(base),
      S.PSet.diff_members(p, al, bl, base,
        U32.shr(S.PSet.half(1n+p)), S.PSet.diff_members(p, ah, bh,
          (base + S.PSet.half(1n+p) : U32),
          U32.shr(S.PSet.half(1n+p)), tail))))
    == True{} : Bool}:
  %E.U32.sym(U32.shr(S.PSet.half(1n+p)), S.PSet.half(p),
    Lf.PSet.half_shr(p, S.PSet.half(1n+p), {==}, dok))
    : {Bool.and(Ol.Ords.asc(S.PSet.diff_members(p, al, bl, base, _,
        S.PSet.diff_members(p, ah, bh,
          (base + S.PSet.half(1n+p) : U32), _, tail))),
      As.Ords.lower_all(U32.to_nat(base),
        S.PSet.diff_members(p, al, bl, base, _,
          S.PSet.diff_members(p, ah, bh,
            (base + S.PSet.half(1n+p) : U32), _, tail))))
      == True{} : Bool}
  ih

law Ords.asc_diff_walk:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +base: U32
  for +tail: List<&2, U32>
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lb: {Sa.U32.lo_zero(base, 12n+d) == True{} : Bool}
  for +dok: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +at: {Ol.Ords.asc(tail) == True{} : Bool}
  for +lw: {As.Ords.lower_all(Nat.add(U32.to_nat(base),
    Dc.Nat.pow2(12n+d)), tail) == True{} : Bool}
  {Bool.and(Ol.Ords.asc(
      S.PSet.diff_members(d, a, b, base, S.PSet.half(d), tail)),
    As.Ords.lower_all(U32.to_nat(base),
      S.PSet.diff_members(d, a, b, base, S.PSet.half(d), tail)))
    == True{} : Bool}

def Ords.asc_diff_walk(d, a, b, base, tail, va, vb, lb, dok, at, lw):
  match d:
    case 0n:
      Ords.asc_diff_walk.leaf(a, b, base, tail, va, vb, lb, at, lw)
    case 1n+p:
      match a:
        case S.PZero{}:
          Ords.asc_diff_walk.stop(p, base, tail, at, lw)
        case S.PSparse{offs}:
          Ords.asc_diff_walk.stop(p, base, tail, at, lw)
        case S.PDense{ws}:
          Ords.asc_diff_walk.stop(p, base, tail, at, lw)
        case S.PFull{}:
          match b:
            case S.PZero{}:
              As.Ords.asc_walk.full(p, base, tail, lb, dok, at, lw)
            case S.PFull{}:
              Ords.asc_diff_walk.stop(p, base, tail, at, lw)
            case S.PSparse{o}:
              As.Ords.asc_walk.full(p, base, tail, lb, dok, at, lw)
            case S.PDense{w}:
              As.Ords.asc_walk.full(p, base, tail, lb, dok, at, lw)
            case S.PBranch{bl, bh}:
              Ords.asc_diff_walk.branch(p, S.PFull{}, S.PFull{}, bl, bh, base, tail, dok,
                Ords.asc_diff_walk(p, S.PFull{}, bl, base,
                  S.PSet.diff_members(p, S.PFull{}, bh,
                (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail),
                  PSet.valid_full(p),
                  E.Bool.and_l(S.PSet.valid(p, bl, True{}),
      S.PSet.valid(p, bh, True{}),
      Vs.PSet.both_of_branch(p, bl, bh, vb)),
                  Hv.Word.lo_zero_down(32n, W.U32.word(base), 12n+p, lb),
                  Dc.Nat.gt_down(32n, 11n+p, dok),
                  E.Bool.and_l(Ol.Ords.asc(S.PSet.diff_members(p, S.PFull{}, bh,
                (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail)),
                    As.Ords.lower_all(
                      U32.to_nat((base + S.PSet.half(1n+p) : U32)),
                      S.PSet.diff_members(p, S.PFull{}, bh,
                (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail)),
                    Ords.asc_diff_walk(p, S.PFull{}, bh,
                (base + S.PSet.half(1n+p) : U32), tail,
                PSet.valid_full(p),
                E.Bool.and_r(S.PSet.valid(p, bl, True{}),
    S.PSet.valid(p, bh, True{}),
    Vs.PSet.both_of_branch(p, bl, bh, vb)),
                Hv.U32.lo_zero_half_base(base, 12n+p, lb),
                Dc.Nat.gt_down(32n, 11n+p, dok), at,
                As.Ords.asc_walk.hi_lower(p, base, tail, lb, dok, lw))),
                  As.Ords.asc_walk.lo_lower(p, base,
                    S.PSet.diff_members(p, S.PFull{}, bh,
                (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail), lb, dok,
                    E.Bool.and_r(Ol.Ords.asc(S.PSet.diff_members(p, S.PFull{}, bh,
                (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail)),
                      As.Ords.lower_all(
                        U32.to_nat((base + S.PSet.half(1n+p) : U32)),
                        S.PSet.diff_members(p, S.PFull{}, bh,
                (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail)),
                      Ords.asc_diff_walk(p, S.PFull{}, bh,
                (base + S.PSet.half(1n+p) : U32), tail,
                PSet.valid_full(p),
                E.Bool.and_r(S.PSet.valid(p, bl, True{}),
    S.PSet.valid(p, bh, True{}),
    Vs.PSet.both_of_branch(p, bl, bh, vb)),
                Hv.U32.lo_zero_half_base(base, 12n+p, lb),
                Dc.Nat.gt_down(32n, 11n+p, dok), at,
                As.Ords.asc_walk.hi_lower(p, base, tail, lb, dok, lw))))))
        case S.PBranch{al, ah}:
          match b:
            case S.PZero{}:
              As.Ords.asc_walk(1n+p, S.PBranch{al, ah}, base, tail,
                va, lb, dok, at, lw)
            case S.PSparse{o}:
              As.Ords.asc_walk(1n+p, S.PBranch{al, ah}, base, tail,
                va, lb, dok, at, lw)
            case S.PDense{w}:
              As.Ords.asc_walk(1n+p, S.PBranch{al, ah}, base, tail,
                va, lb, dok, at, lw)
            case S.PFull{}:
              Ords.asc_diff_walk.stop(p, base, tail, at, lw)
            case S.PBranch{bl, bh}:
              Ords.asc_diff_walk.branch(p, al, ah, bl, bh, base, tail, dok,
                Ords.asc_diff_walk(p, al, bl, base,
                  S.PSet.diff_members(p, ah, bh,
                (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail),
                  E.Bool.and_l(S.PSet.valid(p, al, True{}),
                    S.PSet.valid(p, ah, True{}),
                    Vs.PSet.both_of_branch(p, al, ah, va)),
                  E.Bool.and_l(S.PSet.valid(p, bl, True{}),
      S.PSet.valid(p, bh, True{}),
      Vs.PSet.both_of_branch(p, bl, bh, vb)),
                  Hv.Word.lo_zero_down(32n, W.U32.word(base), 12n+p, lb),
                  Dc.Nat.gt_down(32n, 11n+p, dok),
                  E.Bool.and_l(Ol.Ords.asc(S.PSet.diff_members(p, ah, bh,
                (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail)),
                    As.Ords.lower_all(
                      U32.to_nat((base + S.PSet.half(1n+p) : U32)),
                      S.PSet.diff_members(p, ah, bh,
                (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail)),
                    Ords.asc_diff_walk(p, ah, bh,
                (base + S.PSet.half(1n+p) : U32), tail,
                E.Bool.and_r(S.PSet.valid(p, al, True{}),
                  S.PSet.valid(p, ah, True{}),
                  Vs.PSet.both_of_branch(p, al, ah, va)),
                E.Bool.and_r(S.PSet.valid(p, bl, True{}),
    S.PSet.valid(p, bh, True{}),
    Vs.PSet.both_of_branch(p, bl, bh, vb)),
                Hv.U32.lo_zero_half_base(base, 12n+p, lb),
                Dc.Nat.gt_down(32n, 11n+p, dok), at,
                As.Ords.asc_walk.hi_lower(p, base, tail, lb, dok, lw))),
                  As.Ords.asc_walk.lo_lower(p, base,
                    S.PSet.diff_members(p, ah, bh,
                (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail), lb, dok,
                    E.Bool.and_r(Ol.Ords.asc(S.PSet.diff_members(p, ah, bh,
                (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail)),
                      As.Ords.lower_all(
                        U32.to_nat((base + S.PSet.half(1n+p) : U32)),
                        S.PSet.diff_members(p, ah, bh,
                (base + S.PSet.half(1n+p) : U32), S.PSet.half(p), tail)),
                      Ords.asc_diff_walk(p, ah, bh,
                (base + S.PSet.half(1n+p) : U32), tail,
                E.Bool.and_r(S.PSet.valid(p, al, True{}),
                  S.PSet.valid(p, ah, True{}),
                  Vs.PSet.both_of_branch(p, al, ah, va)),
                E.Bool.and_r(S.PSet.valid(p, bl, True{}),
    S.PSet.valid(p, bh, True{}),
    Vs.PSet.both_of_branch(p, bl, bh, vb)),
                Hv.U32.lo_zero_half_base(base, 12n+p, lb),
                Dc.Nat.gt_down(32n, 11n+p, dok), at,
                As.Ords.asc_walk.hi_lower(p, base, tail, lb, dok, lw))))))

law Ords.asc_missing:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +dok: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {Ol.Ords.asc(S.PSet.missing(d, a, b)) == True{} : Bool}

def Ords.asc_missing(d, a, b, va, vb, dok):
  E.Bool.and_l(Ol.Ords.asc(
    S.PSet.diff_members(d, a, b, 0, S.PSet.half(d), Nil{})),
    As.Ords.lower_all(U32.to_nat(0),
      S.PSet.diff_members(d, a, b, 0, S.PSet.half(d), Nil{})),
    Ords.asc_diff_walk(d, a, b, 0, Nil{}, va, vb,
      Te.Word.lo_zero_of_zero_bits(32n, W.U32.word(0), 12n+d, {==}),
      dok, {==}, {==}))
