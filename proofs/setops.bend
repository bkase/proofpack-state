# proofs/setops.bend -- the set operations are pointwise (law S-02).
#
# Everything this needs is proved. At a leaf the operations are pointwise
# (proofs/leafops.bend). Above a leaf the Zero/Full collapses preserve
# membership (proofs/collapse.bend), and the descent carries an ordinal into
# a child correctly (proofs/descend.bend). What is here is the induction that
# runs them down the tree, with the same shape as P-01's descent: the
# operation and the membership test take the same branch from the same
# half-width, so the tree layer adds nothing but addressing.
#
# Structural validity is what rules out a payload above a leaf, and it is
# what makes the case analysis finite: at any depth above a leaf a valid set
# is `PZero{}`, `PFull{}` or a branch.

import Base
import ./eq.bend as E
import ./collapse.bend as Co
import ./descend.bend as Dc
import ./leaf.bend as Lf
import ./leafops.bend as Lo
import ../core/count.bend as C
import ../core/set.bend as S

law PSet.valid_full:
  for +d: Nat
  {S.PSet.valid(d, S.PFull{}, True{}) == True{} : Bool}

def PSet.valid_full(d):
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

law PSet.diff_pointwise:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +h: U32
  for +x: U32
  for +eh: {h == U32.shln(1, 11n+d) : U32}
  for +dok: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +bt: Bool
  for +ebt: {bt == U32.is_lt(x, h) : Bool}
  {S.PSet.mem(d, S.PSet.diff(d, a, b), h, x)
    == Bool.and(S.PSet.mem(d, a, h, x),
         Bool.not(S.PSet.mem(d, b, h, x))) : Bool}

law Bool.and_true_r2:
  for +b: Bool
  {b == Bool.and(b, True{}) : Bool}

def Bool.and_true_r2(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law Bool.and_false_r2:
  for +b: Bool
  {False{} == Bool.and(b, False{}) : Bool}

def Bool.and_false_r2(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def PSet.diff_pointwise(d, a, b, h, x, eh, dok, va, vb, inv, bt, ebt):
  match d:
    case 0n:
      Lo.PSet.diff_leaf_pointwise(a, b, x, va, vb, inv)
    case 1n+p:
      match a:
        case S.PZero{}:
          {==}
        case S.PSparse{o}:
          E.Bool.noconf({S.PSet.mem(1n+p,
            S.PSet.diff(1n+p, S.PSparse{o}, b), h, x)
            == Bool.and(S.PSet.mem(1n+p, S.PSparse{o}, h, x),
                 Bool.not(S.PSet.mem(1n+p, b, h, x))) : Bool}, va)
        case S.PDense{w}:
          E.Bool.noconf({S.PSet.mem(1n+p,
            S.PSet.diff(1n+p, S.PDense{w}, b), h, x)
            == Bool.and(S.PSet.mem(1n+p, S.PDense{w}, h, x),
                 Bool.not(S.PSet.mem(1n+p, b, h, x))) : Bool}, va)
        case S.PFull{}:
          match b:
            case S.PZero{}:
              {==}
            case S.PFull{}:
              {==}
            case S.PSparse{o}:
              E.Bool.noconf({S.PSet.mem(1n+p,
                S.PSet.diff(1n+p, S.PFull{}, S.PSparse{o}), h, x)
                == Bool.and(S.PSet.mem(1n+p, S.PFull{}, h, x),
                     Bool.not(S.PSet.mem(1n+p, S.PSparse{o}, h, x)))
                : Bool}, vb)
            case S.PDense{w}:
              E.Bool.noconf({S.PSet.mem(1n+p,
                S.PSet.diff(1n+p, S.PFull{}, S.PDense{w}), h, x)
                == Bool.and(S.PSet.mem(1n+p, S.PFull{}, h, x),
                     Bool.not(S.PSet.mem(1n+p, S.PDense{w}, h, x)))
                : Bool}, vb)
            case S.PBranch{bl, bh}:
              match bt:
                case True{}:
                  %E.Bool.sym(
                    S.PSet.mem(1n+p, S.PSet.mk(S.PSet.diff(p, S.PFull{},
                      bl), S.PSet.diff(p, S.PFull{}, bh)), h, x),
                    S.PSet.mem(1n+p, S.PBranch{S.PSet.diff(p, S.PFull{},
                      bl), S.PSet.diff(p, S.PFull{}, bh)}, h, x),
                    Co.PSet.mem_mk(p, S.PSet.diff(p, S.PFull{}, bl),
                      S.PSet.diff(p, S.PFull{}, bh), h, x))
                    : {_ == Bool.and(S.PSet.mem(1n+p, S.PFull{}, h, x),
                        Bool.not(S.PSet.mem(1n+p, S.PBranch{bl, bh},
                          h, x))) : Bool}
                  %ebt : {S.PSet.mem(p, S.PSet.pick(_,
                      S.PSet.diff(p, S.PFull{}, bl),
                      S.PSet.diff(p, S.PFull{}, bh)),
                      U32.shr(h), S.PSet.rebase(_, h, x))
                    == Bool.and(True{},
                         Bool.not(S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                           U32.shr(h), S.PSet.rebase(_, h, x)))) : Bool}
                  %Co.PSet.mem_full(p, U32.shr(h), x)
                    : {S.PSet.mem(p, S.PSet.diff(p, S.PFull{}, bl),
                        U32.shr(h), x)
                      == Bool.and(_, Bool.not(S.PSet.mem(p, bl,
                           U32.shr(h), x))) : Bool}
                  PSet.diff_pointwise(p, S.PFull{}, bl, U32.shr(h), x,
                    Lf.PSet.half_shr(p, h, eh, dok),
                    Dc.Nat.gt_down(32n, 11n+p, dok), PSet.valid_full(p),
                    Lf.PSet.valid_lo(p, bl, bh, vb),
                    Lf.PSet.range_lo(p, h, x, eh, dok, ebt),
                    U32.is_lt(x, U32.shr(h)), {==})
                case False{}:
                  %E.Bool.sym(
                    S.PSet.mem(1n+p, S.PSet.mk(S.PSet.diff(p, S.PFull{},
                      bl), S.PSet.diff(p, S.PFull{}, bh)), h, x),
                    S.PSet.mem(1n+p, S.PBranch{S.PSet.diff(p, S.PFull{},
                      bl), S.PSet.diff(p, S.PFull{}, bh)}, h, x),
                    Co.PSet.mem_mk(p, S.PSet.diff(p, S.PFull{}, bl),
                      S.PSet.diff(p, S.PFull{}, bh), h, x))
                    : {_ == Bool.and(S.PSet.mem(1n+p, S.PFull{}, h, x),
                        Bool.not(S.PSet.mem(1n+p, S.PBranch{bl, bh},
                          h, x))) : Bool}
                  %ebt : {S.PSet.mem(p, S.PSet.pick(_,
                      S.PSet.diff(p, S.PFull{}, bl),
                      S.PSet.diff(p, S.PFull{}, bh)),
                      U32.shr(h), S.PSet.rebase(_, h, x))
                    == Bool.and(True{},
                         Bool.not(S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                           U32.shr(h), S.PSet.rebase(_, h, x)))) : Bool}
                  %Co.PSet.mem_full(p, U32.shr(h), U32.sub(x, h))
                    : {S.PSet.mem(p, S.PSet.diff(p, S.PFull{}, bh),
                        U32.shr(h), U32.sub(x, h))
                      == Bool.and(_, Bool.not(S.PSet.mem(p, bh,
                           U32.shr(h), U32.sub(x, h)))) : Bool}
                  PSet.diff_pointwise(p, S.PFull{}, bh, U32.shr(h),
                    U32.sub(x, h),
                    Lf.PSet.half_shr(p, h, eh, dok),
                    Dc.Nat.gt_down(32n, 11n+p, dok), PSet.valid_full(p),
                    Lf.PSet.valid_hi(p, bl, bh, vb),
                    Lf.PSet.range_hi(p, h, x, eh, dok, ebt, inv),
                    U32.is_lt(U32.sub(x, h), U32.shr(h)), {==})
        case S.PBranch{al, ah}:
          match b:
            case S.PZero{}:
              Bool.and_true_r2(S.PSet.mem(1n+p, S.PBranch{al, ah}, h, x))
            case S.PFull{}:
              Bool.and_false_r2(
                S.PSet.mem(1n+p, S.PBranch{al, ah}, h, x))
            case S.PSparse{o}:
              E.Bool.noconf({S.PSet.mem(1n+p,
                S.PSet.diff(1n+p, S.PBranch{al, ah}, S.PSparse{o}), h, x)
                == Bool.and(S.PSet.mem(1n+p, S.PBranch{al, ah}, h, x),
                     Bool.not(S.PSet.mem(1n+p, S.PSparse{o}, h, x)))
                : Bool}, vb)
            case S.PDense{w}:
              E.Bool.noconf({S.PSet.mem(1n+p,
                S.PSet.diff(1n+p, S.PBranch{al, ah}, S.PDense{w}), h, x)
                == Bool.and(S.PSet.mem(1n+p, S.PBranch{al, ah}, h, x),
                     Bool.not(S.PSet.mem(1n+p, S.PDense{w}, h, x)))
                : Bool}, vb)
            case S.PBranch{bl, bh}:
              match bt:
                case True{}:
                  %E.Bool.sym(
                    S.PSet.mem(1n+p, S.PSet.mk(S.PSet.diff(p, al, bl),
                      S.PSet.diff(p, ah, bh)), h, x),
                    S.PSet.mem(1n+p, S.PBranch{S.PSet.diff(p, al, bl),
                      S.PSet.diff(p, ah, bh)}, h, x),
                    Co.PSet.mem_mk(p, S.PSet.diff(p, al, bl),
                      S.PSet.diff(p, ah, bh), h, x))
                    : {_ == Bool.and(
                        S.PSet.mem(1n+p, S.PBranch{al, ah}, h, x),
                        Bool.not(S.PSet.mem(1n+p, S.PBranch{bl, bh},
                          h, x))) : Bool}
                  %ebt : {S.PSet.mem(p, S.PSet.pick(_,
                      S.PSet.diff(p, al, bl), S.PSet.diff(p, ah, bh)),
                      U32.shr(h), S.PSet.rebase(_, h, x))
                    == Bool.and(S.PSet.mem(p, S.PSet.pick(_, al, ah),
                         U32.shr(h), S.PSet.rebase(_, h, x)),
                         Bool.not(S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                           U32.shr(h), S.PSet.rebase(_, h, x)))) : Bool}
                  PSet.diff_pointwise(p, al, bl, U32.shr(h), x,
                    Lf.PSet.half_shr(p, h, eh, dok),
                    Dc.Nat.gt_down(32n, 11n+p, dok),
                    Lf.PSet.valid_lo(p, al, ah, va),
                    Lf.PSet.valid_lo(p, bl, bh, vb),
                    Lf.PSet.range_lo(p, h, x, eh, dok, ebt),
                    U32.is_lt(x, U32.shr(h)), {==})
                case False{}:
                  %E.Bool.sym(
                    S.PSet.mem(1n+p, S.PSet.mk(S.PSet.diff(p, al, bl),
                      S.PSet.diff(p, ah, bh)), h, x),
                    S.PSet.mem(1n+p, S.PBranch{S.PSet.diff(p, al, bl),
                      S.PSet.diff(p, ah, bh)}, h, x),
                    Co.PSet.mem_mk(p, S.PSet.diff(p, al, bl),
                      S.PSet.diff(p, ah, bh), h, x))
                    : {_ == Bool.and(
                        S.PSet.mem(1n+p, S.PBranch{al, ah}, h, x),
                        Bool.not(S.PSet.mem(1n+p, S.PBranch{bl, bh},
                          h, x))) : Bool}
                  %ebt : {S.PSet.mem(p, S.PSet.pick(_,
                      S.PSet.diff(p, al, bl), S.PSet.diff(p, ah, bh)),
                      U32.shr(h), S.PSet.rebase(_, h, x))
                    == Bool.and(S.PSet.mem(p, S.PSet.pick(_, al, ah),
                         U32.shr(h), S.PSet.rebase(_, h, x)),
                         Bool.not(S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                           U32.shr(h), S.PSet.rebase(_, h, x)))) : Bool}
                  PSet.diff_pointwise(p, ah, bh, U32.shr(h),
                    U32.sub(x, h),
                    Lf.PSet.half_shr(p, h, eh, dok),
                    Dc.Nat.gt_down(32n, 11n+p, dok),
                    Lf.PSet.valid_hi(p, al, ah, va),
                    Lf.PSet.valid_hi(p, bl, bh, vb),
                    Lf.PSet.range_hi(p, h, x, eh, dok, ebt, inv),
                    U32.is_lt(U32.sub(x, h), U32.shr(h)), {==})

# At the depth the product runs at. Depth 20 covers 2^32 ordinals, so every
# `U32` is in range and no hypothesis about the ordinal survives.
law PSet.diff_member:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid(20n, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(20n, b, True{}) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.diff(20n, a, b), x)
    == Bool.and(S.PSet.member(20n, a, x),
         Bool.not(S.PSet.member(20n, b, x))) : Bool}

def PSet.diff_member(a, b, x, va, vb):
  PSet.diff_pointwise(20n, a, b, S.PSet.half(20n), x, {==}, {==},
    va, vb, Dc.U32.hi_zero_full(x),
    U32.is_lt(x, S.PSet.half(20n)), {==})
