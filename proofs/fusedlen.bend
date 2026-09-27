# proofs/fusedlen.bend -- the fused count is the length of the fused list.
#
# SPEC 7.2's fused reductions compute the size of `a \ b` and the members of
# `a \ b` without ever building `a \ b`. The two walks have the same shape
# arm for arm, so this file says what that shape means: the count the first
# returns is the length of the list the second returns.
#
# With proofs/countlen.bend and proofs/nonempty.bend that is the last step
# before a fused count that is not zero produces an ordinal -- which is what
# the converse of the subset bridge needs.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./countlen.bend as Cl
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# A tile.
# ---------------------------------------------------------------------------

law Words.length_diff_members_go:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +ord: U32
  for +acc: List<&2, U32>
  {List.length(&2, U32, Wo.Words.diff_members.go(a, b, ord, acc))
    == Wo.Words.diff_count.go(a, b, List.length(&2, U32, acc)) : Nat}

def Words.length_diff_members_go(a, b, ord, acc):
  match a:
    case Nil{}:
      {==}
    case Con{ah, at}:
      match b:
        case Nil{}:
          Cl.Words.length_members_go(Con{ah, at}, ord, acc)
        case Con{bh, bt}:
          %E.Nat.sym(List.length(&2, U32,
              Wo.Words.diff_members.go(at, bt, (ord + 32 : U32),
                Wo.Words.bits_rev(32n, W.U32.diff(ah, bh), ord, acc))),
            Wo.Words.diff_count.go(at, bt,
              List.length(&2, U32,
                Wo.Words.bits_rev(32n, W.U32.diff(ah, bh), ord, acc))),
            Words.length_diff_members_go(at, bt, (ord + 32 : U32),
              Wo.Words.bits_rev(32n, W.U32.diff(ah, bh), ord, acc)))
            : {_ == Wo.Words.diff_count.go(at, bt,
                 Nat.add(W.U32.popcount(W.U32.diff(ah, bh)),
                   List.length(&2, U32, acc))) : Nat}
          %E.Nat.sym(List.length(&2, U32,
              Wo.Words.bits_rev(32n, W.U32.diff(ah, bh), ord, acc)),
            Nat.add(W.U32.lowcount(32n, W.U32.diff(ah, bh)),
              List.length(&2, U32, acc)),
            Cl.Words.length_bits_rev(32n, W.U32.diff(ah, bh), ord,
              acc))
            : {Wo.Words.diff_count.go(at, bt, _)
              == Wo.Words.diff_count.go(at, bt,
                   Nat.add(W.U32.popcount(W.U32.diff(ah, bh)),
                     List.length(&2, U32, acc))) : Nat}
          %E.Nat.sym(W.U32.lowcount(32n, W.U32.diff(ah, bh)),
            W.U32.popcount(W.U32.diff(ah, bh)),
            Cl.Words.popcount_lowcount(W.U32.diff(ah, bh)))
            : {Wo.Words.diff_count.go(at, bt,
                Nat.add(_, List.length(&2, U32, acc)))
              == Wo.Words.diff_count.go(at, bt,
                   Nat.add(W.U32.popcount(W.U32.diff(ah, bh)),
                     List.length(&2, U32, acc))) : Nat}
          {==}

law Words.diff_count_is_length:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {Wo.Words.diff_count(a, b)
    == List.length(&2, U32, Wo.Words.diff_members(a, b, 0)) : Nat}

def Words.diff_count_is_length(a, b):
  %E.Nat.sym(List.length(&2, U32,
      List.reverse.go(&2, U32, Wo.Words.diff_members.go(a, b, 0,
        Nil{}), Nil{})),
    Nat.add(List.length(&2, U32,
      Wo.Words.diff_members.go(a, b, 0, Nil{})), 0n),
    Cl.List.length_reverse_go(Wo.Words.diff_members.go(a, b, 0,
      Nil{}), Nil{}))
    : {Wo.Words.diff_count(a, b) == _ : Nat}
  %E.Nat.sym(List.length(&2, U32,
      Wo.Words.diff_members.go(a, b, 0, Nil{})),
    Wo.Words.diff_count.go(a, b, 0n),
    Words.length_diff_members_go(a, b, 0, Nil{}))
    : {Wo.Words.diff_count(a, b) == Nat.add(_, 0n) : Nat}
  E.Nat.sym(Nat.add(Wo.Words.diff_count.go(a, b, 0n), 0n),
    Wo.Words.diff_count.go(a, b, 0n),
    N.Nat.add_zero(Wo.Words.diff_count.go(a, b, 0n)))

# ---------------------------------------------------------------------------
# A leaf: five shapes on each side, and only the two dense-against-dense
# arms need anything the tile lemma does not give directly.
# ---------------------------------------------------------------------------

law PSet.leaf_diff_count_is_length:
  for +a: S.PSet
  for +b: S.PSet
  {S.PSet.leaf_diff_count(a, b)
    == List.length(&2, U32, S.PSet.leaf_diff_members(a, b)) : Nat}

def PSet.leaf_diff_count_is_length(a, b):
  match a:
    case S.PZero{}:
      {==}
    case S.PBranch{l, h}:
      {==}
    case S.PSparse{ao}:
      {==}
    case S.PDense{aw}:
      match b:
        case S.PZero{}:
          Cl.Words.count_is_length(aw)
        case S.PFull{}:
          {==}
        case S.PDense{bw}:
          Words.diff_count_is_length(aw, bw)
        case S.PSparse{bo}:
          {==}
        case S.PBranch{l, h}:
          Cl.Words.count_is_length(aw)
    case S.PFull{}:
      match b:
        case S.PZero{}:
          Cl.PSet.count_leaf_is_length(S.PFull{})
        case S.PFull{}:
          {==}
        case S.PDense{bw}:
          Words.diff_count_is_length(Wo.Words.ones(128n), bw)
        case S.PSparse{bo}:
          {==}
        case S.PBranch{l, h}:
          Cl.PSet.count_leaf_is_length(S.PFull{})

# ---------------------------------------------------------------------------
# The tree. Both walks split a branch the same way, so each arm is the two
# halves put back together.
# ---------------------------------------------------------------------------

def PSet.pair_count(+p: Nat, +lo: S.PSet, +hi: S.PSet, +base: U32,
  +tail: List<&2, U32>, +h2: U32,
  +eh2: {h2 == S.PSet.half(p) : U32},
  +lt: {C.Nat.gt(32n, 11n+p) == True{} : Bool})
  -> {List.length(&2, U32,
       S.PSet.members(p, lo, base, h2,
         S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
           h2, tail)))
     == Nat.add(Nat.add(S.PSet.count(p, lo, h2),
          S.PSet.count(p, hi, h2)),
          List.length(&2, U32, tail)) : Nat}:
  %E.U32.sym(h2, S.PSet.half(p), eh2)
    : {List.length(&2, U32,
        S.PSet.members(p, lo, base, _,
          S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
            _, tail)))
      == Nat.add(Nat.add(S.PSet.count(p, lo, _),
           S.PSet.count(p, hi, _)),
           List.length(&2, U32, tail)) : Nat}
  %E.Nat.sym(List.length(&2, U32,
      S.PSet.members(p, lo, base, S.PSet.half(p),
        S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
          S.PSet.half(p), tail))),
    Nat.add(S.PSet.count(p, lo, S.PSet.half(p)),
      List.length(&2, U32,
        S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
          S.PSet.half(p), tail))),
    Cl.PSet.count_is_length(p, lo, base,
      S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
        S.PSet.half(p), tail), lt))
    : {_ == Nat.add(Nat.add(S.PSet.count(p, lo, S.PSet.half(p)),
         S.PSet.count(p, hi, S.PSet.half(p))),
         List.length(&2, U32, tail)) : Nat}
  %E.Nat.sym(List.length(&2, U32,
      S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
        S.PSet.half(p), tail)),
    Nat.add(S.PSet.count(p, hi, S.PSet.half(p)),
      List.length(&2, U32, tail)),
    Cl.PSet.count_is_length(p, hi,
      (base + U32.shln(1, 12n+p) : U32), tail, lt))
    : {Nat.add(S.PSet.count(p, lo, S.PSet.half(p)), _)
      == Nat.add(Nat.add(S.PSet.count(p, lo, S.PSet.half(p)),
           S.PSet.count(p, hi, S.PSet.half(p))),
           List.length(&2, U32, tail)) : Nat}
  E.Nat.sym(Nat.add(Nat.add(S.PSet.count(p, lo, S.PSet.half(p)),
    S.PSet.count(p, hi, S.PSet.half(p))),
    List.length(&2, U32, tail)),
    Nat.add(S.PSet.count(p, lo, S.PSet.half(p)),
      Nat.add(S.PSet.count(p, hi, S.PSet.half(p)),
        List.length(&2, U32, tail))),
    N.Nat.add_assoc(S.PSet.count(p, lo, S.PSet.half(p)),
      S.PSet.count(p, hi, S.PSet.half(p)),
      List.length(&2, U32, tail)))

def PSet.pair_diff(+p: Nat, +al: S.PSet, +bl: S.PSet, +ah: S.PSet,
  +bh: S.PSet, +base: U32, +tail: List<&2, U32>, +h2: U32,
  +eh2: {h2 == S.PSet.half(p) : U32},
  +ihlo: {List.length(&2, U32,
      S.PSet.diff_members(p, al, bl, base, S.PSet.half(p),
        S.PSet.diff_members(p, ah, bh,
          (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail)))
    == Nat.add(S.PSet.diff_count(p, al, bl, S.PSet.half(p)),
         List.length(&2, U32,
           S.PSet.diff_members(p, ah, bh,
             (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
             tail))) : Nat},
  +ihhi: {List.length(&2, U32,
      S.PSet.diff_members(p, ah, bh,
        (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail))
    == Nat.add(S.PSet.diff_count(p, ah, bh, S.PSet.half(p)),
         List.length(&2, U32, tail)) : Nat})
  -> {List.length(&2, U32,
       S.PSet.diff_members(p, al, bl, base, h2,
         S.PSet.diff_members(p, ah, bh,
           (base + U32.shln(1, 12n+p) : U32), h2, tail)))
     == Nat.add(Nat.add(S.PSet.diff_count(p, al, bl, h2),
          S.PSet.diff_count(p, ah, bh, h2)),
          List.length(&2, U32, tail)) : Nat}:
  %E.U32.sym(h2, S.PSet.half(p), eh2)
    : {List.length(&2, U32,
        S.PSet.diff_members(p, al, bl, base, _,
          S.PSet.diff_members(p, ah, bh,
            (base + U32.shln(1, 12n+p) : U32), _, tail)))
      == Nat.add(Nat.add(S.PSet.diff_count(p, al, bl, _),
           S.PSet.diff_count(p, ah, bh, _)),
           List.length(&2, U32, tail)) : Nat}
  %E.Nat.sym(List.length(&2, U32,
      S.PSet.diff_members(p, al, bl, base, S.PSet.half(p),
        S.PSet.diff_members(p, ah, bh,
          (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail))),
    Nat.add(S.PSet.diff_count(p, al, bl, S.PSet.half(p)),
      List.length(&2, U32,
        S.PSet.diff_members(p, ah, bh,
          (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail))),
    ihlo)
    : {_ == Nat.add(Nat.add(S.PSet.diff_count(p, al, bl,
         S.PSet.half(p)),
         S.PSet.diff_count(p, ah, bh, S.PSet.half(p))),
         List.length(&2, U32, tail)) : Nat}
  %E.Nat.sym(List.length(&2, U32,
      S.PSet.diff_members(p, ah, bh,
        (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p), tail)),
    Nat.add(S.PSet.diff_count(p, ah, bh, S.PSet.half(p)),
      List.length(&2, U32, tail)), ihhi)
    : {Nat.add(S.PSet.diff_count(p, al, bl, S.PSet.half(p)), _)
      == Nat.add(Nat.add(S.PSet.diff_count(p, al, bl,
           S.PSet.half(p)),
           S.PSet.diff_count(p, ah, bh, S.PSet.half(p))),
           List.length(&2, U32, tail)) : Nat}
  E.Nat.sym(Nat.add(Nat.add(S.PSet.diff_count(p, al, bl,
    S.PSet.half(p)), S.PSet.diff_count(p, ah, bh, S.PSet.half(p))),
    List.length(&2, U32, tail)),
    Nat.add(S.PSet.diff_count(p, al, bl, S.PSet.half(p)),
      Nat.add(S.PSet.diff_count(p, ah, bh, S.PSet.half(p)),
        List.length(&2, U32, tail))),
    N.Nat.add_assoc(S.PSet.diff_count(p, al, bl, S.PSet.half(p)),
      S.PSet.diff_count(p, ah, bh, S.PSet.half(p)),
      List.length(&2, U32, tail)))

law PSet.diff_count_is_length:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +base: U32
  for +tail: List<&2, U32>
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {List.length(&2, U32,
     S.PSet.diff_members(d, a, b, base, S.PSet.half(d), tail))
   == Nat.add(S.PSet.diff_count(d, a, b, S.PSet.half(d)),
        List.length(&2, U32, tail)) : Nat}

def PSet.diff_count_is_length(d, a, b, base, tail, lt):
  match d:
    case 0n:
      %E.Nat.sym(List.length(&2, U32,
          List.append(&2, U32,
            S.PSet.shift(S.PSet.leaf_diff_members(a, b), base), tail)),
        Nat.add(List.length(&2, U32, S.PSet.leaf_diff_members(a, b)),
          List.length(&2, U32, tail)),
        Cl.PSet.count_is_length.listarm(
          S.PSet.leaf_diff_members(a, b), base, tail))
        : {_ == Nat.add(S.PSet.leaf_diff_count(a, b),
             List.length(&2, U32, tail)) : Nat}
      %PSet.leaf_diff_count_is_length(a, b)
        : {Nat.add(_, List.length(&2, U32, tail))
          == Nat.add(S.PSet.leaf_diff_count(a, b),
               List.length(&2, U32, tail)) : Nat}
      {==}
    case 1n+p:
      match a:
        case S.PZero{}:
          {==}
        case S.PSparse{o}:
          {==}
        case S.PDense{w}:
          {==}
        case S.PFull{}:
          match b:
            case S.PZero{}:
              Cl.List.length_range(
                Nat.add(U32.to_nat(U32.shln(1, 12n+p)),
                  U32.to_nat(U32.shln(1, 12n+p))),
                (base + U32.shln(1, 12n+p) + U32.shln(1, 12n+p)
                  - 1 : U32), tail)
            case S.PFull{}:
              {==}
            case S.PSparse{o}:
              Cl.List.length_range(
                Nat.add(U32.to_nat(U32.shln(1, 12n+p)),
                  U32.to_nat(U32.shln(1, 12n+p))),
                (base + U32.shln(1, 12n+p) + U32.shln(1, 12n+p)
                  - 1 : U32), tail)
            case S.PDense{w}:
              Cl.List.length_range(
                Nat.add(U32.to_nat(U32.shln(1, 12n+p)),
                  U32.to_nat(U32.shln(1, 12n+p))),
                (base + U32.shln(1, 12n+p) + U32.shln(1, 12n+p)
                  - 1 : U32), tail)
            case S.PBranch{bl, bh}:
              PSet.pair_diff(p, S.PFull{}, bl, S.PFull{}, bh, base,
                tail, U32.shr(U32.shln(1, 12n+p)),
                Dc.U32.shr_shln_one(11n+p, lt),
                PSet.diff_count_is_length(p, S.PFull{}, bl, base,
                  S.PSet.diff_members(p, S.PFull{}, bh,
                    (base + U32.shln(1, 12n+p) : U32),
                    S.PSet.half(p), tail),
                  Dc.Nat.gt_down(32n, 11n+p, lt)),
                PSet.diff_count_is_length(p, S.PFull{}, bh,
                  (base + U32.shln(1, 12n+p) : U32), tail,
                  Dc.Nat.gt_down(32n, 11n+p, lt)))
        case S.PBranch{al, ah}:
          match b:
            case S.PZero{}:
              PSet.pair_count(p, al, ah, base, tail,
                U32.shr(U32.shln(1, 12n+p)),
                Dc.U32.shr_shln_one(11n+p, lt),
                Dc.Nat.gt_down(32n, 11n+p, lt))
            case S.PSparse{o}:
              PSet.pair_count(p, al, ah, base, tail,
                U32.shr(U32.shln(1, 12n+p)),
                Dc.U32.shr_shln_one(11n+p, lt),
                Dc.Nat.gt_down(32n, 11n+p, lt))
            case S.PDense{w}:
              PSet.pair_count(p, al, ah, base, tail,
                U32.shr(U32.shln(1, 12n+p)),
                Dc.U32.shr_shln_one(11n+p, lt),
                Dc.Nat.gt_down(32n, 11n+p, lt))
            case S.PFull{}:
              {==}
            case S.PBranch{bl, bh}:
              PSet.pair_diff(p, al, bl, ah, bh, base, tail,
                U32.shr(U32.shln(1, 12n+p)),
                Dc.U32.shr_shln_one(11n+p, lt),
                PSet.diff_count_is_length(p, al, bl, base,
                  S.PSet.diff_members(p, ah, bh,
                    (base + U32.shln(1, 12n+p) : U32),
                    S.PSet.half(p), tail),
                  Dc.Nat.gt_down(32n, 11n+p, lt)),
                PSet.diff_count_is_length(p, ah, bh,
                  (base + U32.shln(1, 12n+p) : U32), tail,
                  Dc.Nat.gt_down(32n, 11n+p, lt)))

law PSet.missing_count_is_length:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {S.PSet.missing_count(d, a, b)
    == List.length(&2, U32, S.PSet.missing(d, a, b)) : Nat}

def PSet.missing_count_is_length(d, a, b, lt):
  %E.Nat.sym(List.length(&2, U32,
      S.PSet.diff_members(d, a, b, 0, S.PSet.half(d), Nil{})),
    Nat.add(S.PSet.diff_count(d, a, b, S.PSet.half(d)), 0n),
    PSet.diff_count_is_length(d, a, b, 0, Nil{}, lt))
    : {S.PSet.missing_count(d, a, b) == _ : Nat}
  E.Nat.sym(Nat.add(S.PSet.diff_count(d, a, b, S.PSet.half(d)), 0n),
    S.PSet.diff_count(d, a, b, S.PSet.half(d)),
    N.Nat.add_zero(S.PSet.diff_count(d, a, b, S.PSet.half(d))))
