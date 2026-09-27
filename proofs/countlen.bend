# proofs/countlen.bend -- the count is the length of the enumeration.
#
# `PSet.count` walks the tree adding popcounts and interval widths;
# `PSet.members` walks the same tree emitting ordinals. This file says the
# first is the length of the second, arm for arm, which is what turns a
# statistic back into a statement about members: a set whose count is not
# zero has an ordinal in the list it enumerates, and that ordinal is a
# member.
#
# The tile arm is where the work is. `Words.count` sums popcounts and
# `Words.members` walks bits low to high, prepending an ordinal for each one
# set -- so the two agree exactly when popcount agrees with the low-bit walk,
# which proofs/popcount.bend already proves.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./popcount.bend as Pc
import ./bits.bend as Bi
import ./shift.bend as Sf
import ./treeenum.bend as Te
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# Lists.
# ---------------------------------------------------------------------------

law List.length_append:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {List.length(&2, U32, List.append(&2, U32, a, b))
    == Nat.add(List.length(&2, U32, a), List.length(&2, U32, b))
    : Nat}

def List.length_append(a, b):
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %E.Nat.sym(List.length(&2, U32, List.append(&2, U32, t, b)),
        Nat.add(List.length(&2, U32, t), List.length(&2, U32, b)),
        List.length_append(t, b))
        : {1n+_
          == Nat.add(1n+List.length(&2, U32, t),
               List.length(&2, U32, b)) : Nat}
      {==}

law List.length_shift:
  for +xs: List<&2, U32>
  for +base: U32
  {List.length(&2, U32, S.PSet.shift(xs, base))
    == List.length(&2, U32, xs) : Nat}

def List.length_shift(xs, base):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %E.Nat.sym(List.length(&2, U32, S.PSet.shift(t, base)),
        List.length(&2, U32, t), List.length_shift(t, base))
        : {1n+_ == 1n+List.length(&2, U32, t) : Nat}
      {==}

law List.length_range:
  for +k: Nat
  for +ord: U32
  for +tail: List<&2, U32>
  {List.length(&2, U32, S.PSet.range(k, ord, tail))
    == Nat.add(k, List.length(&2, U32, tail)) : Nat}

def List.length_range(k, ord, tail):
  match k:
    case 0n:
      {==}
    case 1n+j:
      %E.Nat.sym(List.length(&2, U32,
          S.PSet.range(j, U32.sub(ord, 1), Con{ord, tail})),
        Nat.add(j, 1n+List.length(&2, U32, tail)),
        List.length_range(j, U32.sub(ord, 1), Con{ord, tail}))
        : {_ == Nat.add(1n+j, List.length(&2, U32, tail)) : Nat}
      N.Nat.add_succ(j, List.length(&2, U32, tail))

law List.length_reverse_go:
  for +l: List<&2, U32>
  for +acc: List<&2, U32>
  {List.length(&2, U32, List.reverse.go(&2, U32, l, acc))
    == Nat.add(List.length(&2, U32, l), List.length(&2, U32, acc))
    : Nat}

def List.length_reverse_go(l, acc):
  match l:
    case Nil{}:
      {==}
    case Con{h, t}:
      %E.Nat.sym(List.length(&2, U32,
          List.reverse.go(&2, U32, t, Con{h, acc})),
        Nat.add(List.length(&2, U32, t), 1n+List.length(&2, U32, acc)),
        List.length_reverse_go(t, Con{h, acc}))
        : {_ == Nat.add(1n+List.length(&2, U32, t),
             List.length(&2, U32, acc)) : Nat}
      N.Nat.add_succ(List.length(&2, U32, t),
        List.length(&2, U32, acc))

# ---------------------------------------------------------------------------
# A tile: one ordinal in the list for each bit set.
# ---------------------------------------------------------------------------

law Words.length_cons_if:
  for +w: U32
  for +b: Bool
  for +ord: U32
  for +acc: List<&2, U32>
  for +eb: {b == W.U32.bit(w, 0n) : Bool}
  {List.length(&2, U32,
    Wo.Words.cons_if(Wo.Nat.is_one(W.U32.low(w)), ord, acc))
    == Nat.add(W.U32.low(w), List.length(&2, U32, acc)) : Nat}

def Words.length_cons_if(w, b, ord, acc, eb):
  match b:
    case False{}:
      %E.Nat.sym(W.U32.low(w), W.U32.bump(W.U32.bit(w, 0n), 0n),
        Pc.U32.low_spec(w))
        : {List.length(&2, U32,
            Wo.Words.cons_if(Wo.Nat.is_one(_), ord, acc))
          == Nat.add(_, List.length(&2, U32, acc)) : Nat}
      %eb
        : {List.length(&2, U32,
            Wo.Words.cons_if(Wo.Nat.is_one(W.U32.bump(_, 0n)), ord,
              acc))
          == Nat.add(W.U32.bump(_, 0n),
               List.length(&2, U32, acc)) : Nat}
      {==}
    case True{}:
      %E.Nat.sym(W.U32.low(w), W.U32.bump(W.U32.bit(w, 0n), 0n),
        Pc.U32.low_spec(w))
        : {List.length(&2, U32,
            Wo.Words.cons_if(Wo.Nat.is_one(_), ord, acc))
          == Nat.add(_, List.length(&2, U32, acc)) : Nat}
      %eb
        : {List.length(&2, U32,
            Wo.Words.cons_if(Wo.Nat.is_one(W.U32.bump(_, 0n)), ord,
              acc))
          == Nat.add(W.U32.bump(_, 0n),
               List.length(&2, U32, acc)) : Nat}
      {==}

law Words.length_bits_rev:
  for +k: Nat
  for +w: U32
  for +ord: U32
  for +acc: List<&2, U32>
  {List.length(&2, U32, Wo.Words.bits_rev(k, w, ord, acc))
    == Nat.add(W.U32.lowcount(k, w), List.length(&2, U32, acc)) : Nat}

def Words.length_bits_rev(k, w, ord, acc):
  match k:
    case 0n:
      {==}
    case 1n+j:
      %E.Nat.sym(List.length(&2, U32,
          Wo.Words.bits_rev(j, U32.shr(w), (ord + 1 : U32),
            Wo.Words.cons_if(Wo.Nat.is_one(W.U32.low(w)), ord, acc))),
        Nat.add(W.U32.lowcount(j, U32.shr(w)),
          List.length(&2, U32,
            Wo.Words.cons_if(Wo.Nat.is_one(W.U32.low(w)), ord, acc))),
        Words.length_bits_rev(j, U32.shr(w), (ord + 1 : U32),
          Wo.Words.cons_if(Wo.Nat.is_one(W.U32.low(w)), ord, acc)))
        : {_ == Nat.add(Nat.add(W.U32.low(w),
             W.U32.lowcount(j, U32.shr(w))),
             List.length(&2, U32, acc)) : Nat}
      %E.Nat.sym(List.length(&2, U32,
          Wo.Words.cons_if(Wo.Nat.is_one(W.U32.low(w)), ord, acc)),
        Nat.add(W.U32.low(w), List.length(&2, U32, acc)),
        Words.length_cons_if(w, W.U32.bit(w, 0n), ord, acc, {==}))
        : {Nat.add(W.U32.lowcount(j, U32.shr(w)), _)
          == Nat.add(Nat.add(W.U32.low(w),
               W.U32.lowcount(j, U32.shr(w))),
               List.length(&2, U32, acc)) : Nat}
      Pc.Nat.add_swap(W.U32.lowcount(j, U32.shr(w)), W.U32.low(w),
        List.length(&2, U32, acc))

law Words.length_members_go:
  for +ws: List<&2, U32>
  for +ord: U32
  for +acc: List<&2, U32>
  {List.length(&2, U32, Wo.Words.members.go(ws, ord, acc))
    == Wo.Words.count.go(ws, List.length(&2, U32, acc)) : Nat}

law Words.popcount_lowcount:
  for +w: U32
  {W.U32.lowcount(32n, w) == W.U32.popcount(w) : Nat}

def Words.popcount_lowcount(w):
  %E.Nat.sym(W.U32.popcount(w), W.U32.card(32n, w),
    Pc.U32.popcount_spec(w))
    : {W.U32.lowcount(32n, w) == _ : Nat}
  Pc.U32.lowcount_card(32n, w)

def Words.length_members_go(ws, ord, acc):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      %E.Nat.sym(List.length(&2, U32,
          Wo.Words.members.go(t, (ord + 32 : U32),
            Wo.Words.bits_rev(32n, w, ord, acc))),
        Wo.Words.count.go(t, List.length(&2, U32,
          Wo.Words.bits_rev(32n, w, ord, acc))),
        Words.length_members_go(t, (ord + 32 : U32),
          Wo.Words.bits_rev(32n, w, ord, acc)))
        : {_ == Wo.Words.count.go(t,
             Nat.add(W.U32.popcount(w),
               List.length(&2, U32, acc))) : Nat}
      %E.Nat.sym(List.length(&2, U32,
          Wo.Words.bits_rev(32n, w, ord, acc)),
        Nat.add(W.U32.lowcount(32n, w), List.length(&2, U32, acc)),
        Words.length_bits_rev(32n, w, ord, acc))
        : {Wo.Words.count.go(t, _)
          == Wo.Words.count.go(t,
               Nat.add(W.U32.popcount(w),
                 List.length(&2, U32, acc))) : Nat}
      %E.Nat.sym(W.U32.lowcount(32n, w), W.U32.popcount(w),
        Words.popcount_lowcount(w))
        : {Wo.Words.count.go(t,
            Nat.add(_, List.length(&2, U32, acc)))
          == Wo.Words.count.go(t,
               Nat.add(W.U32.popcount(w),
                 List.length(&2, U32, acc))) : Nat}
      {==}

law Words.count_is_length:
  for +ws: List<&2, U32>
  {Wo.Words.count(ws)
    == List.length(&2, U32, Wo.Words.members(ws, 0)) : Nat}

def Words.count_is_length(ws):
  %E.Nat.sym(List.length(&2, U32,
      List.reverse.go(&2, U32, Wo.Words.members.go(ws, 0, Nil{}),
        Nil{})),
    Nat.add(List.length(&2, U32, Wo.Words.members.go(ws, 0, Nil{})),
      0n),
    List.length_reverse_go(Wo.Words.members.go(ws, 0, Nil{}), Nil{}))
    : {Wo.Words.count(ws) == _ : Nat}
  %E.Nat.sym(List.length(&2, U32, Wo.Words.members.go(ws, 0, Nil{})),
    Wo.Words.count.go(ws, 0n),
    Words.length_members_go(ws, 0, Nil{}))
    : {Wo.Words.count(ws) == Nat.add(_, 0n) : Nat}
  E.Nat.sym(Nat.add(Wo.Words.count.go(ws, 0n), 0n),
    Wo.Words.count.go(ws, 0n),
    N.Nat.add_zero(Wo.Words.count.go(ws, 0n)))

# ---------------------------------------------------------------------------
# A leaf, and then the tree.
# ---------------------------------------------------------------------------

law PSet.count_leaf_is_length:
  for +s: S.PSet
  {S.PSet.count.leaf(s)
    == List.length(&2, U32, S.PSet.leaf_members(s)) : Nat}

def PSet.count_leaf_is_length(s):
  match s:
    case S.PZero{}:
      {==}
    case S.PFull{}:
      %E.Nat.sym(List.length(&2, U32,
          S.PSet.range(4096n, 4095, Nil{})), Nat.add(4096n, 0n),
        List.length_range(4096n, 4095, Nil{}))
        : {4096n == _ : Nat}
      E.Nat.sym(Nat.add(4096n, 0n), 4096n, N.Nat.add_zero(4096n))
    case S.PSparse{offs}:
      {==}
    case S.PDense{ws}:
      Words.count_is_length(ws)
    case S.PBranch{l, h}:
      {==}

def PSet.count_is_length.leafarm(+s: S.PSet, +base: U32,
  +tail: List<&2, U32>)
  -> {List.length(&2, U32,
       List.append(&2, U32, S.PSet.shift(S.PSet.leaf_members(s), base),
         tail))
     == Nat.add(S.PSet.count.leaf(s), List.length(&2, U32, tail))
     : Nat}:
  %E.Nat.sym(List.length(&2, U32,
      List.append(&2, U32, S.PSet.shift(S.PSet.leaf_members(s), base),
        tail)),
    Nat.add(List.length(&2, U32,
      S.PSet.shift(S.PSet.leaf_members(s), base)),
      List.length(&2, U32, tail)),
    List.length_append(S.PSet.shift(S.PSet.leaf_members(s), base),
      tail))
    : {_ == Nat.add(S.PSet.count.leaf(s),
         List.length(&2, U32, tail)) : Nat}
  %E.Nat.sym(List.length(&2, U32,
      S.PSet.shift(S.PSet.leaf_members(s), base)),
    List.length(&2, U32, S.PSet.leaf_members(s)),
    List.length_shift(S.PSet.leaf_members(s), base))
    : {Nat.add(_, List.length(&2, U32, tail))
      == Nat.add(S.PSet.count.leaf(s),
           List.length(&2, U32, tail)) : Nat}
  %PSet.count_leaf_is_length(s)
    : {Nat.add(_, List.length(&2, U32, tail))
      == Nat.add(S.PSet.count.leaf(s),
           List.length(&2, U32, tail)) : Nat}
  {==}

def PSet.count_is_length.listarm(+xs: List<&2, U32>, +base: U32,
  +tail: List<&2, U32>)
  -> {List.length(&2, U32,
       List.append(&2, U32, S.PSet.shift(xs, base), tail))
     == Nat.add(List.length(&2, U32, xs),
          List.length(&2, U32, tail)) : Nat}:
  %E.Nat.sym(List.length(&2, U32,
      List.append(&2, U32, S.PSet.shift(xs, base), tail)),
    Nat.add(List.length(&2, U32, S.PSet.shift(xs, base)),
      List.length(&2, U32, tail)),
    List.length_append(S.PSet.shift(xs, base), tail))
    : {_ == Nat.add(List.length(&2, U32, xs),
         List.length(&2, U32, tail)) : Nat}
  %E.Nat.sym(List.length(&2, U32, S.PSet.shift(xs, base)),
    List.length(&2, U32, xs), List.length_shift(xs, base))
    : {Nat.add(_, List.length(&2, U32, tail))
      == Nat.add(List.length(&2, U32, xs),
           List.length(&2, U32, tail)) : Nat}
  {==}

law PSet.count_is_length:
  for +d: Nat
  for +s: S.PSet
  for +base: U32
  for +tail: List<&2, U32>
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {List.length(&2, U32,
     S.PSet.members(d, s, base, S.PSet.half(d), tail))
   == Nat.add(S.PSet.count(d, s, S.PSet.half(d)),
        List.length(&2, U32, tail)) : Nat}

def PSet.count_is_length(d, s, base, tail, lt):
  match d:
    case 0n:
      PSet.count_is_length.leafarm(s, base, tail)
    case 1n+p:
      match s:
        case S.PZero{}:
          {==}
        case S.PSparse{offs}:
          PSet.count_is_length.listarm(offs, base, tail)
        case S.PDense{ws}:
          %E.Nat.sym(List.length(&2, U32,
              List.append(&2, U32,
                S.PSet.shift(Wo.Words.members(ws, 0), base), tail)),
            Nat.add(List.length(&2, U32, Wo.Words.members(ws, 0)),
              List.length(&2, U32, tail)),
            PSet.count_is_length.listarm(Wo.Words.members(ws, 0), base,
              tail))
            : {_ == Nat.add(Wo.Words.count(ws),
                 List.length(&2, U32, tail)) : Nat}
          %E.Nat.sym(Wo.Words.count(ws),
            List.length(&2, U32, Wo.Words.members(ws, 0)),
            Words.count_is_length(ws))
            : {Nat.add(List.length(&2, U32, Wo.Words.members(ws, 0)),
                List.length(&2, U32, tail))
              == Nat.add(_, List.length(&2, U32, tail)) : Nat}
          {==}
        case S.PFull{}:
          List.length_range(
            Nat.add(U32.to_nat(U32.shln(1, 12n+p)),
              U32.to_nat(U32.shln(1, 12n+p))),
            (base + U32.shln(1, 12n+p) + U32.shln(1, 12n+p) - 1 : U32),
            tail)
        case S.PBranch{lo, hi}:
          %E.U32.sym(U32.shr(U32.shln(1, 12n+p)), U32.shln(1, 11n+p),
            Dc.U32.shr_shln_one(11n+p, lt))
            : {List.length(&2, U32,
                S.PSet.members(p, lo, base, _,
                  S.PSet.members(p, hi,
                    (base + U32.shln(1, 12n+p) : U32), _, tail)))
              == Nat.add(Nat.add(S.PSet.count(p, lo, _),
                   S.PSet.count(p, hi, _)),
                   List.length(&2, U32, tail)) : Nat}
          %E.Nat.sym(List.length(&2, U32,
              S.PSet.members(p, lo, base, S.PSet.half(p),
                S.PSet.members(p, hi,
                  (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                  tail))),
            Nat.add(S.PSet.count(p, lo, S.PSet.half(p)),
              List.length(&2, U32,
                S.PSet.members(p, hi,
                  (base + U32.shln(1, 12n+p) : U32), S.PSet.half(p),
                  tail))),
            PSet.count_is_length(p, lo, base,
              S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
                S.PSet.half(p), tail), Dc.Nat.gt_down(32n, 11n+p, lt)))
            : {_ == Nat.add(Nat.add(S.PSet.count(p, lo,
                 S.PSet.half(p)),
                 S.PSet.count(p, hi, S.PSet.half(p))),
                 List.length(&2, U32, tail)) : Nat}
          %E.Nat.sym(List.length(&2, U32,
              S.PSet.members(p, hi, (base + U32.shln(1, 12n+p) : U32),
                S.PSet.half(p), tail)),
            Nat.add(S.PSet.count(p, hi, S.PSet.half(p)),
              List.length(&2, U32, tail)),
            PSet.count_is_length(p, hi,
              (base + U32.shln(1, 12n+p) : U32), tail,
              Dc.Nat.gt_down(32n, 11n+p, lt)))
            : {Nat.add(S.PSet.count(p, lo, S.PSet.half(p)), _)
              == Nat.add(Nat.add(S.PSet.count(p, lo, S.PSet.half(p)),
                   S.PSet.count(p, hi, S.PSet.half(p))),
                   List.length(&2, U32, tail)) : Nat}
          E.Nat.sym(Nat.add(Nat.add(S.PSet.count(p, lo,
            S.PSet.half(p)), S.PSet.count(p, hi, S.PSet.half(p))),
            List.length(&2, U32, tail)),
            Nat.add(S.PSet.count(p, lo, S.PSet.half(p)),
              Nat.add(S.PSet.count(p, hi, S.PSet.half(p)),
                List.length(&2, U32, tail))),
            N.Nat.add_assoc(S.PSet.count(p, lo, S.PSet.half(p)),
              S.PSet.count(p, hi, S.PSet.half(p)),
              List.length(&2, U32, tail)))

law PSet.count_is_to_list_length:
  for +d: Nat
  for +s: S.PSet
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {List.length(&2, U32, S.PSet.to_list(d, s))
    == S.PSet.count(d, s, S.PSet.half(d)) : Nat}

def PSet.count_is_to_list_length(d, s, lt):
  %E.Nat.sym(List.length(&2, U32,
      S.PSet.members(d, s, 0, S.PSet.half(d), Nil{})),
    Nat.add(S.PSet.count(d, s, S.PSet.half(d)), 0n),
    PSet.count_is_length(d, s, 0, Nil{}, lt))
    : {_ == S.PSet.count(d, s, S.PSet.half(d)) : Nat}
  N.Nat.add_zero(S.PSet.count(d, s, S.PSet.half(d)))
