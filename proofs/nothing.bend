# proofs/nothing.bend -- an empty set enumerates to nothing.
#
# `PSet.empty_p` answers `True{}` for a set with no members, and
# `PSet.to_list` walks a set into its members. This file connects them: a set
# the emptiness test accepts enumerates to the empty list. Not "to a list
# with no members" -- to `Nil{}` itself.
#
# It is worth the work because enumeration is where the algebra hands over to
# everything else. The specification closure takes `post` of a set by walking
# it to a list and gathering successors, so "the closure of an empty set is
# empty" is really this lemma plus one step; and that is what admits the
# rewrite `Reach(Empty) = Empty`, which is the one rewrite in
# query/rewrite.bend that is not a Boolean identity.
#
# The tile case is the only real work. A dense leaf's members come back from
# a walk that shifts the word down thirty-two times and conses when the low
# bit is one, so "no bits set" has to be carried through the walk in the
# shape the walk has -- as a count of low bits rather than as a bit vector.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./count.bend as Ct
import ./popcount.bend as PP
import ./leaf.bend as Lf
import ./empty.bend as Em
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/set.bend as S
import ../closure/graph.bend as G
import ../spec/closure.bend as Sp

# ---------------------------------------------------------------------------
# One word.
# ---------------------------------------------------------------------------

law Word.bits_rev_of_zero:
  for +k: Nat
  for +w: U32
  for +ord: U32
  for +acc: List<&2, U32>
  for +z: {W.U32.lowcount(k, w) == 0n : Nat}
  {Wo.Words.bits_rev(k, w, ord, acc) == acc : List<&2, U32>}

def Word.bits_rev_of_zero(k, w, ord, acc, z):
  match k:
    case 0n:
      {==}
    case 1n+j:
      %E.Nat.sym(W.U32.low(w), 0n,
        Ct.Nat.add_zero_left(W.U32.low(w),
          W.U32.lowcount(j, U32.shr(w)), z))
        : {Wo.Words.bits_rev(j, U32.shr(w), (ord + 1 : U32),
            Wo.Words.cons_if(Wo.Nat.is_one(_), ord, acc)) == acc
          : List<&2, U32>}
      Word.bits_rev_of_zero(j, U32.shr(w), (ord + 1 : U32), acc,
        Ct.Nat.add_zero_right(W.U32.low(w),
          W.U32.lowcount(j, U32.shr(w)), z))

law Word.lowcount_of_count:
  for +w: U32
  for +t: List<&2, U32>
  for +z: {Wo.Words.count(Con{w, t}) == 0n : Nat}
  {W.U32.lowcount(32n, w) == 0n : Nat}

def Word.lowcount_of_count(w, t, z):
  Equal.trans(Nat, W.U32.lowcount(32n, w), W.U32.card(32n, w), 0n,
    PP.U32.lowcount_card(32n, w),
    Ct.Words.count_zero.head(w, t, z))

# ---------------------------------------------------------------------------
# A tile.
# ---------------------------------------------------------------------------

law Words.members_go_of_count:
  for +ws: List<&2, U32>
  for +ord: U32
  for +acc: List<&2, U32>
  for +z: {Wo.Words.count(ws) == 0n : Nat}
  {Wo.Words.members.go(ws, ord, acc) == acc : List<&2, U32>}

def Words.members_go_of_count(ws, ord, acc, z):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      %E.List.sym(U32, Wo.Words.bits_rev(32n, w, ord, acc), acc,
        Word.bits_rev_of_zero(32n, w, ord, acc,
          Word.lowcount_of_count(w, t, z)))
        : {Wo.Words.members.go(t, (ord + 32 : U32), _) == acc
          : List<&2, U32>}
      Words.members_go_of_count(t, (ord + 32 : U32), acc,
        Ct.Words.count_zero.tail(w, t, z))

law Word.lowcount_of_is_zero:
  for +w: U32
  for +e: {U32.is_zero(w) == True{} : Bool}
  {W.U32.lowcount(32n, w) == 0n : Nat}

def Word.lowcount_of_is_zero(w, e):
  %E.U32.sym(w, 0, E.U32.eq_reflect(w, 0, e))
    : {W.U32.lowcount(32n, _) == 0n : Nat}
  {==}

law Words.members_go_of_any_go:
  for +ws: List<&2, U32>
  for +found: Bool
  for +z: {Wo.Words.any.go(ws, found) == False{} : Bool}
  for +ord: U32
  for +acc: List<&2, U32>
  {Wo.Words.members.go(ws, ord, acc) == acc : List<&2, U32>}

def Words.members_go_of_any_go(ws, found, z, ord, acc):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      match found:
        case True{}:
          E.Bool.noconf.r({Wo.Words.members.go(Con{w, t}, ord, acc)
            == acc : List<&2, U32>}, z)
        case False{}:
          %E.List.sym(U32, Wo.Words.bits_rev(32n, w, ord, acc), acc,
            Word.bits_rev_of_zero(32n, w, ord, acc,
              Word.lowcount_of_is_zero(w,
                Em.Words.not_found(U32.is_zero(w), t, z))))
            : {Wo.Words.members.go(t, (ord + 32 : U32), _) == acc
              : List<&2, U32>}
          Words.members_go_of_any_go(t, Bool.not(U32.is_zero(w)), z,
            (ord + 32 : U32), acc)

law Words.members_of_any:
  for +ws: List<&2, U32>
  for +base: U32
  for +z: {Wo.Words.any(ws) == False{} : Bool}
  {Wo.Words.members(ws, base) == Nil{} : List<&2, U32>}

def Words.members_of_any(ws, base, z):
  %E.List.sym(U32, Wo.Words.members.go(ws, base, Nil{}), Nil{},
    Words.members_go_of_any_go(ws, False{}, z, base, Nil{}))
    : {List.reverse(&2, U32, _) == Nil{} : List<&2, U32>}
  {==}

law Words.members_of_count:
  for +ws: List<&2, U32>
  for +base: U32
  for +z: {Wo.Words.count(ws) == 0n : Nat}
  {Wo.Words.members(ws, base) == Nil{} : List<&2, U32>}

def Words.members_of_count(ws, base, z):
  %E.List.sym(U32, Wo.Words.members.go(ws, base, Nil{}), Nil{},
    Words.members_go_of_count(ws, base, Nil{}, z))
    : {List.reverse(&2, U32, _) == Nil{} : List<&2, U32>}
  {==}

# ---------------------------------------------------------------------------
# A set.
# ---------------------------------------------------------------------------

law List.nil_of_length:
  for +xs: List<&2, U32>
  for +z: {List.length(&2, U32, xs) == 0n : Nat}
  {xs == Nil{} : List<&2, U32>}

def List.nil_of_length(xs, z):
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      E.Nat.noconf2({Con{x, t} == Nil{} : List<&2, U32>},
        List.length(&2, U32, t), z)

law PSet.members_of_empty:
  for +d: Nat
  for +s: S.PSet
  for +base: U32
  for +h: U32
  for +tail: List<&2, U32>
  for +z: {S.PSet.is_empty(d, s, True{}) == True{} : Bool}
  {S.PSet.members(d, s, base, h, tail) == tail : List<&2, U32>}

def PSet.members_of_empty(d, s, base, h, tail, z):
  match d:
    case 0n:
      match s:
        case S.PZero{}:
          {==}
        case S.PBranch{l, r}:
          {==}
        case S.PFull{}:
          E.Bool.noconf({S.PSet.members(0n, S.PFull{}, base, h, tail)
            == tail : List<&2, U32>}, z)
        case S.PSparse{offs}:
          %E.List.sym(U32, offs, Nil{},
            List.nil_of_length(offs,
              Lf.Nat.is_eq_reflect(List.length(&2, U32, offs), 0n, z)))
            : {List.append(&2, U32, S.PSet.shift(_, base), tail) == tail
              : List<&2, U32>}
          {==}
        case S.PDense{ws}:
          %E.List.sym(U32, Wo.Words.members(ws, 0), Nil{},
            Words.members_of_count(ws, 0,
              Lf.Nat.is_eq_reflect(Wo.Words.count(ws), 0n, z)))
            : {List.append(&2, U32, S.PSet.shift(_, base), tail) == tail
              : List<&2, U32>}
          {==}
    case 1n+p:
      match s:
        case S.PZero{}:
          {==}
        case S.PFull{}:
          E.Bool.noconf({S.PSet.members(1n+p, S.PFull{}, base, h, tail)
            == tail : List<&2, U32>}, z)
        case S.PSparse{offs}:
          %E.List.sym(U32, offs, Nil{},
            List.nil_of_length(offs, Em.PSet.nil_of_is_empty(offs, z)))
            : {List.append(&2, U32, S.PSet.shift(_, base), tail) == tail
              : List<&2, U32>}
          {==}
        case S.PDense{ws}:
          %E.List.sym(U32, Wo.Words.members(ws, 0), Nil{},
            Words.members_of_any(ws, 0, Em.PSet.not_any(ws, z)))
            : {List.append(&2, U32, S.PSet.shift(_, base), tail) == tail
              : List<&2, U32>}
          {==}
        case S.PBranch{lo, hi}:
          %E.List.sym(U32,
            S.PSet.members(p, hi, (base + h : U32), U32.shr(h), tail), tail,
            PSet.members_of_empty(p, hi, (base + h : U32), U32.shr(h), tail,
              Em.PSet.empty_hi(p, lo, hi, z)))
            : {S.PSet.members(p, lo, base, U32.shr(h), _) == tail
              : List<&2, U32>}
          PSet.members_of_empty(p, lo, base, U32.shr(h), tail,
            Em.PSet.empty_lo(p, lo, hi, z))

law PSet.to_list_of_empty:
  for +d: Nat
  for +s: S.PSet
  for +z: {S.PSet.empty_p(d, s) == True{} : Bool}
  {S.PSet.to_list(d, s) == Nil{} : List<&2, U32>}

def PSet.to_list_of_empty(d, s, z):
  PSet.members_of_empty(d, s, 0, S.PSet.half(d), Nil{}, z)

# ---------------------------------------------------------------------------
# Closing nothing, pointwise.
#
# `closing_nothing_gives_nothing` in LAWS.bend is the equation at `PZero{}`
# itself. That is not enough for the rewriter, which decides with
# `PSet.empty_p` and so may be looking at a set that has no members without
# being `PZero{}` -- a literal read from a store, say, whose leaves are all
# empty. This is the version that covers those: closing a set the emptiness
# test accepts gives a set the emptiness test accepts.
#
# One round does it, and then induction on the fuel. The round takes `post`
# of the set, which walks it to a list -- empty, by the lemma above -- gathers
# the successors of nothing, and builds a set from the empty list, which is
# `PZero{}`. The union with `PZero{}` is then the set itself at every shape
# `empty_p` admits.
# ---------------------------------------------------------------------------

law Spec.post_of_empty:
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +x: S.PSet
  for +z: {S.PSet.empty_p(sd, x) == True{} : Bool}
  {Sp.Spec.post(td, g, sd, x) == S.PZero{} : S.PSet}

def Spec.post_of_empty(td, g, sd, x, z):
  %E.List.sym(U32, S.PSet.to_list(sd, x), Nil{},
    PSet.to_list_of_empty(sd, x, z))
    : {S.PSet.from_list(sd, G.Graph.gather(td, g, _, Nil{}))
      == S.PZero{} : S.PSet}
  {==}

law PSet.empty_union_zero:
  for +p: Nat
  for +s: S.PSet
  for +z: {S.PSet.empty_p(1n+p, s) == True{} : Bool}
  {S.PSet.empty_p(1n+p, S.PSet.union(1n+p, s, S.PZero{}))
    == True{} : Bool}

def PSet.empty_union_zero(p, s, z):
  match s:
    case S.PZero{}:
      {==}
    case S.PSparse{o}:
      {==}
    case S.PDense{w}:
      {==}
    case S.PBranch{al, ah}:
      z
    case S.PFull{}:
      E.Bool.noconf({S.PSet.empty_p(1n+p,
        S.PSet.union(1n+p, S.PFull{}, S.PZero{})) == True{} : Bool}, z)

law Spec.step_of_empty:
  for +td: Nat
  for +g: G.Graph()
  for +p: Nat
  for +x: S.PSet
  for +z: {S.PSet.empty_p(1n+p, x) == True{} : Bool}
  {S.PSet.empty_p(1n+p, Sp.Spec.step(td, g, 1n+p, x)) == True{} : Bool}

def Spec.step_of_empty(td, g, p, x, z):
  %Equal.sym(S.PSet, Sp.Spec.post(td, g, 1n+p, x), S.PZero{},
    Spec.post_of_empty(td, g, 1n+p, x, z))
    : {S.PSet.empty_p(1n+p, S.PSet.union(1n+p, x, _)) == True{} : Bool}
  PSet.empty_union_zero(p, x, z)

law Spec.iter_of_empty:
  for +fuel: Nat
  for +td: Nat
  for +g: G.Graph()
  for +p: Nat
  for +x: S.PSet
  for +z: {S.PSet.empty_p(1n+p, x) == True{} : Bool}
  {S.PSet.empty_p(1n+p, Sp.Spec.iter(fuel, td, g, 1n+p, x))
    == True{} : Bool}

def Spec.iter_of_empty(fuel, td, g, p, x, z):
  match fuel:
    case 0n:
      z
    case 1n+f:
      Spec.iter_of_empty(f, td, g, p, Sp.Spec.step(td, g, 1n+p, x),
        Spec.step_of_empty(td, g, p, x, z))

law Spec.closure_of_empty:
  for +n: Nat
  for +td: Nat
  for +g: G.Graph()
  for +p: Nat
  for +r: S.PSet
  for +z: {S.PSet.empty_p(1n+p, r) == True{} : Bool}
  {S.PSet.empty_p(1n+p, Sp.Spec.closure(n, td, g, 1n+p, r))
    == True{} : Bool}

def Spec.closure_of_empty(n, td, g, p, r, z):
  Spec.iter_of_empty(1n+n, td, g, p, r, z)
