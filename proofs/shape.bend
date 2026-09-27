# proofs/shape.bend -- the part of structural validity the algebra uses.
#
# `PSet.valid` (core/set.bend) is the check a decoded generation has to pass
# before anything answers from it, and it says three things: no sparse or
# dense payload above a leaf, a dense leaf is exactly 128 words, and a sparse
# leaf's offsets are ascending and in range.
#
# The set laws need the first two and never the third. That is not an
# accident: the offsets of a sparse leaf are read back through `Ords.elem`,
# which searches the whole list, so their order changes how fast a lookup is
# and not what it answers. The ascending condition is there for the store and
# for `D-01`, not for the algebra.
#
# So this file separates them. `PSet.wf` is the same recursion as
# `PSet.valid` with the ordering condition dropped, `PSet.valid_wf` says every
# valid set is `wf`, and the set proofs are stated over `wf`. Two things come
# of that. The published laws are unchanged and still read `PSet.valid`,
# because that is the predicate the product checks; but they are now proved
# from a weaker hypothesis, which makes them apply to more values -- and, the
# reason this file exists, `wf` is preserved by union, intersection and
# difference, which `valid` is not known to be. Preservation is what an
# induction over a query's syntax needs, because it has to know the operands
# of the next operation are still well shaped.
#
# Nothing here is a production symbol: `wf` is a proof-only predicate, and
# `PSet.valid` remains the one thing checked on load.

import Base
import ./eq.bend as E
import ./leaf.bend as Lf
import ../core/words.bend as Wo
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# The predicate.
# ---------------------------------------------------------------------------

def PSet.wf.leaf(s: S.PSet) -> Bool:
  match s:
    case S.PZero{}:
      True{}
    case S.PFull{}:
      True{}
    case S.PSparse{offs}:
      True{}
    case S.PDense{ws}:
      Nat.is_eq(List.length(&2, U32, ws), 128n)
    case S.PBranch{l, h}:
      False{}

def PSet.wf(+d: Nat, s: S.PSet, ok: Bool) -> Bool:
  match d:
    case 0n:
      Bool.and(ok, PSet.wf.leaf(s))
    case 1n+p:
      match s:
        case S.PZero{}:
          ok
        case S.PFull{}:
          ok
        case S.PSparse{offs}:
          False{}
        case S.PDense{ws}:
          False{}
        case S.PBranch{lo, hi}:
          match ok:
            case False{}:
              False{}
            case True{}:
              PSet.wf(p, hi, PSet.wf(p, lo, True{}))

# ---------------------------------------------------------------------------
# Every valid set is well shaped. The only place the two differ is a sparse
# leaf, where `valid` asks for ascending offsets and `wf` asks for nothing.
# ---------------------------------------------------------------------------

law PSet.valid_leaf_wf:
  for +s: S.PSet
  for +v: {S.PSet.valid.leaf(s) == True{} : Bool}
  {PSet.wf.leaf(s) == True{} : Bool}

def PSet.valid_leaf_wf(s, v):
  match s:
    case S.PZero{}:
      {==}
    case S.PFull{}:
      {==}
    case S.PSparse{offs}:
      {==}
    case S.PDense{ws}:
      v
    case S.PBranch{l, h}:
      v

law PSet.wf_zero:
  for +d: Nat
  {PSet.wf(d, S.PZero{}, True{}) == True{} : Bool}

def PSet.wf_zero(d):
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

law PSet.wf_full:
  for +d: Nat
  {PSet.wf(d, S.PFull{}, True{}) == True{} : Bool}

def PSet.wf_full(d):
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

law PSet.wf_false:
  for +d: Nat
  for +s: S.PSet
  {PSet.wf(d, s, False{}) == False{} : Bool}

def PSet.wf_false(d, s):
  match d:
    case 0n:
      {==}
    case 1n+p:
      match s:
        case S.PZero{}:
          {==}
        case S.PFull{}:
          {==}
        case S.PSparse{o}:
          {==}
        case S.PDense{w}:
          {==}
        case S.PBranch{lo, hi}:
          {==}

def PSet.wf_at(+p: Nat, +hi: S.PSet, a: Bool) -> Bool:
  PSet.wf(p, hi, a)

law PSet.wf_lo.on:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +a: Bool
  for +ea: {a == PSet.wf(p, lo, True{}) : Bool}
  for +v: {PSet.wf(1n+p, S.PBranch{lo, hi}, True{}) == True{} : Bool}
  {PSet.wf(p, lo, True{}) == True{} : Bool}

def PSet.wf_lo.on(p, lo, hi, a, ea, v):
  match a:
    case True{}:
      E.Bool.sym(a, PSet.wf(p, lo, True{}), ea)
    case False{}:
      E.Bool.noconf({PSet.wf(p, lo, True{}) == True{} : Bool},
        Equal.trans(Bool, False{}, PSet.wf(p, hi, False{}), True{},
          E.Bool.sym(PSet.wf(p, hi, False{}), False{},
            PSet.wf_false(p, hi)),
          Equal.trans(Bool, PSet.wf(p, hi, False{}),
            PSet.wf(p, hi, PSet.wf(p, lo, True{})), True{},
            Equal.cong(Bool, Bool, PSet.wf_at(p, hi), False{},
              PSet.wf(p, lo, True{}), ea),
            v)))

law PSet.wf_lo:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +v: {PSet.wf(1n+p, S.PBranch{lo, hi}, True{}) == True{} : Bool}
  {PSet.wf(p, lo, True{}) == True{} : Bool}

def PSet.wf_lo(p, lo, hi, v):
  PSet.wf_lo.on(p, lo, hi, PSet.wf(p, lo, True{}), {==}, v)

law PSet.wf_hi:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +v: {PSet.wf(1n+p, S.PBranch{lo, hi}, True{}) == True{} : Bool}
  {PSet.wf(p, hi, True{}) == True{} : Bool}

def PSet.wf_hi(p, lo, hi, v):
  %PSet.wf_lo(p, lo, hi, v)
    : {PSet.wf(p, hi, _) == True{} : Bool}
  v

# The branch, rebuilt: two well-shaped halves make a well-shaped branch.
law PSet.wf_branch:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +vl: {PSet.wf(p, lo, True{}) == True{} : Bool}
  for +vh: {PSet.wf(p, hi, True{}) == True{} : Bool}
  {PSet.wf(1n+p, S.PBranch{lo, hi}, True{}) == True{} : Bool}

def PSet.wf_branch(p, lo, hi, vl, vh):
  %E.Bool.sym(PSet.wf(p, lo, True{}), True{}, vl)
    : {PSet.wf(p, hi, _) == True{} : Bool}
  vh

law PSet.valid_wf:
  for +d: Nat
  for +s: S.PSet
  for +v: {S.PSet.valid(d, s, True{}) == True{} : Bool}
  {PSet.wf(d, s, True{}) == True{} : Bool}

def PSet.valid_wf(d, s, v):
  match d:
    case 0n:
      PSet.valid_leaf_wf(s, v)
    case 1n+p:
      match s:
        case S.PZero{}:
          {==}
        case S.PFull{}:
          {==}
        case S.PSparse{o}:
          v
        case S.PDense{w}:
          v
        case S.PBranch{lo, hi}:
          PSet.wf_branch(p, lo, hi,
            PSet.valid_wf(p, lo, Lf.PSet.valid_lo(p, lo, hi, v)),
            PSet.valid_wf(p, hi, Lf.PSet.valid_hi(p, lo, hi, v)))

# ---------------------------------------------------------------------------
# What `wf` rules out above a leaf, and what it gives at one.
# ---------------------------------------------------------------------------

def PSet.is_node(s: S.PSet) -> Bool:
  match s:
    case S.PZero{}:
      True{}
    case S.PFull{}:
      True{}
    case S.PBranch{lo, hi}:
      True{}
    case S.PSparse{o}:
      False{}
    case S.PDense{w}:
      False{}

law PSet.wf_is_node:
  for +p: Nat
  for +s: S.PSet
  for +ok: {PSet.wf(1n+p, s, True{}) == True{} : Bool}
  {PSet.is_node(s) == True{} : Bool}

def PSet.wf_is_node(p, s, ok):
  match s:
    case S.PZero{}:
      {==}
    case S.PFull{}:
      {==}
    case S.PBranch{lo, hi}:
      {==}
    case S.PSparse{o}:
      E.Bool.noconf({PSet.is_node(S.PSparse{o}) == True{} : Bool}, ok)
    case S.PDense{w}:
      E.Bool.noconf({PSet.is_node(S.PDense{w}) == True{} : Bool}, ok)

law PSet.wf_leaf_words_width:
  for +s: S.PSet
  for +v: {PSet.wf.leaf(s) == True{} : Bool}
  {List.length(&2, U32, S.PSet.leaf_words(s)) == 128n : Nat}

def PSet.wf_leaf_words_width(s, v):
  match s:
    case S.PZero{}:
      Lf.Words.length_zeros(128n)
    case S.PFull{}:
      Lf.Words.length_ones(128n)
    case S.PBranch{l, h}:
      E.Bool.noconf({List.length(&2, U32, S.PSet.leaf_words(
        S.PBranch{l, h})) == 128n : Nat}, v)
    case S.PDense{ws}:
      Lf.Nat.is_eq_reflect(List.length(&2, U32, ws), 128n, v)
    case S.PSparse{offs}:
      %E.Nat.sym(
        List.length(&2, U32, S.PSet.spread(offs, Wo.Words.zeros(128n))),
        List.length(&2, U32, Wo.Words.zeros(128n)),
        Lf.Words.length_spread(offs, Wo.Words.zeros(128n)))
        : {_ == 128n : Nat}
      Lf.Words.length_zeros(128n)
