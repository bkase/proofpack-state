# proofs/collapse.bend -- the Zero/Full collapses (part of law S-02).
#
# SPEC 5.3 lets a branch whose halves are both empty become `PZero{}`, and one
# whose halves are both full become `PFull{}`. That is what makes structural
# pruning work: a difference against a pruned subtree costs nothing because
# the subtree is one node rather than a tree of them. `PSet.mk` is where the
# collapse happens, on every union, intersection and difference at a node.
#
# This file proves the collapse is semantics-preserving: `PSet.mk(lo, hi)` has
# exactly the members of `PBranch{lo, hi}`, at every depth and for every
# ordinal. No hypothesis -- not validity, not a range on the ordinal -- because
# the collapse only ever fires when both halves already answer the same thing
# everywhere.
#
# It is the part of S-02 that the tree layer contributes on its own. What S-02
# still needs is at the two ends: the leaf laws, and carrying an ordinal down
# a level, which is the addressing arithmetic LAWS.pending.bend lists.

import Base
import ./eq.bend as E
import ../core/set.bend as S

# An empty node is empty at every depth, and a full node is full at every
# depth. Both are immediate, but the collapse proof needs them as the two
# halves' common answer.

law PSet.mem_zero:
  for +d: Nat
  for +h: U32
  for +x: U32
  {S.PSet.mem(d, S.PZero{}, h, x) == False{} : Bool}

def PSet.mem_zero(d, h, x):
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

law PSet.mem_full:
  for +d: Nat
  for +h: U32
  for +x: U32
  {S.PSet.mem(d, S.PFull{}, h, x) == True{} : Bool}

def PSet.mem_full(d, h, x):
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

# ---------------------------------------------------------------------------
# The collapse. `PSet.mk` decides on the low half's shape, so the proof does
# too, and each arm then decides on the high half.
# ---------------------------------------------------------------------------

law PSet.mem_mk_z:
  for +p: Nat
  for +hi: S.PSet
  for +h: U32
  for +x: U32
  {S.PSet.mem(1n+p, S.PSet.mk.z(S.PZero{}, hi), h, x)
    == S.PSet.mem(1n+p, S.PBranch{S.PZero{}, hi}, h, x) : Bool}

# `PSet.pick` of two `PZero{}` halves is `PZero{}` whichever way the test
# goes, which is what the collapsed arm above needs.
law PSet.mem_pick_zero:
  for +p: Nat
  for +h: U32
  for +x: U32
  {False{} == S.PSet.mem(p,
    S.PSet.pick(U32.is_lt(x, h), S.PZero{}, S.PZero{}), U32.shr(h),
    S.PSet.rebase(U32.is_lt(x, h), h, x)) : Bool}

law PSet.pick_zero_go:
  for +p: Nat
  for +h: U32
  for +x: U32
  for +b: Bool
  {False{} == S.PSet.mem(p, S.PSet.pick(b, S.PZero{}, S.PZero{}),
    U32.shr(h), S.PSet.rebase(b, h, x)) : Bool}

def PSet.pick_zero_go(p, h, x, b):
  match b:
    case True{}:
      E.Bool.sym(S.PSet.mem(p, S.PZero{}, U32.shr(h), x), False{},
        PSet.mem_zero(p, U32.shr(h), x))
    case False{}:
      E.Bool.sym(S.PSet.mem(p, S.PZero{}, U32.shr(h), U32.sub(x, h)),
        False{},
        PSet.mem_zero(p, U32.shr(h), U32.sub(x, h)))

def PSet.mem_pick_zero(p, h, x):
  PSet.pick_zero_go(p, h, x, U32.is_lt(x, h))

def PSet.mem_mk_z(p, hi, h, x):
  match hi:
    case S.PZero{}:
      # Both halves empty: the branch collapses to `PZero{}`, and whichever
      # half the ordinal falls in answers `False{}` anyway.
      PSet.mem_pick_zero(p, h, x)
    case S.PFull{}:
      {==}
    case S.PSparse{o}:
      {==}
    case S.PDense{w}:
      {==}
    case S.PBranch{a, b}:
      {==}

# The full half, the same way.

law PSet.pick_full_go:
  for +p: Nat
  for +h: U32
  for +x: U32
  for +b: Bool
  {True{} == S.PSet.mem(p, S.PSet.pick(b, S.PFull{}, S.PFull{}),
    U32.shr(h), S.PSet.rebase(b, h, x)) : Bool}

def PSet.pick_full_go(p, h, x, b):
  match b:
    case True{}:
      E.Bool.sym(S.PSet.mem(p, S.PFull{}, U32.shr(h), x), True{},
        PSet.mem_full(p, U32.shr(h), x))
    case False{}:
      E.Bool.sym(S.PSet.mem(p, S.PFull{}, U32.shr(h), U32.sub(x, h)),
        True{},
        PSet.mem_full(p, U32.shr(h), U32.sub(x, h)))

law PSet.mem_mk_f:
  for +p: Nat
  for +hi: S.PSet
  for +h: U32
  for +x: U32
  {S.PSet.mem(1n+p, S.PSet.mk.f(S.PFull{}, hi), h, x)
    == S.PSet.mem(1n+p, S.PBranch{S.PFull{}, hi}, h, x) : Bool}

def PSet.mem_mk_f(p, hi, h, x):
  match hi:
    case S.PFull{}:
      PSet.pick_full_go(p, h, x, U32.is_lt(x, h))
    case S.PZero{}:
      {==}
    case S.PSparse{o}:
      {==}
    case S.PDense{w}:
      {==}
    case S.PBranch{a, b}:
      {==}

# ---------------------------------------------------------------------------
# The collapse, over any low half. `PSet.mk` reads the low half's shape
# through `is_zero` and `is_full`, so the proof takes the same two Booleans as
# parameters and matches them.
# ---------------------------------------------------------------------------

law PSet.mem_mk_hi:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +h: U32
  for +x: U32
  for +lz: Bool
  for +lf: Bool
  for +elz: {lz == S.PSet.is_zero(lo) : Bool}
  for +elf: {lf == S.PSet.is_full(lo) : Bool}
  {S.PSet.mem(1n+p, S.PSet.mk.hi(lo, hi, lz, lf), h, x)
    == S.PSet.mem(1n+p, S.PBranch{lo, hi}, h, x) : Bool}

law PSet.mem_mk:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +h: U32
  for +x: U32
  {S.PSet.mem(1n+p, S.PSet.mk(lo, hi), h, x)
    == S.PSet.mem(1n+p, S.PBranch{lo, hi}, h, x) : Bool}

law PSet.is_zero_eq:
  for +s: S.PSet
  for +ok: {S.PSet.is_zero(s) == True{} : Bool}
  {S.PZero{} == s : S.PSet}

def PSet.is_zero_eq(s, ok):
  match s:
    case S.PZero{}:
      {==}
    case S.PFull{}:
      E.Bool.noconf({S.PZero{} == S.PFull{} : S.PSet}, ok)
    case S.PSparse{o}:
      E.Bool.noconf({S.PZero{} == S.PSparse{o} : S.PSet}, ok)
    case S.PDense{w}:
      E.Bool.noconf({S.PZero{} == S.PDense{w} : S.PSet}, ok)
    case S.PBranch{a, b}:
      E.Bool.noconf({S.PZero{} == S.PBranch{a, b} : S.PSet}, ok)

law PSet.is_full_eq:
  for +s: S.PSet
  for +ok: {S.PSet.is_full(s) == True{} : Bool}
  {S.PFull{} == s : S.PSet}

def PSet.is_full_eq(s, ok):
  match s:
    case S.PFull{}:
      {==}
    case S.PZero{}:
      E.Bool.noconf({S.PFull{} == S.PZero{} : S.PSet}, ok)
    case S.PSparse{o}:
      E.Bool.noconf({S.PFull{} == S.PSparse{o} : S.PSet}, ok)
    case S.PDense{w}:
      E.Bool.noconf({S.PFull{} == S.PDense{w} : S.PSet}, ok)
    case S.PBranch{a, b}:
      E.Bool.noconf({S.PFull{} == S.PBranch{a, b} : S.PSet}, ok)

def PSet.mem_mk_hi(p, lo, hi, h, x, lz, lf, elz, elf):
  match lz:
    case True{}:
      # `is_zero(lo)` is `True{}`, so `lo` is `PZero{}`.
      %PSet.is_zero_eq(lo, E.Bool.sym(True{}, S.PSet.is_zero(lo), elz))
        : {S.PSet.mem(1n+p, S.PSet.mk.z(_, hi), h, x)
            == S.PSet.mem(1n+p, S.PBranch{_, hi}, h, x) : Bool}
      PSet.mem_mk_z(p, hi, h, x)
    case False{}:
      match lf:
        case True{}:
          %PSet.is_full_eq(lo, E.Bool.sym(True{}, S.PSet.is_full(lo), elf))
            : {S.PSet.mem(1n+p, S.PSet.mk.f(_, hi), h, x)
                == S.PSet.mem(1n+p, S.PBranch{_, hi}, h, x) : Bool}
          PSet.mem_mk_f(p, hi, h, x)
        case False{}:
          {==}

def PSet.mem_mk(p, lo, hi, h, x):
  PSet.mem_mk_hi(p, lo, hi, h, x, S.PSet.is_zero(lo), S.PSet.is_full(lo),
    {==}, {==})

# `is_zero` and `is_full` are decisions about a constructor, so answering
# `True{}` names the constructor.

# ---------------------------------------------------------------------------
# What structural validity buys (law D-01, and the hypothesis S-02 carries).
#
# Above the leaf level the node operations read a sparse or dense payload as
# empty, while `PSet.mem` reads it as a member -- which is why the pointwise
# laws need `PSet.valid`. This says what `PSet.valid` actually rules out: at
# any depth above a leaf, a valid set is `PZero{}`, `PFull{}` or a branch,
# never a payload. It is the reason a decoded generation is checked on load
# (SPEC 6.5) rather than trusted.
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

law PSet.valid_is_node:
  for +p: Nat
  for +s: S.PSet
  for +ok: {S.PSet.valid(1n+p, s, True{}) == True{} : Bool}
  {PSet.is_node(s) == True{} : Bool}

def PSet.valid_is_node(p, s, ok):
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
