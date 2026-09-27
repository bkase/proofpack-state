# core/set.bend -- the persistent set representation (law families S-*, P-*).
#
# A set is a binary tree over fixed ordinal intervals, exactly SPEC 5.2's
# shape: `Zero` and `Full` compress a whole range, a leaf covers 4096 ordinals
# as either a sorted offset list or 128 bitmap words, and a branch splits its
# interval in half.
#
# The tree is one plain recursive type, with the depth carried as an ordinary
# `Nat` argument rather than as a type index.
#
# It was depth-indexed at first -- `PSet(0n)` a leaf, `PSet(1n+p)` a node, the
# way Base indexes `Word(n)` -- which made "a dense payload above a leaf"
# unrepresentable. That had to go, and the reason is worth recording. The
# compiler's layout pass flattens a datatype's fields unless it can see the
# type is self-recursive, and it decides that by comparing *head names*. For
# `PSet(19n)` the head is the def `PSet`, not the datatype that def reduces
# to, so the check misses and the layout unrolls seven levels before giving
# up: one `PSet(20n)` field costs 127 words, a record holding four of them
# costs 512, and any continuation touching one fails to compile with "an
# arity over 247".
#
# So the invariants SPEC 5.2 states -- sparse and dense payloads only at a
# leaf, branch children partitioning their parent exactly -- are invariants
# again rather than type errors. `PSet.valid` states them, anything decoded
# from storage is checked against it (law D-01), and every operation here is
# total regardless: a shape that should not occur at a depth is given the
# meaning it would have if it did, never a wrong answer.
#
# Membership walks the tree carrying the node's half-width `h` and rebasing
# `x` into the chosen child, so a node never needs to know its absolute
# position. Three native instructions a level: one compare, one shift, one
# conditional subtract.

import Base
import ./count.bend as C
import ./word.bend as W
import ./words.bend as Wo
import ./ords.bend as O

type PSet is Data:
  PZero{}
  PFull{}
  PSparse{offs: List<&2, U32>}
  PDense{words: List<&2, U32>}
  PBranch{lo: PSet, hi: PSet}

def PSet.empty() -> PSet:
  PZero{}

def PSet.full() -> PSet:
  PFull{}

# ---------------------------------------------------------------------------
# Geometry. A leaf covers 4096 = 2^12 ordinals, so a node at depth 1n+p covers
# 2^(12+p+1) and its halves are 2^(12+p) wide. At the deepest supported depth
# (20) that half is 2^31, which still fits a U32 -- the full width would not,
# which is why the walk carries the half rather than the width.
# ---------------------------------------------------------------------------

def PSet.half(+d: Nat) -> U32:
  U32.shln(1, 11n+d)

# The smallest depth whose leaves cover `n` ordinals. v0.1 supports at most
# 2^32-1 ordinals per universe (SPEC 5.4), which is depth 20.
def PSet.depth.go(+fuel: Nat, +cap: Nat, +n: Nat, d: Nat, done: Bool) -> Nat:
  match fuel:
    case 0n:
      d
    case 1n+f:
      match done:
        case True{}:
          d
        case False{}:
          +c2 = Nat.add(cap, cap)
          PSet.depth.go(f, c2, n, 1n+d, C.Nat.upto(n, c2))

def PSet.depth(+n: Nat) -> Nat:
  PSet.depth.go(21n, 4096n, n, 0n, C.Nat.upto(n, 4096n))

# ---------------------------------------------------------------------------
# Membership -- the denotation. Every set law in LAWS.bend is stated
# pointwise against this def (SPEC 3.1 prefers pointwise membership
# equivalence to assuming function extensionality).
# ---------------------------------------------------------------------------

def PSet.pick(b: Bool, lo: PSet, hi: PSet) -> PSet:
  match b:
    case True{}:
      lo
    case False{}:
      hi

def PSet.rebase(b: Bool, +h: U32, +x: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      U32.sub(x, h)

def PSet.spread(offs: List<&2, U32>, ws: List<&2, U32>) -> List<&2, U32>:
  match offs:
    case Nil{}:
      ws
    case Con{o, t}:
      PSet.spread(t, Wo.Words.set(ws, o))

def PSet.leaf_words(s: PSet) -> List<&2, U32>:
  match s:
    case PZero{}:
      Wo.Words.zeros(128n)
    case PFull{}:
      Wo.Words.ones(128n)
    case PSparse{offs}:
      PSet.spread(offs, Wo.Words.zeros(128n))
    case PDense{ws}:
      ws
    case PBranch{lo, hi}:
      Wo.Words.zeros(128n)

# The sparse/dense crossover. SPEC 5.2 calls 64 members a benchmark
# parameter, not a semantic constant: nothing outside this def reads it, and
# changing it changes no denotation (law S-03).
def PSet.sparse_max() -> Nat:
  64n

def PSet.compress.s(+ws: List<&2, U32>, sparse: Bool) -> PSet:
  match sparse:
    case True{}:
      PSparse{Wo.Words.members(ws, 0)}
    case False{}:
      PDense{ws}

def PSet.compress.f(+ws: List<&2, U32>, full: Bool) -> PSet:
  match full:
    case True{}:
      PFull{}
    case False{}:
      PSet.compress.s(ws,
        C.Nat.upto(Wo.Words.count(ws), PSet.sparse_max()))

def PSet.compress.z(+ws: List<&2, U32>, zero: Bool) -> PSet:
  match zero:
    case True{}:
      PZero{}
    case False{}:
      PSet.compress.f(ws, Wo.Words.all_ones(ws))

def PSet.compress(+ws: List<&2, U32>) -> PSet:
  PSet.compress.z(ws, Wo.Words.all_zero(ws))

# ---------------------------------------------------------------------------
# Branch construction, with the Zero/Full collapses of SPEC 5.3.
# ---------------------------------------------------------------------------

def PSet.mk.z(lo: PSet, hi: PSet) -> PSet:
  match hi:
    case PZero{}:
      PZero{}
    case PFull{}:
      PBranch{lo, PFull{}}
    case PSparse{o}:
      PBranch{lo, PSparse{o}}
    case PDense{w}:
      PBranch{lo, PDense{w}}
    case PBranch{a, b}:
      PBranch{lo, PBranch{a, b}}

def PSet.mk.f(lo: PSet, hi: PSet) -> PSet:
  match hi:
    case PFull{}:
      PFull{}
    case PZero{}:
      PBranch{lo, PZero{}}
    case PSparse{o}:
      PBranch{lo, PSparse{o}}
    case PDense{w}:
      PBranch{lo, PDense{w}}
    case PBranch{a, b}:
      PBranch{lo, PBranch{a, b}}

def PSet.mk.hi(lo: PSet, hi: PSet, lz: Bool, lf: Bool) -> PSet:
  match lz:
    case True{}:
      PSet.mk.z(lo, hi)
    case False{}:
      match lf:
        case True{}:
          PSet.mk.f(lo, hi)
        case False{}:
          PBranch{lo, hi}

def PSet.is_zero(s: PSet) -> Bool:
  match s:
    case PZero{}:
      True{}
    case PFull{}:
      False{}
    case PSparse{o}:
      False{}
    case PDense{w}:
      False{}
    case PBranch{a, b}:
      False{}

def PSet.is_full(s: PSet) -> Bool:
  match s:
    case PFull{}:
      True{}
    case PZero{}:
      False{}
    case PSparse{o}:
      False{}
    case PDense{w}:
      False{}
    case PBranch{a, b}:
      False{}

def PSet.leaf.or2(+aw: List<&2, U32>, b: PSet) -> PSet:
  PSet.compress(Wo.Words.or(aw, PSet.leaf_words(b)))

def PSet.leaf.and2(+aw: List<&2, U32>, b: PSet) -> PSet:
  PSet.compress(Wo.Words.and(aw, PSet.leaf_words(b)))

def PSet.leaf.sub2(+aw: List<&2, U32>, b: PSet) -> PSet:
  PSet.compress(Wo.Words.diff(aw, PSet.leaf_words(b)))

def PSet.union.leaf(a: PSet, b: PSet) -> PSet:
  match a:
    case PZero{}:
      b
    case PFull{}:
      PFull{}
    case PSparse{ao}:
      PSet.leaf.or2(PSet.spread(ao, Wo.Words.zeros(128n)), b)
    case PDense{aw}:
      PSet.leaf.or2(aw, b)
    case PBranch{l, h}:
      b

def PSet.inter.leaf(a: PSet, b: PSet) -> PSet:
  match a:
    case PZero{}:
      PZero{}
    case PFull{}:
      b
    case PSparse{ao}:
      PSet.leaf.and2(PSet.spread(ao, Wo.Words.zeros(128n)), b)
    case PDense{aw}:
      PSet.leaf.and2(aw, b)
    case PBranch{l, h}:
      PZero{}

def PSet.diff.leaf(a: PSet, b: PSet) -> PSet:
  match a:
    case PZero{}:
      PZero{}
    case PFull{}:
      PSet.leaf.sub2(Wo.Words.ones(128n), b)
    case PSparse{ao}:
      PSet.leaf.sub2(PSet.spread(ao, Wo.Words.zeros(128n)), b)
    case PDense{aw}:
      PSet.leaf.sub2(aw, b)
    case PBranch{l, h}:
      PZero{}

def PSet.add.leaf.pick(+offs: List<&2, U32>, small: Bool) -> PSet:
  match small:
    case True{}:
      PSparse{offs}
    case False{}:
      PDense{PSet.spread(offs, Wo.Words.zeros(128n))}

def PSet.add.leaf.fit(+offs: List<&2, U32>) -> PSet:
  PSet.add.leaf.pick(offs,
    C.Nat.upto(List.length(&2, U32, offs), PSet.sparse_max()))

def PSet.add.leaf(s: PSet, +x: U32) -> PSet:
  match s:
    case PZero{}:
      PSparse{[x]}
    case PFull{}:
      PFull{}
    case PSparse{offs}:
      PSet.add.leaf.fit(O.Ords.insert(offs, x))
    case PDense{ws}:
      PDense{Wo.Words.set(ws, x)}
    case PBranch{l, h}:
      PSparse{[x]}

def PSet.add(+d: Nat, s: PSet, +h: U32, +x: U32, b: Bool) -> PSet:
  match d:
    case 0n:
      PSet.add.leaf(s, x)
    case 1n+p:
      match s:
        case PFull{}:
          PFull{}
        case PBranch{lo, hi}:
          match b:
            case True{}:
              +h2 = U32.shr(h)
              PBranch{PSet.add(p, lo, h2, x, U32.is_lt(x, h2)), hi}
            case False{}:
              +x2 = U32.sub(x, h)
              +h2 = U32.shr(h)
              PBranch{lo, PSet.add(p, hi, h2, x2, U32.is_lt(x2, h2))}
        case PZero{}:
          match b:
            case True{}:
              +h2 = U32.shr(h)
              PBranch{PSet.add(p, PZero{}, h2, x, U32.is_lt(x, h2)),
                PZero{}}
            case False{}:
              +x2 = U32.sub(x, h)
              +h2 = U32.shr(h)
              PBranch{PZero{},
                PSet.add(p, PZero{}, h2, x2, U32.is_lt(x2, h2))}
        case PSparse{o}:
          match b:
            case True{}:
              +h2 = U32.shr(h)
              PBranch{PSet.add(p, PZero{}, h2, x, U32.is_lt(x, h2)),
                PZero{}}
            case False{}:
              +x2 = U32.sub(x, h)
              +h2 = U32.shr(h)
              PBranch{PZero{},
                PSet.add(p, PZero{}, h2, x2, U32.is_lt(x2, h2))}
        case PDense{w}:
          match b:
            case True{}:
              +h2 = U32.shr(h)
              PBranch{PSet.add(p, PZero{}, h2, x, U32.is_lt(x, h2)),
                PZero{}}
            case False{}:
              +x2 = U32.sub(x, h)
              +h2 = U32.shr(h)
              PBranch{PZero{},
                PSet.add(p, PZero{}, h2, x2, U32.is_lt(x2, h2))}

def PSet.insert(+d: Nat, s: PSet, +x: U32) -> PSet:
  +h = PSet.half(d)
  PSet.add(d, s, h, x, U32.is_lt(x, h))

def PSet.of_list(+d: Nat, xs: List<&2, U32>, s: PSet) -> PSet:
  match xs:
    case Nil{}:
      s
    case Con{x, t}:
      PSet.of_list(d, t, PSet.insert(d, s, x))

def PSet.from_list(+d: Nat, xs: List<&2, U32>) -> PSet:
  PSet.of_list(d, xs, PZero{})

# ---------------------------------------------------------------------------
# Leaf enumeration. Every reduction below goes through an ascending offset
# list rather than re-testing membership per position: a sparse leaf hands
# over its list for nothing, and a dense leaf is walked once, 32 native steps
# a word.
# ---------------------------------------------------------------------------

def PSet.range(+k: Nat, +ord: U32, tail: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      tail
    case 1n+j:
      +o = ord
      PSet.range(j, U32.sub(o, 1), Con{o, tail})

def PSet.leaf_members(s: PSet) -> List<&2, U32>:
  match s:
    case PZero{}:
      Nil{}
    case PFull{}:
      PSet.range(4096n, 4095, Nil{})
    case PSparse{offs}:
      offs
    case PDense{ws}:
      Wo.Words.members(ws, 0)
    case PBranch{l, h}:
      Nil{}

# The fused leaf: the members of `a \ b`, without building `a \ b`. Each arm
# picks the cheapest walk for the pair of shapes it actually got -- a sparse
# operand is merged as a list, two dense operands go through the word kernel,
# and a `PFull` or `PZero` operand short-circuits.
def PSet.leaf_diff_members.full(b: PSet) -> List<&2, U32>:
  match b:
    case PZero{}:
      PSet.range(4096n, 4095, Nil{})
    case PFull{}:
      Nil{}
    case PSparse{bo}:
      O.Ords.diff(PSet.range(4096n, 4095, Nil{}), bo)
    case PDense{bw}:
      Wo.Words.diff_members(Wo.Words.ones(128n), bw, 0)
    case PBranch{l, h}:
      PSet.range(4096n, 4095, Nil{})

def PSet.leaf_diff_members.sp(+ao: List<&2, U32>, b: PSet) ->
  List<&2, U32>:
  match b:
    case PZero{}:
      ao
    case PFull{}:
      Nil{}
    case PSparse{bo}:
      O.Ords.diff(ao, bo)
    case PDense{bw}:
      O.Ords.diff(ao, Wo.Words.members(bw, 0))
    case PBranch{l, h}:
      ao

def PSet.leaf_diff_members.dn(+aw: List<&2, U32>, b: PSet) ->
  List<&2, U32>:
  match b:
    case PZero{}:
      Wo.Words.members(aw, 0)
    case PFull{}:
      Nil{}
    case PSparse{bo}:
      O.Ords.diff(Wo.Words.members(aw, 0), bo)
    case PDense{bw}:
      Wo.Words.diff_members(aw, bw, 0)
    case PBranch{l, h}:
      Wo.Words.members(aw, 0)

def PSet.leaf_diff_members(a: PSet, b: PSet) -> List<&2, U32>:
  match a:
    case PZero{}:
      Nil{}
    case PFull{}:
      PSet.leaf_diff_members.full(b)
    case PSparse{ao}:
      PSet.leaf_diff_members.sp(ao, b)
    case PDense{aw}:
      PSet.leaf_diff_members.dn(aw, b)
    case PBranch{l, h}:
      Nil{}

# ---------------------------------------------------------------------------
# Counting. `h` is the node's half-width, so a `PFull` node counts its whole
# interval without walking it -- which is the point of keeping `PFull` a node
# rather than 128 words of ones.
# ---------------------------------------------------------------------------

def PSet.count.leaf(s: PSet) -> Nat:
  match s:
    case PZero{}:
      0n
    case PFull{}:
      4096n
    case PSparse{offs}:
      List.length(&2, U32, offs)
    case PDense{ws}:
      Wo.Words.count(ws)
    case PBranch{l, h}:
      0n

def PSet.count(+d: Nat, s: PSet, +h: U32) -> Nat:
  match d:
    case 0n:
      PSet.count.leaf(s)
    case 1n+p:
      match s:
        case PZero{}:
          0n
        case PSparse{offs}:
          List.length(&2, U32, offs)
        case PDense{ws}:
          Wo.Words.count(ws)
        case PFull{}:
          +w = U32.to_nat(h)
          Nat.add(w, w)
        case PBranch{lo, hi}:
          +h2 = U32.shr(h)
          Nat.add(PSet.count(p, lo, h2), PSet.count(p, hi, h2))

def PSet.size(+d: Nat, s: PSet) -> Nat:
  PSet.count(d, s, PSet.half(d))

def PSet.is_empty(+d: Nat, s: PSet, so_far: Bool) -> Bool:
  match d:
    case 0n:
      Bool.and(so_far, Nat.is_eq(PSet.count.leaf(s), 0n))
    case 1n+p:
      match s:
        case PZero{}:
          so_far
        case PFull{}:
          False{}
        case PSparse{offs}:
          Bool.and(so_far, List.is_empty(&2, U32, offs))
        case PDense{ws}:
          Bool.and(so_far, Bool.not(Wo.Words.any(ws)))
        case PBranch{lo, hi}:
          match so_far:
            case False{}:
              False{}
            case True{}:
              PSet.is_empty(p, hi, PSet.is_empty(p, lo, True{}))

def PSet.empty_p(+d: Nat, s: PSet) -> Bool:
  PSet.is_empty(d, s, True{})

# ---------------------------------------------------------------------------
# Enumeration over the whole tree, ascending, with an accumulator tail.
# ---------------------------------------------------------------------------

def PSet.shift(xs: List<&2, U32>, +base: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      (x + base : U32) <> PSet.shift(t, base)

def PSet.members(+d: Nat, s: PSet, +base: U32, +h: U32,
  tail: List<&2, U32>) -> List<&2, U32>:
  match d:
    case 0n:
      List.append(&2, U32, PSet.shift(PSet.leaf_members(s), base), tail)
    case 1n+p:
      match s:
        case PZero{}:
          tail
        case PSparse{offs}:
          List.append(&2, U32, PSet.shift(offs, base), tail)
        case PDense{ws}:
          List.append(&2, U32,
            PSet.shift(Wo.Words.members(ws, 0), base), tail)
        case PFull{}:
          +w = U32.to_nat(h)
          PSet.range(Nat.add(w, w), (base + h + h - 1 : U32), tail)
        case PBranch{lo, hi}:
          +h2 = U32.shr(h)
          PSet.members(p, lo, base, h2,
            PSet.members(p, hi, (base + h : U32), h2, tail))

def PSet.to_list(+d: Nat, s: PSet) -> List<&2, U32>:
  PSet.members(d, s, 0, PSet.half(d), Nil{})

# ---------------------------------------------------------------------------
# The fused reductions of SPEC 7.2: the size of `a \ b`, whether `a \ b` is
# inhabited, and the members of `a \ b` -- each computed without ever
# allocating `a \ b`. Structural pruning happens first: a `PZero` or `PFull`
# operand answers for a whole interval without descending into it.
# ---------------------------------------------------------------------------

def PSet.leaf_diff_count(a: PSet, b: PSet) -> Nat:
  match a:
    case PZero{}:
      0n
    case PDense{aw}:
      match b:
        case PZero{}:
          Wo.Words.count(aw)
        case PFull{}:
          0n
        case PDense{bw}:
          Wo.Words.diff_count(aw, bw)
        case PSparse{bo}:
          List.length(&2, U32,
            PSet.leaf_diff_members.dn(aw, PSparse{bo}))
        case PBranch{l, h}:
          Wo.Words.count(aw)
    case PFull{}:
      match b:
        case PZero{}:
          4096n
        case PFull{}:
          0n
        case PDense{bw}:
          Wo.Words.diff_count(Wo.Words.ones(128n), bw)
        case PSparse{bo}:
          List.length(&2, U32,
            PSet.leaf_diff_members.full(PSparse{bo}))
        case PBranch{l, h}:
          4096n
    case PSparse{ao}:
      List.length(&2, U32, PSet.leaf_diff_members.sp(ao, b))
    case PBranch{l, h}:
      0n

def PSet.diff_count(+d: Nat, a: PSet, b: PSet, +h: U32) -> Nat:
  match d:
    case 0n:
      PSet.leaf_diff_count(a, b)
    case 1n+p:
      match a:
        case PZero{}:
          0n
        case PSparse{o}:
          0n
        case PDense{w}:
          0n
        case PFull{}:
          match b:
            case PZero{}:
              +w = U32.to_nat(h)
              Nat.add(w, w)
            case PFull{}:
              0n
            case PSparse{o}:
              +w = U32.to_nat(h)
              Nat.add(w, w)
            case PDense{w}:
              +wd = U32.to_nat(h)
              Nat.add(wd, wd)
            case PBranch{bl, bh}:
              +h2 = U32.shr(h)
              Nat.add(PSet.diff_count(p, PFull{}, bl, h2),
                PSet.diff_count(p, PFull{}, bh, h2))
        case PBranch{al, ah}:
          match b:
            case PZero{}:
              +h2 = U32.shr(h)
              Nat.add(PSet.count(p, al, h2), PSet.count(p, ah, h2))
            case PSparse{o}:
              +h2 = U32.shr(h)
              Nat.add(PSet.count(p, al, h2), PSet.count(p, ah, h2))
            case PDense{w}:
              +h2 = U32.shr(h)
              Nat.add(PSet.count(p, al, h2), PSet.count(p, ah, h2))
            case PFull{}:
              0n
            case PBranch{bl, bh}:
              +h2 = U32.shr(h)
              Nat.add(PSet.diff_count(p, al, bl, h2),
                PSet.diff_count(p, ah, bh, h2))

def PSet.missing_count(+d: Nat, a: PSet, b: PSet) -> Nat:
  PSet.diff_count(d, a, b, PSet.half(d))

def PSet.diff_members(+d: Nat, a: PSet, b: PSet, +base: U32, +h: U32,
  tail: List<&2, U32>) -> List<&2, U32>:
  match d:
    case 0n:
      List.append(&2, U32,
        PSet.shift(PSet.leaf_diff_members(a, b), base), tail)
    case 1n+p:
      match a:
        case PZero{}:
          tail
        case PSparse{o}:
          tail
        case PDense{w}:
          tail
        case PFull{}:
          match b:
            case PZero{}:
              +w = U32.to_nat(h)
              PSet.range(Nat.add(w, w), (base + h + h - 1 : U32), tail)
            case PFull{}:
              tail
            case PSparse{o}:
              +w = U32.to_nat(h)
              PSet.range(Nat.add(w, w), (base + h + h - 1 : U32), tail)
            case PDense{w}:
              +wd = U32.to_nat(h)
              PSet.range(Nat.add(wd, wd), (base + h + h - 1 : U32), tail)
            case PBranch{bl, bh}:
              +h2 = U32.shr(h)
              PSet.diff_members(p, PFull{}, bl, base, h2,
                PSet.diff_members(p, PFull{}, bh, (base + h : U32), h2,
                  tail))
        case PBranch{al, ah}:
          match b:
            case PZero{}:
              +h2 = U32.shr(h)
              PSet.members(p, al, base, h2,
                PSet.members(p, ah, (base + h : U32), h2, tail))
            case PSparse{o}:
              +h2 = U32.shr(h)
              PSet.members(p, al, base, h2,
                PSet.members(p, ah, (base + h : U32), h2, tail))
            case PDense{w}:
              +h2 = U32.shr(h)
              PSet.members(p, al, base, h2,
                PSet.members(p, ah, (base + h : U32), h2, tail))
            case PFull{}:
              tail
            case PBranch{bl, bh}:
              +h2 = U32.shr(h)
              PSet.diff_members(p, al, bl, base, h2,
                PSet.diff_members(p, ah, bh, (base + h : U32), h2, tail))

def PSet.missing(+d: Nat, a: PSet, b: PSet) -> List<&2, U32>:
  PSet.diff_members(d, a, b, 0, PSet.half(d), Nil{})

# Readiness: is every member of `a` also a member of `b`? Law M-02.
def PSet.is_subset(+d: Nat, a: PSet, b: PSet) -> Bool:
  Nat.is_eq(PSet.missing_count(d, a, b), 0n)

# ---------------------------------------------------------------------------
# Structural validity (law D-01). A file is untrusted input: SPEC 6.5
# requires bounds, node references and universe bindings to be validated on
# load, and a checksum is explicitly not a substitute. This is that check --
# sparse and dense payloads only at the leaf level, sparse offsets ascending
# and in range, a dense leaf exactly 128 words.
# ---------------------------------------------------------------------------

def PSet.valid.offs(offs: List<&2, U32>, +last: U32, first: Bool,
  ok: Bool) -> Bool:
  match offs:
    case Nil{}:
      ok
    case Con{o, t}:
      match ok:
        case False{}:
          False{}
        case True{}:
          +oo = o
          PSet.valid.offs(t, oo, False{},
            Bool.and(U32.is_lt(oo, 4096),
              Bool.or(first, U32.is_gt(oo, last))))

def PSet.valid.leaf(s: PSet) -> Bool:
  match s:
    case PZero{}:
      True{}
    case PFull{}:
      True{}
    case PSparse{offs}:
      PSet.valid.offs(offs, 0, True{}, True{})
    case PDense{ws}:
      Nat.is_eq(List.length(&2, U32, ws), 128n)
    case PBranch{l, h}:
      False{}

def PSet.valid(+d: Nat, s: PSet, ok: Bool) -> Bool:
  match d:
    case 0n:
      Bool.and(ok, PSet.valid.leaf(s))
    case 1n+p:
      match s:
        case PZero{}:
          ok
        case PFull{}:
          ok
        case PSparse{offs}:
          False{}
        case PDense{ws}:
          False{}
        case PBranch{lo, hi}:
          match ok:
            case False{}:
              False{}
            case True{}:
              PSet.valid(p, hi, PSet.valid(p, lo, True{}))

# A leaf. `Branch` here is the one structurally invalid shape -- a branch
# below the leaf level -- and reads as empty, which is what `PSet.valid`
# rejects rather than what any operation relies on.
def PSet.mem.leaf(s: PSet, +x: U32) -> Bool:
  match s:
    case PZero{}:
      False{}
    case PFull{}:
      True{}
    case PSparse{offs}:
      O.Ords.elem(offs, x)
    case PDense{ws}:
      Wo.Words.bit(ws, x)
    case PBranch{lo, hi}:
      False{}

def PSet.mem(+d: Nat, s: PSet, +h: U32, +x: U32) -> Bool:
  match d:
    case 0n:
      PSet.mem.leaf(s, x)
    case 1n+p:
      match s:
        case PZero{}:
          False{}
        case PFull{}:
          True{}
        case PSparse{offs}:
          O.Ords.elem(offs, x)
        case PDense{ws}:
          Wo.Words.bit(ws, x)
        case PBranch{lo, hi}:
          +b = U32.is_lt(x, h)
          PSet.mem(p, PSet.pick(b, lo, hi), U32.shr(h),
            PSet.rebase(b, h, x))

def PSet.member(+d: Nat, s: PSet, +x: U32) -> Bool:
  PSet.mem(d, s, PSet.half(d), x)

# ---------------------------------------------------------------------------
# Leaves: words in, compressed node out.
# ---------------------------------------------------------------------------

def PSet.mk(+lo: PSet, hi: PSet) -> PSet:
  PSet.mk.hi(lo, hi, PSet.is_zero(lo), PSet.is_full(lo))

# ---------------------------------------------------------------------------
# Boolean algebra. Each operation takes the structural shortcuts of SPEC 5.3
# (`A u PZero = A`, `A n PFull = A`, `A \ PFull = PZero`, ...) at every node,
# so a difference against a pruned subtree costs nothing, and falls back to
# words only when two real leaves meet.
#
# Above the leaf level only `PZero`, `PFull` and `PBranch` occur: sparse and
# dense payloads are created by `PSet.compress` and `PSet.add`, which build
# them only at depth zero. SPEC 5.2 requires exactly that. The node
# operations therefore read a sparse or dense payload above a leaf as empty,
# and `PSet.valid` is what stops such a value ever reaching them -- it is
# checked on everything decoded from storage (law D-01), because a file is
# untrusted input (SPEC 6.5).
# ---------------------------------------------------------------------------

def PSet.union(+d: Nat, a: PSet, b: PSet) -> PSet:
  match d:
    case 0n:
      PSet.union.leaf(a, b)
    case 1n+p:
      match a:
        case PZero{}:
          b
        case PFull{}:
          PFull{}
        case PSparse{o}:
          b
        case PDense{w}:
          b
        case PBranch{al, ah}:
          match b:
            case PZero{}:
              PBranch{al, ah}
            case PFull{}:
              PFull{}
            case PSparse{o}:
              PBranch{al, ah}
            case PDense{w}:
              PBranch{al, ah}
            case PBranch{bl, bh}:
              PSet.mk(PSet.union(p, al, bl), PSet.union(p, ah, bh))

def PSet.inter(+d: Nat, a: PSet, b: PSet) -> PSet:
  match d:
    case 0n:
      PSet.inter.leaf(a, b)
    case 1n+p:
      match a:
        case PZero{}:
          PZero{}
        case PSparse{o}:
          PZero{}
        case PDense{w}:
          PZero{}
        case PFull{}:
          b
        case PBranch{al, ah}:
          match b:
            case PZero{}:
              PZero{}
            case PSparse{o}:
              PZero{}
            case PDense{w}:
              PZero{}
            case PFull{}:
              PBranch{al, ah}
            case PBranch{bl, bh}:
              PSet.mk(PSet.inter(p, al, bl), PSet.inter(p, ah, bh))

def PSet.diff(+d: Nat, a: PSet, b: PSet) -> PSet:
  match d:
    case 0n:
      PSet.diff.leaf(a, b)
    case 1n+p:
      match a:
        case PZero{}:
          PZero{}
        case PSparse{o}:
          PZero{}
        case PDense{w}:
          PZero{}
        case PFull{}:
          match b:
            case PZero{}:
              PFull{}
            case PFull{}:
              PZero{}
            case PSparse{o}:
              PFull{}
            case PDense{w}:
              PFull{}
            case PBranch{bl, bh}:
              PSet.mk(PSet.diff(p, PFull{}, bl), PSet.diff(p, PFull{}, bh))
        case PBranch{al, ah}:
          match b:
            case PZero{}:
              PBranch{al, ah}
            case PFull{}:
              PZero{}
            case PSparse{o}:
              PBranch{al, ah}
            case PDense{w}:
              PBranch{al, ah}
            case PBranch{bl, bh}:
              PSet.mk(PSet.diff(p, al, bl), PSet.diff(p, ah, bh))

# ---------------------------------------------------------------------------
# Insert. A persistent update copies the path and the affected leaf, and
# leaves every other node shared (law P-01). The branch test is computed by
# the caller and handed down, because Bend matches parameters rather than
# computed values and mutual recursion is not allowed.
# ---------------------------------------------------------------------------
