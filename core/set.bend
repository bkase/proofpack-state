# core/set.bend -- the persistent set representation (law families S-*, P-*).
#
# A set is a binary tree over fixed ordinal intervals, exactly SPEC 5.2's
# shape: `Zero` and `Full` compress a whole range, a leaf covers 4096 ordinals
# as either a sorted offset list or 128 bitmap words, and a branch splits its
# interval in half.
#
# The tree is *depth-indexed*, the way Base indexes `Word(n)`: `PSet(0n)` is a
# leaf and `PSet(1n+p)` is a node. That is not decoration. SPEC 5.2 requires
# that sparse and dense payloads only ever appear at a leaf and that branch
# children partition their parent interval exactly; indexing the type makes
# every other shape unrepresentable, so no operation below needs an
# "impossible" arm that would silently return the wrong set if an invariant
# were ever broken.
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

type PSet.Leaf is Data:
  LZero{}
  LFull{}
  LSparse{offs: List<&2, U32>}
  LDense{words: List<&2, U32>}

type PSet.Node<-p: Nat> is Data:
  NZero{}
  NFull{}
  NBranch{lo: PSet(p), hi: PSet(p)}

def PSet(d: Nat) -> Data:
  match d:
    case 0n:
      PSet.Leaf
    case 1n+p:
      PSet.Node<p>

# The empty set at any depth.
def PSet.empty(d: Nat) -> PSet(d):
  match d:
    case 0n:
      LZero{}
    case 1n+p:
      NZero{}

def PSet.full(d: Nat) -> PSet(d):
  match d:
    case 0n:
      LFull{}
    case 1n+p:
      NFull{}

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

def PSet.pick(-p: Nat, b: Bool, lo: PSet(p), hi: PSet(p)) -> PSet(p):
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

def PSet.mem(d: Nat, s: PSet(d), +h: U32, +x: U32) -> Bool:
  match d:
    case 0n:
      match s:
        case LZero{}:
          False{}
        case LFull{}:
          True{}
        case LSparse{offs}:
          O.Ords.elem(offs, x)
        case LDense{ws}:
          Wo.Words.bit(ws, x)
    case 1n+p:
      match s:
        case NZero{}:
          False{}
        case NFull{}:
          True{}
        case NBranch{lo, hi}:
          +b = U32.is_lt(x, h)
          PSet.mem(p, PSet.pick(p, b, lo, hi), U32.shr(h),
            PSet.rebase(b, h, x))

def PSet.member(+d: Nat, s: PSet(d), +x: U32) -> Bool:
  PSet.mem(d, s, PSet.half(d), x)

# ---------------------------------------------------------------------------
# Leaves: words in, compressed node out.
# ---------------------------------------------------------------------------

def PSet.spread(offs: List<&2, U32>, ws: List<&2, U32>) -> List<&2, U32>:
  match offs:
    case Nil{}:
      ws
    case Con{o, t}:
      PSet.spread(t, Wo.Words.set(ws, o))

def PSet.leaf_words(s: PSet.Leaf) -> List<&2, U32>:
  match s:
    case LZero{}:
      Wo.Words.zeros(128n)
    case LFull{}:
      Wo.Words.ones(128n)
    case LSparse{offs}:
      PSet.spread(offs, Wo.Words.zeros(128n))
    case LDense{ws}:
      ws

# The sparse/dense crossover. SPEC 5.2 calls 64 members a benchmark
# parameter, not a semantic constant: nothing outside this def reads it, and
# changing it changes no denotation (law S-03).
def PSet.sparse_max() -> Nat:
  64n

def PSet.compress.s(+ws: List<&2, U32>, sparse: Bool) -> PSet.Leaf:
  match sparse:
    case True{}:
      LSparse{Wo.Words.members(ws, 0)}
    case False{}:
      LDense{ws}

def PSet.compress.f(+ws: List<&2, U32>, full: Bool) -> PSet.Leaf:
  match full:
    case True{}:
      LFull{}
    case False{}:
      PSet.compress.s(ws,
        C.Nat.upto(Wo.Words.count(ws), PSet.sparse_max()))

def PSet.compress.z(+ws: List<&2, U32>, zero: Bool) -> PSet.Leaf:
  match zero:
    case True{}:
      LZero{}
    case False{}:
      PSet.compress.f(ws, Wo.Words.all_ones(ws))

def PSet.compress(+ws: List<&2, U32>) -> PSet.Leaf:
  PSet.compress.z(ws, Wo.Words.all_zero(ws))

# ---------------------------------------------------------------------------
# Branch construction, with the Zero/Full collapses of SPEC 5.3.
# ---------------------------------------------------------------------------

def PSet.mk.leaf(lo: PSet.Leaf, hi: PSet.Leaf) -> PSet(1n):
  match lo:
    case LZero{}:
      match hi:
        case LZero{}:
          NZero{}
        case LFull{}:
          NBranch{LZero{}, LFull{}}
        case LSparse{o}:
          NBranch{LZero{}, LSparse{o}}
        case LDense{w}:
          NBranch{LZero{}, LDense{w}}
    case LFull{}:
      match hi:
        case LFull{}:
          NFull{}
        case LZero{}:
          NBranch{LFull{}, LZero{}}
        case LSparse{o}:
          NBranch{LFull{}, LSparse{o}}
        case LDense{w}:
          NBranch{LFull{}, LDense{w}}
    case LSparse{a}:
      NBranch{LSparse{a}, hi}
    case LDense{a}:
      NBranch{LDense{a}, hi}

def PSet.mk.node(q: Nat, lo: PSet(1n+q), hi: PSet(1n+q)) -> PSet(2n+q):
  match lo:
    case NZero{}:
      match hi:
        case NZero{}:
          NZero{}
        case NFull{}:
          NBranch{NZero{}, NFull{}}
        case NBranch{x, y}:
          NBranch{NZero{}, NBranch{x, y}}
    case NFull{}:
      match hi:
        case NFull{}:
          NFull{}
        case NZero{}:
          NBranch{NFull{}, NZero{}}
        case NBranch{x, y}:
          NBranch{NFull{}, NBranch{x, y}}
    case NBranch{a, b}:
      NBranch{NBranch{a, b}, hi}

def PSet.mk(+p: Nat, lo: PSet(p), hi: PSet(p)) -> PSet(1n+p):
  match p:
    case 0n:
      PSet.mk.leaf(lo, hi)
    case 1n+q:
      PSet.mk.node(q, lo, hi)

# ---------------------------------------------------------------------------
# Boolean algebra. Each operation takes the structural shortcuts of SPEC 5.3
# (`A u Zero = A`, `A n Full = A`, `A \ Full = Zero`, ...) at every node, so a
# difference against a pruned subtree costs nothing, and falls back to words
# only when two real leaves meet.
# ---------------------------------------------------------------------------

def PSet.leaf.or2(+aw: List<&2, U32>, b: PSet.Leaf) -> PSet.Leaf:
  match b:
    case LZero{}:
      PSet.compress(aw)
    case LFull{}:
      LFull{}
    case LSparse{bo}:
      PSet.compress(Wo.Words.or(aw,
        PSet.spread(bo, Wo.Words.zeros(128n))))
    case LDense{bw}:
      PSet.compress(Wo.Words.or(aw, bw))

def PSet.leaf.and2(+aw: List<&2, U32>, b: PSet.Leaf) -> PSet.Leaf:
  match b:
    case LZero{}:
      LZero{}
    case LFull{}:
      PSet.compress(aw)
    case LSparse{bo}:
      PSet.compress(Wo.Words.and(aw,
        PSet.spread(bo, Wo.Words.zeros(128n))))
    case LDense{bw}:
      PSet.compress(Wo.Words.and(aw, bw))

def PSet.leaf.sub2(+aw: List<&2, U32>, b: PSet.Leaf) -> PSet.Leaf:
  match b:
    case LZero{}:
      PSet.compress(aw)
    case LFull{}:
      LZero{}
    case LSparse{bo}:
      PSet.compress(Wo.Words.diff(aw,
        PSet.spread(bo, Wo.Words.zeros(128n))))
    case LDense{bw}:
      PSet.compress(Wo.Words.diff(aw, bw))

def PSet.union.leaf(a: PSet.Leaf, b: PSet.Leaf) -> PSet.Leaf:
  match a:
    case LZero{}:
      b
    case LFull{}:
      LFull{}
    case LSparse{ao}:
      PSet.leaf.or2(PSet.spread(ao, Wo.Words.zeros(128n)), b)
    case LDense{aw}:
      PSet.leaf.or2(aw, b)

def PSet.inter.leaf(a: PSet.Leaf, b: PSet.Leaf) -> PSet.Leaf:
  match a:
    case LZero{}:
      LZero{}
    case LFull{}:
      b
    case LSparse{ao}:
      PSet.leaf.and2(PSet.spread(ao, Wo.Words.zeros(128n)), b)
    case LDense{aw}:
      PSet.leaf.and2(aw, b)

def PSet.diff.leaf(a: PSet.Leaf, b: PSet.Leaf) -> PSet.Leaf:
  match a:
    case LZero{}:
      LZero{}
    case LFull{}:
      PSet.leaf.sub2(Wo.Words.ones(128n), b)
    case LSparse{ao}:
      PSet.leaf.sub2(PSet.spread(ao, Wo.Words.zeros(128n)), b)
    case LDense{aw}:
      PSet.leaf.sub2(aw, b)

def PSet.union(+d: Nat, a: PSet(d), b: PSet(d)) -> PSet(d):
  match d:
    case 0n:
      PSet.union.leaf(a, b)
    case 1n+p:
      match a:
        case NZero{}:
          b
        case NFull{}:
          NFull{}
        case NBranch{al, ah}:
          match b:
            case NZero{}:
              NBranch{al, ah}
            case NFull{}:
              NFull{}
            case NBranch{bl, bh}:
              PSet.mk(p, PSet.union(p, al, bl), PSet.union(p, ah, bh))

def PSet.inter(+d: Nat, a: PSet(d), b: PSet(d)) -> PSet(d):
  match d:
    case 0n:
      PSet.inter.leaf(a, b)
    case 1n+p:
      match a:
        case NZero{}:
          NZero{}
        case NFull{}:
          b
        case NBranch{al, ah}:
          match b:
            case NZero{}:
              NZero{}
            case NFull{}:
              NBranch{al, ah}
            case NBranch{bl, bh}:
              PSet.mk(p, PSet.inter(p, al, bl), PSet.inter(p, ah, bh))

def PSet.diff(+d: Nat, a: PSet(d), b: PSet(d)) -> PSet(d):
  match d:
    case 0n:
      PSet.diff.leaf(a, b)
    case 1n+p:
      match a:
        case NZero{}:
          NZero{}
        case NFull{}:
          match b:
            case NZero{}:
              NFull{}
            case NFull{}:
              NZero{}
            case NBranch{bl, bh}:
              PSet.mk(p, PSet.diff(p, PSet.full(p), bl),
                PSet.diff(p, PSet.full(p), bh))
        case NBranch{al, ah}:
          match b:
            case NZero{}:
              NBranch{al, ah}
            case NFull{}:
              NZero{}
            case NBranch{bl, bh}:
              PSet.mk(p, PSet.diff(p, al, bl), PSet.diff(p, ah, bh))

# ---------------------------------------------------------------------------
# Insert. A persistent update copies the path and the affected leaf, and
# leaves every other node shared (law P-01).
# ---------------------------------------------------------------------------

def PSet.add.leaf.pick(+offs: List<&2, U32>, small: Bool) -> PSet.Leaf:
  match small:
    case True{}:
      LSparse{offs}
    case False{}:
      LDense{PSet.spread(offs, Wo.Words.zeros(128n))}

def PSet.add.leaf.fit(+offs: List<&2, U32>) -> PSet.Leaf:
  PSet.add.leaf.pick(offs,
    C.Nat.upto(List.length(&2, U32, offs), PSet.sparse_max()))

def PSet.add.leaf(s: PSet.Leaf, +x: U32) -> PSet.Leaf:
  match s:
    case LZero{}:
      LSparse{[x]}
    case LFull{}:
      LFull{}
    case LSparse{offs}:
      PSet.add.leaf.fit(O.Ords.insert(offs, x))
    case LDense{ws}:
      LDense{Wo.Words.set(ws, x)}

def PSet.add(+d: Nat, s: PSet(d), +h: U32, +x: U32, b: Bool) -> PSet(d):
  match d:
    case 0n:
      PSet.add.leaf(s, x)
    case 1n+p:
      match s:
        case NFull{}:
          NFull{}
        case NZero{}:
          match b:
            case True{}:
              +h2 = U32.shr(h)
              NBranch{PSet.add(p, PSet.empty(p), h2, x, U32.is_lt(x, h2)),
                PSet.empty(p)}
            case False{}:
              +x2 = U32.sub(x, h)
              +h2 = U32.shr(h)
              NBranch{PSet.empty(p),
                PSet.add(p, PSet.empty(p), h2, x2, U32.is_lt(x2, h2))}
        case NBranch{lo, hi}:
          match b:
            case True{}:
              +h2 = U32.shr(h)
              NBranch{PSet.add(p, lo, h2, x, U32.is_lt(x, h2)), hi}
            case False{}:
              +x2 = U32.sub(x, h)
              +h2 = U32.shr(h)
              NBranch{lo, PSet.add(p, hi, h2, x2, U32.is_lt(x2, h2))}

# Insert one ordinal. The branch test is computed by the caller and handed
# down, because Bend matches parameters rather than computed values and
# mutual recursion is not allowed -- so `add` cannot delegate the test to a
# helper that calls it back.
def PSet.insert(+d: Nat, s: PSet(d), +x: U32) -> PSet(d):
  +h = PSet.half(d)
  PSet.add(d, s, h, x, U32.is_lt(x, h))

# Build a set from a list of ordinals.
def PSet.of_list(+d: Nat, xs: List<&2, U32>, s: PSet(d)) -> PSet(d):
  match xs:
    case Nil{}:
      s
    case Con{x, t}:
      PSet.of_list(d, t, PSet.insert(d, s, x))

def PSet.from_list(+d: Nat, xs: List<&2, U32>) -> PSet(d):
  PSet.of_list(d, xs, PSet.empty(d))

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

def PSet.leaf_members(s: PSet.Leaf) -> List<&2, U32>:
  match s:
    case LZero{}:
      Nil{}
    case LFull{}:
      PSet.range(4096n, 4095, Nil{})
    case LSparse{offs}:
      offs
    case LDense{ws}:
      Wo.Words.members(ws, 0)

# The fused leaf: the members of `a \ b`, without building `a \ b`. Each arm
# picks the cheapest walk for the pair of shapes it actually got -- a sparse
# operand is merged as a list, two dense operands go through the word kernel,
# and a `Full` or `Zero` operand short-circuits.
def PSet.leaf_diff_members.full(b: PSet.Leaf) -> List<&2, U32>:
  match b:
    case LZero{}:
      PSet.range(4096n, 4095, Nil{})
    case LFull{}:
      Nil{}
    case LSparse{bo}:
      O.Ords.diff(PSet.range(4096n, 4095, Nil{}), bo)
    case LDense{bw}:
      Wo.Words.diff_members(Wo.Words.ones(128n), bw, 0)

def PSet.leaf_diff_members.sp(+ao: List<&2, U32>, b: PSet.Leaf) ->
  List<&2, U32>:
  match b:
    case LZero{}:
      ao
    case LFull{}:
      Nil{}
    case LSparse{bo}:
      O.Ords.diff(ao, bo)
    case LDense{bw}:
      O.Ords.diff(ao, Wo.Words.members(bw, 0))

def PSet.leaf_diff_members.dn(+aw: List<&2, U32>, b: PSet.Leaf) ->
  List<&2, U32>:
  match b:
    case LZero{}:
      Wo.Words.members(aw, 0)
    case LFull{}:
      Nil{}
    case LSparse{bo}:
      O.Ords.diff(Wo.Words.members(aw, 0), bo)
    case LDense{bw}:
      Wo.Words.diff_members(aw, bw, 0)

def PSet.leaf_diff_members(a: PSet.Leaf, b: PSet.Leaf) -> List<&2, U32>:
  match a:
    case LZero{}:
      Nil{}
    case LFull{}:
      PSet.leaf_diff_members.full(b)
    case LSparse{ao}:
      PSet.leaf_diff_members.sp(ao, b)
    case LDense{aw}:
      PSet.leaf_diff_members.dn(aw, b)

# ---------------------------------------------------------------------------
# Counting. `h` is the node's half-width, so a `Full` node counts its whole
# interval without walking it -- which is the point of keeping `Full` a node
# rather than 128 words of ones.
# ---------------------------------------------------------------------------

def PSet.count(+d: Nat, s: PSet(d), +h: U32) -> Nat:
  match d:
    case 0n:
      match s:
        case LZero{}:
          0n
        case LFull{}:
          4096n
        case LSparse{offs}:
          List.length(&2, U32, offs)
        case LDense{ws}:
          Wo.Words.count(ws)
    case 1n+p:
      match s:
        case NZero{}:
          0n
        case NFull{}:
          +w = U32.to_nat(h)
          Nat.add(w, w)
        case NBranch{lo, hi}:
          +h2 = U32.shr(h)
          Nat.add(PSet.count(p, lo, h2), PSet.count(p, hi, h2))

def PSet.size(+d: Nat, s: PSet(d)) -> Nat:
  PSet.count(d, s, PSet.half(d))

def PSet.is_empty(+d: Nat, s: PSet(d), so_far: Bool) -> Bool:
  match d:
    case 0n:
      match s:
        case LZero{}:
          so_far
        case LFull{}:
          False{}
        case LSparse{offs}:
          Bool.and(so_far, List.is_empty(&2, U32, offs))
        case LDense{ws}:
          Bool.and(so_far, Bool.not(Wo.Words.any(ws)))
    case 1n+p:
      match s:
        case NZero{}:
          so_far
        case NFull{}:
          False{}
        case NBranch{lo, hi}:
          match so_far:
            case False{}:
              False{}
            case True{}:
              PSet.is_empty(p, hi, PSet.is_empty(p, lo, True{}))

def PSet.empty_p(+d: Nat, s: PSet(d)) -> Bool:
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

def PSet.members(+d: Nat, s: PSet(d), +base: U32, +h: U32,
  tail: List<&2, U32>) -> List<&2, U32>:
  match d:
    case 0n:
      List.append(&2, U32, PSet.shift(PSet.leaf_members(s), base), tail)
    case 1n+p:
      match s:
        case NZero{}:
          tail
        case NFull{}:
          +w = U32.to_nat(h)
          PSet.range(Nat.add(w, w), (base + h + h - 1 : U32), tail)
        case NBranch{lo, hi}:
          +h2 = U32.shr(h)
          PSet.members(p, lo, base, h2,
            PSet.members(p, hi, (base + h : U32), h2, tail))

def PSet.to_list(+d: Nat, s: PSet(d)) -> List<&2, U32>:
  PSet.members(d, s, 0, PSet.half(d), Nil{})

# ---------------------------------------------------------------------------
# The fused reductions of SPEC 7.2: the size of `a \ b`, whether `a \ b` is
# inhabited, and the members of `a \ b` -- each computed without ever
# allocating `a \ b`. Structural pruning happens first: a `Zero` or `Full`
# operand answers for a whole interval without descending into it.
# ---------------------------------------------------------------------------

def PSet.leaf_diff_count(a: PSet.Leaf, b: PSet.Leaf) -> Nat:
  match a:
    case LZero{}:
      0n
    case LDense{aw}:
      match b:
        case LZero{}:
          Wo.Words.count(aw)
        case LFull{}:
          0n
        case LDense{bw}:
          Wo.Words.diff_count(aw, bw)
        case LSparse{bo}:
          List.length(&2, U32,
            PSet.leaf_diff_members.dn(aw, LSparse{bo}))
    case LFull{}:
      match b:
        case LZero{}:
          4096n
        case LFull{}:
          0n
        case LDense{bw}:
          Wo.Words.diff_count(Wo.Words.ones(128n), bw)
        case LSparse{bo}:
          List.length(&2, U32,
            PSet.leaf_diff_members.full(LSparse{bo}))
    case LSparse{ao}:
      List.length(&2, U32, PSet.leaf_diff_members.sp(ao, b))

def PSet.diff_count(+d: Nat, a: PSet(d), b: PSet(d), +h: U32) -> Nat:
  match d:
    case 0n:
      PSet.leaf_diff_count(a, b)
    case 1n+p:
      match a:
        case NZero{}:
          0n
        case NFull{}:
          match b:
            case NZero{}:
              +w = U32.to_nat(h)
              Nat.add(w, w)
            case NFull{}:
              0n
            case NBranch{bl, bh}:
              +h2 = U32.shr(h)
              Nat.add(PSet.diff_count(p, PSet.full(p), bl, h2),
                PSet.diff_count(p, PSet.full(p), bh, h2))
        case NBranch{al, ah}:
          match b:
            case NZero{}:
              +h2 = U32.shr(h)
              Nat.add(PSet.count(p, al, h2), PSet.count(p, ah, h2))
            case NFull{}:
              0n
            case NBranch{bl, bh}:
              +h2 = U32.shr(h)
              Nat.add(PSet.diff_count(p, al, bl, h2),
                PSet.diff_count(p, ah, bh, h2))

def PSet.missing_count(+d: Nat, a: PSet(d), b: PSet(d)) -> Nat:
  PSet.diff_count(d, a, b, PSet.half(d))

# Readiness: `a \ b` is empty. Stops at the first required object the
# inventory does not have (SPEC 4.3 -- IsEmpty must not pay to count).
def PSet.diff_any(+d: Nat, a: PSet(d), b: PSet(d), found: Bool) -> Bool:
  match d:
    case 0n:
      Bool.or(found, Bool.not(List.is_empty(&2, U32,
        PSet.leaf_diff_members(a, b))))
    case 1n+p:
      match a:
        case NZero{}:
          found
        case NFull{}:
          match b:
            case NZero{}:
              True{}
            case NFull{}:
              found
            case NBranch{bl, bh}:
              match found:
                case True{}:
                  True{}
                case False{}:
                  PSet.diff_any(p, PSet.full(p), bh,
                    PSet.diff_any(p, PSet.full(p), bl, False{}))
        case NBranch{al, ah}:
          match b:
            case NZero{}:
              match found:
                case True{}:
                  True{}
                case False{}:
                  Bool.not(PSet.is_empty(p, ah, PSet.is_empty(p, al, True{})))
            case NFull{}:
              found
            case NBranch{bl, bh}:
              match found:
                case True{}:
                  True{}
                case False{}:
                  PSet.diff_any(p, ah, bh, PSet.diff_any(p, al, bl, False{}))

# True when every member of `a` is also a member of `b`: law M-02.
def PSet.is_subset(+d: Nat, a: PSet(d), b: PSet(d)) -> Bool:
  Bool.not(PSet.diff_any(d, a, b, False{}))

def PSet.diff_members(+d: Nat, a: PSet(d), b: PSet(d), +base: U32, +h: U32,
  tail: List<&2, U32>) -> List<&2, U32>:
  match d:
    case 0n:
      List.append(&2, U32,
        PSet.shift(PSet.leaf_diff_members(a, b), base), tail)
    case 1n+p:
      match a:
        case NZero{}:
          tail
        case NFull{}:
          match b:
            case NZero{}:
              +w = U32.to_nat(h)
              PSet.range(Nat.add(w, w), (base + h + h - 1 : U32), tail)
            case NFull{}:
              tail
            case NBranch{bl, bh}:
              +h2 = U32.shr(h)
              PSet.diff_members(p, PSet.full(p), bl, base, h2,
                PSet.diff_members(p, PSet.full(p), bh, (base + h : U32), h2,
                  tail))
        case NBranch{al, ah}:
          match b:
            case NZero{}:
              +h2 = U32.shr(h)
              PSet.members(p, al, base, h2,
                PSet.members(p, ah, (base + h : U32), h2, tail))
            case NFull{}:
              tail
            case NBranch{bl, bh}:
              +h2 = U32.shr(h)
              PSet.diff_members(p, al, bl, base, h2,
                PSet.diff_members(p, ah, bh, (base + h : U32), h2, tail))

def PSet.missing(+d: Nat, a: PSet(d), b: PSet(d)) -> List<&2, U32>:
  PSet.diff_members(d, a, b, 0, PSet.half(d), Nil{})
