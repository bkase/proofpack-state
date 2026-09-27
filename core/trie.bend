# core/trie.bend -- a depth-indexed ordinal-keyed trie.
#
# The universe assigns ordinals densely, 0..N-1, so every per-object table is
# a vector: adjacency lists, object metadata, closure ranks. This is that
# vector, as a binary trie keyed on the ordinal's bits from the top down.
#
# Why a trie and not a list: lookup is O(depth) rather than O(N), and an
# absent subtree is one `BNil` node rather than a run of holes, so a table
# built for N objects costs about 2N nodes however wide the ordinal space is.
#
# Why built top-down by splitting rather than by N inserts: `Trie.build`
# walks the payload list once per level, so a table of N entries costs
# O(N * depth) list steps and no path copying at all.

import Base
import ./count.bend as C

type Trie.Leaf<-A: Data> is Data:
  TVal{value: A}
  TGap{}

type Trie.Node<-A: Data, -p: Nat> is Data:
  BGap{}
  BBr{lo: Trie(A, p), hi: Trie(A, p)}

def Trie(-A: Data, d: Nat) -> Data:
  match d:
    case 0n:
      Trie.Leaf<A>
    case 1n+p:
      Trie.Node<A, p>

def Trie.gap(-A: Data, d: Nat) -> Trie(A, d):
  match d:
    case 0n:
      TGap{}
    case 1n+p:
      BGap{}

# The depth that covers `n` ordinals: a leaf holds exactly one.
def Trie.depth.go(+fuel: Nat, +cap: Nat, +n: Nat, d: Nat, done: Bool) -> Nat:
  match fuel:
    case 0n:
      d
    case 1n+f:
      match done:
        case True{}:
          d
        case False{}:
          +c2 = Nat.add(cap, cap)
          Trie.depth.go(f, c2, n, 1n+d, C.Nat.upto(n, c2))

def Trie.depth(+n: Nat) -> Nat:
  Trie.depth.go(33n, 1n, n, 0n, C.Nat.upto(n, 1n))

# The half-width of a node at depth `d`: 2^(d-1) for d >= 1. Written as a
# shift by d-1 rather than a shift by d halved, because at the maximum depth
# 32 the full width does not fit a U32 and `U32.shln(1, 32n)` is zero.
def Trie.half(+d: Nat) -> U32:
  U32.shln(1, Nat.sub(d, 1n))

# ---------------------------------------------------------------------------
# Lookup. One compare, one shift and one conditional subtract per level, the
# same walk `PSet.mem` uses.
# ---------------------------------------------------------------------------

def Trie.pick(-A: Data, -p: Nat, b: Bool, lo: Trie(A, p),
  hi: Trie(A, p)) -> Trie(A, p):
  match b:
    case True{}:
      lo
    case False{}:
      hi

def Trie.rebase(b: Bool, +h: U32, +x: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      U32.sub(x, h)

def Trie.get(-A: Data, d: Nat, t: Trie(A, d), +h: U32,
  +x: U32) -> Maybe<&2, A>:
  match d:
    case 0n:
      match t:
        case TGap{}:
          None{}
        case TVal{v}:
          Some{v}
    case 1n+p:
      match t:
        case BGap{}:
          None{}
        case BBr{lo, hi}:
          +b = U32.is_lt(x, h)
          Trie.get(A, p, Trie.pick(A, p, b, lo, hi), U32.shr(h),
            Trie.rebase(b, h, x))

def Trie.at(-A: Data, +d: Nat, t: Trie(A, d), +x: U32) ->
  Maybe<&2, A>:
  Trie.get(A, d, t, Trie.half(d), x)

# ---------------------------------------------------------------------------
# Bulk build. `xs` is the payload in ordinal order; a level splits it in two
# and recurses, and an empty half becomes one gap node.
# ---------------------------------------------------------------------------

def Trie.build(-A: Data, +d: Nat, +h: U32, +xs: List<&2, A>) ->
  Trie(A, d):
  match d:
    case 0n:
      match xs:
        case Nil{}:
          TGap{}
        case Con{v, rest}:
          TVal{v}
    case 1n+p:
      match xs:
        case Nil{}:
          BGap{}
        case Con{v, rest}:
          +ys = {Con{v, rest} : List<&2, A>}
          +k = U32.to_nat(h)
          +h2 = U32.shr(h)
          BBr{Trie.build(A, p, h2, List.take(&2, A, ys, k)),
            Trie.build(A, p, h2, List.drop(&2, A, ys, k))}

def Trie.of_list(-A: Data, +d: Nat, xs: List<&2, A>) ->
  Trie(A, d):
  Trie.build(A, d, Trie.half(d), xs)

# ---------------------------------------------------------------------------
# Point update. The branch test is computed by the caller and handed down,
# because Bend matches parameters rather than computed values and a helper
# that called back would be mutual recursion.
# ---------------------------------------------------------------------------

def Trie.put(-A: Data, +d: Nat, t: Trie(A, d), +h: U32, +x: U32, +v: A,
  b: Bool) -> Trie(A, d):
  match d:
    case 0n:
      match t:
        case TGap{}:
          TVal{v}
        case TVal{old}:
          TVal{v}
    case 1n+p:
      match t:
        case BGap{}:
          match b:
            case True{}:
              +h2 = U32.shr(h)
              BBr{Trie.put(A, p, Trie.gap(A, p), h2, x, v, U32.is_lt(x, h2)),
                Trie.gap(A, p)}
            case False{}:
              +x2 = U32.sub(x, h)
              +h2 = U32.shr(h)
              BBr{Trie.gap(A, p),
                Trie.put(A, p, Trie.gap(A, p), h2, x2, v, U32.is_lt(x2, h2))}
        case BBr{lo, hi}:
          match b:
            case True{}:
              +h2 = U32.shr(h)
              BBr{Trie.put(A, p, lo, h2, x, v, U32.is_lt(x, h2)), hi}
            case False{}:
              +x2 = U32.sub(x, h)
              +h2 = U32.shr(h)
              BBr{lo, Trie.put(A, p, hi, h2, x2, v, U32.is_lt(x2, h2))}

def Trie.set(-A: Data, +d: Nat, t: Trie(A, d), +x: U32, +v: A) ->
  Trie(A, d):
  +h = Trie.half(d)
  Trie.put(A, d, t, h, x, v, U32.is_lt(x, h))
