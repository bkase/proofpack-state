# core/word.bend -- the checked word layer.
#
# Every operation here is written with Base's native `U32` operations, which
# the compiler lowers to one machine instruction each (`U32_BIN(a, op, b)` in
# the emitted C, and the same source compiled by Metal for the device).
#
# Base declares `type U32 is Data: U32{data: Word(32n)}`, and `Word(n)` is a
# little-endian vector of `Bool`. So the checker sees every one of these
# operations as a bit-vector function it can do induction over, while the
# runtime sees a machine word. `U32.word` and `Word.get` below are the bridge:
# they appear in laws and proofs, never in a hot loop, because a `match` on a
# `U32` is the one thing that would materialize the 32 cons cells.
#
# Laws: B-01 (word refinement) in LAWS.bend.

import Base

# ---------------------------------------------------------------------------
# Bit membership -- the specification side.
# ---------------------------------------------------------------------------

# Bit `i` of a bit vector, counting from the least significant. Out of range
# reads False, which is what makes every law below unconditional.
def Word.get(n: Nat, w: Word(n), i: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match w i:
        case WCon{b, t} 0n:
          b
        case WCon{b, t} 1n+j:
          Word.get(p, t, j)

# The bit vector inside a U32. Proof-only: this is the `match` that would cost
# 32 heap cells if it ever ran.
def U32.word(x: U32) -> Word(32n):
  match x:
    case U32{w}:
      w

# Bit `i` of a U32, counting from the least significant. `i >= 32n` is False.
def U32.bit(x: U32, i: Nat) -> Bool:
  Word.get(32n, U32.word(x), i)

# The number of set bits of a bit vector, as a Nat (a native, overflow-checked
# unsigned counter in this runtime -- see core/count.bend).
def Word.count(n: Nat, w: Word(n)) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Word.count(p, t)
        case WCon{True{}, t}:
          1n+Word.count(p, t)

# ---------------------------------------------------------------------------
# The production operations.
# ---------------------------------------------------------------------------

# Set difference on one word: the bits of `a` that `b` does not have.
# Two native instructions; the whole fused kernel is built on this.
def U32.diff(a: U32, b: U32) -> U32:
  U32.and(a, U32.not(b))

# The low bit of a word as a 0/1 Nat. `U32.and(x, 1)` is one native
# instruction and `U32.to_nat` is the identity in the emitted C, so this costs
# two instructions and no allocation -- while the checker still sees it as the
# head of the bit vector.
def U32.low(+x: U32) -> Nat:
  U32.to_nat(U32.and(x, 1))

# Add one to a Nat counter when the bit is set. A separate def because Bend
# matches parameters, never computed values.
def U32.bump(b: Bool, acc: Nat) -> Nat:
  match b:
    case False{}:
      acc
    case True{}:
      1n+acc

# popcount as one shift per bit: three native instructions per bit, no
# allocation, and a tail loop in the emitted C. `k` shrinks first so the
# termination check passes and so the compiler keeps the loop flat.
def U32.popcount.go(+k: Nat, +x: U32, acc: Nat) -> Nat:
  match k:
    case 0n:
      acc
    case 1n+p:
      U32.popcount.go(p, U32.shr(x), Nat.add(U32.low(x), acc))

def U32.popcount(+x: U32) -> Nat:
  U32.popcount.go(32n, x, 0n)

# The same count without the accumulator: the shape the loop refines.
def U32.lowcount(+k: Nat, +x: U32) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+p:
      Nat.add(U32.low(x), U32.lowcount(p, U32.shr(x)))

# The bit vector with exactly the positions below `k` set.
def Word.low_mask(n: Nat, k: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match k:
        case 0n:
          WCon{False{}, Word.low_mask(p, 0n)}
        case 1n+j:
          WCon{True{}, Word.low_mask(p, j)}

# The mask of the low `k` bits. Built through the bit vector rather than by
# shifting: it is computed once per query, for the one word that straddles the
# end of the universe, so the 32 cells it costs never enter a loop -- and the
# bit-for-bit statement `U32.bit(U32.mask(k), i) == (i < k)` is then provable
# without any 32-bit carry reasoning. Every position at or above N must read
# as absent, so a dense leaf's padding bits can never be counted as objects
# (SPEC 5.5).
def U32.mask(k: Nat) -> U32:
  U32{Word.low_mask(32n, k)}

# ---------------------------------------------------------------------------
# Word-list tiles. A tile is the flat shape the leaf kernels walk: a cons list
# of words, owned by the job that reads it (see docs/evidence/T01.md).
# ---------------------------------------------------------------------------

def Words() -> Data:
  List<&2, U32>

# ---------------------------------------------------------------------------
# The specification side of popcount: the cardinality of the bits `U32.bit`
# reports set, over the positions below `k`. This mentions nothing but bit
# membership, so it is the statement `B-01` is worth making.
# ---------------------------------------------------------------------------

def U32.card(+k: Nat, +x: U32) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+p:
      U32.bump(U32.bit(x, p), U32.card(p, x))
