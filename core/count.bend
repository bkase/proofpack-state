# core/count.bend -- the checked counting layer (law family B-02).
#
# SPEC 5.4 asks for a checked pair-of-U32 accumulator for 64-bit counts and
# byte sums, proved against natural-number arithmetic with overflow detected
# rather than wrapped. This runtime already provides exactly that, and
# re-implementing limbs on top of it would add trusted code rather than remove
# it: Bend's `Nat` compiles to a native unsigned integer, `Nat.add` to a single
# machine add, and `nat_chk` posts a runtime error at 2^48-1 instead of
# wrapping. So `Nat` *is* the checked accumulator, its equations are Peano's,
# and every count and byte-sum law is provable by ordinary induction.
#
# What that leaves to do, and what this module does, is the admission bound:
# a weight table is admitted only when the total weight over the whole
# universe fits under the ceiling. Every subset sum is then bounded by that
# total, so no reduction inside an admitted query can reach the ceiling.
# Tables that do not fit are rejected with `NumericOverflow` at admission.

import Base

# The ceiling this runtime's Nat can hold: 2^48 - 1 = 281474976710655.
# Past this the runtime posts an error; it does not wrap and does not saturate
# silently. v0.1 documents it as a first-release limit (SPEC 5.4).
def Count.two32() -> Nat:
  1n+4294967295n

def Count.ceiling() -> Nat:
  Nat.add(Nat.mul(65535n, Count.two32()), 4294967295n)

# `k > i`, that is, `i` is below `k`. The bound comes first so that
# `Nat.gt(0n, i)` reduces to False without knowing `i`, and so that the match
# order follows the binder order Bend requires. Base's `Nat.is_lt` goes
# through `Nat.cmp`, which gets stuck on a symbolic argument in a proof.
def Nat.gt(k: Nat, i: Nat) -> Bool:
  match k:
    case 0n:
      False{}
    case 1n+q:
      match i:
        case 0n:
          True{}
        case 1n+j:
          Nat.gt(q, j)

# `a <= b`, same shape.
def Nat.upto(a: Nat, b: Nat) -> Bool:
  match a:
    case 0n:
      True{}
    case 1n+p:
      match b:
        case 0n:
          False{}
        case 1n+q:
          Nat.upto(p, q)

# A checked add: `None` when the sum would pass the ceiling. The test is made
# *before* the addition -- `Nat.sub` saturates at zero in this runtime and
# never overflows -- so the ceiling is never actually crossed. Production code
# that sums an untrusted table uses this and reports `NumericOverflow`.
def Count.add.fin(a: Nat, b: Nat, ok: Bool) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{Nat.add(a, b)}
    case False{}:
      None{}

def Count.add(+a: Nat, +b: Nat) -> Maybe<&2, Nat>:
  Count.add.fin(a, b, Nat.upto(a, Nat.sub(Count.ceiling(), b)))
