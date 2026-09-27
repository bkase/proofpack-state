# proofs/bits.bend -- from a shifted read to a bit index.
#
# The production bit test is `U32.test(w, b) = is_one(low(shrn(w, b)))`: shift
# the wanted bit down and look at the bottom. Every law elsewhere is stated
# against `U32.bit`, which reads the bit vector `U32` is defined as. These two
# lemmas are the bridge, and they are what lets the hot loop use native shifts
# while the laws talk about bits.

import Base
import ./nat.bend as N
import ./word.bend as PW
import ./popcount.bend as PP
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo

# Shifting `n` down and reading bit `i` is reading bit `n + i`.
law U32.bit_shrn:
  for +n: Nat
  for +a: U32
  for +i: Nat
  {W.U32.bit(U32.shrn(a, n), i) == W.U32.bit(a, Nat.add(n, i)) : Bool}

def U32.bit_shrn(n, a, i):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %N.Nat.add_succ(p, i)
        : {W.U32.bit(U32.shr(U32.shrn(a, p)), i) == W.U32.bit(a, _) : Bool}
      %U32.bit_shrn(p, a, 1n+i)
        : {W.U32.bit(U32.shr(U32.shrn(a, p)), i) == _ : Bool}
      PW.U32.bit_shr(U32.shrn(a, p), i)

law Nat.is_one_bump:
  for b: Bool
  {Wo.Nat.is_one(W.U32.bump(b, 0n)) == b : Bool}

def Nat.is_one_bump(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# The production bit test agrees with the specification's bit accessor.
law U32.test_spec:
  for +w: U32
  for +b: Nat
  {Wo.U32.test(w, b) == W.U32.bit(w, b) : Bool}

def U32.test_spec(w, b):
  %N.Nat.add_zero(b)
    : {Wo.Nat.is_one(W.U32.low(U32.shrn(w, b))) == W.U32.bit(w, _) : Bool}
  %U32.bit_shrn(b, w, 0n)
    : {Wo.Nat.is_one(W.U32.low(U32.shrn(w, b))) == _ : Bool}
  %N.Nat.flip(W.U32.low(U32.shrn(w, b)),
    W.U32.bump(W.U32.bit(U32.shrn(w, b), 0n), 0n),
    PP.U32.low_spec(U32.shrn(w, b)))
    : {Wo.Nat.is_one(_) == W.U32.bit(U32.shrn(w, b), 0n) : Bool}
  Nat.is_one_bump(W.U32.bit(U32.shrn(w, b), 0n))
