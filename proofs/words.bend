# proofs/words.bend -- the flat-kernel contracts (laws S-01, R-01, Q-02).
#
# A tile is a cons list of `U32` words, and `Words.at(ws, i, k)` reads bit `k`
# of word `i`. Everything below is stated pointwise against that reader:
# a tile operation is correct when every position of the result is the
# Boolean of the same positions of the operands.
#
# Two things make these laws unconditional rather than length-indexed. A
# missing word reads as absent (`Words.at` past the end is False), and the
# binary operations treat a short operand as zero-padded. So `a` and `b` need
# not be the same length and no bounds hypothesis appears anywhere.
#
# The fused law at the end is the one SPEC 7.2 asks for: counting the
# difference without building it gives the same number as building it and
# counting.

import Base
import ./nat.bend as N
import ./word.bend as PW
import ./bits.bend as PB
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo

# ---------------------------------------------------------------------------
# One word, through the production bit test.
# ---------------------------------------------------------------------------

law U32.test_and:
  for +a: U32
  for +b: U32
  for +k: Nat
  {Wo.U32.test(U32.and(a, b), k)
    == Bool.and(Wo.U32.test(a, k), Wo.U32.test(b, k)) : Bool}

def U32.test_and(a, b, k):
  %N.Bool.flip(Wo.U32.test(a, k), W.U32.bit(a, k), PB.U32.test_spec(a, k))
    : {Wo.U32.test(U32.and(a, b), k)
        == Bool.and(_, Wo.U32.test(b, k)) : Bool}
  %N.Bool.flip(Wo.U32.test(b, k), W.U32.bit(b, k), PB.U32.test_spec(b, k))
    : {Wo.U32.test(U32.and(a, b), k)
        == Bool.and(W.U32.bit(a, k), _) : Bool}
  %N.Bool.flip(Wo.U32.test(U32.and(a, b), k),
    W.U32.bit(U32.and(a, b), k), PB.U32.test_spec(U32.and(a, b), k))
    : {_ == Bool.and(W.U32.bit(a, k), W.U32.bit(b, k)) : Bool}
  PW.U32.bit_and(a, b, k)

law U32.test_or:
  for +a: U32
  for +b: U32
  for +k: Nat
  {Wo.U32.test(U32.or(a, b), k)
    == Bool.or(Wo.U32.test(a, k), Wo.U32.test(b, k)) : Bool}

def U32.test_or(a, b, k):
  %N.Bool.flip(Wo.U32.test(a, k), W.U32.bit(a, k), PB.U32.test_spec(a, k))
    : {Wo.U32.test(U32.or(a, b), k)
        == Bool.or(_, Wo.U32.test(b, k)) : Bool}
  %N.Bool.flip(Wo.U32.test(b, k), W.U32.bit(b, k), PB.U32.test_spec(b, k))
    : {Wo.U32.test(U32.or(a, b), k)
        == Bool.or(W.U32.bit(a, k), _) : Bool}
  %N.Bool.flip(Wo.U32.test(U32.or(a, b), k),
    W.U32.bit(U32.or(a, b), k), PB.U32.test_spec(U32.or(a, b), k))
    : {_ == Bool.or(W.U32.bit(a, k), W.U32.bit(b, k)) : Bool}
  PW.U32.bit_or(a, b, k)

law U32.test_diff:
  for +a: U32
  for +b: U32
  for +k: Nat
  {Wo.U32.test(W.U32.diff(a, b), k)
    == Bool.and(Wo.U32.test(a, k), Bool.not(Wo.U32.test(b, k))) : Bool}

def U32.test_diff(a, b, k):
  %N.Bool.flip(Wo.U32.test(a, k), W.U32.bit(a, k), PB.U32.test_spec(a, k))
    : {Wo.U32.test(W.U32.diff(a, b), k)
        == Bool.and(_, Bool.not(Wo.U32.test(b, k))) : Bool}
  %N.Bool.flip(Wo.U32.test(b, k), W.U32.bit(b, k), PB.U32.test_spec(b, k))
    : {Wo.U32.test(W.U32.diff(a, b), k)
        == Bool.and(W.U32.bit(a, k), Bool.not(_)) : Bool}
  %N.Bool.flip(Wo.U32.test(W.U32.diff(a, b), k),
    W.U32.bit(W.U32.diff(a, b), k), PB.U32.test_spec(W.U32.diff(a, b), k))
    : {_ == Bool.and(W.U32.bit(a, k), Bool.not(W.U32.bit(b, k))) : Bool}
  PW.U32.bit_diff(a, b, k)

# ---------------------------------------------------------------------------
# A tile. Induction on the first operand, then the second, then the word
# index -- the three shapes `Words.at` walks.
# ---------------------------------------------------------------------------

law Words.at_and:
  for a: List<&2, U32>
  for b: List<&2, U32>
  for i: Nat
  for +k: Nat
  {Wo.Words.at(Wo.Words.and(a, b), i, k)
    == Bool.and(Wo.Words.at(a, i, k), Wo.Words.at(b, i, k)) : Bool}

law Words.or_nil_word:
  for +ah: U32
  for +k: Nat
  {Wo.U32.test(ah, k) == Bool.or(Wo.U32.test(ah, k), False{}) : Bool}

law Bool.or_false:
  for b: Bool
  {b == Bool.or(b, False{}) : Bool}

def Bool.or_false(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Words.or_nil_word(ah, k):
  Bool.or_false(Wo.U32.test(ah, k))

law Words.at_or:
  for a: List<&2, U32>
  for b: List<&2, U32>
  for i: Nat
  for +k: Nat
  {Wo.Words.at(Wo.Words.or(a, b), i, k)
    == Bool.or(Wo.Words.at(a, i, k), Wo.Words.at(b, i, k)) : Bool}

law Words.or_nil_rest:
  for at: List<&2, U32>
  for j: Nat
  for +k: Nat
  {Wo.Words.at(at, j, k)
    == Bool.or(Wo.Words.at(at, j, k), False{}) : Bool}

def Words.or_nil_rest(at, j, k):
  Bool.or_false(Wo.Words.at(at, j, k))

def Words.at_or(a, b, i, k):
  match a:
    case Nil{}:
      {==}
    case Con{ah, at}:
      match b:
        case Nil{}:
          match i:
            case 0n:
              Words.or_nil_word(ah, k)
            case 1n+j:
              Words.or_nil_rest(at, j, k)
        case Con{bh, bt}:
          match i:
            case 0n:
              U32.test_or(ah, bh, k)
            case 1n+j:
              Words.at_or(at, bt, j, k)

law Bool.and_false:
  for b: Bool
  {False{} == Bool.and(b, False{}) : Bool}

def Bool.and_false(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Words.at_and(a, b, i, k):
  match a:
    case Nil{}:
      {==}
    case Con{ah, at}:
      match b:
        case Nil{}:
          match i:
            case 0n:
              Bool.and_false(Wo.U32.test(ah, k))
            case 1n+j:
              Bool.and_false(Wo.Words.at(at, j, k))
        case Con{bh, bt}:
          match i:
            case 0n:
              U32.test_and(ah, bh, k)
            case 1n+j:
              Words.at_and(at, bt, j, k)

law Bool.and_true:
  for b: Bool
  {b == Bool.and(b, True{}) : Bool}

def Bool.and_true(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law Words.diff_nil_word:
  for +ah: U32
  for +k: Nat
  {Wo.U32.test(ah, k)
    == Bool.and(Wo.U32.test(ah, k), Bool.not(False{})) : Bool}

def Words.diff_nil_word(ah, k):
  Bool.and_true(Wo.U32.test(ah, k))

law Words.at_diff:
  for a: List<&2, U32>
  for b: List<&2, U32>
  for i: Nat
  for +k: Nat
  {Wo.Words.at(Wo.Words.diff(a, b), i, k)
    == Bool.and(Wo.Words.at(a, i, k),
         Bool.not(Wo.Words.at(b, i, k))) : Bool}

law Words.diff_nil_rest:
  for at: List<&2, U32>
  for j: Nat
  for +k: Nat
  {Wo.Words.at(at, j, k)
    == Bool.and(Wo.Words.at(at, j, k), Bool.not(False{})) : Bool}

def Words.diff_nil_rest(at, j, k):
  Bool.and_true(Wo.Words.at(at, j, k))

# ---------------------------------------------------------------------------
# The fused reduction of SPEC 7.2. Counting `a \ b` as it goes gives the same
# answer as building `a \ b` and counting it -- which is what makes it legal
# for a matrix cell never to allocate the difference.
# ---------------------------------------------------------------------------

def Words.at_diff(a, b, i, k):
  match a:
    case Nil{}:
      {==}
    case Con{ah, at}:
      match b:
        case Nil{}:
          match i:
            case 0n:
              Words.diff_nil_word(ah, k)
            case 1n+j:
              Words.diff_nil_rest(at, j, k)
        case Con{bh, bt}:
          match i:
            case 0n:
              U32.test_diff(ah, bh, k)
            case 1n+j:
              Words.at_diff(at, bt, j, k)

law Words.diff_count_go:
  for a: List<&2, U32>
  for b: List<&2, U32>
  for acc: Nat
  {Wo.Words.diff_count.go(a, b, acc)
    == Wo.Words.count.go(Wo.Words.diff(a, b), acc) : Nat}

def Words.diff_count_go(a, b, acc):
  match a:
    case Nil{}:
      {==}
    case Con{ah, at}:
      match b:
        case Nil{}:
          {==}
        case Con{bh, bt}:
          Words.diff_count_go(at, bt,
            Nat.add(W.U32.popcount(W.U32.diff(ah, bh)), acc))

law Words.diff_count_spec:
  for a: List<&2, U32>
  for b: List<&2, U32>
  {Wo.Words.diff_count(a, b)
    == Wo.Words.count(Wo.Words.diff(a, b)) : Nat}

def Words.diff_count_spec(a, b):
  Words.diff_count_go(a, b, 0n)
