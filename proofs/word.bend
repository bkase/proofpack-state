# proofs/word.bend -- the bit-level lemmas behind law family B-01.
#
# Every lemma is stated over `Word(n)` and proved by induction on `n`, then
# lifted to `U32` by one `match` that exposes the 32-bit vector Base defines
# `U32` to be. Nothing here runs: these are dead-code proofs over the very
# definitions the compiler lowers to single machine instructions.

import Base
import ./nat.bend as N
import ../core/count.bend as C
import ../core/word.bend as W

# ---------------------------------------------------------------------------
# Pointwise bit laws over Word(n).
# ---------------------------------------------------------------------------

law Word.get_zero:
  for n: Nat
  for i: Nat
  {W.Word.get(n, Word.zero(n), i) == False{} : Bool}

def Word.get_zero(n, i):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match i:
        case 0n:
          {==}
        case 1n+j:
          Word.get_zero(p, j)

law Word.and_zero:
  for n: Nat
  for +a: Word(n)
  {Word.and(n, a, Word.zero(n)) == Word.zero(n) : Word(n)}

def Word.and_zero(n, a):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{ab, at}:
          match ab:
            case False{}:
              %Word.and_zero(p, at)
                : {WCon{False{}, Word.and(p, at, Word.zero(p))}
                    == WCon{False{}, _} : Word(1n+p)}
              {==}
            case True{}:
              %Word.and_zero(p, at)
                : {WCon{False{}, Word.and(p, at, Word.zero(p))}
                    == WCon{False{}, _} : Word(1n+p)}
              {==}

law Word.get_and:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for i: Nat
  {W.Word.get(n, Word.and(n, a, b), i)
    == Bool.and(W.Word.get(n, a, i), W.Word.get(n, b, i)) : Bool}

def Word.get_and(n, a, b, i):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b i:
        case WCon{ab, at} WCon{bb, bt} 0n:
          {==}
        case WCon{ab, at} WCon{bb, bt} 1n+j:
          Word.get_and(p, at, bt, j)

law Word.get_or:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for i: Nat
  {W.Word.get(n, Word.or(n, a, b), i)
    == Bool.or(W.Word.get(n, a, i), W.Word.get(n, b, i)) : Bool}

def Word.get_or(n, a, b, i):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b i:
        case WCon{ab, at} WCon{bb, bt} 0n:
          {==}
        case WCon{ab, at} WCon{bb, bt} 1n+j:
          Word.get_or(p, at, bt, j)

# `not` on its own is wrong out of range -- `get` reads absent past the end,
# and `not` of absent is present. Intersecting with a real operand kills that,
# which is why difference is one law rather than two composed.
law Word.get_and_not:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for i: Nat
  {W.Word.get(n, Word.and(n, a, Word.not(n, b)), i)
    == Bool.and(W.Word.get(n, a, i), Bool.not(W.Word.get(n, b, i))) : Bool}

def Word.get_and_not(n, a, b, i):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b i:
        case WCon{ab, at} WCon{bb, bt} 0n:
          {==}
        case WCon{ab, at} WCon{bb, bt} 1n+j:
          Word.get_and_not(p, at, bt, j)

# Shifting right drops the low bit and pads a False in at the top; the pad is
# invisible to every read, and reading position i of `shr w` is reading
# position i+1 of `w`.
law Word.get_pad:
  for n: Nat
  for w: Word(n)
  for i: Nat
  {W.Word.get(1n+n, Word.shr.pad(n, w), i) == W.Word.get(n, w, i) : Bool}

def Word.get_pad(n, w, i):
  match n:
    case 0n:
      match w:
        case WNil{}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              Word.get_pad(p, t, j)

law Word.get_shr:
  for n: Nat
  for w: Word(n)
  for i: Nat
  {W.Word.get(n, Word.shr(n, w), i) == W.Word.get(n, w, 1n+i) : Bool}

def Word.get_shr(n, w, i):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Word.get_pad(p, t, i)

# The mask of the low k bits, within a word of n bits.
law Word.get_low_mask:
  for n: Nat
  for k: Nat
  for i: Nat
  {W.Word.get(n, W.Word.low_mask(n, k), i)
    == Bool.and(C.Nat.gt(n, i), C.Nat.gt(k, i)) : Bool}

def Word.get_low_mask(n, k, i):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match k i:
        case 0n 0n:
          {==}
        case 0n 1n+j:
          Word.get_low_mask(p, 0n, j)
        case 1n+q 0n:
          {==}
        case 1n+q 1n+j:
          Word.get_low_mask(p, q, j)

# ---------------------------------------------------------------------------
# Lifting to U32.
# ---------------------------------------------------------------------------

law U32.bit_and:
  for a: U32
  for b: U32
  for i: Nat
  {W.U32.bit(U32.and(a, b), i)
    == Bool.and(W.U32.bit(a, i), W.U32.bit(b, i)) : Bool}

def U32.bit_and(a, b, i):
  match a b:
    case U32{x} U32{y}:
      Word.get_and(32n, x, y, i)

law U32.bit_or:
  for a: U32
  for b: U32
  for i: Nat
  {W.U32.bit(U32.or(a, b), i)
    == Bool.or(W.U32.bit(a, i), W.U32.bit(b, i)) : Bool}

def U32.bit_or(a, b, i):
  match a b:
    case U32{x} U32{y}:
      Word.get_or(32n, x, y, i)

law U32.bit_diff:
  for a: U32
  for b: U32
  for i: Nat
  {W.U32.bit(W.U32.diff(a, b), i)
    == Bool.and(W.U32.bit(a, i), Bool.not(W.U32.bit(b, i))) : Bool}

def U32.bit_diff(a, b, i):
  match a b:
    case U32{x} U32{y}:
      Word.get_and_not(32n, x, y, i)

law U32.bit_shr:
  for a: U32
  for i: Nat
  {W.U32.bit(U32.shr(a), i) == W.U32.bit(a, 1n+i) : Bool}

def U32.bit_shr(a, i):
  match a:
    case U32{x}:
      Word.get_shr(32n, x, i)

law U32.bit_mask:
  for k: Nat
  for i: Nat
  {W.U32.bit(W.U32.mask(k), i)
    == Bool.and(C.Nat.gt(32n, i), C.Nat.gt(k, i)) : Bool}

def U32.bit_mask(k, i):
  Word.get_low_mask(32n, k, i)

law U32.bit_zero:
  for i: Nat
  {W.U32.bit(0, i) == False{} : Bool}

def U32.bit_zero(i):
  Word.get_zero(32n, i)
