# proofs/popcount.bend -- law B-01c: the production popcount counts exactly
# the bits that `U32.bit` reports set.
#
# The production loop peels the *low* bit and carries an accumulator; the
# specification `U32.card` peels the *top* bit and carries nothing. The three
# steps below close that gap: drop the accumulator, turn the low-peeling form
# into the top-peeling one, and read off the 32-bit instance.

import Base
import ./nat.bend as N
import ./word.bend as PW
import ../core/word.bend as W

# ---------------------------------------------------------------------------
# Rearranging Nat sums.
# ---------------------------------------------------------------------------

law Nat.add_swap:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(b, a), c) : Nat}

def Nat.add_swap(a, b, c):
  %Equal.sym(Nat, Nat.add(b, a), Nat.add(a, b), N.Nat.add_comm(b, a))
    : {Nat.add(a, Nat.add(b, c)) == Nat.add(_, c) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)),
    N.Nat.add_assoc(a, b, c))

law Nat.bump_add:
  for b: Bool
  for +m: Nat
  for +c: Nat
  {W.U32.bump(b, Nat.add(m, c)) == Nat.add(m, W.U32.bump(b, c)) : Nat}

def Nat.bump_add(b, m, c):
  match b:
    case False{}:
      {==}
    case True{}:
      Equal.sym(Nat, Nat.add(m, 1n+c), 1n+Nat.add(m, c), N.Nat.add_succ(m, c))

# ---------------------------------------------------------------------------
# The low bit as a 0/1 Nat.
# ---------------------------------------------------------------------------

law U32.low_spec:
  for x: U32
  {W.U32.low(x) == W.U32.bump(W.U32.bit(x, 0n), 0n) : Nat}

def U32.low_spec(x):
  match x:
    case U32{w}:
      match w:
        case WCon{b, t}:
          match b:
            case False{}:
              %Equal.sym(Word(31n), Word.and(31n, t, Word.zero(31n)),
                Word.zero(31n), PW.Word.and_zero(31n, t))
                : {Nat.double(Word.to_nat(31n, _)) == 0n : Nat}
              {==}
            case True{}:
              %Equal.sym(Word(31n), Word.and(31n, t, Word.zero(31n)),
                Word.zero(31n), PW.Word.and_zero(31n, t))
                : {1n+Nat.double(Word.to_nat(31n, _)) == 1n : Nat}
              {==}

# ---------------------------------------------------------------------------
# Dropping the accumulator.
# ---------------------------------------------------------------------------

law U32.popcount_go_spec:
  for +k: Nat
  for +x: U32
  for +acc: Nat
  {W.U32.popcount.go(k, x, acc)
    == Nat.add(W.U32.lowcount(k, x), acc) : Nat}

def U32.popcount_go_spec(k, x, acc):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %N.Nat.flip(W.U32.popcount.go(p, U32.shr(x), Nat.add(W.U32.low(x), acc)),
        Nat.add(W.U32.lowcount(p, U32.shr(x)), Nat.add(W.U32.low(x), acc)),
        U32.popcount_go_spec(p, U32.shr(x), Nat.add(W.U32.low(x), acc)))
        : {_ == Nat.add(W.U32.lowcount(1n+p, x), acc) : Nat}
      Nat.add_swap(W.U32.lowcount(p, U32.shr(x)), W.U32.low(x), acc)

# ---------------------------------------------------------------------------
# From peeling the low bit to peeling the top bit.
# ---------------------------------------------------------------------------

law U32.card_peel:
  for +p: Nat
  for +x: U32
  {W.U32.card(1n+p, x)
    == Nat.add(W.U32.low(x), W.U32.card(p, U32.shr(x))) : Nat}

def U32.card_peel(p, x):
  match p:
    case 0n:
      %Equal.sym(Nat, W.U32.low(x), W.U32.bump(W.U32.bit(x, 0n), 0n),
        U32.low_spec(x))
        : {W.U32.bump(W.U32.bit(x, 0n), 0n) == Nat.add(_, 0n) : Nat}
      Equal.sym(Nat, Nat.add(W.U32.bump(W.U32.bit(x, 0n), 0n), 0n),
        W.U32.bump(W.U32.bit(x, 0n), 0n),
        N.Nat.add_zero(W.U32.bump(W.U32.bit(x, 0n), 0n)))
    case 1n+q:
      %N.Bool.flip(W.U32.bit(U32.shr(x), q), W.U32.bit(x, 1n+q),
        PW.U32.bit_shr(x, q))
        : {W.U32.bump(W.U32.bit(x, 1n+q), W.U32.card(1n+q, x))
            == Nat.add(W.U32.low(x),
                 W.U32.bump(_, W.U32.card(q, U32.shr(x)))) : Nat}
      %N.Nat.flip(W.U32.card(1n+q, x),
        Nat.add(W.U32.low(x), W.U32.card(q, U32.shr(x))),
        U32.card_peel(q, x))
        : {W.U32.bump(W.U32.bit(x, 1n+q), _)
            == Nat.add(W.U32.low(x),
                 W.U32.bump(W.U32.bit(x, 1n+q),
                   W.U32.card(q, U32.shr(x)))) : Nat}
      Nat.bump_add(W.U32.bit(x, 1n+q), W.U32.low(x),
        W.U32.card(q, U32.shr(x)))

law U32.lowcount_card:
  for +k: Nat
  for +x: U32
  {W.U32.lowcount(k, x) == W.U32.card(k, x) : Nat}

def U32.lowcount_card(k, x):
  match k:
    case 0n:
      {==}
    case 1n+p:
      %N.Nat.flip(W.U32.lowcount(p, U32.shr(x)), W.U32.card(p, U32.shr(x)),
        U32.lowcount_card(p, U32.shr(x)))
        : {Nat.add(W.U32.low(x), _) == W.U32.card(1n+p, x) : Nat}
      Equal.sym(Nat, W.U32.card(1n+p, x),
        Nat.add(W.U32.low(x), W.U32.card(p, U32.shr(x))),
        U32.card_peel(p, x))

# ---------------------------------------------------------------------------
# B-01c.
# ---------------------------------------------------------------------------

law U32.popcount_spec:
  for +x: U32
  {W.U32.popcount(x) == W.U32.card(32n, x) : Nat}

def U32.popcount_spec(x):
  %U32.lowcount_card(32n, x)
    : {W.U32.popcount.go(32n, x, 0n) == _ : Nat}
  %N.Nat.add_zero(W.U32.lowcount(32n, x))
    : {W.U32.popcount.go(32n, x, 0n) == _ : Nat}
  U32.popcount_go_spec(32n, x, 0n)
