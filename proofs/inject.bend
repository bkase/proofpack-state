# proofs/inject.bend -- addressing fact A3: the tile address is injective.
#
# `Words.bit(ws, x)` reads word `x >> 5`, bit `x & 31`. For a sparse leaf and
# the tile it spreads into to have the same members, that address has to be
# injective: two different ordinals must not land on the same bit of the same
# word. Otherwise setting one offset could be read back as another, and the
# sparse/dense crossover would change a set's denotation -- which is exactly
# what law S-03 denies.
#
# The route is: `Word.to_nat` is injective, so equal addresses give equal
# shifted and masked words; then the ordinal is reconstructed bit by bit, the
# low five from the mask and the rest from the shift.
#
# The `Nat` side of that needs one fact this runtime's `Nat` does not ship: a
# doubled number is never one more than a doubled number. That is parity, and
# it is what separates the two halves of a bit vector.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ../core/count.bend as C
import ../core/word.bend as W

# ---------------------------------------------------------------------------
# Using a false equation at `Nat`.
# ---------------------------------------------------------------------------

def Nat.code(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def Nat.empty(e: {0n == 1n+0n : Nat}) -> Empty:
  %e : Nat.code(_)
  Unit{}

def Nat.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

law Nat.succ_inj:
  for +a: Nat
  for +b: Nat
  for +e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

def Nat.succ_inj(a, b, e):
  Equal.cong(Nat, Nat, Nat.pred, 1n+a, 1n+b, e)

# Collapses every successor to one, so a single `Nat.code` covers them all.
def Nat.trim(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      1n+0n

# ---------------------------------------------------------------------------
# Parity, and doubling.
# ---------------------------------------------------------------------------

def Nat.noconf(-A: Type, -k: Nat, e: {0n == 1n+k : Nat}) -> A:
  Empty.absurd(A, Nat.empty(Equal.cong(Nat, Nat, Nat.trim, 0n, 1n+k, e)))

law Nat.double_not_succ:
  for +a: Nat
  for +b: Nat
  for +e: {Nat.double(a) == 1n+Nat.double(b) : Nat}
  {Empty : Type}

def Nat.double_not_succ(a, b, e):
  match a:
    case 0n:
      Nat.noconf(Empty, Nat.double(b), e)
    case 1n+p:
      match b:
        case 0n:
          Nat.noconf(Empty, Nat.double(p),
            E.Nat.sym(1n+Nat.double(p), 0n,
              Nat.succ_inj(1n+Nat.double(p), 0n, e)))
        case 1n+q:
          Nat.double_not_succ(p, q,
            Nat.succ_inj(Nat.double(p), 1n+Nat.double(q),
              Nat.succ_inj(1n+Nat.double(p), 2n+Nat.double(q), e)))

law Nat.double_inj:
  for +a: Nat
  for +b: Nat
  for +e: {Nat.double(a) == Nat.double(b) : Nat}
  {a == b : Nat}

def Nat.double_inj(a, b, e):
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          Nat.noconf({0n == 1n+q : Nat}, 1n+Nat.double(q), e)
    case 1n+p:
      match b:
        case 0n:
          Nat.noconf({1n+p == 0n : Nat}, 1n+Nat.double(p),
            E.Nat.sym(2n+Nat.double(p), 0n, e))
        case 1n+q:
          %Nat.double_inj(p, q,
            Nat.succ_inj(Nat.double(p), Nat.double(q),
              Nat.succ_inj(1n+Nat.double(p), 1n+Nat.double(q), e)))
            : {1n+p == 1n+_ : Nat}
          {==}

# ---------------------------------------------------------------------------
# `Word.to_nat` is injective. The head bit is the parity and the tail is the
# halved value, so an equality of numbers splits into an equality of bits and
# an equality of tails.
# ---------------------------------------------------------------------------

law Word.to_nat_head_eq:
  for +p: Nat
  for +ab: Bool
  for +bb: Bool
  for +at: Word(p)
  for +bt: Word(p)
  for +e: {Word.to_nat(1n+p, WCon{ab, at})
    == Word.to_nat(1n+p, WCon{bb, bt}) : Nat}
  {ab == bb : Bool}

def Word.to_nat_head_eq(p, ab, bb, at, bt, e):
  match ab bb:
    case False{} False{}:
      {==}
    case True{} True{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool},
        Nat.double_not_succ(Word.to_nat(p, at), Word.to_nat(p, bt), e))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool},
        Nat.double_not_succ(Word.to_nat(p, bt), Word.to_nat(p, at),
          E.Nat.sym(1n+Nat.double(Word.to_nat(p, at)),
            Nat.double(Word.to_nat(p, bt)), e)))

law Word.to_nat_tail_eq:
  for +p: Nat
  for +ab: Bool
  for +bb: Bool
  for +at: Word(p)
  for +bt: Word(p)
  for +e: {Word.to_nat(1n+p, WCon{ab, at})
    == Word.to_nat(1n+p, WCon{bb, bt}) : Nat}
  {Word.to_nat(p, at) == Word.to_nat(p, bt) : Nat}

def Word.to_nat_tail_eq(p, ab, bb, at, bt, e):
  match ab bb:
    case False{} False{}:
      Nat.double_inj(Word.to_nat(p, at), Word.to_nat(p, bt), e)
    case True{} True{}:
      Nat.double_inj(Word.to_nat(p, at), Word.to_nat(p, bt),
        Nat.succ_inj(Nat.double(Word.to_nat(p, at)),
          Nat.double(Word.to_nat(p, bt)), e))
    case False{} True{}:
      Empty.absurd({Word.to_nat(p, at) == Word.to_nat(p, bt) : Nat},
        Nat.double_not_succ(Word.to_nat(p, at), Word.to_nat(p, bt), e))
    case True{} False{}:
      Empty.absurd({Word.to_nat(p, at) == Word.to_nat(p, bt) : Nat},
        Nat.double_not_succ(Word.to_nat(p, bt), Word.to_nat(p, at),
          E.Nat.sym(1n+Nat.double(Word.to_nat(p, at)),
            Nat.double(Word.to_nat(p, bt)), e)))

law Word.to_nat_inj:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +e: {Word.to_nat(n, a) == Word.to_nat(n, b) : Nat}
  {a == b : Word(n)}

def Word.to_nat_inj(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          %Word.to_nat_head_eq(p, ab, bb, at, bt, e)
            : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
          %Word.to_nat_inj(p, at, bt,
            Word.to_nat_tail_eq(p, ab, bb, at, bt, e))
            : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
          {==}

law U32.to_nat_inj:
  for +a: U32
  for +b: U32
  for +e: {U32.to_nat(a) == U32.to_nat(b) : Nat}
  {a == b : U32}

def U32.to_nat_inj(a, b, e):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, E.U32.pak, x, y,
        Word.to_nat_inj(32n, x, y, e))

# ---------------------------------------------------------------------------
# What is still missing, and why it is not here.
#
# A3 in full -- that the tile address `x -> (x >> 5, x & 31)` is injective --
# needs one more step from here: that two words with the same bits are the
# same word. The natural statement of that takes a hypothesis quantified over
# bit positions, and Bend's affine values will not let such a hypothesis be
# used twice, which an induction down a vector has to do: once for the head
# bit and once for the tail. Encoding "same bits" as a `Bool` instead makes
# the hypothesis reusable but moves the problem to relating that encoding to
# the mask and shift, which is the same work in a different place.
#
# So A3 remains open, and with it the direction of the sparse/dense bridge
# that reads a member *out of* a tile. The direction that puts one in is
# proved (proofs/leaf.bend), and it is the one P-01 needed.
