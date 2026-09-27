# proofs/bitset.bend -- setting a bit, and reading it back (part of law P-01).
#
# `Words.set` ORs a one-bit mask into the word the ordinal lives in, and
# `Words.bit` reads the same position back. This file proves they agree: after
# setting position (i, b) of a tile, reading position (i, b) answers `True{}`.
#
# It answers `True{}` *if the tile has a word i at all*. It is not a
# conditional dressed up as a law -- it is the law, because `Words.set.at`
# past the end of a tile silently changes nothing and `Words.at` past the end
# reads `False{}`. So the right-hand side is exactly "the tile has that word",
# and the equation is unconditional in `ws`. tests.bend keeps the
# counterexample that shows why: a `PDense` leaf that is not 128 words wide
# loses the bit it was just given.
#
# The one genuine side condition is on `b`: a bit index has to be a bit index.
# `U32.shln(1, 32n)` is zero, so setting "bit 32" of a word sets nothing, and
# the law would be false without `b < 32`.
#
# The work is a shift lemma. `U32.shln(1, b)` is `b` left shifts of one, and
# the claim is that the result has bit `b` set. `Word.shl` pushes a `False{}`
# in at the bottom and moves everything up through `Word.shl.put`, so the
# induction is on that.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./word.bend as PW
import ./bits.bend as PB
import ./words.bend as PWo
import ./addr.bend as PA
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo

# ---------------------------------------------------------------------------
# The shift. `Word.shl.put(n, c, w)` writes `c` at the bottom and moves `w`
# up one, so reading index `i` of it is reading index `i` of `WCon{c, w}` --
# as long as index `i` is still inside the word.
# ---------------------------------------------------------------------------

law Word.get_shl_put:
  for +p: Nat
  for +c: Bool
  for +t: Word(p)
  for +i: Nat
  for +ok: {C.Nat.gt(p, i) == True{} : Bool}
  {W.Word.get(p, Word.shl.put(p, c, t), i)
    == W.Word.get(1n+p, WCon{c, t}, i) : Bool}

def Word.get_shl_put(p, c, t, i, ok):
  match p:
    case 0n:
      E.Bool.noconf({W.Word.get(0n, Word.shl.put(0n, c, t), i)
        == W.Word.get(1n, WCon{c, t}, i) : Bool}, ok)
    case 1n+q:
      match t:
        case WCon{b, t2}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              Word.get_shl_put(q, b, t2, j, ok)

law Word.get_shl:
  for +n: Nat
  for +w: Word(n)
  for +i: Nat
  for +ok: {C.Nat.gt(n, 1n+i) == True{} : Bool}
  {W.Word.get(n, Word.shl(n, w), 1n+i) == W.Word.get(n, w, i) : Bool}

def Word.get_shl(n, w, i, ok):
  match n:
    case 0n:
      E.Bool.noconf({W.Word.get(0n, Word.shl(0n, w), 1n+i)
        == W.Word.get(0n, w, i) : Bool}, ok)
    case 1n+p:
      match w:
        case WCon{b, t}:
          Word.get_shl_put(p, b, t, i, ok)

law U32.bit_shl:
  for +a: U32
  for +i: Nat
  for +ok: {C.Nat.gt(32n, 1n+i) == True{} : Bool}
  {W.U32.bit(U32.shl(a), 1n+i) == W.U32.bit(a, i) : Bool}

def U32.bit_shl(a, i, ok):
  match a:
    case U32{w}:
      Word.get_shl(32n, w, i, ok)

# ---------------------------------------------------------------------------
# The mask: `1 << b` has bit `b` set, for every bit index of a word.
# ---------------------------------------------------------------------------

law U32.bit_shln_one:
  for +b: Nat
  for +ok: {C.Nat.gt(32n, b) == True{} : Bool}
  {W.U32.bit(U32.shln(1, b), b) == True{} : Bool}

# `gt` is monotone downwards in its second argument, which is what carries the
# bound through the shift induction.
law Nat.gt.down:
  for +n: Nat
  for +i: Nat
  for +ok: {C.Nat.gt(n, 1n+i) == True{} : Bool}
  {C.Nat.gt(n, i) == True{} : Bool}

def Nat.gt.down(n, i, ok):
  match n:
    case 0n:
      E.Bool.noconf({C.Nat.gt(0n, i) == True{} : Bool}, ok)
    case 1n+p:
      match i:
        case 0n:
          {==}
        case 1n+j:
          Nat.gt.down(p, j, ok)

# ---------------------------------------------------------------------------
# One word, through the production bit test.
# ---------------------------------------------------------------------------

def U32.bit_shln_one(b, ok):
  match b:
    case 0n:
      {==}
    case 1n+i:
      %E.Bool.sym(W.U32.bit(U32.shl(U32.shln(1, i)), 1n+i),
        W.U32.bit(U32.shln(1, i), i),
        U32.bit_shl(U32.shln(1, i), i, ok))
        : {_ == True{} : Bool}
      U32.bit_shln_one(i, Nat.gt.down(32n, i, ok))

law U32.test_set:
  for +w: U32
  for +b: Nat
  for +ok: {C.Nat.gt(32n, b) == True{} : Bool}
  {Wo.U32.test(U32.or(w, U32.shln(1, b)), b) == True{} : Bool}

law Bool.or_true_r:
  for c: Bool
  {Bool.or(c, True{}) == True{} : Bool}

def Bool.or_true_r(c):
  match c:
    case False{}:
      {==}
    case True{}:
      {==}

# ---------------------------------------------------------------------------
# The tile.
# ---------------------------------------------------------------------------

def U32.test_set(w, b, ok):
  %E.Bool.sym(Wo.U32.test(U32.or(w, U32.shln(1, b)), b),
    Bool.or(Wo.U32.test(w, b), Wo.U32.test(U32.shln(1, b), b)),
    PWo.U32.test_or(w, U32.shln(1, b), b))
    : {_ == True{} : Bool}
  %E.Bool.sym(Wo.U32.test(U32.shln(1, b), b),
    W.U32.bit(U32.shln(1, b), b),
    PB.U32.test_spec(U32.shln(1, b), b))
    : {Bool.or(Wo.U32.test(w, b), _) == True{} : Bool}
  %E.Bool.sym(W.U32.bit(U32.shln(1, b), b), True{},
    U32.bit_shln_one(b, ok))
    : {Bool.or(Wo.U32.test(w, b), _) == True{} : Bool}
  Bool.or_true_r(Wo.U32.test(w, b))

law Words.at_set_at:
  for ws: List<&2, U32>
  for +i: Nat
  for +b: Nat
  for +ok: {C.Nat.gt(32n, b) == True{} : Bool}
  {Wo.Words.at(Wo.Words.set.at(ws, i, b), i, b)
    == Wo.Words.has_word(ws, i) : Bool}

def Words.at_set_at(ws, i, b, ok):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      match i:
        case 0n:
          U32.test_set(w, b, ok)
        case 1n+j:
          Words.at_set_at(t, j, b, ok)

# The `Words.bit` form: the same law with the ordinal doing the addressing.
# Unconditional, because proofs/addr.bend proves the bit index is a bit index.
law Words.bit_set:
  for ws: List<&2, U32>
  for +x: U32
  {Wo.Words.bit(Wo.Words.set(ws, x), x)
    == Wo.Words.has_word(ws, U32.to_nat(U32.shrn(x, 5n))) : Bool}

def Words.bit_set(ws, x):
  Words.at_set_at(ws, U32.to_nat(U32.shrn(x, 5n)),
    U32.to_nat(U32.and(x, 31)), PA.U32.low_five_bound(x))

# ---------------------------------------------------------------------------
# Setting one bit never clears another, which is what makes filling a tile
# from a list of offsets work.
# ---------------------------------------------------------------------------

law Words.at_set_at_mono:
  for ws: List<&2, U32>
  for +i: Nat
  for +j: Nat
  for +b: Nat
  for +c: Nat
  for +ok: {Wo.Words.at(ws, i, b) == True{} : Bool}
  {Wo.Words.at(Wo.Words.set.at(ws, j, c), i, b) == True{} : Bool}

def Words.at_set_at_mono(ws, i, j, b, c, ok):
  match ws:
    case Nil{}:
      E.Bool.noconf({Wo.Words.at(Wo.Words.set.at(Nil{}, j, c), i, b)
        == True{} : Bool}, ok)
    case Con{w, t}:
      match i:
        case 0n:
          match j:
            case 0n:
              # Same word: the set ORs a mask in, and `or` keeps a set bit.
              %E.Bool.sym(Wo.U32.test(U32.or(w, U32.shln(1, c)), b),
                Bool.or(Wo.U32.test(w, b), Wo.U32.test(U32.shln(1, c), b)),
                PWo.U32.test_or(w, U32.shln(1, c), b))
                : {_ == True{} : Bool}
              %E.Bool.sym(Wo.U32.test(w, b), True{}, ok)
                : {Bool.or(_, Wo.U32.test(U32.shln(1, c), b))
                    == True{} : Bool}
              {==}
            case 1n+j2:
              # A different word is set; this one is untouched.
              ok
        case 1n+i2:
          match j:
            case 0n:
              ok
            case 1n+j2:
              Words.at_set_at_mono(t, i2, j2, b, c, ok)

law Words.bit_set_mono:
  for ws: List<&2, U32>
  for +x: U32
  for +o: U32
  for +ok: {Wo.Words.bit(ws, x) == True{} : Bool}
  {Wo.Words.bit(Wo.Words.set(ws, o), x) == True{} : Bool}

def Words.bit_set_mono(ws, x, o, ok):
  Words.at_set_at_mono(ws, U32.to_nat(U32.shrn(x, 5n)),
    U32.to_nat(U32.shrn(o, 5n)), U32.to_nat(U32.and(x, 31)),
    U32.to_nat(U32.and(o, 31)), ok)

# Setting a bit does not change how many words the tile has.
law Words.has_word_set_at:
  for ws: List<&2, U32>
  for +i: Nat
  for +j: Nat
  for +c: Nat
  {Wo.Words.has_word(Wo.Words.set.at(ws, j, c), i)
    == Wo.Words.has_word(ws, i) : Bool}

def Words.has_word_set_at(ws, i, j, c):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      match i:
        case 0n:
          match j:
            case 0n:
              {==}
            case 1n+j2:
              {==}
        case 1n+i2:
          match j:
            case 0n:
              {==}
            case 1n+j2:
              Words.has_word_set_at(t, i2, j2, c)

law Words.has_word_set:
  for ws: List<&2, U32>
  for +i: Nat
  for +o: U32
  {Wo.Words.has_word(Wo.Words.set(ws, o), i) == Wo.Words.has_word(ws, i) : Bool}

def Words.has_word_set(ws, i, o):
  Words.has_word_set_at(ws, i, U32.to_nat(U32.shrn(o, 5n)),
    U32.to_nat(U32.and(o, 31)))
