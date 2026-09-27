# proofs/decr.bend -- what subtracting one does to a word.
#
# `PSet.range` enumerates a full interval by counting down, so the
# enumeration law's `PFull` arm needs to know what one step of that count is
# worth. The adder spec in proofs/adder.bend covers addition; subtraction is
# the same ripple with the second operand complemented and the carry set, so
# the first step here is to say that, and then subtracting one is adding the
# complement of one with a carry in.
#
# From there it is the adder spec and a cancellation: the sum cannot have
# fitted without the carry coming out, and once it has, the two sides differ
# by exactly one.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./adder.bend as Ad
import ./count.bend as Ct
import ./split.bend as Sp
import ./descend.bend as Dc
import ../core/count.bend as C
import ../core/word.bend as W

# Subtracting is adding the complement with a carry in. The flag only ever
# complements the second operand, and it is passed down unchanged.
law Word.sub_is_add_not:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  {Word.adc(n, a, b, True{}, c)
    == Word.adc(n, a, Word.not(n, b), False{}, c) : Word(n)}

def Word.sub_is_add_not(n, a, b, c):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          %Dc.Word.sym(1n+p,
            Word.adc.con(p, at, bt, True{},
              Bool.full_add(ab, Bool.not(bb), c)),
            WCon{Ad.Bool.fst2(Bool.full_add(ab, Bool.not(bb), c)),
              Word.adc(p, at, bt, True{},
                Ad.Bool.snd2(Bool.full_add(ab, Bool.not(bb), c)))},
            Ad.Word.adc_con_pair(p, at, bt, True{},
              Bool.full_add(ab, Bool.not(bb), c)))
            : {_ == Word.adc.con(p, at, Word.not(p, bt), False{},
                Bool.full_add(ab, Bool.not(bb), c)) : Word(1n+p)}
          %Dc.Word.sym(1n+p,
            Word.adc.con(p, at, Word.not(p, bt), False{},
              Bool.full_add(ab, Bool.not(bb), c)),
            WCon{Ad.Bool.fst2(Bool.full_add(ab, Bool.not(bb), c)),
              Word.adc(p, at, Word.not(p, bt), False{},
                Ad.Bool.snd2(Bool.full_add(ab, Bool.not(bb), c)))},
            Ad.Word.adc_con_pair(p, at, Word.not(p, bt), False{},
              Bool.full_add(ab, Bool.not(bb), c)))
            : {WCon{Ad.Bool.fst2(Bool.full_add(ab, Bool.not(bb), c)),
                Word.adc(p, at, bt, True{},
                  Ad.Bool.snd2(Bool.full_add(ab, Bool.not(bb), c)))}
              == _ : Word(1n+p)}
          %Dc.Word.sym(p, Word.adc(p, at, bt, True{},
              Ad.Bool.snd2(Bool.full_add(ab, Bool.not(bb), c))),
            Word.adc(p, at, Word.not(p, bt), False{},
              Ad.Bool.snd2(Bool.full_add(ab, Bool.not(bb), c))),
            Word.sub_is_add_not(p, at, bt,
              Ad.Bool.snd2(Bool.full_add(ab, Bool.not(bb), c))))
            : {WCon{Ad.Bool.fst2(Bool.full_add(ab, Bool.not(bb), c)), _}
              == WCon{Ad.Bool.fst2(Bool.full_add(ab, Bool.not(bb), c)),
                   Word.adc(p, at, Word.not(p, bt), False{},
                     Ad.Bool.snd2(Bool.full_add(ab, Bool.not(bb), c)))}
              : Word(1n+p)}
          {==}

# ---------------------------------------------------------------------------
# One step down.
#
# The borrow form: `a + ~0 + 0` is `a - 1`, and the ripple makes that an
# induction with two cases. A set low bit clears and the borrow stops; a
# clear low bit sets and the borrow goes on. Nothing here expands a 32-bit
# constant, which matters: a `Nat` literal that size does not normalise.
# ---------------------------------------------------------------------------

def Word.dec(+n: Nat, a: Word(n)) -> Word(n):
  Word.adc(n, a, Dc.Word.zeros(n), True{}, False{})

law Nat.double_pos_down:
  for +m: Nat
  for +pos: {C.Nat.gt(Nat.double(m), 0n) == True{} : Bool}
  {C.Nat.gt(m, 0n) == True{} : Bool}

def Nat.double_pos_down(m, pos):
  match m:
    case 0n:
      pos
    case 1n+j:
      {==}

law Nat.dec_double:
  for +m: Nat
  for +pos: {C.Nat.gt(m, 0n) == True{} : Bool}
  {1n+Nat.double(Nat.sub(m, 1n)) == Nat.sub(Nat.double(m), 1n) : Nat}

law Nat.sub_zero:
  for +j: Nat
  {Nat.sub(j, 0n) == j : Nat}

def Nat.sub_zero(j):
  match j:
    case 0n:
      {==}
    case 1n+i:
      {==}

def Nat.dec_double(m, pos):
  match m:
    case 0n:
      E.Bool.noconf({1n+Nat.double(Nat.sub(0n, 1n))
        == Nat.sub(Nat.double(0n), 1n) : Nat}, pos)
    case 1n+j:
      %E.Nat.sym(Nat.sub(j, 0n), j, Nat.sub_zero(j))
        : {1n+Nat.double(_) == Nat.sub(Nat.double(1n+j), 1n) : Nat}
      {==}

law Word.dec_spec:
  for +n: Nat
  for +a: Word(n)
  for +pos: {C.Nat.gt(Word.to_nat(n, a), 0n) == True{} : Bool}
  {Word.to_nat(n, Word.dec(n, a))
    == Nat.sub(Word.to_nat(n, a), 1n) : Nat}

def Word.dec_spec(n, a, pos):
  match n:
    case 0n:
      E.Bool.noconf({Word.to_nat(0n, Word.dec(0n, a))
        == Nat.sub(Word.to_nat(0n, a), 1n) : Nat}, pos)
    case 1n+p:
      match a:
        case WCon{True{}, at}:
          %Dc.Word.sym(p, Word.adc(p, at, Dc.Word.zeros(p), True{},
              True{}), at, Dc.Word.adc_sub_zero(p, at))
            : {Word.to_nat(1n+p, WCon{False{}, _})
              == Nat.sub(Word.to_nat(1n+p, WCon{True{}, at}), 1n) : Nat}
          E.Nat.sym(Nat.sub(Nat.double(Word.to_nat(p, at)), 0n),
            Nat.double(Word.to_nat(p, at)),
            Nat.sub_zero(Nat.double(Word.to_nat(p, at))))
        case WCon{False{}, at}:
          %E.Nat.sym(Word.to_nat(p, Word.dec(p, at)),
            Nat.sub(Word.to_nat(p, at), 1n),
            Word.dec_spec(p, at,
              Nat.double_pos_down(Word.to_nat(p, at), pos)))
            : {1n+Nat.double(_)
              == Nat.sub(Word.to_nat(1n+p, WCon{False{}, at}), 1n) : Nat}
          Nat.dec_double(Word.to_nat(p, at),
            Nat.double_pos_down(Word.to_nat(p, at), pos))

# ---------------------------------------------------------------------------
# At `U32`: subtracting one is the borrow form, so it is one less.
# ---------------------------------------------------------------------------

law U32.sub_one_is_dec:
  for +x: U32
  {U32.sub(x, 1) == U32{Word.dec(32n, W.U32.word(x))} : U32}

def U32.sub_one_is_dec(x):
  match x:
    case U32{w}:
      match w:
        case WCon{wb, wt}:
          match wb:
            case True{}:
              {==}
            case False{}:
              {==}

law U32.dec_spec:
  for +x: U32
  for +pos: {C.Nat.gt(U32.to_nat(x), 0n) == True{} : Bool}
  {U32.to_nat(U32.sub(x, 1)) == Nat.sub(U32.to_nat(x), 1n) : Nat}

def U32.dec_spec(x, pos):
  match x:
    case U32{w}:
      %E.U32.sym(U32.sub(U32{w}, 1), U32{Word.dec(32n, w)},
        U32.sub_one_is_dec(U32{w}))
        : {U32.to_nat(_) == Nat.sub(Word.to_nat(32n, w), 1n) : Nat}
      Word.dec_spec(32n, w, pos)
