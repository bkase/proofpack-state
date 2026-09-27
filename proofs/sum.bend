# proofs/sum.bend -- addition that does not overflow is addition.
#
# proofs/adder.bend proves the ripple-carry adder against `Nat`: the sum and
# the carry out together account for the two inputs. Most of this codebase
# adds into free bits, where proofs/split_add.bend shows the addition is an
# `or` and no carry moves at all. The walk that enumerates a full node is the
# exception -- `base + h + h` genuinely carries -- so it needs the ordinary
# statement instead: if the sum fits in the word, the word is the sum.
#
# The carry out is not assumed away. It is ruled out: a set carry would put
# the true sum a whole word above the part that was kept, and the bound says
# there is no room for that.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./inject.bend as Ij
import ./split.bend as Sp
import ./descend.bend as Dc
import ./adder.bend as Ad
import ./interval.bend as It
import ../core/count.bend as C
import ../core/word.bend as W

law Nat.dbl_one:
  for +n: Nat
  {Sp.Nat.dbl(n, 1n) == Dc.Nat.pow2(n) : Nat}

def Nat.dbl_one(n):
  match n:
    case 0n:
      {==}
    case 1n+j:
      %E.Nat.sym(Sp.Nat.dbl(j, 1n), Dc.Nat.pow2(j), Nat.dbl_one(j))
        : {Nat.double(_) == Nat.double(Dc.Nat.pow2(j)) : Nat}
      {==}

law Nat.gt_false_of_le:
  for +a: Nat
  for +b: Nat
  for +le: {C.Nat.upto(a, b) == True{} : Bool}
  {C.Nat.gt(a, b) == False{} : Bool}

def Nat.gt_false_of_le(a, b, le):
  match a:
    case 0n:
      {==}
    case 1n+p:
      match b:
        case 0n:
          E.Bool.noconf({True{} == False{} : Bool}, le)
        case 1n+q:
          Nat.gt_false_of_le(p, q, le)

law Nat.eq_cast:
  for +a: Nat
  for +a2: Nat
  for +c: Nat
  for +c2: Nat
  for +ea: {a == a2 : Nat}
  for +ec: {c == c2 : Nat}
  for +ok: {a == c : Nat}
  {a2 == c2 : Nat}

def Nat.eq_cast(a, a2, c, c2, ea, ec, ok):
  %ea : {_ == c2 : Nat}
  %ec : {a == _ : Nat}
  ok

# ---------------------------------------------------------------------------
# The carry out is zero when the sum fits.
# ---------------------------------------------------------------------------

law Word.add_spec:
  for +n: Nat
  for +c: Bool
  for +a: Word(n)
  for +b: Word(n)
  for +ec: {c == Ad.Word.carry(n, a, b, False{}, False{}) : Bool}
  for +bound: {C.Nat.gt(Dc.Nat.pow2(n),
    Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) == True{} : Bool}
  {Word.to_nat(n, Word.adc(n, a, b, False{}, False{}))
    == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

# `s + dbl(n, 0)` is `s`.
def Word.add_spec.left(+n: Nat, +a: Word(n), +b: Word(n))
  -> {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
       Sp.Nat.dbl(n, Ad.Bool.nat(False{})))
     == Word.to_nat(n, Word.adc(n, a, b, False{}, False{})) : Nat}:
  %E.Nat.sym(Sp.Nat.dbl(n, 0n), 0n, Sp.Nat.dbl_zero(n))
    : {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})), _)
      == Word.to_nat(n, Word.adc(n, a, b, False{}, False{})) : Nat}
  N.Nat.add_zero(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})))

def Word.add_spec.right(+n: Nat, +a: Word(n), +b: Word(n))
  -> {Nat.add(Word.to_nat(n, a),
       Nat.add(Word.to_nat(n, b), Ad.Bool.nat(False{})))
     == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}:
  %E.Nat.sym(Nat.add(Word.to_nat(n, b), 0n), Word.to_nat(n, b),
    N.Nat.add_zero(Word.to_nat(n, b)))
    : {Nat.add(Word.to_nat(n, a), _)
      == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}
  {==}

def Word.add_spec.carry(+n: Nat, +a: Word(n), +b: Word(n), +c: Bool,
  +ec: {c == Ad.Word.carry(n, a, b, False{}, False{}) : Bool})
  -> {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
       Sp.Nat.dbl(n, Ad.Bool.nat(Ad.Word.carry(n, a, b, False{},
         False{}))))
     == Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
          Sp.Nat.dbl(n, Ad.Bool.nat(c))) : Nat}:
  %E.Bool.sym(c, Ad.Word.carry(n, a, b, False{}, False{}), ec)
    : {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
      Sp.Nat.dbl(n, Ad.Bool.nat(Ad.Word.carry(n, a, b, False{}, False{}))))
    == Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
         Sp.Nat.dbl(n, Ad.Bool.nat(_))) : Nat}
  {==}

def Word.add_spec.one(+n: Nat, +a: Word(n), +b: Word(n),
  +ec: {True{} == Ad.Word.carry(n, a, b, False{}, False{}) : Bool})
  -> {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
       Sp.Nat.dbl(n, Ad.Bool.nat(Ad.Word.carry(n, a, b, False{},
         False{}))))
     == Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
          Dc.Nat.pow2(n)) : Nat}:
  %ec
    : {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
        Sp.Nat.dbl(n, Ad.Bool.nat(_)))
      == Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
           Dc.Nat.pow2(n)) : Nat}
  %E.Nat.sym(Sp.Nat.dbl(n, 1n), Dc.Nat.pow2(n), Nat.dbl_one(n))
    : {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})), _)
      == Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
           Dc.Nat.pow2(n)) : Nat}
  {==}

def Word.add_spec.sum(+n: Nat, +a: Word(n), +b: Word(n),
  +ec: {True{} == Ad.Word.carry(n, a, b, False{}, False{}) : Bool})
  -> {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
       Dc.Nat.pow2(n))
     == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}:
  Nat.eq_cast(
    Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
      Sp.Nat.dbl(n, Ad.Bool.nat(Ad.Word.carry(n, a, b, False{}, False{})))),
    Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
      Dc.Nat.pow2(n)),
    Nat.add(Word.to_nat(n, a),
      Nat.add(Word.to_nat(n, b), Ad.Bool.nat(False{}))),
    Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)),
    Word.add_spec.one(n, a, b, ec),
    Word.add_spec.right(n, a, b),
    Ad.Word.adc_spec(n, a, b, False{}))

# A carry out would put the true sum a word above what was kept.
def Word.add_spec.absurd(+n: Nat, +a: Word(n), +b: Word(n),
  +ec: {True{} == Ad.Word.carry(n, a, b, False{}, False{}) : Bool},
  +bound: {C.Nat.gt(Dc.Nat.pow2(n),
    Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) == True{} : Bool})
  -> {False{} == True{} : Bool}:
  %bound : {False{} == _ : Bool}
  E.Bool.sym(C.Nat.gt(Dc.Nat.pow2(n),
    Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))), False{},
    Nat.gt_false_of_le(Dc.Nat.pow2(n),
    Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)),
    It.Nat.upto_cast(Dc.Nat.pow2(n), Dc.Nat.pow2(n),
      Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
        Dc.Nat.pow2(n)),
      Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), {==},
      Word.add_spec.sum(n, a, b, ec),
      It.Nat.le_add_left(Dc.Nat.pow2(n),
        Word.to_nat(n, Word.adc(n, a, b, False{}, False{}))))))

def Word.add_spec(n, c, a, b, ec, bound):
  match c:
    case False{}:
      Nat.eq_cast(
        Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
          Sp.Nat.dbl(n, Ad.Bool.nat(False{}))),
        Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
        Nat.add(Word.to_nat(n, a),
          Nat.add(Word.to_nat(n, b), Ad.Bool.nat(False{}))),
        Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)),
        Word.add_spec.left(n, a, b),
        Word.add_spec.right(n, a, b),
        Nat.eq_cast(
          Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
            Sp.Nat.dbl(n,
              Ad.Bool.nat(Ad.Word.carry(n, a, b, False{}, False{})))),
          Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
            Sp.Nat.dbl(n, Ad.Bool.nat(False{}))),
          Nat.add(Word.to_nat(n, a),
            Nat.add(Word.to_nat(n, b), Ad.Bool.nat(False{}))),
          Nat.add(Word.to_nat(n, a),
            Nat.add(Word.to_nat(n, b), Ad.Bool.nat(False{}))),
          Word.add_spec.carry(n, a, b, False{}, ec), {==},
          Ad.Word.adc_spec(n, a, b, False{})))
    case True{}:
      E.Bool.noconf({Word.to_nat(n, Word.adc(n, a, b, False{}, False{}))
        == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat},
        Word.add_spec.absurd(n, a, b, ec, bound))

# The same statement without the bound: adding words that do not carry out
# adds the numbers they read as. This form survives at width 32, where the
# bound above cannot even be written down -- `Nat.pow2(32n)` is 2^32 tally
# marks, and the checker expands it.
law Word.add_of_no_carry:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +nc: {Ad.Word.carry(n, a, b, False{}, False{}) == False{} : Bool}
  {Word.to_nat(n, Word.adc(n, a, b, False{}, False{}))
    == Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}

def Word.add_of_no_carry(n, a, b, nc):
  Nat.eq_cast(
    Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
      Sp.Nat.dbl(n, Ad.Bool.nat(False{}))),
    Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
    Nat.add(Word.to_nat(n, a),
      Nat.add(Word.to_nat(n, b), Ad.Bool.nat(False{}))),
    Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)),
    Word.add_spec.left(n, a, b),
    Word.add_spec.right(n, a, b),
    Nat.eq_cast(
      Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
        Sp.Nat.dbl(n,
          Ad.Bool.nat(Ad.Word.carry(n, a, b, False{}, False{})))),
      Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, False{})),
        Sp.Nat.dbl(n, Ad.Bool.nat(False{}))),
      Nat.add(Word.to_nat(n, a),
        Nat.add(Word.to_nat(n, b), Ad.Bool.nat(False{}))),
      Nat.add(Word.to_nat(n, a),
        Nat.add(Word.to_nat(n, b), Ad.Bool.nat(False{}))),
      Word.add_spec.carry(n, a, b, False{},
        E.Bool.sym(Ad.Word.carry(n, a, b, False{}, False{}), False{},
          nc)), {==},
      Ad.Word.adc_spec(n, a, b, False{})))

law U32.add_of_no_carry:
  for +y: U32
  for +b: U32
  for +nc: {Ad.Word.carry(32n, W.U32.word(y), W.U32.word(b), False{},
    False{}) == False{} : Bool}
  {U32.to_nat((y + b : U32))
    == Nat.add(U32.to_nat(y), U32.to_nat(b)) : Nat}

def U32.add_of_no_carry(y, b, nc):
  match y b:
    case U32{yw} U32{bw}:
      Word.add_of_no_carry(32n, yw, bw, nc)
