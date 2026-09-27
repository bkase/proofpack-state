# proofs/adder.bend -- what `U32` addition computes.
#
# `Words.members` walks a tile building ordinals by `ord + 1` within a word
# and `ord + 32` between words. Reading those ordinals back as tile addresses
# -- which is what law S-03's sparse arm needs -- means knowing that `U32`
# addition is addition, and that is a statement about the ripple adder
# `Word.adc`, not about anything in the set algebra.
#
# The adder's contract is the usual one: the sum plus the carry out, weighted
# by the width, equals the two inputs plus the carry in. Each bit of it is
# `Bool.full_add`, whose own contract is an eight-case check.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./inject.bend as Ij
import ./split.bend as Sp
import ./descend.bend as Dc
import ../core/count.bend as C
import ../core/word.bend as W

def Bool.nat(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

def Bool.fst2(p: Bool & Bool) -> Bool:
  (s, k) = p
  s

def Bool.snd2(p: Bool & Bool) -> Bool:
  (s, k) = p
  k

# The carry the adder hands out at the top. `Word.adc` drops it; the proof
# needs it, so it is recomputed here rather than changing the runtime.
def Word.carry(n: Nat, a: Word(n), b: Word(n), f: Bool, c: Bool) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match a b f:
        case WCon{ab, at} WCon{bb, bt} False{}:
          Word.carry(p, at, bt, False{},
            Bool.snd2(Bool.full_add(ab, bb, c)))
        case WCon{ab, at} WCon{bb, bt} True{}:
          Word.carry(p, at, bt, True{},
            Bool.snd2(Bool.full_add(ab, Bool.not(bb), c)))

# One bit: the three inputs sum to the carry out doubled plus the sum bit.
law Bool.full_add_spec:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Nat.add(Bool.nat(a), Nat.add(Bool.nat(b), Bool.nat(c)))
    == Nat.add(Nat.double(Bool.nat(Bool.snd2(Bool.full_add(a, b, c)))),
         Bool.nat(Bool.fst2(Bool.full_add(a, b, c)))) : Nat}

def Bool.full_add_spec(a, b, c):
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

# ---------------------------------------------------------------------------
# Nat algebra the ripple needs.
# ---------------------------------------------------------------------------

law Nat.add_shuffle:
  for +ta: Nat
  for +tb: Nat
  for +na: Nat
  for +nb: Nat
  for +nc: Nat
  {Nat.add(Nat.add(Nat.double(ta), na),
      Nat.add(Nat.add(Nat.double(tb), nb), nc))
    == Nat.add(Nat.double(Nat.add(ta, tb)),
         Nat.add(na, Nat.add(nb, nc))) : Nat}

def Nat.add_at2(+r: Nat, l: Nat) -> Nat:
  Nat.add(l, r)

# (a + x) + (b + y) == (a + b) + (x + y), by associativity and commutativity.
law Nat.four_shuffle:
  for +a: Nat
  for +x: Nat
  for +b: Nat
  for +y: Nat
  {Nat.add(Nat.add(a, x), Nat.add(b, y))
    == Nat.add(Nat.add(a, b), Nat.add(x, y)) : Nat}

def Nat.at_add2(+l: Nat, r: Nat) -> Nat:
  Nat.add(l, r)

law Nat.mid_swap:
  for +x: Nat
  for +b: Nat
  for +y: Nat
  {Nat.add(x, Nat.add(b, y)) == Nat.add(b, Nat.add(x, y)) : Nat}

def Nat.mid_swap(x, b, y):
  Equal.trans(Nat, Nat.add(x, Nat.add(b, y)), Nat.add(Nat.add(x, b), y),
    Nat.add(b, Nat.add(x, y)),
    E.Nat.sym(Nat.add(Nat.add(x, b), y), Nat.add(x, Nat.add(b, y)),
      N.Nat.add_assoc(x, b, y)),
    Equal.trans(Nat, Nat.add(Nat.add(x, b), y),
      Nat.add(Nat.add(b, x), y), Nat.add(b, Nat.add(x, y)),
      Equal.cong(Nat, Nat, Nat.add_at2(y), Nat.add(x, b), Nat.add(b, x),
        N.Nat.add_comm(x, b)),
      N.Nat.add_assoc(b, x, y)))

def Nat.four_shuffle(a, x, b, y):
  Equal.trans(Nat, Nat.add(Nat.add(a, x), Nat.add(b, y)),
    Nat.add(a, Nat.add(x, Nat.add(b, y))),
    Nat.add(Nat.add(a, b), Nat.add(x, y)),
    N.Nat.add_assoc(a, x, Nat.add(b, y)),
    Equal.trans(Nat, Nat.add(a, Nat.add(x, Nat.add(b, y))),
      Nat.add(a, Nat.add(b, Nat.add(x, y))),
      Nat.add(Nat.add(a, b), Nat.add(x, y)),
      Equal.cong(Nat, Nat, Nat.at_add2(a),
        Nat.add(x, Nat.add(b, y)), Nat.add(b, Nat.add(x, y)),
        Nat.mid_swap(x, b, y)),
      E.Nat.sym(Nat.add(Nat.add(a, b), Nat.add(x, y)),
        Nat.add(a, Nat.add(b, Nat.add(x, y))),
        N.Nat.add_assoc(a, b, Nat.add(x, y)))))

def Nat.add_shuffle(ta, tb, na, nb, nc):
  %E.Nat.sym(Nat.add(Nat.add(Nat.double(tb), nb), nc),
    Nat.add(Nat.double(tb), Nat.add(nb, nc)),
    N.Nat.add_assoc(Nat.double(tb), nb, nc))
    : {Nat.add(Nat.add(Nat.double(ta), na), _)
      == Nat.add(Nat.double(Nat.add(ta, tb)),
           Nat.add(na, Nat.add(nb, nc))) : Nat}
  Equal.trans(Nat,
    Nat.add(Nat.add(Nat.double(ta), na),
      Nat.add(Nat.double(tb), Nat.add(nb, nc))),
    Nat.add(Nat.add(Nat.double(ta), Nat.double(tb)),
      Nat.add(na, Nat.add(nb, nc))),
    Nat.add(Nat.double(Nat.add(ta, tb)),
      Nat.add(na, Nat.add(nb, nc))),
    Nat.four_shuffle(Nat.double(ta), na, Nat.double(tb),
      Nat.add(nb, nc)),
    Equal.cong(Nat, Nat,
      Nat.add_at2(Nat.add(na, Nat.add(nb, nc))),
      Nat.add(Nat.double(ta), Nat.double(tb)),
      Nat.double(Nat.add(ta, tb)),
      E.Nat.sym(Nat.double(Nat.add(ta, tb)),
        Nat.add(Nat.double(ta), Nat.double(tb)),
        Sp.Nat.double_add(ta, tb))))

# ---------------------------------------------------------------------------
# The ripple. Sum plus carry-out weighted by the width equals the inputs plus
# the carry in.
# ---------------------------------------------------------------------------

law Word.adc_spec:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)),
      Sp.Nat.dbl(n, Bool.nat(Word.carry(n, a, b, False{}, c))))
    == Nat.add(Word.to_nat(n, a),
         Nat.add(Word.to_nat(n, b), Bool.nat(c))) : Nat}

law Word.adc_spec.zero:
  for +c: Bool
  {Nat.add(0n, Sp.Nat.dbl(0n, Bool.nat(c)))
    == Nat.add(0n, Nat.add(0n, Bool.nat(c))) : Nat}

def Word.adc_spec.zero(c):
  match c:
    case False{}:
      {==}
    case True{}:
      {==}

law Word.to_nat_cons2:
  for +n: Nat
  for +b: Bool
  for +t: Word(n)
  {Word.to_nat(1n+n, WCon{b, t})
    == Nat.add(Nat.double(Word.to_nat(n, t)), Bool.nat(b)) : Nat}

law Nat.add_one:
  for +a: Nat
  {Nat.add(a, 1n) == 1n+a : Nat}

def Nat.add_one(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %E.Nat.sym(Nat.add(p, 1n), 1n+p, Nat.add_one(p))
        : {1n+_ == 2n+p : Nat}
      {==}

def Word.to_nat_cons2(n, b, t):
  match b:
    case False{}:
      E.Nat.sym(Nat.add(Nat.double(Word.to_nat(n, t)), 0n),
        Nat.double(Word.to_nat(n, t)),
        N.Nat.add_zero(Nat.double(Word.to_nat(n, t))))
    case True{}:
      E.Nat.sym(Nat.add(Nat.double(Word.to_nat(n, t)), 1n),
        1n+Nat.double(Word.to_nat(n, t)),
        Nat.add_one(Nat.double(Word.to_nat(n, t))))

law Nat.swap_mid:
  for +u: Nat
  for +n: Nat
  for +v: Nat
  {Nat.add(Nat.add(u, n), v) == Nat.add(Nat.add(u, v), n) : Nat}

def Nat.swap_mid(u, n, v):
  Equal.trans(Nat, Nat.add(Nat.add(u, n), v), Nat.add(u, Nat.add(n, v)),
    Nat.add(Nat.add(u, v), n),
    N.Nat.add_assoc(u, n, v),
    Equal.trans(Nat, Nat.add(u, Nat.add(n, v)), Nat.add(u, Nat.add(v, n)),
      Nat.add(Nat.add(u, v), n),
      Equal.cong(Nat, Nat, Nat.at_add2(u), Nat.add(n, v), Nat.add(v, n),
        N.Nat.add_comm(n, v)),
      E.Nat.sym(Nat.add(Nat.add(u, v), n), Nat.add(u, Nat.add(v, n)),
        N.Nat.add_assoc(u, v, n))))

law Word.adc_con_pair:
  for +p: Nat
  for +at: Word(p)
  for +bt: Word(p)
  for +f: Bool
  for sk: Bool & Bool
  {Word.adc.con(p, at, bt, f, sk)
    == WCon{Bool.fst2(sk), Word.adc(p, at, bt, f, Bool.snd2(sk))}
    : Word(1n+p)}

def Word.adc_con_pair(p, at, bt, f, sk):
  (s, k) = sk
  {==}

law Word.adc_spec.step:
  for +p: Nat
  for +ab: Bool
  for +bb: Bool
  for +at: Word(p)
  for +bt: Word(p)
  for +c: Bool
  for +ih: {Nat.add(Word.to_nat(p, Word.adc(p, at, bt, False{},
        Bool.snd2(Bool.full_add(ab, bb, c)))),
      Sp.Nat.dbl(p, Bool.nat(Word.carry(p, at, bt, False{},
        Bool.snd2(Bool.full_add(ab, bb, c))))))
    == Nat.add(Word.to_nat(p, at),
         Nat.add(Word.to_nat(p, bt),
           Bool.nat(Bool.snd2(Bool.full_add(ab, bb, c))))) : Nat}
  {Nat.add(Word.to_nat(1n+p,
        Word.adc(1n+p, WCon{ab, at}, WCon{bb, bt}, False{}, c)),
      Sp.Nat.dbl(1n+p, Bool.nat(Word.carry(1n+p, WCon{ab, at},
        WCon{bb, bt}, False{}, c))))
    == Nat.add(Word.to_nat(1n+p, WCon{ab, at}),
         Nat.add(Word.to_nat(1n+p, WCon{bb, bt}), Bool.nat(c))) : Nat}

# The column's arithmetic, with every word and bit replaced by the number it
# stands for. `fa` is what the full adder promises, `ih` what the rest of the
# ripple promises, and the rest is associativity.
law Word.adc_spec.arith:
  for +ta: Nat
  for +tb: Nat
  for +x: Nat
  for +d: Nat
  for +na: Nat
  for +nb: Nat
  for +nc: Nat
  for +ns: Nat
  for +nk: Nat
  for +fa: {Nat.add(na, Nat.add(nb, nc))
    == Nat.add(Nat.double(nk), ns) : Nat}
  for +ih: {Nat.add(x, d) == Nat.add(ta, Nat.add(tb, nk)) : Nat}
  {Nat.add(Nat.add(Nat.double(x), ns), Nat.double(d))
    == Nat.add(Nat.add(Nat.double(ta), na),
         Nat.add(Nat.add(Nat.double(tb), nb), nc)) : Nat}

def Word.adc_spec.arith(ta, tb, x, d, na, nb, nc, ns, nk, fa, ih):
  %E.Nat.sym(Nat.add(Nat.add(Nat.double(x), ns), Nat.double(d)),
    Nat.add(Nat.add(Nat.double(x), Nat.double(d)), ns),
    Nat.swap_mid(Nat.double(x), ns, Nat.double(d)))
    : {_ == Nat.add(Nat.add(Nat.double(ta), na),
         Nat.add(Nat.add(Nat.double(tb), nb), nc)) : Nat}
  %Sp.Nat.double_add(x, d)
    : {Nat.add(_, ns) == Nat.add(Nat.add(Nat.double(ta), na),
         Nat.add(Nat.add(Nat.double(tb), nb), nc)) : Nat}
  %E.Nat.sym(Nat.add(x, d), Nat.add(ta, Nat.add(tb, nk)), ih)
    : {Nat.add(Nat.double(_), ns)
      == Nat.add(Nat.add(Nat.double(ta), na),
           Nat.add(Nat.add(Nat.double(tb), nb), nc)) : Nat}
  %E.Nat.sym(Nat.add(Nat.add(Nat.double(ta), na),
      Nat.add(Nat.add(Nat.double(tb), nb), nc)),
    Nat.add(Nat.double(Nat.add(ta, tb)), Nat.add(na, Nat.add(nb, nc))),
    Nat.add_shuffle(ta, tb, na, nb, nc))
    : {Nat.add(Nat.double(Nat.add(ta, Nat.add(tb, nk))), ns) == _ : Nat}
  %E.Nat.sym(Nat.add(na, Nat.add(nb, nc)),
    Nat.add(Nat.double(nk), ns), fa)
    : {Nat.add(Nat.double(Nat.add(ta, Nat.add(tb, nk))), ns)
      == Nat.add(Nat.double(Nat.add(ta, tb)), _) : Nat}
  %N.Nat.add_assoc(ta, tb, nk)
    : {Nat.add(Nat.double(_), ns)
      == Nat.add(Nat.double(Nat.add(ta, tb)),
           Nat.add(Nat.double(nk), ns)) : Nat}
  %E.Nat.sym(Nat.double(Nat.add(Nat.add(ta, tb), nk)),
    Nat.add(Nat.double(Nat.add(ta, tb)), Nat.double(nk)),
    Sp.Nat.double_add(Nat.add(ta, tb), nk))
    : {Nat.add(_, ns)
      == Nat.add(Nat.double(Nat.add(ta, tb)),
           Nat.add(Nat.double(nk), ns)) : Nat}
  N.Nat.add_assoc(Nat.double(Nat.add(ta, tb)), Nat.double(nk), ns)

def Word.adc_spec.step(p, ab, bb, at, bt, c, ih):
  # `s` and `k` are the sum bit and the carry this column produces, `X` and
  # `co` what the rest of the ripple returns. The adder hands the pair along
  # unsplit, so it has to be split first.
  %E.Word.sym(1n+p, Word.adc.con(p, at, bt, False{},
      Bool.full_add(ab, bb, c)),
    WCon{Bool.fst2(Bool.full_add(ab, bb, c)),
      Word.adc(p, at, bt, False{},
        Bool.snd2(Bool.full_add(ab, bb, c)))},
    Word.adc_con_pair(p, at, bt, False{}, Bool.full_add(ab, bb, c)))
    : {Nat.add(Word.to_nat(1n+p, _),
        Sp.Nat.dbl(1n+p, Bool.nat(Word.carry(p, at, bt, False{},
          Bool.snd2(Bool.full_add(ab, bb, c))))))
      == Nat.add(Word.to_nat(1n+p, WCon{ab, at}),
           Nat.add(Word.to_nat(1n+p, WCon{bb, bt}), Bool.nat(c))) : Nat}
  %E.Nat.sym(
    Word.to_nat(1n+p, WCon{Bool.fst2(Bool.full_add(ab, bb, c)),
      Word.adc(p, at, bt, False{},
        Bool.snd2(Bool.full_add(ab, bb, c)))}),
    Nat.add(Nat.double(Word.to_nat(p,
      Word.adc(p, at, bt, False{},
        Bool.snd2(Bool.full_add(ab, bb, c))))),
      Bool.nat(Bool.fst2(Bool.full_add(ab, bb, c)))),
    Word.to_nat_cons2(p, Bool.fst2(Bool.full_add(ab, bb, c)),
      Word.adc(p, at, bt, False{},
        Bool.snd2(Bool.full_add(ab, bb, c)))))
    : {Nat.add(_, Sp.Nat.dbl(1n+p, Bool.nat(Word.carry(p, at, bt,
        False{}, Bool.snd2(Bool.full_add(ab, bb, c))))))
      == Nat.add(Word.to_nat(1n+p, WCon{ab, at}),
           Nat.add(Word.to_nat(1n+p, WCon{bb, bt}), Bool.nat(c))) : Nat}
  %E.Nat.sym(Word.to_nat(1n+p, WCon{ab, at}),
    Nat.add(Nat.double(Word.to_nat(p, at)), Bool.nat(ab)),
    Word.to_nat_cons2(p, ab, at))
    : {Nat.add(Nat.add(Nat.double(Word.to_nat(p,
          Word.adc(p, at, bt, False{},
            Bool.snd2(Bool.full_add(ab, bb, c))))),
        Bool.nat(Bool.fst2(Bool.full_add(ab, bb, c)))),
        Sp.Nat.dbl(1n+p, Bool.nat(Word.carry(p, at, bt, False{},
          Bool.snd2(Bool.full_add(ab, bb, c))))))
      == Nat.add(_, Nat.add(Word.to_nat(1n+p, WCon{bb, bt}),
           Bool.nat(c))) : Nat}
  %E.Nat.sym(Word.to_nat(1n+p, WCon{bb, bt}),
    Nat.add(Nat.double(Word.to_nat(p, bt)), Bool.nat(bb)),
    Word.to_nat_cons2(p, bb, bt))
    : {Nat.add(Nat.add(Nat.double(Word.to_nat(p,
          Word.adc(p, at, bt, False{},
            Bool.snd2(Bool.full_add(ab, bb, c))))),
        Bool.nat(Bool.fst2(Bool.full_add(ab, bb, c)))),
        Sp.Nat.dbl(1n+p, Bool.nat(Word.carry(p, at, bt, False{},
          Bool.snd2(Bool.full_add(ab, bb, c))))))
      == Nat.add(Nat.add(Nat.double(Word.to_nat(p, at)), Bool.nat(ab)),
           Nat.add(_, Bool.nat(c))) : Nat}
  Word.adc_spec.arith(Word.to_nat(p, at), Word.to_nat(p, bt),
    Word.to_nat(p, Word.adc(p, at, bt, False{},
      Bool.snd2(Bool.full_add(ab, bb, c)))),
    Sp.Nat.dbl(p, Bool.nat(Word.carry(p, at, bt, False{},
      Bool.snd2(Bool.full_add(ab, bb, c))))),
    Bool.nat(ab), Bool.nat(bb), Bool.nat(c),
    Bool.nat(Bool.fst2(Bool.full_add(ab, bb, c))),
    Bool.nat(Bool.snd2(Bool.full_add(ab, bb, c))),
    Bool.full_add_spec(ab, bb, c), ih)

def Word.adc_spec(n, a, b, c):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          Word.adc_spec.zero(c)
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          Word.adc_spec.step(p, ab, bb, at, bt, c,
            Word.adc_spec(p, at, bt,
              Bool.snd2(Bool.full_add(ab, bb, c))))

# ---------------------------------------------------------------------------
# When the carry vanishes: two operands that fit in k bits, with k below the
# width, cannot carry out of the top.
# ---------------------------------------------------------------------------

law Bool.not_true:
  for +b: Bool
  for +ok: {Bool.not(b) == True{} : Bool}
  {False{} == b : Bool}

def Bool.not_true(b, ok):
  match b:
    case False{}:
      {==}
    case True{}:
      E.Bool.noconf({False{} == True{} : Bool}, ok)

law Word.carry_zero:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +za: {Dc.Word.hi_zero(n, a, 0n) == True{} : Bool}
  for +zb: {Dc.Word.hi_zero(n, b, 0n) == True{} : Bool}
  {Word.carry(n, a, b, False{}, False{}) == False{} : Bool}

law Word.carry_zero.step:
  for +p: Nat
  for +ab: Bool
  for +bb: Bool
  for +at: Word(p)
  for +bt: Word(p)
  for +za: {Dc.Word.hi_zero(1n+p, WCon{ab, at}, 0n) == True{} : Bool}
  for +zb: {Dc.Word.hi_zero(1n+p, WCon{bb, bt}, 0n) == True{} : Bool}
  for +ih: {Word.carry(p, at, bt, False{}, False{}) == False{} : Bool}
  {Word.carry(1n+p, WCon{ab, at}, WCon{bb, bt}, False{}, False{})
    == False{} : Bool}

def Word.carry_zero.step(p, ab, bb, at, bt, za, zb, ih):
  %Bool.not_true(ab,
    Dc.Bool.and_left(Bool.not(ab), Dc.Word.hi_zero(p, at, 0n), za))
    : {Word.carry(p, at, bt, False{},
        Bool.snd2(Bool.full_add(_, bb, False{})))
      == False{} : Bool}
  %Bool.not_true(bb,
    Dc.Bool.and_left(Bool.not(bb), Dc.Word.hi_zero(p, bt, 0n), zb))
    : {Word.carry(p, at, bt, False{},
        Bool.snd2(Bool.full_add(False{}, _, False{})))
      == False{} : Bool}
  ih

def Word.carry_zero(n, a, b, za, zb):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          Word.carry_zero.step(p, ab, bb, at, bt, za, zb,
            Word.carry_zero(p, at, bt,
              Dc.Bool.and_right(Bool.not(ab), Dc.Word.hi_zero(p, at, 0n),
                za),
              Dc.Bool.and_right(Bool.not(bb), Dc.Word.hi_zero(p, bt, 0n),
                zb)))

law Word.carry_small:
  for +n: Nat
  for +k: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  for +za: {Dc.Word.hi_zero(n, a, k) == True{} : Bool}
  for +zb: {Dc.Word.hi_zero(n, b, k) == True{} : Bool}
  for +ok: {C.Nat.gt(n, k) == True{} : Bool}
  {Word.carry(n, a, b, False{}, c) == False{} : Bool}

# Both operands are zero, so whatever carry comes in is absorbed by the first
# column and nothing carries out.
law Word.carry_small.zero:
  for +p: Nat
  for +ab: Bool
  for +bb: Bool
  for +at: Word(p)
  for +bt: Word(p)
  for +c: Bool
  for +za: {Dc.Word.hi_zero(1n+p, WCon{ab, at}, 0n) == True{} : Bool}
  for +zb: {Dc.Word.hi_zero(1n+p, WCon{bb, bt}, 0n) == True{} : Bool}
  {Word.carry(1n+p, WCon{ab, at}, WCon{bb, bt}, False{}, c)
    == False{} : Bool}

law Word.carry_small.zero.tail:
  for +p: Nat
  for +at: Word(p)
  for +bt: Word(p)
  for +c: Bool
  for +za: {Dc.Word.hi_zero(p, at, 0n) == True{} : Bool}
  for +zb: {Dc.Word.hi_zero(p, bt, 0n) == True{} : Bool}
  {Word.carry(p, at, bt, False{},
    Bool.snd2(Bool.full_add(False{}, False{}, c))) == False{} : Bool}

def Word.carry_small.zero.tail(p, at, bt, c, za, zb):
  match c:
    case False{}:
      Word.carry_zero(p, at, bt, za, zb)
    case True{}:
      Word.carry_zero(p, at, bt, za, zb)

def Word.carry_small.zero(p, ab, bb, at, bt, c, za, zb):
  %Bool.not_true(ab,
    Dc.Bool.and_left(Bool.not(ab), Dc.Word.hi_zero(p, at, 0n), za))
    : {Word.carry(p, at, bt, False{},
        Bool.snd2(Bool.full_add(_, bb, c))) == False{} : Bool}
  %Bool.not_true(bb,
    Dc.Bool.and_left(Bool.not(bb), Dc.Word.hi_zero(p, bt, 0n), zb))
    : {Word.carry(p, at, bt, False{},
        Bool.snd2(Bool.full_add(False{}, _, c))) == False{} : Bool}
  Word.carry_small.zero.tail(p, at, bt, c,
    Dc.Bool.and_right(Bool.not(ab), Dc.Word.hi_zero(p, at, 0n), za),
    Dc.Bool.and_right(Bool.not(bb), Dc.Word.hi_zero(p, bt, 0n), zb))

def Word.carry_small(n, k, a, b, c, za, zb, ok):
  match n:
    case 0n:
      E.Bool.noconf({Word.carry(0n, a, b, False{}, c) == False{} : Bool},
        ok)
    case 1n+p:
      match k:
        case 0n:
          match a b:
            case WCon{ab, at} WCon{bb, bt}:
              Word.carry_small.zero(p, ab, bb, at, bt, c, za, zb)
        case 1n+j:
          match a b:
            case WCon{ab, at} WCon{bb, bt}:
              Word.carry_small(p, j, at, bt,
                Bool.snd2(Bool.full_add(ab, bb, c)), za, zb, ok)

# ---------------------------------------------------------------------------
# So at `U32`: addition is addition, as long as both operands fit in fewer
# than 32 bits.
# ---------------------------------------------------------------------------

law U32.to_nat_add:
  for +a: U32
  for +b: U32
  for +k: Nat
  for +za: {Dc.U32.hi_zero(a, k) == True{} : Bool}
  for +zb: {Dc.U32.hi_zero(b, k) == True{} : Bool}
  for +ok: {C.Nat.gt(32n, k) == True{} : Bool}
  {U32.to_nat(U32.add(a, b))
    == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

law U32.to_nat_add.on:
  for +x: Word(32n)
  for +y: Word(32n)
  for +nc: {Word.carry(32n, x, y, False{}, False{}) == False{} : Bool}
  for +sp: {Nat.add(Word.to_nat(32n, Word.adc(32n, x, y, False{},
        False{})),
      Sp.Nat.dbl(32n, Bool.nat(Word.carry(32n, x, y, False{}, False{}))))
    == Nat.add(Word.to_nat(32n, x),
         Nat.add(Word.to_nat(32n, y), Bool.nat(False{}))) : Nat}
  {Word.to_nat(32n, Word.adc(32n, x, y, False{}, False{}))
    == Nat.add(Word.to_nat(32n, x), Word.to_nat(32n, y)) : Nat}

law U32.to_nat_add.left:
  for +x: Word(32n)
  for +y: Word(32n)
  for +nc: {Word.carry(32n, x, y, False{}, False{}) == False{} : Bool}
  for +sp: {Nat.add(Word.to_nat(32n, Word.adc(32n, x, y, False{},
        False{})),
      Sp.Nat.dbl(32n, Bool.nat(Word.carry(32n, x, y, False{}, False{}))))
    == Nat.add(Word.to_nat(32n, x),
         Nat.add(Word.to_nat(32n, y), Bool.nat(False{}))) : Nat}
  {Word.to_nat(32n, Word.adc(32n, x, y, False{}, False{}))
    == Nat.add(Word.to_nat(32n, x),
         Nat.add(Word.to_nat(32n, y), 0n)) : Nat}

def U32.to_nat_add.left(x, y, nc, sp):
  %N.Nat.add_zero(Word.to_nat(32n,
    Word.adc(32n, x, y, False{}, False{})))
    : {_ == Nat.add(Word.to_nat(32n, x),
        Nat.add(Word.to_nat(32n, y), 0n)) : Nat}
  %Sp.Nat.dbl_zero(32n)
    : {Nat.add(Word.to_nat(32n, Word.adc(32n, x, y, False{}, False{})),
        _) == Nat.add(Word.to_nat(32n, x),
          Nat.add(Word.to_nat(32n, y), 0n)) : Nat}
  %Equal.cong(Bool, Nat, Bool.nat,
    Word.carry(32n, x, y, False{}, False{}), False{}, nc)
    : {Nat.add(Word.to_nat(32n, Word.adc(32n, x, y, False{}, False{})),
        Sp.Nat.dbl(32n, _))
      == Nat.add(Word.to_nat(32n, x),
           Nat.add(Word.to_nat(32n, y), 0n)) : Nat}
  sp

def U32.to_nat_add.on(x, y, nc, sp):
  Equal.trans(Nat,
    Word.to_nat(32n, Word.adc(32n, x, y, False{}, False{})),
    Nat.add(Word.to_nat(32n, x),
      Nat.add(Word.to_nat(32n, y), 0n)),
    Nat.add(Word.to_nat(32n, x), Word.to_nat(32n, y)),
    U32.to_nat_add.left(x, y, nc, sp),
    Equal.cong(Nat, Nat, Nat.at_add2(Word.to_nat(32n, x)),
      Nat.add(Word.to_nat(32n, y), 0n), Word.to_nat(32n, y),
      N.Nat.add_zero(Word.to_nat(32n, y))))

def U32.to_nat_add(a, b, k, za, zb, ok):
  match a b:
    case U32{x} U32{y}:
      U32.to_nat_add.on(x, y,
        Word.carry_small(32n, k, x, y, False{}, za, zb, ok),
        Word.adc_spec(32n, x, y, False{}))
