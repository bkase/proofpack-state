# proofs/shift.bend -- what shifting a list of offsets does to membership.
#
# A leaf enumerates its offsets shifted to the interval it covers, and the
# question the enumeration law asks is whether a given ordinal is one of
# them. With the offsets fitting in the low `k` bits and the base having room
# for them (proofs/split_add.bend), that question splits in two: does the
# ordinal's high part match the base, and is its low part one of the offsets?
#
# Both halves are ordinary tests a walk can perform, and neither needs
# subtraction.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./split_add.bend as Sa
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/set.bend as S

# Every offset fits in the low `k` bits.
def Ords.all_fit(xs: List<&2, U32>, +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{y, t}:
      Bool.and(Dc.U32.hi_zero(y, k), Ords.all_fit(t, k))

# One offset, shifted: the two tests.
law U32.eq_shift:
  for +y: U32
  for +base: U32
  for +x: U32
  for +k: Nat
  for +hy: {Dc.U32.hi_zero(y, k) == True{} : Bool}
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  for +hit: {U32.is_eq((y + base : U32), x) == True{} : Bool}
  {Bool.and(U32.is_eq(y, U32.and(x, W.U32.mask(k))),
    U32.is_eq(base, W.U32.diff(x, W.U32.mask(k)))) == True{} : Bool}

law U32.eq_shift.parts:
  for +y: U32
  for +base: U32
  for +k: Nat
  for +hy: {Dc.U32.hi_zero(y, k) == True{} : Bool}
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  {Bool.and(U32.is_eq(y, U32.and(U32.or(y, base), W.U32.mask(k))),
    U32.is_eq(base, W.U32.diff(U32.or(y, base), W.U32.mask(k))))
    == True{} : Bool}

def U32.eq_shift.parts(y, base, k, hy, lb):
  %E.U32.sym(U32.and(U32.or(y, base), W.U32.mask(k)), y,
    Sa.U32.and_or_low(y, base, k, hy, lb))
    : {Bool.and(U32.is_eq(y, _),
        U32.is_eq(base, W.U32.diff(U32.or(y, base), W.U32.mask(k))))
      == True{} : Bool}
  %E.U32.sym(W.U32.diff(U32.or(y, base), W.U32.mask(k)), base,
    Sa.U32.diff_or_high(y, base, k, hy, lb))
    : {Bool.and(U32.is_eq(y, y), U32.is_eq(base, _)) == True{} : Bool}
  %E.Bool.sym(U32.is_eq(y, y), True{}, E.U32.is_eq_refl(y))
    : {Bool.and(_, U32.is_eq(base, base)) == True{} : Bool}
  E.U32.is_eq_refl(base)

def U32.eq_shift(y, base, x, k, hy, lb, hit):
  %Equal.trans(U32, U32.or(y, base), (y + base : U32), x,
    E.U32.sym((y + base : U32), U32.or(y, base),
      Sa.U32.add_disjoint(y, base, k, hy, lb)),
    E.U32.eq_reflect((y + base : U32), x, hit))
    : {Bool.and(U32.is_eq(y, U32.and(_, W.U32.mask(k))),
        U32.is_eq(base, W.U32.diff(_, W.U32.mask(k)))) == True{} : Bool}
  U32.eq_shift.parts(y, base, k, hy, lb)

# And the other direction: matching parts make a matching whole.
law U32.shift_eq:
  for +y: U32
  for +base: U32
  for +x: U32
  for +k: Nat
  for +hy: {Dc.U32.hi_zero(y, k) == True{} : Bool}
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  for +low: {U32.is_eq(y, U32.and(x, W.U32.mask(k))) == True{} : Bool}
  for +high: {U32.is_eq(base, W.U32.diff(x, W.U32.mask(k)))
    == True{} : Bool}
  {U32.is_eq((y + base : U32), x) == True{} : Bool}

def U32.shift_eq(y, base, x, k, hy, lb, low, high):
  %E.U32.sym((y + base : U32), U32.or(y, base),
    Sa.U32.add_disjoint(y, base, k, hy, lb))
    : {U32.is_eq(_, x) == True{} : Bool}
  %E.U32.sym(y, U32.and(x, W.U32.mask(k)),
    E.U32.eq_reflect(y, U32.and(x, W.U32.mask(k)), low))
    : {U32.is_eq(U32.or(_, base), x) == True{} : Bool}
  %E.U32.sym(base, W.U32.diff(x, W.U32.mask(k)),
    E.U32.eq_reflect(base, W.U32.diff(x, W.U32.mask(k)), high))
    : {U32.is_eq(U32.or(U32.and(x, W.U32.mask(k)), _), x)
      == True{} : Bool}
  %E.U32.sym(U32.or(U32.and(x, W.U32.mask(k)),
      W.U32.diff(x, W.U32.mask(k))), x, Sa.U32.or_split(x, k))
    : {U32.is_eq(_, x) == True{} : Bool}
  E.U32.is_eq_refl(x)

# ---------------------------------------------------------------------------
# A whole list of offsets.
# ---------------------------------------------------------------------------

def Ords.head_shift_eq(xs: List<&2, U32>, +base: U32, +x: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, t}:
      U32.is_eq((y + base : U32), x)

def Ords.head_low_eq(xs: List<&2, U32>, +x: U32, +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, t}:
      U32.is_eq(y, U32.and(x, W.U32.mask(k)))

law Ords.contains_shift:
  for +xs: List<&2, U32>
  for +hit: Bool
  for +hi: Bool
  for +lo: Bool
  for +base: U32
  for +x: U32
  for +k: Nat
  for +eh: {hit == Ords.head_shift_eq(xs, base, x) : Bool}
  for +ehi: {hi == U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))) : Bool}
  for +elo: {lo == Ords.head_low_eq(xs, x, k) : Bool}
  for +fit: {Ords.all_fit(xs, k) == True{} : Bool}
  for +lb: {Sa.U32.lo_zero(base, k) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, S.PSet.shift(xs, base), x)
    == Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
         List.contains(~U32, ~U32.is_eq, xs,
           U32.and(x, W.U32.mask(k)))) : Bool}

# The head matched: both sides are `True{}`.
law Ords.contains_shift.hit:
  for +y: U32
  for +t: List<&2, U32>
  for +base: U32
  for +x: U32
  for +k: Nat
  for +lo: {U32.is_eq(y, U32.and(x, W.U32.mask(k))) == True{} : Bool}
  for +hi: {U32.is_eq(base, W.U32.diff(x, W.U32.mask(k)))
    == True{} : Bool}
  for +eh: {U32.is_eq((y + base : U32), x) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, S.PSet.shift(Con{y, t}, base), x)
    == Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
         List.contains(~U32, ~U32.is_eq, Con{y, t},
           U32.and(x, W.U32.mask(k)))) : Bool}

def Ords.contains_shift.hit(y, t, base, x, k, lo, hi, eh):
  %E.Bool.sym(U32.is_eq((y + base : U32), x), True{}, eh) : {Bool.or(_, List.contains(~U32, ~U32.is_eq,
      S.PSet.shift(t, base), x))
    == Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
         Bool.or(U32.is_eq(y, U32.and(x, W.U32.mask(k))),
           List.contains(~U32, ~U32.is_eq, t,
             U32.and(x, W.U32.mask(k))))) : Bool}
  %E.Bool.sym(U32.is_eq(y, U32.and(x, W.U32.mask(k))), True{}, lo)
    : {True{} == Bool.and(U32.is_eq(base,
      W.U32.diff(x, W.U32.mask(k))),
      Bool.or(_, List.contains(~U32, ~U32.is_eq, t,
        U32.and(x, W.U32.mask(k))))) : Bool}
  %E.Bool.sym(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))), True{}, hi)
    : {True{} == Bool.and(_, True{}) : Bool}
  {==}

# The head did not match and neither does the base: both sides are `False{}`.
law Ords.contains_shift.miss:
  for +y: U32
  for +t: List<&2, U32>
  for +base: U32
  for +x: U32
  for +k: Nat
  for +eh: {U32.is_eq((y + base : U32), x) == False{} : Bool}
  for +ehi: {U32.is_eq(base, W.U32.diff(x, W.U32.mask(k)))
    == False{} : Bool}
  for +ih: {List.contains(~U32, ~U32.is_eq, S.PSet.shift(t, base), x)
    == Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
         List.contains(~U32, ~U32.is_eq, t,
           U32.and(x, W.U32.mask(k)))) : Bool}
  {List.contains(~U32, ~U32.is_eq, S.PSet.shift(Con{y, t}, base), x)
    == Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
         List.contains(~U32, ~U32.is_eq, Con{y, t},
           U32.and(x, W.U32.mask(k)))) : Bool}

law Bool.and_false_cong:
  for +h: Bool
  for +a: Bool
  for +b: Bool
  for +e: {h == False{} : Bool}
  {Bool.and(h, a) == Bool.and(h, b) : Bool}

def Bool.and_false_cong(h, a, b, e):
  %E.Bool.sym(h, False{}, e)
    : {Bool.and(_, a) == Bool.and(_, b) : Bool}
  {==}

def Ords.contains_shift.miss(y, t, base, x, k, eh, ehi, ih):
  %E.Bool.sym(U32.is_eq((y + base : U32), x), False{}, eh)
    : {Bool.or(_, List.contains(~U32, ~U32.is_eq,
        S.PSet.shift(t, base), x))
      == Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
           Bool.or(U32.is_eq(y, U32.and(x, W.U32.mask(k))),
             List.contains(~U32, ~U32.is_eq, t,
               U32.and(x, W.U32.mask(k))))) : Bool}
  Equal.trans(Bool,
    List.contains(~U32, ~U32.is_eq, S.PSet.shift(t, base), x),
    Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
      List.contains(~U32, ~U32.is_eq, t, U32.and(x, W.U32.mask(k)))),
    Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
      Bool.or(U32.is_eq(y, U32.and(x, W.U32.mask(k))),
        List.contains(~U32, ~U32.is_eq, t, U32.and(x, W.U32.mask(k))))),
    ih,
    Bool.and_false_cong(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
      List.contains(~U32, ~U32.is_eq, t, U32.and(x, W.U32.mask(k))),
      Bool.or(U32.is_eq(y, U32.and(x, W.U32.mask(k))),
        List.contains(~U32, ~U32.is_eq, t, U32.and(x, W.U32.mask(k)))),
      ehi))

# The head did not match, the base did, and the head is not the low part
# either: both sides are the tail.
law Ords.contains_shift.tail:
  for +y: U32
  for +t: List<&2, U32>
  for +base: U32
  for +x: U32
  for +k: Nat
  for +eh: {U32.is_eq((y + base : U32), x) == False{} : Bool}
  for +ehi: {U32.is_eq(base, W.U32.diff(x, W.U32.mask(k)))
    == True{} : Bool}
  for +elo: {U32.is_eq(y, U32.and(x, W.U32.mask(k))) == False{} : Bool}
  for +ih: {List.contains(~U32, ~U32.is_eq, S.PSet.shift(t, base), x)
    == Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
         List.contains(~U32, ~U32.is_eq, t,
           U32.and(x, W.U32.mask(k)))) : Bool}
  {List.contains(~U32, ~U32.is_eq, S.PSet.shift(Con{y, t}, base), x)
    == Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
         List.contains(~U32, ~U32.is_eq, Con{y, t},
           U32.and(x, W.U32.mask(k)))) : Bool}

def Ords.contains_shift.tail(y, t, base, x, k, eh, ehi, elo, ih):
  %E.Bool.sym(U32.is_eq((y + base : U32), x), False{}, eh) : {Bool.or(_, List.contains(~U32, ~U32.is_eq,
      S.PSet.shift(t, base), x))
    == Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
         Bool.or(U32.is_eq(y, U32.and(x, W.U32.mask(k))),
           List.contains(~U32, ~U32.is_eq, t,
             U32.and(x, W.U32.mask(k))))) : Bool}
  %E.Bool.sym(U32.is_eq(y, U32.and(x, W.U32.mask(k))), False{}, elo)
    : {List.contains(~U32, ~U32.is_eq, S.PSet.shift(t, base), x)
    == Bool.and(U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
         Bool.or(_, List.contains(~U32, ~U32.is_eq, t,
           U32.and(x, W.U32.mask(k))))) : Bool}
  ih

def Ords.contains_shift(xs, hit, hi, lo, base, x, k, eh, ehi, elo, fit,
  lb):
  match xs:
    case Nil{}:
      E.Bool.sym(Bool.and(U32.is_eq(base,
        W.U32.diff(x, W.U32.mask(k))), False{}), False{},
        Sa.Word.and_false_r(U32.is_eq(base,
          W.U32.diff(x, W.U32.mask(k)))))
    case Con{y, t}:
      match hit:
        case True{}:
          Ords.contains_shift.hit(y, t, base, x, k,
            E.Bool.and_l(U32.is_eq(y, U32.and(x, W.U32.mask(k))),
              U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
              U32.eq_shift(y, base, x, k,
                E.Bool.and_l(Dc.U32.hi_zero(y, k), Ords.all_fit(t, k),
                  fit), lb,
                E.Bool.sym(True{}, Ords.head_shift_eq(Con{y, t}, base, x),
                  eh))),
            E.Bool.and_r(U32.is_eq(y, U32.and(x, W.U32.mask(k))),
              U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
              U32.eq_shift(y, base, x, k,
                E.Bool.and_l(Dc.U32.hi_zero(y, k), Ords.all_fit(t, k),
                  fit), lb,
                E.Bool.sym(True{}, Ords.head_shift_eq(Con{y, t}, base, x),
                  eh))),
            E.Bool.sym(True{}, Ords.head_shift_eq(Con{y, t}, base, x), eh))
        case False{}:
          match hi:
            case False{}:
              Ords.contains_shift.miss(y, t, base, x, k,
                E.Bool.sym(False{},
                  Ords.head_shift_eq(Con{y, t}, base, x), eh),
                E.Bool.sym(False{},
                  U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))), ehi),
                Ords.contains_shift(t, Ords.head_shift_eq(t, base, x),
                  False{}, Ords.head_low_eq(t, x, k), base, x, k, {==},
                  ehi, {==},
                  E.Bool.and_r(Dc.U32.hi_zero(y, k), Ords.all_fit(t, k),
                    fit), lb))
            case True{}:
              match lo:
                case True{}:
                  E.Bool.noconf({List.contains(~U32, ~U32.is_eq,
                    S.PSet.shift(Con{y, t}, base), x)
                    == Bool.and(U32.is_eq(base,
                      W.U32.diff(x, W.U32.mask(k))),
                      List.contains(~U32, ~U32.is_eq, Con{y, t},
                        U32.and(x, W.U32.mask(k)))) : Bool},
                    Equal.trans(Bool, False{},
                      U32.is_eq((y + base : U32), x), True{},
                      E.Bool.sym(U32.is_eq((y + base : U32), x), False{},
                        E.Bool.sym(False{},
                          Ords.head_shift_eq(Con{y, t}, base, x), eh)),
                      U32.shift_eq(y, base, x, k,
                        E.Bool.and_l(Dc.U32.hi_zero(y, k),
                          Ords.all_fit(t, k), fit), lb,
                        E.Bool.sym(True{},
                          Ords.head_low_eq(Con{y, t}, x, k), elo),
                        E.Bool.sym(True{},
                          U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))),
                          ehi))))
                case False{}:
                  Ords.contains_shift.tail(y, t, base, x, k,
                    E.Bool.sym(False{},
                      Ords.head_shift_eq(Con{y, t}, base, x), eh),
                    E.Bool.sym(True{},
                      U32.is_eq(base, W.U32.diff(x, W.U32.mask(k))), ehi),
                    E.Bool.sym(False{},
                      Ords.head_low_eq(Con{y, t}, x, k), elo),
                    Ords.contains_shift(t, Ords.head_shift_eq(t, base, x),
                      True{}, Ords.head_low_eq(t, x, k), base, x, k, {==},
                      ehi, {==},
                      E.Bool.and_r(Dc.U32.hi_zero(y, k),
                        Ords.all_fit(t, k), fit), lb))
