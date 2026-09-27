# proofs/bridge.bend -- a sparse leaf and the tile it spreads into hold the
# same ordinals (laws S-02 and S-03, at the representation).
#
# SPEC 5.2 calls the sparse/dense crossover a benchmark parameter, not a
# semantic constant. That is only true if a leaf's offset list and the tile it
# spreads into have exactly the same members -- in both directions. Putting a
# member in is proved in proofs/leaf.bend; reading one back out is this file,
# and it is what addressing fact A3 was needed for.
#
# The step that needs A3: setting the bit for one ordinal must not set the bit
# for another. `Words.set` writes at `(o >> 5, o & 31)`, and for that write to
# be invisible at `(x >> 5, x & 31)` the two addresses have to differ -- which
# is exactly A3, now proved in proofs/split.bend from the division identity.

import Base
import ./eq.bend as E
import ./word.bend as PW
import ./bits.bend as PB
import ./words.bend as PWo
import ./ords.bend as PO
import ./addr.bend as Ad
import ./descend.bend as Dc
import ./split.bend as Sp
import ./leaf.bend as Lf
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/ords.bend as O
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# Bit `b` of `2^c` is set exactly when `b` is `c`.
# ---------------------------------------------------------------------------

law Word.get_pow2:
  for +n: Nat
  for +c: Nat
  for +b: Nat
  for +ok: {C.Nat.gt(n, c) == True{} : Bool}
  {W.Word.get(n, Dc.Word.pow2(n, c), b) == Nat.is_eq(b, c) : Bool}

law Word.get_zeros:
  for +n: Nat
  for +j: Nat
  {W.Word.get(n, Dc.Word.zeros(n), j) == False{} : Bool}

def Word.get_zeros(n, j):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match j:
        case 0n:
          {==}
        case 1n+i:
          Word.get_zeros(p, i)

def Word.get_pow2(n, c, b, ok):
  match n:
    case 0n:
      E.Bool.noconf({W.Word.get(0n, Dc.Word.pow2(0n, c), b)
        == Nat.is_eq(b, c) : Bool}, ok)
    case 1n+p:
      match c:
        case 0n:
          match b:
            case 0n:
              {==}
            case 1n+j:
              Word.get_zeros(p, j)
        case 1n+i:
          match b:
            case 0n:
              {==}
            case 1n+j:
              Word.get_pow2(p, i, j, ok)

law U32.test_pow2:
  for +c: Nat
  for +b: Nat
  for +ok: {C.Nat.gt(32n, c) == True{} : Bool}
  {Wo.U32.test(U32.shln(1, c), b) == Nat.is_eq(b, c) : Bool}

def U32.test_pow2(c, b, ok):
  %E.Bool.sym(Wo.U32.test(U32.shln(1, c), b),
    W.U32.bit(U32.shln(1, c), b),
    PB.U32.test_spec(U32.shln(1, c), b))
    : {_ == Nat.is_eq(b, c) : Bool}
  %E.U32.sym(U32.shln(1, c), U32{Dc.Word.pow2(32n, c)},
    Dc.U32.shln_one_pow2(c))
    : {W.U32.bit(_, b) == Nat.is_eq(b, c) : Bool}
  Word.get_pow2(32n, c, b, ok)

# ---------------------------------------------------------------------------
# Setting a bit at a different address changes nothing here.
# ---------------------------------------------------------------------------

law Words.at_set_at_other:
  for +ws: List<&2, U32>
  for +i: Nat
  for +j: Nat
  for +b: Nat
  for +c: Nat
  for +cok: {C.Nat.gt(32n, c) == True{} : Bool}
  for +ne: {Bool.and(Nat.is_eq(i, j), Nat.is_eq(b, c)) == False{} : Bool}
  {Wo.Words.at(Wo.Words.set.at(ws, j, c), i, b)
    == Wo.Words.at(ws, i, b) : Bool}

law Bool.or_false_r:
  for +v: Bool
  {Bool.or(v, False{}) == v : Bool}

def Bool.or_false_r(v):
  match v:
    case False{}:
      {==}
    case True{}:
      {==}

def Words.at_set_at_other(ws, i, j, b, c, cok, ne):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      match i:
        case 0n:
          match j:
            case 0n:
              # Same word, so the bit indices must differ.
              %E.Bool.sym(Wo.U32.test(U32.or(w, U32.shln(1, c)), b),
                Bool.or(Wo.U32.test(w, b), Wo.U32.test(U32.shln(1, c), b)),
                PWo.U32.test_or(w, U32.shln(1, c), b))
                : {_ == Wo.U32.test(w, b) : Bool}
              %E.Bool.sym(Wo.U32.test(U32.shln(1, c), b),
                Nat.is_eq(b, c), U32.test_pow2(c, b, cok))
                : {Bool.or(Wo.U32.test(w, b), _)
                  == Wo.U32.test(w, b) : Bool}
              %E.Bool.sym(Nat.is_eq(b, c), False{}, ne)
                : {Bool.or(Wo.U32.test(w, b), _)
                  == Wo.U32.test(w, b) : Bool}
              Bool.or_false_r(Wo.U32.test(w, b))
            case 1n+j2:
              {==}
        case 1n+i2:
          match j:
            case 0n:
              {==}
            case 1n+j2:
              Words.at_set_at_other(t, i2, j2, b, c, cok, ne)

# ---------------------------------------------------------------------------
# Two different ordinals have two different addresses. This is where A3 is
# spent: without it, `U32.is_eq(o, x) == False{}` says nothing about where in
# a tile the two ordinals live.
# ---------------------------------------------------------------------------

law U32.address_differs:
  for +o: U32
  for +x: U32
  for +ne: {U32.is_eq(o, x) == False{} : Bool}
  {Bool.and(Nat.is_eq(U32.to_nat(U32.shrn(x, 5n)),
      U32.to_nat(U32.shrn(o, 5n))),
      Nat.is_eq(U32.to_nat(U32.and(x, 31)),
        U32.to_nat(U32.and(o, 31)))) == False{} : Bool}

law U32.address_differs.on:
  for +o: U32
  for +x: U32
  for +ne: {U32.is_eq(o, x) == False{} : Bool}
  for +p: Bool
  for +ep: {p == Nat.is_eq(U32.to_nat(U32.shrn(x, 5n)),
    U32.to_nat(U32.shrn(o, 5n))) : Bool}
  for +q: Bool
  for +eq: {q == Nat.is_eq(U32.to_nat(U32.and(x, 31)),
    U32.to_nat(U32.and(o, 31))) : Bool}
  {Bool.and(Nat.is_eq(U32.to_nat(U32.shrn(x, 5n)),
      U32.to_nat(U32.shrn(o, 5n))),
      Nat.is_eq(U32.to_nat(U32.and(x, 31)),
        U32.to_nat(U32.and(o, 31)))) == False{} : Bool}

law U32.address_differs.absurd:
  for +o: U32
  for +x: U32
  for +ne: {U32.is_eq(o, x) == False{} : Bool}
  for +ep: {True{} == Nat.is_eq(U32.to_nat(U32.shrn(x, 5n)),
    U32.to_nat(U32.shrn(o, 5n))) : Bool}
  for +eq: {True{} == Nat.is_eq(U32.to_nat(U32.and(x, 31)),
    U32.to_nat(U32.and(o, 31))) : Bool}
  {False{} == True{} : Bool}

def U32.eq_at(+o: U32, k: U32) -> Bool:
  U32.is_eq(o, k)

def U32.address_differs.absurd(o, x, ne, ep, eq):
  Equal.trans(Bool, False{}, U32.is_eq(o, x), True{},
    E.Bool.sym(U32.is_eq(o, x), False{}, ne),
    Equal.trans(Bool, U32.is_eq(o, x), U32.is_eq(o, o), True{},
      Equal.cong(U32, Bool, U32.eq_at(o), x, o,
        Sp.U32.address_inj(x, o,
          Lf.Nat.is_eq_reflect(U32.to_nat(U32.shrn(x, 5n)),
            U32.to_nat(U32.shrn(o, 5n)),
            E.Bool.sym(True{}, Nat.is_eq(U32.to_nat(U32.shrn(x, 5n)),
              U32.to_nat(U32.shrn(o, 5n))), ep)),
          Lf.Nat.is_eq_reflect(U32.to_nat(U32.and(x, 31)),
            U32.to_nat(U32.and(o, 31)),
            E.Bool.sym(True{}, Nat.is_eq(U32.to_nat(U32.and(x, 31)),
              U32.to_nat(U32.and(o, 31))), eq)))),
      E.U32.is_eq_refl(o)))

def U32.address_differs.on(o, x, ne, p, ep, q, eq):
  match p:
    case False{}:
      %ep : {Bool.and(_, Nat.is_eq(U32.to_nat(U32.and(x, 31)),
        U32.to_nat(U32.and(o, 31)))) == False{} : Bool}
      {==}
    case True{}:
      match q:
        case False{}:
          %eq : {Bool.and(Nat.is_eq(U32.to_nat(U32.shrn(x, 5n)),
            U32.to_nat(U32.shrn(o, 5n))), _) == False{} : Bool}
          %ep : {Bool.and(_, False{}) == False{} : Bool}
          {==}
        case True{}:
          # Both halves of the address agree, so by A3 the ordinals are the
          # same -- which `ne` denies.
          E.Bool.noconf({Bool.and(Nat.is_eq(U32.to_nat(U32.shrn(x, 5n)),
            U32.to_nat(U32.shrn(o, 5n))),
            Nat.is_eq(U32.to_nat(U32.and(x, 31)),
              U32.to_nat(U32.and(o, 31)))) == False{} : Bool},
            U32.address_differs.absurd(o, x, ne, ep, eq))

def U32.address_differs(o, x, ne):
  U32.address_differs.on(o, x, ne,
    Nat.is_eq(U32.to_nat(U32.shrn(x, 5n)),
      U32.to_nat(U32.shrn(o, 5n))), {==},
    Nat.is_eq(U32.to_nat(U32.and(x, 31)),
      U32.to_nat(U32.and(o, 31))), {==})

# ---------------------------------------------------------------------------
# So a set for one ordinal is invisible at another, and an ordinal not in a
# sparse leaf's list is not in the tile it spreads into.
# ---------------------------------------------------------------------------

law Words.bit_set_other:
  for +ws: List<&2, U32>
  for +x: U32
  for +o: U32
  for +ne: {U32.is_eq(o, x) == False{} : Bool}
  {Wo.Words.bit(Wo.Words.set(ws, o), x) == Wo.Words.bit(ws, x) : Bool}

def Words.bit_set_other(ws, x, o, ne):
  Words.at_set_at_other(ws, U32.to_nat(U32.shrn(x, 5n)),
    U32.to_nat(U32.shrn(o, 5n)), U32.to_nat(U32.and(x, 31)),
    U32.to_nat(U32.and(o, 31)), Ad.U32.low_five_bound(o),
    U32.address_differs(o, x, ne))

# `Ords.elem` answers `False{}` only if the head comparison did too, because
# once the scan has found the ordinal it stays found.
def Ords.go_at(+t: List<&2, U32>, +x: U32, k: Bool) -> Bool:
  O.Ords.elem.go(t, x, k)

law Ords.head_ne:
  for +o: U32
  for +t: List<&2, U32>
  for +x: U32
  for +no: {O.Ords.elem(Con{o, t}, x) == False{} : Bool}
  {U32.is_eq(o, x) == False{} : Bool}

law Ords.head_ne.on:
  for +o: U32
  for +t: List<&2, U32>
  for +x: U32
  for +no: {O.Ords.elem(Con{o, t}, x) == False{} : Bool}
  for +e: Bool
  for +ee: {e == U32.is_eq(o, x) : Bool}
  {U32.is_eq(o, x) == False{} : Bool}

def Ords.head_ne.on(o, t, x, no, e, ee):
  match e:
    case False{}:
      E.Bool.sym(e, U32.is_eq(o, x), ee)
    case True{}:
      # The head matched, so the scan found the ordinal and cannot have
      # answered `False{}`.
      E.Bool.noconf({U32.is_eq(o, x) == False{} : Bool},
        Equal.trans(Bool, False{}, O.Ords.elem.go(t, x, True{}), True{},
          E.Bool.sym(O.Ords.elem.go(t, x, True{}), False{},
            Equal.trans(Bool, O.Ords.elem.go(t, x, True{}),
              O.Ords.elem.go(t, x, U32.is_eq(o, x)), False{},
              Equal.cong(Bool, Bool, Ords.go_at(t, x), True{},
                U32.is_eq(o, x), ee),
              no)),
          PO.Ords.elem_go_found(t, x)))

def Ords.head_ne(o, t, x, no):
  Ords.head_ne.on(o, t, x, no, U32.is_eq(o, x), {==})

law Words.bit_spread_not_elem:
  for +offs: List<&2, U32>
  for +ws: List<&2, U32>
  for +x: U32
  for +no: {O.Ords.elem(offs, x) == False{} : Bool}
  {Wo.Words.bit(S.PSet.spread(offs, ws), x)
    == Wo.Words.bit(ws, x) : Bool}

law Ords.tail_no:
  for +o: U32
  for +t: List<&2, U32>
  for +x: U32
  for +no: {O.Ords.elem(Con{o, t}, x) == False{} : Bool}
  {O.Ords.elem(t, x) == False{} : Bool}

def Ords.tail_no(o, t, x, no):
  Equal.trans(Bool, O.Ords.elem.go(t, x, False{}),
    O.Ords.elem.go(t, x, U32.is_eq(o, x)), False{},
    E.Bool.sym(O.Ords.elem.go(t, x, U32.is_eq(o, x)),
      O.Ords.elem.go(t, x, False{}),
      Equal.cong(Bool, Bool, Ords.go_at(t, x), U32.is_eq(o, x), False{},
        Ords.head_ne(o, t, x, no))),
    no)

def Words.bit_spread_not_elem(offs, ws, x, no):
  match offs:
    case Nil{}:
      {==}
    case Con{o, t}:
      %Words.bit_set_other(ws, x, o, Ords.head_ne(o, t, x, no))
        : {Wo.Words.bit(S.PSet.spread(t, Wo.Words.set(ws, o)), x)
          == _ : Bool}
      Words.bit_spread_not_elem(t, Wo.Words.set(ws, o), x,
        Ords.tail_no(o, t, x, no))

# ---------------------------------------------------------------------------
# Both directions at once: a sparse leaf's offsets are exactly the bits of the
# tile it spreads into.
# ---------------------------------------------------------------------------

law Words.bit_zeros:
  for +n: Nat
  for +x: U32
  {Wo.Words.bit(Wo.Words.zeros(n), x) == False{} : Bool}

law Words.at_zeros:
  for +n: Nat
  for +i: Nat
  for +b: Nat
  {Wo.Words.at(Wo.Words.zeros(n), i, b) == False{} : Bool}

def Words.at_zeros(n, i, b):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match i:
        case 0n:
          Equal.trans(Bool, Wo.U32.test(0, b), W.U32.bit(0, b), False{},
            PB.U32.test_spec(0, b), PW.U32.bit_zero(b))
        case 1n+j:
          Words.at_zeros(p, j, b)

def Words.bit_zeros(n, x):
  Words.at_zeros(n, U32.to_nat(U32.shrn(x, 5n)),
    U32.to_nat(U32.and(x, 31)))

law PSet.sparse_matches_its_tile:
  for +offs: List<&2, U32>
  for +x: U32
  for +fits: {Wo.Words.has_word(Wo.Words.zeros(128n),
    U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}
  {Wo.Words.bit(S.PSet.spread(offs, Wo.Words.zeros(128n)), x)
    == O.Ords.elem(offs, x) : Bool}

law PSet.sparse_matches_its_tile.on:
  for +offs: List<&2, U32>
  for +x: U32
  for +fits: {Wo.Words.has_word(Wo.Words.zeros(128n),
    U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}
  for +e: Bool
  for +ee: {e == O.Ords.elem(offs, x) : Bool}
  {Wo.Words.bit(S.PSet.spread(offs, Wo.Words.zeros(128n)), x)
    == O.Ords.elem(offs, x) : Bool}

def PSet.sparse_matches_its_tile.on(offs, x, fits, e, ee):
  match e:
    case True{}:
      %ee : {Wo.Words.bit(S.PSet.spread(offs, Wo.Words.zeros(128n)), x)
        == _ : Bool}
      Lf.Words.bit_spread_elem(offs, Wo.Words.zeros(128n), x,
        E.Bool.sym(True{}, O.Ords.elem(offs, x), ee), fits)
    case False{}:
      %ee : {Wo.Words.bit(S.PSet.spread(offs, Wo.Words.zeros(128n)), x)
        == _ : Bool}
      Equal.trans(Bool,
        Wo.Words.bit(S.PSet.spread(offs, Wo.Words.zeros(128n)), x),
        Wo.Words.bit(Wo.Words.zeros(128n), x), False{},
        Words.bit_spread_not_elem(offs, Wo.Words.zeros(128n), x,
          E.Bool.sym(False{}, O.Ords.elem(offs, x), ee)),
        Words.bit_zeros(128n, x))

def PSet.sparse_matches_its_tile(offs, x, fits):
  PSet.sparse_matches_its_tile.on(offs, x, fits, O.Ords.elem(offs, x),
    {==})
