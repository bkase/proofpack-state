# proofs/leaf.bend -- inserting into a leaf (law P-01, restated).
#
# P-01 says a persistent update leaves the ordinal it inserted present. As
# stated in LAWS.pending.bend it was *false*, and the counterexample is in
# tests.bend: a `PDense` leaf that is not 128 words wide loses the bit it was
# just given, because `Words.set` past the end of a tile changes nothing.
# That is exactly the shape `PSet.valid` rejects, so the fix is not to weaken
# the claim but to say which leaves it is about.
#
# So the law here carries one hypothesis: the leaf's tile has a word for the
# ordinal being inserted. That is a real condition with a real
# counterexample, it is implied by the structural invariant every stored set
# is checked against (`PSet.valid`, law D-01), and it is the only thing the
# proof needs.
#
# What is *not* here: the same claim at a node. A node's insert descends in
# exact lockstep with a node's membership -- both take the same branch from
# the same half-width -- so the tree layer adds nothing but addressing. The
# addressing is the gap: carrying "the ordinal is inside this interval" down a
# level needs `U32.sub` to be subtraction when it does not borrow, which this
# release does not prove. LAWS.pending.bend lists that with the other
# addressing facts.

import Base
import ./eq.bend as E
import ./ords.bend as PO
import ./bitset.bend as PBs
import ../core/ords.bend as O
import ../core/words.bend as Wo
import ../core/count.bend as C
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# Filling a tile from a list of offsets.
# ---------------------------------------------------------------------------

law Words.has_word_spread:
  for +offs: List<&2, U32>
  for +ws: List<&2, U32>
  for +i: Nat
  {Wo.Words.has_word(S.PSet.spread(offs, ws), i)
    == Wo.Words.has_word(ws, i) : Bool}

def Words.has_word_spread(offs, ws, i):
  match offs:
    case Nil{}:
      {==}
    case Con{o, t}:
      %PBs.Words.has_word_set(ws, i, o)
        : {Wo.Words.has_word(S.PSet.spread(t, Wo.Words.set(ws, o)), i)
            == _ : Bool}
      Words.has_word_spread(t, Wo.Words.set(ws, o), i)

law Words.bit_spread_mono:
  for +offs: List<&2, U32>
  for +ws: List<&2, U32>
  for +x: U32
  for +ok: {Wo.Words.bit(ws, x) == True{} : Bool}
  {Wo.Words.bit(S.PSet.spread(offs, ws), x) == True{} : Bool}

def Words.bit_spread_mono(offs, ws, x, ok):
  match offs:
    case Nil{}:
      ok
    case Con{o, t}:
      Words.bit_spread_mono(t, Wo.Words.set(ws, o), x,
        PBs.Words.bit_set_mono(ws, x, o, ok))

# Implication as a Bool, so a hypothesis can be an equation.
def Bool.imp(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      True{}
    case True{}:
      b

law Bool.imp_elim:
  for +a: Bool
  for +b: Bool
  for +ea: {a == True{} : Bool}
  for +h: {Bool.imp(a, b) == True{} : Bool}
  {b == True{} : Bool}

def Bool.imp_elim(a, b, ea, h):
  match a:
    case True{}:
      h
    case False{}:
      E.Bool.noconf({b == True{} : Bool}, ea)

# The bit is already set once the scan has found the ordinal: if the head is
# the ordinal being looked for, then setting the head set it.
law Words.spread_already:
  for +ws: List<&2, U32>
  for +x: U32
  for +o: U32
  for +e: Bool
  for +ee: {e == U32.is_eq(o, x) : Bool}
  for +fits: {Wo.Words.has_word(ws, U32.to_nat(U32.shrn(x, 5n)))
    == True{} : Bool}
  {Bool.imp(e, Wo.Words.bit(Wo.Words.set(ws, o), x)) == True{} : Bool}

def Words.spread_already(ws, x, o, e, ee, fits):
  match e:
    case False{}:
      {==}
    case True{}:
      %E.U32.sym(o, x,
        E.U32.eq_reflect(o, x, E.Bool.sym(True{}, U32.is_eq(o, x), ee)))
        : {Bool.imp(True{}, Wo.Words.bit(Wo.Words.set(ws, _), x))
            == True{} : Bool}
      %E.Bool.sym(Wo.Words.bit(Wo.Words.set(ws, x), x),
        Wo.Words.has_word(ws, U32.to_nat(U32.shrn(x, 5n))),
        PBs.Words.bit_set(ws, x))
        : {_ == True{} : Bool}
      fits

# An offset in the list ends up set in the tile. `found` is `Ords.elem.go`'s
# accumulator, carried here the same way, with the invariant that once the
# scan has found the ordinal the bit is already set.
law Words.bit_spread_go:
  for +offs: List<&2, U32>
  for +ws: List<&2, U32>
  for +x: U32
  for +found: Bool
  for +ok: {O.Ords.elem.go(offs, x, found) == True{} : Bool}
  for +fits: {Wo.Words.has_word(ws, U32.to_nat(U32.shrn(x, 5n)))
    == True{} : Bool}
  for +already: {Bool.imp(found, Wo.Words.bit(ws, x)) == True{} : Bool}
  {Wo.Words.bit(S.PSet.spread(offs, ws), x) == True{} : Bool}

law Words.has_word_fits:
  for +ws: List<&2, U32>
  for +x: U32
  for +o: U32
  for +fits: {Wo.Words.has_word(ws, U32.to_nat(U32.shrn(x, 5n)))
    == True{} : Bool}
  {Wo.Words.has_word(Wo.Words.set(ws, o), U32.to_nat(U32.shrn(x, 5n)))
    == True{} : Bool}

def Words.has_word_fits(ws, x, o, fits):
  %E.Bool.sym(
    Wo.Words.has_word(Wo.Words.set(ws, o), U32.to_nat(U32.shrn(x, 5n))),
    Wo.Words.has_word(ws, U32.to_nat(U32.shrn(x, 5n))),
    PBs.Words.has_word_set(ws, U32.to_nat(U32.shrn(x, 5n)), o))
    : {_ == True{} : Bool}
  fits

def Words.bit_spread_go(offs, ws, x, found, ok, fits, already):
  match offs:
    case Nil{}:
      Bool.imp_elim(found, Wo.Words.bit(ws, x), ok, already)
    case Con{o, t}:
      match found:
        case True{}:
          Words.bit_spread_mono(Con{o, t}, ws, x,
            Bool.imp_elim(True{}, Wo.Words.bit(ws, x), {==}, already))
        case False{}:
          Words.bit_spread_go(t, Wo.Words.set(ws, o), x,
            U32.is_eq(o, x), ok,
            Words.has_word_fits(ws, x, o, fits),
            Words.spread_already(ws, x, o, U32.is_eq(o, x), {==}, fits))

law Words.bit_spread_elem:
  for +offs: List<&2, U32>
  for +ws: List<&2, U32>
  for +x: U32
  for +ok: {O.Ords.elem(offs, x) == True{} : Bool}
  for +fits: {Wo.Words.has_word(ws, U32.to_nat(U32.shrn(x, 5n)))
    == True{} : Bool}
  {Wo.Words.bit(S.PSet.spread(offs, ws), x) == True{} : Bool}

def Words.bit_spread_elem(offs, ws, x, ok, fits):
  Words.bit_spread_go(offs, ws, x, False{}, ok, fits, {==})

# ---------------------------------------------------------------------------
# P-01 at a leaf.
# ---------------------------------------------------------------------------

law PSet.fits_sparse:
  for +offs: List<&2, U32>
  for +x: U32
  for +fits: {Wo.Words.has_word(S.PSet.leaf_words(S.PSparse{offs}),
    U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}
  {Wo.Words.has_word(Wo.Words.zeros(128n), U32.to_nat(U32.shrn(x, 5n)))
    == True{} : Bool}

def PSet.fits_sparse(offs, x, fits):
  %Words.has_word_spread(offs, Wo.Words.zeros(128n),
    U32.to_nat(U32.shrn(x, 5n)))
    : {_ == True{} : Bool}
  fits

# The sparse/dense crossover, with the decision taken as a parameter. Which
# side it lands on is a storage choice and not a semantic one, which is what
# law S-03 says in general; here it is only needed for the ordinal just
# inserted.
law PSet.mem_fit:
  for +ords: List<&2, U32>
  for +x: U32
  for +small: Bool
  for +inl: {O.Ords.elem(ords, x) == True{} : Bool}
  for +fits: {Wo.Words.has_word(Wo.Words.zeros(128n),
    U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.add.leaf.pick(ords, small), x) == True{} : Bool}

def PSet.mem_fit(ords, x, small, inl, fits):
  match small:
    case True{}:
      inl
    case False{}:
      Words.bit_spread_elem(ords, Wo.Words.zeros(128n), x, inl, fits)

law PSet.mem_add_leaf:
  for +s: S.PSet
  for +x: U32
  for +fits: {Wo.Words.has_word(S.PSet.leaf_words(s),
    U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.add.leaf(s, x), x) == True{} : Bool}

def PSet.mem_add_leaf(s, x, fits):
  match s:
    case S.PZero{}:
      # A new sparse leaf holding just `x`.
      E.U32.is_eq_refl(x)
    case S.PFull{}:
      {==}
    case S.PBranch{l, h}:
      # Structurally invalid at a leaf, and treated as empty: the insert
      # still produces a leaf holding `x`.
      E.U32.is_eq_refl(x)
    case S.PDense{ws}:
      %E.Bool.sym(Wo.Words.bit(Wo.Words.set(ws, x), x),
        Wo.Words.has_word(ws, U32.to_nat(U32.shrn(x, 5n))),
        PBs.Words.bit_set(ws, x))
        : {_ == True{} : Bool}
      fits
    case S.PSparse{offs}:
      PSet.mem_fit(O.Ords.insert(offs, x), x,
        C.Nat.upto(List.length(&2, U32, O.Ords.insert(offs, x)),
          S.PSet.sparse_max()),
        PO.Ords.elem_insert(offs, x),
        PSet.fits_sparse(offs, x, fits))
