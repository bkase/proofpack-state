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
import ./descend.bend as Dc
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

# ---------------------------------------------------------------------------
# From the descent invariant to the leaf's tile width.
#
# A leaf covers 4096 ordinals, so an ordinal inside it fits in 12 bits, so the
# word it lives in -- `x >> 5` -- fits in 7, so it is below 128. A structurally
# valid leaf is 128 words wide. So the hypothesis
# `inserting_into_a_leaf_keeps_that_ordinal` carries is implied by the
# invariant the descent maintains, and no longer has to be assumed once the
# ordinal has arrived at the leaf.
# ---------------------------------------------------------------------------

law Nat.is_eq_reflect:
  for +a: Nat
  for +b: Nat
  for +ok: {Nat.is_eq(a, b) == True{} : Bool}
  {a == b : Nat}

def Nat.is_eq_reflect(a, b, ok):
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          E.Bool.noconf({0n == 1n+q : Nat}, ok)
    case 1n+p:
      match b:
        case 0n:
          E.Bool.noconf({1n+p == 0n : Nat}, ok)
        case 1n+q:
          %Nat.is_eq_reflect(p, q, ok) : {1n+p == 1n+_ : Nat}
          {==}

law Words.has_word_of_length:
  for +ws: List<&2, U32>
  for +i: Nat
  for +ok: {C.Nat.gt(List.length(&2, U32, ws), i) == True{} : Bool}
  {Wo.Words.has_word(ws, i) == True{} : Bool}

def Words.has_word_of_length(ws, i, ok):
  match ws:
    case Nil{}:
      E.Bool.noconf({Wo.Words.has_word(Nil{}, i) == True{} : Bool}, ok)
    case Con{w, t}:
      match i:
        case 0n:
          {==}
        case 1n+j:
          Words.has_word_of_length(t, j, ok)

law Words.length_zeros:
  for +n: Nat
  {List.length(&2, U32, Wo.Words.zeros(n)) == n : Nat}

def Words.length_zeros(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %E.Nat.sym(List.length(&2, U32, Wo.Words.zeros(p)), p,
        Words.length_zeros(p)) : {1n+_ == 1n+p : Nat}
      {==}

law Words.length_ones:
  for +n: Nat
  {List.length(&2, U32, Wo.Words.ones(n)) == n : Nat}

def Words.length_ones(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %E.Nat.sym(List.length(&2, U32, Wo.Words.ones(p)), p,
        Words.length_ones(p)) : {1n+_ == 1n+p : Nat}
      {==}

law Words.length_set:
  for +ws: List<&2, U32>
  for +i: Nat
  for +b: Nat
  {List.length(&2, U32, Wo.Words.set.at(ws, i, b))
    == List.length(&2, U32, ws) : Nat}

def Words.length_set(ws, i, b):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      match i:
        case 0n:
          {==}
        case 1n+j:
          %E.Nat.sym(List.length(&2, U32, Wo.Words.set.at(t, j, b)),
            List.length(&2, U32, t), Words.length_set(t, j, b))
            : {1n+_ == 1n+List.length(&2, U32, t) : Nat}
          {==}

law Words.length_spread:
  for +offs: List<&2, U32>
  for +ws: List<&2, U32>
  {List.length(&2, U32, S.PSet.spread(offs, ws))
    == List.length(&2, U32, ws) : Nat}

def Words.length_spread(offs, ws):
  match offs:
    case Nil{}:
      {==}
    case Con{o, t}:
      %Words.length_set(ws, U32.to_nat(U32.shrn(o, 5n)),
        U32.to_nat(U32.and(o, 31)))
        : {List.length(&2, U32, S.PSet.spread(t, Wo.Words.set(ws, o)))
          == _ : Nat}
      Words.length_spread(t, Wo.Words.set(ws, o))

law PSet.leaf_words_width:
  for +s: S.PSet
  for +v: {S.PSet.valid.leaf(s) == True{} : Bool}
  {List.length(&2, U32, S.PSet.leaf_words(s)) == 128n : Nat}

def PSet.leaf_words_width(s, v):
  match s:
    case S.PZero{}:
      Words.length_zeros(128n)
    case S.PFull{}:
      Words.length_ones(128n)
    case S.PBranch{l, h}:
      E.Bool.noconf({List.length(&2, U32, S.PSet.leaf_words(
        S.PBranch{l, h})) == 128n : Nat}, v)
    case S.PDense{ws}:
      Nat.is_eq_reflect(List.length(&2, U32, ws), 128n, v)
    case S.PSparse{offs}:
      %E.Nat.sym(
        List.length(&2, U32, S.PSet.spread(offs, Wo.Words.zeros(128n))),
        List.length(&2, U32, Wo.Words.zeros(128n)),
        Words.length_spread(offs, Wo.Words.zeros(128n)))
        : {_ == 128n : Nat}
      Words.length_zeros(128n)

# The word an in-range ordinal lives in is one a 128-word tile has.
law PSet.fits_of_range:
  for +s: S.PSet
  for +x: U32
  for +v: {S.PSet.valid.leaf(s) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {Wo.Words.has_word(S.PSet.leaf_words(s),
    U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}

law PSet.word_index_bound:
  for +s: S.PSet
  for +x: U32
  for +v: {S.PSet.valid.leaf(s) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {C.Nat.gt(List.length(&2, U32, S.PSet.leaf_words(s)),
    U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}

# `x` fits in 12 bits, so `x >> 5` fits in 7, so it is below 128.
law PSet.shift_bound:
  for +x: U32
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {C.Nat.gt(128n, U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}

law PSet.shift_bound.inv:
  for +x: U32
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {Dc.U32.hi_zero(U32.shrn(x, 5n), 7n) == True{} : Bool}

def PSet.shift_bound.inv(x, inr):
  %E.Bool.sym(Dc.U32.hi_zero(U32.shrn(x, 5n), 7n),
    Dc.U32.hi_zero(x, 12n), Dc.U32.hi_zero_shrn(x, 5n, 7n))
    : {_ == True{} : Bool}
  inr

law PSet.shift_bound.go:
  for +y: U32
  for +hz: {Dc.U32.hi_zero(y, 7n) == True{} : Bool}
  {C.Nat.gt(128n, U32.to_nat(y)) == True{} : Bool}

def PSet.shift_bound.go(y, hz):
  match y:
    case U32{w}:
      Dc.Word.to_nat_bound(32n, 7n, w, hz)

def PSet.shift_bound(x, inr):
  PSet.shift_bound.go(U32.shrn(x, 5n),
    PSet.shift_bound.inv(x, inr))

def PSet.word_index_bound(s, x, v, inr):
  %E.Nat.sym(List.length(&2, U32, S.PSet.leaf_words(s)), 128n,
    PSet.leaf_words_width(s, v))
    : {C.Nat.gt(_, U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}
  PSet.shift_bound(x, inr)

def PSet.fits_of_range(s, x, v, inr):
  Words.has_word_of_length(S.PSet.leaf_words(s),
    U32.to_nat(U32.shrn(x, 5n)),
    PSet.word_index_bound(s, x, v, inr))

# ---------------------------------------------------------------------------
# Structural validity, split.
# ---------------------------------------------------------------------------

law PSet.valid_zero:
  for +d: Nat
  {S.PSet.valid(d, S.PZero{}, True{}) == True{} : Bool}

def PSet.valid_zero(d):
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

law PSet.valid_false:
  for +d: Nat
  for +s: S.PSet
  {S.PSet.valid(d, s, False{}) == False{} : Bool}

def PSet.valid_false(d, s):
  match d:
    case 0n:
      {==}
    case 1n+p:
      match s:
        case S.PZero{}:
          {==}
        case S.PFull{}:
          {==}
        case S.PSparse{o}:
          {==}
        case S.PDense{w}:
          {==}
        case S.PBranch{lo, hi}:
          {==}

def PSet.valid_at(+p: Nat, +hi: S.PSet, a: Bool) -> Bool:
  S.PSet.valid(p, hi, a)

law PSet.valid_lo:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +v: {S.PSet.valid(1n+p, S.PBranch{lo, hi}, True{}) == True{} : Bool}
  {S.PSet.valid(p, lo, True{}) == True{} : Bool}

law PSet.valid_lo.on:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +a: Bool
  for +ea: {a == S.PSet.valid(p, lo, True{}) : Bool}
  for +v: {S.PSet.valid(1n+p, S.PBranch{lo, hi}, True{}) == True{} : Bool}
  {S.PSet.valid(p, lo, True{}) == True{} : Bool}

def PSet.valid_lo.on(p, lo, hi, a, ea, v):
  match a:
    case True{}:
      E.Bool.sym(a, S.PSet.valid(p, lo, True{}), ea)
    case False{}:
      # The low half is invalid, so the whole branch is -- the accumulator
      # never recovers once it is `False{}` -- and that contradicts `v`.
      E.Bool.noconf({S.PSet.valid(p, lo, True{}) == True{} : Bool},
        Equal.trans(Bool, False{}, S.PSet.valid(p, hi, False{}), True{},
          E.Bool.sym(S.PSet.valid(p, hi, False{}), False{},
            PSet.valid_false(p, hi)),
          Equal.trans(Bool, S.PSet.valid(p, hi, False{}),
            S.PSet.valid(p, hi, S.PSet.valid(p, lo, True{})), True{},
            Equal.cong(Bool, Bool, PSet.valid_at(p, hi), False{},
              S.PSet.valid(p, lo, True{}), ea),
            v)))

def PSet.valid_lo(p, lo, hi, v):
  PSet.valid_lo.on(p, lo, hi, S.PSet.valid(p, lo, True{}), {==}, v)

law PSet.valid_hi:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +v: {S.PSet.valid(1n+p, S.PBranch{lo, hi}, True{}) == True{} : Bool}
  {S.PSet.valid(p, hi, True{}) == True{} : Bool}

def PSet.valid_hi(p, lo, hi, v):
  %PSet.valid_lo(p, lo, hi, v)
    : {S.PSet.valid(p, hi, _) == True{} : Bool}
  v

# ---------------------------------------------------------------------------
# P-01's descent.
#
# `PSet.add` and `PSet.mem` take the same branch from the same half-width at
# every node, so the tree layer adds nothing but addressing -- and the
# addressing is now proved (proofs/descend.bend). The invariant carried down
# is `U32.hi_zero(x, 12n+d)`: at depth d a node covers 2^(12+d) ordinals, so
# an ordinal inside it fits in 12+d bits. At depth 20 that is 32 bits, which
# every `U32` satisfies, so the production entry point needs no hypothesis
# about the ordinal at all.
# ---------------------------------------------------------------------------

def U32.lt_at(+x: U32, k: U32) -> Bool:
  U32.is_lt(x, k)

law PSet.half_shr:
  for +p: Nat
  for +h: U32
  for +eh: {h == U32.shln(1, 12n+p) : U32}
  for +dok: {C.Nat.gt(32n, 12n+p) == True{} : Bool}
  {U32.shr(h) == U32.shln(1, 11n+p) : U32}

def PSet.half_shr(p, h, eh, dok):
  %E.U32.sym(h, U32.shln(1, 12n+p), eh)
    : {U32.shr(_) == U32.shln(1, 11n+p) : U32}
  Dc.U32.shr_shln_one(11n+p, dok)

law PSet.range_lo:
  for +p: Nat
  for +h: U32
  for +x: U32
  for +eh: {h == U32.shln(1, 12n+p) : U32}
  for +dok: {C.Nat.gt(32n, 12n+p) == True{} : Bool}
  for +eb: {True{} == U32.is_lt(x, h) : Bool}
  {Dc.U32.hi_zero(x, 12n+p) == True{} : Bool}

def PSet.range_lo(p, h, x, eh, dok, eb):
  Equal.trans(Bool, Dc.U32.hi_zero(x, 12n+p),
    U32.is_lt(x, U32.shln(1, 12n+p)), True{},
    E.Bool.sym(U32.is_lt(x, U32.shln(1, 12n+p)),
      Dc.U32.hi_zero(x, 12n+p), Dc.U32.is_lt_shln(x, 12n+p, dok)),
    Equal.trans(Bool, U32.is_lt(x, U32.shln(1, 12n+p)),
      U32.is_lt(x, h), True{},
      Equal.cong(U32, Bool, U32.lt_at(x), U32.shln(1, 12n+p), h,
        E.U32.sym(h, U32.shln(1, 12n+p), eh)),
      E.Bool.sym(True{}, U32.is_lt(x, h), eb)))

law PSet.range_hi:
  for +p: Nat
  for +h: U32
  for +x: U32
  for +eh: {h == U32.shln(1, 12n+p) : U32}
  for +dok: {C.Nat.gt(32n, 12n+p) == True{} : Bool}
  for +eb: {False{} == U32.is_lt(x, h) : Bool}
  for +inv: {Dc.U32.hi_zero(x, 13n+p) == True{} : Bool}
  {Dc.U32.hi_zero(U32.sub(x, h), 12n+p) == True{} : Bool}

law PSet.range_hi.no:
  for +p: Nat
  for +h: U32
  for +x: U32
  for +eh: {h == U32.shln(1, 12n+p) : U32}
  for +dok: {C.Nat.gt(32n, 12n+p) == True{} : Bool}
  for +eb: {False{} == U32.is_lt(x, h) : Bool}
  {Dc.U32.hi_zero(x, 12n+p) == False{} : Bool}

def PSet.range_hi.no(p, h, x, eh, dok, eb):
  Equal.trans(Bool, Dc.U32.hi_zero(x, 12n+p),
    U32.is_lt(x, U32.shln(1, 12n+p)), False{},
    E.Bool.sym(U32.is_lt(x, U32.shln(1, 12n+p)),
      Dc.U32.hi_zero(x, 12n+p), Dc.U32.is_lt_shln(x, 12n+p, dok)),
    Equal.trans(Bool, U32.is_lt(x, U32.shln(1, 12n+p)),
      U32.is_lt(x, h), False{},
      Equal.cong(U32, Bool, U32.lt_at(x), U32.shln(1, 12n+p), h,
        E.U32.sym(h, U32.shln(1, 12n+p), eh)),
      E.Bool.sym(False{}, U32.is_lt(x, h), eb)))

def PSet.range_hi(p, h, x, eh, dok, eb, inv):
  %E.U32.sym(h, U32.shln(1, 12n+p), eh)
    : {Dc.U32.hi_zero(U32.sub(x, _), 12n+p) == True{} : Bool}
  Dc.U32.hi_zero_sub(x, 12n+p, inv,
    PSet.range_hi.no(p, h, x, eh, dok, eb))

law PSet.mem_add_go:
  for +d: Nat
  for +s: S.PSet
  for +h: U32
  for +x: U32
  for +b: Bool
  for +eh: {h == U32.shln(1, 11n+d) : U32}
  for +eb: {b == U32.is_lt(x, h) : Bool}
  for +dok: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +v: {S.PSet.valid(d, s, True{}) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  {S.PSet.mem(d, S.PSet.add(d, s, h, x, b), h, x) == True{} : Bool}

def PSet.mem_add_go(d, s, h, x, b, eh, eb, dok, v, inv):
  match d:
    case 0n:
      # At the leaf, `add` and `mem` both ignore the half-width, and the
      # invariant is exactly the hypothesis the leaf law asks for.
      PSet.mem_add_leaf(s, x, PSet.fits_of_range(s, x, v, inv))
    case 1n+p:
      match s:
        case S.PFull{}:
          {==}
        case S.PSparse{o}:
          E.Bool.noconf({S.PSet.mem(1n+p,
            S.PSet.add(1n+p, S.PSparse{o}, h, x, b), h, x)
            == True{} : Bool}, v)
        case S.PDense{w}:
          E.Bool.noconf({S.PSet.mem(1n+p,
            S.PSet.add(1n+p, S.PDense{w}, h, x, b), h, x)
            == True{} : Bool}, v)
        case S.PZero{}:
          match b:
            case True{}:
              %eb
                : {S.PSet.mem(p, S.PSet.pick(_,
                    S.PSet.add(p, S.PZero{}, U32.shr(h), x,
                      U32.is_lt(x, U32.shr(h))), S.PZero{}),
                    U32.shr(h), S.PSet.rebase(_, h, x)) == True{} : Bool}
              PSet.mem_add_go(p, S.PZero{}, U32.shr(h), x,
                U32.is_lt(x, U32.shr(h)),
                PSet.half_shr(p, h, eh, dok), {==},
                Dc.Nat.gt_down(32n, 11n+p, dok),
                PSet.valid_zero(p),
                PSet.range_lo(p, h, x, eh, dok, eb))
            case False{}:
              %eb
                : {S.PSet.mem(p, S.PSet.pick(_, S.PZero{},
                    S.PSet.add(p, S.PZero{}, U32.shr(h), U32.sub(x, h),
                      U32.is_lt(U32.sub(x, h), U32.shr(h)))),
                    U32.shr(h), S.PSet.rebase(_, h, x)) == True{} : Bool}
              PSet.mem_add_go(p, S.PZero{}, U32.shr(h), U32.sub(x, h),
                U32.is_lt(U32.sub(x, h), U32.shr(h)),
                PSet.half_shr(p, h, eh, dok), {==},
                Dc.Nat.gt_down(32n, 11n+p, dok),
                PSet.valid_zero(p),
                PSet.range_hi(p, h, x, eh, dok, eb, inv))
        case S.PBranch{lo, hi}:
          match b:
            case True{}:
              %eb
                : {S.PSet.mem(p, S.PSet.pick(_,
                    S.PSet.add(p, lo, U32.shr(h), x,
                      U32.is_lt(x, U32.shr(h))), hi),
                    U32.shr(h), S.PSet.rebase(_, h, x)) == True{} : Bool}
              PSet.mem_add_go(p, lo, U32.shr(h), x,
                U32.is_lt(x, U32.shr(h)),
                PSet.half_shr(p, h, eh, dok), {==},
                Dc.Nat.gt_down(32n, 11n+p, dok),
                PSet.valid_lo(p, lo, hi, v),
                PSet.range_lo(p, h, x, eh, dok, eb))
            case False{}:
              %eb
                : {S.PSet.mem(p, S.PSet.pick(_, lo,
                    S.PSet.add(p, hi, U32.shr(h), U32.sub(x, h),
                      U32.is_lt(U32.sub(x, h), U32.shr(h)))),
                    U32.shr(h), S.PSet.rebase(_, h, x)) == True{} : Bool}
              PSet.mem_add_go(p, hi, U32.shr(h), U32.sub(x, h),
                U32.is_lt(U32.sub(x, h), U32.shr(h)),
                PSet.half_shr(p, h, eh, dok), {==},
                Dc.Nat.gt_down(32n, 11n+p, dok),
                PSet.valid_hi(p, lo, hi, v),
                PSet.range_hi(p, h, x, eh, dok, eb, inv))

# P-01's checkable half, at the depth the product runs at. `Idx.sd()` is 20,
# and a depth-20 tree covers 4096 * 2^20 = 2^32 ordinals -- every `U32` -- so
# the range invariant is satisfied by every ordinal and no hypothesis about
# `x` survives. What is left is the structural invariant, which is what
# `PSet.valid` states and what every stored generation is checked against on
# load (law D-01).
law PSet.mem_insert:
  for +s: S.PSet
  for +x: U32
  for +v: {S.PSet.valid(20n, s, True{}) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.insert(20n, s, x), x) == True{} : Bool}

def PSet.mem_insert(s, x, v):
  PSet.mem_add_go(20n, s, S.PSet.half(20n), x,
    U32.is_lt(x, S.PSet.half(20n)), {==}, {==}, {==}, v,
    Dc.U32.hi_zero_full(x))

law Nat.succ_inj2:
  for +a: Nat
  for +b: Nat
  for +e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

def Nat.pred2(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def Nat.succ_inj2(a, b, e):
  Equal.cong(Nat, Nat, Nat.pred2, 1n+a, 1n+b, e)
