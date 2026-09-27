# proofs/intern.bend -- interning round-trips (law U-01, in part).
#
# `Uni.intern` looks an object id up in the identity table and, on a first
# mention, writes a new slot and hands back a fresh ordinal. SPEC's U-01 asks
# for two things: that the map is injective, and that a lookup round-trips
# within one universe. This file proves the round-trip: the ordinal a first
# mention assigns is the ordinal the next lookup finds.
#
# Two pieces do it. `Oid.eq` is reflexive, so the slot just written matches
# the id that wrote it; and a trie reads back what was written
# (proofs/trie.bend), so the bucket the write went into is the bucket the read
# comes out of.
#
# Injectivity -- that two different ids never share an ordinal -- is a
# statement about the whole table rather than one write, and it stays in
# LAWS.pending.bend.

import Base
import ./eq.bend as E
import ./trie.bend as Tr
import ../core/trie.bend as T
import ../adapters/git/oid.bend as O
import ../adapters/git/intern.bend as I

law Oid.eq_refl:
  for +o: O.Oid
  {O.Oid.eq(o, o) == True{} : Bool}

def Oid.eq_refl(o):
  match o:
    case O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}:
      %E.Bool.sym(U32.is_eq(a0, a0), True{}, E.U32.is_eq_refl(a0)) : {Bool.and(_, Bool.and(U32.is_eq(a1, a1),
        Bool.and(U32.is_eq(a2, a2), Bool.and(U32.is_eq(a3, a3),
          Bool.and(U32.is_eq(a4, a4), Bool.and(U32.is_eq(a5, a5),
            Bool.and(U32.is_eq(a6, a6), U32.is_eq(a7, a7))))))))
        == True{} : Bool}
      %E.Bool.sym(U32.is_eq(a1, a1), True{}, E.U32.is_eq_refl(a1)) : {Bool.and(True{}, Bool.and(_,
        Bool.and(U32.is_eq(a2, a2), Bool.and(U32.is_eq(a3, a3),
          Bool.and(U32.is_eq(a4, a4), Bool.and(U32.is_eq(a5, a5),
            Bool.and(U32.is_eq(a6, a6), U32.is_eq(a7, a7))))))))
        == True{} : Bool}
      %E.Bool.sym(U32.is_eq(a2, a2), True{}, E.U32.is_eq_refl(a2)) : {Bool.and(True{}, Bool.and(True{},
        Bool.and(_, Bool.and(U32.is_eq(a3, a3),
          Bool.and(U32.is_eq(a4, a4), Bool.and(U32.is_eq(a5, a5),
            Bool.and(U32.is_eq(a6, a6), U32.is_eq(a7, a7))))))))
        == True{} : Bool}
      %E.Bool.sym(U32.is_eq(a3, a3), True{}, E.U32.is_eq_refl(a3)) : {Bool.and(True{}, Bool.and(True{},
        Bool.and(True{}, Bool.and(_,
          Bool.and(U32.is_eq(a4, a4), Bool.and(U32.is_eq(a5, a5),
            Bool.and(U32.is_eq(a6, a6), U32.is_eq(a7, a7))))))))
        == True{} : Bool}
      %E.Bool.sym(U32.is_eq(a4, a4), True{}, E.U32.is_eq_refl(a4)) : {Bool.and(True{}, Bool.and(True{},
        Bool.and(True{}, Bool.and(True{},
          Bool.and(_, Bool.and(U32.is_eq(a5, a5),
            Bool.and(U32.is_eq(a6, a6), U32.is_eq(a7, a7))))))))
        == True{} : Bool}
      %E.Bool.sym(U32.is_eq(a5, a5), True{}, E.U32.is_eq_refl(a5)) : {Bool.and(True{}, Bool.and(True{},
        Bool.and(True{}, Bool.and(True{},
          Bool.and(True{}, Bool.and(_,
            Bool.and(U32.is_eq(a6, a6), U32.is_eq(a7, a7))))))))
        == True{} : Bool}
      %E.Bool.sym(U32.is_eq(a6, a6), True{}, E.U32.is_eq_refl(a6)) : {Bool.and(True{}, Bool.and(True{},
        Bool.and(True{}, Bool.and(True{},
          Bool.and(True{}, Bool.and(True{},
            Bool.and(_, U32.is_eq(a7, a7))))))))
        == True{} : Bool}
      %E.Bool.sym(U32.is_eq(a7, a7), True{}, E.U32.is_eq_refl(a7)) : {Bool.and(True{}, Bool.and(True{},
        Bool.and(True{}, Bool.and(True{},
          Bool.and(True{}, Bool.and(True{},
            Bool.and(True{}, _)))))))
        == True{} : Bool}
      {==}

# ---------------------------------------------------------------------------
# The slot just written is the slot found.
# ---------------------------------------------------------------------------

law Slot.find_written:
  for +o: O.Oid
  for +ord: U32
  for +rest: List<&2, I.Slot>
  {I.Slot.find(Con{I.Slot{o, ord}, rest}, o, None{})
    == Some{ord} : Maybe<&2, U32>}

law Slot.find_found:
  for +rest: List<&2, I.Slot>
  for +o: O.Oid
  for +ord: U32
  {I.Slot.find(rest, o, Some{ord}) == Some{ord} : Maybe<&2, U32>}

def Slot.find_found(rest, o, ord):
  match rest:
    case Nil{}:
      {==}
    case Con{s, t}:
      {==}

# ---------------------------------------------------------------------------
# And the bucket it was written into is the bucket that is read.
# ---------------------------------------------------------------------------

def Slot.find_written(o, ord, rest):
  %E.Bool.sym(O.Oid.eq(o, o), True{}, Oid.eq_refl(o))
    : {I.Slot.find(rest, o, I.Slot.match_one.pick(ord, _))
      == Some{ord} : Maybe<&2, U32>}
  Slot.find_found(rest, o, ord)

law Uni.find_after_insert:
  for +t: T.Trie<I.Bucket()>
  for +o: O.Oid
  for +ord: U32
  {I.Uni.find(T.Trie.set(I.Bucket(), 20n, t, I.Uni.slot_key(o),
      Con{I.Slot{o, ord}, I.Uni.bucket(t, I.Uni.slot_key(o))}), o)
    == Some{ord} : Maybe<&2, U32>}

def Uni.find_after_insert(t, o, ord):
  %E.Maybe.sym(I.Bucket(),
    T.Trie.at(I.Bucket(), 20n,
      T.Trie.set(I.Bucket(), 20n, t, I.Uni.slot_key(o),
        Con{I.Slot{o, ord}, I.Uni.bucket(t, I.Uni.slot_key(o))}),
      I.Uni.slot_key(o)),
    Some{Con{I.Slot{o, ord}, I.Uni.bucket(t, I.Uni.slot_key(o))}},
    Tr.Trie.at_set(I.Bucket(), 20n, t, I.Uni.slot_key(o),
      Con{I.Slot{o, ord}, I.Uni.bucket(t, I.Uni.slot_key(o))}))
    : {I.Slot.find(I.Uni.bucket.un(_), o, None{})
      == Some{ord} : Maybe<&2, U32>}
  Slot.find_written(o, ord, I.Uni.bucket(t, I.Uni.slot_key(o)))

# ---------------------------------------------------------------------------
# The round trip, at `Uni.intern` itself.
#
# Both branches: if the id was already known the table does not change and the
# ordinal handed back is the one the lookup found; if it was not, the write
# above makes the next lookup find the ordinal just assigned. The lookup that
# decided the branch is carried as a parameter with an equation naming it,
# because the decision has to stay tied to `t` across the match.
# ---------------------------------------------------------------------------

law Uni.intern_go_round_trip:
  for +f: O.Fmt
  for +next: U32
  for +t: T.Trie<I.Bucket()>
  for +oids: List<&2, O.Oid>
  for +o: O.Oid
  for +found: Maybe<&2, U32>
  for +ok: {I.Uni.find(t, o) == found : Maybe<&2, U32>}
  {I.Uni.find(
      I.Uni.table(I.Interned.uni(I.Uni.intern.go(f, next, t, oids, o, found))),
      o)
    == Some{I.Interned.ord(I.Uni.intern.go(f, next, t, oids, o, found))}
    : Maybe<&2, U32>}

def Uni.intern_go_round_trip(f, next, t, oids, o, found, ok):
  match found:
    case Some{k}:
      ok
    case None{}:
      Uni.find_after_insert(t, o, next)

law Uni.intern_round_trip:
  for +u: I.Universe
  for +o: O.Oid
  {I.Uni.find(I.Uni.table(I.Interned.uni(I.Uni.intern(u, o))), o)
    == Some{I.Interned.ord(I.Uni.intern(u, o))} : Maybe<&2, U32>}

def Uni.intern_round_trip(u, o):
  match u:
    case I.Uni{f, next, table, oids}:
      Uni.intern_go_round_trip(f, next, table, oids, o,
        I.Uni.find(table, o), {==})

# ---------------------------------------------------------------------------
# A universe built the way the importer builds one: from nothing, interning
# one id at a time. Proof-only -- the importer threads a universe through the
# fetch loop rather than folding a finished list -- but it is the shape the
# open half of U-01 is stated over, because injectivity is a property of a
# table that was *built* by interning and not of an arbitrary table.
# ---------------------------------------------------------------------------

def Uni.of_list(f: O.Fmt, os: List<&2, O.Oid>) -> I.Universe:
  match os:
    case Nil{}:
      I.Uni.new(f)
    case Con{o, rest}:
      I.Interned.uni(I.Uni.intern(Uni.of_list(f, rest), o))
