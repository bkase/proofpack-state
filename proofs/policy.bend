# proofs/policy.bend -- the tree-data policy, at the row (law G-02).
#
# SPEC 8.2's table says `tree-data` follows tag -> target, commit -> root
# tree, tree -> subtree and tree -> blob, but not commit -> parent. The
# importer implements that by keeping the full successor rows and, for a row
# belonging to a commit, dropping the successors that are themselves commits
# -- no edge labels, only the object types it already recorded.
#
# The claim proved here is that this drops exactly the commit -> commit
# edges: a successor survives the filter precisely when it was in the full row
# and is not itself a commit. It holds for an arbitrary row and an arbitrary
# metadata table, with no hypothesis about either.
#
# The one step that is not Boolean algebra is this. `List.contains` decides
# membership with `U32.is_eq`, while the filter consults the metadata of each
# element. When `U32.is_eq(w, v)` says yes, the proof needs `w` and `v` to
# have the *same* metadata -- which follows from `w == v` and not from a
# Boolean test agreeing. So it goes through the reflection lemma of
# proofs/eq.bend.

import Base
import ./eq.bend as E
import ../core/trie.bend as T
import ../adapters/git/import.bend as Im
import ../index/source.bend as Sc

# The kind of `v`, as the filter reads it.
def Policy.commit_at(+mt: T.Trie<Im.Meta>, +v: U32) -> Bool:
  Sc.Idx.is_commit(Sc.Source.meta_of.un(T.Trie.at(Im.Meta, 32n, mt, v)))

def Policy.has(row: List<&2, U32>, +v: U32) -> Bool:
  List.contains(~U32, ~U32.is_eq, row, v)

# ---------------------------------------------------------------------------
# Boolean lemmas.
# ---------------------------------------------------------------------------

law Bool.and_false_r:
  for b: Bool
  {Bool.and(b, False{}) == False{} : Bool}

def Bool.and_false_r(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law Bool.and_or_r:
  for a: Bool
  for b: Bool
  for c: Bool
  {Bool.or(Bool.and(a, c), Bool.and(b, c))
    == Bool.and(Bool.or(a, b), c) : Bool}

def Bool.and_or_r(a, b, c):
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
# One row element, with the two decisions taken as parameters.
#
# Bend matches parameters rather than computed values, so "is the target a
# commit" (`cw`) and "is the target the ordinal being tested for" (`a`) come
# in as Booleans carrying the equations that name them. With both concrete,
# three of the four arms are Boolean algebra over the induction hypothesis.
# The fourth is the one with content: `a` says `w` is the ordinal tested for,
# so `w == v`, so the two metadata lookups are the same lookup.
# ---------------------------------------------------------------------------

law Policy.step.arm:
  for +mt: T.Trie<Im.Meta>
  for +w: U32
  for +t: List<&2, U32>
  for +v: U32
  for +cw: Bool
  for +a: Bool
  for +ecw: {cw == Policy.commit_at(mt, w) : Bool}
  for +ea: {a == U32.is_eq(w, v) : Bool}
  for +ih: {Bool.and(Policy.has(t, v), Bool.not(Policy.commit_at(mt, v)))
    == Policy.has(Sc.Idx.filter_succ(mt, t), v) : Bool}
  {Policy.has(Sc.Idx.keep.pick(w, cw, Sc.Idx.filter_succ(mt, t)), v)
    == Bool.and(Bool.or(U32.is_eq(w, v), Policy.has(t, v)),
         Bool.not(Policy.commit_at(mt, v))) : Bool}

def Policy.step.arm(mt, w, t, v, cw, a, ecw, ea, ih):
  match cw:
    case True{}:
      match a:
        case False{}:
          # Dropped, and not the ordinal tested for: both sides are the
          # filtered tail, which the induction hypothesis describes.
          %ea : {Policy.has(Sc.Idx.filter_succ(mt, t), v)
            == Bool.and(Bool.or(_, Policy.has(t, v)),
                 Bool.not(Policy.commit_at(mt, v))) : Bool}
          %ih : {_ == Bool.and(Bool.or(False{}, Policy.has(t, v)),
                   Bool.not(Policy.commit_at(mt, v))) : Bool}
          {==}
        case True{}:
          # Dropped, and `w` is the ordinal tested for -- so `v` is that same
          # commit, and nothing survives on either side.
          %ea : {Policy.has(Sc.Idx.filter_succ(mt, t), v)
            == Bool.and(Bool.or(_, Policy.has(t, v)),
                 Bool.not(Policy.commit_at(mt, v))) : Bool}
          %ih : {_ == Bool.and(Bool.or(True{}, Policy.has(t, v)),
                   Bool.not(Policy.commit_at(mt, v))) : Bool}
          %E.U32.eq_reflect(w, v, E.Bool.sym(True{}, U32.is_eq(w, v), ea))
            : {Bool.and(Policy.has(t, v),
                Bool.not(Policy.commit_at(mt, _)))
              == Bool.and(Bool.or(True{}, Policy.has(t, v)),
                   Bool.not(Policy.commit_at(mt, _))) : Bool}
          %ecw : {Bool.and(Policy.has(t, v), Bool.not(_))
            == Bool.and(Bool.or(True{}, Policy.has(t, v)),
                 Bool.not(_)) : Bool}
          Bool.and_false_r(Policy.has(t, v))
    case False{}:
      match a:
        case False{}:
          # Kept, and not the ordinal tested for.
          %ea : {Bool.or(_, Policy.has(Sc.Idx.filter_succ(mt, t), v))
            == Bool.and(Bool.or(_, Policy.has(t, v)),
                 Bool.not(Policy.commit_at(mt, v))) : Bool}
          %ih : {Bool.or(False{}, _)
            == Bool.and(Bool.or(False{}, Policy.has(t, v)),
                 Bool.not(Policy.commit_at(mt, v))) : Bool}
          {==}
        case True{}:
          # Kept, and `w` is the ordinal tested for -- so `v` is not a commit
          # either, and the test survives on both sides.
          %ea : {Bool.or(_, Policy.has(Sc.Idx.filter_succ(mt, t), v))
            == Bool.and(Bool.or(_, Policy.has(t, v)),
                 Bool.not(Policy.commit_at(mt, v))) : Bool}
          %ih : {Bool.or(True{}, _)
            == Bool.and(Bool.or(True{}, Policy.has(t, v)),
                 Bool.not(Policy.commit_at(mt, v))) : Bool}
          %E.U32.eq_reflect(w, v, E.Bool.sym(True{}, U32.is_eq(w, v), ea))
            : {Bool.or(True{}, Bool.and(Policy.has(t, v),
                Bool.not(Policy.commit_at(mt, _))))
              == Bool.and(Bool.or(True{}, Policy.has(t, v)),
                   Bool.not(Policy.commit_at(mt, _))) : Bool}
          %ecw : {Bool.or(True{}, Bool.and(Policy.has(t, v),
              Bool.not(_)))
            == Bool.and(Bool.or(True{}, Policy.has(t, v)),
                 Bool.not(_)) : Bool}
          {==}

# ---------------------------------------------------------------------------
# The row.
# ---------------------------------------------------------------------------

law Policy.filter_drops_commits:
  for +mt: T.Trie<Im.Meta>
  for +row: List<&2, U32>
  for +v: U32
  {Bool.and(Policy.has(row, v), Bool.not(Policy.commit_at(mt, v)))
    == Policy.has(Sc.Idx.filter_succ(mt, row), v) : Bool}

def Policy.filter_drops_commits(mt, row, v):
  match row:
    case Nil{}:
      {==}
    case Con{w, t}:
      E.Bool.sym(
        Policy.has(Sc.Idx.keep.pick(w, Policy.commit_at(mt, w),
          Sc.Idx.filter_succ(mt, t)), v),
        Bool.and(Bool.or(U32.is_eq(w, v), Policy.has(t, v)),
          Bool.not(Policy.commit_at(mt, v))),
        Policy.step.arm(mt, w, t, v, Policy.commit_at(mt, w),
          U32.is_eq(w, v), {==}, {==},
          Policy.filter_drops_commits(mt, t, v)))
