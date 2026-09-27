# LAWS.bend -- the public claims of ProofPack State.
#
# These are the guarantees this release actually makes, stated over the
# production definitions that the shipped binary runs. `PROOF.bend` discharges
# every one of them; `bend PROOF.bend` fails while any is open or false, and
# `tools/gate.sh` is what CI runs.
#
# Read this file as the contract. Three things about how it is written:
#
#   * Laws are **pointwise**. A set is correct when every position of the
#     result is the Boolean of the same positions of the operands. SPEC 3.1
#     prefers that to assuming function extensionality, and it is also what
#     makes the laws hold for operands of different lengths with no bounds
#     hypothesis anywhere.
#
#   * Laws are stated over the **production** symbol, not a model of it.
#     `U32.popcount` here is the 32-step native loop the hot path runs, and
#     `Words.diff_count` is the fused kernel a matrix cell uses. Where a
#     specification twin exists (`U32.bit`, `Words.count`), the law is the
#     bridge between the two, not a claim about the twin alone.
#
#   * What is **not** here matters. `LAWS.pending.bend` states, in the same
#     syntax and with the same precision, the obligations this release
#     specifies but has not proved -- the closure algebra, the persistent-set
#     refinement, the compiler contract. Those are backed at run time instead,
#     by the closure certificate of SPEC 4.4 (`pp git verify`) and by
#     differential tests against the specification evaluator. `law-registry.json`
#     records which is which, per obligation, and `TRUST.md` says what is
#     trusted outright.
#
# Nothing here says a result is "mathematically verified" because the binary
# ships with proofs. These laws constrain the algebra. They say nothing about
# whether an imported graph matches a real repository, whether a receiver
# really holds what it reported, or whether the compiler lowered any of it
# correctly.

import Base
import ./core/count.bend as C
import ./core/ords.bend as Or
import ./proofs/descend.bend as Dc
import ./proofs/shape.bend as Sh
import ./proofs/split.bend as Sp
import ./proofs/order.bend as Or2
import ./proofs/adder.bend as Ad
import ./proofs/enum.bend as En
import ./proofs/collapse.bend as Co
import ./closure/graph.bend as Gr
import ./spec/closure.bend as Sp2
import ./closure/reach.bend as Re
import ./closure/cert.bend as Ct
import ./closure/explain.bend as Ex
import ./core/trie.bend as Tr
import ./adapters/git/import.bend as Im
import ./adapters/git/intern.bend as Ui
import ./adapters/git/oid.bend as Od
import ./index/source.bend as Sc
import ./core/word.bend as W
import ./core/words.bend as Wo
import ./core/set.bend as S
import ./query/ast.bend as A
import ./query/rewrite.bend as Rw
import ./spec/query.bend as Q
import ./proofs/denote.bend as Dn
import ./proofs/extensive.bend as Ex2
import ./proofs/table.bend as Tb
import ./proofs/insert.bend as In
import ./adapters/git/inventory.bend as Iv
import ./adapters/git/intern.bend as Ui2
import ./proofs/missing.bend as M

# ===========================================================================
# B-01 -- the word kernel.
#
# `U32` is declared in Base as a 32-bit vector and lowered by the compiler to
# a machine word. These laws are stated against the bit vector and run as
# single instructions.
# ===========================================================================

# Difference is one law rather than `and` composed with `not`, because `not`
# alone is wrong past the end of a word: an out-of-range read is absent, and
# the negation of absent is present. Intersecting with a real operand is what
# kills that, so the two must be stated together.
law word_difference_is_pointwise:
  for a: U32
  for b: U32
  for i: Nat
  {W.U32.bit(W.U32.diff(a, b), i)
    == Bool.and(W.U32.bit(a, i), Bool.not(W.U32.bit(b, i))) : Bool}

law word_intersection_is_pointwise:
  for a: U32
  for b: U32
  for i: Nat
  {W.U32.bit(U32.and(a, b), i)
    == Bool.and(W.U32.bit(a, i), W.U32.bit(b, i)) : Bool}

law word_union_is_pointwise:
  for a: U32
  for b: U32
  for i: Nat
  {W.U32.bit(U32.or(a, b), i)
    == Bool.or(W.U32.bit(a, i), W.U32.bit(b, i)) : Bool}

law shifting_right_reads_the_next_bit_up:
  for a: U32
  for i: Nat
  {W.U32.bit(U32.shr(a), i) == W.U32.bit(a, 1n+i) : Bool}

# SPEC 5.5: a newly discovered object must not appear in yesterday's
# inventory because unused bitmap capacity happened to contain ones. This is
# the mask that enforces it -- bit i of `mask(k)` is set exactly when i is
# both inside the word and below k.
law the_tail_mask_hides_every_padding_bit:
  for k: Nat
  for i: Nat
  {W.U32.bit(W.U32.mask(k), i)
    == Bool.and(C.Nat.gt(32n, i), C.Nat.gt(k, i)) : Bool}

# The production popcount -- one shift per bit, three native instructions,
# no allocation -- counts exactly the bits `U32.bit` reports set.
law popcount_counts_the_bits_that_are_set:
  for +x: U32
  {W.U32.popcount(x) == W.U32.card(32n, x) : Nat}

# The hot path tests a bit by shifting it down and looking at the bottom.
# That is the same bit the laws above talk about.
law the_fast_bit_test_agrees_with_the_bit_vector:
  for +w: U32
  for +b: Nat
  {Wo.U32.test(w, b) == W.U32.bit(w, b) : Bool}

# ===========================================================================
# S-01, R-01 -- the tile kernel.
#
# A tile is a cons list of words and `Words.at(ws, i, k)` reads bit k of word
# i. A missing word reads as absent and a short operand is treated as
# zero-padded, so these hold for operands of any two lengths.
#
# Restriction to a word index is the partition law R-01 in its concrete form:
# because every law here is *at a position*, restricting an operation to a
# disjoint range of positions and reassembling gives the same answer -- which
# is what licenses CPU/Metal tiling.
# ===========================================================================

law tile_difference_is_pointwise:
  for a: List<&2, U32>
  for b: List<&2, U32>
  for i: Nat
  for +k: Nat
  {Wo.Words.at(Wo.Words.diff(a, b), i, k)
    == Bool.and(Wo.Words.at(a, i, k),
         Bool.not(Wo.Words.at(b, i, k))) : Bool}

law tile_intersection_is_pointwise:
  for a: List<&2, U32>
  for b: List<&2, U32>
  for i: Nat
  for +k: Nat
  {Wo.Words.at(Wo.Words.and(a, b), i, k)
    == Bool.and(Wo.Words.at(a, i, k), Wo.Words.at(b, i, k)) : Bool}

law tile_union_is_pointwise:
  for a: List<&2, U32>
  for b: List<&2, U32>
  for i: Nat
  for +k: Nat
  {Wo.Words.at(Wo.Words.or(a, b), i, k)
    == Bool.or(Wo.Words.at(a, i, k), Wo.Words.at(b, i, k)) : Bool}

# ===========================================================================
# Q-02 -- the fused reduction.
#
# SPEC 7.2: for a matrix cell, do not allocate `Missing = Required \ Have`
# merely to count it. This is the permission to do that: counting the
# difference as it goes gives the same number as building the difference and
# counting it.
# ===========================================================================

law counting_a_difference_needs_no_difference:
  for a: List<&2, U32>
  for b: List<&2, U32>
  {Wo.Words.diff_count(a, b)
    == Wo.Words.count(Wo.Words.diff(a, b)) : Nat}

# ===========================================================================
# R-02 -- statistics are a commutative monoid.
#
# Componentwise addition, with the zero statistic as its identity. Together
# these are what license a parallel reduction over disjoint ordinal ranges
# and a deterministic balanced fold: commutativity is why the order tiles
# come back in cannot change a byte total.
#
# For *overlapping* sets, adding statistics double-counts. SPEC 4.3 forbids
# caching `Stats(Union(a, b))` as `Stats(a) + Stats(b)` without proving
# disjointness, and no such rewrite exists in this code.
# ===========================================================================

law statistics_have_a_left_identity:
  for s: A.Stats
  {A.Stats.add(A.Stats.zero(), s) == s : A.Stats}

law statistics_have_a_right_identity:
  for +s: A.Stats
  {A.Stats.add(s, A.Stats.zero()) == s : A.Stats}

law statistics_add_commutatively:
  for +x: A.Stats
  for +y: A.Stats
  {A.Stats.add(x, y) == A.Stats.add(y, x) : A.Stats}

law statistics_add_associatively:
  for +x: A.Stats
  for +y: A.Stats
  for +z: A.Stats
  {A.Stats.add(A.Stats.add(x, y), z)
    == A.Stats.add(x, A.Stats.add(y, z)) : A.Stats}

# Whatever its type, one object adds one to the count -- so the type
# breakdown can never disagree with the total.
law every_object_counts_once:
  for +size: Nat
  for +kind: U32
  {A.Stats.count(A.Stats.of_kind(size, kind)) == 1n : Nat}

# ===========================================================================
# M-01, M-02, M-03, I-01 -- the least additional object set.
#
# SPEC 3.4, for roots R and *any* recorded inventory H, with K = C(R) and
# M = K \ H:
#
#     K is inside H u M,  and  for every candidate transfer set T,
#     K inside H u T  <=>  M inside T.
#
# So M is the unique least set that completes the requirement. The content is
# pointwise: it holds position by position, for whatever the three sets say
# at that position, with no induction and no structure. That is also exactly
# why H need not be graph-closed, which is what makes any of this usable
# against a partial cache.
#
# `Bool.imp` is implication and `Bool.sub` is difference, both at one
# position; `Words.at` and `PSet.mem` are what produce those Booleans.
# ===========================================================================

law the_missing_set_covers_the_requirement:
  for k: Bool
  for h: Bool
  {M.Bool.imp(k, Bool.or(h, M.Bool.sub(k, h))) == True{} : Bool}

law the_missing_set_is_the_least_one:
  for k: Bool
  for h: Bool
  for t: Bool
  {M.Bool.imp(k, Bool.or(h, t))
    == M.Bool.imp(M.Bool.sub(k, h), t) : Bool}

law readiness_is_an_empty_difference:
  for k: Bool
  for h: Bool
  {M.Bool.imp(k, h) == Bool.not(M.Bool.sub(k, h)) : Bool}

# Why two requirements can share one inventory scan.
law missing_distributes_over_a_union_of_requirements:
  for a: Bool
  for b: Bool
  for h: Bool
  {M.Bool.sub(Bool.or(a, b), h)
    == Bool.or(M.Bool.sub(a, h), M.Bool.sub(b, h)) : Bool}

# Why local, LAN and upstream inventories can be subtracted one after
# another. SPEC 4.2: this does *not* imply those tiers are authorized or
# reachable. That is a service contract, not an algebraic one.
law inventory_tiers_compose:
  for a: Bool
  for h1: Bool
  for h2: Bool
  {M.Bool.sub(a, Bool.or(h1, h2))
    == M.Bool.sub(M.Bool.sub(a, h1), h2) : Bool}

# An additions-only inventory update needs no re-derivation:
# M' = K \ (H u A) = (K \ H) \ A.
law an_additions_only_update_needs_no_rederivation:
  for k: Bool
  for h: Bool
  for a: Bool
  {M.Bool.sub(k, Bool.or(h, a))
    == M.Bool.sub(M.Bool.sub(k, h), a) : Bool}

# "Add wins" in SPEC 4.2's patch semantics, patch(H, D, A) = (H \ D) u A.
# That is all this says: two patches to the same inventory are *not*
# automatically commutative with each other, and SPEC 4.2 requires a
# restricted commuting-update law to be certified separately before such
# updates are parallelised. This release certifies none.
law add_wins_in_a_patch:
  for h: Bool
  for d: Bool
  for a: Bool
  {Bool.or(M.Bool.sub(h, d), a) == Bool.or(a, M.Bool.sub(h, d)) : Bool}

# ===========================================================================
# B-02 -- the checked accumulator.
#
# SPEC 5.4 proposed a checked pair-of-U32 for 64-bit counts and byte sums,
# proved against natural-number arithmetic with overflow detected rather than
# wrapped. This runtime's `Nat` already is one: a native unsigned integer
# whose adds are single instructions and which posts an error at 2^48-1
# instead of wrapping. Re-implementing limbs would add trusted code, not
# remove it, so `Nat` is the accumulator and these are its equations.
# ===========================================================================

law the_accumulator_has_an_identity:
  for +a: Nat
  {Nat.add(a, 0n) == a : Nat}

law the_accumulator_adds_commutatively:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

law the_accumulator_adds_associatively:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

# ===========================================================================
# G-02 -- the tree-data policy, at the row.
#
# SPEC 8.2: `tree-data` follows tag -> target, commit -> root tree, tree ->
# subtree and tree -> blob, but not commit -> parent. The importer implements
# that with no edge labels at all: it keeps the full successor rows, and for a
# row belonging to a commit it drops the successors that are themselves
# commits.
#
# This law says that filter drops *exactly* the commit targets and nothing
# else -- an ordinal survives precisely when it was in the row and is not a
# commit. It holds for any row and any metadata table, with no hypothesis.
#
# What it does not yet cover is stated in `LAWS.pending.bend`: lifting this
# from a row to `Graph.edge` over the two assembled tries needs the positional
# alignment of `Trie.of_list` with list position, which in turn needs
# bit-vector arithmetic for the trie descent. So this is the semantic content
# of G-02, proved, and the addressing around it is not.
#
# The one step here that is not Boolean algebra: `List.contains` decides
# membership with `U32.is_eq` while the filter reads each element's metadata,
# so the proof needs `U32.is_eq(w, v) == True{}` to give `w == v`. That is
# `word_equality_is_reflected` below, and it is why that law exists.
# ===========================================================================

law a_filtered_row_drops_exactly_the_commit_targets:
  for +mt: Tr.Trie<Im.Meta>
  for +row: List<&2, U32>
  for +v: U32
  {Bool.and(List.contains(~U32, ~U32.is_eq, row, v),
      Bool.not(Sc.Idx.is_commit(Sc.Source.meta_of.un(
        Tr.Trie.at(Im.Meta, 32n, mt, v)))))
    == List.contains(~U32, ~U32.is_eq,
         Sc.Idx.filter_succ(mt, row), v) : Bool}

# ===========================================================================
# Machine-word equality reflects.
#
# Every law above this point is pointwise over `Bool`, and none of them needs
# to know that two ordinals are *the same ordinal* -- which is the whole
# reason the set algebra could be proved without it. The Git adapter is where
# that stops being enough: a list membership test and a metadata lookup have
# to be talking about the same object.
#
# `U32.is_eq` is `Word.cmp` on the 32-bit vector, so this is an induction on
# the vector, and it is the bridge from a Boolean answer to an equality.
# ===========================================================================

law word_equality_is_reflected:
  for +a: U32
  for +b: U32
  for +ok: {U32.is_eq(a, b) == True{} : Bool}
  {a == b : U32}

# ===========================================================================
# P-01 -- inserting into a leaf.
#
# P-01 says a persistent update leaves the ordinal it inserted present. As it
# was first written in `LAWS.pending.bend` that claim was **false**, and the
# counterexample is small enough to run: a `PDense` leaf that is not 128 words
# wide silently loses the bit it was just given, because `Words.set` past the
# end of a tile changes nothing. `tests.bend` keeps that counterexample.
#
# So the law says which leaves it is about, and it says it in the form that
# carries the content: the leaf's tile has a word for the ordinal being
# inserted. That is implied by the structural invariant every stored set is
# checked against on load (`PSet.valid`, law D-01), and it is the only thing
# the proof needs.
#
# This is the leaf. The same claim at a node is still open, and for a reason
# that has nothing to do with insertion: a node's insert descends in exact
# lockstep with a node's membership, both taking the same branch from the same
# half-width, so the tree layer adds nothing but addressing -- and it is the
# addressing that is unproved. `LAWS.pending.bend` says which facts are
# missing.
# ===========================================================================

law inserting_into_a_leaf_keeps_that_ordinal:
  for +s: S.PSet
  for +x: U32
  for +fits: {Wo.Words.has_word(S.PSet.leaf_words(s),
    U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.add.leaf(s, x), x) == True{} : Bool}

# The sparse half of the same fact, which needs no hypothesis at all: a
# sparse leaf is an ascending offset list, and inserting into one leaves the
# ordinal in it, for any list of any length.
law inserting_into_an_ordinal_list_keeps_that_ordinal:
  for +xs: List<&2, U32>
  for +x: U32
  {Or.Ords.elem(Or.Ords.insert(xs, x), x) == True{} : Bool}

# The dense half, at the tile. The right-hand side is not a hypothesis in
# disguise -- it is the answer: setting a bit of a tile that has no such word
# changes nothing, and reading it back gives `False{}`.
law setting_a_bit_reads_it_back:
  for ws: List<&2, U32>
  for +x: U32
  {Wo.Words.bit(Wo.Words.set(ws, x), x)
    == Wo.Words.has_word(ws, U32.to_nat(U32.shrn(x, 5n))) : Bool}

# Why that law needs no side condition on the bit index: masking an ordinal
# with 31 always leaves a number below a word's width. `U32.shln(1, 32n)` is
# zero, so without this the tile laws would be false for a bit index of 32 or
# more.
law a_bit_index_is_below_the_word_width:
  for +x: U32
  {C.Nat.gt(32n, U32.to_nat(U32.and(x, 31))) == True{} : Bool}

# ===========================================================================
# E-01 -- what a dependency witness guarantees.
#
# SPEC 4.4 asks that a returned explanation begin at a requested root, end at
# the requested object, and take a real policy edge at every step.
# `pp git explain` checks all three on every witness it emits, and the check
# does not trust the producer -- a cached or heuristic witness is accepted on
# the same terms as a freshly walked one.
#
# Two of the three hold for a produced witness with no hypothesis at all, and
# they are the two below. Every step is a real edge because the predecessor
# search only ever returns a vertex it has just tested `Graph.edge` on; and
# the witness ends at the object asked about because the walk starts there and
# only ever prepends.
#
# The third -- that it *starts* at a root -- is not here, and the reason is
# worth stating: it depends on the levels being a genuine breadth-first
# layering from the roots, which is the traversal obligation C-02. A walk over
# levels that are not such a layering can stop early, and then its first
# vertex is not a root. That is exactly why the check tests all three, and why
# tests.bend keeps a witness that starts off-root and must be rejected.
# ===========================================================================

law every_step_of_a_produced_witness_is_an_edge:
  for +td: Nat
  for +g: Gr.Graph()
  for +rev: Re.Levels
  for +target: U32
  {Ex.Explain.steps_ok(td, g, Ex.Explain.path.go(td, g, rev, target),
    True{}) == True{} : Bool}

law a_produced_witness_ends_at_the_object_asked_about:
  for +td: Nat
  for +g: Gr.Graph()
  for +rev: Re.Levels
  for +target: U32
  for +p: Maybe<&2, U32>
  {Ex.Explain.last_is(
    Ex.Explain.walk(td, g, rev, target, Nil{}, p), target) == True{} : Bool}

# ===========================================================================
# S-02, in part -- the Zero/Full collapses.
#
# SPEC 5.3 lets a branch whose halves are both empty become `PZero{}`, and one
# whose halves are both full become `PFull{}`. That collapse is what makes
# structural pruning work: a difference against a pruned subtree costs nothing
# because the subtree is one node instead of a tree of them, and `PSet.mk`
# performs it on every union, intersection and difference at a node.
#
# This says the collapse changes no member, at every depth and for every
# ordinal, with no hypothesis at all -- not validity, not a range on the
# ordinal -- because it only ever fires when both halves already answer the
# same thing everywhere.
#
# It is the part of S-02 that the tree layer contributes by itself. The rest
# of S-02 is at the two ends: the leaf laws, and carrying an ordinal down one
# level, which is the addressing arithmetic `LAWS.pending.bend` lists.
# ===========================================================================

law collapsing_a_branch_keeps_its_members:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +h: U32
  for +x: U32
  {S.PSet.mem(1n+p, S.PSet.mk(lo, hi), h, x)
    == S.PSet.mem(1n+p, S.PBranch{lo, hi}, h, x) : Bool}

# ===========================================================================
# The addressing arithmetic: carrying an ordinal down a level.
#
# Every operation on the set tree splits an interval by comparing the ordinal
# with the half-width `h` and, in the upper half, rebasing by `x - h`. For a
# descent to preserve "this ordinal is inside this interval", `x - h` has to
# be subtraction and the result has to land inside the child. Until now that
# was assumed; `LAWS.pending.bend` listed it as the fact that several
# obligations were waiting on.
#
# It is provable without any arithmetic on `Nat`, because the half-width is
# never an arbitrary number: `PSet.half(d)` is `U32.shln(1, 11n+d)`, a single
# set bit. For a power of two the whole question is bitwise.
#
# `U32.hi_zero(x, k)` reads "x fits in k bits". The first law says that is
# exactly `x < 2^k`. The second says an ordinal that fits in k+1 bits but not
# in k -- so it is in the upper half -- fits in k once rebased. Together they
# are what a node needs to hand its child.
#
# `Word.sub` is `Word.adc` with the borrow flag set, and the second law's
# proof is that for a subtrahend with a single bit the carry is `True{}` at
# every position: each output bit is the input bit, except at `k`, where the
# set bit clears.
# ===========================================================================

law an_ordinal_is_below_a_power_of_two_exactly_when_it_fits_in_that_many_bits:
  for +x: U32
  for +k: Nat
  for +ok: {C.Nat.gt(32n, k) == True{} : Bool}
  {U32.is_lt(x, U32.shln(1, k)) == Dc.U32.hi_zero(x, k) : Bool}

law rebasing_into_the_upper_half_keeps_the_ordinal_in_range:
  for +x: U32
  for +k: Nat
  for +hi: {Dc.U32.hi_zero(x, 1n+k) == True{} : Bool}
  for +no: {Dc.U32.hi_zero(x, k) == False{} : Bool}
  {Dc.U32.hi_zero(U32.sub(x, U32.shln(1, k)), k) == True{} : Bool}

# And the half-width the child is given really is half: one shift right of a
# single set bit is the bit one position down.
law halving_a_half_width_moves_the_bit_down:
  for +k: Nat
  for +ok: {C.Nat.gt(32n, 1n+k) == True{} : Bool}
  {U32.shr(U32.shln(1, 1n+k)) == U32.shln(1, k) : U32}

# ===========================================================================
# P-01 -- inserting, at the depth the product runs at.
#
# The leaf case above is the interesting half of the work; this is the whole
# claim. `Idx.sd()` is 20, and a depth-20 tree covers 4096 * 2^20 = 2^32
# ordinals -- every `U32` -- so there is no range hypothesis left to state:
# every ordinal is inside the tree. What survives is the structural
# invariant, which is what `PSet.valid` says and what every stored generation
# is checked against on load (law D-01).
#
# The descent is where the addressing laws above are spent: `PSet.add` and
# `PSet.mem` take the same branch from the same half-width at every node, so
# the only thing that could go wrong is the rebasing, and the rebasing is
# proved.
#
# What P-01 also asks, and what is *not* here, is that every retained old root
# still denotes what it did. That was never going to be an equation: it is a
# statement about sharing, and Bend's affine values make it true by
# construction, since a persistent update copies the path it changes and
# cannot reach the nodes it did not copy.
# ===========================================================================

law inserting_adds_exactly_that_ordinal:
  for +s: S.PSet
  for +x: U32
  for +v: {S.PSet.valid(20n, s, True{}) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.insert(20n, s, x), x) == True{} : Bool}

# ===========================================================================
# The numeric reading of a word determines the word.
#
# `Words.bit(ws, x)` addresses a tile by two numbers, `x >> 5` and `x & 31`,
# both read through `U32.to_nat`. For a sparse leaf and the tile it spreads
# into to have the same members, that address has to be injective -- two
# different ordinals must not land on the same bit of the same word -- and
# the first half of that is this law.
#
# The head bit of a word is the parity of its value and the tail is the
# halved value, so an equality of numbers splits into an equality of bits and
# an equality of tails. What separates the two halves is the one fact this
# runtime's `Nat` does not ship: a doubled number is never one more than a
# doubled number.
#
# The second half -- reconstructing the ordinal from the two addresses -- is
# still open; `proofs/inject.bend` says exactly where it stops and why.
# ===========================================================================

law the_number_a_word_reads_as_determines_the_word:
  for +a: U32
  for +b: U32
  for +e: {U32.to_nat(a) == U32.to_nat(b) : Nat}
  {a == b : U32}

# ===========================================================================
# A3 -- the tile address is injective.
#
# `Words.bit(ws, x)` addresses a tile by two numbers: `x >> 5` picks the word
# and `x & 31` picks the bit. SPEC 5.2 calls the sparse/dense crossover a
# benchmark parameter rather than a semantic constant, and that is only true
# if a leaf's offset list and the tile it spreads into hold exactly the same
# ordinals -- which needs two different ordinals to land on two different
# bits.
#
# The way in is the identity every such split rests on: an ordinal is its word
# index scaled by 32 plus its bit index. With it, two ordinals with the same
# address have the same `U32.to_nat`, and
# `the_number_a_word_reads_as_determines_the_word` finishes. Nothing here
# reasons about bit positions under a quantifier, which is what made the
# direct route stall.
# ===========================================================================

law an_ordinal_is_its_word_index_scaled_plus_its_bit_index:
  for +x: U32
  {U32.to_nat(x)
    == Nat.add(Sp.Nat.dbl(5n, U32.to_nat(U32.shrn(x, 5n))),
         U32.to_nat(U32.and(x, 31))) : Nat}

law the_tile_address_is_injective:
  for +o: U32
  for +x: U32
  for +ei: {U32.to_nat(U32.shrn(o, 5n))
    == U32.to_nat(U32.shrn(x, 5n)) : Nat}
  for +eb: {U32.to_nat(U32.and(o, 31))
    == U32.to_nat(U32.and(x, 31)) : Nat}
  {o == x : U32}

# ===========================================================================
# S-03, at the representation -- a sparse leaf and its tile agree.
#
# This is what A3 was for. A sparse leaf is an ascending offset list; the same
# leaf as words is that list spread into 128 zero words. They hold the same
# ordinals: an offset in the list is a set bit, and a set bit is an offset in
# the list. The second direction is the one that needed A3 -- without it,
# "these two ordinals differ" says nothing about where in the tile they live.
#
# The hypothesis is the same one every leaf law carries: the tile has a word
# for the ordinal being asked about.
# ===========================================================================

law a_sparse_leaf_and_its_tile_hold_the_same_ordinals:
  for +offs: List<&2, U32>
  for +x: U32
  for +fits: {Wo.Words.has_word(Wo.Words.zeros(128n),
    U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}
  {Wo.Words.bit(S.PSet.spread(offs, Wo.Words.zeros(128n)), x)
    == Or.Ords.elem(offs, x) : Bool}

# ===========================================================================
# S-03, at the count -- what a bit count says about the bits.
#
# `PSet.compress` decides a leaf's representation from one number: how many
# bits are set. Zero means `PZero{}`, a full 4096 means `PFull{}`, few enough
# means a sparse offset list, and the rest stays dense. For that decision to
# preserve membership, the two extreme answers have to be justified by the
# count alone.
#
# The second is a pigeonhole: 128 words hold at most 32 bits each, so 4096 is
# only reachable when every word is full, and a word is full only when every
# one of its bits is set. `Nat.dbl(5n, n)` is 32n -- the capacity of an
# n-word tile.
# ===========================================================================

law a_tile_at_capacity_has_every_bit_set:
  for +ws: List<&2, U32>
  for +full: {Wo.Words.count(ws)
    == Sp.Nat.dbl(5n, List.length(&2, U32, ws)) : Nat}
  for +i: Nat
  for +iok: {C.Nat.gt(List.length(&2, U32, ws), i) == True{} : Bool}
  for +b: Nat
  for +bok: {C.Nat.gt(32n, b) == True{} : Bool}
  {Wo.Words.at(ws, i, b) == True{} : Bool}

law a_tile_counting_zero_has_no_bit_set:
  for +ws: List<&2, U32>
  for +z: {Wo.Words.count(ws) == 0n : Nat}
  for +i: Nat
  for +b: Nat
  for +bok: {C.Nat.gt(32n, b) == True{} : Bool}
  {Wo.Words.at(ws, i, b) == False{} : Bool}

# ===========================================================================
# What `U32` addition computes.
#
# `Words.members` walks a tile building ordinals by `ord + 1` within a word
# and `ord + 32` between words, and reading those ordinals back as tile
# addresses -- which is what S-03's sparse arm needs -- means knowing that
# `U32` addition is addition. That is a statement about the ripple adder
# `Word.adc`, not about anything in the set algebra, and it holds as long as
# neither operand needs the top bits: two values that fit in fewer than 32
# bits cannot carry out of the top.
#
# `Dc.U32.hi_zero(x, k)` reads "x fits in k bits".
# ===========================================================================

law adding_two_small_ordinals_adds_their_values:
  for +a: U32
  for +b: U32
  for +k: Nat
  for +za: {Dc.U32.hi_zero(a, k) == True{} : Bool}
  for +zb: {Dc.U32.hi_zero(b, k) == True{} : Bool}
  for +ok: {C.Nat.gt(32n, k) == True{} : Bool}
  {U32.to_nat(U32.add(a, b))
    == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

# ===========================================================================
# S-03, at the enumeration -- what the sparse list holds.
#
# The remaining arm of compression enumerates the tile: `Words.members` walks
# the words and, within each, the bits, consing an ordinal for each set bit.
# This law says the list it produces holds exactly what that walk holds --
# `Words.holds` is the same walk written as a predicate -- with no hypothesis
# at all. It covers the enumeration itself, the reversal at the end, and the
# accumulator threaded through both.
#
# What is left of S-03 after this, and it is the only thing left, is that the
# walk and the tile address name the same positions:
# `Words.holds(ws, 0, x) == Words.bit(ws, x)`. That is an addressing claim,
# stated in `LAWS.pending.bend`, and the two facts it needs -- the division
# identity and what `U32` addition computes -- are both proved above.
# ===========================================================================

law enumerating_a_tile_lists_what_the_walk_holds:
  for +ws: List<&2, U32>
  for +x: U32
  {Or.Ords.elem(Wo.Words.members(ws, 0), x)
    == En.Words.holds(ws, 0, x) : Bool}

# ===========================================================================
# S-03, at the count -- the two arms compression decides by counting.
# ===========================================================================

law a_tile_compression_calls_empty_has_no_members:
  for +ws: List<&2, U32>
  for +x: U32
  for +z: {Wo.Words.count(ws) == 0n : Nat}
  {Wo.Words.bit(ws, x) == False{} : Bool}

law a_tile_compression_calls_full_has_every_member:
  for +ws: List<&2, U32>
  for +x: U32
  for +wide: {List.length(&2, U32, ws) == 128n : Nat}
  for +full: {Wo.Words.count(ws) == 4096n : Nat}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {Wo.Words.bit(ws, x) == True{} : Bool}

# ===========================================================================
# S-02, at the representation -- a valid leaf and its tile agree.
#
# Every leaf operation converts to words, works there, and compresses back.
# For that to be sound the conversion has to be faithful, and this says it is:
# `PSet.leaf_words` produces a tile with exactly the leaf's members, for each
# of the four shapes a structurally valid leaf can take.
#
# The sparse case is the one that needed A3. The `PFull{}` case is the one the
# hypothesis is for: a leaf covers 4096 ordinals, and `PFull{}` means *those*
# 4096 rather than "everything", which is exactly what the counterexample in
# tests.bend shows. `Dc.U32.hi_zero(x, 12n)` reads "x fits in 12 bits", which
# is the leaf's extent.
#
# With this and the tile laws, a leaf operation is pointwise as soon as
# compression is -- which is S-03, and S-03 is now down to one addressing
# claim.
# ===========================================================================

law a_valid_leaf_and_its_tile_hold_the_same_ordinals:
  for +s: S.PSet
  for +x: U32
  for +v: {S.PSet.valid.leaf(s) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {S.PSet.mem.leaf(s, x)
    == Wo.Words.bit(S.PSet.leaf_words(s), x) : Bool}

# ===========================================================================
# D-01, in part -- what structural validity rules out.
#
# Above the leaf level the node operations read a sparse or dense payload as
# empty, while `PSet.mem` reads it as a member. That is the whole reason the
# pointwise laws carry a validity hypothesis, and `tests.bend` runs the
# counterexample.
#
# This says what `PSet.valid` actually excludes: at any depth above a leaf, a
# valid set is `PZero{}`, `PFull{}` or a branch -- never a payload. It is why
# a decoded generation is checked structurally on load rather than trusted
# (SPEC 6.5, which also says plainly that a checksum is not a substitute).
# ===========================================================================

law a_valid_set_has_no_payload_above_a_leaf:
  for +p: Nat
  for +s: S.PSet
  for +ok: {S.PSet.valid(1n+p, s, True{}) == True{} : Bool}
  {Co.PSet.is_node(s) == True{} : Bool}

# ===========================================================================
# S-03, discharged.
#
# SPEC 5.2 calls the sparse/dense crossover a benchmark parameter rather than
# a semantic constant, and this is what makes that true: compression changes
# no member, whichever of the four representations it picks.
#
# The two hypotheses are the ones the counterexamples in `tests.bend` need. A
# tile that is not 128 words wide is not a leaf, and an ordinal past 4096 is
# not one this leaf covers -- `PFull{}` means *these* 4096.
#
# The four arms: zero bits means `PZero{}` and no member, by counting; a full
# 4096 means `PFull{}` and every member, by the pigeonhole; the dense arm is
# the identity; and the sparse arm enumerates, which lists what the walk
# holds, which is what the address holds.
# ===========================================================================

law compressing_a_leaf_keeps_its_members:
  for +ws: List<&2, U32>
  for +x: U32
  for +wide: {Nat.is_eq(List.length(&2, U32, ws), 128n) == True{} : Bool}
  for +inr: {U32.is_lt(x, 4096) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.compress(ws), x)
    == Wo.Words.bit(ws, x) : Bool}

# And the addressing claim it rested on, which is now proved: the walk that
# enumerates a tile and the address that indexes it name the same positions.

law the_walk_agrees_with_the_tile_address:
  for +ws: List<&2, U32>
  for +x: U32
  for +wide: {List.length(&2, U32, ws) == 128n : Nat}
  {En.Words.holds(ws, 0, x) == Wo.Words.bit(ws, x) : Bool}

# ===========================================================================
# S-02, at the leaf -- the leaf operations are pointwise.
#
# A leaf operation converts both operands to words, works there, and
# compresses the result back. All three steps are proved above: conversion is
# faithful, the tile kernel is pointwise (law S-01), and compression changes
# no member (law S-03). These put them together.
#
# The hypotheses are the ones the counterexamples in `tests.bend` need: both
# operands are structurally valid leaves, and the ordinal is one the leaf
# covers.
# ===========================================================================

law the_leaf_difference_is_pointwise:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.diff.leaf(a, b), x)
    == Bool.and(S.PSet.mem.leaf(a, x),
         Bool.not(S.PSet.mem.leaf(b, x))) : Bool}

law the_leaf_union_is_pointwise:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.union.leaf(a, b), x)
    == Bool.or(S.PSet.mem.leaf(a, x), S.PSet.mem.leaf(b, x)) : Bool}

law the_leaf_intersection_is_pointwise:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.inter.leaf(a, b), x)
    == Bool.and(S.PSet.mem.leaf(a, x), S.PSet.mem.leaf(b, x)) : Bool}

# ===========================================================================
# S-02 -- set difference is pointwise.
#
# The one the product's central question is made of: `Missing = Required \
# Have`. Everything it needs is proved above -- the tile kernel is pointwise,
# a valid leaf agrees with its tile, compression changes no member, the
# Zero/Full collapses preserve membership, and the descent carries an ordinal
# into a child correctly -- and this is the induction that runs them down the
# tree.
#
# Stated at the depth the product runs at. `Idx.sd()` is 20, and a depth-20
# tree covers 4096 * 2^20 = 2^32 ordinals, so every `U32` is in range and no
# hypothesis about the ordinal survives. What remains is the structural
# invariant, which every stored generation is checked against on load.
# ===========================================================================

law set_difference_is_pointwise:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid(20n, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(20n, b, True{}) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.diff(20n, a, b), x)
    == Bool.and(S.PSet.member(20n, a, x),
         Bool.not(S.PSet.member(20n, b, x))) : Bool}

law set_union_is_pointwise:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid(20n, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(20n, b, True{}) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.union(20n, a, b), x)
    == Bool.or(S.PSet.member(20n, a, x),
         S.PSet.member(20n, b, x)) : Bool}

law set_intersection_is_pointwise:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid(20n, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(20n, b, True{}) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.inter(20n, a, b), x)
    == Bool.and(S.PSet.member(20n, a, x),
         S.PSet.member(20n, b, x)) : Bool}

# ===========================================================================
# S-04 -- the admitted Boolean rewrites.
#
# `query/rewrite.bend` rewrites `A u Empty` to `A`, `A n Empty` to `Empty` and
# `A \ Empty` to `A`, on the strength of `PSet.empty_p`'s answer. That test is
# the early exit SPEC 4.3 asks for -- it stops at the first word with a bit in
# it rather than counting -- so what the rewrites rest on is that it only
# answers `True{}` for a set with no members. That is the first law here; the
# three rewrites are then instances of S-02 with an empty operand.
#
# What is deliberately *not* admitted is in `tests.bend`: closure does not
# distribute over intersection or difference, and the counterexamples of SPEC
# 4.1 run on every build so that adding such a rewrite fails it.
# ===========================================================================

law an_empty_set_has_no_members:
  for +d: Nat
  for +s: S.PSet
  for +h: U32
  for +x: U32
  for +z: {S.PSet.empty_p(d, s) == True{} : Bool}
  {S.PSet.mem(d, s, h, x) == False{} : Bool}

law union_with_an_empty_set_changes_nothing:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid(20n, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(20n, b, True{}) == True{} : Bool}
  for +z: {S.PSet.empty_p(20n, a) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.union(20n, a, b), x)
    == S.PSet.member(20n, b, x) : Bool}

law intersection_with_an_empty_set_is_empty:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid(20n, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(20n, b, True{}) == True{} : Bool}
  for +z: {S.PSet.empty_p(20n, a) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.inter(20n, a, b), x) == False{} : Bool}

law subtracting_an_empty_set_changes_nothing:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid(20n, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(20n, b, True{}) == True{} : Bool}
  for +z: {S.PSet.empty_p(20n, b) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.diff(20n, a, b), x)
    == S.PSet.member(20n, a, x) : Bool}

# ===========================================================================
# C-03, in part -- closing nothing gives nothing.
#
# SPEC 3.3 defines the closure as the least fixed point of `X |-> X u
# post(X)` started from the roots. Closing the empty set gives the empty set:
# there is no member to follow an edge from, so every round leaves it where
# it was. This is what licenses `query/rewrite.bend` to rewrite
# `Reach(Empty)` to `Empty` without traversing.
#
# The rest of C-03 -- extensivity, monotonicity, idempotence and union
# preservation -- is still open, and `LAWS.pending.bend` says what it needs:
# the subset test related to membership, which needs the set-level fused
# count.
# ===========================================================================

law closing_nothing_gives_nothing:
  for +n: Nat
  for +td: Nat
  for +g: Gr.Graph()
  for +p: Nat
  {Sp2.Spec.closure(n, td, g, 1n+p, S.PZero{}) == S.PZero{} : S.PSet}

# ===========================================================================
# C-04, restated -- what an accepted certificate means.
#
# SPEC 4.4's certificate is four conditions, and `pp git verify` runs all four
# on every query. What this release cannot mechanise is their *meaning* --
# that conditions 1 and 2 put `Reach(R)` inside `C`, and condition 3's
# well-founded predecessor chains put `C` inside `Reach(R)`. That argument is
# written out in `closure/cert.bend` and in `TRUST.md`, and it stays argued;
# `LAWS.pending.bend` states it as the open claim.
#
# What is mechanised here is the other half, and it is the half a reader of
# `pp git verify`'s output actually needs: acceptance really does establish
# each of the four conditions, not some weaker conjunction. These four laws
# can be read instead of the checker.
# ===========================================================================

law an_accepted_certificate_contains_the_roots:
  for +td: Nat
  for +g: Gr.Graph()
  for +sd: Nat
  for +roots: List<&2, U32>
  for +levels: Re.Levels
  for +c: S.PSet
  for +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool}
  {S.PSet.is_subset(sd, S.PSet.from_list(sd, roots), c) == True{} : Bool}

law an_accepted_certificate_is_edge_closed:
  for +td: Nat
  for +g: Gr.Graph()
  for +sd: Nat
  for +roots: List<&2, U32>
  for +levels: Re.Levels
  for +c: S.PSet
  for +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool}
  {Sp2.Spec.closed(td, g, sd, c) == True{} : Bool}

law an_accepted_certificate_matches_its_levels:
  for +td: Nat
  for +g: Gr.Graph()
  for +sd: Nat
  for +roots: List<&2, U32>
  for +levels: Re.Levels
  for +c: S.PSet
  for +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool}
  {Ct.Cert.same(sd, S.PSet.from_list(sd,
    Ct.Cert.concat(levels, Nil{})), c) == True{} : Bool}

law an_accepted_certificate_has_layered_predecessors:
  for +td: Nat
  for +g: Gr.Graph()
  for +sd: Nat
  for +roots: List<&2, U32>
  for +levels: Re.Levels
  for +c: S.PSet
  for +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool}
  {Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
    Ct.Cert.first(levels, roots),
    S.PSet.is_subset(sd, S.PSet.from_list(sd,
      Ct.Cert.first(levels, roots)),
      S.PSet.from_list(sd, roots))) == True{} : Bool}

# ===========================================================================
# A1 -- machine-word comparison agrees with the numeric order.
#
# The last of the addressing facts. `U32.cmp` walks the bit vector comparing
# the high bits first with the low bit as the tiebreak; `Nat.cmp` walks two
# unary numbers. They agree, which is what lets a proof move between "this
# ordinal is smaller" and "this number is smaller".
#
# The power-of-two case was enough for the set tree's descent and was proved
# earlier; this is the general statement, and it is what the
# ascending-offsets invariant of a sparse leaf is stated with.
# ===========================================================================

law comparing_two_ordinals_compares_their_values:
  for +a: U32
  for +b: U32
  {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}

# ===========================================================================
# U-01 (round trip) -- interning an object id, then looking it up.
#
# The identity table is what makes `identify` a function at all: the first
# mention of an object id is given the next ordinal, every later mention has
# to answer the same one, and an object can be referenced long before it is
# fetched. If a second mention could get a second ordinal, two rows of the
# same generation would describe the same object and every count in the
# system would be wrong.
#
# This is the round-trip half of U-01, and it holds for any universe and any
# id, without a well-formedness hypothesis: whichever branch `intern` takes,
# looking the id up in the table it hands back finds the ordinal it handed
# back. The already-known branch does not touch the table; the fresh branch
# writes a slot, and the write is visible to the read because a trie reads
# back what was written and `Oid.eq` holds of an id and itself.
#
# The other half of U-01 -- that two *different* ids never share an ordinal
# -- is a statement about the whole table rather than about one write, and it
# is still open; it is stated in LAWS.pending.bend.
# ===========================================================================

law interning_an_id_then_finding_it_gives_the_same_ordinal:
  for +u: Ui.Universe
  for +o: Od.Oid
  {Ui.Uni.find(Ui.Uni.table(Ui.Interned.uni(Ui.Uni.intern(u, o))), o)
    == Some{Ui.Interned.ord(Ui.Uni.intern(u, o))} : Maybe<&2, U32>}

# ===========================================================================
# A trie reads back what was written.
#
# The identity table, the object store and the ordinal index are all this one
# structure: a path-compressed 32-ary trie keyed on a machine word. The law
# is the one thing a caller needs of it, and it needs no hypothesis -- `set`
# builds the path it descends and `get` takes the same branch from the same
# half-width, so a read at the key just written cannot miss.
# ===========================================================================

law reading_a_trie_at_the_key_just_written_gives_that_value:
  for -A: Data
  for +d: Nat
  for +t: Tr.Trie<A>
  for +x: U32
  for +v: A
  {Tr.Trie.at(A, d, Tr.Trie.set(A, d, t, x, v), x) == Some{v}
    : Maybe<&2, A>}

# ===========================================================================
# The shape the algebra needs, and that the operations keep.
#
# `PSet.valid` is the structural check a decoded generation has to pass
# before anything answers from it (SPEC 6.5), and it says three things: no
# sparse or dense payload above a leaf, a dense leaf exactly 128 words, and a
# sparse leaf's offsets ascending and in range. The pointwise laws above need
# the first two and never the third -- a sparse leaf is searched by
# `Ords.elem`, which reads the whole list, so the order of the offsets changes
# how fast a lookup is and not what it answers.
#
# `PSet.wf` (proofs/shape.bend) is the first two conditions alone. It is a
# proof-only predicate: nothing in the product computes it, `PSet.valid`
# remains the one thing checked on load, and the first law below is what ties
# them together. Everything the pointwise laws actually use is proved from
# `PSet.wf`, which is why they hold of more values than `PSet.valid` admits.
#
# The reason to separate them is the three laws after it. `PSet.wf` is
# preserved by union, intersection and difference; `PSet.valid` is not known
# to be, because a compressed sparse leaf's offsets come back from a tile walk
# whose ascending order this release has not proved. Preservation is what an
# induction over a query's syntax needs: to use a pointwise law at a node, the
# proof has to know the operands are still well shaped, and the operands are
# themselves results of operations. Without it such an induction stops at
# depth one.
# ===========================================================================

law every_structurally_valid_set_is_well_shaped:
  for +d: Nat
  for +s: S.PSet
  for +v: {S.PSet.valid(d, s, True{}) == True{} : Bool}
  {Sh.PSet.wf(d, s, True{}) == True{} : Bool}

law union_keeps_a_set_well_shaped:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {Sh.PSet.wf(d, a, True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(d, b, True{}) == True{} : Bool}
  {Sh.PSet.wf(d, S.PSet.union(d, a, b), True{}) == True{} : Bool}

law intersection_keeps_a_set_well_shaped:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {Sh.PSet.wf(d, a, True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(d, b, True{}) == True{} : Bool}
  {Sh.PSet.wf(d, S.PSet.inter(d, a, b), True{}) == True{} : Bool}

law difference_keeps_a_set_well_shaped:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {Sh.PSet.wf(d, a, True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(d, b, True{}) == True{} : Bool}
  {Sh.PSet.wf(d, S.PSet.diff(d, a, b), True{}) == True{} : Bool}

# ===========================================================================
# An empty set enumerates to nothing, and closing it gives nothing.
#
# `closing_nothing_gives_nothing` above is the equation at `PZero{}` itself.
# It is not enough for the optimizer, which decides with `PSet.empty_p` and so
# may be holding a set with no members that is not `PZero{}` -- a literal read
# from a store whose leaves are all empty, say. These are the versions that
# cover those.
#
# The first is the one that does the work: a set the emptiness test accepts
# walks to the empty list, not merely to a list with no members. Enumeration
# is where the algebra hands over to everything else -- the traversal takes
# the successors of a set by walking it to a list -- so this is what carries
# emptiness across that boundary. The dense case is the real content: a tile's
# members come back from a walk that shifts a word down thirty-two times and
# conses when the low bit is one, so "no bits set" has to be carried through
# the walk in the shape the walk has.
# ===========================================================================

law an_empty_set_enumerates_to_nothing:
  for +d: Nat
  for +s: S.PSet
  for +z: {S.PSet.empty_p(d, s) == True{} : Bool}
  {S.PSet.to_list(d, s) == Nil{} : List<&2, U32>}

law closing_a_set_with_no_members_gives_a_set_with_no_members:
  for +n: Nat
  for +td: Nat
  for +g: Gr.Graph()
  for +p: Nat
  for +r: S.PSet
  for +z: {S.PSet.empty_p(1n+p, r) == True{} : Bool}
  {S.PSet.empty_p(1n+p, Sp2.Spec.closure(n, td, g, 1n+p, r))
    == True{} : Bool}

# ===========================================================================
# Q-01 -- every admitted rewrite keeps the denotation.
#
# `query/rewrite.bend` simplifies an expression before it is compiled, and
# SPEC 3.5 admits a rewrite only if a law says the denotation is unchanged.
# These are those laws, one per rewrite the optimizer performs: the expression
# it produces has exactly the members the expression it replaced had, at the
# production depth, for every ordinal.
#
# The rewriter decides with `Rw.is_empty_expr`, which answers `True{}` only
# for `Empty` itself and for a literal whose set has no members. Each law is
# stated over that decision as the rewriter computes it, so there is no gap
# between the rewrite that is proved and the rewrite that runs.
#
# Validation is not part of this and does not need to be: a literal carries
# its set value, so an expression with an unresolved input cannot be built at
# all, and no rewrite can skip a check that has already happened. That is
# SPEC 3.5's "validation precedes elimination", structurally rather than as a
# proof obligation.
#
# The hypothesis is that the operands' denotations are well shaped, which is
# what the pointwise laws need; `every_denotation_is_well_shaped` below
# discharges it for any expression whose literals are.
#
# What is deliberately absent: the two closure rewrites SPEC 4.1 forbids --
# C(A n B) = C(A) n C(B) and C(A \ B) = C(A) \ C(B) -- and pushing a type
# filter through reachability. `tests/forbidden.bend` runs the
# counterexamples, so adding one later fails the build rather than quietly
# changing answers.
# ===========================================================================

law simplifying_a_union_keeps_every_member:
  for +src: Sc.Source
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +x: U32
  for +va: {Sh.PSet.wf(20n, Q.Den.eval(src, a), True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(20n, Q.Den.eval(src, b), True{}) == True{} : Bool}
  {S.PSet.member(20n, Q.Den.eval(src,
      Rw.Rw.union(a, b, Rw.Rw.is_empty_expr(a), Rw.Rw.is_empty_expr(b))), x)
    == S.PSet.member(20n, Q.Den.eval(src, A.EUnion{a, b}), x) : Bool}

law simplifying_an_intersection_keeps_every_member:
  for +src: Sc.Source
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +x: U32
  for +va: {Sh.PSet.wf(20n, Q.Den.eval(src, a), True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(20n, Q.Den.eval(src, b), True{}) == True{} : Bool}
  {S.PSet.member(20n, Q.Den.eval(src,
      Rw.Rw.inter(a, b, Rw.Rw.is_empty_expr(a), Rw.Rw.is_empty_expr(b))), x)
    == S.PSet.member(20n, Q.Den.eval(src, A.EInter{a, b}), x) : Bool}

law simplifying_a_difference_keeps_every_member:
  for +src: Sc.Source
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +x: U32
  for +va: {Sh.PSet.wf(20n, Q.Den.eval(src, a), True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(20n, Q.Den.eval(src, b), True{}) == True{} : Bool}
  {S.PSet.member(20n, Q.Den.eval(src,
      Rw.Rw.diff(a, b, Rw.Rw.is_empty_expr(a), Rw.Rw.is_empty_expr(b))), x)
    == S.PSet.member(20n, Q.Den.eval(src, A.EDiff{a, b}), x) : Bool}

law simplifying_a_reachability_keeps_every_member:
  for +src: Sc.Source
  for +p: Sc.Policy
  for +a: A.SetExpr
  for +x: U32
  {S.PSet.member(20n, Q.Den.eval(src,
      Rw.Rw.reach(p, a, Rw.Rw.is_empty_expr(a))), x)
    == S.PSet.member(20n, Q.Den.eval(src, A.EReach{p, a}), x) : Bool}

# ===========================================================================
# Every denotation is well shaped.
#
# The hypothesis the four laws above carry, discharged for any expression
# whose literals carry it. `SetExpr.wf_lits` is that condition -- `ELit` holds
# a set value outright, so an expression can name a badly shaped set the same
# way a decoded file can, and nothing but a check rules it out.
#
# Everything else is proved: `Empty`, `Full`, the three Boolean operations,
# reachability and filtering. Reachability is the interesting one -- the
# specification closure iterates `X |-> X u post(X)`, and `post` builds a set
# from a list of successors, so each round is a union of a well-shaped set
# with a set built by insertion.
# ===========================================================================

law every_denotation_is_well_shaped:
  for +src: Sc.Source
  for +e: A.SetExpr
  for +ok: {Dn.SetExpr.wf_lits(e) == True{} : Bool}
  {Sh.PSet.wf(20n, Q.Den.eval(src, e), True{}) == True{} : Bool}

# ===========================================================================
# C-03, in part -- the closure contains what it closes.
#
# SPEC 3.3's closure is extensive. The registry states that with
# `PSet.is_subset`, which is a count rather than a membership test, and
# relating a count to membership needs the set-level fused-count theorem this
# release has not written. Stated pointwise -- every member of the roots is a
# member of the closure -- it needs none of that, and it is the form every
# other set law here is stated in.
#
# One round plus induction on the fuel does it: a round is `X u post(X)`, and
# union is pointwise, so a member of `X` survives whatever `post` contributed.
#
# This is the half of extensivity that matters for the optimizer, which needs
# to know a closure never loses a root. The `is_subset` form, and the other
# three closure properties -- edge-closure, idempotence and union preservation
# -- are still open, and LAWS.pending.bend says why: all three are statements
# about the *fixed point* rather than about a round, so they need the argument
# that the iteration is stable after `n` rounds.
# ===========================================================================

law the_closure_contains_every_member_of_its_roots:
  for +n: Nat
  for +td: Nat
  for +g: Gr.Graph()
  for +r: S.PSet
  for +x: U32
  for +v: {Sh.PSet.wf(20n, r, True{}) == True{} : Bool}
  for +m: {S.PSet.member(20n, r, x) == True{} : Bool}
  {S.PSet.member(20n, Sp2.Spec.closure(n, td, g, 20n, r), x)
    == True{} : Bool}

# ===========================================================================
# What a table built from a list answers.
#
# Every per-object table in the index is a trie built in one pass from a list
# in ordinal order: adjacency under each policy, object metadata, the object
# ids. `Trie.build` splits the list in half at each level and `Trie.get`
# descends the same halves, so the answer at an ordinal is fixed by the list.
#
# `List.at_ord` is that same descent, performed on the list: it takes the same
# branch from the same half-width, by construction. Saying the answer is "the
# element at index `to_nat(x)`" instead would drag in the whole numeric
# reading of a machine word -- that the half-width is a power of two, that
# `U32.sub` is subtraction, that `take` and `drop` at `to_nat(h)` line up with
# the bit test -- and none of that is needed for what the tables are for,
# which is to be read at the same ordinal as each other.
# ===========================================================================

law a_table_built_from_a_list_answers_the_same_descent_over_the_list:
  for -A: Data
  for +d: Nat
  for +xs: List<&2, A>
  for +x: U32
  {Tr.Trie.at(A, d, Tr.Trie.of_list(A, d, xs), x)
    == Tb.List.at_ord(A, d, xs, Tr.Trie.half(d), x) : Maybe<&2, A>}

# ===========================================================================
# G-02 -- the tree-data policy, at an edge.
#
# `a_filtered_row_drops_exactly_the_commit_targets` above is the row-level
# half, and this is the lift the obligation asks for: the same statement about
# `Graph.edge` over the two assembled adjacency tables.
#
# The two expressions named here are exactly what `Idx.assemble.tries` stores
# in a built source as its `full` and `tree` graphs, and the metadata table it
# stores is the third. All three are `Trie.of_list` over lists that run in
# ordinal order and in step, so by the law above they descend together, and
# the question reduces to the three lists at a position -- where the row law
# applies.
#
# The hypothesis is that the metadata table describes `u`. It is not
# decorative: `Idx.tree_rows` stops at the shorter of rows and metadata, so an
# object with a successor row but no metadata entry would be absent from the
# tree-data table while still present in the full one, and the two policies
# would then disagree about an edge for a reason that has nothing to do with
# the policy. The importer rules that out -- it appends to both in the same
# step, and `Graph.domain_ok` is the check that says the graph describes every
# ordinal (SPEC 3.2) -- so the hypothesis holds of every source `pp` builds.
# ===========================================================================

law the_tree_data_policy_drops_exactly_the_parent_edges:
  for +rows: List<&2, Im.Row>
  for +metas: List<&2, Im.Meta>
  for +u: U32
  for +v: U32
  for +m: Im.Meta
  for +hm: {Tr.Trie.at(Im.Meta, 32n, Tr.Trie.of_list(Im.Meta, 32n, metas), u)
    == Some{m} : Maybe<&2, Im.Meta>}
  {Gr.Graph.edge(32n, Tr.Trie.of_list(Gr.Succ, 32n,
      Sc.Idx.tree_rows(Tr.Trie.of_list(Im.Meta, 32n, metas), rows, metas)),
      u, v)
    == Bool.and(
         Gr.Graph.edge(32n, Tr.Trie.of_list(Gr.Succ, 32n,
           Sc.Idx.full_rows(rows)), u, v),
         Bool.not(Bool.and(Sc.Idx.is_commit(m),
           Sc.Idx.is_commit(Sc.Source.meta_of.un(
             Tr.Trie.at(Im.Meta, 32n,
               Tr.Trie.of_list(Im.Meta, 32n, metas), v)))))) : Bool}

# ===========================================================================
# P-01, the other half -- inserting never loses a member.
#
# `inserting_adds_exactly_that_ordinal` says the ordinal just inserted is
# present. It does not say the ones already there still are, and nothing built
# out of repeated insertion can be reasoned about until it does: every set
# that enters the algebra from outside is a fold of `PSet.insert` over a list
# -- the universe of `Full`, a type filter's result, a receiver's inventory
# projected into the source universe -- and each step has to keep what the
# steps before it put in.
#
# The shape hypothesis is doing real work. Above a leaf `PSet.add` treats a
# sparse or dense payload as an empty subtree and replaces it with a fresh
# branch, while `PSet.mem` reads it as a set of members: for that one shape
# inserting really does lose members, and it is exactly the shape `PSet.wf`
# rules out. `every_structurally_valid_set_is_well_shaped` discharges the
# hypothesis for anything the store accepted.
#
# The second law is the two halves put together, at the fold.
# ===========================================================================

law inserting_keeps_every_member:
  for +s: S.PSet
  for +y: U32
  for +x: U32
  for +v: {Sh.PSet.wf(20n, s, True{}) == True{} : Bool}
  for +ok: {S.PSet.member(20n, s, x) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.insert(20n, s, y), x) == True{} : Bool}

law a_set_built_from_a_list_has_every_ordinal_on_it:
  for +xs: List<&2, U32>
  for +x: U32
  for +ok: {List.contains(~U32, ~U32.is_eq, xs, x) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.from_list(20n, xs), x) == True{} : Bool}

# ===========================================================================
# G-03, in part -- the inventory projection names what it was told.
#
# A receiver reports the object ids it holds. `Inv.project` turns that report
# into a set of source ordinals by looking each id up in the source
# universe's identity table: an id the source never named has no ordinal,
# which is what out-of-scope means and why it is counted and reported rather
# than discarded.
#
# This is the direction that decides whether an answer can be trusted: every
# id on the report that the universe names has its ordinal in the projection.
# Dropping one would make `pp` report an object as missing that the receiver
# actually has -- the failure that matters, because it is the one that causes
# an unnecessary transfer or a wrong readiness answer.
#
# Two things do it. `Oid.eq` decides equality of the complete digest, so an id
# that matches the one asked about *is* that id; no hash-collision assumption
# appears anywhere (SPEC 8.4). And insertion never loses a member, so an
# ordinal put in by one step survives every later step.
#
# The converse -- that the projection contains *nothing else* -- is still
# open, and LAWS.pending.bend says what it needs.
# ===========================================================================

law the_projection_contains_every_id_the_universe_names:
  for +u: Ui2.Universe
  for +oids: List<&2, Od.Oid>
  for +o: Od.Oid
  for +x: U32
  for +f: {Ui2.Uni.find(Ui2.Uni.table(u), o) == Some{x} : Maybe<&2, U32>}
  for +ok: {List.contains(~Od.Oid, ~Od.Oid.eq, oids, o) == True{} : Bool}
  {S.PSet.member(20n, Iv.Inventory.present(Iv.Inv.project(u, oids)), x)
    == True{} : Bool}
