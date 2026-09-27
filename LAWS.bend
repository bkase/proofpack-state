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
import ./proofs/split.bend as Sp
import ./proofs/adder.bend as Ad
import ./proofs/enum.bend as En
import ./proofs/collapse.bend as Co
import ./closure/graph.bend as Gr
import ./closure/reach.bend as Re
import ./closure/explain.bend as Ex
import ./core/trie.bend as Tr
import ./adapters/git/import.bend as Im
import ./index/source.bend as Sc
import ./core/word.bend as W
import ./core/words.bend as Wo
import ./core/set.bend as S
import ./query/ast.bend as A
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
