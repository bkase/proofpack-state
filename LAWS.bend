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
