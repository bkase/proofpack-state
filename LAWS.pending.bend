# LAWS.pending.bend -- specified, not proved.
#
# These are the obligations from `law-registry.json` that this release states
# but has **not** discharged as a law. Everything that was ever written here
# as a statement is now proved and lives in `LAWS.bend`: as of this release
# the file holds **no open law**, and `bend LAWS.pending.bend --check-only`
# reports no TODO. What is left is the record of how each one closed, and
# three obligations whose remaining halves are not statements about this tree
# -- D-01's text round trip, G-01's fidelity to Git's grammar, and Q-04's
# remaining half -- kept here as prose with what backs them instead.
#
# The file is still deliberately not imported by `PROOF.bend`, and the
# closure notes are kept rather than deleted: a record of what an obligation
# needed, and which hypothesis it gained on the way, is worth more than a
# clean file.
#
# What backs the prose-only obligations is recorded next to each, and in
# `TRUST.md`: mostly the closure certificate of SPEC 4.4, which `pp git
# verify` runs per query and which establishes *exactness* rather than an
# overapproximation, and the differential tests of SPEC 11.1.
#
# Closing one means moving it into `LAWS.bend` with a proof in `PROOF.bend`,
# and flipping its `status` in `law-registry.json`. Nothing here should be
# closed by weakening it: SPEC 10.3 forbids making a law vacuous by rejecting
# previously supported valid inputs. Two laws did gain a hypothesis on the way
# in -- U-01's no-wrap counter and E-01's reachable target -- and in both
# cases the statement was *false* without it, which is the one honest reason
# to add one; each is written out where it closed.

import Base
import ./core/count.bend as C
import ./core/set.bend as S
import ./core/words.bend as Wo
import ./proofs/enum.bend as En
import ./core/trie.bend as T
import ./closure/graph.bend as G
import ./closure/reach.bend as R
import ./closure/explain.bend as Ex
import ./spec/closure.bend as Sp
import ./query/ast.bend as A
import ./query/rewrite.bend as Rw
import ./spec/query.bend as Den
import ./index/source.bend as Idx
import ./closure/cert.bend as Ct
import ./query/eval.bend as Ev
import ./adapters/git/oid.bend as Od
import ./adapters/git/intern.bend as Ui
import ./proofs/intern.bend as PIn
import ./proofs/denote.bend as PDn

# ===========================================================================
# What the gaps had in common, and what closed them.
#
# Ten obligations were proved in part when this file was written. Their open
# halves routed through two pieces, and both closed first.
#
#   1. The converse of the subset bridge -- from "every member of a is a
#      member of b" back to `PSet.is_subset` -- is proved, as
#      `a_set_whose_members_are_all_in_another_is_a_subset`.
#
#      The obstruction was that the hypothesis quantifies over ordinals and
#      an ordinal-quantified hypothesis cannot be used twice under Bend's
#      affine discipline. It is used once, at one ordinal, and what produces
#      that ordinal is the counting work: the fused count is the length of
#      the fused list, so a count that is not zero means the list has a first
#      ordinal, and the fused walk is right about what it emits.
#
#      The hypothesis is data rather than a function -- every ordinal on a
#      list is a member of `b` -- which is the form a caller can build out of
#      laws, one ordinal at a time.
#
#   2. That a set's enumeration agrees with its membership is proved twice:
#      for a tree of the shape the enumeration names, and for any set that
#      passed `PSet.valid`, the check a decoded set is already put through.
#
# That turned out to be the whole technique, and it generalised: *every*
# obligation that closed after those two closed the same way, by replacing a
# quantified hypothesis with decidable data the induction may read as often
# as it likes -- `PSet.is_subset` and `PSet.same` for the closure and the
# rewrite pass, `Reach.settled` for the traversal, `Cert.levels_fit` for the
# certificate, `Ev.stack_ok` for the evaluator, `Uni.bounded` for interning,
# `Ex.ladder` for the witness. The affine discipline is not an obstacle to
# these proofs; it is a standing instruction to make the invariant checkable,
# which is also what makes it runnable.
#
# The one place that needed something else was the fixed point. Leastness is
# an induction over the rounds, but *reaching* the fixed point is a counting
# argument: a round that is not edge-closed exhibits a witness through the
# fused difference list and so is strictly bigger than the round before, and
# every set is inside a bounding set the graph respects, so only so many
# rounds can change. Making that bound the source rather than the depth is
# what makes the fuel hypothesis satisfiable -- 2^32 ordinals at production
# depth is not a number of rounds anyone can supply.
# ===========================================================================

# ===========================================================================
# The addressing arithmetic -- closed.
#
# Almost everything that was open in this file reduced to the same short list
# of facts about how a `U32` ordinal addresses the structures: none of them
# about sets, closure or queries, and all of them now proved and published in
# LAWS.bend. They are kept named here because the notes below refer to them.
#
#   A1  `U32.cmp` agrees with `Nat.cmp` on `U32.to_nat`
#       (`comparing_two_ordinals_compares_their_values`), with the
#       power-of-two case in the bitwise form the descent uses.
#   A2  rebasing into a node's upper half keeps the ordinal inside the child
#       (`rebasing_into_the_upper_half_keeps_the_ordinal_in_range`).
#   A3  the tile address is injective (`the_tile_address_is_injective`), by
#       the division identity rather than by word extensionality.
#   A4  a leaf ordinal's word index is inside a 128-word tile.
#   A5  the enumeration walk and the tile address name the same positions
#       (`the_walk_agrees_with_the_tile_address`).
#
# The counting argument is closed too: that finding 4096 set bits across 128
# words of at most 32 bits each means every bit is set is proved by
# pigeonhole in proofs/count.bend, which is what let S-03 close.
#
# So nothing below is waiting on arithmetic any more. What the remaining
# obligations are waiting on is stated under each of them, and it is mostly
# one of two things: an induction over a structure whose invariant quantifies
# over keys or positions (which Bend's affine values will not let an
# induction use twice unless the invariant is made decidable first), or a
# fixed-point argument about an iteration rather than about a value.
#
# ===========================================================================
# S-02, S-03 -- the persistent set, above the tile.
#
# The tile laws are proved (`tile_difference_is_pointwise` and friends in
# LAWS.bend). What is open is lifting them through the tree.
#
# These were first written without hypotheses, and in that form they were
# **false**. `tests.bend` runs the counterexamples:
#
#   * At a leaf, `PFull{}` means that leaf's own 4096 ordinals, but converting
#     it to words gives a tile that reads `False{}` past 4096. So
#     `diff(PFull, PDense{ones})` is empty while the pointwise right-hand side
#     is `True{}` at ordinal 4096.
#
#   * Above a leaf, a sparse or dense payload is a shape `PSet.valid` rejects.
#     The node operations read it as empty; `PSet.mem` reads it as a member.
#     So `union(PSparse{[5]}, PZero{})` loses the 5 that the right-hand side
#     keeps.
#
# Both counterexamples are values `PSet.valid` rejects, or ordinals outside
# the leaf they are asked about. So the laws are restated at the production
# depth -- `Idx.sd()` is 20, and a depth-20 tree covers 4096 * 2^20 = 2^32
# ordinals, which is every `U32` -- with the structural invariant as a
# hypothesis. In that form there is no range condition left to state, and no
# counterexample: every ordinal is in range at depth 20.
#
# Backed by: the differential in tests.bend (the production traversal, which
# uses these operations throughout, against the specification closure), and by
# tools/differential.sh against Git on real repositories.
#
# Both are now closed; what follows records how, and what the hypothesis is,
# because the hypothesis is the whole content of the restatement.
# ===========================================================================

# S-02 is proved and lives in LAWS.bend as `set_difference_is_pointwise`,
# `set_union_is_pointwise` and `set_intersection_is_pointwise`, at the
# production depth and with structural validity as the only hypothesis.
#
# S-03 is proved and lives in LAWS.bend as
# `compressing_a_leaf_keeps_its_members`, together with the addressing claim
# it rested on, `the_walk_agrees_with_the_tile_address`. Compression changes
# no member, whichever of its four representations it picks.

# P-01's checkable half is now proved and lives in LAWS.bend as
# `inserting_adds_exactly_that_ordinal`. What remains of P-01 is the part that
# was never going to be an equation: that every *retained old root* still has
# the denotation it had. That is a statement about sharing, and Bend's affine
# values make it true by construction -- a persistent update copies the path
# it changes and cannot reach the nodes it did not copy -- so this release
# records it as a property of the substrate rather than stating it as a law
# over a symbol that cannot observe it.

# ===========================================================================
# C-01, C-02, C-03 -- closure.
#
# C-01 is the least-fixed-point characterisation: C(R) is the least
# edge-closed set containing R. Two of the three things that says are proved
# and live in LAWS.bend -- that C(R) contains R, and that a round which
# changes nothing has reached an edge-closed set.
#
# What is open is that the iteration *does* stabilise within the universe's
# size, which is a pigeonhole argument, and leastness. Leastness has a
# specific obstruction worth recording, because it is the same one that
# blocks U-01's injectivity and Q-01's whole pass. The induction has to carry
# "this round is still inside X" from round to round, so that hypothesis must
# be reusable, so it must be `PSet.is_subset` -- and proving `is_subset` of
# the *next* round needs the converse of the bridge this release does prove:
# from "every member of a is a member of b" to "the fused difference count is
# zero". That converse quantifies over ordinals, and a hypothesis quantified
# over ordinals cannot be used twice under Bend's affine discipline.
#
# C-02 is closed. `the_traversal_returns_the_specification_closure` is in
# LAWS.bend, proved as two inclusions by opposite means: the traversal never
# leaves the closure because every vertex it adds is a successor of one it
# had already accepted and the closure is edge-closed, and the closure never
# leaves the traversal because a finished traversal is itself edge-closed and
# holds the roots -- and the closure is the least such set.
#
# What makes a finished traversal edge-closed is the invariant the frontier
# exists to maintain, written out as `Reach.settled`: every vertex seen has
# either had its successors pushed already, or is still waiting on a
# frontier. When both frontiers are empty the first disjunct holds
# everywhere, which is edge-closure.
#
# `done` is a hypothesis rather than a claim, because an unfinished traversal
# is `ResourceLimit` and never an answer (SPEC 3.3).
# ===========================================================================

# Extensivity is closed in both forms. The pointwise one is
# `the_closure_contains_every_member_of_its_roots`; the counted one is
# `closure_contains_its_roots` in LAWS.bend, with the conditions the product
# establishes -- the graph's successors are ordinals of the universe, the
# depth is the production depth or less, and the roots passed `PSet.valid`.
# Leastness is closed too, as
# `the_closure_is_inside_every_edge_closed_set_holding_its_roots`: the chain
# never leaves an edge-closed set that holds the roots, by induction over the
# rounds using the monotonicity of `post` and the union of two subsets.
#
# What is left of C-01 is the fixed point itself: that the iteration is
# stable after `n` rounds, which is the pigeonhole argument over the universe.

# Edge-closure is closed, in both forms, and so is idempotence. What used to
# stand here said the fixed point was waiting on "a pigeonhole argument over
# the universe this release has not written". It is written:
# `the_enumeration_of_a_valid_set_ascends` makes the length of `PSet.to_list`
# a cardinality, `a_proper_subset_is_strictly_smaller` makes each round that
# is not edge-closed strictly bigger than the one before, and
# `every_set_is_inside_the_universe_of_its_own_depth` bounds how often that
# can happen. `closure_is_edge_closed`,
# `closure_is_edge_closed_at_every_edge` and `closure_is_idempotent` are in
# LAWS.bend.
#
# They carry the fuel condition SPEC 3.3 states -- at least as many rounds as
# the universe has ordinals -- because that is what makes the iteration
# stable, and `Spec.closure` passes exactly that plus one. The edge form also
# carries the ordinal's range, which was free at the fixed production depth
# and has to be said once the law is stated at any depth.

# Union preservation is closed and lives in LAWS.bend as
# `closure_preserves_unions`. It is not a fact about the fixed point: a round
# distributes over a union because `post` does, so it holds at every fuel,
# settled or not. Monotonicity in the roots closed the same way, as
# `closure_is_monotone_in_its_roots`.

# ===========================================================================
# C-04 -- the certificate's own soundness.
#
# C-04 is closed. `an_accepted_certificate_means_an_exact_closure` is in
# LAWS.bend: conditions 1 and 2 make the candidate an edge-closed set
# containing the roots, and the closure is the least such set, so the closure
# is inside the candidate; condition 3 walks the other way, level 0 being
# inside the closure because the closure holds the roots and every later level
# because the closure is edge-closed and each member is one edge from the
# level before.
#
# So `pp git verify` is a check whose soundness is proved rather than argued.
# What the checker does not itself re-derive is carried as hypotheses: the
# ordinals on the levels and in the roots are the universe's, the candidate is
# a set the store would accept, and the fuel is at least the universe's size.
# ===========================================================================

# ===========================================================================
# E-01 -- closed.
#
# All three parts are in LAWS.bend now. Two hold of a produced path with no
# hypothesis at all. The third -- that it starts at a requested root -- held
# only of a *returned* path when this file was written, because it depends on
# the levels being a genuine breadth-first layering, which was obligation
# C-02. C-02 is closed, and so is this: `the_traversal_records_a_breadth_
# first_layering` says `Reach.closure`'s levels are a ladder, and
# `a_produced_witness_starts_at_a_requested_root` walks one back to a root.
#
# It gained one hypothesis on the way: that the target appears in some level.
# That is not a weakening. It is what "the object is reachable" means, and
# what "a witness was produced at all" means -- `Explain.path` answers the
# empty list for an object no level holds, which is how `pp` reports
# unreachable, and the empty list starts nowhere. Stated without it the law
# was false, not open.
#
# `closure/explain.bend` still checks rather than trusts, and `pp git explain`
# still runs `Explain.valid` before printing. A cached or heuristically
# produced witness is not this producer's, and the check is what makes that
# safe.
# ===========================================================================

# ===========================================================================
# Q-01, Q-03 -- the query compiler.
#
# Q-01 is now proved for every rewrite the optimizer performs, and those laws
# live in LAWS.bend: `simplifying_a_union_keeps_every_member` and its three
# siblings say that the expression each rewrite produces has exactly the
# members the expression it replaced had, at the production depth, for every
# ordinal, over the decision `Rw.is_empty_expr` as the rewriter computes it.
# `every_denotation_is_well_shaped` discharges their shape hypothesis for any
# expression whose literals are well shaped.
#
# What is open is the whole pass. `Rw.simplify` also recurses *inside*
# `Reach` and `Filter`, and there the induction needs something the rewrite
# laws do not: that a subexpression which has been simplified to a set with
# the same members -- not the same representation -- closes and filters to a
# set with the same members. That is the statement that closure respects
# pointwise equality, and it needs a set equality that a proof can carry.
# `PSet.is_subset` is the decidable one, and relating it to membership needs
# the set-level fused count, which is the same missing piece C-03 names
# below. An equality stated as "the same at every ordinal" instead cannot be
# used: it is a hypothesis quantified over ordinals, and Bend's affine values
# will not let an induction use one twice, which this proof needs -- once for
# each operand.
#
# Q-01 is closed. `rewriting_preserves_denotation` is in LAWS.bend, with the
# congruence step written: `PSet.same` -- mutual `PSet.is_subset` -- is a
# decidable equality on sets that an induction can carry, every operator is a
# congruence for it, and the bridge from "these two sets agree at every
# ordinal either enumerates" to `PSet.same` is what lets the per-rewrite
# laws, which are pointwise, be used inside it.
#
# The hypothesis is stronger than the per-rewrite laws asked for: the
# literals are sets that passed `PSet.valid`, not just ones that are well
# shaped, because the enumeration bridge the congruence runs on is stated
# over `PSet.valid`. The source's two policy graphs also have to have
# successors that are ordinals of the universe, which is what `Store.succ`
# checks on load.
#
# Q-03 is closed. `the_evaluator_computes_the_denotation` is in LAWS.bend:
# `Ev.go` is an explicit machine, so the proof gives its stack a meaning and
# shows that every step keeps the meaning of the whole configuration. Every
# step but one is definitional; the one that is not is `Reach`, where the
# machine runs the frontier traversal and the meaning names the specification
# closure -- which is law C-02, and why the equality carried is `PSet.same`.
#
# `Val.ok` is a hypothesis, because a traversal that ran out of budget is
# `ResourceLimit` and never an answer.
# ===========================================================================

# ===========================================================================
# G-01, G-03 -- the Git adapter.
#
# G-01 is about a byte grammar: that parsing Git's object metadata is sound
# and complete within the declared grammar and the explicit size limits. Two
# parts of it are statements about the parser alone rather than about
# agreeing with Git, and those are proved and live in LAWS.bend: an object id
# is read at exactly the format's width, and a body is taken by its declared
# length, so neither a short id nor a truncated record is ever accepted.
#
# The rest is not a statement about a definition in this tree -- there is no
# encoder here to invert, and "the grammar" is Git's, not ours -- so what
# would make it a law is a written grammar predicate in Bend and a proof that
# the parser accepts exactly what satisfies it. This release does not have
# that predicate, and writing one that is *faithful* to Git rather than to
# the parser is the hard half: a predicate read off the parser would make the
# law true by construction and worth nothing.
#
# Backed by: tools/differential.sh, which checks both policies and the
# inventory against independent Git plumbing on three repositories, over a
# corpus that includes a merge, a tag to a tag, a tag to a tree, a tag to a
# blob, a symlink, a zero-byte blob, a non-UTF-8 tree entry name and a
# gitlink with no submodule present.
#
# G-03 is closed. `the_projection_contains_every_id_the_universe_names` is
# the direction that decides whether an answer can be trusted -- every id on
# a receiver's report that the source universe names has its ordinal in the
# projection, so it cannot under-report and make `pp` claim an object is
# missing that the receiver has. `the_projection_contains_only_ordinals_the_
# table_named` is the converse, over the proof-only list of ordinals the
# identity table returned for the reported ids.
#
# The converse used to be recorded here as waiting on the pointwise form of
# P-01 -- that inserting `y` leaves `x` absent when it was absent. That is
# now proved as `inserting_adds_nothing_else`, and with it the whole of
# `PSet.insert` is pinned down at every ordinal.
#
# G-02 is closed. The row-level half was proved earlier; the lift to
# `Graph.edge` is now proved too and lives in LAWS.bend as
# `the_tree_data_policy_drops_exactly_the_parent_edges`, over exactly the two
# expressions `Idx.assemble.tries` stores as a source's two graphs. The note
# that used to stand here said the lift needed arithmetic this release had not
# proved -- that `U32.is_lt` agrees with the numeric order, and that `U32.sub`
# is subtraction when it does not borrow. That was the wrong route rather than
# a missing fact: the tables do not need to be read at an absolute index, only
# at the same ordinal as each other, and stating the answer as the same
# *descent over the list* removes the arithmetic entirely. Both facts have
# since been proved anyway, for the set tree; neither is used here.
# ===========================================================================

# ===========================================================================
# D-01 -- the persistent store, and what is checked instead.
#
# M2 shipped the derived store, so this obligation is live rather than
# premature. `index/store.bend` validates a decoded generation structurally
# before it answers anything: the magic line, the declared format, the
# declared object count against the objects actually present, the hex width,
# and every successor index in range. A file that fails any of those is
# `CorruptIndex`, not a wrong answer. SPEC 6.5 requires exactly that and says
# plainly that a checksum is not a substitute.
#
# `PSet.valid` in core/set.bend is the structural check for the set
# representation itself -- sparse and dense payloads only at a leaf, sparse
# offsets ascending and in range, a dense leaf exactly 128 words. It is the
# predicate D-01 would be stated over, and it is also the hypothesis the S-02
# laws above need, because above the leaf level the node operations read a
# stray sparse or dense payload as empty while `PSet.mem` reads it as a
# member.
#
# What is not stated: that decode inverts encode. The differential checks the
# round trip observationally -- a stored generation answers identically to the
# import that produced it, on both policies -- and checks that four kinds of
# corruption are rejected, each corruption derived from the file so that it
# cannot silently become a no-op.
#
# ===========================================================================
# Q-04 -- batch deduplication.
#
# `pp git matrix` answers one cell per *distinct* inventory and points every
# duplicate at the cell it shares with, reporting `distinct_inventories`
# alongside `cells`. The obligation is that this changes no answer and no
# position: a deduplicated batch returns what the undeduplicated one would
# have, in the caller's order.
#
# The order half is proved and lives in LAWS.bend:
# `the_matrix_rows_are_the_cells_in_order` and
# `the_matrix_has_one_row_per_cell`. `Cmd.matrix.rows` builds the output with
# an accumulator and reverses once at the end, and that agrees with the same
# walk written in order -- so a cell's position in the output is its position
# in the input, whether or not its answer was reused.
#
# What a reused answer *is* is proved too:
# `a_reused_answer_is_the_first_one_recorded_under_that_name`. The lookup
# agrees with a plain find-first-by-name, so a duplicate reuses the recorded
# answer of the first cell whose name it points at, and nothing the
# deduplication invented.
#
# What is open is the step from there to "the answer that cell would have
# computed". `Cmd.matrix.same` compares two inventories with `PSet.is_subset`
# in both directions, which now gives equal *members*
# (`a_subset_contains_every_member`); going from equal members to an equal
# statistic needs the enumeration of a set to agree with its membership --
# `List.contains(PSet.to_list(d, s), x) == PSet.member(d, s, x)` -- which
# this release does not prove. That lemma is the one piece several of the
# remaining obligations share.
#
# Backed by: tests.bend checks that three cells over two distinct inventories
# report `cells 3 distinct 2` with the third row pointing at the first, and
# that the shared row's answer is the one the first cell computed.
# ===========================================================================

# ===========================================================================
# I-02, I-03, U-02 -- incremental reuse.
#
# Still not applicable. `pp` re-imports a generation rather than extending
# one: there is no graph append, no cache binding and no generation lifting in
# this release, so there is nothing yet for these to constrain.
# ===========================================================================

# ===========================================================================
# U-01 -- closed.
#
# The round trip was already in LAWS.bend. Injectivity is now there too, as
# `interning_gives_different_ids_different_ordinals`, with one hypothesis this
# file did not have: `Uni.room(os, f)`, saying the `U32` counter strictly grew
# at every step of the run. That is not a convenience. `intern` hands out
# `next` and then increments it as a machine word, so a wrapped counter really
# would give two different objects the same ordinal, and the law as stated
# here was false without it. A source of fewer than 2^32 objects satisfies it,
# and it is decidable data, so the induction can use it freely.
#
# The route this file predicted -- make the invariant a decidable predicate
# over the table, so the hypothesis is reusable under the affine discipline --
# is the one that worked (`Uni.bounded`, in proofs/interninj.bend). What it
# did not predict is that trie *key* injectivity is never needed: the write is
# read back by casing on whether two keys descend the trie the same way
# (`Trie.path_ne`, proofs/trieput.bend), which is all the structure can see,
# and the object ids settle the rest.
# ===========================================================================
