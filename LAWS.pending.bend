# LAWS.pending.bend -- specified, not proved.
#
# These are the obligations from `law-registry.json` that this release states
# precisely but has **not** discharged. They are written in the same syntax
# and over the same production symbols as `LAWS.bend`, because a precise open
# claim is worth more than a paragraph of prose -- but they are open claims,
# and this file is deliberately *not* imported by `PROOF.bend`.
#
# `bend LAWS.pending.bend --check-only` typechecks every statement against the
# production symbols it names and then reports one TODO per unproved law --
# currently 11. That count is the point of the file, so the command "failing"
# is the expected result, and `tools/gate.sh` does not run it as a gate.
#
# What backs each of these instead is recorded next to it, and in `TRUST.md`:
# mostly the closure certificate of SPEC 4.4, which `pp git verify` runs per
# query and which establishes *exactness* rather than an overapproximation,
# and the differential tests of SPEC 11.1.
#
# Closing one of these means moving it into `LAWS.bend` with a proof in
# `PROOF.bend`, and flipping its `status` in `law-registry.json`. Nothing
# here should be closed by weakening it: SPEC 10.3 forbids making a law
# vacuous by rejecting previously supported valid inputs.

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
# C-02 is that the production frontier traversal returns the same set as the
# specification iteration. That is the interesting one, and it is the one the
# closure certificate exists for: SPEC 4.4's conditions establish exactness
# per query, independently of how the answer was computed.
#
# Backed by: `pp git verify` (the certificate), and the five-graph
# differential in tests.bend.
# ===========================================================================

law the_traversal_returns_the_specification_closure:
  for +n: Nat
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +roots: List<&2, U32>
  for +x: U32
  {S.PSet.member(sd,
      R.Reach.seen(sd, R.Reach.closure(n, td, g, sd, roots)), x)
    == S.PSet.member(sd,
        Sp.Spec.closure(n, td, g, sd, S.PSet.from_list(sd, roots)),
        x) : Bool}

# Extensivity is proved, pointwise, and lives in LAWS.bend as
# `the_closure_contains_every_member_of_its_roots`. The `is_subset` form
# below is the same claim counted rather than tested, and it stays open for
# the reason C-03's remaining properties do: `PSet.is_subset` is a count, and
# relating a count to membership needs the set-level fused-count theorem.
law closure_contains_its_roots:
  for +n: Nat
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +r: S.PSet
  {S.PSet.is_subset(sd, r, Sp.Spec.closure(n, td, g, sd, r))
    == True{} : Bool}

# Edge-closure, in the pointwise form the rest of LAWS.bend is written in --
# no `is_subset`, so this one is not waiting on the count. It is waiting on
# the fixed point: the iteration is edge-closed only once it is stable, and
# that it is stable after `n` rounds is C-01, which needs a pigeonhole
# argument over the universe this release has not written.
law closure_is_edge_closed_at_every_edge:
  for +n: Nat
  for +td: Nat
  for +g: G.Graph()
  for +r: S.PSet
  for +u: U32
  for +v: U32
  for +mu: {S.PSet.member(20n, Sp.Spec.closure(n, td, g, 20n, r), u)
    == True{} : Bool}
  for +e: {G.Graph.edge(td, g, u, v) == True{} : Bool}
  {S.PSet.member(20n, Sp.Spec.closure(n, td, g, 20n, r), v)
    == True{} : Bool}

law closure_is_edge_closed:
  for +n: Nat
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +r: S.PSet
  {Sp.Spec.closed(td, g, sd, Sp.Spec.closure(n, td, g, sd, r))
    == True{} : Bool}

law closure_preserves_unions:
  for +n: Nat
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  {S.PSet.member(sd,
      Sp.Spec.closure(n, td, g, sd, S.PSet.union(sd, a, b)), x)
    == S.PSet.member(sd,
        S.PSet.union(sd, Sp.Spec.closure(n, td, g, sd, a),
          Sp.Spec.closure(n, td, g, sd, b)), x) : Bool}

law closure_is_idempotent:
  for +n: Nat
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +r: S.PSet
  for +x: U32
  {S.PSet.member(sd,
      Sp.Spec.closure(n, td, g, sd, Sp.Spec.closure(n, td, g, sd, r)), x)
    == S.PSet.member(sd, Sp.Spec.closure(n, td, g, sd, r), x) : Bool}

# ===========================================================================
# C-04 -- the certificate's own soundness.
#
# `Cert.check` runs SPEC 4.4's four conditions and this release *relies* on
# their meaning: conditions 1-2 give Reach(R) inside C, and condition 3's
# well-founded predecessor chains give C inside Reach(R). That argument is
# written out in closure/cert.bend and in TRUST.md; it is not mechanised.
#
# Until it is, `pp git verify` is a check whose *soundness* is argued rather
# than proved -- which is still stronger than trusting the traversal, because
# a tampered closure is caught either way (tests.bend rejects both an extra
# member and a missing one).
# ===========================================================================

law an_accepted_certificate_means_an_exact_closure:
  for +n: Nat
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +roots: List<&2, U32>
  for +levels: R.Levels
  for +c: S.PSet
  for +x: U32
  for ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool}
  {S.PSet.member(sd, c, x)
    == S.PSet.member(sd,
        Sp.Spec.closure(n, td, g, sd, S.PSet.from_list(sd, roots)),
        x) : Bool}

# ===========================================================================
# E-01 -- the reachability witness.
#
# Closed, in the form the product guarantees it. Two of the three parts hold
# of a produced path with no hypothesis and are proved in LAWS.bend; the
# third -- that it starts at a requested root -- does not hold of the
# producer alone, because it depends on the levels being a genuine
# breadth-first layering, which is C-02.
#
# That is why `closure/explain.bend` checks rather than trusts, and why
# `pp git explain` runs `Explain.valid` on the witness it is about to print
# and exits non-zero when it fails. So the obligation is stated about a
# witness that is *returned* -- `an_accepted_witness_starts_at_a_requested_
# root` and its three siblings say what passing the check means, part by
# part, with the step fold unfolded so that "every step is a policy edge"
# follows by walking the list rather than by trusting the checker.
#
# The law below is the producer-side claim -- that the path the walk builds
# always passes without being checked. It stays open, and it is not what any
# `pp` output rests on.
# ===========================================================================

# ===========================================================================
# E-01 -- the third part of a dependency witness.
#
# Two of SPEC 4.4's three parts are proved and live in LAWS.bend: every step
# of a produced witness is a real policy edge, and the witness ends at the
# object asked about. What is left is that it *starts* at a requested root,
# and that is not a fact about the walk -- the walk is correct. It is a fact
# about the levels it walks: a breadth-first layering from the roots has its
# level 0 inside the roots and every later level reachable in one edge from
# the one before, and only then does walking back from the target land on a
# root rather than stopping early.
#
# So this is C-02 wearing a different hat, and it is stated here with the
# layering as an explicit hypothesis rather than as a claim about
# `Reach.closure`'s output.
#
# Backed by: `Explain.valid` checks all three parts on every witness
# `pp git explain` emits, so a witness that does not start at a root is
# rejected rather than returned; tests.bend runs one.
# ===========================================================================

law a_produced_witness_starts_at_a_requested_root:
  for +td: Nat
  for +g: G.Graph()
  for +n: Nat
  for +sd: Nat
  for +roots: List<&2, U32>
  for +target: U32
  {Ex.Explain.first_in(
    Ex.Explain.path(td, g, R.Reach.levels(sd, R.Reach.closure(n, td, g, sd,
      roots)), target), roots) == True{} : Bool}

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
# So the whole-pass law is stated below with the hypothesis the per-rewrite
# laws need, and it is the congruence step alone that is missing.
#
# Q-03 is SPEC 3.6's compiler contract itself:
#
#     observe(execute_b(compile(W, q))) = [[q]]_W
#
# stated here as: the production evaluator and the denotational evaluator
# agree on every expression. Backed by the differential in tests.bend, which
# runs exactly this comparison for `Reach` over five graphs.
# ===========================================================================

law rewriting_preserves_denotation:
  for +src: Idx.Source
  for +e: A.SetExpr
  for +x: U32
  for +ok: {PDn.SetExpr.wf_lits(e) == True{} : Bool}
  {S.PSet.member(20n, Den.Den.eval(src, Rw.Rw.simplify(e)), x)
    == S.PSet.member(20n, Den.Den.eval(src, e), x) : Bool}

law the_evaluator_computes_the_denotation:
  for +src: Idx.Source
  for e: A.SetExpr
  for +x: U32
  for ok: {Ev.Val.ok(Ev.Ev.run(src, e)) == True{} : Bool}
  {S.PSet.member(20n, Ev.Val.set(Ev.Ev.run(src, e)), x)
    == S.PSet.member(20n, Den.Den.eval(src, e), x) : Bool}

# ===========================================================================
# G-01, G-03 -- the Git adapter.
#
# G-01 is about a byte grammar: that parsing Git's object metadata is sound
# and complete within the declared grammar and the explicit size limits. It
# is not a statement about a definition in this tree -- there is no encoder
# here to invert, and "the grammar" is Git's, not ours -- so what would make
# it a law is a written grammar predicate in Bend and a proof that the parser
# accepts exactly what satisfies it. This release does not have that
# predicate, and writing one that is *faithful* to Git rather than to the
# parser is the hard half: a predicate read off the parser would make the law
# true by construction and worth nothing.
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
# U-01 -- the half that is still open.
#
# The round trip is proved and lives in LAWS.bend: interning an id and then
# looking it up in the table interning handed back finds the ordinal
# interning handed back, for any universe and any id.
#
# Injectivity is the other direction, and it is not a property of one write:
# it says that across every write ever made into this table, no two different
# ids ended up sharing an ordinal. So it is stated over a universe that was
# *built* by interning -- `Uni.of_list`, interning a list of ids into a fresh
# universe, which is what the importer does as it discovers objects -- rather
# than over an arbitrary `Universe`, because an arbitrary hand-built table can
# obviously repeat an ordinal and nothing in the type rules that out.
#
# Proving it needs an invariant carried across every step -- every ordinal in
# the table is below `next`, and no two slots share one -- and that invariant
# quantifies over all keys of a trie. A function-typed hypothesis cannot be
# used twice under Bend's affine discipline, and this proof needs it twice,
# once for each of the two ids. The route that would work is to make the
# invariant a decidable predicate over the table, so the hypothesis is data
# and reusable, and then prove extraction from it by induction on the trie.
# That is a development on its own and this release does not have it.
#
# Backed by: construction. `Uni.intern` assigns `next` and then increments it,
# and the only writer of a slot is that branch, so a repeated ordinal would
# require the same `next` to be handed out twice.
# ===========================================================================

law interning_gives_different_ids_different_ordinals:
  for +f: Od.Fmt
  for +os: List<&2, Od.Oid>
  for +x: Od.Oid
  for +y: Od.Oid
  for +a: U32
  for +b: U32
  for +fx: {Ui.Uni.find(Ui.Uni.table(PIn.Uni.of_list(f, os)), x) == Some{a}
    : Maybe<&2, U32>}
  for +fy: {Ui.Uni.find(Ui.Uni.table(PIn.Uni.of_list(f, os)), y) == Some{b}
    : Maybe<&2, U32>}
  for +same: {a == b : U32}
  {Od.Oid.eq(x, y) == True{} : Bool}
