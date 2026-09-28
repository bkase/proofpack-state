# PROOF.bend -- discharges every law in LAWS.bend.
#
# `bend PROOF.bend` fails while any law is open or false and prints
# "All terms check." once every one holds. `bend PROOF.bend --safe`
# re-checks the result with the proven BendTT kernel and lists what it
# leaves out; `tools/gate.sh` runs both and records the exclusion audit.
#
# Each def here delegates to the module that does the work, so the structure
# of the argument stays where the definitions are:
#
#   proofs/nat.bend       the Nat accumulator's equations
#   proofs/word.bend      pointwise bit laws over Word(n), lifted to U32
#   proofs/popcount.bend  the production popcount against the bit vector
#   proofs/bits.bend      the fast bit test against the bit accessor
#   proofs/words.bend     the tile kernel and the fused count
#   proofs/stats.bend     the statistics monoid
#   proofs/missing.bend   the least-additional-set theorem
#   proofs/eq.bend        machine-word equality reflection
#   proofs/policy.bend    the tree-data row filter
#   proofs/addr.bend      how an ordinal addresses a tile
#   proofs/ords.bend      the sparse leaf's offset list
#   proofs/bitset.bend    setting a bit and reading it back
#   proofs/leaf.bend      inserting into a leaf
#   proofs/witness.bend   what a dependency witness guarantees
#   proofs/collapse.bend  the Zero/Full branch collapses
#   proofs/descend.bend   carrying an ordinal down a level
#   proofs/inject.bend    the numeric reading of a word is injective
#   proofs/split.bend     the division identity, and A3
#   proofs/bridge.bend    a sparse leaf and its tile agree
#   proofs/count.bend     what a bit count says about the bits
#   proofs/adder.bend     what U32 addition computes
#   proofs/enum.bend      enumerating a tile
#   proofs/compress.bend  what compression decides
#   proofs/faithful.bend  a valid leaf and its tile agree
#   proofs/walk.bend      the walk and the address agree
#   proofs/leafops.bend   the leaf operations are pointwise
#   proofs/setops.bend    the set operations are pointwise
#   proofs/empty.bend     an empty set has no members
#   proofs/closure.bend   closing nothing gives nothing
#   proofs/cert.bend      what an accepted certificate means
#   proofs/order.bend     comparison agrees with the numeric order
#   proofs/shape.bend     the part of structural validity the algebra uses
#   proofs/preserve.bend  the set operations keep that shape
#   proofs/nothing.bend   an empty set enumerates to nothing
#   proofs/denote.bend    every denotation is well shaped
#   proofs/rewrite.bend   every admitted query rewrite keeps the denotation
#   proofs/extensive.bend the closure contains what it closes
#   proofs/table.bend     what a table built from a list answers
#   proofs/insert.bend    inserting never loses a member
#   proofs/only.bend      inserting adds nothing else
#   proofs/subset.bend    the subset test, related to membership
#   proofs/batch.bend     the matrix restores the caller's positions
#   proofs/store.bend     what accepting a stored generation means
#   proofs/machine.bend   a failure the evaluator notices is one it reports
#   proofs/traverse.bend  the traversal never loses a vertex
#   proofs/parse.bend     the parser never reads short
#   proofs/split_add.bend adding into free bits is setting them
#   proofs/decr.bend      what subtracting one does
#   proofs/span.bend      what counting down covers
#   proofs/leafenum.bend  a leaf enumerates exactly its members
#   proofs/interval.bend  a subtree's bit test is an interval of ordinals
#   proofs/nodeenum.bend  a full node enumerates exactly its interval
#   proofs/maskwidth.bend the same ordinal, masked at two adjacent widths
#   proofs/lastord.bend   the last ordinal of a node's interval
#   proofs/halves.bend    a node's two halves, as bases
#   proofs/childtest.bend which half an ordinal is in
#   proofs/treeenum.bend  the tree enumerates exactly its members
#   proofs/tilefit.bend   the tile walk stays inside the leaf
#   proofs/countlen.bend  the count is the length of the enumeration
#   proofs/fusedlen.bend  the fused count is the length of the fused list
#   proofs/orderlist.bend ascending and descending lists of ordinals
#   proofs/tileorder.bend the tile walk emits ordinals in order
#   proofs/merge.bend     what the merge-based difference contains
#   proofs/leafdiff.bend  what the fused leaf difference emits
#   proofs/leaffit.bend   everything the fused leaf emits fits in a leaf
#   proofs/treediff.bend  the fused difference walk, over a tree
#   proofs/subsetconv.bend  the converse of the subset bridge
#   proofs/subsetalg.bend the subset relation is transitive
#   proofs/validkeep.bend the algebra keeps the shape the store checks
#   proofs/insertvalid.bend  insertion keeps it too
#   proofs/listset.bend   building a set from a list, at any depth
#   proofs/graphrange.bend  a graph whose successors are ordinals
#   proofs/postmono.bend  the successor step is monotone
#   proofs/nonempty.bend  a nonzero count exhibits a member
#   proofs/validshape.bend  validity gives the enumeration the shape it needs
#   proofs/sum.bend       addition that does not overflow is addition
#   proofs/inventory.bend the inventory projection names what it was told
#   proofs/policylift.bend  G-02, from a row to an edge
#   proofs/trie.bend      a trie reads back what was written
#   proofs/intern.bend    interning an id and finding it again

import Base
import ./LAWS.bend as Laws
import ./proofs/shape.bend as PSh
import ./proofs/preserve.bend as PPr
import ./proofs/nothing.bend as PNo
import ./proofs/denote.bend as PDn
import ./proofs/rewrite.bend as PRw
import ./proofs/extensive.bend as PEx
import ./proofs/table.bend as PTb
import ./proofs/insert.bend as PIns
import ./proofs/only.bend as POn
import ./proofs/subset.bend as PSb
import ./proofs/batch.bend as PBa
import ./proofs/store.bend as PSt
import ./proofs/machine.bend as PMa
import ./proofs/traverse.bend as PTv
import ./proofs/parse.bend as PPa
import ./proofs/split_add.bend as PSa
import ./proofs/decr.bend as PDe
import ./proofs/span.bend as PSn
import ./proofs/leafenum.bend as PLe
import ./proofs/interval.bend as PIt
import ./proofs/nodeenum.bend as PNe
import ./proofs/maskwidth.bend as PMw
import ./proofs/lastord.bend as PLd
import ./proofs/halves.bend as PHv
import ./proofs/childtest.bend as PCh
import ./proofs/treeenum.bend as PTe
import ./proofs/validshape.bend as PVs
import ./proofs/tilefit.bend as PTf
import ./proofs/countlen.bend as PCn
import ./proofs/fusedlen.bend as PFl
import ./proofs/orderlist.bend as POl
import ./proofs/tileorder.bend as PTo
import ./proofs/merge.bend as PMg
import ./proofs/leafdiff.bend as PLf2
import ./proofs/leaffit.bend as PLf3
import ./proofs/treediff.bend as PTd
import ./proofs/subsetconv.bend as PSc2
import ./proofs/subsetalg.bend as PSa2
import ./proofs/validkeep.bend as PVk
import ./proofs/insertvalid.bend as PIvd
import ./proofs/listset.bend as PLs
import ./proofs/graphrange.bend as PGr
import ./proofs/postmono.bend as PPm
import ./proofs/nonempty.bend as PNe2
import ./proofs/sum.bend as PSm
import ./proofs/inventory.bend as PIv
import ./proofs/policylift.bend as PPl
import ./proofs/trie.bend as PTr
import ./proofs/intern.bend as PIn
import ./proofs/nat.bend as N
import ./proofs/word.bend as PW
import ./proofs/popcount.bend as PP
import ./proofs/bits.bend as PB
import ./proofs/words.bend as PWo
import ./proofs/stats.bend as PS
import ./proofs/missing.bend as PM
import ./proofs/eq.bend as PE
import ./proofs/policy.bend as PPol
import ./proofs/addr.bend as PAd
import ./proofs/ords.bend as POrd
import ./proofs/order.bend as POrder
import ./proofs/bitset.bend as PBs
import ./proofs/leaf.bend as PLf
import ./proofs/witness.bend as PWit
import ./proofs/collapse.bend as PCo
import ./proofs/descend.bend as PDc
import ./proofs/inject.bend as PIj
import ./proofs/split.bend as PSp
import ./proofs/bridge.bend as PBr
import ./proofs/count.bend as PCt
import ./proofs/adder.bend as PAdd
import ./proofs/enum.bend as PEn
import ./proofs/compress.bend as PCp
import ./proofs/faithful.bend as PFa
import ./proofs/walk.bend as PWk
import ./proofs/leafops.bend as PLo
import ./proofs/setops.bend as PSo
import ./proofs/empty.bend as PEm
import ./proofs/closure.bend as PCl
import ./proofs/cert.bend as PCe

# --- B-01: the word kernel --------------------------------------------------

def Laws.word_difference_is_pointwise(a, b, i):
  PW.U32.bit_diff(a, b, i)

def Laws.word_intersection_is_pointwise(a, b, i):
  PW.U32.bit_and(a, b, i)

def Laws.word_union_is_pointwise(a, b, i):
  PW.U32.bit_or(a, b, i)

def Laws.shifting_right_reads_the_next_bit_up(a, i):
  PW.U32.bit_shr(a, i)

def Laws.the_tail_mask_hides_every_padding_bit(k, i):
  PW.U32.bit_mask(k, i)

def Laws.popcount_counts_the_bits_that_are_set(x):
  PP.U32.popcount_spec(x)

def Laws.the_fast_bit_test_agrees_with_the_bit_vector(w, b):
  PB.U32.test_spec(w, b)

# --- S-01, R-01: the tile kernel --------------------------------------------

def Laws.tile_difference_is_pointwise(a, b, i, k):
  PWo.Words.at_diff(a, b, i, k)

def Laws.tile_intersection_is_pointwise(a, b, i, k):
  PWo.Words.at_and(a, b, i, k)

def Laws.tile_union_is_pointwise(a, b, i, k):
  PWo.Words.at_or(a, b, i, k)

# --- Q-02: the fused reduction ----------------------------------------------

def Laws.counting_a_difference_needs_no_difference(a, b):
  PWo.Words.diff_count_spec(a, b)

# --- R-02: statistics are a commutative monoid -------------------------------

def Laws.statistics_have_a_left_identity(s):
  PS.Stats.add_zero_left(s)

def Laws.statistics_have_a_right_identity(s):
  PS.Stats.add_zero_right(s)

def Laws.statistics_add_commutatively(x, y):
  PS.Stats.add_comm(x, y)

def Laws.statistics_add_associatively(x, y, z):
  PS.Stats.add_assoc(x, y, z)

def Laws.every_object_counts_once(size, kind):
  PS.Stats.one_object(size, kind)

# --- M-01, M-02, M-03, I-01: the least additional object set ----------------

def Laws.the_missing_set_covers_the_requirement(k, h):
  PM.Missing.covers(k, h)

def Laws.the_missing_set_is_the_least_one(k, h, t):
  PM.Missing.least(k, h, t)

def Laws.readiness_is_an_empty_difference(k, h):
  PM.Missing.ready(k, h)

def Laws.missing_distributes_over_a_union_of_requirements(a, b, h):
  PM.Missing.union_split(a, b, h)

def Laws.inventory_tiers_compose(a, h1, h2):
  PM.Missing.tiers(a, h1, h2)

def Laws.an_additions_only_update_needs_no_rederivation(k, h, a):
  PM.Missing.added(k, h, a)

def Laws.add_wins_in_a_patch(h, d, a):
  PM.Missing.add_wins(h, d, a)

# --- B-02: the checked accumulator ------------------------------------------

def Laws.the_accumulator_has_an_identity(a):
  N.Nat.add_zero(a)

def Laws.the_accumulator_adds_commutatively(a, b):
  N.Nat.add_comm(a, b)

def Laws.the_accumulator_adds_associatively(a, b, c):
  N.Nat.add_assoc(a, b, c)

# --- G-02: the tree-data policy, at the row ---------------------------------

def Laws.a_filtered_row_drops_exactly_the_commit_targets(mt, row, v):
  PPol.Policy.filter_drops_commits(mt, row, v)

# --- reflection -------------------------------------------------------------

def Laws.word_equality_is_reflected(a, b, ok):
  PE.U32.eq_reflect(a, b, ok)

# --- P-01: inserting into a leaf --------------------------------------------

def Laws.inserting_into_a_leaf_keeps_that_ordinal(s, x, fits):
  PLf.PSet.mem_add_leaf(s, x, fits)

def Laws.inserting_into_an_ordinal_list_keeps_that_ordinal(xs, x):
  POrd.Ords.elem_insert(xs, x)

def Laws.setting_a_bit_reads_it_back(ws, x):
  PBs.Words.bit_set(ws, x)

def Laws.a_bit_index_is_below_the_word_width(x):
  PAd.U32.low_five_bound(x)

# --- E-01: dependency witnesses ---------------------------------------------

def Laws.every_step_of_a_produced_witness_is_an_edge(td, g, rev, target):
  PWit.Explain.path_steps(td, g, rev, target)

def Laws.a_produced_witness_ends_at_the_object_asked_about(td, g, rev,
  target, p):
  PWit.Explain.walk_ends_at_target(td, g, rev, target, p)

# --- S-02, in part: the Zero/Full collapses ---------------------------------

def Laws.collapsing_a_branch_keeps_its_members(p, lo, hi, h, x):
  PCo.PSet.mem_mk(p, lo, hi, h, x)

# --- the addressing arithmetic ----------------------------------------------

def Laws.an_ordinal_is_below_a_power_of_two_exactly_when_it_fits_in_that_many_bits(
  x, k, ok):
  PDc.U32.is_lt_shln(x, k, ok)

def Laws.rebasing_into_the_upper_half_keeps_the_ordinal_in_range(x, k, hi,
  no):
  PDc.U32.hi_zero_sub(x, k, hi, no)

def Laws.halving_a_half_width_moves_the_bit_down(k, ok):
  PDc.U32.shr_shln_one(k, ok)

def Laws.inserting_adds_exactly_that_ordinal(s, x, v):
  PLf.PSet.mem_insert(s, x, v)

def Laws.the_number_a_word_reads_as_determines_the_word(a, b, e):
  PIj.U32.to_nat_inj(a, b, e)

def Laws.an_ordinal_is_its_word_index_scaled_plus_its_bit_index(x):
  PSp.U32.to_nat_split(x)

def Laws.the_tile_address_is_injective(o, x, ei, eb):
  PSp.U32.address_inj(o, x, ei, eb)

def Laws.a_sparse_leaf_and_its_tile_hold_the_same_ordinals(offs, x, fits):
  PBr.PSet.sparse_matches_its_tile(offs, x, fits)

def Laws.a_tile_at_capacity_has_every_bit_set(ws, full, i, iok, b, bok):
  PCt.Words.count_full(ws, full, i, iok, b, bok)

def Laws.a_tile_counting_zero_has_no_bit_set(ws, z, i, b, bok):
  PCt.Words.count_zero(ws, z, i, b, bok)

def Laws.adding_two_small_ordinals_adds_their_values(a, b, k, za, zb, ok):
  PAdd.U32.to_nat_add(a, b, k, za, zb, ok)

def Laws.enumerating_a_tile_lists_what_the_walk_holds(ws, x):
  PEn.Words.elem_members(ws, x)

def Laws.a_tile_compression_calls_empty_has_no_members(ws, x, z):
  PCp.PSet.compress_zero(ws, x, z)

def Laws.a_tile_compression_calls_full_has_every_member(ws, x, wide, full,
  inr):
  PCp.PSet.compress_full(ws, x, wide, full, inr)

def Laws.a_valid_leaf_and_its_tile_hold_the_same_ordinals(s, x, v, inr):
  PFa.PSet.leaf_faithful(s, x, PSh.PSet.valid_leaf_wf(s, v), inr)

def Laws.a_valid_set_has_no_payload_above_a_leaf(p, s, ok):
  PCo.PSet.valid_is_node(p, s, ok)

def Laws.compressing_a_leaf_keeps_its_members(ws, x, wide, inr):
  PCp.PSet.compress_keeps_pending(ws, x, wide, inr)

def Laws.the_walk_agrees_with_the_tile_address(ws, x, wide):
  PWk.Words.holds_bit(ws, x, wide)

def Laws.the_leaf_difference_is_pointwise(a, b, x, va, vb, inr):
  PLo.PSet.diff_leaf_pointwise(a, b, x, PSh.PSet.valid_leaf_wf(a, va),
    PSh.PSet.valid_leaf_wf(b, vb), inr)

def Laws.the_leaf_union_is_pointwise(a, b, x, va, vb, inr):
  PLo.PSet.union_leaf_pointwise(a, b, x, PSh.PSet.valid_leaf_wf(a, va),
    PSh.PSet.valid_leaf_wf(b, vb), inr)

def Laws.the_leaf_intersection_is_pointwise(a, b, x, va, vb, inr):
  PLo.PSet.inter_leaf_pointwise(a, b, x, PSh.PSet.valid_leaf_wf(a, va),
    PSh.PSet.valid_leaf_wf(b, vb), inr)

def Laws.set_difference_is_pointwise(a, b, x, va, vb):
  PSo.PSet.diff_member(a, b, x, PSh.PSet.valid_wf(20n, a, va),
    PSh.PSet.valid_wf(20n, b, vb))

def Laws.set_union_is_pointwise(a, b, x, va, vb):
  PSo.PSet.union_member(a, b, x, PSh.PSet.valid_wf(20n, a, va),
    PSh.PSet.valid_wf(20n, b, vb))

def Laws.set_intersection_is_pointwise(a, b, x, va, vb):
  PSo.PSet.inter_member(a, b, x, PSh.PSet.valid_wf(20n, a, va),
    PSh.PSet.valid_wf(20n, b, vb))

def Laws.an_empty_set_has_no_members(d, s, h, x, z):
  PEm.PSet.empty_no_member(d, s, h, x, z, U32.is_lt(x, h), {==})

def Laws.union_with_an_empty_set_changes_nothing(a, b, x, va, vb, z):
  PEm.PSet.union_empty_left(a, b, x, PSh.PSet.valid_wf(20n, a, va),
    PSh.PSet.valid_wf(20n, b, vb), z)

def Laws.intersection_with_an_empty_set_is_empty(a, b, x, va, vb, z):
  PEm.PSet.inter_empty_left(a, b, x, PSh.PSet.valid_wf(20n, a, va),
    PSh.PSet.valid_wf(20n, b, vb), z)

def Laws.subtracting_an_empty_set_changes_nothing(a, b, x, va, vb, z):
  PEm.PSet.diff_empty_right(a, b, x, PSh.PSet.valid_wf(20n, a, va),
    PSh.PSet.valid_wf(20n, b, vb), z)

def Laws.closing_nothing_gives_nothing(n, td, g, p):
  PCl.Spec.closure_empty(n, td, g, p)

def Laws.an_accepted_certificate_contains_the_roots(td, g, sd, roots,
  levels, c, ok):
  PCe.Cert.accepts_roots(td, g, sd, roots, levels, c, ok)

def Laws.an_accepted_certificate_is_edge_closed(td, g, sd, roots, levels,
  c, ok):
  PCe.Cert.accepts_closed(td, g, sd, roots, levels, c, ok)

def Laws.an_accepted_certificate_matches_its_levels(td, g, sd, roots,
  levels, c, ok):
  PCe.Cert.accepts_levels(td, g, sd, roots, levels, c, ok)

def Laws.an_accepted_certificate_has_layered_predecessors(td, g, sd,
  roots, levels, c, ok):
  PCe.Cert.accepts_layers(td, g, sd, roots, levels, c, ok)

def Laws.comparing_two_ordinals_compares_their_values(a, b):
  POrder.U32.cmp_spec(a, b)

def Laws.interning_an_id_then_finding_it_gives_the_same_ordinal(u, o):
  PIn.Uni.intern_round_trip(u, o)

def Laws.reading_a_trie_at_the_key_just_written_gives_that_value(A, d, t,
  x, v):
  PTr.Trie.at_set(A, d, t, x, v)

def Laws.every_structurally_valid_set_is_well_shaped(d, s, v):
  PSh.PSet.valid_wf(d, s, v)

def Laws.union_keeps_a_set_well_shaped(d, a, b, va, vb):
  PPr.PSet.wf_union(d, a, b, va, vb)

def Laws.intersection_keeps_a_set_well_shaped(d, a, b, va, vb):
  PPr.PSet.wf_inter(d, a, b, va, vb)

def Laws.difference_keeps_a_set_well_shaped(d, a, b, va, vb):
  PPr.PSet.wf_diff(d, a, b, va, vb)

def Laws.an_empty_set_enumerates_to_nothing(d, s, z):
  PNo.PSet.to_list_of_empty(d, s, z)

def Laws.closing_a_set_with_no_members_gives_a_set_with_no_members(n, td, g,
  p, r, z):
  PNo.Spec.closure_of_empty(n, td, g, p, r, z)

def Laws.simplifying_a_union_keeps_every_member(src, a, b, x, va, vb):
  PRw.Simp.union_sound(src, a, b, x, va, vb)

def Laws.simplifying_an_intersection_keeps_every_member(src, a, b, x, va,
  vb):
  PRw.Simp.inter_sound(src, a, b, x, va, vb)

def Laws.simplifying_a_difference_keeps_every_member(src, a, b, x, va, vb):
  PRw.Simp.diff_sound(src, a, b, x, va, vb)

def Laws.simplifying_a_reachability_keeps_every_member(src, p, a, x):
  PRw.Simp.reach_sound(src, p, a, x)

def Laws.every_denotation_is_well_shaped(src, e, ok):
  PDn.Eval.wf(src, e, ok)

def Laws.the_closure_contains_every_member_of_its_roots(n, td, g, r, x, v,
  m):
  PEx.Spec.closure_contains_its_roots(n, td, g, r, x, v, m)

def Laws.a_table_built_from_a_list_answers_the_same_descent_over_the_list(A,
  d, xs, x):
  PTb.Trie.at_of_list(A, d, xs, x)

def Laws.the_tree_data_policy_drops_exactly_the_parent_edges(rows, metas, u,
  v, m, hm):
  PPl.Idx.tree_data_edge(rows, metas, u, v, m, hm)

def Laws.inserting_keeps_every_member(s, y, x, v, ok):
  PIns.PSet.insert_keeps(s, y, x, v, ok)

def Laws.a_set_built_from_a_list_has_every_ordinal_on_it(xs, x, ok):
  PIns.PSet.from_list_contains(xs, x, ok)

def Laws.the_projection_contains_every_id_the_universe_names(u, oids, o, x,
  f, ok):
  PIv.Inv.project_finds(u, oids, o, x, f, ok)

def Laws.inserting_adds_nothing_else(s, y, x, v, ok):
  POn.PSet.insert_only(s, y, x, v, ok)

def Laws.a_set_built_from_a_list_has_only_the_ordinals_on_it(xs, x, ok):
  POn.PSet.from_list_only(xs, x, ok)

def Laws.the_projection_contains_only_ordinals_the_table_named(u, oids, x,
  ok):
  PIv.Inv.project_only(u, oids, x, ok)

def Laws.an_accepted_witness_starts_at_a_requested_root(td, g, roots, u,
  rest, target, ok):
  PWit.Explain.accepts_root_head(td, g, roots, u, rest, target, ok)

def Laws.an_accepted_witness_ends_at_the_object_asked_about(td, g, roots,
  path, target, ok):
  PWit.Explain.accepts_last(td, g, roots, path, target, ok)

def Laws.an_accepted_witness_takes_an_edge_at_every_step(td, g, u, v, rest,
  ok):
  PWit.Explain.checked_edge(td, g, u, v, rest, ok)

def Laws.the_rest_of_an_accepted_witness_is_accepted(td, g, u, v, rest, ok):
  PWit.Explain.checked_rest(td, g, u, v, rest, ok)

def Laws.an_accepted_witness_is_checked_end_to_end(td, g, roots, path,
  target, ok):
  PWit.Explain.accepts_steps(td, g, roots, path, target, ok)

def Laws.a_subset_contains_every_member(a, b, x, va, vb, sub, ma):
  PSb.PSet.is_subset_member(a, b, x, va, vb, sub, ma)

def Laws.a_set_with_a_zero_count_has_no_members(d, s, bx, h, x, eh, dok,
  ebx, v, z):
  PSb.PSet.count_zero_mem(d, s, bx, h, x, eh, dok, ebx, v, z)

def Laws.a_stable_round_has_reached_an_edge_closed_set(td, g, xs, v, w, st,
  mp):
  PEx.Spec.stable_is_closed(td, g, xs, v, w, st, mp)

def Laws.the_matrix_rows_are_the_cells_in_order(cx, k, cells, done):
  PBa.Rows.from_empty(cx, k, cells, done)

def Laws.the_matrix_has_one_row_per_cell(cx, k, cells, done):
  PBa.Rows.one_per_cell(cx, k, cells, done)

def Laws.a_reused_answer_is_the_first_one_recorded_under_that_name(done,
  want):
  PBa.Rows.lookup_is_find(done, want)

def Laws.an_accepted_store_declared_the_objects_it_holds(c, d, ec, ok):
  PSt.Store.accepted_count(c, d, ec, ok)

def Laws.a_rejected_store_says_why(u, d, eu, no):
  PSt.Store.rejection_is_reported(u, d, eu, no)

def Laws.an_unfinished_traversal_is_never_reported_as_complete(fuel, src, c,
  k):
  PMa.Mach.failure_is_reported(fuel, src, c, k)

def Laws.the_evaluator_machine_computes_the_fold(src, e, good):
  PMa.Mach.set_computes(src, e, good)

def Laws.the_traversal_keeps_every_vertex_it_has_seen(fuel, td, g, seen,
  front, next, levels, rounds, x, v, ok):
  PTv.Reach.go_keeps(fuel, td, g, seen, front, next, levels, rounds, x, v,
    ok)

def Laws.the_traversal_returns_every_root_it_was_given(n, td, g, roots, r,
  ok):
  PTv.Reach.closure_keeps_its_roots(n, td, g, roots, r, ok)

def Laws.an_accepted_object_id_had_its_full_width(f, bs, ok):
  PPa.Oid.of_hex_needs_width(f, bs, ok)

def Laws.an_accepted_record_had_its_declared_size(oid, k, n, bs, ok):
  PPa.Parse.a_record_fits_its_declared_size(oid, k, n, bs, ok)

def Laws.adding_into_free_bits_is_setting_them(y, b, k, hy, lb):
  PSa.U32.add_disjoint(y, b, k, hy, lb)

def Laws.a_word_is_its_low_bits_or_its_high_bits(x, k):
  PSa.U32.or_split(x, k)

def Laws.subtracting_one_is_one_less(x, pos):
  PDe.U32.dec_spec(x, pos)

def Laws.counting_down_reaches_every_ordinal_in_the_span(k, eq, ord, x,
  eeq, le, g):
  PSn.Ords.in_down_of_span(k, eq, ord, x, eeq, le, g)

def Laws.counting_down_reaches_nothing_else(k, eq, ord, x, eeq, nowrap,
  ok):
  PSn.Ords.span_of_in_down(k, eq, ord, x, eeq, nowrap, ok)

def Laws.a_leaf_enumerates_exactly_its_members(s, y, inr, ok):
  PLe.PSet.leaf_members_mem(s, y, inr, ok)

def Laws.a_subtree_test_is_an_interval(base, x, k, lb, m):
  PIt.Interval.bounds_of_match(base, x, k, lb, m)

def Laws.an_interval_forces_the_subtree_test(base, x, k, lb, lo, hi):
  PIt.Interval.match_of_bounds(base, x, k, lb, lo, hi)

def Laws.a_full_node_enumerates_its_interval(k, base, ord, x, tail, lb,
  eo):
  PNe.Ords.range_is_an_interval(k, base, ord, x, tail, lb, eo)

def Laws.addition_that_does_not_carry_out_is_addition(n, a, b, nc):
  PSm.Word.add_of_no_carry(n, a, b, nc)

def Laws.a_sum_that_fits_does_not_carry_out(n, c, a, b, ec, bound):
  PSm.Word.add_spec(n, c, a, b, ec, bound)

def Laws.clearing_the_top_bit_of_a_mask_narrows_it(x, k):
  PMw.U32.clear_mask(x, k)

def Laws.a_clear_top_bit_makes_two_masks_agree(x, k, hz):
  PMw.U32.mask_step(x, k, hz)

def Laws.the_last_ordinal_of_a_node_fills_its_low_bits(base, j, lz):
  PLd.U32.last_ordinal(base, j, lz)

def Laws.the_last_ordinal_of_a_node_is_one_below_the_next(base, j, lz,
  le):
  PLd.U32.last_ordinal_value(base, j, lz, le)

def Laws.an_ordinal_below_the_half_is_the_low_childs(base, k, x, e, f,
  lz, hz, ee, ef):
  PCh.Test.low_matches(base, k, x, e, f, lz, hz, ee, ef)

def Laws.an_ordinal_below_the_half_is_not_the_high_childs(base, k, x, f,
  lz, lt, hz, ef):
  PCh.Test.high_misses(base, k, x, f, lz, lt, hz, ef)

def Laws.an_ordinal_at_the_half_is_the_high_childs(base, k, x, e, f, lz,
  lt, nz, ee, ef):
  PCh.Test.high_matches(base, k, x, e, f, lz, lt, nz, ee, ef)

def Laws.an_ordinal_at_the_half_is_not_the_low_childs(base, k, x, f, lz,
  nz, ef):
  PCh.Test.low_misses(base, k, x, f, lz, nz, ef)

def Laws.the_second_halfs_base_is_one_half_above(base, k, lz, lt):
  PHv.U32.to_nat_half_base(base, k, lz, lt)

def Laws.the_list_a_node_contributes_is_its_interval_and_its_members(d,
  s, base, x, tail, ok, lz, lt):
  PTe.PSet.members_contains(d, s, base, x, tail, ok, lz, lt)

def Laws.enumerating_a_set_lists_exactly_its_members(d, s, x, ok, lt,
  inr):
  PTe.PSet.to_list_member(d, s, x, ok, lt, inr)

def Laws.a_valid_set_has_the_shape_the_enumeration_needs(d, s, v):
  PVs.PSet.ok_of_valid(d, s, v)

def Laws.a_valid_set_lists_exactly_its_members(d, s, x, v, lt, inr):
  PVs.PSet.to_list_member_of_valid(d, s, x, v, lt, inr)

def Laws.a_tile_walk_stays_inside_the_leaf(ws, len):
  PTf.Words.members_fit(ws, len)

def Laws.the_count_is_the_length_of_the_enumeration(d, s, lt):
  PCn.PSet.count_is_to_list_length(d, s, lt)

def Laws.a_set_with_a_nonzero_count_has_a_member(d, s, l, ok, lt, el,
  pos):
  PNe2.PSet.witness(d, s, l, ok, lt, el, pos)

def Laws.the_fused_count_is_the_length_of_the_fused_list(d, a, b, lt):
  PFl.PSet.missing_count_is_length(d, a, b, lt)

def Laws.a_tile_lists_its_ordinals_in_order(ws, len):
  PTo.Ords.asc_members(ws, len)

def Laws.the_merge_difference_holds_exactly_what_it_should(a, b, x, aa,
  ab):
  PMg.Ords.diff_contains(a, b, x, aa, ab)

def Laws.the_fused_leaf_difference_lists_exactly_what_it_should(a, b,
  y, va, vb, inr):
  PLf2.PSet.leaf_diff_members_mem(a, b, y, va, vb, inr)

def Laws.the_fused_difference_lists_exactly_what_it_should(d, a, b, x,
  va, vb, lt):
  PSc2.PSet.missing_contains(d, a, b, x, va, vb, lt)

def Laws.a_set_whose_members_are_all_in_another_is_a_subset(d, a, b,
  va, vb, lt, am):
  PSc2.PSet.subset_of_members(d, a, b, va, vb, lt, am)

def Laws.an_ordinal_a_set_lists_is_one_of_its_members(d, a, y, va, lt,
  c):
  PSa2.PSet.member_of_to_list(d, a, y, va, lt, c)

def Laws.a_subset_of_a_subset_is_a_subset(d, a, b, c, va, vb, vc, lt,
  ab, bc):
  PSa2.PSet.subset_trans(d, a, b, c, va, vb, vc, lt, ab, bc)

def Laws.union_keeps_a_set_valid(d, a, b, va, vb):
  PVk.PSet.valid_union(d, a, b, va, vb)

def Laws.intersection_keeps_a_set_valid(d, a, b, va, vb):
  PVk.PSet.valid_inter(d, a, b, va, vb)

def Laws.difference_keeps_a_set_valid(d, a, b, va, vb):
  PVk.PSet.valid_diff(d, a, b, va, vb)

def Laws.the_union_of_two_subsets_is_a_subset(d, a, b, c, va, vb, vc,
  lt, ac, bc):
  PSa2.PSet.subset_union(d, a, b, c, va, vb, vc, lt, ac, bc)

def Laws.inserting_keeps_a_set_valid(d, s, x, dok, inv, v):
  PIvd.PSet.valid_insert(d, s, x, dok, inv, v)

def Laws.a_set_built_from_a_list_is_valid(xs, d, dok, fits):
  PIvd.PSet.valid_from_list(xs, d, dok, fits)

def Laws.the_image_of_a_frontier_is_a_valid_set(td, sd, g, a, gf, lt):
  PPm.Spec.post_valid(td, sd, g, a, gf, lt)

def Laws.a_bigger_frontier_has_a_bigger_image(td, sd, g, a, b, gf,
  lt, va, vb, ab):
  PPm.Spec.post_mono(td, sd, g, a, b, gf, lt, va, vb, ab)
