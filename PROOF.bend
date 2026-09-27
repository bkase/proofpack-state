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

import Base
import ./LAWS.bend as Laws
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
import ./proofs/ords.bend as POr
import ./proofs/bitset.bend as PBs
import ./proofs/leaf.bend as PLf
import ./proofs/witness.bend as PWit

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
  POr.Ords.elem_insert(xs, x)

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
