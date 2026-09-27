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
# currently 14. That count is the point of the file, so the command "failing"
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
import ./core/trie.bend as T
import ./closure/graph.bend as G
import ./closure/reach.bend as R
import ./spec/closure.bend as Sp
import ./query/ast.bend as A
import ./query/rewrite.bend as Rw
import ./spec/query.bend as Den
import ./index/source.bend as Idx
import ./closure/cert.bend as Ct
import ./query/eval.bend as Ev

# ===========================================================================
# S-02, S-03 -- the persistent set, above the tile.
#
# The tile laws are proved (`tile_difference_is_pointwise` and friends in
# LAWS.bend). What is open is lifting them through the tree: that a node
# operation's membership is the pointwise Boolean at every depth, and that
# compressing a leaf to `PZero`, `PFull`, a sparse offset list or 128 dense
# words never changes which ordinals it holds.
#
# Backed by: the differential in tests.bend (the production traversal, which
# uses these operations throughout, against the specification closure), and
# by tools/differential.sh against Git on real repositories.
# ===========================================================================

law set_difference_is_pointwise:
  for +d: Nat
  for a: S.PSet
  for b: S.PSet
  for +h: U32
  for +x: U32
  {S.PSet.mem(d, S.PSet.diff(d, a, b), h, x)
    == Bool.and(S.PSet.mem(d, a, h, x),
         Bool.not(S.PSet.mem(d, b, h, x))) : Bool}

law set_union_is_pointwise:
  for +d: Nat
  for a: S.PSet
  for b: S.PSet
  for +h: U32
  for +x: U32
  {S.PSet.mem(d, S.PSet.union(d, a, b), h, x)
    == Bool.or(S.PSet.mem(d, a, h, x), S.PSet.mem(d, b, h, x)) : Bool}

law set_intersection_is_pointwise:
  for +d: Nat
  for a: S.PSet
  for b: S.PSet
  for +h: U32
  for +x: U32
  {S.PSet.mem(d, S.PSet.inter(d, a, b), h, x)
    == Bool.and(S.PSet.mem(d, a, h, x), S.PSet.mem(d, b, h, x)) : Bool}

# S-03: the sparse/dense crossover is a storage decision, not a semantic one.
law compressing_a_leaf_keeps_its_members:
  for +ws: List<&2, U32>
  for +x: U32
  {S.PSet.mem(0n, S.PSet.compress(ws), 0, x)
    == S.PSet.mem(0n, S.PDense{ws}, 0, x) : Bool}

# P-01: a persistent update must not disturb the set it was derived from.
# Here as the weaker, checkable half -- the new root has the member added --
# because "every retained old root has an unchanged denotation" is a
# statement about sharing that Bend's affine values make true by
# construction and that this release does not state formally.
law inserting_adds_exactly_that_ordinal:
  for +d: Nat
  for s: S.PSet
  for +x: U32
  {S.PSet.member(d, S.PSet.insert(d, s, x), x) == True{} : Bool}

# ===========================================================================
# C-01, C-02, C-03 -- closure.
#
# C-01 is the least-fixed-point characterisation: C(R) is the least
# edge-closed set containing R. `Spec.closure` iterates X |-> X u post(X)
# from R, which is that definition operationally; what is open is that the
# iteration reaches the fixed point within the universe's size, which needs
# the pigeonhole argument this release has not written.
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

law closure_contains_its_roots:
  for +n: Nat
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +r: S.PSet
  {S.PSet.is_subset(sd, r, Sp.Spec.closure(n, td, g, sd, r))
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
# Q-01, Q-03 -- the query compiler.
#
# Q-01: every rewrite `Rw.simplify` performs preserves denotation. The
# rewrites it performs are small and each is an instance of a Boolean law
# already proved at the tile level; what is open is the statement over the
# whole expression.
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
  for e: A.SetExpr
  for +x: U32
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
# G-01, G-02, G-03 -- the Git adapter.
#
# These are the obligations that cross out of the algebra and into a real
# repository, and they are the ones a proof can least reach: G-01 is about a
# byte grammar, G-02 about matching Git's own semantics, G-03 about a
# projection between two universes.
#
# Backed by: tools/differential.sh, which checks both policies and the
# inventory against independent Git plumbing on three repositories, over a
# corpus that includes a merge, a tag to a tag, a tag to a tree, a tag to a
# blob, a symlink, a zero-byte blob, a non-UTF-8 tree entry name and a
# gitlink with no submodule present.
# ===========================================================================

# The row-level half of G-02 is now proved unconditionally and lives in
# LAWS.bend as `a_filtered_row_drops_exactly_the_commit_targets`: an ordinal
# survives `Idx.filter_succ` exactly when it was in the successor row and is
# not itself a commit.
#
# What remains open is the lift from a row to `Graph.edge`. Both adjacency
# tables are `Trie.of_list` over positionally parallel lists, so the lift
# reduces to a single missing lemma -- that a trie built from a list answers,
# at ordinal `x`, the element of that list at position `x`:
#
#     Trie.at(A, d, Trie.of_list(A, d, xs), x)  ==  the element of xs at x
#
# and that needs arithmetic this release has not proved: that `U32.is_lt`
# agrees with the order on `U32.to_nat`, and that `U32.sub` is subtraction
# when it does not borrow. Both are bit-vector facts about the descent, not
# about the policy.
law the_tree_data_policy_drops_exactly_the_parent_edges:
  for +src: Idx.Source
  for +u: U32
  for +v: U32
  {G.Graph.edge(32n, Idx.Source.graph(src, Idx.PTreeData{}), u, v)
    == Bool.and(G.Graph.edge(32n, Idx.Source.graph(src, Idx.PFull{}), u, v),
         Bool.not(Bool.and(Idx.Idx.is_commit(Idx.Source.meta_of(src, u)),
           Idx.Idx.is_commit(Idx.Source.meta_of(src, v))))) : Bool}

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
# I-02, I-03, U-02 -- incremental reuse.
#
# Still not applicable. `pp` re-imports a generation rather than extending
# one: there is no graph append, no cache binding and no generation lifting in
# this release, so there is nothing yet for these to constrain.
# ===========================================================================
