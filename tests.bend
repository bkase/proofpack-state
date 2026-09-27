# tests.bend -- the executable checks.
#
# Three kinds, run by `tools/test.sh`:
#
#   * **Counterexamples.** SPEC 4.1 forbids distributing closure over
#     intersection or difference and names the witness: a -> x and b -> x.
#     These run that witness and *fail the build if the forbidden identity
#     ever starts holding*, which is the only way an accidental rewrite gets
#     caught.
#
#   * **Boundaries.** SPEC 11.2's bitmap positions -- 0, 1, 31, 32, 33, 4095,
#     4096, 4097 -- plus tail masking, sparse/dense conversion at the
#     crossover, and padding bits that must never count as objects.
#
#   * **Differentials.** The production frontier traversal against the
#     specification closure of spec/closure.bend, which recomputes post over
#     the whole set every round; and the closure certificate against both,
#     including tampered closures it must reject.
#
# A check that passes prints `ok`; one that fails prints `FAIL` and the
# program exits 1.

import Base
import ./core/count.bend as C
import ./core/word.bend as W
import ./core/words.bend as Wo
import ./core/ords.bend as O
import ./core/set.bend as S
import ./core/trie.bend as T
import ./closure/graph.bend as G
import ./closure/reach.bend as R
import ./closure/explain.bend as E
import ./closure/cert.bend as Ct
import ./spec/closure.bend as Sp
import ./query/eval.bend as Ev
import ./index/source.bend as Idx
import ./adapters/git/oid.bend as Oid
import ./adapters/git/intern.bend as In
import ./adapters/git/import.bend as Im

type Case is Data:
  Case{name: String, ok: Bool}

def Case.ok(c: Case) -> Bool:
  match c:
    case Case{name, ok}:
      ok

def Case.mark(ok: Bool) -> String:
  match ok:
    case True{}:
      "ok  "
    case False{}:
      "FAIL"

# ---------------------------------------------------------------------------
# The graph of SPEC 4.1's counterexample: a -> x, b -> x, and nothing else.
# Ordinals: a = 0, b = 1, x = 2.
# ---------------------------------------------------------------------------

def Case.line(c: Case) -> String:
  match c:
    case Case{name, ok}:
      Case.mark(ok) ++ " " ++ name

def Tests.depth() -> Nat:
  8n

def Tests.sd() -> Nat:
  1n

def Tests.diamond() -> G.Graph:
  T.Trie.of_list(G.Succ, Tests.depth(), [[2], [2], Nil{}])

def Tests.set(xs: List<&2, U32>) -> S.PSet:
  S.PSet.from_list(Tests.sd(), xs)

def Tests.close(g: G.Graph, xs: List<&2, U32>) -> S.PSet:
  Sp.Spec.closure(8n, Tests.depth(), g, Tests.sd(), Tests.set(xs))

def Tests.same(a: S.PSet, b: S.PSet) -> Bool:
  +x = a
  +y = b
  Bool.and(S.PSet.is_subset(Tests.sd(), x, y),
    S.PSet.is_subset(Tests.sd(), y, x))

# C({a} n {b}) is empty; C({a}) n C({b}) holds x. They must differ.
def Tests.forbidden_intersection() -> Case:
  +g = Tests.diamond()
  +lhs = Tests.close(g, Nil{})
  +rhs = S.PSet.inter(Tests.sd(), Tests.close(g, [0]), Tests.close(g, [1]))
  Case{"closure does not distribute over intersection",
    Bool.not(Tests.same(lhs, rhs))}

# C({a} \ {b}) keeps x; C({a}) \ C({b}) removes it. They must differ.
def Tests.forbidden_difference() -> Case:
  +g = Tests.diamond()
  +lhs = Tests.close(g, [0])
  +rhs = S.PSet.diff(Tests.sd(), Tests.close(g, [0]), Tests.close(g, [1]))
  Case{"closure does not distribute over difference",
    Bool.not(Tests.same(lhs, rhs))}

# What closure *does* preserve: finite unions (law C-03).
def Tests.union_preserved() -> Case:
  +g = Tests.diamond()
  +lhs = Tests.close(g, [0, 1])
  +rhs = S.PSet.union(Tests.sd(), Tests.close(g, [0]), Tests.close(g, [1]))
  Case{"closure preserves unions", Tests.same(lhs, rhs)}

def Tests.empty_closed() -> Case:
  +g = Tests.diamond()
  Case{"closure of the empty set is empty",
    S.PSet.empty_p(Tests.sd(), Tests.close(g, Nil{}))}

def Tests.extensive() -> Case:
  +g = Tests.diamond()
  Case{"closure contains its roots",
    S.PSet.is_subset(Tests.sd(), Tests.set([0]), Tests.close(g, [0]))}

def Tests.idempotent() -> Case:
  +g = Tests.diamond()
  +once = Tests.close(g, [0])
  +twice = Sp.Spec.closure(8n, Tests.depth(), g, Tests.sd(), once)
  Case{"closure is idempotent", Tests.same(once, twice)}

# An isolated root is in its own closure (SPEC 3.3).
def Tests.isolated_root() -> Case:
  +g = Tests.diamond()
  Case{"an isolated root is in its own closure",
    S.PSet.member(Tests.sd(), Tests.close(g, [2]), 2)}

# A cycle terminates and closes (SPEC 3.2: the generic core handles cycles).
def Tests.cycle() -> Case:
  +g = {T.Trie.of_list(G.Succ, Tests.depth(), [[1], [2], [0]]) : G.Graph}
  Case{"a cycle closes and terminates",
    Nat.is_eq(S.PSet.size(Tests.sd(), Tests.close(g, [0])), 3n)}

# ---------------------------------------------------------------------------
# Bitmap boundaries (SPEC 11.2).
# ---------------------------------------------------------------------------

def Tests.big_sd() -> Nat:
  2n

def Tests.bits() -> List<&2, U32>:
  [0, 1, 31, 32, 33, 4095, 4096, 4097]

def Tests.each_present(+s: S.PSet, xs: List<&2, U32>, ok: Bool) -> Bool:
  match xs:
    case Nil{}:
      ok
    case Con{x, t}:
      match ok:
        case False{}:
          False{}
        case True{}:
          Tests.each_present(s, t, S.PSet.member(Tests.big_sd(), s, x))

def Tests.boundaries() -> Case:
  +s = S.PSet.from_list(Tests.big_sd(), Tests.bits())
  Case{"bitmap boundaries 0 1 31 32 33 4095 4096 4097 all present",
    Bool.and(Tests.each_present(s, Tests.bits(), True{}),
      Nat.is_eq(S.PSet.size(Tests.big_sd(), s), 8n))}

# A position not inserted must be absent, whatever the representation did
# with its neighbours. This is the padding-bit check: 4098 sits in the same
# word as 4097 and must not be counted.
def Tests.no_extra_bits() -> Case:
  +s = S.PSet.from_list(Tests.big_sd(), Tests.bits())
  Case{"a neighbouring padding bit is not a member",
    Bool.not(Bool.or(S.PSet.member(Tests.big_sd(), s, 4098),
      S.PSet.member(Tests.big_sd(), s, 30)))}

# The sparse/dense crossover changes the representation and not the set
# (law S-03).
def Tests.upto(+n: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      Tests.upto(p, Con{U32.from_nat(p), acc})

def Tests.crossover() -> Case:
  +sparse = S.PSet.from_list(Tests.big_sd(), Tests.upto(64n, Nil{}))
  +dense = S.PSet.from_list(Tests.big_sd(), Tests.upto(65n, Nil{}))
  Case{"the sparse/dense crossover preserves membership",
    Bool.and(Nat.is_eq(S.PSet.size(Tests.big_sd(), sparse), 64n),
      Bool.and(Nat.is_eq(S.PSet.size(Tests.big_sd(), dense), 65n),
        S.PSet.member(Tests.big_sd(), dense, 64)))}

# The tail mask: bit i of mask(k) is set exactly when i is inside the word
# and below k. Checked at the ends, where an off-by-one would live.
def Tests.mask_bits() -> Case:
  +m = W.U32.mask(5n)
  Case{"mask(5) holds bits 0..4 and nothing above",
    Bool.and(W.U32.bit(m, 4n),
      Bool.and(Bool.not(W.U32.bit(m, 5n)),
        Bool.not(W.U32.bit(W.U32.mask(0n), 0n))))}

def Tests.mask32() -> Case:
  +m = W.U32.mask(32n)
  Case{"mask(32) holds bit 31 and reads absent past the word",
    Bool.and(W.U32.bit(m, 31n), Bool.not(W.U32.bit(m, 32n)))}

# The fused count against the built difference, on real tiles.
def Tests.fused_count() -> Case:
  +a = {[4294967295, 255, 0, 4096] : List<&2, U32>}
  +b = {[15, 255, 4294967295] : List<&2, U32>}
  Case{"the fused count equals counting the built difference",
    Nat.is_eq(Wo.Words.diff_count(a, b),
      Wo.Words.count(Wo.Words.diff(a, b)))}

# Reversing a difference is not the same difference -- the mutation test of
# SPEC 11.2.
def Tests.reversed_difference() -> Case:
  +a = {[4294967295, 0] : List<&2, U32>}
  +b = {[15, 0] : List<&2, U32>}
  Case{"a reversed difference is a different answer",
    Bool.not(Nat.is_eq(Wo.Words.diff_count(a, b),
      Wo.Words.diff_count(b, a)))}

# ---------------------------------------------------------------------------
# Differentials. The production frontier traversal against the specification
# closure, which recomputes post over the whole set every round (SPEC 11.1's
# first independent comparison, run in-process).
#
# Five graphs on four vertices: a chain, a diamond, a cycle, a self-loop,
# and a graph with an unreachable component -- the shapes SPEC 11.2 calls
# for, small enough that every one is checked exhaustively from every root.
# ---------------------------------------------------------------------------

def Tests.graphs() -> List<&2, G.Graph>:
  [T.Trie.of_list(G.Succ, Tests.depth(), [[1], [2], [3], Nil{}]),
    T.Trie.of_list(G.Succ, Tests.depth(), [[1, 2], [3], [3], Nil{}]),
    T.Trie.of_list(G.Succ, Tests.depth(), [[1], [2], [0], Nil{}]),
    T.Trie.of_list(G.Succ, Tests.depth(), [[0], [1], Nil{}, Nil{}]),
    T.Trie.of_list(G.Succ, Tests.depth(), [[1], Nil{}, [3], [2]])]

def Tests.roots() -> List<&2, List<&2, U32>>:
  [Nil{}, [0], [1], [2], [3], [0, 3], [1, 2], [0, 1, 2, 3]]

def Tests.agree(g: G.Graph, +rs: List<&2, U32>) -> Bool:
  +gg = g
  +spec = Sp.Spec.closure(8n, Tests.depth(), gg, Tests.sd(),
    Tests.set(rs))
  +prod = R.Reach.seen(Tests.sd(),
    R.Reach.closure(8n, Tests.depth(), gg, Tests.sd(), rs))
  Tests.same(spec, prod)

def Tests.agree_roots(+g: G.Graph, rss: List<&2, List<&2, U32>>,
  ok: Bool) -> Bool:
  match rss:
    case Nil{}:
      ok
    case Con{rs, t}:
      match ok:
        case False{}:
          False{}
        case True{}:
          Tests.agree_roots(g, t, Tests.agree(g, rs))

def Tests.agree_all(gs: List<&2, G.Graph>, ok: Bool) -> Bool:
  match gs:
    case Nil{}:
      ok
    case Con{g, t}:
      match ok:
        case False{}:
          False{}
        case True{}:
          Tests.agree_all(t, Tests.agree_roots(g, Tests.roots(), True{}))

def Tests.differential() -> Case:
  Case{"the frontier traversal agrees with the specification closure",
    Tests.agree_all(Tests.graphs(), True{})}

# ---------------------------------------------------------------------------
# The closure certificate (law C-04). It must accept the traversal's own
# output, and reject a closure that has been tampered with in either
# direction: an extra member that is not reachable, and a missing member that
# is.
# ---------------------------------------------------------------------------

def Tests.cert_of(g: G.Graph, rs: List<&2, U32>, c: S.PSet) -> Bool:
  +gg = g
  +rr = rs
  Ct.Cert.check(Tests.depth(), gg, Tests.sd(), rr,
    R.Reach.levels(Tests.sd(),
      R.Reach.closure(8n, Tests.depth(), gg, Tests.sd(), rr)), c)

def Tests.cert_accepts() -> Case:
  +g = Tests.diamond()
  Case{"the certificate accepts the traversal's own closure",
    Tests.cert_of(g, [0], R.Reach.seen(Tests.sd(),
      R.Reach.closure(8n, Tests.depth(), g, Tests.sd(), [0])))}

def Tests.cert_rejects_extra() -> Case:
  +g = Tests.diamond()
  Case{"the certificate rejects an unreachable extra member",
    Bool.not(Tests.cert_of(g, [0], Tests.set([0, 1, 2])))}

def Tests.cert_rejects_missing() -> Case:
  +g = Tests.diamond()
  Case{"the certificate rejects a closure missing a reachable member",
    Bool.not(Tests.cert_of(g, [0], Tests.set([0])))}

# ---------------------------------------------------------------------------
# Witnesses (law E-01). A produced path must check; a fabricated one must
# not -- neither a path that skips an edge nor one that starts off-root.
# ---------------------------------------------------------------------------

def Tests.witness() -> Case:
  +g = {T.Trie.of_list(G.Succ, Tests.depth(),
    [[1], [2], [3], Nil{}]) : G.Graph}
  +lv = R.Reach.levels(Tests.sd(),
    R.Reach.closure(8n, Tests.depth(), g, Tests.sd(), [0]))
  Case{"a produced witness checks",
    E.Explain.valid(Tests.depth(), g, [0],
      E.Explain.path(Tests.depth(), g, lv, 3), 3)}

def Tests.witness_skips_an_edge() -> Case:
  +g = {T.Trie.of_list(G.Succ, Tests.depth(),
    [[1], [2], [3], Nil{}]) : G.Graph}
  Case{"a witness that skips an edge is rejected",
    Bool.not(E.Explain.valid(Tests.depth(), g, [0], [0, 3], 3))}

def Tests.witness_off_root() -> Case:
  +g = {T.Trie.of_list(G.Succ, Tests.depth(),
    [[1], [2], [3], Nil{}]) : G.Graph}
  Case{"a witness that does not start at a requested root is rejected",
    Bool.not(E.Explain.valid(Tests.depth(), g, [0], [1, 2, 3], 3))}

# ---------------------------------------------------------------------------
# An unfinished traversal must not be reported as a complete answer.
#
# `Reach.go` returns `done = False` when its budget runs out, and SPEC 3.3
# says the caller must report that rather than dress it up. The evaluator
# reacts by emptying its own stack, so the machine stops -- and this checks
# that stopping that way is a failure and not a success.
# ---------------------------------------------------------------------------

def Tests.src() -> Idx.Source:
  Idx.Src{Oid.Sha1{}, 0n, In.Uni.new(Oid.Sha1{}),
    T.Trie.gap(G.Succ), T.Trie.gap(G.Succ), T.Trie.gap(Im.Meta),
    T.Trie.gap(Oid.Oid), Nil{}, Nil{}, Nil{}, Nil{}}

def Tests.unfinished_traversal() -> Case:
  Case{"an unfinished traversal is not reported as a complete answer",
    Bool.not(Ev.Val.ok(Ev.Ev.go(4n, Tests.src(),
      Ev.CVal{Tests.set([1])},
      Ev.Ev.reach.stack(False{}, [Ev.FFilter{0}]), False{})))}

# ---------------------------------------------------------------------------
# The runner.
# ---------------------------------------------------------------------------

# P-01: a dense leaf that is not 128 words wide loses the bit it was given,
# because `Words.set` past the end of a tile changes nothing.
def Tests.insert_needs_a_wide_enough_tile() -> Case:
  +s = {S.PDense{Nil{}} : S.PSet}
  +got = S.PSet.member(0n, S.PSet.insert(0n, s, 0), 0)
  Case{"a narrow dense leaf loses an inserted ordinal (P-01 hypothesis)",
    Bool.and(Bool.not(got),
      Bool.not(S.PSet.valid(0n, {S.PDense{Nil{}} : S.PSet}, True{})))}

# S-02: at a leaf, `PFull` means the leaf's own 4096 ordinals, but converting
# it to words gives a tile that reads `False{}` past 4096. So the pointwise
# difference law needs the ordinal to be inside the leaf.
def Tests.leaf_difference_needs_an_in_range_ordinal() -> Case:
  +a = {S.PFull{} : S.PSet}
  +b = {S.PDense{Wo.Words.ones(128n)} : S.PSet}
  +lhs = S.PSet.mem(0n, S.PSet.diff(0n, a, b), 0, 4096)
  +rhs = Bool.and(S.PSet.mem(0n, {S.PFull{} : S.PSet}, 0, 4096),
    Bool.not(S.PSet.mem(0n,
      {S.PDense{Wo.Words.ones(128n)} : S.PSet}, 0, 4096)))
  Case{"a leaf difference past 4096 is not pointwise (S-02 hypothesis)",
    Bool.and(Bool.not(lhs), rhs)}

# S-02 again, above the leaf: a sparse payload at a node is a shape
# `PSet.valid` rejects, and the node operations read it as empty while
# `PSet.mem` reads it as a member.
def Tests.node_union_needs_a_valid_shape() -> Case:
  +a = {S.PSparse{[5]} : S.PSet}
  +h = S.PSet.half(1n)
  +lhs = S.PSet.mem(1n, S.PSet.union(1n, a, {S.PZero{} : S.PSet}), h, 5)
  +rhs = Bool.or(S.PSet.mem(1n, {S.PSparse{[5]} : S.PSet}, h, 5),
    S.PSet.mem(1n, {S.PZero{} : S.PSet}, h, 5))
  Case{"a sparse payload above a leaf breaks the union law (S-02 hypothesis)",
    Bool.and(Bool.not(lhs),
      Bool.and(rhs,
        Bool.not(S.PSet.valid(1n, {S.PSparse{[5]} : S.PSet}, True{}))))}

# S-03: compression to `PFull` says "the whole leaf", which disagrees with the
# tile it came from past 4096.
def Tests.compress_needs_an_in_range_ordinal() -> Case:
  +lhs = S.PSet.mem(0n, S.PSet.compress(Wo.Words.ones(128n)), 0, 4096)
  +rhs = S.PSet.mem(0n,
    {S.PDense{Wo.Words.ones(128n)} : S.PSet}, 0, 4096)
  Case{"compression past 4096 is not member-preserving (S-03 hypothesis)",
    Bool.and(lhs, Bool.not(rhs))}

def Tests.all() -> List<&2, Case>:
  [Tests.forbidden_intersection(), Tests.forbidden_difference(),
    Tests.union_preserved(), Tests.empty_closed(), Tests.extensive(),
    Tests.idempotent(), Tests.isolated_root(), Tests.cycle(),
    Tests.boundaries(), Tests.no_extra_bits(), Tests.crossover(),
    Tests.mask_bits(), Tests.mask32(), Tests.fused_count(),
    Tests.reversed_difference(), Tests.differential(),
    Tests.cert_accepts(), Tests.cert_rejects_extra(),
    Tests.cert_rejects_missing(), Tests.witness(),
    Tests.witness_skips_an_edge(), Tests.witness_off_root(),
    Tests.insert_needs_a_wide_enough_tile(),
    Tests.leaf_difference_needs_an_in_range_ordinal(),
    Tests.node_union_needs_a_valid_shape(),
    Tests.compress_needs_an_in_range_ordinal(),
    Tests.unfinished_traversal()]

# ---------------------------------------------------------------------------
# Why the leaf laws carry hypotheses.
#
# Four of the obligations in LAWS.pending.bend were first written without
# them, and were false. These run the counterexamples, so that anyone who
# "strengthens" a law by deleting its hypothesis fails the build instead of
# shipping a false claim. Each of these values is one `PSet.valid` rejects,
# which is why the hypotheses are the structural invariant rather than an
# invention.
# ---------------------------------------------------------------------------

def Tests.bump(ok: Bool, bad: Nat) -> Nat:
  match ok:
    case True{}:
      bad
    case False{}:
      1n+bad

def Tests.report(cs: List<&2, Case>, bad: Nat) -> IO(Nat):
  match cs:
    case Nil{}:
      IO.pure(Nat, bad)
    case Con{c, t}:
      +cc = c
      do IO<Nat>:
        IO.print(Case.line(cc))
        Tests.report(t, Tests.bump(Case.ok(cc), bad))

def Tests.finish(bad: Nat) -> IO(Unit):
  match bad:
    case 0n:
      IO.print("all checks passed")
    case 1n+p:
      do IO<Unit>:
        IO.print(Nat.show(1n+p) ++ " checks FAILED")
        IO.die(Unit, 1, "")

def main() -> IO(Unit):
  do IO<Unit>:
    bad : Nat <- Tests.report(Tests.all(), 0n)
    Tests.finish(bad)
