# Optimizations, and the laws that authorize them

SPEC 10.3: every optimization entry names its preconditions, law IDs,
production symbols, property tests, counterexamples, and benchmark. This is
that table. An entry with no law is not an optimization this release ships.

The performance thesis is SPEC 1.3's: **prune first, reuse second, fuse
third, parallelize last.** A GPU is an optional execution backend, not the
definition of success.

---

## 1. Structural pruning

**What.** A `PZero` or `PFull` operand answers for a whole ordinal interval
without descending into it. `PSet.union`, `PSet.inter`, `PSet.diff`,
`PSet.diff_count` and `PSet.diff_members` all take the shortcut at every
node, so a difference against a pruned subtree costs one match.

**Symbols.** `core/set.bend`: `PSet.union`, `PSet.inter`, `PSet.diff`,
`PSet.diff_count`, `PSet.diff_members`, `PSet.mk`.

**Law.** `S-04` (Boolean rewrites), instantiated at SPEC 5.3's shortcuts:
`A u Zero = A`, `A n Full = A`, `A \ Full = Zero`, `Zero \ B = Zero`.
Proved pointwise at the tile level as `tile_*_is_pointwise` in `LAWS.bend`;
the node-level shortcuts are `LAWS.pending.bend`'s `S-02`.

**Precondition.** Same immutable node, same range, same generation. Pointer
or node-id equality is a sound shortcut only inside the owning arena and
identity generation; this release does not use digest equality as an equality
axiom anywhere, and there is no hash-consing to collide.

**Checked by.** `tests.bend` boundary cases; `tools/differential.sh` object
counts against Git.

---

## 2. The fused difference reduction

**What.** For a matrix cell, `Missing = Required \ Have` is never allocated
merely to be measured. `Words.diff_count` walks two tiles accumulating
`popcount(required AND NOT have)`; `PSet.diff_members` walks two trees and
yields only the members of the difference.

**Symbols.** `core/words.bend`: `Words.diff_count`, `Words.diff_members`,
`Words.diff_any`. `core/set.bend`: `PSet.diff_count`, `PSet.diff_members`.
`query/eval.bend`: `Ev.missing_stats`, `Ev.missing_count`, `Ev.ready`.

**Law.** `Q-02` / `R-02` — `counting_a_difference_needs_no_difference` in
`LAWS.bend`: `Words.diff_count(a, b) == Words.count(Words.diff(a, b))`,
proved.

**Precondition.** Reachability is resolved *before* any ordinal-local work.
SPEC 7.2 is explicit: graph paths leave an ordinal tile and come back, so
`Reach(R) n I` is **not** the closure of `R n I` in the induced graph on `I`.
Leaf jobs here only ever see established set values. Nothing in
`query/eval.bend` truncates a traversal to a tile.

**Cost that is not free.** Weighted sums are not free with popcount. A byte
total needs the per-object weight, so `Ev.missing_stats` enumerates the
difference's members and `Ev.missing_count` — count only — stays in the word
kernel. The two paths are separate on purpose.

**Checked by.** `tests.bend`: the fused count against the built difference on
real tiles, and a reversed difference that must give a different answer.

---

## 3. Early exit on readiness

**What.** `pp git ready` stops at the first required object the inventory
does not have; `Words.any` stops at the first non-zero word.

**Symbols.** `core/words.bend`: `Words.any`, `Words.diff_any`.
`core/set.bend`: `PSet.is_empty`.

**Law.** `M-02` — `readiness_is_an_empty_difference`, proved. SPEC 4.3:
`IsEmpty` must not pay to count every result; conversely a successful exact
`Stats` query cannot stop after its first missing object, and it does not.

**Checked by.** `tools/differential.sh`: readiness agrees with an empty
missing set for both policies.

---

## 4. Set-at-a-time traversal

**What.** Each BFS round gathers the frontier's successors, subtracts `seen`
with a tree difference, and takes the remainder as the next frontier. There is
**no per-vertex membership test at all**: a round costs one pass over the
frontier's adjacency plus two tree walks, not `|frontier| * depth` lookups.

**Symbols.** `closure/reach.bend`: `Reach.go`.

**Law.** `C-02` (traversal refinement) — stated in `LAWS.pending.bend`, not
proved. Established instead, per query, by the closure certificate `C-04`
(`pp git verify`), and by the differential against the specification closure
in `tests.bend` over five graph shapes from eight root sets each.

**Precondition.** Each vertex is expanded at most once, because a vertex only
enters a frontier when it was absent from `seen`, and `seen` only grows.
Termination is an explicit decreasing `Nat` budget derived from the finite
universe, not `@unsafe`; running out returns `done = False`, which the CLI
reports as `ResourceLimit` and exit 3 rather than as an answer.

---

## 5. The tree-data policy, derived rather than labelled

**What.** SPEC 8.2's `tree-data` follows tag → target, commit → root tree,
tree → subtree and tree → blob, but not commit → parent. A commit's parents
are commits and its root tree is a tree, so dropping exactly the
commit → commit edges *is* that policy. No edge labels are stored; the
second graph is derived once at import from the types the importer already
recorded.

**Symbols.** `index/source.bend`: `Idx.tree_rows`, `Idx.filter_succ`.

**Law.** `G-02` (Git policies) — stated in `LAWS.pending.bend`, not proved.

**Checked by.** `tools/differential.sh`: `tree-data` object counts and byte
totals against `rev-parse` plus `ls-tree -r -t` with gitlinks excluded, on
three repositories.

**Precondition, and what it does not mean.** `tree-data` means enough
ordinary superproject object content to describe the selected snapshot. It
is **not** a guarantee that a checkout, build, submodule operation or smudge
filter will succeed. LFS payloads, submodule repositories, external filters,
filesystem permissions, case sensitivity and toolchains are separate
requirements (SPEC 8.2). The mode is explicit in the command and in the
result envelope's `policy` field.

---

## 6. `--batch-check` before `--batch`

**What.** Object types and sizes are read first, and only commits, trees and
tags have their bodies fetched. A blob's contents are never read.

**Symbols.** `adapters/git/git.bend`: `Git.batch_check`, `Git.batch`.
`adapters/git/import.bend`: `Imp.wanted`.

**Law.** None needed: this is an IO decision, not a semantic one. The graph
is identical either way, because a blob is terminal under both policies.

**Why it matters.** Without it, importing a repository with large blobs would
stream every byte of every blob through the parser.

---

## 7. Interning on first mention

**What.** An object id is given its ordinal the first time it is *mentioned* —
as a root, or as a child inside a commit, tag or tree — not when it is
fetched. So a child gets an ordinal long before its body is read, ordinals
are assigned in discovery order, and the adjacency rows come out dense and in
order with an empty row for every blob.

**Symbols.** `adapters/git/intern.bend`: `Uni.intern`.

**Law.** `U-01` (identity mapping) — stated in `LAWS.pending.bend`. The
injectivity is by construction: an ordinal is handed out once per distinct
complete key, and the bucket compares the complete key, never a prefix or a
digest.

---

## 8. Sparse and dense leaves

**What.** A leaf covering 4096 ordinals is stored as a sorted offset list
below 64 members and as 128 bitmap words above it. `PSet.compress` picks, and
`PZero`/`PFull` collapse a leaf that is empty or complete.

**Symbols.** `core/set.bend`: `PSet.compress`, `PSet.sparse_max`.

**Law.** `S-03` (representation conversion) — stated in
`LAWS.pending.bend`, not proved.

**Precondition.** 64 is a benchmark parameter, not a semantic constant.
Nothing outside `PSet.compress` and `PSet.add.leaf.fit` reads it, and
changing it must change no denotation.

**Checked by.** `tests.bend`: the crossover at 64 and 65 members preserves
membership and size.

---

## 9. What is deliberately absent

These would be optimizations if they were sound. They are not.

| Rewrite | Why not |
|---|---|
| `C(A n B) = C(A) n C(B)` | false: with `a -> x` and `b -> x`, the closures meet at `x` although the root sets do not. `tests.bend` runs the counterexample. |
| `C(A \ B) = C(A) \ C(B)` | false: closing `{a} \ {b}` keeps `x`, subtracting the closures removes it. `tests.bend` runs it. |
| pushing a type filter through `Reach` | false without a separately proved graph-policy transformation: dropping commit vertices before traversal erases the paths to the blobs they require (SPEC 4.1). `Den.filter` and `Ev.filter` are applied *after* closure, never pushed. |
| `Stats(A u B) = Stats(A) + Stats(B)` | false without disjointness: overlapping members are double-counted (SPEC 4.3). Statistics come from one enumeration of one set. |
| `lift(Full_old) = Full_new` | false once the universe grows: `Full` means full within a node's *valid* range, and unused bitmap capacity must never read as membership (SPEC 5.5). |
| `Reach(R) n tile = Reach_in_induced_tile(R n tile)` | false: graph paths leave a tile and return. Reachability is resolved before any ordinal-local work. |
| resolving an invalid input after a rewrite eliminated it | forbidden by SPEC 3.5. Structurally impossible here: a literal carries its set value, so an unresolved input cannot be represented in an expression at all. |

---

## 10. Measured, and what it cost

`docs/evidence/T01.md` has the substrate experiment. Two numbers shaped the
code:

* Handing one host-built operand list to every leaf costs an atomic per
  operand per fork level and ran **~12x slower** than leaf-owned tiles
  (178 ms against 15 ms, 2^16 leaves x 128 words). So the planner's rule is
  that a leaf job owns the words it reads. `bench/spike_t01.bend` is the
  regression that catches a change which starts broadcasting again.

* CPU and Metal returned identical sums on every trial. That is the M0
  equality evidence; it is not a speed claim, and `auto` does not dispatch to
  Metal at the sizes this release handles.
