# ProofPack State

`pp` is a read-only Git state calculator with a proved finite-set and
reachability core, written in [Bend2](https://github.com/bendlang/bend).

Given a set of roots (refs) in a source repository and the object inventory
of some other store (a mirror, a worker's partial clone, a cache), it answers
exactly:

| Question | Command | Meaning |
|---|---|---|
| Which objects are missing? | `pp git missing` | the closure of the roots, minus what the receiver reports having |
| Is this store ready for this requirement? | `pp git ready` | set inclusion at a recorded observation, not a live lease |
| Which of many caches is closest? | `pp git matrix` | one requirement against many inventories, from one load |
| What is retained only by these roots? | `pp git retention` | reachability difference against an explicit retained-root set |
| Why is this object required? | `pp git explain` | one checked root-to-object dependency path |

The library, not `git rev-list`, computes closure, set algebra, missing state
and batch plans. Git supplies object bodies and metadata through `cat-file`
and nothing else. The algebra that produces every number is stated as laws
and proved; the traversal is certified per query; everything that touches a
real repository is named as trusted. Nothing is ever written to the
repository being read.

This README describes the whole system. The three companion documents are
normative where they overlap with it:

* `TRUST.md`: what is proved, what is checked at run time, what is trusted.
* `OPTIMIZATIONS.md`: every optimization, the law that authorizes it, and how it is checked.
* `docs/MODULES.md`: the module layout and the toolchain rules that shaped it.

The original design handoff that this implementation was built from is in
`proofpack-handoff/PROOFPACK_SPEC.md`. Comments throughout the code cite it as
"SPEC §n".

---

## 1. Current state

As of 28 September 2026, on the `main` branch:

**The release gate is green.** `tools/gate.sh` runs eight steps and all pass on
this machine: every module typechecks; `bend PROOF.bend` discharges every law
in `LAWS.bend`; `bend PROOF.bend --safe` rechecks them with the BendTT kernel
(which has a Lean proof) and excludes nothing; `tests.bend` passes; `pp`
builds; and the Git differential agrees with independent Git plumbing on every
case, including the derived store round trip and four injected corruptions.

**What has been built**, by the specification's milestones:

| Milestone | Status |
|---|---|
| M0 semantic and substrate spike | done: checked words, tile kernel, specification closure, the memory-substrate experiment (`docs/evidence/T01.md`) |
| M1 first Git utility | done: importer, `full` and `tree-data` policies, `missing`, `ready`, `explain`, `retention`, `inventory`, `verify`, JSON envelopes, closure certificates, Git differential |
| M2 persistent algebra | partly done: the persistent set with sparse and dense leaves, and a derived store (`pp git import` then `--graph NAME`). Not done: inventory patches, checkpoint closures, generation lifting |
| M3 query compiler | mostly done: typed AST, validated rewrites, fused statistics, explanations, `matrix` with inventory deduplication. Not done: leaf-operand pair reuse across cells, tiling of very large matrices |
| M4 accelerated v0.1 | partly done: production native executor, a real Metal leaf path with honest backend reporting, cross-checked on every query. Not done: an automatic cost threshold that ever chooses Metal, incremental graph append |

**What is proved.** 137 laws in `LAWS.bend`, discharged by `PROOF.bend`. They
cover the word and tile kernels, the fused count, the statistics monoid, the
least-missing theorem and the checked accumulator, and -- as of this release --
the set algebra itself:

* `S-02`: difference, union and intersection are pointwise at the production
  depth, for structurally valid operands and every `U32` ordinal.
* `S-03`: compression changes no member, whichever of its four
  representations it picks.
* `S-04`: the emptiness test only accepts a set with no members, so the three
  admitted Boolean rewrites preserve membership.
* `P-01`: `PSet.insert` pinned down at every ordinal -- the ordinal inserted
  is present, nothing already there is lost, and nothing else is added -- so a
  set folded up from a list has exactly the ordinals on that list, which is
  how the universe, a filter's result and a projected inventory all get built.
* `U-01` (round trip): interning an object id and then looking it up finds
  the ordinal that interning returned -- resting on the trie reading back
  what was written, which needs no hypothesis at all.
* `Q-01`: every rewrite the query optimizer performs keeps the denotation,
  stated over the emptiness decision as the rewriter computes it. The set
  operations keep a set in the shape the pointwise laws need, so every
  denotation is well shaped and the rewrites' hypothesis discharges itself.
* the enumeration: `PSet.to_list` lists exactly the ordinals `PSet.member`
  accepts, for an ordinal inside the universe and any set that passed
  `PSet.valid` -- the check a decoded set is already put through. The leaf
  arm is the shift law over the leaf law, the full-node arm is the count-down
  being the node's interval, and the branch arm is the two walks -- one
  comparing against the half, one masking one bit narrower -- arriving at the
  same ordinal.
* plus the addressing arithmetic all of that rests on -- that `U32` addition
  adds, that a word is determined by the number it reads as, that the tile
  address is injective, and that the enumeration walk and the tile address
  name the same positions.

Two of the three Git-adapter obligations are now proved in full. `G-02`: the
tree-data filter at a row, and the lift to `Graph.edge` over the two
assembled adjacency tables. `G-03`: the inventory projection contains the
ordinal of every reported id the universe names, and nothing else.

`E-01` is closed in the form the product guarantees it: two parts hold of any
produced witness, and all three hold of a *returned* one, because
`pp git explain` runs the checker and exits non-zero when it fails.

Partly proved, with the remaining half stated precisely: `C-01` (the closure
contains its roots, and a round that changes nothing has reached an
edge-closed set), `C-03` (closing nothing gives nothing -- pointwise as well
as at `PZero`), `C-04` (what an accepted certificate means), `U-01` (the
lookup round trip; injectivity is open), `Q-01` (every rewrite the optimizer
performs; the whole pass is open), `Q-04` (the matrix restores the caller's
positions, and what a reused answer is), `D-01` (what structural validity
rules out). Section 4 below lists each law with the optimization it
unlocks.

Four of the laws in `LAWS.pending.bend` turned out to be **false** as first
written -- each was missing the structural invariant `PSet.valid` states -- and
each counterexample now runs on every build. They have been restated with the
hypothesis they need, and `P-01` was then proved outright. `TRUST.md` §1 has
the list.

Every obligation this release is subject to now has something proved about
it: 17 discharged in full, 10 in part with the remaining half stated
precisely in `LAWS.pending.bend`, and 5 not applicable until a later
milestone.

**What is checked at run time instead.** The closure traversal (by the
certificate `pp git verify` runs), dependency witnesses (by an independent
checker), and the whole pipeline (by differential tests against a slow
specification evaluator and against Git itself). These are stated as open
laws in `LAWS.pending.bend`.

**What is measured.** `docs/evidence/T06.md` measures the acceptance workload
(one requirement against many inventories) on a 31,516-object repository.
Against a competent `rev-list` plus `comm` baseline, with small inventories
(the case the product is for), `pp` costs 81.8% less per cell, crosses over
between 4 and 8 cells, and is 2.9x faster at 32 cells, with a 0.1% noise
floor. With near-full inventories no speed claim is made, and the benchmark
script refuses to make one. No GPU speed claim is made anywhere.

**Known gaps and stale labels**, worth knowing before reading further:

* Every result envelope reports `"lineage": "ephemeral"`, including answers
  from a stored generation. The store exists; the envelope has not caught up.
* `D-01` is live but unstated: the store has full structural validation on
  load, which is the check `D-01` would be stated over, and
  `tools/differential.sh` rejects four kinds of corruption -- but the law
  itself is not yet written.
* `OPTIMIZATIONS.md` §4 describes a set-at-a-time traversal. The traversal
  was changed to per-vertex when the set-at-a-time shape proved quadratic on
  long commit chains (see `closure/reach.bend`). The law situation is
  unchanged; the description is stale.
* `auto` never dispatches to Metal. `--backend metal` does, and the result is
  checked byte-for-byte against the CPU path, but no size has yet been
  measured where the GPU wins after planning and dispatch.
* At most 2^32-1 ordinals per universe, and byte totals are capped at
  2^48-1. Both are documented limits with explicit rejection, not wraparound.
* Single writer, no locking on the derived store. Two concurrent imports of
  the same name race; the loser is replaced, never corrupted.

---

## 2. Quick start

### Toolchain

Everything runs on one pinned Bend release, verified by sha256 against the
hash in the pinned revision's own `flake.nix`:

```sh
tools/bootstrap.sh          # fetch and verify bend 2.0.31 into .toolchain/
tools/bend version          # never uses a bend on PATH
```

`tools/bend` refuses to run anything but that artifact. `--safe` additionally
needs Lean on PATH (the gate finds `~/.elan/bin`); native builds need clang,
and a binary containing a `!` call needs clang 19 or newer.

### Build, prove, test

```sh
tools/gate.sh               # the whole release gate; logs in build/gate/
tools/bend pp.bend -o build/pp
fixtures/make_repos.sh      # deterministic Git fixtures for the differential
tools/differential.sh       # pp against git plumbing on those fixtures
```

### Ask a repository something

Every query takes either `--repo PATH` (import now, answer, discard) or
`--graph NAME` (a snapshot stored earlier by `pp git import`). Roots default
to `refs/heads/main` when no `--root` is given.

```sh
# What does main require, and how big is it?
build/pp git stats --repo ~/src/thing --root refs/heads/main
build/pp git stats --repo ~/src/thing --mode tree-data     # no history

# What is a partial mirror missing, and is it ready?
build/pp git missing --repo ~/src/thing --have-repo /mirrors/thing
build/pp git missing --repo ~/src/thing --have-repo /mirrors/thing --output oids
build/pp git ready   --repo ~/src/thing --have-repo /mirrors/thing   # exit 1 if not

# Why is this blob required?
build/pp git explain --repo ~/src/thing --object 1aa22346fa57065a53320af0d443640086306138

# Import once, then answer many times without starting git
build/pp git import --repo ~/src/thing --root refs/heads/main --root refs/tags/v1 --as thing
build/pp git stats  --graph thing
build/pp git matrix --graph thing --have-repo /w1 --have-repo /w2 --have-repo /w3

# Check the traversal's own answer with the closure certificate
build/pp git verify --repo ~/src/thing

# Preview what only these refs retain (a preview, never a deletion)
build/pp git retention --repo ~/src/thing --root refs/heads/main --remove refs/heads/old
```

Global flags: `--mode full|tree-data`, `--backend auto|cpu|metal`,
`--store PATH` (the derived-cache directory, defaulting to
`~/Library/Caches/ProofPack` on macOS and `$XDG_CACHE_HOME/proofpack` or
`~/.cache/proofpack` elsewhere), and Bend's own `--gpu off`.

### Reading a result

Every command prints one JSON object. The one below is `missing` on the
repository fixture against the receiver fixture:

```json
{
  "schema_version": 1,
  "query_semantics": "proofpack-state/v1",
  "law_bundle": "proofpack-laws/v0.1",
  "universe": { "namespace": "fixtures/repos/source", "lineage": "ephemeral",
                "generation": "1", "object_format": "sha1", "size": "22" },
  "graph_snapshot": {
    "requested_roots": ["refs/heads/main"],
    "resolved_roots": ["1aa22346fa57065a53320af0d443640086306138"],
    "external_references": ["758408b1c5bbcc987be5dd5ae3624c480b32a2fa"] },
  "policy": "git-full/v1",
  "inventory_snapshot": "fixtures/repos/receiver",
  "completeness": "complete",
  "inventory_assurance": "trusted-odb-observation",
  "availability_scope": "recorded-observation-only",
  "result": {
    "ready_at_observation": false,
    "required": { "objects": "22", "logical_payload_bytes": "2453",
                  "by_type": { "commit": "6", "tree": "9", "blob": "7", "tag": "0" } },
    "missing":  { "objects": "11", "logical_payload_bytes": "1720",
                  "by_type": { "commit": "4", "tree": "5", "blob": "2", "tag": "0" } },
    "inventory": { "in_scope": "11", "out_of_scope": "0", "observed_total": "11" },
    "missing_objects": null },
  "execution": {
    "requested_backend": "auto", "actual_backend": "cpu", "gpu_dispatches": "0",
    "leaf_jobs": "1", "intervals_pruned": "20", "words_read": "256", "bytes_read": "1024" }
}
```

Things to notice:

* **Roots are resolved before anything else.** The query is about the
  resolved object ids, not a moving ref.
* **`external_references`** are gitlinks: submodule commits recorded but never
  traversed. This program never opens a second repository.
* **`availability_scope: recorded-observation-only`** appears on every result.
  An inventory is what a store reported at a moment. It is not a lease.
* **`execution`** reports what actually ran, not what was asked for. Here the
  set tree had 21 intervals at the top level and 20 were pruned structurally;
  one leaf job read 256 words.
* **Bytes are logical payload bytes**, the uncompressed object size Git
  reports, not disk or network bytes.

Exit codes: `0` complete (including an empty set), `1` a complete negative
`ready`, `2` rejected or failed (`InvalidInput`, `IncompleteGraph`,
`CorruptIndex`, `UnknownRoot`, `BackendUnavailable`, `NumericOverflow`),
`3` a resource limit with no complete result. On failure the JSON carries an
`error` object with `class` and `message`; the class is a prefix of the
message so the two cannot drift.

---

## 3. How it works

### 3.1 The idea in one paragraph

Objects get dense ordinals. A set of objects is a bitmap over those ordinals,
stored as a persistent tree whose whole-interval nodes can be `Zero` or
`Full`. Reachability is a least fixed point computed once by a traversal. The
"missing" set is a Boolean difference. Every optimization is a rewrite of that
Boolean algebra, and every rewrite is either proved as a law or forbidden.
Git is a source of bytes at the edge; it is never the algorithm.

### 3.2 The pipeline

```
git cat-file (bytes)                       adapters/git/git.bend, host/run_bytes.c
  -> parsed commits, trees, tags           adapters/git/parse.bend
  -> interned identities, dense ordinals   adapters/git/intern.bend, oid.bend
  -> full graph + derived tree-data graph  adapters/git/import.bend, index/source.bend
  -> (optionally) a published generation   index/store.bend
  -> a typed query expression              query/ast.bend
  -> semantics-preserving rewrites         query/rewrite.bend
  -> frontier traversal for Reach          closure/reach.bend
  -> persistent set algebra                core/set.bend, core/words.bend, core/word.bend
  -> a leaf-job plan, CPU or Metal         execute/plan.bend
  -> fused statistics, never a bitmap      query/eval.bend
  -> a JSON envelope with provenance       cli/main.bend, cli/json.bend
```

Alongside it, and deliberately slow: `spec/closure.bend` recomputes `post`
over the whole set every round, and `spec/query.bend` maps each operator to
the plain set operation. They are the oracle every production path is
checked against.

### 3.3 The Git boundary

`adapters/git/git.bend` builds every Git invocation, and every one is
read-only. Each carries `--no-replace-objects` (grafts cannot change what an
id means), `--no-lazy-fetch` (a partial clone never touches the network
during a query), `--no-optional-locks` (not even an index refresh is written)
and `--literal-pathspecs`. There is no shell; argv is literal.

Import is two subprocess phases and one pure walk:

1. `cat-file --batch-check --batch-all-objects` learns every object's type
   and size. Blob contents are never read, in any phase.
2. `cat-file --batch` fetches the bodies of commits, trees and tags in chunks
   of 2048, into an object table keyed by complete object id.
3. A breadth-first walk from the resolved roots reads that table, handing
   out an ordinal to each object id the first time it is *mentioned*, as a
   root or as a child. The universe is exactly the closure of the roots;
   objects fetched in phase 2 but unreachable are discarded.

A required object the repository does not have is `IncompleteGraph`, never a
vertex with zero successors. This is what rejects a partial or shallow clone
as a source, correctly.

Why bytes and not strings: a Git tree entry holds a raw 20- or 32-byte id,
`cat-file --batch` frames records by declared byte length, and Bend's
`Process.run` decodes stdout as UTF-8 with U+FFFD substitution, which shifts
every record after the first invalid byte. `host/run_bytes.c` is the
toolchain's own `Process.run`, vendored with every symbol renamed and exactly
one change: stdout comes back as bytes. It is the only foreign code in the
program besides an 18-line GPU probe.

### 3.4 Identity and the universe

An `Oid` is eight `U32` words (SHA-1 fills five, SHA-256 all eight) with an
explicit format tag read from the repository, never guessed from a length.
`Uni.intern` maps an id to an ordinal through a bucket trie keyed on the last
word of the digest; a bucket compares the complete key, so a collision costs a
list step and never a wrong answer. No hash-collision assumption exists
anywhere in the algebra.

Ordinals are dense from zero, so every per-object table (adjacency, metadata,
object id) is a 32-deep binary trie (`core/trie.bend`) where an unused half
is one gap node. A table of N objects costs about 2N nodes however wide the
ordinal space is.

### 3.5 Two graphs, one import

An edge `x -> y` means "having x requires y". The `full` policy follows every
edge Git's object model implies. The `tree-data` policy drops exactly the
commit-to-parent edges, which is derived, not labelled: a commit's parents are
commits and its root tree is a tree, so filtering successors by the recorded
types produces the second graph from the first on load. `tree-data` means
enough object content to describe a snapshot, not a promise that checkout,
LFS, submodules or filters will succeed.

### 3.6 Reachability

`closure/reach.bend` is a per-vertex breadth-first search over the persistent
set. A vertex enters a frontier only when absent from `seen`, and `seen` only
grows, so each vertex is expanded at most once. Termination is an explicit
decreasing `Nat` budget of `2n+2` steps for a universe of size `n`, never
`@unsafe`; running out reports `ResourceLimit` and exit 3, never a truncated
answer dressed as complete.

The traversal records its BFS levels. Those are the ranks the closure
certificate needs and the layers `explain` walks back through, so neither
needs extra bookkeeping.

**The certificate** (`closure/cert.bend`, run by `pp git verify`) checks four
things over the traversal's own output: the roots are inside the closure; the
closure is edge-closed; the levels union to exactly the closure; and every
level is one edge from the level before. The first two establish that the
reachable set is inside the answer; the well-founded predecessor chains
establish the converse. Acceptance therefore means *exactness*, not an
overapproximation, which is what lets a cached or independently produced
closure be reused without trusting how it was computed.

**A witness** (`closure/explain.bend`) is read off the levels: the target
sits in level k, some member of level k-1 has an edge to it, and so on to a
root. The path is then checked by a separate function that does not trust
the producer: first element a requested root, last element the target, every
step a real policy edge.

### 3.7 The persistent set

`core/set.bend` is a binary tree over fixed ordinal intervals. A leaf covers
4096 ordinals and is a sorted offset list below 64 members or 128 `U32`
bitmap words above it; `PZero` and `PFull` stand for a whole empty or
complete interval at any depth; a branch splits its interval in half. The
production tree is 20 deep (4096 x 2^20 = 2^32 ordinals).

Every set operation takes the structural shortcuts at every node (`A u Zero =
A`, `A n Full = A`, `A \ Full = Zero`, `Zero \ B = Zero`) and only descends
to words where two real leaves meet. Membership costs three native
instructions a level: compare, shift, conditional subtract.

The fused reductions are the point of the representation. `PSet.diff_count`
walks two trees and accumulates `popcount(required AND NOT have)` at the
leaves; `PSet.diff_members` yields only the members of the difference;
`PSet.is_subset` stops at the first required object the inventory lacks.
`Missing = Required \ Have` is never allocated merely to be measured.

### 3.8 Queries

`query/ast.bend` is small and typed: `Empty | Full | Lit | Union | Inter |
Diff | Reach(policy, e) | Filter(type, e)`. A literal carries its set value,
so an unresolved input cannot be represented in an expression at all, which
is how "validation precedes rewriting" is enforced structurally rather than
by discipline.

`query/rewrite.bend` performs only rewrites a law licenses: `Empty` is the
identity of union and absorbs intersection; `A \ Empty = A`; `C(Empty) =
Empty`. It pointedly does *not* distribute closure over intersection or
difference, nor push a type filter through `Reach`; `tests.bend` runs the
counterexamples so that adding one of those later fails the build.

`query/eval.bend` is an explicit machine (control word, frame stack, one tail
call per step) rather than a structural fold, because this runtime rejects a
def with two non-tail self-calls (see 5.4 below). Its fuel is derived from
the expression's size.

### 3.9 Planning and backends

`execute/plan.bend` mirrors the set tree into a fork tree of leaf jobs. Each
leaf holds *its own* pair of word tiles. That is the measured finding of
`docs/evidence/T01.md`, not a style: handing one host-built operand list to
every leaf costs one atomic per operand per fork level and ran about 12x
slower. Intervals are disjoint by construction, each job returns one `Nat`,
and the fold is balanced, which is sound because `Nat` addition is a proved
commutative monoid.

The same leaf code runs on the CPU pool or, behind a `!` call, on Metal.
`host/gpu.c` reads the runtime's own `io_gpu` flag so the envelope reports
the backend that actually ran. On every forced-backend query the plan's count
is cross-checked against the tree reduction; a disagreement is reported as
`actual_backend: "disagreed"` with exit 2, never as an answer. `--backend
metal` with no usable GPU is `BackendUnavailable`, not a silent fallback.

### 3.10 The derived store

`pp git import ... --as NAME` writes one generation to `NAME.pps`: the object
format, the resolved root vector, and for each ordinal in order its id, size,
type and successors under `full`. The `tree-data` graph and the interning
table are rebuilt on load, and the decoder checks that reading the ids back
in order reproduces exactly the ordinals written.

The format is line-oriented ASCII on purpose: the thing that gets validated
should be the thing a person can read. Validated on load: the magic line, the
object format, the declared count against the objects present, each id being
exactly the format's width of hex, each size and type code, each successor
count, every successor inside the declared universe. A checksum is explicitly
not a substitute for this. Publishing writes to a temporary name and renames,
so a crash leaves the previous generation intact.

On the fixture, answering from a stored generation takes 44 ms against 137 ms
for an import; the gap is the whole import and grows with the repository.

### 3.11 The matrix

`pp git matrix --graph NAME --have-repo H...` loads the generation once,
computes the requirement once, and answers each inventory as one fused
difference. Inventories that report identical object sets (linked worktrees
sharing an object store, workers restored from one snapshot) are one cell,
and each row says which earlier row it shares. The envelope reports the
number of distinct inventories alongside the rows.

---

## 4. The laws, and what each one unlocks

The specification names 32 obligations with stable ids. Each optimization in
`OPTIMIZATIONS.md` cites the law that authorizes it, and each law names the
production definition it constrains. `law-registry.json` records the status of
every obligation. This section is the reader's map.

Three things about how the laws are written:

* **Pointwise.** A set operation is correct when every position of the
  result is the Boolean of the same positions of the operands. This avoids
  assuming function extensionality, and it is also what makes the laws hold
  for operands of different lengths with no bounds hypothesis anywhere.
* **Over production symbols.** `U32.popcount` in a law is the 32-step native
  loop the hot path runs, not a model of it. Where a specification twin
  exists (`U32.bit`, `Words.count`), the law is the bridge between the two.
* **Open claims are stated, not described.** `LAWS.pending.bend` writes the
  unproved obligations in the same syntax over the same symbols, typechecked
  with `--check-only`, so that "not yet proved" means a precise statement is
  waiting for a proof rather than a paragraph of prose.

### 4.1 Proved (`LAWS.bend`, discharged by `PROOF.bend`, rechecked by BendTT)

| Id | Law(s) in `LAWS.bend` | What it says | Optimization it unlocks | Where it runs |
|---|---|---|---|---|
| **B-01** word refinement | `word_difference_is_pointwise`, `word_intersection_is_pointwise`, `word_union_is_pointwise`, `shifting_right_reads_the_next_bit_up`, `the_tail_mask_hides_every_padding_bit`, `popcount_counts_the_bits_that_are_set`, `the_fast_bit_test_agrees_with_the_bit_vector` | `U32.and`, `U32.or`, `and-not`, `shr` are pointwise on the 32-bit vector; the mask of the low k bits is set exactly below k and inside the word; the production popcount equals the cardinality the bit accessor reports; the shift-and-test bit read equals the bit accessor | **The dense leaf loop is native.** Every hot-loop word operation is one machine instruction, while the proofs reason about bit vectors. The mask law is what stops a dense leaf's padding bits from ever counting as objects when the universe is not a multiple of 4096 | `core/word.bend`: `U32.diff`, `U32.popcount`, `U32.mask`; `core/words.bend`: `U32.test` |
| **S-01** pointwise set operations | `tile_difference_is_pointwise`, `tile_intersection_is_pointwise`, `tile_union_is_pointwise` | Over word lists of any two lengths, bit k of word i of the result is the Boolean of the same bit of the operands; a missing word reads as absent | **All set-operation correctness** at the tile level, and hence every structural shortcut instantiated on words | `core/words.bend`: `Words.and`, `Words.or`, `Words.diff`, `Words.at` |
| **R-01** ordinal partition | the same three tile laws, read as being *at a position* | A law stated at a position commutes with restriction to a disjoint range of positions | **Independent CPU/Metal leaf jobs.** Splitting a set operation into disjoint tiles and reassembling gives the same set, so a plan may hand tiles to independent workers | `core/words.bend`: `Words.at` |
| **Q-02** fused difference statistics | `counting_a_difference_needs_no_difference` | `Words.diff_count(a, b) == Words.count(Words.diff(a, b))` | **No intermediate missing bitmap.** A matrix cell counts `required AND NOT have` as it goes instead of allocating the difference. This is the essential optimization of the whole design | `core/words.bend`: `Words.diff_count`; `core/set.bend`: `PSet.diff_count`; `query/eval.bend`: `Ev.missing_count` |
| **R-02** disjoint statistics | `statistics_have_a_left_identity`, `statistics_have_a_right_identity`, `statistics_add_commutatively`, `statistics_add_associatively`, `every_object_counts_once` | `Stats` (count, bytes, counts by type) is a commutative monoid under componentwise addition with `Stats.zero`; one object always adds one to the count | **Balanced, deterministic parallel reductions.** Commutativity is why the order tiles come back in cannot change a byte total; associativity is why the fold may be balanced. The disjointness hypothesis is why `Stats(A u B) = Stats(A) + Stats(B)` is *forbidden* for overlapping sets | `query/ast.bend`: `Stats.add`, `Stats.zero`, `Stats.of_kind` |
| **M-01** least missing set | `the_missing_set_covers_the_requirement`, `the_missing_set_is_the_least_one` | For K = C(R) and *any* H: K inside H u (K \ H), and K inside H u T iff (K \ H) inside T | **Exact additional-object requirements against a partial cache.** H need not be graph-closed, so a receiver's raw inventory can be used as-is. This is the theorem the product is | `core/set.bend`: `PSet.diff`, `PSet.missing`; `query/eval.bend`: `Ev.missing_stats` |
| **M-02** readiness | `readiness_is_an_empty_difference` | K inside H iff K \ H is empty | **Early exit.** `pp git ready` stops at the first required object the inventory lacks; it never pays to count | `core/set.bend`: `PSet.is_subset`; `query/eval.bend`: `Ev.ready` |
| **M-03** missing composition | `missing_distributes_over_a_union_of_requirements`, `inventory_tiers_compose` | (A u B) \ H = (A \ H) u (B \ H); A \ (H1 u H2) = (A \ H1) \ H2 | **Shared inventory scans and tiered filtering.** Two requirements can share one inventory scan; local, LAN and upstream inventories can be subtracted in sequence. Neither implies a tier is authorized or reachable | `core/set.bend`: `PSet.diff`, `PSet.union` |
| **I-01** inventory maintenance | `an_additions_only_update_needs_no_rederivation`, `add_wins_in_a_patch` | K \ (H u A) = (K \ H) \ A; patch(H, D, A) = (H \ D) u A with add winning | **Incremental inventory updates without re-deriving the requirement.** An additions-only update is one more difference. Patches are not assumed to commute with each other; no parallel-update law is certified | `core/set.bend`: `PSet.diff`, `PSet.union` |
| **B-02** checked numeric refinement | `the_accumulator_has_an_identity`, `the_accumulator_adds_commutatively`, `the_accumulator_adds_associatively` | `Nat.add` has identity 0 and is commutative and associative | **Exact counts and byte totals in a parallel fold.** This runtime's `Nat` is a native unsigned integer that posts an error at 2^48-1 instead of wrapping, so it *is* the checked accumulator the specification asked for, and re-implementing limbs would add trusted code rather than remove it | `core/count.bend`: `Nat.add`, `Count.add`, `Count.ceiling` |

### 4.2 Specified, checked at run time (`LAWS.pending.bend`)

These are stated precisely and typecheck, but have no proof. What backs each
is a runtime check or a differential rather than a theorem.

| Id | Open statement(s) | Would unlock | Backed today by |
|---|---|---|---|
| **S-02** representation refinement | `set_difference_is_pointwise`, `set_union_is_pointwise`, `set_intersection_is_pointwise` (lifting the tile laws through the tree) | adaptive persistent representations as a proved fact | the traversal differential in `tests.bend` and `tools/differential.sh`, both of which exercise these operations throughout |
| **S-03** representation conversion | `compressing_a_leaf_keeps_its_members` | density-adaptive storage | `tests.bend`: the sparse/dense crossover at 64 and 65 members preserves membership and size |
| **P-01** persistent updates | `inserting_adds_exactly_that_ordinal` (the checkable half) | sharing across inventory versions | affine values make "old roots unchanged" true by construction; not stated formally |
| **C-01** least fixed point | `closure_contains_its_roots`, `closure_is_edge_closed` | authoritative requirement semantics | `spec/closure.bend` is the definition operationally; the pigeonhole argument for reaching the fixed point within N rounds is not written |
| **C-02** traversal refinement | `the_traversal_returns_the_specification_closure` | efficient CPU traversal as a proved refinement | the certificate per query (`pp git verify`), five graph shapes times eight root sets against the specification closure in `tests.bend`, and `rev-list --objects` in the differential |
| **C-03** closure algebra | `closure_preserves_unions`, `closure_is_idempotent` | grouped roots and closure reuse; the `C(A u B) = C(A) u C(B)` rewrite in `query/rewrite.bend` | `tests.bend` checks union preservation, extensivity, idempotence and closure-of-empty on the counterexample graph |
| **C-04** certificate soundness | `an_accepted_certificate_means_an_exact_closure` | checked reuse of cached or foreign closures | the argument is written in `closure/cert.bend` and `TRUST.md`; `tests.bend` shows the checker accepts a real closure and rejects one with an extra member and one missing a member |
| **Q-01** validated rewrites | `rewriting_preserves_denotation` | safe algebraic query optimization | each rewrite is an instance of a proved tile law; the counterexamples for the forbidden ones are permanent tests |
| **Q-03** compiler soundness | `the_evaluator_computes_the_denotation` | the end-to-end refinement `observe(execute(compile(q))) = [[q]]` | the `tests.bend` differential against `spec/query.bend`, and the Git differential |
| **G-02** Git policies | `a_filtered_row_drops_exactly_the_commit_targets`, `the_tree_data_policy_drops_exactly_the_parent_edges`, on `a_table_built_from_a_list_answers_the_same_descent_over_the_list` | history versus current-tree requirements as a proved projection: the policy can be applied to a row instead of re-deriving a graph | `tools/differential.sh`: `tree-data` counts and bytes against `rev-parse` plus `ls-tree -r -t` with gitlinks excluded |
| **U-01** identity mapping | `interning_an_id_then_finding_it_gives_the_same_ordinal`, on `reading_a_trie_at_the_key_just_written_gives_that_value` | dense ordinals with no identity confusion: an object may be referenced long before it is fetched, and the second mention gets the first mention's ordinal | injectivity -- the other half -- by construction in `intern.bend`: only the fresh branch writes a slot, and it hands out `next` and then increments it |
| **G-03** inventory projection | `the_projection_contains_every_id_the_universe_names`, `the_projection_contains_only_ordinals_the_table_named` | partial receiver caches: a receiver's report is projected into the source universe without assuming its store is graph-closed | `tools/differential.sh`: inventory totals against `cat-file --batch-all-objects`, and no reported-missing object actually present in the receiver |
| **E-01**, **G-01**, **S-04** | registered but not written as laws | checked witnesses; the parser contract; Boolean pruning | `Explain.valid` on every witness; the differential's corpus (merge, tag chains, symlink, empty blob, non-UTF-8 name, gitlink); the structural shortcuts being instances of proved tile laws |

### 4.3 Not applicable yet

`U-02` generation lifting, `C-05` checkpoint shortcut, `Q-04` batch
deduplication, `I-02` graph extension, `I-03` cache binding, `B-03` plan
execution refinement, `D-01` serialization. Each names the feature it waits
for. Note that `Q-04` and `D-01` now have code to be stated over (the matrix
deduplicates inventories; the store validates on load) and the registry has
not been updated.

### 4.4 What is deliberately forbidden

These would be optimizations if they were sound. `tests.bend` runs the
counterexamples so that adding one fails the build.

| Rewrite | Why not |
|---|---|
| `C(A n B) = C(A) n C(B)` | with `a -> x` and `b -> x`, the closures meet at x although the root sets do not |
| `C(A \ B) = C(A) \ C(B)` | closing `{a} \ {b}` keeps x; subtracting the closures removes it |
| pushing a type filter through `Reach` | dropping commit vertices before traversal erases the paths to the blobs they require |
| `Stats(A u B) = Stats(A) + Stats(B)` | double-counts overlap; statistics come from one enumeration of one set |
| `lift(Full_old) = Full_new` | `Full` is full within a node's valid range; unused bitmap capacity must never read as membership |
| `Reach(R) n tile = Reach_in_tile(R n tile)` | graph paths leave a tile and come back; reachability is resolved before any ordinal-local work |
| resolving an invalid input after a rewrite removed it | structurally impossible: a literal carries its value, so an unresolved input cannot appear in an expression |

---

## 5. How Bend2 is leveraged

Bend2 is used for everything except two small C effects: specifications,
proofs, production algorithms, planning, the native executable and the Metal
leaf kernel are one language and one file tree. That is not incidental. The
laws constrain the *shipped* definitions because they can name them.

### 5.1 Laws and proofs in the same language as production

Bend has `law` and `def` at the top level. A law states a proposition as a
type; a def of the same name proves it; `bend PROOF.bend` fails while any law
is open or false. This repository follows the guide's convention exactly:
`LAWS.bend` imports the production modules and states claims over them,
`PROOF.bend` imports `LAWS.bend` and fills each with a proof that delegates to
`proofs/*.bend`. There are no tactics; a proof is case analysis, a recursive
call as induction hypothesis, and `%e : P` rewriting. For example the whole
proof that the fused count equals the built count:

```python
law Words.diff_count_spec:
  for a: List<&2, U32>
  for b: List<&2, U32>
  {Wo.Words.diff_count(a, b) == Wo.Words.count(Wo.Words.diff(a, b)) : Nat}

def Words.diff_count_spec(a, b):
  Words.diff_count_go(a, b, 0n)          # the accumulator lemma, at zero
```

`tools/gate.sh` runs this as a release gate, so a change to a production
definition that breaks a law is a failed build, not a failed review.

### 5.2 `U32` is a bit vector to the checker and a machine word to the compiler

This is the single most important fact the design rests on. Base declares
`type U32 is Data: U32{data: Word(32n)}`, where `Word(n)` is a little-endian
vector of `Bool`. So the *checker* sees `U32.and` as `Word.and(32n, ..)`, a
function it can do induction over, while the compiler's operation table
lowers `U32.and`, `U32.or`, `U32.shr`, `U32.add` to single native operations
(`U32_BIN(a, &, b)` in the emitted C, and the same source compiled by Metal).

Law `B-01` is therefore proved by structural induction over 32 bits
(`proofs/word.bend`: a lemma over `Word(n)` by induction on `n`, then one
`match` to expose the 32-bit vector inside a `U32`), and the production hot
loop still runs one instruction per operation. The `Word(32n)` vector never
materializes at run time, because a `match` on a `U32` appears only in proof
code, which is erased. `docs/evidence/T01.md` has the emitted C.

One consequence shaped the code: `U32.mask(k)` is built *through* the bit
vector (`U32{Word.low_mask(32n, k)}`) rather than by shifting, because that
makes `bit i of mask(k) == (i < k)` provable with no carry reasoning. It
costs 32 cells once per query, for the one word that straddles the end of
the universe, so it never enters a loop.

### 5.3 `--safe` and the BendTT kernel

`bend PROOF.bend --safe` translates the checked file to BendTT and rechecks
it with a small kernel that has a proof in Lean. It lists what it leaves out:
`@unsafe` defs, and foreign defs, which it checks as a model built from their
type rather than their C. This release has **no `@unsafe` defs**, and no
proof reaches either foreign def (`Host.run_bytes`, `Host.gpu_enabled`), so
`--safe` excludes nothing and the gate records that. The translation itself
is unproved, which `TRUST.md` says plainly.

### 5.4 Termination without `@unsafe`

Bend's termination checker requires a self-call to shrink an argument. Every
loop in the program that is not obviously structural (the BFS, the import
walk, the evaluator machine, the store decoder) carries an explicit `Nat`
fuel derived from a finite quantity: the universe size, the expression size,
the byte count. Running out is `ResourceLimit`, an error class, never a
result. This is how the specification's "an unfinished traversal must never
become a successful answer" is enforced by the type checker rather than by
convention.

### 5.5 Affine values, borrowing, and the memory substrate

Bend is affine: a value is used at most once unless marked `+`. The compiler
borrows a list a def only matches and frees a node when a `match` opens it,
with no garbage collector. `docs/evidence/T01.md` inspected the emitted C to
confirm that the leaf kernels (`Words.diff_count`, `U32.popcount.go`) compile
to flat tail loops with zero reference-count operations, and that the
reference-count traffic in the shared-operand shape lives in the *fork node*:
one atomic per operand per fork level. That measurement (about 12x) is why the
planner gives each leaf its own tiles, and `bench/spike_t01.bend` is the
regression that catches a change which starts broadcasting again.

The specification had proposed new runtime intrinsics (`FrozenWords`,
`ReadSpan`, `OwnedTile`) if the substrate proved insufficient. The experiment
found it sufficient: the cost was a plan shape, not a missing storage API, so
no compiler or runtime change was made.

### 5.6 `!` calls and honest backends

A `!` after a call hands it to Metal when a GPU is present and to the CPU
pool otherwise; `bend x.bend -o x` emits `x.gpu` beside the binary. The same
leaf code is called plainly for the CPU path and as `Exec.count!(d, j)` for
the Metal path in `execute/plan.bend`. Because the fallback is silent by
design, `host/gpu.c` reads the runtime's `io_gpu` flag so the envelope can
say which backend actually ran, and forced Metal without a GPU is an error.
Deleting `pp.gpu` and rerunning makes the runtime say it is recompiling the
GPU program, which is how it was confirmed the file is consulted at run time.

### 5.7 `Nat` as the checked accumulator

The runtime's `Nat` compiles to a native unsigned integer whose add is one
instruction and whose `nat_chk` posts an error at 2^48-1 instead of
wrapping. So `Nat` satisfies the specification's checked-accumulator
requirement directly, its equations are Peano's, and `B-02` is provable by
ordinary induction. `core/count.bend` adds the admission bound: a weight
table is admitted only when its total fits under the ceiling, so no subset
sum inside an admitted query can reach it.

### 5.8 Foreign effects, kept small

Two C files, both spliced in after the runtime and both dependent on its
internal, unversioned effect ABI, so both must be rebuilt on every toolchain
bump:

* `host/run_bytes.c` (with a `.js` twin): byte-exact `Process.run`, described in 3.3.
* `host/gpu.c` (with a `.js` twin that answers `false`, which is the truth for the sequential JavaScript target): reads `io_gpu`.

`mkdir -p` and `mv` for the derived store go through the same literal-argv
boundary rather than adding more C.

### 5.9 Toolchain rules that shaped the code

`docs/MODULES.md` records these; they are worth knowing before editing.

* **Module identity is a normalized import path relative to the entry file.**
  So every entry point (`LAWS.bend`, `PROOF.bend`, `pp.bend`, `tests.bend`)
  lives at the repository root, subdirectory modules import each other with
  `./` and `../` spellings, and `tools/check.sh` typechecks everything
  through one generated root-level entry so a module that only checks in
  isolation cannot pass.
* **No mutual recursion, and a def must be declared above its callers.**
  Where an algorithm wants "compute, branch, recurse", the comparison is
  carried as a parameter recomputed by a small def declared above.
  `tools/order.py` topologically sorts a file's definitions and reports a
  genuine cycle rather than hiding it.
* **A def or continuation takes at most 247 words.** A def with two non-tail
  self-calls becomes a segmented continuation that overruns it, which is why
  `query/eval.bend` is an explicit machine and why large JSON objects are
  built in pieces. A record threaded through many defs (`Ctx` in the CLI)
  exists for the same reason.
* **Depth-indexed recursive types get unrolled by the layout pass.** The set
  was `PSet(depth)` at first, like Base's `Word(n)`; the layout pass compares
  head names to detect self-recursion, misses a def-headed index, and unrolls
  seven levels, so one field cost 127 words. `PSet` and `Trie` carry depth as
  an ordinary `Nat` argument, and the invariants the index would have
  enforced are stated in `PSet.valid` and checked on anything decoded from
  storage.
* **A `match` inspects parameters in binder order**, and the shrinking
  argument of a self-call goes before the accumulator.

---

## 6. Testing and evidence

`tools/gate.sh` is what a release has to pass. In order:

| Step | What it establishes |
|---|---|
| `typecheck` | every module typechecks through one root entry |
| `proof` | `bend PROOF.bend`: every law in `LAWS.bend` holds |
| `bendtt` | the BendTT translation is written to `build/gate/PROOF.bendtt` for inspection |
| `proof-safe` | the BendTT kernel rechecks; the exclusion list is recorded (currently empty) |
| `build-tests`, `tests` | `tests.bend`: counterexamples, bitmap boundaries, the traversal differential, certificate acceptance and rejection, witness acceptance and rejection |
| `build-pp` | the executable builds |
| `git-differential` | `tools/differential.sh` against independent Git plumbing |

**`tests.bend`** runs the forbidden-rewrite counterexamples on the `a -> x,
b -> x` graph; checks bitmap positions 0, 1, 31, 32, 33, 4095, 4096, 4097,
tail masking, the sparse/dense crossover and a padding bit that must not be
a member; checks the fused count against the built difference; runs the
production traversal against the specification closure over five graph
shapes and eight root sets each; and checks that the certificate and the
witness checker each accept a real answer and reject two kinds of tampering.

**`tools/differential.sh`** computes both sides differently on purpose. For
`full`, `pp` walks raw `cat-file` bodies while Git's side is `rev-list
--objects`; for `tree-data`, Git's side is `rev-parse` plus `ls-tree -r -t`
with gitlinks excluded. It also checks inventory totals against
`--batch-all-objects`, that every reported-missing object is really absent,
readiness against an empty missing set, exit codes, CPU against Metal on
identical queries, a forced Metal run without a GPU failing rather than
falling back, the store round trip, and four derived corruptions each
rejected as `CorruptIndex`. It refuses to run at all unless all three fixture
repositories are present and stamped with the current generator version,
because a differential that runs half its cases and reports success is
worse than one that refuses to start.

**`fixtures/make_repos.sh`** builds three deterministic repositories (fixed
identity and dates, so object ids are stable and the script can detect a
stale set): a source with a merge, a tag chain, tags to a tree and a blob, a
symlink, an empty blob, a non-UTF-8 entry name and a gitlink; a bare receiver
holding part of the history; and a repository with one empty commit.

**`bench/repeated.sh`** and **`docs/evidence/T06.md`** are the acceptance
workload: fixed receivers, warm-ups, trials interleaved in both orders,
medians, an A-versus-A control, the import timed separately, and every cell
checked against Git's own difference before a single timing is printed.

**`bench/spike_t01.bend`** and **`docs/evidence/T01.md`** are the substrate
experiment: the fused kernel over 2^16 leaves x 128 words, owned versus
shared operands, CPU pool versus Metal, with the emitted C.

---

## 7. Trust boundary, in brief

`TRUST.md` is the full statement. The short form: **the algebra is proved,
the traversal is checked per query, and everything that touches a real
repository is trusted.** Trusted means: that `git cat-file` returns the bytes
an id names; the subprocess and filesystem boundary; the two C effects; the
compiler's lowering of `U32` operations to machine words and its translation
to BendTT; the runtime, OS, Metal and hardware; that an inventory describes
what a store held at a moment; and that a repository did not change during an
import (prefer a quiescent mirror). No result is called "mathematically
verified" because the binary ships with proofs.

---

## 8. Repository layout

```
LAWS.bend             the public claims, proved
LAWS.pending.bend     the open claims, stated in the same syntax
PROOF.bend            discharges LAWS.bend; delegates to proofs/
pp.bend               the executable's entry point
tests.bend            executable checks
law-registry.json     per-obligation status
TRUST.md  OPTIMIZATIONS.md  docs/MODULES.md  docs/evidence/

core/       word.bend (checked words)  words.bend (tiles)  set.bend (persistent set)
            trie.bend (ordinal tables)  count.bend (checked counting)  ords.bend
spec/       closure.bend (the slow oracle)  query.bend (the denotation)
closure/    graph.bend  reach.bend (BFS)  cert.bend (certificate)  explain.bend (witnesses)
query/      ast.bend  rewrite.bend  eval.bend (production evaluator)
execute/    plan.bend (leaf jobs, CPU and Metal)
index/      source.bend (the derived graph)  store.bend (generations on disk)
adapters/git/  git.bend (plumbing argv)  import.bend  parse.bend  intern.bend
               inventory.bend  oid.bend  bytes.bend
host/       proc.bend  run_bytes.c/.js  gpu.c/.js
cli/        main.bend  args.bend  json.bend
proofs/     nat  word  popcount  bits  words  stats  missing
tools/      bend  bootstrap.sh  check.sh  gate.sh  differential.sh  order.py
fixtures/   make_repos.sh (repos/ is generated and ignored)
bench/      spike_t01.bend  repeated.sh
proofpack-handoff/   the original specification and its Python reference checker
toolchain.lock.json  the pinned Bend release and archive hashes
```

Every `.bend` entry point is at the root, and every module in a subdirectory
imports its neighbours as `./x.bend` and other directories as `../dir/x.bend`.
See `docs/MODULES.md` for why that is forced rather than chosen.
