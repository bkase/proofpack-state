# ProofPack State
## Product and engineering specification — v0.1

**Status:** implementation handoff; proposed contracts, not an already-proved implementation.  
**Date:** 27 September 2026.  
**Initial product:** a read-only Git state-query engine with a reusable, proved finite-set and reachability core.  
**Implementation:** Bend2 for specifications, proofs, algorithms, planning, native execution, and Metal leaf kernels. Minimal host effects for Git subprocesses and storage.  
**Future consumers:** shared Git caches, build CAS services, worker placement, retention policies, and agent runtimes. These are not first-release deliverables.

> Given immutable requirements and an explicitly scoped inventory, calculate exactly what is missing. Prove that all representations and execution plans mean the same thing, then avoid and parallelize work without changing that meaning.

This document is normative for the first release. “Must” denotes a release requirement; “later” denotes deliberately deferred work. Mathematical signatures and data declarations are pseudocode unless explicitly labeled otherwise. They are not untested Bend source presented as working code.

---

## 1. Product boundary and first useful release

### 1.1 What to build

Build **ProofPack State**, executable `pp`, as a local library and command-line program that imports Git metadata once and answers repeated repository-state queries. It must answer:

| Question | Initial interface | Exact meaning |
|---|---|---|
| Which objects are missing? | `pp git missing` | Required logical objects minus the recorded inventory |
| Does this inventory cover this requirement? | `pp git ready` | Set inclusion at named snapshots, not a live availability lease |
| Which cache is already closest to these tasks? | `pp git matrix` | Batched missing counts, logical payload bytes, and coverage predicates |
| What is retained only by these roots? | `pp git retention` | Reachability difference against an explicit retained-root set |
| Why is this object required? | `pp git explain` | One valid root-to-object dependency path |

The library—not a shell wrapper around `git rev-list`—computes closure, set differences, statistics, and batch plans. Git initially supplies object decoding and metadata access. The resulting program should be useful to an engineer managing local mirrors, detached worktrees, and partially populated remote caches before it becomes a distributed service.

**Do not market this as a faster `git status`, a build system, or a generic code-intelligence product.** A worktree's checked-out commit does not describe everything its object database contains. Linked Git worktrees already share repository state, except for per-worktree metadata. Deduplicate identical physical cache inventories rather than inventing different caches for each worktree. [S3]

### 1.2 Deliverables

The first release includes a pinned toolchain; public denotational contracts; completed proofs for the core and shipped rewrites; an independent reference evaluator; a Git adapter; persistent adaptive sets; demand-driven closure indexing; native CPU execution; a real Metal execution path for suitable batches; structured result and error formats; reproducible benchmarks; and a documented trusted-computing boundary.

The first release **does not** execute agents, create VMs, launch browsers, manage ports, distribute credentials, schedule builds, implement REAPI, write Git packs, transfer objects, mutate Git refs, or delete repository objects. It is safe to invoke against a developer repository because it writes only its own derived store. Networking and lazy Git fetching are disabled during ordinary import/query operations.

### 1.3 What makes this more than a bitmap benchmark

The product has four substantive contributions:

1. A reusable semantics for requirements, inventories, closure, and missing state.
2. A verified query compiler, including fused reductions that do not allocate intermediate sets.
3. Persistent sharing and exact incremental reuse across related requirements and inventories.
4. A Git adapter and evidence model that distinguish mathematical results from storage and freshness assumptions.

The performance thesis is **prune first, reuse second, fuse third, parallelize last**. A GPU is an optional execution backend, not the definition of success.

---

## 2. Decisions fixed for v0.1

| Area | Decision |
|---|---|
| Source language | Bend2; specifications and production algorithms stay in the same language |
| Scope | Finite immutable object graphs; no programming-language semantic analysis |
| Logical identity | Namespace + object format + complete object ID, never an unscoped ordinal |
| Primary algebra | Finite Boolean sets, monotone reachability closure, and disjoint-partition reductions |
| Persistent representation | Fixed-range binary tree/DAG with empty, full, sparse, and dense leaves |
| Dense page | Initially 4,096 ordinal positions = 128 logical `U32` bitmap words; tune later |
| Backend strategy | CPU graph traversal and structural pruning; native/Metal flat leaf work |
| Git importer | Buffered Git plumbing for metadata and raw non-blob object bodies; Bend parsing and graph construction |
| Source graph | Complete full superproject closure of explicitly imported roots |
| Receiver inventory | May be incomplete as a graph; must declare inventory evidence and projection scope |
| Git query policies | `full` and `tree-data`; do not call the latter a guarantee that checkout will succeed |
| Metrics | Object count and uncompressed logical object payload bytes, not network or reclaimable disk bytes |
| Persistence | Single writer, immutable generations, atomically published manifests |
| API | CLI and bounded JSON batch protocol; no public network daemon initially |
| Proof gate | `bend PROOF.bend --verdict`, the effects manifest, and tests over the production implementation |
| Native integration | Small effect/storage boundary; no opaque C implementation of the set engine |

The proposed source baseline is `bendlang/bend` commit **`af569d4826913b2ce3557e9829ccad31fcf86f94`**, inspected on 27 September 2026. That commit names version 2.0.31 in its Nix flake. Pin both source revision and actual compiler artifact; record any additional runtime patch separately. This is a reproducibility choice, not a claim that this revision is independently audited. [S1]

The implementation has since moved to **`4f856f61392425f25f5798e8773c50a18cc3ae51`** (version 2.0.32); `toolchain.lock.json` is the live pin, and `docs/evidence/T01.md` records what changed. Two differences matter to this specification: the kernel recheck is `--verdict` rather than `--safe`, and it now refuses a file in which anything relies on unsafe or foreign code — which forces the effectful code to live in modules the proof closure does not import.

---

## 3. Denotational semantics: the authoritative model

### 3.1 Universes, identities, and observations

A universe generation is:

```text
Universe = {
  namespace,
  object_format,
  lineage_id,
  generation,
  size: N,
  identify: Fin(N) -> ObjectKey
}
```

`identify` is injective. Its image is exactly the set of identities registered in this generation. A set is mathematically a membership predicate over `Fin(N)`. In proofs, prefer **pointwise membership equivalence** over assuming function extensionality.

Every stored set and query operand carries its universe lineage and generation. Two words at ordinal 17 have no relationship unless an explicit identity-preserving mapping relates their universes. Set operations across unrelated universes are rejected, not guessed.

An immutable observation environment `W` contains a universe, graph snapshot, policy version, named root sets, inventory observations, immutable weight/type tables, and query semantics version. A symbolic ref is resolved to an object ID before evaluation. The query then refers to the resolved root vector, not a moving `HEAD`.

### 3.2 Graphs and policy

Let `G = (V, E)` be a finite directed graph over the universe. An edge `x -> y` means **having the requirement rooted at x requires y** under the selected policy. This orientation is deliberately the same for commits-to-parents and actions-to-inputs.

The generic core handles cycles. It must not assume every future artifact graph is acyclic. The Git adapter may validate stronger properties, but termination of the general closure algorithm comes from finiteness and a visited set.

Each graph supplied to exact evaluation has a complete adjacency description. A missing graph object is not a vertex with zero successors. Graph construction fails with `IncompleteGraph` when it cannot establish required adjacency or required object metadata.

### 3.3 Reachability as a least fixed point

Define:

\[
\operatorname{post}_G(X)=\{y\mid \exists x\in X,\ (x,y)\in E\}.
\]

For a root set `R`:

\[
C_G(R)=\mu X.\;R\cup\operatorname{post}_G(X).
\]

Equivalently, `C_G(R)` is the least edge-closed set containing `R`. It includes roots themselves, including isolated roots. `C_G(empty) = empty`.

A simple executable specification starts with `X0 = R` and repeatedly applies `X(k+1) = Xk ∪ post(Xk)` until stable. On a universe of size N, at most N strict-growth rounds are possible. An optimized frontier traversal must refine this specification. An operational fuel limit can return `ResourceLimit`, but must never turn unfinished traversal into a successful result.

### 3.4 The generic theorem underneath the product

For roots `R` and **any** recorded inventory `H`, define:

\[
K=C_G(R),\qquad M=K\setminus H.
\]

Prove:

\[
K\subseteq H\cup M
\]

and, for every candidate transfer set `T`:

\[
K\subseteq H\cup T\quad\Longleftrightarrow\quad M\subseteq T.
\]

Thus `M` is the **unique least additional object set** that covers the requirement, ordered by set inclusion. It excludes objects already in `H` and contains every missing required object.

This theorem does not require `H` to be graph-closed. That matters for partial caches. It also does not say that the associated transfer encoding is byte-minimal, that a receiver really possesses its advertised inventory, or that objects remain available after the observation.

### 3.5 Query denotations

Keep the initial query language small and typed:

```text
SetExpr = Empty | Full | Literal(set_id) | Roots(root_set_id)
        | Union(a,b) | Intersect(a,b) | Difference(a,b)
        | Reach(graph_policy_id, a) | Filter(metadata_predicate, a)

Query = Objects(expr, order)
      | Stats(expr)
      | IsEmpty(expr)
      | IsSubset(a,b)
      | ExplainReach(root_set_id, object_id, graph_policy_id)
      | Batch(queries)
```

`Filter` initially supports exact object-type filtering. Predicates are declarative, versioned operations—not arbitrary agent-supplied executable functions.

Denotation is recursive. For example:

\[
\llbracket a\cup b\rrbracket_W=\llbracket a\rrbracket_W\cup\llbracket b\rrbracket_W,
\]

\[
\llbracket Reach(p,a)\rrbracket_W=C_{G_p}(\llbracket a\rrbracket_W).
\]

`Objects` returns a complete, duplicate-free enumeration of the denoted set, or explicit pagination over a pinned snapshot. `Stats` returns exact count, logical payload-byte sum, and counts by type. Default user-facing enumeration is lexicographic object-ID order; an explicitly requested ordinal order is generation-specific. Sorting costs must be measured.

Invalid operands, unsupported policies, absent weights, universe mismatches, and unresolved graph inputs are errors during validation. Only **validated, total queries** enter the algebraic optimizer. For example, simplifying `Difference(q,q)` must not hide an unresolved input or malformed graph by skipping validation.

### 3.6 The central compiler contract

For every valid environment `W`, valid query `q`, and supported backend `b`:

\[
\operatorname{observe}\bigl(\operatorname{execute}_b(\operatorname{compile}(W,q))\bigr)
=\llbracket q\rrbracket_W.
\]

Admissibility includes the numeric bounds in §5.4; the pure executor is total over admitted finite plans. Host cancellation and resource exhaustion belong to the explicit outer error protocol, not to a successful value of this equation. The observation includes exact result contents, requested order, and completeness—not timings or incidental node identities. For errors outside the total core, preserve the documented error class and do not present partial results as complete.

This equation is the architecture. Git parsing refines imported objects into `W`; set implementations refine denotations; rewrite passes preserve query meaning; leaf execution refines plans. Proofs should connect these layers rather than leave a proved reference model disconnected from the shipped executable.

---

## 4. Laws and the optimizations they authorize

Keep stable law IDs in `LAWS.bend` and in the law registry supplied with this handoff. Each optimization cites its enabling law. Each law names the actual production definition it constrains.

| Family | Required statement | Optimization or capability unlocked |
|---|---|---|
| `U-*`: identity | Ordinal mapping is injective; lookup round-trips; all operands have compatible scope | Compact ordinals, persistent generations, safe cross-cache comparison |
| `S-*`: representation | Decoding empty/full/sparse/dense/branch nodes gives exactly their members | Adaptive sparse/dense layout; representation independence |
| `S-*`: Boolean algebra | Union/intersection/difference implement their pointwise definitions | Empty/full pruning, idempotence, absorption, common-subexpression elimination |
| `P-*`: persistence | Updating a new root does not change the old root's denotation | Shared worker inventories and closure snapshots |
| `C-*`: closure | Extensivity, edge closure, leastness, monotonicity, idempotence, union preservation | Checkpoints, shared ancestor closure reuse, grouped roots |
| `C-*`: certificate | Valid closure certificate implies exact equality to reachability | Independently checked cached or heuristic-produced closure results |
| `M-*`: missing state | The least-additional-set theorem in §3.4 | Missing manifests and readiness predicates |
| `R-*`: partition | Restricting an expression to disjoint ordinal intervals composes to the whole result | CPU/GPU tiling and independent scheduling |
| `R-*`: reduction | Statistics of disjoint union equal the combination of partial statistics | Fused difference-and-reduce; no intermediate bitmap allocation |
| `Q-*`: planning | Each rewrite and compiled plan preserves denotation | Query DAG sharing, fusion, reordered work, adaptive backend choice |
| `I-*`: incremental | Valid extension/update equals fresh evaluation | Reuse after inventory changes and graph append |
| `E-*`: evidence | Reported witness paths use real edges from a requested root | Explainability without trusting an optimizer's narrative |
| `B-*`: backend | Checked word operations, tile execution, and reductions refine their specifications | Flat native/Metal kernels with exact integer results |
| `D-*`: durability | Decoding a validated stored representation preserves its denotation | Persistent indexes; corruption and version rejection |

### 4.1 Closure laws

Prove at least:

\[
R\subseteq C(R),\quad C(C(R))=C(R),
\]

\[
A\subseteq B\Rightarrow C(A)\subseteq C(B),
\]

\[
C(A\cup B)=C(A)\cup C(B),\quad C(\varnothing)=\varnothing.
\]

The closure operation is a closure operator that also preserves finite unions. It is **not** a Boolean-algebra homomorphism.

**Forbidden rewrites:** in general,

\[
C(A\cap B)\ne C(A)\cap C(B),
\]

\[
C(A\setminus B)\ne C(A)\setminus C(B).
\]

For example, let `a -> x` and `b -> x`. The closures of `{a}` and `{b}` intersect at `x`, although their root sets do not intersect. In the same graph, closing `{a} \ {b}` keeps `x`, while subtracting the two closures removes it. Put these counterexamples in permanent tests.

Do not push object-type filters through reachability without a distinct, proved graph-policy transformation. Removing commit vertices before traversal can erase paths to required blobs.

### 4.2 Missing-state composition

Useful laws include:

\[
(A\cup B)\setminus H=(A\setminus H)\cup(B\setminus H),
\]

\[
A\setminus(H_1\cup H_2)=(A\setminus H_1)\setminus H_2.
\]

The second permits successive local, LAN, and upstream inventory filtering. It does not imply those tiers are authorized or physically reachable; those are future service contracts.

For additions-only inventory updates:

\[
M'=K\setminus(H\cup A)=(K\setminus H)\setminus A.
\]

For general patches, define precedence explicitly, for example:

\[
\operatorname{patch}(H,D,A)=(H\setminus D)\cup A.
\]

“Add wins” is part of this patch semantics. Such patches are not automatically commutative. Independently certify any restricted commuting-update law before parallelizing updates to the same inventory.

### 4.3 Statistics form a monoid over disjoint partitions

Let `w(x)` be a nonnegative logical payload size. Define:

\[
Stats(A)=(|A|,\sum_{x\in A}w(x),countsByType(A)).
\]

For **disjoint** sets `A` and `B`:

\[
Stats(A\uplus B)=Stats(A)\oplus Stats(B),
\]

where `⊕` is componentwise addition. This enables parallel reduction over disjoint ordinal ranges.

For overlapping sets, adding counts double-counts shared objects. Do not cache `Stats(Union(a,b))` as `Stats(a)+Stats(b)` without proving disjointness or accounting for overlap.

`IsEmpty` can use a Boolean reduction and early exit. It must not pay to count every result. Conversely, a successful exact `Stats` query cannot stop after its first missing object.

### 4.4 Closure certificates: a small, useful verified checker

For a candidate set `C`, record a witness predecessor and a natural-number rank for every non-root member. Accept only when:

1. `R ⊆ C`.
2. Every required outgoing edge of a member of `C` stays inside `C`.
3. Every `v ∈ C \ R` has a predecessor `u ∈ C` with `u -> v` and `rank(u) < rank(v)`.
4. All identities, ranks, and graph/policy bindings validate.

Conditions 1–2 prove `Reach(R) ⊆ C`. The well-founded predecessor chains prove `C ⊆ Reach(R)`. Therefore acceptance establishes exactness—not merely an overapproximation.

A traversal can emit this certificate as it discovers vertices. A cached result from a different implementation can also be checked against the independent graph. Certificate size and validation cost are charged to index construction, not repeated for every hot query. After a validated immutable cache entry is bound to its graph generation, subsequent queries can reuse it under the cache laws.

The checker does not establish that an imported graph matches a real repository. That remains an adapter contract.

---

## 5. Representation: persistent sets, not an all-pairs bitmap allocation

### 5.1 Separate three structures

Keep distinct:

- **Object graph:** dependency edges.
- **Persistent set values:** concrete immutable object sets.
- **Query DAG:** unevaluated expressions over those values.

A cached `Union(a,b)` expression is not necessarily a materialized set. Distinguish it in types and storage to prevent accidental infinite recomputation or accounting errors.

### 5.2 Persistent set layout

Use a binary tree over fixed ordinal intervals. A node is one of:

```text
Zero(range)
Full(valid_range)
SparseLeaf(sorted_unique_offsets)
DenseLeaf(128 logical U32 words)
Branch(left, right)
```

The initial dense leaf covers 4,096 positions. All high padding bits above N are zero. `Full` means full **within the node's valid range and universe generation**, not unbounded full storage capacity. Sparse offsets are sorted, unique, and in range. Branch children partition their parent interval exactly.

Suggested initial sparse/dense crossover: 64 members per leaf. This is a benchmark parameter, not a semantic constant. Support `Zero` and `Full` compression first; do not build a general compression zoo.

Persistently updating `k` affected leaves copies the affected paths and leaves, not the entire universe. An individual update has a target bound proportional to tree height plus leaf work. Sharing is an opportunity, not a promise of canonical structure or optimal memory use.

### 5.3 Structural shortcuts

For the same immutable node, range, and generation:

```text
A \ A      => Zero
A \ Zero   => A
A \ Full   => Zero
Zero \ B   => Zero
A ∪ A      => A
A ∩ Full   => A
```

Pointer/node-ID equality is a sound shortcut only within the owning immutable arena and identity generation. Digest equality alone must not become an unconditional mathematical equality axiom. Hash-consing must validate equal structural keys on collisions, or explicitly add a cryptographic assumption to the trust boundary. A cache miss due to different representations of equal sets is acceptable.

### 5.4 Numeric refinement

The specification uses mathematical naturals. The hot path uses `U32` bitmap words and checked, bounded offsets. For v0.1, support at most `2^32 - 1` object ordinals per universe and reject larger imports explicitly. This is a documented first-release limit, not an undocumented wraparound.

Use a checked pair-of-`U32` representation for 64-bit sizes, counts where necessary, offsets, and sums. Prove conversion, addition, comparison, and overflow detection against natural-number arithmetic. Admitting a weight table requires its total universe weight to fit this accumulator, so every subset reduction fits too; reject a larger table explicitly. Other aggregate/offset overflow returns `NumericOverflow`; it never silently wraps or saturates. Decimal JSON counters are strings to avoid downstream number-precision loss.

A dense leaf contains 512 bytes of *logical* bitmap payload. Its actual Bend heap footprint may be larger. Measure the emitted representation rather than reporting logical payload as resident memory.

### 5.5 Universe growth

Append-only generations preserve old ordinal meanings. Lift an old set by extending membership with false for newly registered identities.

Prove lifting preserves union, intersection, and difference. It does **not** preserve universe-relative complement or `Full` unchanged:

\[
lift(U_n\setminus A)\ne U_{n+1}\setminus lift(A)
\]

when the universe gains members. Tail masking and `Full` expansion are release-critical tests. A newly discovered object must not appear in yesterday's inventory because unused bitmap capacity happened to contain ones.

Unrelated universes require an explicit validated OID translation. Rebuilding an index may change ordinal order; semantic comparison must use object identities.

---

## 6. Closure indexing and incrementality

### 6.1 Start with a reference traversal

Implement a simple frontier traversal in Bend using a visited set. Maintain:

```text
seen ⊆ reference closure
frontier ⊆ seen
roots ⊆ seen
all expanded vertices have their successors in seen
```

Each vertex is expanded at most once. Use a well-founded measure or an explicit decreasing natural budget derived from the finite graph. Do not use `@unsafe` to bypass termination in the proved core.

The executable mathematical evaluator can be slow. The production traversal must share these contracts, not this exact data layout.

### 6.2 Cache only selected closures

Do not precompute an N-by-N transitive closure or one full bitmap per commit. Cache requested roots, selected checkpoint roots, and hot subclosures under a memory budget. Build statistics must report cache bytes and total indexed memberships.

During traversal, a validated checkpoint can contribute its entire closure and stop exploration of that checkpoint. The union law and checkpoint exactness justify this shortcut. Changing checkpoint selection must not change results.

For a graph segment validated to be acyclic, bottom-up closure composition is allowed. A generic cyclic graph uses frontier traversal or a separately verified SCC strategy. SCC optimization is not required for v0.1.

### 6.3 Exact cache keys

Use at least:

```text
(namespace, universe_lineage, graph_generation, policy_version,
 root_set_identity, operation_semantics_version)
```

Stats caches additionally bind the weight/type-table version. Inventory differences bind both inventory generations. Never key a closure by a bare moving ref name.

### 6.4 Valid graph extension

An immutable graph append can reuse an old closure only when the old vertices' outgoing adjacency is unchanged and complete. New vertices may point to old vertices. If old metadata is filled in, a policy changes, replacement semantics change, or an old outgoing edge is added, invalidate or rebuild affected closures.

Prove, for a validated extension embedding `j`:

\[
C_{G'}(j(R))=j(C_G(R))
\]

for old root sets. New roots are evaluated against `G'`, combining old checkpoints where legal.

Inventory changes are a separate axis: objects may be evicted even though the graph and ordinal universe are append-only. Never infer monotone availability from immutable object identity.

### 6.5 Durable snapshots

The derived store is single-writer in v0.1. Write new segments, validate checksums and structure, flush required data, and atomically publish a manifest. Readers retain the old manifest until they finish. Crashes and cancellation cannot publish half-built sets or closure certificates as valid.

On load, validate format/version, bounds, node references, acyclicity of the representation DAG, and universe bindings. A file checksum is not a substitute for structural validation. On reopening a persisted closure entry, revalidate its certificate against the exact graph/policy before reuse; v0.1 does not assume an authenticated prior-validation service. Account for this once-per-load cost. Treat local files as corruptible input.

---

## 7. Query compilation and high-performance execution

### 7.1 The pipeline

```text
Git/raw manifests
    -> parsed, validated immutable snapshots
    -> typed query expression
    -> semantics-preserving rewrites
    -> CPU traversal and structural pruning
    -> compact leaf-job plan
    -> native CPU or Metal evaluation
    -> deterministic reduction / requested enumeration
    -> structured result with provenance
```

Logical optimization and hardware lowering are separate stages. This prevents the proof of a set identity from silently depending on one GPU layout.

### 7.2 Essential optimization: fused difference statistics

For a matrix cell, do not allocate `Missing = Required \ Have` merely to count it. Generate:

```text
for each word in this tile:
    bits = required_word AND NOT have_word
    accumulate popcount(bits)
    accumulate requested type counts and weights
```

**Resolve reachability before ordinal-local execution.** Graph paths can leave one ordinal tile and return to it. Therefore `Reach(R) intersect I` is not generally the closure of `R intersect I` inside the induced graph on I. Leaf jobs operate on already established set values or pointwise Boolean expressions, never independently truncated graph traversals.

The mask is restricted to valid ordinal positions. Weight accumulation can iterate set bits or use a measured dense path. Weighted sums are not “free” with popcount; report that additional work.

Prove:

\[
FusedStats(A,B)=Stats(\llbracket A\rrbracket\setminus\llbracket B\rrbracket).
\]

Only materialize object IDs or a missing bitmap when the caller asks. A million matrix cells must not imply a million full-universe output bitmaps.

### 7.3 Disjoint tiles and work ownership

A plan partitions each result over nonoverlapping ordinal ranges. Its obligations are coverage, disjointness, bounded input reads, exact leaf semantics, and correctly associated outputs. Aggregate results in a deterministic balanced reduction.

Outputs are independently owned records or buffers. Do not let two workers write different bits in the same physical word. Work ownership includes machine-word write granularity, not just logical element indices.

A simple schedule returns one result record per job and reduces records later. Shared mutable result arrays and atomics are not required for the first path.

### 7.4 Native and Metal division of labor

Keep metadata parsing, irregular graph traversal, tree pruning, cache interning, small sparse operations, and tiny queries on the CPU. Send large homogeneous batches of dense difference/count jobs to Metal. Batch compatible work across queries; group by kernel kind and estimated cost.

The inspected Bend runtime documents balanced fork/join execution and CPU fallback for GPU-marked calls. Its shader guide recommends bounded fork trees ending in flat loops, and warns about shared-reference-count overhead. Treat its tuning numbers as observations about that runtime/example, not universal constants. [S1, S2]

Build the job frontier once, fork to a measured number of approximately equal work packets, and execute flat loops at leaves. Avoid a fork per bit, a GPU launch per set node, and pointer-chasing the full graph in every GPU lane. Specialize kernel families at compile time; pass runtime constants and descriptors rather than capturing giant structures in closures.

### 7.5 The memory-substrate experiment is mandatory

Ordinary Bend arrays are affine, and the inspected guide says their indexing wraps. Therefore a shared random-access bitmap arena is not an API we can simply assume exists. [S1]

First benchmark an implementation using host-owned immutable `Data` word blocks with provably safe reads and verified compiler borrowing. Inspect emitted code for hot-loop reference-count activity. Compare this against owned tile-local data and an optimized C baseline.

If this representation is insufficient, make a narrow, explicit runtime/compiler contribution:

```text
FrozenWords: immutable, lifetime-pinned word storage
ReadSpan: bounded read view into FrozenWords
OwnedTile: exclusive output ownership
```

These are **proposed primitives**, not current Bend library APIs. A GPU-readable intrinsic needs supported native and Metal lowering; a host-only foreign IO function does not solve it. Specify its sequential model, bounds, borrowing lifetime, release ordering, and implementation trust obligations. Keep difference, popcount, traversal, and reduction in Bend.

Do not hide the entire fast engine in C and prove a separate toy Bend interpreter.

### 7.6 Unified memory and backend reporting

The host constructs immutable inputs, submits work, and retains those inputs until completion. Shared memory removes the need for a duplicate transfer representation where the allocation really is shared; it does not remove synchronization, cache traffic, or allocation costs. Apple documents explicit CPU/GPU ordering requirements. [S4]

Expose `--backend auto|cpu|metal`. In forced Metal mode, fail if GPU execution cannot actually occur. `auto` may use CPU. Every benchmark/result diagnostic reports requested backend, actual backend, dispatch count, copied bytes, layout-conversion time, and kernel time.

A source-level theorem relates the common algorithm to its model. It does not by itself verify the compiler, Metal driver, or hardware. Differential execution is an additional check, not a replacement for that distinction.

### 7.7 Matrix scaling

Deduplicate equal inventory roots and equal requirement roots before evaluating pairs. Reuse identical leaf-operand pairs. Prune zero/equal/full subtrees. Tile the remaining matrix and return bounded summaries.

For perspective, 10 million objects require 1.25 MB per dense bitmap. One million pair comparisons can entail approximately 2.5 TB of operand reads in a naïve two-input implementation, before weight reads and outputs. This is arithmetic, not a forecast. The system must report actual work avoided and actual bytes processed rather than implying that a GPU makes any matrix cheap.

---

## 8. Git adapter and compatibility contract

### 8.1 Separate graph construction from inventory observation

A **graph snapshot** says what named objects require. An **inventory observation** says what a selected object store reports as locally present. They are different data products.

Import a complete source graph from explicit roots. This initial source must provide the full superproject object closure for those roots; a shallow or partial source with unavailable dependencies is rejected for full import. It may be expanded explicitly in a later operation, never by hidden network activity during a query.

A receiver can be a partial clone or incomplete cache. Its raw local inventory is projected by object identity into the source universe. Objects outside that universe are reported as out-of-scope inventory entries, not mistaken for source requirements or discarded without accounting. No receiver-graph closure assumption is needed.

### 8.2 Policy table

| Git object/edge | `full` | `tree-data` |
|---|---|---|
| Requested root object | Include | Include |
| Annotated tag -> target | Follow | Follow |
| Commit -> root tree | Follow | Follow |
| Commit -> parent commits | Follow | Do not follow |
| Tree -> subtree | Follow | Follow |
| Tree -> regular/executable blob | Follow | Follow |
| Tree -> symlink blob | Include blob, do not follow link contents | Same |
| Tree gitlink -> submodule commit | Record external reference; do not traverse another repository | Same |
| Blob | Terminal | Terminal |

`tree-data` means enough ordinary superproject object content to describe the selected snapshot, not enough to guarantee every `git checkout`, build, submodule operation, or smudge filter succeeds. LFS payloads, submodule repositories, external filters, filesystem permissions, case sensitivity, and toolchains are separate requirements. Git's object and submodule documentation provide the adapter basis. [S5, S6]

A full closure contains historical blobs. Consequently it is the wrong requirement for an agent that only needs current tree data. Keep mode explicit in commands, cache keys, and receipts. The initial full source import can support both policies without a separate source-tree-only importer.

### 8.3 Import flow

1. Discover repository location/common directory and object format using Git plumbing, not assumptions about `.git` being a directory.
2. Resolve requested roots to complete IDs. Record the resolved vector and acquisition metadata.
3. Fetch metadata and raw bodies for reachable commits, trees, and tags through a persistent buffered Git subprocess. Read blob type/size metadata without scanning blob contents unnecessarily.
4. Parse length-delimited raw records. Build labeled adjacency and immutable type/size tables in Bend.
5. Validate object IDs, target types, tree modes, record bounds, duplicate/inconsistent metadata, and the closed graph domain. Fail explicitly on required missing objects.
6. Intern object identities, construct the graph, and build demand-driven closure entries/certificates.
7. Publish a validated derived generation.

Git's buffered `cat-file` modes are the initial IO boundary, not the production reachability algorithm. `--batch-all-objects --unordered` is useful for receiver inventory enumeration, including alternate stores; raw content must be consumed by declared length, not line parsing. [S7]

Use a sanitized subprocess environment and literal argv. Disable replacement objects and lazy fetching. Git exposes `--no-replace-objects` / `GIT_NO_REPLACE_OBJECTS` and `--no-lazy-fetch` / `GIT_NO_LAZY_FETCH`. Do not invoke filters, text conversion, hooks, shell aliases, or repository-supplied code. Detect and reject unsupported graft/shallow-history semantics. [S8]

### 8.4 Supported format and error scope

Support SHA-1 and SHA-256 object-ID widths through an explicit object-format tag. If the pinned Git build cannot support one format, report that capability and reject it rather than assuming 20-byte IDs. Tree names are raw bytes, not necessarily valid UTF-8; evidence output escapes them losslessly.

The parser contract is soundness and completeness for the **declared supported metadata grammar**, with explicit resource limits. It is not a claim to implement every `git fsck` check. The Git object-to-content mapping and decoding are trusted in normal mode. Optional strict verification may invoke Git integrity checks and must report its separate cost and assurance.

No claim of hash collision impossibility is required by the finite-set algebra: identity equality is equality of complete namespace/format/ID keys. The external premise that those keys name the intended bytes remains separate.

### 8.5 Snapshots and concurrent mutation

Ref resolution, graph collection, and inventory enumeration are not automatically one atomic filesystem transaction. Prefer a quiescent mirror or externally retained object store during import. Pin the resolved root vector; report observation start/end and provenance. Abort on missing/inconsistent required data rather than silently retrying with a different root.

Once published, the derived graph is immutable even if the live repository changes. A query answer is exact for its named observations. It is not a promise that the original disk still contains every recorded object. The first release has no physical retention authority over a user's repository.

---

## 9. Results, CLI, and errors

### 9.1 Proposed user workflow

The commands below define the intended interface; the engineer implements them. All commands accept global `--store PATH`. Default to a user-owned derived-cache directory (`~/Library/Caches/ProofPack` on macOS, or `$XDG_CACHE_HOME/proofpack` with `~/.cache/proofpack` fallback elsewhere). Do not create or modify repository configuration. The requested aliases below are names within this derived store.

```sh
# Import the source graph and selected root snapshots.
pp git import --repo /repos/project --as source \
  --root refs/heads/main --root refs/heads/feature

# Capture inventories. Remote machines can run export locally and send the file.
pp git inventory --repo /repos/project --as laptop
pp git inventory-import --file worker-17.inventory.json --as worker-17

# Exact state questions at recorded snapshots.
pp git missing --graph source --want refs/heads/feature \
  --mode tree-data --have worker-17 --output stats
pp git ready --graph source --want refs/heads/feature \
  --mode tree-data --have worker-17
pp git missing --graph source --want refs/heads/feature \
  --mode full --have worker-17 --output oids

# Batch protocol: requests identify immutable resolved roots/inventory generations.
pp git matrix --request placement.json --backend auto

# Explain one dependency and preview logical retention effects.
pp git explain --graph source --root refs/heads/main --object <full-oid>
pp git retention --graph source --roots-file retained-roots.json \
  --remove refs/heads/feature
```

Stored ref aliases resolve within the named graph snapshot. Updating the live Git ref does not mutate an old snapshot's alias. Require explicit import/update to observe new roots.

### 9.2 Result envelope

```json
{
  "schema_version": 1,
  "query_semantics": "proofpack-state/v1",
  "universe": {"namespace": "project", "lineage": "u1", "generation": "7"},
  "graph_snapshot": "g7",
  "policy": "git-tree-data/v1",
  "inventory_snapshot": "worker-17/i12",
  "completeness": "complete",
  "inventory_assurance": "trusted-odb-observation",
  "availability_scope": "recorded-observation-only",
  "result": {
    "ready_at_observation": false,
    "missing_objects": "41",
    "logical_payload_bytes": "184202"
  },
  "execution": {
    "requested_backend": "auto",
    "actual_backend": "cpu",
    "gpu_dispatches": "0"
  }
}
```

The numbers are illustrative, not benchmark results. Include implementation/compiler identifiers in actual receipts. Do not label a result `mathematically_verified` merely because its binary ships with proofs. Identify the law bundle and imported-data assumptions separately.

Large results use a cursor tied to the immutable query/environment digest. Distinguish `completeness` from pagination: a complete query may have more result pages. A budget-limited computation is not a complete query with zero results.

### 9.3 Required error classes

`InvalidInput`, `UniverseMismatch`, `UnknownRoot`, `UnsupportedPolicy`, `IncompleteGraph`, `UnsupportedRepository`, `CorruptIndex`, `NumericOverflow`, `ResourceLimit`, `BackendUnavailable`, `ObservationInvalidated`, and `Cancelled`.

Use structured error payloads and stable machine-readable codes. For the CLI, use exit 0 for successful complete queries (including empty sets), exit 1 for a complete negative `ready` predicate, exit 2 for rejected/failed queries, and exit 3 for resource-limit/cancellation without complete results. The JSON status remains authoritative for clients.

### 9.4 Availability uncertainty: model it before building a service

For v0.1, exact queries accept a caller-asserted exact inventory observation, with its evidence stated. A stale worker advertisement must not be relabeled as current availability.

Reserve a later interval inventory type `L ⊆ H ⊆ U`, with all sets scoped to the relevant universe. Then:

\[
K\setminus U\subseteq K\setminus H\subseteq K\setminus L.
\]

`K ⊆ L` establishes coverage under the evidence; `K \ U != empty` establishes missing state; otherwise readiness is unknown. This refinement avoids redesigning the algebra when distributed observations arrive.

A future live `ReadyLease` needs atomic pinning, transfer verification, lease expiry, and eviction coordination. Set inclusion alone is not a lease.

---

## 10. Trust boundary and proof workflow

### 10.1 What this release proves

Target proofs over the actual set implementation, closure algorithm/checker, query rewrites, tile planning, arithmetic refinement, fused statistics, inventory updates, and serialization models. Tie their definitions together through the compiler contract.

Initially trusted or externally validated components include Git decoding and object identity mapping; filesystem and subprocess effects; compiler lowering; any proposed native storage primitive; runtime scheduling; Metal/OS/hardware; and the assertion that a recorded inventory described actual readable storage at observation time.

The inspected Bend guide provides a second checking path through `--safe` (`--verdict` from 2.0.32), but explicitly identifies the translation from Bend to the kernel's language as itself unproved. Record that in `TRUST.md`; do not advertise a verified driver or fully proved distributed system. [S1]

### 10.2 Repository structure

```text
SPEC.md                     this contract
LAWS.bend                   reviewed public claims importing production modules
PROOF.bend                  proof root importing and discharging LAWS.bend
TRUST.md                    trust assumptions and unsafe/foreign inventory
OPTIMIZATIONS.md             each enabled rewrite linked to law IDs

spec/                       finite-set, graph, query, and result denotations
core/                       checked words/integers, set representation, updates
closure/                    reference traversal, production traversal, certificates
query/                      validated AST, rewrites, plans, fused evaluators
execute/                    native/Metal leaf jobs and reductions
index/                      generations, manifests, cache serialization
adapters/git/               metadata parsing, policies, inventory observations
host/                       minimal IO effects and any documented storage primitive
cli/                        command and bounded JSON batch interface
proofs/                     proof implementations, imported by PROOF.bend
fixtures/                   graph, Git, adversarial, and malformed-input cases
bench/                      C/reference baselines and reproducible workload manifests
```

Module names can be adjusted to the pinned Bend module syntax. Keep the denotational model independent of its optimized representation and IO.

### 10.3 Change discipline

Engineers may replace algorithms and representations while preserving public laws. Changes to semantics, supported input domains, or law preconditions require explicit review. An implementation must not make a law vacuous by rejecting previously supported valid inputs.

Every optimization entry names its preconditions, law IDs, production symbols, property tests, counterexamples, and benchmark. CI fails if a public law is unresolved or a supposedly proved path depends on unreviewed unsafe/foreign code.

Ship exported checker artifacts, the toolchain lock, completed-law registry, generated-code inspection summaries, and test/benchmark manifests. Erased proof arguments should not travel in hot runtime data structures.

---

## 11. Testing and performance acceptance

### 11.1 Independent correctness checks

Use three independent comparisons:

- Denotational/reference evaluator versus production Bend algorithms.
- Native versus Metal execution over identical validated plans.
- Git adapter/closure results versus competent Git plumbing over the same roots and semantics.

For full superproject closure, compare with `git rev-list --objects --no-object-names` under the same no-replacement, complete-history assumptions. For `tree-data`, compare explicit commit/tag roots plus an independent recursive tree enumeration, including intermediate trees and symlink blobs but excluding submodule target traversal. Do not use the production parser to generate both sides of the expected result.

Git already supports reachability bitmap acceleration. Include it in relevant baselines rather than comparing only against repeated cold subprocess traversals. [S9]

### 11.2 Required adversarial cases

Test empty sets/graphs, isolated roots, cycles, diamond sharing, merge parents, deep chains, duplicate objects, duplicate roots, tags to tags/trees/blobs, symlinks, gitlinks, zero-byte blobs, SHA-1/SHA-256, malformed/truncated metadata, invalid OIDs, unexpected target types, binary/non-UTF-8 names, unavailable required objects, and corrupt indexes.

For bitmaps test boundaries at 0, 1, 31, 32, 33, 4,095, 4,096, and 4,097 positions; tail masking; sparse/dense conversion; `Full` under universe extension; mixed generations; and checked arithmetic overflow. Test type/weight-table changes invalidating derived statistics.

For updates test additions, removals, conflicting patches under documented precedence, graph append with unchanged old adjacency, and rejected reuse after changed old adjacency. Keep mutation tests for omitted edges, extra unreachable certificate members, illegal closure-distribution rewrites, reversed difference, and padding bits counted as objects.

### 11.3 Benchmarks

Benchmark cold import, incremental import, first query, hot repeated query, batched distinct queries, inventory patches, and result enumeration separately. Use real repositories and synthetic stress graphs. Simulated inventories must be identified as simulated; a worktree's root is not a measured machine inventory.

Native baselines include optimized C dense bitsets, a competent sparse/bitmap implementation where appropriate, and Git's own bitmap-assisted traversal. Benchmark equal semantics and include preprocessing, data-layout conversion, cache memory, output size, and warmup.

Required reporting: graph vertices/edges; physical inventory count versus agent count; logical pair count versus distinct pair count; structural branches pruned; dense words actually scanned; bytes copied; indexed memberships; resident/peak memory; cold/warm latency distributions; backend/dispatch data; and proof-check/build time.

Measure small queries too. `auto` must avoid dispatching a GPU merely to demonstrate that it exists. Run interleaved CPU/Metal trials with fixed inputs, including an A-versus-A noise control. No numerical speedup is assumed in this specification.

### 11.4 Release gates

A correctness release requires all mandatory laws discharged, zero mismatches on the independent fixtures/corpora, complete error handling, clean forced-backend reporting, and no writes to user repositories.

A performance release additionally requires an end-to-end advantage over the agreed baseline on at least one declared **repeated Git-state workload**, with preprocessing and memory reported. Metal earns automatic use only in a measured regime where it improves the optimized native implementation after planning/dispatch costs. If that regime does not yet exist, ship a useful native product and identify Metal as experimental; do not fabricate a speed claim.

---

## 12. Implementation layers and ticket order

Each milestone ends with a usable or independently testable artifact. Parallelize work on proofs and execution, but do not postpone the first real Git integration until every optimization exists.

| Milestone | Build | Required evidence |
|---|---|---|
| **M0 — semantic and substrate spike** | Finite-set model, checked words, simple dense difference/count, graph reference evaluator, native/Metal experiment | Word/tile laws; CPU/Metal equality; emitted-layout measurements; decision on borrowed blocks versus a storage intrinsic |
| **M1 — first Git utility** | Buffered Git importer; full/tree-data policies; sparse/reference missing and ready; JSON output; closure certificates | Real two-repository example; exact closure and least-missing proofs; Git differential tests |
| **M2 — persistent algebra** | Binary persistent sets, sparse/dense conversion, generational store, inventory patches, checkpoint closures | Representation, persistence, update, and checkpoint laws; bounded index memory; old snapshots remain valid |
| **M3 — query compiler** | Typed AST, validated rewrites, fused stats, explanations, matrix deduplication and tiling | Compiler/refinement laws; real repeated-state benchmarks; no per-pair full bitmap allocation for stats |
| **M4 — accelerated v0.1** | Production native executor, Metal leaf path, automatic cost threshold, incremental graph append | Safe proof gate, actual backend reporting, end-to-end measurement, all v0.1 acceptance tests |
| **M5 — local state service, later** | Shared object cache, atomic preparation/pinning, lease state machine, explicit Git-assisted transfer | Conditional preparation and eviction invariants tied to real storage transitions |
| **M6 — more domains, later** | Build CAS manifests and input-root adapters; then distribution/worker services | Reuse of the same set/closure core, domain-specific validity and authorization laws |

### First engineering tickets

**T01: Pin and exercise Bend.** Build a trivial native and forced-Metal program using the pinned source/artifact. Record actual backend execution and inspect how immutable shared words are read. Do not publish performance claims yet.

**T02: Write the semantic types and public laws.** Implement finite ordinals, pointwise sets, graph closure specification, query denotation, and the least-missing theorem. Include the forbidden-rewrite counterexamples from day one.

**T03: Prove the first flat kernel.** Difference plus count over bounded `U32` words; explicit final-word mask; disjoint tile reduction; checked aggregate arithmetic. This is the first proof-and-performance demonstration.

**T04: Implement the bounded Git metadata effect and parser.** No network, no filters, no source-language parsing. Build the tiny Git fixture and independently compare graph edges.

**T05: Ship `missing`, `ready`, and `explain` on a real repository pair.** Use the simpler set representation if necessary. This must precede a full distributed daemon, VM runner, or sophisticated cache policy.

**T06: Add persistent leaves and fused matrix plans.** Retain the simple evaluator as an oracle. Introduce optimizations one at a time, with enabling laws and measured effects.

---

## 13. Future compatibility without expanding v0.1

For a future build action, required input artifacts form a graph closure. A cached action result is an **optional alternative to execution**, not automatically another mandatory edge in the same conjunction-only graph. The adapter must choose a plan, then supply its hard requirements to this core. It must separately verify action identity, platform/configuration dependencies, and cache-publication trust.

For future retention, the abstract invariant `Evicted ∩ Pinned = empty` is useful, but physical pack deletion also depends on surviving representations and delta bases. Root selection is also a policy input: refs alone omit potential retention obligations from reflogs, detached worktrees, indexes, and grace periods. Do not call an explicitly scoped preview the complete Git GC root set. Do not turn `retention` output into a deletion command without another storage refinement layer. Git's pack representation and reported per-object disk size are not stable logical object properties. [S7, S10]

For future distribution, inventory union denotes aggregate coverage across locations, not necessarily local readiness. A source-cover planner may be heuristic. Its checker must establish coverage, authorization, representation validity, and the appropriate leases. A snapshot proof does not establish continued availability on a failed or malicious machine.

For future cells/VMs, the current library supplies requirements and inventory facts. Isolation, browser profiles, process supervision, APFS clones, and credential handling are separate adapters and policies. None belongs in the v0.1 mathematical kernel.

---

## 14. Definition of done

An engineer can demonstrate the following without changing Git storage:

1. Import an explicitly scoped source graph and inventories from two real repositories.
2. Compute `full` and `tree-data` requirements and explain why they differ.
3. Return exact missing IDs, readiness-at-observation, logical byte totals, and a dependency witness.
4. Add an inventory patch and a valid graph extension while reusing unaffected persistent state.
5. Execute a batch through native CPU and actual Metal paths, obtaining identical results.
6. Show the laws authorizing pruning, checkpoint reuse, tiling, and fusion; show mutation tests fail when those semantics are broken.
7. Report realistic end-to-end costs, a bounded index, explicit trust assumptions, and honest limits.

**The first shipping product is a proved Git-state calculator. The enduring asset is its compositional denotational core and verified execution compiler.**

---

## Sources and verification notes

These sources establish existing tool behavior. All project APIs, laws, data structures, milestones, thresholds, and performance gates above are design decisions or mathematical derivations, not assertions that upstream already implements ProofPack.

- **[S1] Bend2 source and guide**, pinned revision `af569d4826913b2ce3557e9829ccad31fcf86f94`: https://github.com/bendlang/bend/tree/af569d4826913b2ce3557e9829ccad31fcf86f94 ; https://github.com/bendlang/bend/blob/af569d4826913b2ce3557e9829ccad31fcf86f94/guide/GUIDE.md . Laws/proofs, `--safe` limitations, affine arrays, native/GPU execution. Toolchain inspected 27 September 2026.
- **[S2] Bend shader guide**, same revision: https://github.com/bendlang/bend/blob/af569d4826913b2ce3557e9829ccad31fcf86f94/guide/SHADERS.md . Runtime-specific work shaping and borrowing guidance; the guide identifies itself as AI-written and pending human revision. Treat empirical numbers as workload-specific.
- **[S3] Git worktree documentation:** https://git-scm.com/docs/git-worktree . Shared repository state and per-worktree metadata.
- **[S4] Apple, Synchronizing CPU and GPU work:** https://developer.apple.com/documentation/metal/synchronizing-cpu-and-gpu-work . Resource synchronization remains necessary with shared storage.
- **[S5] Git object-format documentation:** https://git-scm.com/docs/gitformat-pack . Object types, object-ID formats, and distinction between logical objects and pack representations.
- **[S6] Git submodule documentation:** https://git-scm.com/docs/gitsubmodules . Gitlinks and separate submodule repositories.
- **[S7] Git cat-file documentation:** https://git-scm.com/docs/git-cat-file . Buffered batch IO, inventory enumeration, raw object bodies, and caveats on physical sizes/delta bases.
- **[S8] Git command/environment documentation:** https://git-scm.com/docs/git . No-replacement and no-lazy-fetch controls.
- **[S9] Git rev-list and bitmap documentation:** https://git-scm.com/docs/git-rev-list ; https://git-scm.com/docs/bitmap-format . Competent reachability baselines and existing bitmap support.
- **[S10] Git pack-format documentation:** https://git-scm.com/docs/gitformat-pack . Delta-base representation dependencies.

No Bend implementation was compiled or formally checked in preparing this specification. The handoff's small machine-readable fixtures and optional Python reference checker are specification aids, not Bend proofs or performance measurements.
