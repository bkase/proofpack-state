# Trust boundary

What this release proves, what it checks at run time, and what it trusts
outright. SPEC 10.1 requires this list; it is meant to be read before any
claim about ProofPack State is repeated elsewhere.

The short version: **the algebra is proved, the traversal is checked per
query, and everything that touches a real repository is trusted.** No result
is labelled "mathematically verified" because the binary ships with proofs.

---

## 1. Proved

`bend PROOF.bend` discharges every law in `LAWS.bend`, and
`bend PROOF.bend --safe` rechecks the result with the BendTT kernel, which
has a proof in Lean. On this machine, with Lean 4.28.0-rc1, both pass and
`--safe` excludes nothing: no law's proof reaches an `@unsafe` def or a
foreign definition.

The proofs cover:

| Family | What is proved |
|---|---|
| `B-01` | the word kernel: difference, union and intersection are pointwise; shifting reads the next bit up; the tail mask covers exactly the low bits; the production popcount counts exactly the bits `U32.bit` reports set; the fast shift-and-test agrees with the bit accessor |
| `B-02` | the checked accumulator's equations (identity, commutativity, associativity) |
| `S-01` | the tile kernel: difference, union and intersection are pointwise over word lists, for operands of any two lengths |
| `R-01` | restriction: every tile law is *at a position*, which is the partition law in concrete form |
| `R-02` | statistics are a commutative monoid; one object counts once |
| `Q-02` | the fused count equals counting the built difference |
| `M-01` | the least additional object set, in full: `H u (K \ H)` covers `K`, and `K` inside `H u T` exactly when `(K \ H)` inside `T` |
| `M-02` | readiness is an empty difference |
| `M-03` | missing distributes over a union of requirements; inventory tiers compose |
| `I-01` | an additions-only update needs no re-derivation; "add wins" in a patch |
| `P-01` | inserting an ordinal into a structurally valid set leaves it present, at the depth the product runs at, with no hypothesis on the ordinal. The sharing half -- that retained old roots are undisturbed -- is a property of Bend's affine values, not an equation; §3 |
| `G-02` | at a row: the tree-data filter drops exactly the commit targets. Lifting that to `Graph.edge` over the assembled tries is still open |
| `E-01` | of a produced dependency witness: every step is a real policy edge, and it ends at the object asked about. That it *starts* at a root depends on the levels being a genuine BFS layering, which is `C-02` |
| `S-02` | set difference, union and intersection are pointwise at the production depth, for structurally valid operands and every `U32` ordinal |
| `S-03` | compression changes no member, whichever of its four representations it picks |
| `S-04` | the emptiness test only accepts a set with no members, and the three admitted Boolean rewrites follow |
| `C-03` (part) | closing the empty set gives the empty set -- at `PZero{}` and, pointwise, for any set the emptiness test accepts, which is what the optimizer actually holds |
| `Q-01` (part) | every rewrite the query optimizer performs keeps the denotation, stated over the emptiness decision as the rewriter computes it. The whole pass -- which also recurses inside `Reach` and `Filter` -- needs closure to respect pointwise equality and is still open |
| shape | the set operations, insertion included, keep a set in the shape the pointwise laws need, so every denotation of an expression whose literals are well shaped is well shaped. `PSet.wf` is a proof-only weakening of `PSet.valid`: the algebra never uses the ascending-offsets condition, which is there for the store |
| `U-01` (part) | the lookup round trip: interning an object id and then looking it up in the table interning returned gives the ordinal it returned, for any universe and any id, with no well-formedness hypothesis. It rests on a trie reading back what was written, which is proved outright. Injectivity -- that two different ids never share an ordinal -- is a property of every write the table ever took and is still open |
| addressing | an ordinal is below a power of two exactly when it fits in that many bits; rebasing into a node's upper half keeps it inside the child; the tile address is injective; a bit index is below a word's width; `U32` addition adds when neither operand is large; the enumeration walk and the tile address name the same positions |

`LAWS.pending.bend` states, in the same syntax, the obligations this release
specifies but has **not** proved. `law-registry.json` records the status of
each of the registry's obligations individually.

### Four laws that were false

Four obligations in `LAWS.pending.bend` were not merely unproved: as first
written they were **false**, and each counterexample now runs on every build
from `tests.bend`. A `PDense` leaf narrower than 128 words loses the bit it
was just given; a leaf difference past ordinal 4096 is not pointwise; a
sparse payload above the leaf level breaks the union law; compression past
4096 is not member-preserving.

Every one of those is a value `PSet.valid` rejects, or an ordinal outside the
leaf it is asked about -- so the statements were missing the structural
invariant the code documents and the store checks on load. They have been
restated with it, and `P-01` was then proved outright. That is the honest
reading of "specified but not proved": a precise open claim is worth having,
and a false one is worth catching.

### What a proved law does not say

A law constrains the algebra. It says nothing about whether the graph the
algebra ran on describes a real repository, whether the compiler lowered the
algebra correctly, or whether the machine executed what the compiler emitted.
Those are §3 below.

---

## 2. Checked at run time

Three obligations are established per query rather than once at build time.
This is a deliberate trade, not a shortfall: a runtime check also catches a
corrupted cache, a different implementation's cached answer, and a bug in the
part of the traversal that no static proof covers.

**The closure certificate (`C-04`).** `pp git verify` runs SPEC 4.4's four
conditions over the traversal's own output: the roots are inside the closure,
the closure is edge-closed, the levels union to exactly the closure, and every
level is one edge from the level before. Conditions 1–2 establish that the
reachable set is inside the answer; the well-founded predecessor chains of
condition 3 establish the converse. **Acceptance therefore establishes
exactness, not an overapproximation** — which is what lets a cached or
independently produced closure be reused without trusting how it was
computed.

The checker does not establish that the imported graph matches a real
repository. That is an adapter contract (§3).

**The witness checker (`E-01`).** `pp git explain` produces a path and then
checks it independently: it must start at a requested root, end at the
requested object, and take a real policy edge at every step. The law is
stated over the *checker*, not the producer, so an optimizer's narrative is
never taken on trust.

**Differential execution.** `tools/differential.sh` checks `pp` against Git's
own reachability engine over the same roots and semantics, and `tests.bend`
checks the production frontier traversal against the specification evaluator
in `spec/closure.bend`, which recomputes `post` over the whole set every
round. SPEC 7.6 is right that this is an additional check and not a
replacement for the distinction between a source-level theorem and a verified
toolchain.

---

## 3. Trusted

Listed because they are load-bearing, not because they are suspect.

**Git decoding and object identity.** `pp` asks `git cat-file` for object
bodies and believes the answer. That the bytes Git returns for an object id
are the bytes that object id names is an external premise. `pp` does not
verify object hashes, and normal mode does not run `git fsck`. Identity
equality here is equality of the complete namespace/format/id key; the finite
set algebra needs no assumption that hash collisions are impossible, but the
premise that those keys name the intended bytes remains outside it
(SPEC 8.4).

**The subprocess and filesystem boundary.** `host/proc.bend` starts `git`
with a literal argv and no shell. Every invocation sets
`--no-replace-objects`, `--no-lazy-fetch`, `--no-optional-locks` and
`--literal-pathspecs`, so replacements do not change what an object id means,
a partial clone does not reach the network during a query, and nothing in the
user's repository is written. The child inherits the environment; a
`GIT_*` variable set by the caller is not scrubbed, and a repository-supplied
`core.hooksPath` is not consulted by any command used here, but neither is
audited.

**`host/run_bytes.c` and `host/run_bytes.js`.** A byte-exact variant of
Base's `Process.run`, vendored from the pinned toolchain with every symbol
renamed and exactly one behavioural change: stdout comes back as bytes rather
than through a UTF-8 decode. It exists because a Git tree entry holds a raw
20- or 32-byte object id, `cat-file --batch` frames records by a declared byte
length, and `io_str` substitutes U+FFFD for invalid sequences — which shifts
every record after the first non-UTF-8 one. Nothing else is changed: literal
argv, no shell, the poll loop that keeps stdin writes from deadlocking
against stdout reads, the timeout and the output cap are the toolchain's.

This is C, it is spliced into the program after the runtime, and the effect
ABI is the runtime's internals with no stability promise. **Rebuild it on
every toolchain bump.** It is the only foreign code in this release.

**The compiler.** Bend's `--safe` mode gives a second checking path through a
kernel with a Lean proof, but the guide is explicit that the translation from
Bend to BendTT is itself unproved, that a foreign def is checked as a model
built from its type rather than as its C or JS code, and that `@unsafe` defs
are out of scope. This release has no `@unsafe` defs. It has one foreign def
(`Host.run_bytes`), which `--safe` checks as a model of its type — that is, it
checks that the *type* is used consistently, not that the C is correct.

Separately, the compiler's lowering is trusted end to end. `U32.and` is
*defined* in Base as a bit-vector operation and the laws are proved against
that definition; that the compiler emits a single machine `&` for it is a
trusted optimization, not a proved refinement.

**The runtime, the OS and the hardware.** Scheduling, the heap, Metal, the
GPU driver and the silicon. A source-level theorem relates the algorithm to
its model. It does not verify any of these.

**The inventory assertion.** Every result carries
`"availability_scope": "recorded-observation-only"`. An inventory is what a
store reported at a moment. It is not a lease, not a pin, and not a promise
that the objects are still there. `K inside H` establishes coverage *under
that evidence*, and SPEC 9.4 reserves the interval type `L ⊆ H ⊆ U` for when
distributed observations arrive.

**The derived graph's correspondence to the repository.** Ref resolution,
graph collection and inventory enumeration are not one atomic filesystem
transaction (SPEC 8.5). `pp` pins the resolved root vector before fetching any
body, and the published graph is immutable afterwards — but a repository that
changes mid-import can still produce `IncompleteGraph`, and a repository that
changes after an import does not invalidate a snapshot that has already been
answered. Prefer a quiescent mirror.

---

## 4. Known limits of this release

* No persistent derived store yet: `pp` imports per invocation. Every result
  reports `"lineage": "ephemeral"` rather than a stored generation.
* Metal is available and reported, but `auto` never dispatches to it: the
  measured crossover does not exist at the sizes this release handles, and
  SPEC 11.4 says to ship a useful native product rather than fabricate a
  speed claim. `--backend metal` fails loudly if the GPU cannot actually run.
* At most 2^32-1 ordinals per universe, and the `Nat` accumulator's ceiling is
  2^48-1 — both documented limits with explicit rejection, not silent
  wraparound (SPEC 5.4).
* SHA-1 and SHA-256 are both supported through an explicit object-format tag;
  the format is read from the repository, never guessed from a length.
