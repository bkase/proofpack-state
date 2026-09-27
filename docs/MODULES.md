# Module layout and the one import rule

The tree follows SPEC 10.2 (`core/`, `spec/`, `closure/`, `query/`, `execute/`,
`index/`, `adapters/git/`, `host/`, `cli/`, `proofs/`, `fixtures/`, `bench/`).

**Every `.bend` entry point lives at the repository root.** That is not a
style preference; it is forced by how the pinned toolchain identifies modules.

Bend keys a module by its import path *normalized against the entry file's
directory*. With the entry at the root, `./closure/graph.bend` and the
`../closure/graph.bend` that `spec/closure.bend` writes both normalize to
`closure/graph`, so they are the same module and their types unify. Run the
same check with an entry inside `closure/` and the two spellings normalize to
`graph` and `../closure/graph`, which Bend treats as two different modules —
and a `Graph` from one will not typecheck against a `Graph` from the other:

```
- expected : a defined name
- observed : ../closure/graph.Graph
```

So:

* `LAWS.bend`, `PROOF.bend`, `pp.bend` and every test entry sit at the root.
* A module in a subdirectory imports its neighbours as `./x.bend` and other
  directories as `../dir/x.bend`. Those spellings are correct *as long as the
  entry is the root*, which `tools/check.sh` enforces by never checking a
  subdirectory file directly.
* `tools/check.sh` builds a root-level entry that imports every module, so a
  module that only typechecks in isolation cannot pass.

Two more toolchain rules shaped the code, worth stating once:

* **No mutual recursion.** A def cannot call a def below it, and two defs
  cannot call each other. Where an algorithm wants "compute a comparison, then
  branch and recurse", the comparison is carried as a parameter and recomputed
  by a small def declared above (`Ords.head_cmp`, `Graph.has.un`,
  `PSet.add`'s branch bit).
* **A match inspects parameters in binder order.** `match b` before `match a`
  is rejected when `a` comes first; and a self-call must pass its arguments
  unchanged until one shrinks, so the shrinking list goes *before* the
  accumulator (`PSet.of_list(d, xs, s)`, not `(d, s, xs)`).
