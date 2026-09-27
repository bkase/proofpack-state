# ProofPack State — engineering handoff

Start with **PROOFPACK_SPEC.md**. It is the self-contained product/engineering contract for the first release: a Bend2 finite-set and reachability engine, applied to read-only Git state queries, with native and Metal execution.

## Contents

- `PROOFPACK_SPEC.md` — product scope, denotational semantics, theorem, representations, Git policy, compiler/backend design, trust boundary, CLI, tests, and ordered milestones.
- `law-registry.json` — 32 named proof obligations, dependencies, milestones, and enabling optimizations. Every obligation is explicitly `specified_not_proved`.
- `fixtures.json` — seven symbolic metadata cases covering history versus tree-data, arbitrary inventories, tags, isolated roots, and empty roots. These are not raw Git object fixtures.
- `reference_check.py` — standard-library Python specification oracle. It checks the golden cases, closure certificates, 512 directed graphs on three vertices, and counterexamples to unsafe rewrites. It is not the production engine and is not a formal proof.
- `checks-report.json` — output from the reference checker when this handoff was prepared.

Run the supplied specification checks with Python 3.10 or newer:

```sh
python3 reference_check.py
```

The engineer's first work is M0/T01–T03 in the specification: pin Bend, exercise actual native/Metal execution, and implement/prove the finite-set and flat-kernel contracts. M1 then connects that core to real Git repositories. Do not start with a distributed daemon, agent runner, VM layer, or source-language analyzer.

## Status

This package contains a design, law register, and checked finite examples. It contains **no completed Bend implementation, no discharged Bend proof bundle, and no measured performance claim**. The proposed source baseline was inspected at `bendlang/bend` revision `af569d4826913b2ce3557e9829ccad31fcf86f94`; pin and audit the actual compiler artifact before implementation work.
