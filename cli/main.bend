# cli/main.bend -- the `pp` commands.
#
#   pp git stats     --repo R --root REF... [--mode full|tree-data]
#   pp git missing   --repo R --root REF... --have-repo H [--output stats|oids]
#   pp git ready     --repo R --root REF... --have-repo H
#   pp git explain   --repo R --root REF... --object OID
#   pp git retention --repo R --root REF... --remove REF...
#   pp git inventory --repo R --against-repo S --root REF...
#   pp git verify    --repo R --root REF...
#
# Exit codes (SPEC 9.3): 0 for a successful complete query including an empty
# set, 1 for a complete negative `ready`, 2 for a rejected or failed query,
# 3 for a resource limit without complete results. The JSON status stays
# authoritative for clients.
#
# This release writes nothing to the repository it reads: every Git call goes
# through adapters/git/git.bend, which sets --no-optional-locks, and no
# command has a write path at all.

import Base
import ../core/count.bend as C
import ../core/set.bend as S
import ../core/trie.bend as T
import ../closure/graph.bend as G
import ../closure/reach.bend as R
import ../closure/explain.bend as E
import ../closure/cert.bend as Ct
import ../index/source.bend as Idx
import ../adapters/git/oid.bend as O
import ../adapters/git/bytes.bend as B
import ../adapters/git/intern.bend as I
import ../adapters/git/import.bend as Im
import ../adapters/git/inventory.bend as Inv
import ../adapters/git/git.bend as Gi
import ../query/ast.bend as A
import ../query/eval.bend as Ev
import ../spec/query.bend as Den
import ../execute/plan.bend as X
import ../host/proc.bend as P
import ../index/store.bend as St
import ./args.bend as Ar
import ./json.bend as J
# ---------------------------------------------------------------------------
# Options.
# ---------------------------------------------------------------------------

# The requested backend, the one that actually ran, and what the plan did.
# SPEC 7.6 requires every result diagnostic to report all of it, and requires
# a forced Metal run to fail when GPU execution cannot actually occur.
type Backend is Data:
  Bk{requested: String, actual: String, dispatches: Nat, leaves: Nat,
    pruned: Nat, words: Nat}

# One value carrying everything every command needs, rather than five
# parameters threaded through five defs. SHADERS.md's advice -- "wrap a big
# header in a constructor of the tree it heads" -- is not only about speed
# here: a chain of defs each taking ten-plus parameters overruns this
# runtime's 247-word limit for a def or continuation, and the compiler
# answers "an arity over 247".
type Ctx is Data:
  Cx{repo: String, src: Idx.Source, policy: Idx.Policy,
    refs: List<&2, String>, backend: Backend}

def Backend.requested(+b: Backend) -> String:
  match b:
    case Bk{requested, actual, dispatches, leaves, pruned, words}:
      requested

def Backend.actual(+b: Backend) -> String:
  match b:
    case Bk{requested, actual, dispatches, leaves, pruned, words}:
      actual

def Backend.dispatches(+b: Backend) -> Nat:
  match b:
    case Bk{requested, actual, dispatches, leaves, pruned, words}:
      dispatches

def Backend.leaves(+b: Backend) -> Nat:
  match b:
    case Bk{requested, actual, dispatches, leaves, pruned, words}:
      leaves

def Backend.pruned(+b: Backend) -> Nat:
  match b:
    case Bk{requested, actual, dispatches, leaves, pruned, words}:
      pruned

def Backend.words(+b: Backend) -> Nat:
  match b:
    case Bk{requested, actual, dispatches, leaves, pruned, words}:
      words

def Ctx.repo(+c: Ctx) -> String:
  match c:
    case Cx{repo, src, policy, refs, backend}:
      repo

def Ctx.src(+c: Ctx) -> Idx.Source:
  match c:
    case Cx{repo, src, policy, refs, backend}:
      src

def Ctx.policy(+c: Ctx) -> Idx.Policy:
  match c:
    case Cx{repo, src, policy, refs, backend}:
      policy

def Ctx.refs(+c: Ctx) -> List<&2, String>:
  match c:
    case Cx{repo, src, policy, refs, backend}:
      refs

def Ctx.backend(+c: Ctx) -> Backend:
  match c:
    case Cx{repo, src, policy, refs, backend}:
      backend

def Cli.policy.pick(td: Bool) -> Idx.Policy:
  match td:
    case True{}:
      Idx.PTreeData{}
    case False{}:
      Idx.PFull{}

def Cli.policy(+m: String) -> Idx.Policy:
  Cli.policy.pick(String.eq(m, "tree-data"))

def Cli.roots_or(rs: List<&2, String>) -> List<&2, String>:
  match rs:
    case Nil{}:
      ["HEAD"]
    case Con{h, t}:
      Con{h, t}

# ---------------------------------------------------------------------------
# The envelope.
# ---------------------------------------------------------------------------

def Cli.roots_of(+ar: Ar.Args) -> List<&2, String>:
  Cli.roots_or(Ar.Args.values(ar, "root"))

def Cli.oids_json(+f: O.Fmt, os: List<&2, O.Oid>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      Con{J.Json.str(O.Oid.show(f, o)), Cli.oids_json(f, t)}

def Cli.ord_oids(+src: Idx.Source, xs: List<&2, U32>) ->
  List<&2, O.Oid>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{Idx.Source.oid_of(src, x), Cli.ord_oids(src, t)}

def Cli.stats_json(s: A.Stats) -> String:
  +st = s
  J.Json.obj([
    J.Json.field("objects", J.Json.num(A.Stats.count(st))),
    J.Json.field("logical_payload_bytes", J.Json.num(A.Stats.bytes(st))),
    J.Json.field("by_type", J.Json.obj([
      J.Json.field("commit", J.Json.num(A.Stats.commits(st))),
      J.Json.field("tree", J.Json.num(A.Stats.trees(st))),
      J.Json.field("blob", J.Json.num(A.Stats.blobs(st))),
      J.Json.field("tag", J.Json.num(A.Stats.tags(st)))]))])

def Cli.env.universe.go(repo: String, +src: Idx.Source) -> String:
  J.Json.obj([
    J.Json.field("namespace", J.Json.str(repo)),
    J.Json.field("lineage", J.Json.str("ephemeral")),
    J.Json.field("generation", J.Json.str("1")),
    J.Json.field("object_format",
      J.Json.str(O.Fmt.name(Idx.Source.fmt(src)))),
    J.Json.field("size", J.Json.num(Idx.Source.n(src)))])

# Built in pieces rather than as one literal: a  def or continuation in this
# runtime takes at most 247 words, and one flat object with every field
# inlined overruns it.
def Cli.env.universe(+cx: Ctx) -> String:
  Cli.env.universe.go(Ctx.repo(cx), Ctx.src(cx))

def Cli.env.snapshot(+src: Idx.Source, refs: List<&2, String>) -> String:
  J.Json.obj([
    J.Json.field("requested_roots", J.Json.arr(J.Json.strings(refs))),
    J.Json.field("resolved_roots", J.Json.arr(
      Cli.oids_json(Idx.Source.fmt(src), Idx.Source.root_oids(src)))),
    J.Json.field("external_references", J.Json.arr(
      Cli.oids_json(Idx.Source.fmt(src), Idx.Source.ext(src))))])

def Cli.env.execution(+b: Backend) -> String:
  J.Json.obj([
    J.Json.field("requested_backend",
      J.Json.str(Backend.requested(b))),
    J.Json.field("actual_backend", J.Json.str(Backend.actual(b))),
    J.Json.field("gpu_dispatches", J.Json.num(Backend.dispatches(b))),
    J.Json.field("leaf_jobs", J.Json.num(Backend.leaves(b))),
    J.Json.field("intervals_pruned", J.Json.num(Backend.pruned(b))),
    J.Json.field("words_read", J.Json.num(Backend.words(b))),
    J.Json.field("bytes_read",
      J.Json.num(Nat.mul(4n, Backend.words(b))))])

def Cli.env.head(+cx: Ctx) -> List<&2, String>:
  [J.Json.field("schema_version", "1"),
    J.Json.field("query_semantics", J.Json.str("proofpack-state/v1")),
    J.Json.field("law_bundle", J.Json.str("proofpack-laws/v0.1")),
    J.Json.field("universe", Cli.env.universe(cx)),
    J.Json.field("graph_snapshot",
      Cli.env.snapshot(Ctx.src(cx), Ctx.refs(cx))),
    J.Json.field("policy", J.Json.str(Idx.Policy.name(Ctx.policy(cx))))]

def Cli.env.tail(inventory: String, completeness: String,
  +backend: Backend, result: String) -> List<&2, String>:
  [J.Json.field("inventory_snapshot", J.Json.str(inventory)),
    J.Json.field("completeness", J.Json.str(completeness)),
    J.Json.field("inventory_assurance",
      J.Json.str("trusted-odb-observation")),
    J.Json.field("availability_scope",
      J.Json.str("recorded-observation-only")),
    J.Json.field("result", result),
    J.Json.field("execution", Cli.env.execution(backend))]

def Cli.envelope(+cx: Ctx, inventory: String, completeness: String,
  result: String) -> String:
  J.Json.obj(List.append(&2, String, Cli.env.head(cx),
    Cli.env.tail(inventory, completeness, Ctx.backend(cx), result)))

def Cli.text_of.pick(+cls: String, +msg: String, has: Bool) -> String:
  match has:
    case False{}:
      msg
    case True{}:
      String.drop(msg, 2n+String.length(cls))

# The message already begins with its class, because the producing module
# writes `"Class: text"` so the code and the human text cannot drift apart.
# Drop that prefix when rendering, so a reader does not see it twice.
def Cli.text_of(+cls: String, +msg: String) -> String:
  Cli.text_of.pick(cls, msg,
    String.starts_with(msg, cls ++ ": "))

def Cli.error(+cls: String, msg: String) -> String:
  J.Json.obj([
    J.Json.field("schema_version", "1"),
    J.Json.field("query_semantics", J.Json.str("proofpack-state/v1")),
    J.Json.field("completeness", J.Json.str("failed")),
    J.Json.field("error", J.Json.obj([
      J.Json.field("class", J.Json.str(cls)),
      J.Json.field("message", J.Json.str(Cli.text_of(cls, msg)))]))])

def Cli.class_of.head(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      "InvalidInput"
    case Con{h, t}:
      h

# The error class is the prefix the producing module put on the message, so
# the machine-readable code and the human text never drift apart.
def Cli.class_of(+msg: String) -> String:
  Cli.class_of.head(String.split(msg, ':'))

def Cli.fail(msg: String) -> IO(Unit):
  +m = msg
  do IO<Unit>:
    IO.print(Cli.error(Cli.class_of(m), m))
    IO.die(Unit, 2, "")

def Cli.limit(msg: String) -> IO(Unit):
  +m = msg
  do IO<Unit>:
    IO.print(Cli.error(Cli.class_of(m), m))
    IO.die(Unit, 3, "")

# ---------------------------------------------------------------------------
# The requirement: the closure of the resolved roots under the chosen policy.
# ---------------------------------------------------------------------------

def Cli.required(+src: Idx.Source, +p: Idx.Policy) -> Ev.Val:
  Ev.Ev.run(src, A.EReach{p, A.ELit{S.PSet.from_list(20n,
    Idx.Source.roots(src))}})

def Cli.reach_of(+src: Idx.Source, +p: Idx.Policy,
  rs: List<&2, U32>) -> Ev.Val:
  Ev.Ev.run(src, A.EReach{p, A.ELit{S.PSet.from_list(20n, rs)}})

# ---------------------------------------------------------------------------
# pp git stats
# ---------------------------------------------------------------------------

def Cmd.stats.go(+cx: Ctx, s: S.PSet, ok: Bool,
  err: String) -> IO(Unit):
  match ok:
    case False{}:
      Cli.limit(err)
    case True{}:
      IO.print(Cli.envelope(cx, "none", "complete",
    J.Json.obj([
          J.Json.field("required", Cli.stats_json(Ev.Ev.stats(Ctx.src(cx), s)))])))

def Cmd.stats.out(+cx: Ctx, +v: Ev.Val) -> IO(Unit):
  Cmd.stats.go(cx, Ev.Val.set(v), Ev.Val.ok(v),
    Ev.Val.err(v))

def Cmd.stats(+cx: Ctx) -> IO(Unit):
  Cmd.stats.out(cx, Cli.required(Ctx.src(cx), Ctx.policy(cx)))

# ---------------------------------------------------------------------------
# pp git missing / pp git ready
#
# The least additional object set (SPEC 3.4): M = K \ H, where K is the
# closure of the roots and H is whatever the receiver reported. H is not
# assumed graph-closed -- that is the point, and why this works on a partial
# cache.
# ---------------------------------------------------------------------------

def Cmd.missing.oids(+src: Idx.Source, k: S.PSet, h: S.PSet) ->
  List<&2, String>:
  Cli.oids_json(Idx.Source.fmt(src),
    Cli.ord_oids(src, S.PSet.missing(20n, k, h)))

def Cmd.missing.list(+src: Idx.Source, k: S.PSet, h: S.PSet,
  want: Bool) -> String:
  match want:
    case False{}:
      "null"
    case True{}:
      J.Json.arr(Cmd.missing.oids(src, k, h))

# Built in three pieces for the reason `Cli.envelope` is: a def or
# continuation in this runtime takes at most 247 words, and one flat object
# with every field inlined overruns it.
def Cmd.missing.body.inv(inv: Inv.Inventory) -> String:
  +iv = inv
  J.Json.obj([
    J.Json.field("in_scope", J.Json.num(Inv.Inventory.in_scope(iv))),
    J.Json.field("out_of_scope",
      J.Json.num(Inv.Inventory.out_of_scope(iv))),
    J.Json.field("observed_total", J.Json.num(Inv.Inventory.total(iv)))])

def Cmd.missing.body.sets(+src: Idx.Source, k: S.PSet,
  h: S.PSet) -> List<&2, String>:
  +kk = k
  +hh = h
  [J.Json.field("ready_at_observation", J.Json.bool(Ev.Ev.ready(kk, hh))),
    J.Json.field("required", Cli.stats_json(Ev.Ev.stats(src, kk))),
    J.Json.field("missing",
      Cli.stats_json(Ev.Ev.missing_stats(src, kk, hh)))]

def Cmd.missing.body.rest(+src: Idx.Source, k: S.PSet,
  h: S.PSet, want_oids: Bool, inv: Inv.Inventory) ->
  List<&2, String>:
  [J.Json.field("inventory", Cmd.missing.body.inv(inv)),
    J.Json.field("missing_objects", Cmd.missing.list(src, k, h, want_oids))]

def Cmd.missing.body(+src: Idx.Source, +k: S.PSet, +h: S.PSet,
  want_oids: Bool, inv: Inv.Inventory) -> String:
  J.Json.obj(List.append(&2, String, Cmd.missing.body.sets(src, k, h),
    Cmd.missing.body.rest(src, k, h, want_oids, inv)))

def Cmd.missing.ready_exit(ready: Bool) -> IO(Unit):
  match ready:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "")

def Cmd.missing.gate(ready: Bool, gated: Bool) -> IO(Unit):
  match gated:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      Cmd.missing.ready_exit(ready)

def Cmd.missing.agreed(disagreed: Bool, ready: Bool, gated: Bool) ->
  IO(Unit):
  match disagreed:
    case True{}:
      IO.die(Unit, 2, "")
    case False{}:
      Cmd.missing.gate(ready, gated)

def Cmd.kind_name.pick(n: Nat) -> String:
  match n:
    case 0n:
      "commit"
    case 1n+a:
      match a:
        case 0n:
          "tree"
        case 1n+b:
          match b:
            case 0n:
              "blob"
            case 1n+c:
              match c:
                case 0n:
                  "tag"
                case 1n+d:
                  "unknown"

def Cmd.kind_name(+k: U32) -> String:
  Cmd.kind_name.pick(U32.to_nat(k))

def Cmd.explain.step(+src: Idx.Source, x: U32) -> String:
  +xx = x
  J.Json.obj([
    J.Json.field("oid",
      J.Json.str(O.Oid.show(Idx.Source.fmt(src),
        Idx.Source.oid_of(src, xx)))),
    J.Json.field("type", J.Json.str(Cmd.kind_name(
      Im.Meta.kind(Idx.Source.meta_of(src, xx)))))])

def Cmd.explain.path_json(+src: Idx.Source, xs: List<&2, U32>) ->
  List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{Cmd.explain.step(src, x), Cmd.explain.path_json(src, t)}

def Cmd.explain.exit(valid: Bool) -> IO(Unit):
  match valid:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 2, "")

def Cmd.explain.emit(+cx: Ctx, target: O.Oid,
  path: List<&2, U32>, +valid: Bool) -> IO(Unit):
  +pp = path
  do IO<Unit>:
    IO.print(Cli.envelope(cx, "none", "complete",
    J.Json.obj([
        J.Json.field("object",
          J.Json.str(O.Oid.show(Idx.Source.fmt(Ctx.src(cx)), target))),
        J.Json.field("reachable",
          J.Json.bool(Bool.not(List.is_empty(&2, U32, pp)))),
        J.Json.field("witness_checked", J.Json.bool(valid)),
        J.Json.field("path",
          J.Json.arr(Cmd.explain.path_json(Ctx.src(cx), pp)))])))
    Cmd.explain.exit(valid)

def Cmd.explain.found(+cx: Ctx, target: O.Oid, +x: U32) ->
  IO(Unit):
  +out = R.Reach.closure(Idx.Source.n(Ctx.src(cx)), 32n,
    Idx.Source.graph(Ctx.src(cx), Ctx.policy(cx)), 20n, Idx.Source.roots(Ctx.src(cx)))
  +path = E.Explain.path(32n, Idx.Source.graph(Ctx.src(cx), Ctx.policy(cx)),
    R.Reach.levels(20n, out), x)
  Cmd.explain.emit(cx, target, path,
    E.Explain.valid(32n, Idx.Source.graph(Ctx.src(cx), Ctx.policy(cx)), Idx.Source.roots(Ctx.src(cx)),
      path, x))

def Cmd.explain.lookup(+cx: Ctx, target: O.Oid,
  m: Maybe<&2, U32>) -> IO(Unit):
  match m:
    case None{}:
      Cli.fail("UnknownRoot: the object is not in this graph snapshot")
    case Some{x}:
      Cmd.explain.found(cx, target, x)

def Cmd.explain.read(+cx: Ctx, r: O.OidRead) -> IO(Unit):
  match r:
    case O.Read{oid, ok}:
      match ok:
        case False{}:
          Cli.fail("InvalidInput: --object is not a complete object id")
        case True{}:
          +o = oid
          Cmd.explain.lookup(cx, o,
            I.Uni.find(I.Uni.table(Idx.Source.uni(Ctx.src(cx))), o))

def Cmd.explain(+cx: Ctx, obj: String) -> IO(Unit):
  Cmd.explain.read(cx, O.Oid.of_hex(Idx.Source.fmt(Ctx.src(cx)), B.Bytes.of_string(obj)))

# ---------------------------------------------------------------------------
# pp git verify -- run the closure certificate of SPEC 4.4 over this query's
# own traversal. Acceptance establishes exactness, not an overapproximation.
# ---------------------------------------------------------------------------

def Cmd.verify.emit(+cx: Ctx, +accepted: Bool, rounds: Nat,
  size: Nat) -> IO(Unit):
  do IO<Unit>:
    IO.print(Cli.envelope(cx, "none", "complete",
    J.Json.obj([
        J.Json.field("certificate_accepted", J.Json.bool(accepted)),
        J.Json.field("closure_size", J.Json.num(size)),
        J.Json.field("traversal_rounds", J.Json.num(rounds)),
        J.Json.field("conditions", J.Json.arr(J.Json.strings([
          "roots are inside the closure",
          "the closure is edge-closed",
          "the levels union to exactly the closure",
          "every level is one edge from the level before"])))])))
    Cmd.explain.exit(accepted)

def Cmd.verify(+cx: Ctx) -> IO(Unit):
  +out = R.Reach.closure(Idx.Source.n(Ctx.src(cx)), 32n,
    Idx.Source.graph(Ctx.src(cx), Ctx.policy(cx)), 20n, Idx.Source.roots(Ctx.src(cx)))
  +seen = R.Reach.seen(20n, out)
  Cmd.verify.emit(cx, Ct.Cert.check(32n, Idx.Source.graph(Ctx.src(cx), Ctx.policy(cx)), 20n,
      Idx.Source.roots(Ctx.src(cx)), R.Reach.levels(20n, out), seen),
    R.Reach.rounds(20n, out), S.PSet.size(20n, seen))

# ---------------------------------------------------------------------------
# pp git retention
#
# What is retained only by these roots: the reachability difference against
# an explicitly scoped retained-root set. SPEC 13 is emphatic that this is a
# *preview*, not a GC root set: Ctx.refs(cx) alone omit reflogs, detached worktrees,
# indexes and grace periods, and physical pack deletion also depends on
# surviving representations and delta bases. The envelope says so, and this
# command has no deletion path.
# ---------------------------------------------------------------------------

def Cmd.retention.list(+src: Idx.Source, s: S.PSet, want: Bool) ->
  String:
  match want:
    case False{}:
      "null"
    case True{}:
      J.Json.arr(Cli.oids_json(Idx.Source.fmt(src),
        Cli.ord_oids(src, S.PSet.to_list(20n, s))))

def Cmd.retention.caveat() -> String:
  J.Json.str("A scoped preview, not the Git GC root set: reflogs, detached "
    ++ "worktrees, indexes and grace periods are not included, and pack "
    ++ "representation and delta bases are not modelled. Do not turn this "
    ++ "into a deletion command.")

def Cmd.retention.body(+src: Idx.Source, refs: List<&2, String>,
  removed: List<&2, String>, +only: S.PSet, want_oids: Bool) ->
  List<&2, String>:
  List.append(&2, String,
    [J.Json.field("retained_roots", J.Json.arr(J.Json.strings(refs))),
      J.Json.field("removed_roots", J.Json.arr(J.Json.strings(removed)))],
    [J.Json.field("retained_only_by_removed",
        Cli.stats_json(Ev.Ev.stats(src, only))),
      J.Json.field("objects", Cmd.retention.list(src, only, want_oids)),
      J.Json.field("caveat", Cmd.retention.caveat())])

def Cmd.retention.emit(+cx: Ctx, +removed: List<&2, String>,
  only: S.PSet, want_oids: Bool) -> IO(Unit):
  IO.print(Cli.envelope(cx, "none", "complete",
    J.Json.obj(Cmd.retention.body(Ctx.src(cx), Ctx.refs(cx), removed, only, want_oids))))

def Cmd.retention.checked(+cx: Ctx, removed: List<&2, String>,
  only: S.PSet, ok: Bool, err: String, want_oids: Bool) -> IO(Unit):
  match ok:
    case False{}:
      Cli.limit(err)
    case True{}:
      Cmd.retention.emit(cx, removed, only,
        want_oids)

def Cmd.retention.both(+cx: Ctx, removed: List<&2, String>,
  keep: Ev.Val, gone: Ev.Val, want_oids: Bool) -> IO(Unit):
  +k = keep
  +g = gone
  Cmd.retention.checked(cx, removed,
    S.PSet.diff(20n, Ev.Val.set(g), Ev.Val.set(k)),
    Bool.and(Ev.Val.ok(k), Ev.Val.ok(g)), Ev.Val.err(g), want_oids)

# The retained and removed roots were resolved in one import, so both are
# ordinals in the same universe. `keep_n` is how many of the resolved root
# vector are retained roots; the rest are the removed ones.
def Cmd.retention(+cx: Ctx, removed: List<&2, String>,
  +keep_n: Nat, want_oids: Bool) -> IO(Unit):
  +rs = Idx.Source.roots(Ctx.src(cx))
  Cmd.retention.both(cx, removed,
    Cli.reach_of(Ctx.src(cx), Ctx.policy(cx), List.take(&2, U32, rs, keep_n)),
    Cli.reach_of(Ctx.src(cx), Ctx.policy(cx), rs), want_oids)

# ---------------------------------------------------------------------------
# pp git inventory -- an observation, reported as one (SPEC 9.4).
# ---------------------------------------------------------------------------

def Cmd.inventory.emit(+cx: Ctx, have: String,
  inv: Inv.Inventory) -> IO(Unit):
  +iv = inv
  IO.print(Cli.envelope(cx, have, "complete",
    J.Json.obj(List.append(&2, String,
      [J.Json.field("observed", Cmd.missing.body.inv(iv))],
      [J.Json.field("in_scope_stats",
        Cli.stats_json(Ev.Ev.stats(Ctx.src(cx), Inv.Inventory.present(iv))))]))))

def Cmd.inventory.got(+cx: Ctx, have: String,
  ir: Inv.InvResult) -> IO(Unit):
  match ir:
    case Inv.IErr{msg}:
      Cli.fail(msg)
    case Inv.IOk{inv}:
      Cmd.inventory.emit(cx, have, inv)

def Cmd.inventory(+cx: Ctx, have: String) -> IO(Unit):
  +h = have
  do IO<Unit>:
    ir : Inv.InvResult <- Inv.Inv.observe(h, Idx.Source.uni(Ctx.src(cx)),
      Idx.Source.fmt(Ctx.src(cx)))
    Cmd.inventory.got(cx, h, ir)

# ---------------------------------------------------------------------------
# Dispatch.
# ---------------------------------------------------------------------------

def Cli.actual.pick(forced: Bool, gpu: Bool) -> String:
  match forced:
    case False{}:
      "cpu"
    case True{}:
      match gpu:
        case True{}:
          "metal"
        case False{}:
          "unavailable"

# The actual backend: Metal only when the runtime says a `!` call really
# reaches the GPU in this process, which `Host.gpu_enabled` reads from the
# runtime itself. `auto` stays on the CPU: SPEC 11.4 says to ship a useful
# native product and call Metal experimental until a measured regime exists,
# rather than dispatch a GPU to demonstrate that it exists.
def Cli.actual(requested: String, gpu: Bool) -> String:
  Cli.actual.pick(String.eq(requested, "metal"), gpu)

def Cli.backend_of(+requested: String, gpu: Bool) -> Backend:
  Bk{requested, Cli.actual(requested, gpu), 0n, 0n, 0n, 0n}

def Cli.backend_ok(+b: Backend) -> Bool:
  Bool.not(String.eq(Backend.actual(b), "unavailable"))

def Cli.execute.pick(metal: Bool, j: X.Job) -> Nat:
  match metal:
    case True{}:
      X.Exec.count_gpu(Idx.Idx.sd(), j)
    case False{}:
      X.Exec.count(Idx.Idx.sd(), j)

def Cli.execute.run(+b: Backend, j: X.Job) -> Nat:
  Cli.execute.pick(String.eq(Backend.actual(b), "metal"), j)

def Cli.execute.dispatches(metal: Bool) -> Nat:
  match metal:
    case True{}:
      1n
    case False{}:
      0n

def Cli.execute.check(+b: Backend, leaves: Nat, pruned: Nat, words: Nat,
  agree: Bool) -> Backend:
  match agree:
    case True{}:
      Bk{Backend.requested(b), Backend.actual(b),
        Cli.execute.dispatches(String.eq(Backend.actual(b), "metal")),
        leaves, pruned, words}
    case False{}:
      Bk{Backend.requested(b), "disagreed", 0n, leaves, pruned, words}

def Cli.execute.go(+b: Backend, leaves: Nat, pruned: Nat, words: Nat,
  got: Nat, tree: Nat) -> Backend:
  Cli.execute.check(b, leaves, pruned, words, Nat.is_eq(got, tree))

# Run the leaf-job plan on the chosen backend, and cross-check it against the
# tree reduction. SPEC 11.1's second independent comparison is native against
# Metal over identical validated plans; this runs it on every query rather
# than only in a benchmark, and a disagreement is an error, not a warning.
def Cli.execute(+b: Backend, k: S.PSet, h: S.PSet, tree: Nat) -> Backend:
  +j = X.Plan.of(Idx.Idx.sd(), k, h)
  Cli.execute.go(b, X.Plan.leaves(j, 0n), X.Plan.pruned(j, 0n),
    X.Plan.words(j, 0n), Cli.execute.run(b, j), tree)

def Cmd.missing.emit(+cx: Ctx, have: String, k: S.PSet,
  inv: Inv.Inventory, want_oids: Bool, ready_gate: Bool) -> IO(Unit):
  +kk = k
  +iv = inv
  +hh = Inv.Inventory.present(iv)
  # The leaf-job plan runs on the chosen backend and its count is checked
  # against the tree reduction. A disagreement between the two is reported as
  # `actual_backend: "disagreed"` and exits 2 -- never as an answer.
  +bk = Cli.execute(Ctx.backend(cx), kk, hh, Ev.Ev.missing_count(kk, hh))
  do IO<Unit>:
    IO.print(Cli.envelope(Cx{Ctx.repo(cx), Ctx.src(cx), Ctx.policy(cx),
      Ctx.refs(cx), bk}, have, "complete",
      Cmd.missing.body(Ctx.src(cx), kk, hh, want_oids, iv)))
    Cmd.missing.agreed(String.eq(Backend.actual(bk), "disagreed"),
      Ev.Ev.ready(kk, hh), ready_gate)

def Cmd.missing.checked(+cx: Ctx, have: String,
  inv: Inv.Inventory, k: S.PSet, ok: Bool, err: String,
  want_oids: Bool, ready_gate: Bool) -> IO(Unit):
  match ok:
    case False{}:
      Cli.limit(err)
    case True{}:
      Cmd.missing.emit(cx, have, k, inv,
        want_oids, ready_gate)

def Cmd.missing.have(+cx: Ctx, have: String, +v: Ev.Val,
  ir: Inv.InvResult, want_oids: Bool, ready_gate: Bool) -> IO(Unit):
  match ir:
    case Inv.IErr{msg}:
      Cli.fail(msg)
    case Inv.IOk{inv}:
      Cmd.missing.checked(cx, have, inv,
        Ev.Val.set(v), Ev.Val.ok(v), Ev.Val.err(v), want_oids, ready_gate)

def Cmd.missing(+cx: Ctx, have: String, want_oids: Bool,
  ready_gate: Bool) -> IO(Unit):
  +h = have
  do IO<Unit>:
    ir : Inv.InvResult <- Inv.Inv.observe(h, Idx.Source.uni(Ctx.src(cx)),
      Idx.Source.fmt(Ctx.src(cx)))
    Cmd.missing.have(cx, h, Cli.required(Ctx.src(cx), Ctx.policy(cx)),
      ir, want_oids, ready_gate)

# ---------------------------------------------------------------------------
# pp git explain
#
# Law E-01: the returned path begins at a requested root, ends at the
# requested object, and every step is a real policy edge. The path is
# produced from the traversal's BFS levels and then *checked* independently
# by `Explain.valid`, so the answer does not rest on trusting the producer.
# ---------------------------------------------------------------------------

def Cli.store.xdg(home: String, +xdg: String, empty: Bool) -> String:
  match empty:
    case True{}:
      home ++ "/.cache/proofpack"
    case False{}:
      xdg ++ "/proofpack"

# ---------------------------------------------------------------------------
# Where the derived store lives. SPEC 9.1: a user-owned derived-cache
# directory, and never a change to repository configuration. On macOS that is
# ~/Library/Caches/ProofPack; elsewhere $XDG_CACHE_HOME/proofpack, falling
# back to ~/.cache/proofpack. `--store PATH` overrides all of it.
def Cli.store.of(home: String, +xdg: String, mac: Bool) -> String:
  match mac:
    case True{}:
      home ++ "/Library/Caches/ProofPack"
    case False{}:
      Cli.store.xdg(home, xdg, String.is_empty(xdg))

def Cli.store.given(+ar: Ar.Args, dflt: String) -> String:
  Ar.Args.one(ar, "store", dflt)

def Cli.env.or(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Fail{e}:
      ""
    case Done{v}:
      v

def Cli.store.mac.go(v: U32 & (P.Bytes & String)) -> Bool:
  match v:
    case Tuple{st, rest}:
      U32.is_zero(st)

def Cli.store.mac(r: Result<&1, &1, U32 & String,
  U32 & (P.Bytes & String)>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{v}:
      Cli.store.mac.go(v)

def Cli.store.dir(+ar: Ar.Args) -> IO(String):
  do IO<String>:
    h : Result<&1, &1, U32 & String, String> <- IO.get_env("HOME")
    x : Result<&1, &1, U32 & String, String> <-
      IO.get_env("XDG_CACHE_HOME")
    +home : String = Cli.env.or(h)
    lib : Result<&1, &1, U32 & String, U32 & (P.Bytes & String)> <-
      P.Host.run_bytes("test", ["-d", home ++ "/Library"], "", 1024, 5000)
    return Cli.store.given(ar,
      Cli.store.of(home, Cli.env.or(x), Cli.store.mac(lib)))

# ---------------------------------------------------------------------------
# pp git import -- the "once" of SPEC 1.1.
# ---------------------------------------------------------------------------

def Cmd.import.emit(+cx: Ctx, store: String, name: String, ok: Bool) ->
  IO(Unit):
  match ok:
    case False{}:
      Cli.fail("CorruptIndex: the generation could not be written to "
        ++ store)
    case True{}:
      IO.print(Cli.envelope(cx, "none", "complete", J.Json.obj([
        J.Json.field("stored_as", J.Json.str(name)),
        J.Json.field("store", J.Json.str(store)),
        J.Json.field("imported", Cli.stats_json(
          Ev.Ev.stats(Ctx.src(cx), Den.Den.universe(
            Idx.Source.n(Ctx.src(cx))))))])))

def Cmd.import(+cx: Ctx, store: String, name: String) -> IO(Unit):
  +st = store
  +nm = name
  +src = Ctx.src(cx)
  do IO<Unit>:
    ok : Bool <- St.Store.publish(st, nm,
      St.Store.encode(src, Idx.Source.metas(src), Idx.Source.rows(src)))
    Cmd.import.emit(cx, st, nm, ok)

def Cli.usage() -> String:
  "pp -- ProofPack State\n"
    ++ "\n"
    ++ "  pp git stats     --repo R [--root REF]... [--mode full|tree-data]\n"
    ++ "  pp git missing   --repo R [--root REF]... --have-repo H\n"
    ++ "                   [--output stats|oids]\n"
    ++ "  pp git ready     --repo R [--root REF]... --have-repo H\n"
    ++ "  pp git explain   --repo R [--root REF]... --object OID\n"
    ++ "  pp git retention --repo R [--root REF]... --remove REF...\n"
    ++ "  pp git inventory --repo R [--root REF]... --have-repo H\n"
    ++ "  pp git verify    --repo R [--root REF]...\n"
    ++ "  pp git import    --repo R [--root REF]... --as NAME\n"
    ++ "\n"
    ++ "Every query takes --repo R (import now) or --graph NAME (a stored\n"
    ++ "snapshot). --store PATH overrides the derived-cache directory.\n"
    ++ "\n"
    ++ "Global: --mode full|tree-data  --backend auto|cpu|metal\n"
    ++ "\n"
    ++ "--backend metal fails if this process has no GPU rather than\n"
    ++ "falling back; auto stays on the CPU, because no measured regime\n"
    ++ "yet exists where Metal beats the native path after dispatch.\n"
    ++ "\n"
    ++ "Every command is read-only. Exit 0 complete, 1 not ready,\n"
    ++ "2 rejected, 3 resource limit."

# The index of `cmd` in the command list, or the list length for an unknown
# one. The head comparison is carried as a parameter and recomputed by
# `Cli.head_eq`, because Bend forbids the mutual recursion the obvious
# `go`/`step` pair would need.
def Cli.head_eq(ns: List<&2, String>, +cmd: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{h, t}:
      String.eq(h, cmd)

def Cli.which.go(+cmd: String, names: List<&2, String>, i: Nat,
  hit: Bool) -> Nat:
  match names:
    case Nil{}:
      i
    case Con{h, t}:
      match hit:
        case True{}:
          i
        case False{}:
          +t2 = t
          Cli.which.go(cmd, t2, 1n+i, Cli.head_eq(t2, cmd))

def Cli.which(+cmd: String) -> Nat:
  +ns = {["stats", "missing", "ready", "explain", "retention",
    "inventory", "verify", "import"] : List<&2, String>}
  Cli.which.go(cmd, ns, 0n, Cli.head_eq(ns, cmd))

def Cli.go.pick(+ar: Ar.Args, +cx: Ctx, +keep_n: Nat, k: Nat) ->
  IO(Unit):
  match k:
    case 0n:
      Cmd.stats(cx)
    case 1n+a:
      match a:
        case 0n:
          Cmd.missing(cx, Ar.Args.one(ar, "have-repo", ""),
            String.eq(Ar.Args.one(ar, "output", "stats"), "oids"),
            False{})
        case 1n+b:
          match b:
            case 0n:
              Cmd.missing(cx, Ar.Args.one(ar, "have-repo", ""), False{}, True{})
            case 1n+c:
              match c:
                case 0n:
                  Cmd.explain(cx, Ar.Args.one(ar, "object", ""))
                case 1n+d:
                  match d:
                    case 0n:
                      Cmd.retention(cx, Ar.Args.values(ar, "remove"), keep_n,
                        String.eq(Ar.Args.one(ar, "output", "stats"),
                          "oids"))
                    case 1n+e:
                      match e:
                        case 0n:
                          Cmd.inventory(cx, Ar.Args.one(ar, "have-repo", ""))
                        case 1n+f:
                          match f:
                            case 0n:
                              Cmd.verify(cx)
                            case 1n+g:
                              match g:
                                case 0n:
                                  Cmd.import(cx,
                                    Ar.Args.one(ar, "store-dir", ""),
                                    Ar.Args.one(ar, "as", "source"))
                                case 1n+h:
                                  Cli.fail(
                                    "InvalidInput: unknown command")

def Cli.go(+ar: Ar.Args, +cmd: String, +cx: Ctx, +keep_n: Nat) ->
  IO(Unit):
  Cli.go.pick(ar, cx, keep_n, Cli.which(cmd))

def Cli.dispatch(+ar: Ar.Args, +cmd: String, repo: String,
  +p: Idx.Policy, refs: List<&2, String>, backend: Backend, +keep_n: Nat,
  b: Idx.Built) -> IO(Unit):
  match b:
    case Idx.BErr{msg}:
      Cli.fail(msg)
    case Idx.BOk{src}:
      Cli.go(ar, cmd, Cx{repo, src, p, refs, backend}, keep_n)

def Args.of_dir(ar: Ar.Args, dir: String) -> Ar.Args:
  Con{Ar.Flag{"store-dir", dir}, ar}

def Cli.source.pick(+repo: String, all: List<&2, String>, +store: String,
  graph: String, fresh: Bool) -> IO(Idx.Built):
  match fresh:
    case True{}:
      Idx.Idx.import(repo, all)
    case False{}:
      St.Store.load(store, graph)

# A query names either a stored graph snapshot (`--graph NAME`, resolved
# against the derived store) or a repository to import now (`--repo PATH`).
# SPEC 9.1: a stored ref alias resolves within the named snapshot, and
# updating the live Git ref does not mutate it -- observing new roots takes
# an explicit import.
def Cli.source(+ar: Ar.Args, +repo: String, all: List<&2, String>,
  +store: String, +graph: String) -> IO(Idx.Built):
  Cli.source.pick(repo, all, store, graph, String.is_empty(graph))

def Cli.run.checked(+ar: Ar.Args, +cmd: String, +repo: String,
  +p: Idx.Policy, +refs: List<&2, String>, +bk: Backend,
  removed: List<&2, String>, all: List<&2, String>, ok: Bool) ->
  IO(Unit):
  match ok:
    case False{}:
      Cli.fail("BackendUnavailable: --backend metal was requested, but "
        ++ "this process has no GPU: either the binary was built without a "
        ++ "`!` call, no device was found, or --gpu off was passed")
    case True{}:
      do IO<Unit>:
        dir : String <- Cli.store.dir(ar)
        +sd : String = dir
        b : Idx.Built <- Cli.source(ar, repo, all, sd,
          Ar.Args.one(ar, "graph", ""))
        Cli.dispatch(Args.of_dir(ar, sd), cmd, repo, p, refs, bk,
          List.length(&2, String, refs), b)

def Cli.run(+ar: Ar.Args, +cmd: String, repo: String, +p: Idx.Policy,
  +refs: List<&2, String>, requested: String,
  removed: List<&2, String>) -> IO(Unit):
  +rp = repo
  +rm = removed
  do IO<Unit>:
    gpu : Bool <- P.Host.gpu_enabled()
    +bk : Backend = Cli.backend_of(requested, gpu)
    Cli.run.checked(ar, cmd, rp, p, refs, bk, rm,
      List.append(&2, String, refs, rm), Cli.backend_ok(bk))

def Cli.top.pick(+ar: Ar.Args, +cmd: String, ok: Bool) -> IO(Unit):
  match ok:
    case False{}:
      IO.print(Cli.usage())
    case True{}:
      Cli.run(ar, cmd, Ar.Args.one(ar, "repo", "."),
        Cli.policy(Ar.Args.one(ar, "mode", "full")),
        Cli.roots_of(ar), Ar.Args.one(ar, "backend", "auto"),
        Ar.Args.values(ar, "remove"))

def Cli.top(+ar: Ar.Args, area: String, +cmd: String) -> IO(Unit):
  Cli.top.pick(ar, cmd, Bool.and(String.eq(area, "git"),
    Bool.not(String.is_empty(cmd))))

def Cli.entry(xs: List<&1, String>) -> IO(Unit):
  +ar = Ar.Args.of(xs)
  Cli.top(ar, Ar.Args.word(ar, 0n), Ar.Args.word(ar, 1n))
