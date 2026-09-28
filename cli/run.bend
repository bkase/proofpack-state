# cli/run.bend -- the command line, where the effects are.
#
# cli/main.bend holds everything the CLI decides: the answer envelope, the
# JSON rendering, the backend accounting, the matrix dedup, and the command
# bodies that take their inputs as arguments. LAWS.bend states laws about
# several of those. This module holds the parts that read a repository,
# resolve the derived store, publish a generation, and dispatch argv --
# every place where a command actually reaches the outside.
#
# Keeping them apart is what lets `bend PROOF.bend --verdict` report no
# reliance on unsafe or foreign code: a module reaches that code by
# importing it, so the module the laws import must not.

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
import ./main.bend as Cm
import ../adapters/git/gitout.bend as Go
import ../adapters/git/observe.bend as Ob
import ../index/ingest.bend as Ig
import ../index/publish.bend as Pb
import ./json.bend as J
def Cmd.inventory(+cx: Cm.Ctx, have: String) -> IO(Unit):
  +h = have
  do IO<Unit>:
    ir : Inv.InvResult <- Ob.Inv.observe(h, Idx.Source.uni(Cm.Ctx.src(cx)),
      Idx.Source.fmt(Cm.Ctx.src(cx)))
    Cm.Cmd.inventory.got(cx, h, ir)

def Cmd.missing(+cx: Cm.Ctx, have: String, want_oids: Bool,
  ready_gate: Bool) -> IO(Unit):
  +h = have
  do IO<Unit>:
    ir : Inv.InvResult <- Ob.Inv.observe(h, Idx.Source.uni(Cm.Ctx.src(cx)),
      Idx.Source.fmt(Cm.Ctx.src(cx)))
    Cm.Cmd.missing.have(cx, h, Cm.Cli.required(Cm.Ctx.src(cx), Cm.Ctx.policy(cx)),
      ir, want_oids, ready_gate)

def Cli.store.dir(+ar: Ar.Args) -> IO(String):
  do IO<String>:
    h : Result<&1, &1, U32 & String, String> <- IO.get_env("HOME")
    x : Result<&1, &1, U32 & String, String> <-
      IO.get_env("XDG_CACHE_HOME")
    +home : String = Cm.Cli.env.or(h)
    lib : Result<&1, &1, U32 & String, U32 & (P.Bytes & String)> <-
      P.Host.run_bytes("test", ["-d", home ++ "/Library"], "", 1024, 5000)
    return Cm.Cli.store.given(ar,
      Cm.Cli.store.of(home, Cm.Cli.env.or(x), Cm.Cli.store.mac(lib)))

def Cmd.import(+cx: Cm.Ctx, store: String, name: String) -> IO(Unit):
  +st = store
  +nm = name
  +src = Cm.Ctx.src(cx)
  do IO<Unit>:
    ok : Bool <- Pb.Store.publish(st, nm,
      St.Store.encode(src, Idx.Source.metas(src), Idx.Source.rows(src)))
    Cm.Cmd.import.emit(cx, st, nm, ok)

def Cmd.matrix.scan(+cx: Cm.Ctx, haves: List<&2, String>,
  cells: List<&2, Cm.Cell>) -> IO(List<&2, Cm.Cell>):
  match haves:
    case Nil{}:
      IO.pure(List<&2, Cm.Cell>, cells)
    case Con{h, t}:
      +hh = h
      do IO<List<&2, Cm.Cell>>:
        r : Inv.InvResult <- Ob.Inv.observe(hh,
          Idx.Source.uni(Cm.Ctx.src(cx)), Idx.Source.fmt(Cm.Ctx.src(cx)))
        Cmd.matrix.scan(cx, t, Cm.Cmd.matrix.add(cells, hh, r))

def Cmd.matrix(+cx: Cm.Ctx, haves: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    cells : List<&2, Cm.Cell> <- Cmd.matrix.scan(cx, haves, Nil{})
    Cm.Cmd.matrix.emit(cx, Cm.Cli.required(Cm.Ctx.src(cx), Cm.Ctx.policy(cx)), cells)

def Cli.go.pick(+ar: Ar.Args, +cx: Cm.Ctx, +keep_n: Nat, k: Nat) ->
  IO(Unit):
  match k:
    case 0n:
      Cm.Cmd.stats(cx)
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
                  Cm.Cmd.explain(cx, Ar.Args.one(ar, "object", ""))
                case 1n+d:
                  match d:
                    case 0n:
                      Cm.Cmd.retention(cx, Ar.Args.values(ar, "remove"), keep_n,
                        String.eq(Ar.Args.one(ar, "output", "stats"),
                          "oids"))
                    case 1n+e:
                      match e:
                        case 0n:
                          Cmd.inventory(cx, Ar.Args.one(ar, "have-repo", ""))
                        case 1n+f:
                          match f:
                            case 0n:
                              Cm.Cmd.verify(cx)
                            case 1n+g:
                              match g:
                                case 0n:
                                  Cmd.import(cx,
                                    Ar.Args.one(ar, "store-dir", ""),
                                    Ar.Args.one(ar, "as", "source"))
                                case 1n+h:
                                  match h:
                                    case 0n:
                                      Cmd.matrix(cx,
                                        Ar.Args.values(ar, "have-repo"))
                                    case 1n+j:
                                      Cm.Cli.fail(
                                        "InvalidInput: unknown command")

def Cli.go(+ar: Ar.Args, +cmd: String, +cx: Cm.Ctx, +keep_n: Nat) ->
  IO(Unit):
  Cli.go.pick(ar, cx, keep_n, Cm.Cli.which(cmd))

def Cli.dispatch(+ar: Ar.Args, +cmd: String, repo: String,
  +p: Idx.Policy, refs: List<&2, String>, backend: Cm.Backend, +keep_n: Nat,
  b: Idx.Built) -> IO(Unit):
  match b:
    case Idx.BErr{msg}:
      Cm.Cli.fail(msg)
    case Idx.BOk{src}:
      Cli.go(ar, cmd, Cm.Cx{repo, src, p, refs, backend}, keep_n)

def Args.of_dir(ar: Ar.Args, dir: String) -> Ar.Args:
  Con{Ar.Flag{"store-dir", dir}, ar}

def Cli.source.pick(+repo: String, all: List<&2, String>, +store: String,
  graph: String, fresh: Bool) -> IO(Idx.Built):
  match fresh:
    case True{}:
      Ig.Idx.import(repo, all)
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
  +p: Idx.Policy, +refs: List<&2, String>, +bk: Cm.Backend,
  removed: List<&2, String>, all: List<&2, String>, ok: Bool) ->
  IO(Unit):
  match ok:
    case False{}:
      Cm.Cli.fail("BackendUnavailable: --backend metal was requested, but "
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
    +bk : Cm.Backend = Cm.Cli.backend_of(requested, gpu)
    Cli.run.checked(ar, cmd, rp, p, refs, bk, rm,
      List.append(&2, String, refs, rm), Cm.Cli.backend_ok(bk))

def Cli.top.pick(+ar: Ar.Args, +cmd: String, ok: Bool) -> IO(Unit):
  match ok:
    case False{}:
      IO.print(Cm.Cli.usage())
    case True{}:
      Cli.run(ar, cmd, Ar.Args.one(ar, "repo", "."),
        Cm.Cli.policy(Ar.Args.one(ar, "mode", "full")),
        Cm.Cli.roots_of(ar), Ar.Args.one(ar, "backend", "auto"),
        Ar.Args.values(ar, "remove"))

def Cli.top(+ar: Ar.Args, area: String, +cmd: String) -> IO(Unit):
  Cli.top.pick(ar, cmd, Bool.and(String.eq(area, "git"),
    Bool.not(String.is_empty(cmd))))

def Cli.entry(xs: List<&1, String>) -> IO(Unit):
  +ar = Ar.Args.of(xs)
  Cli.top(ar, Ar.Args.word(ar, 0n), Ar.Args.word(ar, 1n))
