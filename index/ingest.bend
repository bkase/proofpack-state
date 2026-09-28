# index/ingest.bend -- building a source by actually reading a repository.
#
# index/source.bend is the pure index: the object table, the two graph
# policies, assembly from a walk accumulator, and the row and metadata
# readers. LAWS.bend talks about those. This module is the entry that runs
# `git` -- resolving refs, importing objects, seeding the roots -- and hands
# the pure assembler what it produced.
#
# The split keeps index/source.bend free of adapters/git/git.bend, so no law
# reaches unsafe or foreign code.

import Base
import ../core/count.bend as C
import ../core/set.bend as S
import ../core/trie.bend as T
import ../closure/graph.bend as G
import ../adapters/git/oid.bend as O
import ../adapters/git/intern.bend as I
import ../adapters/git/parse.bend as Pa
import ../adapters/git/import.bend as Im
import ../adapters/git/git.bend as Gi
import ../adapters/git/gitout.bend as Go
import ../adapters/git/fetch.bend as Ft
import ./source.bend as Sc
def Idx.rounds() -> Nat:
  4194304n

def Idx.import.fold(a: Im.FAcc, +f: O.Fmt, roots: List<&2, U32>,
  root_oids: List<&2, O.Oid>) -> Sc.Built:
  Sc.Idx.assemble(f, a, roots, root_oids)

def Idx.import.loop(+repo: String, +f: O.Fmt, root_oids: List<&2, O.Oid>,
  roots: List<&2, U32>, u: I.Universe, queue: List<&2, O.Oid>) ->
  IO(Sc.Built):
  do IO<Sc.Built>:
    a : Im.FAcc <- Ft.Imp.loop(Idx.rounds(), repo, f,
      Im.FA{u, Nil{}, Nil{}, Nil{}, Nil{}, True{}, ""}, queue)
    return Idx.import.fold(a, f, roots, root_oids)

def Idx.import.seeded(+repo: String, +f: O.Fmt, rs: Im.Roots, ok: Bool) ->
  IO(Sc.Built):
  match ok:
    case False{}:
      IO.pure(Sc.Built, Sc.BErr{Im.Roots.err(rs)})
    case True{}:
      +oids = Im.Roots.oids(rs)
      +sd = Sc.Idx.seed.all(oids, I.Uni.new(f))
      +u = Sc.Seed.uni(sd)
      Idx.import.loop(repo, f, oids, Sc.Seed.ords(sd), u, I.Uni.identify(u))

def Idx.import.roots(+repo: String, refs: List<&2, String>, +f: O.Fmt) ->
  IO(Sc.Built):
  do IO<Sc.Built>:
    rs : Im.Roots <- Ft.Imp.roots(refs, repo, f,
      Im.Rts{Nil{}, True{}, ""})
    +r2 : Im.Roots = rs
    Idx.import.seeded(repo, f, r2, Im.Roots.ok(r2))

def Idx.import.with_fmt(+repo: String, refs: List<&2, String>,
  mf: Maybe<&2, O.Fmt>) -> IO(Sc.Built):
  match mf:
    case None{}:
      IO.pure(Sc.Built,
        Sc.BErr{"UnsupportedRepository: unrecognised object format"})
    case Some{f}:
      Idx.import.roots(repo, refs, f)

def Idx.import.checked(+repo: String, refs: List<&2, String>, out: Go.Out,
  ran: Bool) -> IO(Sc.Built):
  match ran:
    case False{}:
      IO.pure(Sc.Built,
        Sc.BErr{"UnsupportedRepository: not a Git repository: "
          ++ Go.Out.err(out)})
    case True{}:
      Idx.import.with_fmt(repo, refs, Go.Git.fmt_of(Go.Out.body(out)))

def Idx.import(+repo: String, refs: List<&2, String>) -> IO(Sc.Built):
  do IO<Sc.Built>:
    fo : Go.Out <- Gi.Git.object_format(repo)
    +f0 : Go.Out = fo
    Idx.import.checked(repo, refs, f0, U32.is_zero(Go.Out.status(f0)))

# ---------------------------------------------------------------------------
# Reading the per-ordinal tables back out, in ordinal order. The store
# encoder needs them; nothing on a query path does, so the O(n * depth) walk
# is paid once per import rather than per query.
# ---------------------------------------------------------------------------
