# index/source.bend -- the derived source graph, as a published artifact.
#
# A graph snapshot says what named objects require; an inventory observation
# says what a store reports as present. They are different data products
# (SPEC 8.1), and this is the first one.
#
# Depths are fixed rather than sized to the import: the ordinal trie is 32
# deep (the whole 2^32 ordinal space v0.1 supports) and the set tree is 20
# deep (a 4096-ordinal leaf times 2^20). Ordinals are assigned densely from
# zero, so an unused half of a node is a single gap and a table of N objects
# still costs about 2N nodes -- while every type in the program gets a
# concrete depth instead of a dependent pair threaded through every
# signature.

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

def Idx.td() -> Nat:
  32n

def Idx.sd() -> Nat:
  20n

def Idx.meta_gap() -> Im.Meta:
  Im.Meta{0, 5}

type Policy is Data:
  PFull{}
  PTreeData{}

def Policy.name(p: Policy) -> String:
  match p:
    case PFull{}:
      "git-full/v1"
    case PTreeData{}:
      "git-tree-data/v1"

def Policy.short(p: Policy) -> String:
  match p:
    case PFull{}:
      "full"
    case PTreeData{}:
      "tree-data"

type Source is Data:
  Src{fmt: O.Fmt, n: Nat, uni: I.Universe,
    full: G.Graph(), tree: G.Graph(),
    meta: T.Trie<Im.Meta>, ids: T.Trie<O.Oid>,
    roots: List<&2, U32>, root_oids: List<&2, O.Oid>,
    ext: List<&2, O.Oid>, bad: List<&2, O.Oid>}

def Source.fmt(+s: Source) -> O.Fmt:
  match s:
    case Src{fmt, n, uni, full, tree, meta, ids, roots, root_oids, ext, bad}:
      fmt

def Source.n(+s: Source) -> Nat:
  match s:
    case Src{fmt, n, uni, full, tree, meta, ids, roots, root_oids, ext, bad}:
      n

def Source.uni(+s: Source) -> I.Universe:
  match s:
    case Src{fmt, n, uni, full, tree, meta, ids, roots, root_oids, ext, bad}:
      uni

def Source.graph.pick(p: Policy, full: G.Graph(), tree: G.Graph()) ->
  G.Graph():
  match p:
    case PFull{}:
      full
    case PTreeData{}:
      tree

def Source.graph(+s: Source, p: Policy) -> G.Graph():
  match s:
    case Src{fmt, n, uni, full, tree, meta, ids, roots, root_oids, ext, bad}:
      Source.graph.pick(p, full, tree)

def Source.meta(+s: Source) -> T.Trie<Im.Meta>:
  match s:
    case Src{fmt, n, uni, full, tree, meta, ids, roots, root_oids, ext, bad}:
      meta

def Source.ids(+s: Source) -> T.Trie<O.Oid>:
  match s:
    case Src{fmt, n, uni, full, tree, meta, ids, roots, root_oids, ext, bad}:
      ids

def Source.roots(+s: Source) -> List<&2, U32>:
  match s:
    case Src{fmt, n, uni, full, tree, meta, ids, roots, root_oids, ext, bad}:
      roots

def Source.root_oids(+s: Source) -> List<&2, O.Oid>:
  match s:
    case Src{fmt, n, uni, full, tree, meta, ids, roots, root_oids, ext, bad}:
      root_oids

def Source.ext(+s: Source) -> List<&2, O.Oid>:
  match s:
    case Src{fmt, n, uni, full, tree, meta, ids, roots, root_oids, ext, bad}:
      ext

def Source.bad(+s: Source) -> List<&2, O.Oid>:
  match s:
    case Src{fmt, n, uni, full, tree, meta, ids, roots, root_oids, ext, bad}:
      bad

# The object id an ordinal names. `identify` of SPEC 3.1, in the direction
# results are printed.
def Source.oid_of.un(m: Maybe<&2, O.Oid>) -> O.Oid:
  match m:
    case None{}:
      O.Oid.zero()
    case Some{o}:
      o

def Source.oid_of(+s: Source, +x: U32) -> O.Oid:
  Source.oid_of.un(T.Trie.at(O.Oid, 32n, Source.ids(s), x))

def Source.meta_of.un(m: Maybe<&2, Im.Meta>) -> Im.Meta:
  match m:
    case None{}:
      Idx.meta_gap()
    case Some{v}:
      v

def Source.meta_of(+s: Source, +x: U32) -> Im.Meta:
  Source.meta_of.un(T.Trie.at(Im.Meta, 32n, Source.meta(s), x))

# ---------------------------------------------------------------------------
# The tree-data policy, derived from the full graph.
#
# SPEC 8.2's table: `tree-data` follows tag -> target, commit -> root tree,
# tree -> subtree and tree -> blob, but does *not* follow commit -> parent.
# A commit's parents are commits and its root tree is a tree, so dropping
# exactly the commit -> commit edges is exactly that policy -- no edge labels
# are needed, only the types the importer already recorded.
#
# `tree-data` means enough ordinary superproject object content to describe
# the selected snapshot. It is NOT a guarantee that a checkout, build,
# submodule operation or smudge filter will succeed (SPEC 8.2).
# ---------------------------------------------------------------------------

def Idx.is_commit(+m: Im.Meta) -> Bool:
  U32.is_eq(Im.Meta.kind(m), 0)

def Idx.keep.pick(+v: U32, drop: Bool, rest: List<&2, U32>) ->
  List<&2, U32>:
  match drop:
    case True{}:
      rest
    case False{}:
      Con{v, rest}

def Idx.filter_succ(+mt: T.Trie<Im.Meta>, +succ: List<&2, U32>) ->
  List<&2, U32>:
  match succ:
    case Nil{}:
      Nil{}
    case Con{v, t}:
      Idx.keep.pick(v,
        Idx.is_commit(Source.meta_of.un(T.Trie.at(Im.Meta, 32n, mt, v))),
        Idx.filter_succ(mt, t))

def Idx.tree_row(+mt: T.Trie<Im.Meta>, row: List<&2, U32>,
  parent_commit: Bool) -> List<&2, U32>:
  match parent_commit:
    case False{}:
      row
    case True{}:
      Idx.filter_succ(mt, row)

def Idx.tree_rows(+mt: T.Trie<Im.Meta>, rows: List<&2, Im.Row>,
  metas: List<&2, Im.Meta>) -> List<&2, G.Succ>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, rt}:
      match metas:
        case Nil{}:
          Nil{}
        case Con{m, mtl}:
          Con{Idx.tree_row(mt, Im.Row.succ(r), Idx.is_commit(m)),
            Idx.tree_rows(mt, rt, mtl)}

def Idx.full_rows(rows: List<&2, Im.Row>) -> List<&2, G.Succ>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{Im.Row.succ(r), Idx.full_rows(t)}

# ---------------------------------------------------------------------------
# Assembling an import into a published source graph.
# ---------------------------------------------------------------------------

type Built is Data:
  BOk{src: Source}
  BErr{msg: String}

type Seed is Data:
  Sd{uni: I.Universe, ords: List<&2, U32>}

def Idx.seed.done(s: Seed) -> Seed:
  match s:
    case Sd{uni, ords}:
      Sd{uni, List.reverse(&2, U32, ords)}

def Idx.seed.push(ords: List<&2, U32>, i: I.Interned) -> Seed:
  match i:
    case I.In{uni, ord}:
      Sd{uni, Con{ord, ords}}

def Idx.seed(oids: List<&2, O.Oid>, s: Seed) -> Seed:
  match oids:
    case Nil{}:
      Idx.seed.done(s)
    case Con{o, t}:
      match s:
        case Sd{u, ords}:
          Idx.seed(t, Idx.seed.push(ords, I.Uni.intern(u, o)))

def Idx.seed.all(oids: List<&2, O.Oid>, u: I.Universe) -> Seed:
  Idx.seed(oids, Sd{u, Nil{}})

def Seed.uni(s: Seed) -> I.Universe:
  match s:
    case Sd{uni, ords}:
      uni

def Seed.ords(s: Seed) -> List<&2, U32>:
  match s:
    case Sd{uni, ords}:
      ords

# An object the repository does not have is IncompleteGraph, reported with
# its identity rather than silently treated as a leaf (SPEC 3.2).
#
# Only the first few are named. A partial clone is missing thousands, and an
# error message that lists them all is both useless and, built by appending
# to a growing accumulator, quadratic -- on a 16k-object partial clone that
# single line took two and a half minutes of the three the whole command
# took. The append is right-nested now as well, so it is linear in what it
# does print.
def Idx.report_max() -> Nat:
  8n

def Idx.report_bad(+f: O.Fmt, +k: Nat, bad: List<&2, O.Oid>) -> String:
  match k:
    case 0n:
      " ..."
    case 1n+p:
      match bad:
        case Nil{}:
          ""
        case Con{o, t}:
          " " ++ O.Oid.show(f, o) ++ Idx.report_bad(f, p, t)

def Idx.assemble.tries(+f: O.Fmt, +n: Nat, +uni: I.Universe,
  +rows: List<&2, Im.Row>, +metas: List<&2, Im.Meta>,
  ext: List<&2, O.Oid>, roots: List<&2, U32>,
  root_oids: List<&2, O.Oid>) -> Built:
  +mt = T.Trie.of_list(Im.Meta, 32n, metas)
  BOk{Src{f, n, uni,
    T.Trie.of_list(G.Succ, 32n, Idx.full_rows(rows)),
    T.Trie.of_list(G.Succ, 32n, Idx.tree_rows(mt, rows, metas)),
    mt,
    T.Trie.of_list(O.Oid, 32n, I.Uni.identify(uni)),
    roots, root_oids, ext, Nil{}}}

def Idx.assemble.go(+f: O.Fmt, +a: Im.FAcc, roots: List<&2, U32>,
  root_oids: List<&2, O.Oid>) -> Built:
  Idx.assemble.tries(f, I.Uni.size(Im.FAcc.uni(a)),
    Im.FAcc.uni(a), Im.FAcc.rows(a), Im.FAcc.metas(a),
    Im.FAcc.ext(a), roots, root_oids)

def Idx.assemble.bad(+f: O.Fmt, +a: Im.FAcc, roots: List<&2, U32>,
  root_oids: List<&2, O.Oid>, clean: Bool) -> Built:
  match clean:
    case True{}:
      Idx.assemble.go(f, a, roots, root_oids)
    case False{}:
      +missing = Im.FAcc.bad(a)
      BErr{"IncompleteGraph: the repository is missing "
        ++ Nat.show(List.length(&2, O.Oid, missing))
        ++ " objects the full closure of these roots requires. A partial "
        ++ "clone or a shallow history cannot serve as an import source "
        ++ "(SPEC 8.1), and no object is fetched over the network during "
        ++ "an import. Among the missing:"
        ++ Idx.report_bad(f, Idx.report_max(), missing)}

def Idx.assemble.ok(+f: O.Fmt, +a: Im.FAcc, roots: List<&2, U32>,
  root_oids: List<&2, O.Oid>, ok: Bool) -> Built:
  match ok:
    case True{}:
      Idx.assemble.bad(f, a, roots, root_oids,
        List.is_empty(&2, O.Oid, Im.FAcc.bad(a)))
    case False{}:
      BErr{Im.FAcc.err(a)}
def Idx.assemble(+f: O.Fmt, +a: Im.FAcc, roots: List<&2, U32>,
  root_oids: List<&2, O.Oid>) -> Built:
  Idx.assemble.ok(f, a, roots, root_oids, Im.FAcc.ok(a))


# ---------------------------------------------------------------------------
# The import, end to end.
#
# SPEC 8.5: ref resolution, graph collection and inventory enumeration are not
# one atomic filesystem transaction. The resolved root vector is pinned here,
# before any body is fetched, and everything after that refers to the pinned
# vector rather than to a moving ref. Once published, the derived graph is
# immutable even if the live repository changes.
# ---------------------------------------------------------------------------

def Idx.rounds() -> Nat:
  4194304n

def Idx.import.fold(a: Im.FAcc, +f: O.Fmt, roots: List<&2, U32>,
  root_oids: List<&2, O.Oid>) -> Built:
  Idx.assemble(f, a, roots, root_oids)

def Idx.import.loop(+repo: String, +f: O.Fmt, root_oids: List<&2, O.Oid>,
  roots: List<&2, U32>, u: I.Universe, queue: List<&2, O.Oid>) ->
  IO(Built):
  do IO<Built>:
    a : Im.FAcc <- Im.Imp.loop(Idx.rounds(), repo, f,
      Im.FA{u, Nil{}, Nil{}, Nil{}, Nil{}, True{}, ""}, queue)
    return Idx.import.fold(a, f, roots, root_oids)

def Idx.import.seeded(+repo: String, +f: O.Fmt, rs: Im.Roots, ok: Bool) ->
  IO(Built):
  match ok:
    case False{}:
      IO.pure(Built, BErr{Im.Roots.err(rs)})
    case True{}:
      +oids = Im.Roots.oids(rs)
      +sd = Idx.seed.all(oids, I.Uni.new(f))
      +u = Seed.uni(sd)
      Idx.import.loop(repo, f, oids, Seed.ords(sd), u, I.Uni.identify(u))

def Idx.import.roots(+repo: String, refs: List<&2, String>, +f: O.Fmt) ->
  IO(Built):
  do IO<Built>:
    rs : Im.Roots <- Im.Imp.roots(refs, repo, f,
      Im.Rts{Nil{}, True{}, ""})
    +r2 : Im.Roots = rs
    Idx.import.seeded(repo, f, r2, Im.Roots.ok(r2))

def Idx.import.with_fmt(+repo: String, refs: List<&2, String>,
  mf: Maybe<&2, O.Fmt>) -> IO(Built):
  match mf:
    case None{}:
      IO.pure(Built,
        BErr{"UnsupportedRepository: unrecognised object format"})
    case Some{f}:
      Idx.import.roots(repo, refs, f)

def Idx.import.checked(+repo: String, refs: List<&2, String>, out: Gi.Out,
  ran: Bool) -> IO(Built):
  match ran:
    case False{}:
      IO.pure(Built,
        BErr{"UnsupportedRepository: not a Git repository: "
          ++ Gi.Out.err(out)})
    case True{}:
      Idx.import.with_fmt(repo, refs, Gi.Git.fmt_of(Gi.Out.body(out)))

def Idx.import(+repo: String, refs: List<&2, String>) -> IO(Built):
  do IO<Built>:
    fo : Gi.Out <- Gi.Git.object_format(repo)
    +f0 : Gi.Out = fo
    Idx.import.checked(repo, refs, f0, U32.is_zero(Gi.Out.status(f0)))

# ---------------------------------------------------------------------------
# Reading the per-ordinal tables back out, in ordinal order. The store
# encoder needs them; nothing on a query path does, so the O(n * depth) walk
# is paid once per import rather than per query.
# ---------------------------------------------------------------------------

def Source.metas.go(+src: Source, +k: Nat, +i: U32,
  acc: List<&2, Im.Meta>) -> List<&2, Im.Meta>:
  match k:
    case 0n:
      List.reverse(&2, Im.Meta, acc)
    case 1n+p:
      Source.metas.go(src, p, (i + 1 : U32),
        Con{Source.meta_of(src, i), acc})

def Source.metas(+src: Source) -> List<&2, Im.Meta>:
  Source.metas.go(src, Source.n(src), 0, Nil{})

def Source.row_of.un(m: Maybe<&2, G.Succ>) -> Im.Row:
  match m:
    case None{}:
      Im.Row{Nil{}}
    case Some{s}:
      Im.Row{s}

def Source.rows.go(+src: Source, +k: Nat, +i: U32,
  acc: List<&2, Im.Row>) -> List<&2, Im.Row>:
  match k:
    case 0n:
      List.reverse(&2, Im.Row, acc)
    case 1n+p:
      Source.rows.go(src, p, (i + 1 : U32),
        Con{Source.row_of.un(T.Trie.at(G.Succ, 32n,
          Source.graph(src, PFull{}), i)), acc})

def Source.rows(+src: Source) -> List<&2, Im.Row>:
  Source.rows.go(src, Source.n(src), 0, Nil{})
