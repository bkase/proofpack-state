# adapters/git/import.bend -- building a source graph from a repository.
#
# SPEC 8.3's import flow, as one loop:
#
#   1. resolve the requested roots to complete object ids and pin them
#   2. ask `cat-file --batch-check` for the type and size of everything in
#      the queue -- so a blob's *contents* are never fetched
#   3. ask `cat-file --batch` for the bodies of the commits, trees and tags
#      only
#   4. parse those bodies, intern every object id they name, and record one
#      adjacency row and one metadata entry per ordinal
#   5. repeat until the queue is empty
#
# Objects are interned on first *mention*, so a child gets its ordinal when a
# parent names it and long before it is fetched. Ordinals are therefore
# assigned in discovery order and the rows come out dense and in order, with
# an empty row for every blob.
#
# A required object the repository does not have is collected, not skipped: a
# missing object is `IncompleteGraph`, never a vertex with no successors
# (SPEC 3.2). A gitlink is recorded as an external reference and not
# traversed -- this program never opens another repository (SPEC 8.2).
#
# Every loop carries a fuel. Running out is `ResourceLimit`, reported as such,
# never an import that quietly stopped early.

import Base
import ../../core/count.bend as C
import ../../host/proc.bend as P
import ./bytes.bend as B
import ./oid.bend as O
import ./intern.bend as I
import ./parse.bend as Pa
import ./git.bend as Gi

# One object's metadata: uncompressed logical payload size, and type. Not a
# physical or on-disk size -- SPEC 2 measures logical object payload bytes.
type Meta is Data:
  Meta{size: U32, kind: U32}

def Meta.size(m: Meta) -> U32:
  match m:
    case Meta{size, kind}:
      size

def Meta.kind(m: Meta) -> U32:
  match m:
    case Meta{size, kind}:
      kind

type Row is Data:
  Row{succ: List<&2, U32>}

def Row.succ(r: Row) -> List<&2, U32>:
  match r:
    case Row{succ}:
      succ

# 256 objects a round, at most 16 MiB of bodies. Both are memory parameters:
# every byte of a body becomes a list cell while it is being parsed, so a
# round's footprint is bounded rather than the whole repository's.
def Imp.batch_size() -> Nat:
  256n

def Imp.batch_bytes() -> U32:
  16777216

def Imp.check_bytes() -> U32:
  4194304

# ---------------------------------------------------------------------------
# Interning the children of one object.
# ---------------------------------------------------------------------------

type KAcc is Data:
  KA{uni: I.Universe, succ: List<&2, U32>, ext: List<&2, O.Oid>}

def Imp.kid.put(succ: List<&2, U32>, ext: List<&2, O.Oid>,
  i: I.Interned) -> KAcc:
  match i:
    case I.In{uni, ord}:
      KA{uni, Con{ord, succ}, ext}

def Imp.kid.go(u: I.Universe, succ: List<&2, U32>, ext: List<&2, O.Oid>,
  +o: O.Oid, link: Bool) -> KAcc:
  match link:
    case True{}:
      KA{u, succ, Con{o, ext}}
    case False{}:
      Imp.kid.put(succ, ext, I.Uni.intern(u, o))

def Imp.kid(+k: Pa.Child, a: KAcc) -> KAcc:
  match a:
    case KA{u, succ, ext}:
      Imp.kid.go(u, succ, ext, Pa.Child.oid(k), Pa.Child.gitlink(k))

def Imp.kids(ks: List<&2, Pa.Child>, a: KAcc) -> KAcc:
  match ks:
    case Nil{}:
      a
    case Con{k, t}:
      Imp.kids(t, Imp.kid(k, a))

def KAcc.uni(a: KAcc) -> I.Universe:
  match a:
    case KA{uni, succ, ext}:
      uni

def KAcc.succ(a: KAcc) -> List<&2, U32>:
  match a:
    case KA{uni, succ, ext}:
      succ

def KAcc.ext(a: KAcc) -> List<&2, O.Oid>:
  match a:
    case KA{uni, succ, ext}:
      ext

# ---------------------------------------------------------------------------
# Folding one round's objects into rows and metadata.
# ---------------------------------------------------------------------------

type FAcc is Data:
  FA{uni: I.Universe, rows: List<&2, Row>, metas: List<&2, Meta>,
    ext: List<&2, O.Oid>, bad: List<&2, O.Oid>, ok: Bool, err: String}

def FAcc.uni(a: FAcc) -> I.Universe:
  match a:
    case FA{uni, rows, metas, ext, bad, ok, err}:
      uni

def FAcc.rows(a: FAcc) -> List<&2, Row>:
  match a:
    case FA{uni, rows, metas, ext, bad, ok, err}:
      List.reverse(&2, Row, rows)

def FAcc.metas(a: FAcc) -> List<&2, Meta>:
  match a:
    case FA{uni, rows, metas, ext, bad, ok, err}:
      List.reverse(&2, Meta, metas)

def FAcc.ext(a: FAcc) -> List<&2, O.Oid>:
  match a:
    case FA{uni, rows, metas, ext, bad, ok, err}:
      ext

def FAcc.bad(a: FAcc) -> List<&2, O.Oid>:
  match a:
    case FA{uni, rows, metas, ext, bad, ok, err}:
      bad

def FAcc.ok(a: FAcc) -> Bool:
  match a:
    case FA{uni, rows, metas, ext, bad, ok, err}:
      ok

def FAcc.err(a: FAcc) -> String:
  match a:
    case FA{uni, rows, metas, ext, bad, ok, err}:
      err

def FAcc.fail(a: FAcc, msg: String) -> FAcc:
  match a:
    case FA{uni, rows, metas, ext, bad, ok, err}:
      FA{uni, rows, metas, ext, bad, False{}, msg}

def Imp.needs_body(k: Pa.GType) -> Bool:
  match k:
    case Pa.TCommit{}:
      True{}
    case Pa.TTree{}:
      True{}
    case Pa.TTag{}:
      True{}
    case Pa.TBlob{}:
      False{}
    case Pa.TMissing{}:
      False{}
    case Pa.TBad{}:
      False{}

def Imp.recs_head(rs: List<&2, Pa.Rec>, want: Bool) -> Maybe<&2, Pa.Rec>:
  match want:
    case False{}:
      None{}
    case True{}:
      List.head(&2, Pa.Rec, rs)

def Imp.recs_rest(rs: List<&2, Pa.Rec>, want: Bool) -> List<&2, Pa.Rec>:
  match want:
    case False{}:
      rs
    case True{}:
      List.tail(&2, Pa.Rec, rs)

def Imp.plain.go(uni: I.Universe, rows: List<&2, Row>,
  metas: List<&2, Meta>, ext: List<&2, O.Oid>, bad: List<&2, O.Oid>,
  ok: Bool, err: String, +oid: O.Oid, +k: Pa.GType, +size: U32,
  missing: Bool) -> FAcc:
  match missing:
    case True{}:
      FA{uni, Con{Row{Nil{}}, rows},
        Con{Meta{0, Pa.GType.code(k)}, metas}, ext, Con{oid, bad}, ok, err}
    case False{}:
      FA{uni, Con{Row{Nil{}}, rows},
        Con{Meta{size, Pa.GType.code(k)}, metas}, ext, bad, ok, err}

# An object with no body: a blob (terminal), or one the repository does not
# have (collected as `bad`, which the caller turns into IncompleteGraph).
def Imp.plain(a: FAcc, +oid: O.Oid, +k: Pa.GType, +size: U32) -> FAcc:
  match a:
    case FA{uni, rows, metas, ext, bad, ok, err}:
      Imp.plain.go(uni, rows, metas, ext, bad, ok, err, oid, k, size,
        Pa.GType.is_missing(k))

def Imp.bodied.go(rows: List<&2, Row>, metas: List<&2, Meta>,
  bad: List<&2, O.Oid>, ok: Bool, err: String, +k: Pa.GType, +size: U32,
  +ka: KAcc) -> FAcc:
  FA{KAcc.uni(ka), Con{Row{KAcc.succ(ka)}, rows},
    Con{Meta{size, Pa.GType.code(k)}, metas}, KAcc.ext(ka), bad, ok, err}

def Imp.bodied.kids(uni: I.Universe, rows: List<&2, Row>,
  metas: List<&2, Meta>, ext: List<&2, O.Oid>, bad: List<&2, O.Oid>,
  ok: Bool, err: String, +k: Pa.GType, +size: U32, ks: Pa.Kids) -> FAcc:
  match ks:
    case Pa.Kids{items, kok}:
      match kok:
        case False{}:
          FA{uni, rows, metas, ext, bad, False{},
            "InvalidInput: malformed object body"}
        case True{}:
          Imp.bodied.go(rows, metas, bad, ok, err, k, size,
            Imp.kids(items, KA{uni, Nil{}, ext}))

def Imp.bodied(a: FAcc, +f: O.Fmt, +k: Pa.GType, +size: U32,
  body: B.Bytes) -> FAcc:
  match a:
    case FA{uni, rows, metas, ext, bad, ok, err}:
      Imp.bodied.kids(uni, rows, metas, ext, bad, ok, err, k, size,
        Pa.Parse.children(f, k, body))

def Imp.one(a: FAcc, +f: O.Fmt, +i: Pa.Info, mr: Maybe<&2, Pa.Rec>) -> FAcc:
  match mr:
    case None{}:
      Imp.plain(a, Pa.Info.oid(i), Pa.Info.kind(i),
        U32.from_nat(Pa.Info.size(i)))
    case Some{r}:
      Imp.bodied(a, f, Pa.Info.kind(i), U32.from_nat(Pa.Info.size(i)),
        Pa.Rec.body(r))

def Imp.objs(+infos: List<&2, Pa.Info>, +recs: List<&2, Pa.Rec>,
  +f: O.Fmt, a: FAcc) -> FAcc:
  match infos:
    case Nil{}:
      a
    case Con{i, it}:
      +want = Imp.needs_body(Pa.Info.kind(i))
      Imp.objs(it, Imp.recs_rest(recs, want), f,
        Imp.one(a, f, i, Imp.recs_head(recs, want)))

# ---------------------------------------------------------------------------
# Building the stdin for one `cat-file` call.
# ---------------------------------------------------------------------------

def Imp.hex_lines(+f: O.Fmt, os: List<&2, O.Oid>) -> String:
  match os:
    case Nil{}:
      ""
    case Con{o, t}:
      O.Oid.show(f, o) ++ "\n" ++ Imp.hex_lines(f, t)

def Imp.wanted.push(o: O.Oid, want: Bool, rest: List<&2, O.Oid>) ->
  List<&2, O.Oid>:
  match want:
    case False{}:
      rest
    case True{}:
      Con{o, rest}

def Imp.wanted(+infos: List<&2, Pa.Info>) -> List<&2, O.Oid>:
  match infos:
    case Nil{}:
      Nil{}
    case Con{i, t}:
      Imp.wanted.push(Pa.Info.oid(i), Imp.needs_body(Pa.Info.kind(i)),
        Imp.wanted(t))

# ---------------------------------------------------------------------------
# One round, as a pure fold over what the two Git calls answered.
# ---------------------------------------------------------------------------

def Imp.absorb.recs(+a: FAcc, +f: O.Fmt, infos: List<&2, Pa.Info>,
  rs: Pa.Recs) -> FAcc:
  match rs:
    case Pa.Recs{items, ok}:
      match ok:
        case False{}:
          FAcc.fail(a, "InvalidInput: malformed cat-file --batch stream")
        case True{}:
          Imp.objs(infos, items, f, a)

def Imp.absorb.bodies(+a: FAcc, +f: O.Fmt, infos: List<&2, Pa.Info>,
  +bod: Gi.Out, good: Bool) -> FAcc:
  match good:
    case False{}:
      FAcc.fail(a, "UnsupportedRepository: git cat-file --batch failed: "
        ++ Gi.Out.err(bod))
    case True{}:
      Imp.absorb.recs(a, f, infos, Pa.Parse.recs(f, Gi.Out.body(bod)))

def Imp.absorb.infos(+a: FAcc, +f: O.Fmt, inf: Pa.Infos, +bod: Gi.Out,
  chk_ok: Bool) -> FAcc:
  match chk_ok:
    case False{}:
      FAcc.fail(a,
        "InvalidInput: malformed cat-file --batch-check stream")
    case True{}:
      Imp.absorb.bodies(a, f, Pa.Infos.items(inf), bod,
        U32.is_zero(Gi.Out.status(bod)))

def Imp.absorb.check(+a: FAcc, +f: O.Fmt, +inf: Pa.Infos, bod: Gi.Out,
  ran: Bool, msg: String) -> FAcc:
  match ran:
    case False{}:
      FAcc.fail(a,
        "UnsupportedRepository: git cat-file --batch-check failed: " ++ msg)
    case True{}:
      Imp.absorb.infos(a, f, inf, bod, Pa.Infos.ok(inf))

def Imp.absorb(+a: FAcc, +f: O.Fmt, +chk: Gi.Out, inf: Pa.Infos,
  bod: Gi.Out) -> FAcc:
  Imp.absorb.check(a, f, inf, bod, U32.is_zero(Gi.Out.status(chk)),
    Gi.Out.err(chk))

# The queue for the next round: whatever this round did not take, plus every
# object this round discovered, in ordinal order.
def Imp.next_queue(rest: List<&2, O.Oid>, +a2: FAcc, +n0: Nat) ->
  List<&2, O.Oid>:
  List.append(&2, O.Oid, rest,
    I.Uni.recent(FAcc.uni(a2), Nat.sub(I.Uni.size(FAcc.uni(a2)), n0)))

def Imp.keep_queue(q: List<&2, O.Oid>, ok: Bool) -> List<&2, O.Oid>:
  match ok:
    case True{}:
      q
    case False{}:
      Nil{}

# ---------------------------------------------------------------------------
# The loop. One def, because Bend forbids mutual recursion: a failed round
# stops it by handing an empty queue to the next iteration rather than by
# calling a helper that would call back.
# ---------------------------------------------------------------------------

def Imp.loop(+fuel: Nat, +repo: String, +f: O.Fmt, +a: FAcc,
  queue: List<&2, O.Oid>) -> IO(FAcc):
  match fuel:
    case 0n:
      IO.pure(FAcc,
        FAcc.fail(a, "ResourceLimit: import rounds exhausted"))
    case 1n+g:
      match queue:
        case Nil{}:
          IO.pure(FAcc, a)
        case Con{o, t}:
          +q = {Con{o, t} : List<&2, O.Oid>}
          +batch = List.take(&2, O.Oid, q, Imp.batch_size())
          +rest = List.drop(&2, O.Oid, q, Imp.batch_size())
          +n0 = I.Uni.size(FAcc.uni(a))
          do IO<FAcc>:
            chk0 : Gi.Out <- Gi.Git.batch_check(repo,
              Imp.hex_lines(f, batch), Imp.check_bytes())
            +chk : Gi.Out = chk0
            +inf : Pa.Infos = Pa.Parse.infos(f, Gi.Out.body(chk))
            bod : Gi.Out <- Gi.Git.batch(repo,
              Imp.hex_lines(f, Imp.wanted(Pa.Infos.items(inf))),
              Imp.batch_bytes())
            +a2 : FAcc = Imp.absorb(a, f, chk, inf, bod)
            Imp.loop(g, repo, f, a2,
              Imp.keep_queue(Imp.next_queue(rest, a2, n0), FAcc.ok(a2)))

# ---------------------------------------------------------------------------
# Resolving the requested roots. SPEC 3.1: a symbolic ref is resolved to an
# object id before evaluation, and the query then refers to the resolved root
# vector, not a moving HEAD.
# ---------------------------------------------------------------------------

type Roots is Data:
  Rts{oids: List<&2, O.Oid>, ok: Bool, err: String}

def Roots.oids(r: Roots) -> List<&2, O.Oid>:
  match r:
    case Rts{oids, ok, err}:
      List.reverse(&2, O.Oid, oids)

def Roots.ok(r: Roots) -> Bool:
  match r:
    case Rts{oids, ok, err}:
      ok

def Roots.err(r: Roots) -> String:
  match r:
    case Rts{oids, ok, err}:
      err

def Imp.root.push(acc: Roots, +oid: O.Oid) -> Roots:
  match acc:
    case Rts{oids, ok, err}:
      Rts{Con{oid, oids}, ok, err}

def Imp.root.take(acc: Roots, ref: String, r: O.OidRead) -> Roots:
  match r:
    case O.Read{oid, ok}:
      match ok:
        case False{}:
          Rts{Nil{}, False{},
            "UnknownRoot: unreadable object id for " ++ ref}
        case True{}:
          Imp.root.push(acc, oid)

def Imp.root.read(acc: Roots, +f: O.Fmt, ref: String, out: Gi.Out,
  ran: Bool) -> Roots:
  match ran:
    case False{}:
      Rts{Nil{}, False{},
        "UnknownRoot: git rev-parse --verify failed for " ++ ref}
    case True{}:
      Imp.root.take(acc, ref,
        O.Oid.of_hex(f, B.Cut.taken(B.Bytes.line(Gi.Out.body(out)))))

def Imp.roots(refs: List<&2, String>, +repo: String, +f: O.Fmt,
  acc: Roots) -> IO(Roots):
  match refs:
    case Nil{}:
      IO.pure(Roots, acc)
    case Con{ref, t}:
      +r = ref
      do IO<Roots>:
        out : Gi.Out <- Gi.Git.resolve(repo, r)
        +o2 : Gi.Out = out
        Imp.roots(t, repo, f,
          Imp.root.read(acc, f, r, o2, U32.is_zero(Gi.Out.status(o2))))
