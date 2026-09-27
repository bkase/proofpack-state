# adapters/git/import.bend -- building a source graph from a repository.
#
# SPEC 8.3's import flow, in two phases:
#
#   1. one `cat-file --batch-check --batch-all-objects` call learns the type
#      and size of every object in the store -- and no blob contents, ever
#   2. the commits, trees and tags have their bodies fetched in large chunks
#      by `cat-file --batch`, parsed, and recorded in an object table keyed by
#      complete object id
#   3. a pure breadth-first walk from the resolved roots reads that table,
#      interning each object id on first mention
#
# It was a queue-driven loop at first, fetching what the frontier had just
# discovered. That is the natural shape and it is the wrong one for Git
# history: a commit names one parent, so a linear history advances about two
# objects a round, and a round is a subprocess. On a 16k-object repository
# that was ~6000 `git` invocations at ~30 ms each -- the process sat in
# `select` while its own batching starved. Fetching the bodies in chunks of
# 2048 makes it nine calls.
#
# The universe is still exactly the closure of the roots, not the whole
# repository: bodies are fetched in bulk, but an ordinal is only ever handed
# out by the walk in phase 3, so an unreachable object is read and discarded.
#
# Objects are interned on first *mention*, so a child gets its ordinal when a
# parent names it. Ordinals are therefore assigned in discovery order and the
# rows come out dense and in order, with an empty row for every blob.
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
import ../../core/trie.bend as T

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

# ---------------------------------------------------------------------------
# The object table: complete object id -> type, size, and the object ids the
# body names. Bucketed on a digest word like the interning table, and
# compared on the complete key, so a collision costs a list step and never a
# wrong answer.
#
# This is *not* the universe. Nothing here has an ordinal; an object is in the
# universe only once the walk below reaches it.
# ---------------------------------------------------------------------------

type Obj is Data:
  Ob{oid: O.Oid, kind: U32, size: U32, kids: List<&2, Pa.Child>}

def ObjBucket() -> Data:
  List<&2, Obj>

def Obj.oid(+o: Obj) -> O.Oid:
  match o:
    case Ob{oid, kind, size, kids}:
      oid

def Obj.kind(+o: Obj) -> U32:
  match o:
    case Ob{oid, kind, size, kids}:
      kind

def Obj.size(+o: Obj) -> U32:
  match o:
    case Ob{oid, kind, size, kids}:
      size

def Obj.kids(+o: Obj) -> List<&2, Pa.Child>:
  match o:
    case Ob{oid, kind, size, kids}:
      kids

def Tab.key(+o: O.Oid) -> U32:
  U32.and(O.Oid.key(o), 1048575)

def Tab.pick(+b: Obj, same: Bool) -> Maybe<&2, Obj>:
  match same:
    case True{}:
      Some{b}
    case False{}:
      None{}

def Tab.scan(bs: List<&2, Obj>, +o: O.Oid, got: Maybe<&2, Obj>) ->
  Maybe<&2, Obj>:
  match bs:
    case Nil{}:
      got
    case Con{b, t}:
      match got:
        case Some{x}:
          Some{x}
        case None{}:
          +bb = b
          Tab.scan(t, o, Tab.pick(bb, O.Oid.eq(Obj.oid(bb), o)))

def Tab.bucket.un(m: Maybe<&2, ObjBucket>) -> ObjBucket:
  match m:
    case None{}:
      Nil{}
    case Some{b}:
      b

def Tab.bucket(+t: T.Trie<ObjBucket>, +k: U32) -> ObjBucket:
  Tab.bucket.un(T.Trie.at(ObjBucket, 20n, t, k))

def Tab.find(+t: T.Trie<ObjBucket>, +o: O.Oid) -> Maybe<&2, Obj>:
  Tab.scan(Tab.bucket(t, Tab.key(o)), o, None{})

# The size phase 1 recorded, or zero if the object was somehow not listed.
def Tab.size_of(m: Maybe<&2, Obj>) -> U32:
  match m:
    case None{}:
      0
    case Some{ob}:
      Obj.size(ob)

def Tab.put(+t: T.Trie<ObjBucket>, +ob: Obj) -> T.Trie<ObjBucket>:
  +k = Tab.key(Obj.oid(ob))
  T.Trie.set(ObjBucket, 20n, t, k, Con{ob, Tab.bucket(t, k)})

# Phase 1: every object's type and size, from one `--batch-check
# --batch-all-objects` call. Bodies come later and only for the non-blobs.
def Tab.of_infos(infos: List<&2, Pa.Info>, t: T.Trie<ObjBucket>) -> T.Trie<ObjBucket>:
  match infos:
    case Nil{}:
      t
    case Con{i, rest}:
      +ii = i
      Tab.of_infos(rest, Tab.put(t, Ob{Pa.Info.oid(ii),
        Pa.GType.code(Pa.Info.kind(ii)),
        U32.from_nat(Pa.Info.size(ii)), Nil{}}))

def Imp.walk.absent(a: FAcc, +oid: O.Oid) -> FAcc:
  match a:
    case FA{uni, rows, metas, ext, bad, ok, err}:
      FA{uni, Con{Row{Nil{}}, rows}, Con{Meta{0, 4}, metas}, ext,
        Con{oid, bad}, ok, err}

def Imp.walk.emit(rows: List<&2, Row>, metas: List<&2, Meta>,
  bad: List<&2, O.Oid>, ok: Bool, err: String, +kind: U32, +size: U32,
  +ka: KAcc) -> FAcc:
  FA{KAcc.uni(ka), Con{Row{List.reverse(&2, U32, KAcc.succ(ka))}, rows},
    Con{Meta{size, kind}, metas}, KAcc.ext(ka), bad, ok, err}

def Imp.walk.here(a: FAcc, +ob: Obj) -> FAcc:
  match a:
    case FA{uni, rows, metas, ext, bad, ok, err}:
      Imp.walk.emit(rows, metas, bad, ok, err, Obj.kind(ob), Obj.size(ob),
        Imp.kids(Obj.kids(ob), KA{uni, Nil{}, ext}))

def Imp.walk.got(a: FAcc, +oid: O.Oid, m: Maybe<&2, Obj>) -> FAcc:
  match m:
    case None{}:
      Imp.walk.absent(a, oid)
    case Some{ob}:
      Imp.walk.here(a, ob)

def Imp.walk.one(a: FAcc, +tab: T.Trie<ObjBucket>, +oid: O.Oid) -> FAcc:
  Imp.walk.got(a, oid, Tab.find(tab, oid))

# The queue holds the object ids in ordinal order. Interning during a step
# appends newly mentioned ids to the universe; `Uni.recent` reads them back
# and they join the queue, which is why the rows stay dense and in order.
#
# It is a two-list queue -- take from the front, push onto the back, and
# reverse the back when the front empties -- because appending to the end of
# a single list costs the queue's whole length. With one append per object
# that is quadratic, and it was: the walk alone took minutes on a 16k-object
# repository. Amortised, this is one cons per object.
def Imp.walk.push(xs: List<&2, O.Oid>, back: List<&2, O.Oid>) ->
  List<&2, O.Oid>:
  match xs:
    case Nil{}:
      back
    case Con{x, t}:
      Imp.walk.push(t, Con{x, back})

def Imp.walk(+fuel: Nat, +tab: T.Trie<ObjBucket>, +a: FAcc,
  front: List<&2, O.Oid>, back: List<&2, O.Oid>) -> FAcc:
  match fuel:
    case 0n:
      FAcc.fail(a, "ResourceLimit: the import walk ran out of steps")
    case 1n+g:
      match front:
        case Con{o, t}:
          +n0 = I.Uni.size(FAcc.uni(a))
          +a2 = Imp.walk.one(a, tab, o)
          Imp.walk(g, tab, a2, t,
            Imp.walk.push(I.Uni.recent(FAcc.uni(a2),
              Nat.sub(I.Uni.size(FAcc.uni(a2)), n0)), back))
        case Nil{}:
          match back:
            case Nil{}:
              a
            case Con{b, bt}:
              Imp.walk(g, tab, a,
                List.reverse(&2, O.Oid, Con{b, bt}), Nil{})

# ---------------------------------------------------------------------------
# Phases 1 and 2, the only part that touches Git.
# ---------------------------------------------------------------------------

def Imp.chunk() -> Nat:
  2048n

def Imp.nonblob(infos: List<&2, Pa.Info>) -> List<&2, O.Oid>:
  Imp.wanted(infos)

type Load is Data:
  Ld{tab: T.Trie<ObjBucket>, ok: Bool, err: String}

# Phase 2: attach the children a body names. The entry is replaced rather
# than mutated, and the newest entry wins because `Tab.find` scans from the
# front of the bucket -- so the *size* learned in phase 1 has to be carried
# across, or a body would silently erase it.
def Tab.of_recs(+f: O.Fmt, recs: List<&2, Pa.Rec>,
  t: T.Trie<ObjBucket>, ok: Bool) -> Load:
  match recs:
    case Nil{}:
      Ld{t, ok, ""}
    case Con{r, rest}:
      +rr = r
      +ks = Pa.Parse.children(f, Pa.Rec.kind(rr), Pa.Rec.body(rr))
      +tt = t
      Tab.of_recs(f, rest,
        Tab.put(tt, Ob{Pa.Rec.oid(rr), Pa.GType.code(Pa.Rec.kind(rr)),
          Tab.size_of(Tab.find(tt, Pa.Rec.oid(rr))),
          Pa.Kids.items(ks)}),
        Bool.and(ok, Pa.Kids.ok(ks)))

# ---------------------------------------------------------------------------
# Phase 3: the walk. Pure -- no Git call happens from here on.
#
# A queue of object ids, interned on first mention. Each object contributes
# one metadata entry and one adjacency row, in ordinal order, because the
# queue hands them out in exactly the order interning did. An object the
# table does not describe is collected into `bad`, which the caller turns
# into `IncompleteGraph`: a missing object is never a vertex with no
# successors (SPEC 3.2). A gitlink is recorded as an external reference and
# not traversed (SPEC 8.2).
# ---------------------------------------------------------------------------

def Load.tab(+l: Load) -> T.Trie<ObjBucket>:
  match l:
    case Ld{tab, ok, err}:
      tab

def Load.ok(+l: Load) -> Bool:
  match l:
    case Ld{tab, ok, err}:
      ok

def Load.err(+l: Load) -> String:
  match l:
    case Ld{tab, ok, err}:
      err

def Imp.bodies.merge(+l: Load, +r: Load) -> Load:
  Ld{Load.tab(r), Bool.and(Load.ok(l), Load.ok(r)), Load.err(l)}

def Imp.bodies.parsed(+f: O.Fmt, +l: Load, rs: Pa.Recs) -> Load:
  match rs:
    case Pa.Recs{items, rok}:
      match rok:
        case False{}:
          Ld{Load.tab(l), False{},
            "InvalidInput: malformed cat-file --batch stream"}
        case True{}:
          Imp.bodies.merge(l,
            Tab.of_recs(f, items, Load.tab(l), True{}))

def Imp.bodies.add(+f: O.Fmt, +l: Load, out: Gi.Out, ran: Bool) -> Load:
  match ran:
    case False{}:
      Ld{Load.tab(l), False{},
        "UnsupportedRepository: git cat-file --batch failed: "
          ++ Gi.Out.err(out)}
    case True{}:
      Imp.bodies.parsed(f, l, Pa.Parse.recs(f, Gi.Out.body(out)))

def Imp.bodies(+fuel: Nat, +repo: String, +f: O.Fmt, l: Load,
  oids: List<&2, O.Oid>) -> IO(Load):
  match fuel:
    case 0n:
      IO.pure(Load, Ld{Load.tab(l), False{},
        "ResourceLimit: too many body chunks"})
    case 1n+g:
      match oids:
        case Nil{}:
          IO.pure(Load, l)
        case Con{o, t}:
          +q = {Con{o, t} : List<&2, O.Oid>}
          do IO<Load>:
            out : Gi.Out <- Gi.Git.batch(repo,
              Imp.hex_lines(f, List.take(&2, O.Oid, q, Imp.chunk())),
              Imp.batch_bytes())
            +o2 : Gi.Out = out
            Imp.bodies(g, repo, f,
              Imp.bodies.add(f, l, o2, U32.is_zero(Gi.Out.status(o2))),
              List.drop(&2, O.Oid, q, Imp.chunk()))

# The whole import: one `--batch-check --batch-all-objects` call, the body
# chunks, then the pure walk.
def Imp.all.parsed(+repo: String, +f: O.Fmt, inf: Pa.Infos, ok: Bool) ->
  IO(Load):
  match ok:
    case False{}:
      IO.pure(Load, Ld{T.Trie.gap(ObjBucket), False{},
        "InvalidInput: malformed cat-file --batch-check stream"})
    case True{}:
      +items = Pa.Infos.items(inf)
      Imp.bodies(1n+List.length(&2, Pa.Info, items), repo, f,
        Ld{Tab.of_infos(items, T.Trie.gap(ObjBucket)), True{}, ""},
        Imp.nonblob(items))

def Imp.all.checked(+repo: String, +f: O.Fmt, out: Gi.Out, ran: Bool) ->
  IO(Load):
  match ran:
    case False{}:
      IO.pure(Load, Ld{T.Trie.gap(ObjBucket), False{},
        "UnsupportedRepository: git cat-file --batch-all-objects failed: "
          ++ Gi.Out.err(out)})
    case True{}:
      +inf = Pa.Parse.infos(f, Gi.Out.body(out))
      Imp.all.parsed(repo, f, inf, Pa.Infos.ok(inf))

# 256 MiB of `--batch-check --batch-all-objects` output: about four million
# objects at ~60 bytes an entry. Past that the call fails rather than
# truncating, and the caller reports ResourceLimit.
def Imp.all_bytes() -> U32:
  268435456

def Imp.all(+repo: String, +f: O.Fmt) -> IO(Load):
  do IO<Load>:
    out : Gi.Out <- Gi.Git.all_objects(repo, Imp.all_bytes())
    +o2 : Gi.Out = out
    Imp.all.checked(repo, f, o2, U32.is_zero(Gi.Out.status(o2)))

# Every object in the store, doubled -- the walk visits each reachable one
# once and can never see more than the store holds.
def Imp.walk_fuel(+t: T.Trie<ObjBucket>) -> Nat:
  4194304n

def Imp.loop.walk(+l: Load, u: I.Universe, queue: List<&2, O.Oid>,
  ok: Bool) -> FAcc:
  match ok:
    case False{}:
      FA{u, Nil{}, Nil{}, Nil{}, Nil{}, False{}, Load.err(l)}
    case True{}:
      Imp.walk(Imp.walk_fuel(Load.tab(l)), Load.tab(l),
        FA{u, Nil{}, Nil{}, Nil{}, Nil{}, True{}, ""}, queue, Nil{})

def Imp.loop(+fuel: Nat, +repo: String, +f: O.Fmt, +a: FAcc,
  queue: List<&2, O.Oid>) -> IO(FAcc):
  +q = queue
  +u = FAcc.uni(a)
  do IO<FAcc>:
    l : Load <- Imp.all(repo, f)
    +l2 : Load = l
    return Imp.loop.walk(l2, u, q, Load.ok(l2))
