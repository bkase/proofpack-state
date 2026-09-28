# index/store.bend -- the derived store.
#
# SPEC 1.1's whole point: import Git metadata once, then answer repeated
# repository-state questions. This is the "once".
#
# A generation is one file. It holds everything a query needs and nothing it
# does not: the object format, the resolved root vector, and for each ordinal
# in order its object id, its logical payload size, its type and its
# successors under the `full` policy. The `tree-data` graph is *derived* on
# load rather than stored, because it is a function of the full graph and the
# recorded types (see index/source.bend); the interning table is rebuilt by
# reading the object ids back in ordinal order, which reproduces exactly the
# ordinals that were written.
#
# The format is line-oriented ASCII on purpose. SPEC 6.5 requires structural
# validation on load and says plainly that a checksum is not a substitute, so
# the format that gets validated should also be the one a person can read
# when something goes wrong.
#
# Publishing is SPEC 6.5's atomic publish: write to a temporary name, then
# rename. A crash or a cancellation leaves the previous generation intact and
# never publishes a half-built one. v0.1 is single-writer and does not lock;
# two concurrent imports of the same name race, and the loser's generation is
# simply replaced rather than corrupted.

import Base
import ../core/count.bend as C
import ../core/trie.bend as T
import ../adapters/git/bytes.bend as B
import ../adapters/git/oid.bend as O
import ../adapters/git/intern.bend as I
import ../adapters/git/import.bend as Im
import ../closure/graph.bend as G
import ./source.bend as Idx

def Store.magic() -> String:
  "proofpack-state-store v1"

def Store.max_bytes() -> U32:
  1073741824

# ---------------------------------------------------------------------------
# Encoding.
# ---------------------------------------------------------------------------

def Store.ords(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      " " ++ U32.show(x) ++ Store.ords(t)

def Store.oids(+f: O.Fmt, os: List<&2, O.Oid>) -> String:
  match os:
    case Nil{}:
      ""
    case Con{o, t}:
      "external " ++ O.Oid.show(f, o) ++ "\n" ++ Store.oids(f, t)

def Store.object(+f: O.Fmt, o: O.Oid, m: Im.Meta, r: Im.Row) -> String:
  +mm = m
  +rr = Im.Row.succ(r)
  "object " ++ O.Oid.show(f, o) ++ " " ++ U32.show(Im.Meta.size(mm))
    ++ " " ++ U32.show(Im.Meta.kind(mm)) ++ " "
    ++ Nat.show(List.length(&2, U32, rr)) ++ Store.ords(rr) ++ "\n"

def Store.objects(+f: O.Fmt, os: List<&2, O.Oid>, ms: List<&2, Im.Meta>,
  rs: List<&2, Im.Row>) -> String:
  match os:
    case Nil{}:
      ""
    case Con{o, ot}:
      match ms:
        case Nil{}:
          ""
        case Con{m, mt}:
          match rs:
            case Nil{}:
              ""
            case Con{r, rt}:
              Store.object(f, o, m, r)
                ++ Store.objects(f, ot, mt, rt)

def Store.encode(+src: Idx.Source, ms: List<&2, Im.Meta>,
  rs: List<&2, Im.Row>) -> String:
  +f = Idx.Source.fmt(src)
  Store.magic() ++ "\n"
    ++ "format " ++ O.Fmt.name(f) ++ "\n"
    ++ "objects " ++ Nat.show(Idx.Source.n(src)) ++ "\n"
    ++ "roots" ++ Store.ords(Idx.Source.roots(src)) ++ "\n"
    ++ Store.oids(f, Idx.Source.ext(src))
    ++ Store.objects(f, I.Uni.identify(Idx.Source.uni(src)), ms, rs)

# ---------------------------------------------------------------------------
# Decoding. Every field is validated: the magic line, the object format, the
# declared count against the objects actually present, each object id being
# exactly the format's width of hex, each successor being below the declared
# count. A file is untrusted input (SPEC 6.5).
# ---------------------------------------------------------------------------

type Dec is Data:
  D{uni: I.Universe, metas: List<&2, Im.Meta>, rows: List<&2, Im.Row>,
    ext: List<&2, O.Oid>, roots: List<&2, U32>, n: Nat, seen: Nat,
    ok: Bool, err: String}

def Dec.fail(d: Dec, msg: String) -> Dec:
  match d:
    case D{uni, metas, rows, ext, roots, n, seen, ok, err}:
      D{uni, metas, rows, ext, roots, n, seen, False{}, msg}

def Dec.ok(+d: Dec) -> Bool:
  match d:
    case D{uni, metas, rows, ext, roots, n, seen, ok, err}:
      ok

def Dec.err(+d: Dec) -> String:
  match d:
    case D{uni, metas, rows, ext, roots, n, seen, ok, err}:
      err

def Dec.n(+d: Dec) -> Nat:
  match d:
    case D{uni, metas, rows, ext, roots, n, seen, ok, err}:
      n

def Dec.seen(+d: Dec) -> Nat:
  match d:
    case D{uni, metas, rows, ext, roots, n, seen, ok, err}:
      seen

def Dec.uni(+d: Dec) -> I.Universe:
  match d:
    case D{uni, metas, rows, ext, roots, n, seen, ok, err}:
      uni

def Dec.metas(+d: Dec) -> List<&2, Im.Meta>:
  match d:
    case D{uni, metas, rows, ext, roots, n, seen, ok, err}:
      List.reverse(&2, Im.Meta, metas)

def Dec.rows(+d: Dec) -> List<&2, Im.Row>:
  match d:
    case D{uni, metas, rows, ext, roots, n, seen, ok, err}:
      List.reverse(&2, Im.Row, rows)

def Dec.ext(+d: Dec) -> List<&2, O.Oid>:
  match d:
    case D{uni, metas, rows, ext, roots, n, seen, ok, err}:
      ext

def Dec.roots(+d: Dec) -> List<&2, U32>:
  match d:
    case D{uni, metas, rows, ext, roots, n, seen, ok, err}:
      roots

# --- reading the pieces of one line ---------------------------------------

# A tuple is a `Sigma`, which is affine, so a parsed run of ordinals comes
# back in a Data record that can be read more than once.
type Ords is Data:
  Os{xs: List<&2, U32>, ok: Bool}

def Store.tok(+bs: B.Bytes) -> B.Bytes:
  B.Cut.taken(B.Bytes.word(bs))

def Store.rest(+bs: B.Bytes) -> B.Bytes:
  B.Cut.rest(B.Bytes.word(bs))

def Store.num.un(r: Nat & Bool) -> Nat:
  match r:
    case Tuple{n, ok}:
      n

def Store.num(+bs: B.Bytes) -> Nat:
  Store.num.un(B.Bytes.number(bs))

def Store.num_ok.un(r: Nat & Bool) -> Bool:
  match r:
    case Tuple{n, ok}:
      ok

def Store.num_ok(+bs: B.Bytes) -> Bool:
  Store.num_ok.un(B.Bytes.number(bs))

# A whitespace-separated run of decimal ordinals, each checked against the
# declared object count -- a successor pointing outside the universe is a
# corrupt index, not a set with an extra member.
def Store.succ(+fuel: Nat, +bs: B.Bytes, +n: Nat, acc: List<&2, U32>,
  ok: Bool, tok: B.Bytes, rest: B.Bytes) -> Ords:
  match fuel:
    case 0n:
      Os{List.reverse(&2, U32, acc), False{}}
    case 1n+g:
      match bs:
        case Nil{}:
          Os{List.reverse(&2, U32, acc), ok}
        case Con{b, t}:
          # A leading or doubled space yields an empty token; skip it rather
          # than reading it as a malformed ordinal.
          match tok:
            case Nil{}:
              +r = rest
              Store.succ(g, r, n, acc, ok, Store.tok(r), Store.rest(r))
            case Con{tb, tt}:
              +tk = {Con{tb, tt} : B.Bytes}
              +v = Store.num(tk)
              +r = rest
              Store.succ(g, r, n, Con{U32.from_nat(v), acc},
                Bool.and(ok, Bool.and(Store.num_ok(tk), C.Nat.gt(n, v))),
                Store.tok(r), Store.rest(r))

def Store.ords_of(+bs: B.Bytes, +n: Nat) -> Ords:
  Store.succ(1n+List.length(&2, U32, bs), bs, n, Nil{}, True{},
    Store.tok(bs), Store.rest(bs))

def Store.ok_pair(+r: Ords) -> Bool:
  match r:
    case Os{xs, ok}:
      ok

def Store.list_pair(+r: Ords) -> List<&2, U32>:
  match r:
    case Os{xs, ok}:
      xs

# --- one `object` line -----------------------------------------------------

def Store.obj.put(i: I.Interned, metas: List<&2, Im.Meta>,
  rows: List<&2, Im.Row>, ext: List<&2, O.Oid>, roots: List<&2, U32>,
  +n: Nat, +seen: Nat, ok: Bool, err: String, +size: Nat, +kind: Nat,
  succ: List<&2, U32>) -> Dec:
  match i:
    case I.In{uni, ord}:
      D{uni, Con{Im.Meta{U32.from_nat(size), U32.from_nat(kind)}, metas},
        Con{Im.Row{succ}, rows}, ext, roots, n, 1n+seen,
        Bool.and(ok, Nat.is_eq(U32.to_nat(ord), seen)), err}

def Store.obj.add(+d: Dec, +o: O.Oid, +size: Nat, +kind: Nat,
  succ: List<&2, U32>, ok: Bool) -> Dec:
  match d:
    case D{uni, metas, rows, ext, roots, n, seen, dok, err}:
      Store.obj.put(I.Uni.intern(uni, o), metas, rows, ext, roots, n, seen,
        Bool.and(dok, ok), err, size, kind, succ)

def Store.obj.succ(+d: Dec, +oid: O.Oid, +size: Nat, +kind: Nat,
  +count: Nat, ok3: Bool, +rest: B.Bytes, +n: Nat) -> Dec:
  +r = Store.ords_of(rest, n)
  Store.obj.add(d, oid, size, kind, Store.list_pair(r),
    Bool.and(ok3, Bool.and(Store.ok_pair(r),
      Nat.is_eq(List.length(&2, U32, Store.list_pair(r)), count))))

def Store.obj.count(+d: Dec, +oid: O.Oid, +size: Nat, +kind: Nat,
  ok2: Bool, +c3: B.Cut) -> Dec:
  Store.obj.succ(d, oid, size, kind,
    Store.num(B.Cut.taken(c3)),
    Bool.and(ok2, Store.num_ok(B.Cut.taken(c3))),
    B.Cut.rest(c3), Dec.n(d))

def Store.obj.kind(+d: Dec, +oid: O.Oid, +size: Nat, ok1: Bool,
  +c2: B.Cut) -> Dec:
  Store.obj.count(d, oid, size, Store.num(B.Cut.taken(c2)),
    Bool.and(ok1, Store.num_ok(B.Cut.taken(c2))),
    B.Bytes.word(B.Cut.rest(c2)))

def Store.obj.fields(+d: Dec, +oid: O.Oid, +c1: B.Cut) -> Dec:
  Store.obj.kind(d, oid, Store.num(B.Cut.taken(c1)),
    Store.num_ok(B.Cut.taken(c1)), B.Bytes.word(B.Cut.rest(c1)))

def Store.obj.read(+d: Dec, +f: O.Fmt, +rest: B.Bytes, r: O.OidRead) ->
  Dec:
  match r:
    case O.Read{oid, ok}:
      match ok:
        case False{}:
          Dec.fail(d, "CorruptIndex: an object id is not "
            ++ Nat.show(O.Fmt.hex_len(f)) ++ " hex characters")
        case True{}:
          Store.obj.fields(d, oid, B.Bytes.word(rest))

# ---------------------------------------------------------------------------
# The line loop. One `Step` constructor per recognised line, so the loop is a
# single self-recursive def (Bend forbids mutual recursion) and an
# unrecognised line is an explicit `CorruptIndex` rather than a skipped one.
# ---------------------------------------------------------------------------

type Line is Data:
  LEnd{}
  LSkip{rest: B.Bytes}
  LFormat{name: B.Bytes, rest: B.Bytes}
  LCount{n: Nat, ok: Bool, rest: B.Bytes}
  LRoots{body: B.Bytes, rest: B.Bytes}
  LExternal{hex: B.Bytes, rest: B.Bytes}
  LObject{body: B.Bytes, rest: B.Bytes}
  LBad{}

def Store.kind_of.count(+body: B.Bytes, +rest: B.Bytes) -> Line:
  LCount{Store.num(body), Store.num_ok(body), rest}

def Store.kind_of.magic(+rest: B.Bytes, ok: Bool) -> Line:
  match ok:
    case True{}:
      LSkip{rest}
    case False{}:
      LBad{}

def Store.kind_of.pick(+line: B.Bytes, +rest: B.Bytes, first: Bool,
  obj: Bool, fmt: Bool, cnt: Bool, rts: Bool, ext: Bool) -> Line:
  match first:
    case True{}:
      Store.kind_of.magic(rest,
        B.Bytes.equal(line, B.Bytes.of_string(Store.magic())))
    case False{}:
      match obj:
        case True{}:
          LObject{B.Bytes.skip(7n, line), rest}
        case False{}:
          match fmt:
            case True{}:
              LFormat{B.Bytes.skip(7n, line), rest}
            case False{}:
              match cnt:
                case True{}:
                  Store.kind_of.count(B.Bytes.skip(8n, line), rest)
                case False{}:
                  match rts:
                    case True{}:
                      LRoots{B.Bytes.skip(5n, line), rest}
                    case False{}:
                      match ext:
                        case True{}:
                          LExternal{B.Bytes.skip(9n, line), rest}
                        case False{}:
                          LBad{}

def Store.kind_of(+line: B.Bytes, +rest: B.Bytes, first: Bool) -> Line:
  Store.kind_of.pick(line, rest, first,
    B.Bytes.starts(B.Bytes.of_string("object "), line),
    B.Bytes.starts(B.Bytes.of_string("format "), line),
    B.Bytes.starts(B.Bytes.of_string("objects "), line),
    B.Bytes.starts(B.Bytes.of_string("roots"), line),
    B.Bytes.starts(B.Bytes.of_string("external "), line))

def Store.next.pick(+bs: B.Bytes, first: Bool, empty: Bool) -> Line:
  match empty:
    case True{}:
      LEnd{}
    case False{}:
      +c = B.Bytes.line(bs)
      Store.kind_of(B.Cut.taken(c), B.Cut.rest(c), first)

def Store.next(+bs: B.Bytes, first: Bool) -> Line:
  Store.next.pick(bs, first, List.is_empty(&2, U32, bs))

def Store.fmt_of.pick(two: Bool) -> O.Fmt:
  match two:
    case True{}:
      O.Sha256{}
    case False{}:
      O.Sha1{}

def Store.fmt_of(+name: B.Bytes) -> O.Fmt:
  Store.fmt_of.pick(B.Bytes.equal(name, B.Bytes.of_string("sha256")))

def Store.set_n(+d: Dec, +n: Nat, ok: Bool) -> Dec:
  match d:
    case D{uni, metas, rows, ext, roots, on, seen, dok, err}:
      D{uni, metas, rows, ext, roots, n, seen, Bool.and(dok, ok), err}

def Store.set_roots(+d: Dec, +rs: Ords) -> Dec:
  match d:
    case D{uni, metas, rows, ext, roots, n, seen, dok, err}:
      D{uni, metas, rows, ext, Store.list_pair(rs), n, seen,
        Bool.and(dok, Store.ok_pair(rs)), err}

def Store.add_ext.go(+d: Dec, +oid: O.Oid, ok: Bool) -> Dec:
  match d:
    case D{uni, metas, rows, ext, roots, n, seen, dok, err}:
      D{uni, metas, rows, Con{oid, ext}, roots, n, seen,
        Bool.and(dok, ok), err}

def Store.add_ext(+d: Dec, r: O.OidRead) -> Dec:
  match r:
    case O.Read{oid, ok}:
      Store.add_ext.go(d, oid, ok)

def Store.decode.go(+fuel: Nat, +f: O.Fmt, +d: Dec, ln: Line) -> Dec:
  match fuel:
    case 0n:
      Dec.fail(d, "ResourceLimit: the store file has too many lines")
    case 1n+g:
      match ln:
        case LEnd{}:
          d
        case LBad{}:
          Dec.fail(d, "CorruptIndex: unrecognised line in the store file")
        case LSkip{rest}:
          +r = rest
          Store.decode.go(g, f, d, Store.next(r, False{}))
        case LFormat{name, rest}:
          +r = rest
          Store.decode.go(g, Store.fmt_of(name), d,
            Store.next(r, False{}))
        case LCount{n, ok, rest}:
          +r = rest
          Store.decode.go(g, f, Store.set_n(d, n, ok),
            Store.next(r, False{}))
        case LRoots{body, rest}:
          +r = rest
          Store.decode.go(g, f,
            Store.set_roots(d, Store.ords_of(body, Dec.n(d))),
            Store.next(r, False{}))
        case LExternal{hex, rest}:
          +r = rest
          Store.decode.go(g, f, Store.add_ext(d, O.Oid.of_hex(f, hex)),
            Store.next(r, False{}))
        case LObject{body, rest}:
          +r = rest
          +b = body
          Store.decode.go(g, f,
            Store.obj.read(d, f, B.Bytes.skip(1n,
              B.Bytes.skip(O.Fmt.hex_len(f), b)), O.Oid.of_hex(f, b)),
            Store.next(r, False{}))

def Store.decode.count(+d: Dec, ok: Bool) -> Dec:
  match ok:
    case True{}:
      d
    case False{}:
      Dec.fail(d, "CorruptIndex: the declared object count does not match "
        ++ "the objects in the file")

def Store.decode.named.go(+d: Dec, unnamed: Bool) -> Dec:
  match unnamed:
    case False{}:
      d
    case True{}:
      Dec.fail(d, "CorruptIndex: a field in the store file failed "
        ++ "validation -- an object id, a size, a type code, a successor "
        ++ "count, or a successor outside the declared universe")

# A field-level check that failed sets `ok` without a message, because it is
# one `Bool.and` deep inside a fold. Give it one here rather than reporting an
# empty error class: SPEC 9.3 asks for stable machine-readable codes.
def Store.decode.named(+d: Dec) -> Dec:
  Store.decode.named.go(d, Bool.and(Bool.not(Dec.ok(d)),
    String.is_empty(Dec.err(d))))

# The declared object count must match the objects actually present. A file
# that says 4000 and holds 3999 is a corrupt index, not a smaller universe.
def Store.decode.fin(+d: Dec) -> Dec:
  Store.decode.named(Store.decode.count(d,
    Nat.is_eq(Dec.n(d), Dec.seen(d))))

def Store.decode(+bs: B.Bytes) -> Dec:
  Store.decode.fin(Store.decode.go(1n+List.length(&2, U32, bs),
    O.Sha1{}, D{I.Uni.new(O.Sha1{}), Nil{}, Nil{}, Nil{}, Nil{}, 0n, 0n,
      True{}, ""}, Store.next(bs, True{})))

# ---------------------------------------------------------------------------
# Files. Reading, writing, and the atomic publish of SPEC 6.5.
# ---------------------------------------------------------------------------

def Store.path(store: String, name: String) -> String:
  store ++ "/" ++ name ++ ".pps"

def Store.temp(store: String, name: String) -> String:
  store ++ "/" ++ name ++ ".pps.new"

def Store.load.at(m: Maybe<&2, O.Oid>) -> O.Oid:
  match m:
    case None{}:
      O.Oid.zero()
    case Some{o}:
      o

def Store.load.pick(+ids: List<&2, O.Oid>, rs: List<&2, U32>) ->
  List<&2, O.Oid>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{Store.load.at(List.get(&2, O.Oid, ids, U32.to_nat(r))),
        Store.load.pick(ids, t)}

def Store.load.root_oids(+u: I.Universe, rs: List<&2, U32>) ->
  List<&2, O.Oid>:
  Store.load.pick(I.Uni.identify(u), rs)

def Store.load.check(+d: Dec, ok: Bool) -> Idx.Built:
  match ok:
    case False{}:
      Idx.BErr{Dec.err(d)}
    case True{}:
      Idx.Idx.assemble(I.Uni.fmt(Dec.uni(d)),
        Im.FA{Dec.uni(d), List.reverse(&2, Im.Row, Dec.rows(d)),
          List.reverse(&2, Im.Meta, Dec.metas(d)), Dec.ext(d), Nil{},
          True{}, ""},
        Dec.roots(d),
        Store.load.root_oids(Dec.uni(d), Dec.roots(d)))

def Store.load.decoded(+d: Dec) -> Idx.Built:
  Store.load.check(d, Dec.ok(d))

def Store.read.un(r: Result<&1, &1, U32 & String, List<&2, U32>>) ->
  Idx.Built:
  match r:
    case Fail{e}:
      Idx.BErr{"CorruptIndex: the store file could not be read"}
    case Done{bs}:
      Store.load.decoded(Store.decode(bs))

def Store.read.body(fr: File & Result<&1, &1, U32 & String,
  List<&2, U32>>) -> IO(Idx.Built):
  match fr:
    case Tuple{file, r}:
      do IO<Idx.Built>:
        File.close(file)
        return Store.read.un(r)

def Store.read.opened(r: Result<&1, &1, U32 & String, File>) ->
  IO(Idx.Built):
  match r:
    case Fail{e}:
      IO.pure(Idx.Built,
        Idx.BErr{"UnknownRoot: no such graph snapshot in the store"})
    case Done{file}:
      do IO<Idx.Built>:
        fr : File & Result<&1, &1, U32 & String, List<&2, U32>> <-
          File.read_bytes(file, Store.max_bytes())
        Store.read.body(fr)

def Store.load(store: String, name: String) -> IO(Idx.Built):
  do IO<Idx.Built>:
    r : Result<&1, &1, U32 & String, File> <-
      File.open(Store.path(store, name), "r")
    Store.read.opened(r)

# --- writing ---------------------------------------------------------------

def Store.write.un(r: Result<&1, &1, U32 & String, Unit>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{u}:
      True{}

def Store.write.done(fr: File & Result<&1, &1, U32 & String, Unit>) ->
  IO(Bool):
  match fr:
    case Tuple{file, r}:
      do IO<Bool>:
        File.close(file)
        return Store.write.un(r)

def Store.write.opened(text: String,
  r: Result<&1, &1, U32 & String, File>) -> IO(Bool):
  match r:
    case Fail{e}:
      IO.pure(Bool, False{})
    case Done{file}:
      do IO<Bool>:
        fr : File & Result<&1, &1, U32 & String, Unit> <-
          File.write(file, text)
        Store.write.done(fr)

# Write to a temporary name and rename it into place. A crash or a
# cancellation leaves the previous generation intact; readers never see a
# half-built one (SPEC 6.5).
