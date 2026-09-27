# adapters/git/parse.bend -- the Git metadata grammar (law G-01).
#
# The parser contract is soundness and completeness for the *declared*
# metadata grammar, with explicit limits. It is not a claim to implement every
# `git fsck` check (SPEC 8.4). What is declared here:
#
#   batch-check line  <hex-oid> SP <type> SP <size> LF
#                   | <hex-oid> SP "missing" LF
#   batch record      <hex-oid> SP <type> SP <size> LF <size bytes> LF
#                   | <hex-oid> SP "missing" LF
#   commit body       ("tree" SP <hex> | "parent" SP <hex>) LF ... then a
#                     header this parser stops at and never reads past
#   tag body          ("object" SP <hex> | "type" SP <name>) LF ... likewise
#   tree body         (<octal mode> SP <name> NUL <raw oid>)*
#
# Bodies are read by declared length, never by line-scanning the stream
# (SPEC 8.3): a record whose size overruns the buffer, or whose object id is
# not exactly the format's width of hex, is rejected rather than read short.
#
# Every loop carries an explicit `fuel` because the remainder of a parse is a
# computed value, not a structural sub-term, and Bend's termination check
# wants something that provably shrinks. The fuel is the input length, so it
# is always enough and never truncates a well-formed input.

import Base
import ../../core/count.bend as C
import ./bytes.bend as B
import ./oid.bend as O

# ---------------------------------------------------------------------------
# Object types.
# ---------------------------------------------------------------------------

type GType is Data:
  TCommit{}
  TTree{}
  TBlob{}
  TTag{}
  TMissing{}
  TBad{}

def GType.of_bytes.pick(c: Bool, t: Bool, b: Bool, g: Bool, m: Bool) ->
  GType:
  match c:
    case True{}:
      TCommit{}
    case False{}:
      match t:
        case True{}:
          TTree{}
        case False{}:
          match b:
            case True{}:
              TBlob{}
            case False{}:
              match g:
                case True{}:
                  TTag{}
                case False{}:
                  match m:
                    case True{}:
                      TMissing{}
                    case False{}:
                      TBad{}

def GType.of_bytes(+bs: B.Bytes) -> GType:
  GType.of_bytes.pick(B.Bytes.equal(bs, B.Bytes.of_string("commit")),
    B.Bytes.equal(bs, B.Bytes.of_string("tree")),
    B.Bytes.equal(bs, B.Bytes.of_string("blob")),
    B.Bytes.equal(bs, B.Bytes.of_string("tag")),
    B.Bytes.equal(bs, B.Bytes.of_string("missing")))

def GType.code(k: GType) -> U32:
  match k:
    case TCommit{}:
      0
    case TTree{}:
      1
    case TBlob{}:
      2
    case TTag{}:
      3
    case TMissing{}:
      4
    case TBad{}:
      5

def GType.of_code.pick(n: Nat) -> GType:
  match n:
    case 0n:
      TCommit{}
    case 1n+a:
      match a:
        case 0n:
          TTree{}
        case 1n+b:
          match b:
            case 0n:
              TBlob{}
            case 1n+c:
              match c:
                case 0n:
                  TTag{}
                case 1n+d:
                  match d:
                    case 0n:
                      TMissing{}
                    case 1n+e:
                      TBad{}

def GType.of_code(+c: U32) -> GType:
  GType.of_code.pick(U32.to_nat(c))

def GType.name(k: GType) -> String:
  match k:
    case TCommit{}:
      "commit"
    case TTree{}:
      "tree"
    case TBlob{}:
      "blob"
    case TTag{}:
      "tag"
    case TMissing{}:
      "missing"
    case TBad{}:
      "invalid"

def GType.is_commit(k: GType) -> Bool:
  match k:
    case TCommit{}:
      True{}
    case TTree{}:
      False{}
    case TBlob{}:
      False{}
    case TTag{}:
      False{}
    case TMissing{}:
      False{}
    case TBad{}:
      False{}

def GType.is_missing(k: GType) -> Bool:
  match k:
    case TMissing{}:
      True{}
    case TCommit{}:
      False{}
    case TTree{}:
      False{}
    case TBlob{}:
      False{}
    case TTag{}:
      False{}
    case TBad{}:
      True{}

# ---------------------------------------------------------------------------
# One header line: <hex-oid> SP <type> [SP <size>].
# ---------------------------------------------------------------------------

type Info is Data:
  Info{oid: O.Oid, kind: GType, size: Nat}

def Info.oid(i: Info) -> O.Oid:
  match i:
    case Info{oid, kind, size}:
      oid

def Info.kind(i: Info) -> GType:
  match i:
    case Info{oid, kind, size}:
      kind

def Info.size(i: Info) -> Nat:
  match i:
    case Info{oid, kind, size}:
      size

def Parse.info.only_kind(oid: O.Oid, k: GType) -> Maybe<&2, Info>:
  match k:
    case TMissing{}:
      Some{Info{oid, TMissing{}, 0n}}
    case TBad{}:
      None{}
    case TCommit{}:
      None{}
    case TTree{}:
      None{}
    case TBlob{}:
      None{}
    case TTag{}:
      None{}

def Parse.info.size(oid: O.Oid, k: GType, ns: Nat & Bool) ->
  Maybe<&2, Info>:
  match ns:
    case Tuple{n, ok}:
      match ok:
        case False{}:
          None{}
        case True{}:
          Some{Info{oid, k, n}}

def Parse.info.kind(oid: O.Oid, c: B.Cut) -> Maybe<&2, Info>:
  match c:
    case B.Cut{taken, rest, ok}:
      match ok:
        case False{}:
          Parse.info.only_kind(oid, GType.of_bytes(taken))
        case True{}:
          Parse.info.size(oid, GType.of_bytes(taken), B.Bytes.number(rest))

def Parse.info.after_oid(+f: O.Fmt, r: O.OidRead, +rest: B.Bytes) ->
  Maybe<&2, Info>:
  match r:
    case O.Read{oid, ok}:
      match ok:
        case False{}:
          None{}
        case True{}:
          Parse.info.kind(oid, B.Bytes.word(rest))

# `line` is one batch-check line, with the terminating LF already removed.
def Parse.info.line(+f: O.Fmt, +line: B.Bytes) -> Maybe<&2, Info>:
  Parse.info.after_oid(f, O.Oid.of_hex(f, line),
    B.Bytes.skip(1n, B.Bytes.skip(O.Fmt.hex_len(f), line)))

def Parse.info.head(+f: O.Fmt, +bs: B.Bytes) -> Maybe<&2, Info>:
  Parse.info.line(f, B.Cut.taken(B.Bytes.line(bs)))

# ---------------------------------------------------------------------------
# Every line of a `git cat-file --batch-check` run.
# ---------------------------------------------------------------------------

type Infos is Data:
  Infos{items: List<&2, Info>, ok: Bool}

def Infos.items(i: Infos) -> List<&2, Info>:
  match i:
    case Infos{items, ok}:
      items

def Infos.ok(i: Infos) -> Bool:
  match i:
    case Infos{items, ok}:
      ok

def Parse.infos.go(+fuel: Nat, +f: O.Fmt, +bs: B.Bytes, acc: List<&2, Info>,
  m: Maybe<&2, Info>) -> Infos:
  match fuel:
    case 0n:
      Infos{List.reverse(&2, Info, acc), False{}}
    case 1n+g:
      match bs:
        case Nil{}:
          Infos{List.reverse(&2, Info, acc), True{}}
        case Con{b, t}:
          match m:
            case None{}:
              Infos{List.reverse(&2, Info, acc), False{}}
            case Some{i}:
              +rest = B.Cut.rest(B.Bytes.line(bs))
              Parse.infos.go(g, f, rest, Con{i, acc},
                Parse.info.head(f, rest))

def Parse.infos(+f: O.Fmt, +bs: B.Bytes) -> Infos:
  Parse.infos.go(1n+List.length(&2, U32, bs), f, bs, Nil{},
    Parse.info.head(f, bs))

# ---------------------------------------------------------------------------
# Every record of a `git cat-file --batch` run. The body is taken by its
# declared length.
# ---------------------------------------------------------------------------

type Rec is Data:
  Rec{oid: O.Oid, kind: GType, body: B.Bytes}

type Recs is Data:
  Recs{items: List<&2, Rec>, ok: Bool}

def Recs.items(r: Recs) -> List<&2, Rec>:
  match r:
    case Recs{items, ok}:
      items

def Recs.ok(r: Recs) -> Bool:
  match r:
    case Recs{items, ok}:
      ok

def Rec.oid(r: Rec) -> O.Oid:
  match r:
    case Rec{oid, kind, body}:
      oid

def Rec.kind(r: Rec) -> GType:
  match r:
    case Rec{oid, kind, body}:
      kind

def Rec.body(r: Rec) -> B.Bytes:
  match r:
    case Rec{oid, kind, body}:
      body

# One record, as a value. `Step` exists so the loop below can be a single
# self-recursive def: Bend forbids mutual recursion, and every branch here is
# on a computed value, which a `match` cannot scrutinize.
type Step is Data:
  SDone{}
  SBad{}
  SRec{rec: Rec, rest: B.Bytes}

def Parse.recs.step.take(oid: O.Oid, k: GType, c: B.Cut) -> Step:
  match c:
    case B.Cut{taken, rest, ok}:
      match ok:
        case False{}:
          SBad{}
        case True{}:
          SRec{Rec{oid, k, taken}, B.Bytes.skip(1n, rest)}

# A missing object has no body and no trailing LF; a present one has both.
def Parse.recs.step.body(oid: O.Oid, k: GType, c: B.Cut, missing: Bool,
  +after: B.Bytes) -> Step:
  match missing:
    case True{}:
      SRec{Rec{oid, k, Nil{}}, after}
    case False{}:
      Parse.recs.step.take(oid, k, c)

def Parse.recs.step.hdr(+after: B.Bytes, +m: Maybe<&2, Info>) -> Step:
  match m:
    case None{}:
      SBad{}
    case Some{i}:
      Parse.recs.step.body(Info.oid(i), Info.kind(i),
        B.Bytes.split(Info.size(i), after),
        GType.is_missing(Info.kind(i)), after)

def Parse.recs.step.pick(+f: O.Fmt, +bs: B.Bytes, empty: Bool) -> Step:
  match empty:
    case True{}:
      SDone{}
    case False{}:
      Parse.recs.step.hdr(B.Cut.rest(B.Bytes.line(bs)),
        Parse.info.head(f, bs))

def Parse.recs.step(+f: O.Fmt, +bs: B.Bytes) -> Step:
  Parse.recs.step.pick(f, bs, List.is_empty(&2, U32, bs))

def Parse.recs.go(+fuel: Nat, +f: O.Fmt, acc: List<&2, Rec>, s: Step) ->
  Recs:
  match fuel:
    case 0n:
      Recs{List.reverse(&2, Rec, acc), False{}}
    case 1n+g:
      match s:
        case SDone{}:
          Recs{List.reverse(&2, Rec, acc), True{}}
        case SBad{}:
          Recs{List.reverse(&2, Rec, acc), False{}}
        case SRec{r, rest}:
          +rs = rest
          Parse.recs.go(g, f, Con{r, acc}, Parse.recs.step(f, rs))

def Parse.recs(+f: O.Fmt, +bs: B.Bytes) -> Recs:
  Parse.recs.go(1n+List.length(&2, U32, bs), f, Nil{},
    Parse.recs.step(f, bs))

# ---------------------------------------------------------------------------
# Bodies: the children a commit, tag or tree names.
#
# Each body type has its own `step`, and one shared fuel-bounded loop walks
# it. `LStep` plays the same role `Step` does above: it turns a decision made
# on computed values into a constructor the loop can match.
# ---------------------------------------------------------------------------

type Child is Data:
  Kid{oid: O.Oid, gitlink: Bool, name: B.Bytes}

def Child.oid(c: Child) -> O.Oid:
  match c:
    case Kid{oid, gitlink, name}:
      oid

def Child.gitlink(c: Child) -> Bool:
  match c:
    case Kid{oid, gitlink, name}:
      gitlink

def Child.name(c: Child) -> B.Bytes:
  match c:
    case Kid{oid, gitlink, name}:
      name

type LStep is Data:
  LDone{}
  LBad{}
  LKid{kid: Child, rest: B.Bytes}

type Kids is Data:
  Kids{items: List<&2, Child>, ok: Bool}

def Kids.items(k: Kids) -> List<&2, Child>:
  match k:
    case Kids{items, ok}:
      items

def Kids.ok(k: Kids) -> Bool:
  match k:
    case Kids{items, ok}:
      ok

def Parse.kid.of(r: O.OidRead, +rest: B.Bytes, link: Bool,
  name: B.Bytes) -> LStep:
  match r:
    case O.Read{oid, ok}:
      match ok:
        case False{}:
          LBad{}
        case True{}:
          LKid{Kid{oid, link, name}, rest}

# --- commit: "tree <hex>" and "parent <hex>", in the header block ---------

def Parse.commit.arm(+f: O.Fmt, +line: B.Bytes, +rest: B.Bytes, t: Bool,
  p: Bool) -> LStep:
  match t:
    case True{}:
      Parse.kid.of(O.Oid.of_hex(f, B.Bytes.skip(5n, line)), rest, False{},
        Nil{})
    case False{}:
      match p:
        case True{}:
          Parse.kid.of(O.Oid.of_hex(f, B.Bytes.skip(7n, line)), rest,
            False{}, Nil{})
        case False{}:
          LDone{}

def Parse.commit.line(+f: O.Fmt, +line: B.Bytes, +rest: B.Bytes) -> LStep:
  Parse.commit.arm(f, line, rest,
    B.Bytes.starts(B.Bytes.of_string("tree "), line),
    B.Bytes.starts(B.Bytes.of_string("parent "), line))

def Parse.commit.pick(+f: O.Fmt, +bs: B.Bytes, empty: Bool) -> LStep:
  match empty:
    case True{}:
      LDone{}
    case False{}:
      +c = B.Bytes.line(bs)
      Parse.commit.line(f, B.Cut.taken(c), B.Cut.rest(c))

# Stops at the first header that is neither `tree` nor `parent`, so the
# message is never scanned.
def Parse.commit.step(+f: O.Fmt, +bs: B.Bytes) -> LStep:
  Parse.commit.pick(f, bs, List.is_empty(&2, U32, bs))

# --- tag: "object <hex>" -------------------------------------------------

def Parse.tag.arm(+f: O.Fmt, +line: B.Bytes, +rest: B.Bytes, o: Bool) ->
  LStep:
  match o:
    case True{}:
      Parse.kid.of(O.Oid.of_hex(f, B.Bytes.skip(7n, line)), rest, False{},
        Nil{})
    case False{}:
      LDone{}

def Parse.tag.pick(+f: O.Fmt, +bs: B.Bytes, empty: Bool) -> LStep:
  match empty:
    case True{}:
      LDone{}
    case False{}:
      +c = B.Bytes.line(bs)
      Parse.tag.arm(f, B.Cut.taken(c), B.Cut.rest(c),
        B.Bytes.starts(B.Bytes.of_string("object "),
          B.Cut.taken(B.Bytes.line(bs))))

def Parse.tag.step(+f: O.Fmt, +bs: B.Bytes) -> LStep:
  Parse.tag.pick(f, bs, List.is_empty(&2, U32, bs))

# --- tree: <octal mode> SP <name> NUL <raw oid> ---------------------------

def Parse.tree.oid(+f: O.Fmt, c: B.Cut, link: Bool, name: B.Bytes) ->
  LStep:
  match c:
    case B.Cut{taken, rest, ok}:
      match ok:
        case False{}:
          LBad{}
        case True{}:
          LKid{Kid{O.Oid.of_bytes(f, taken), link, name}, rest}

def Parse.tree.name(+f: O.Fmt, +mode: B.Bytes, +rest1: B.Bytes) -> LStep:
  +c = B.Bytes.until(0, rest1)
  Parse.tree.oid(f, B.Bytes.split(O.Fmt.bytes(f), B.Cut.rest(c)),
    B.Bytes.equal(mode, B.Bytes.of_string("160000")), B.Cut.taken(c))

def Parse.tree.pick(+f: O.Fmt, +bs: B.Bytes, empty: Bool) -> LStep:
  match empty:
    case True{}:
      LDone{}
    case False{}:
      +c = B.Bytes.until(32, bs)
      Parse.tree.name(f, B.Cut.taken(c), B.Cut.rest(c))

def Parse.tree.step(+f: O.Fmt, +bs: B.Bytes) -> LStep:
  Parse.tree.pick(f, bs, List.is_empty(&2, U32, bs))

# --- the shared loop ------------------------------------------------------

def Parse.kids.go(~step: @+f:O.Fmt -> @+bs:B.Bytes -> LStep, +fuel: Nat,
  +f: O.Fmt, acc: List<&2, Child>, s: LStep) -> Kids:
  match fuel:
    case 0n:
      Kids{List.reverse(&2, Child, acc), False{}}
    case 1n+g:
      match s:
        case LDone{}:
          Kids{List.reverse(&2, Child, acc), True{}}
        case LBad{}:
          Kids{List.reverse(&2, Child, acc), False{}}
        case LKid{k, rest}:
          +rs = rest
          Parse.kids.go(~step, g, f, Con{k, acc}, step(f, rs))

def Parse.kids(~step: @+f:O.Fmt -> @+bs:B.Bytes -> LStep, +f: O.Fmt,
  +bs: B.Bytes) -> Kids:
  Parse.kids.go(~step, 1n+List.length(&2, U32, bs), f, Nil{}, step(f, bs))

# The children a record names, by its type. A blob is terminal; a missing or
# invalid object names nothing and is reported by its own record.
def Parse.children(+f: O.Fmt, k: GType, +body: B.Bytes) -> Kids:
  match k:
    case TCommit{}:
      Parse.kids(~Parse.commit.step, f, body)
    case TTag{}:
      Parse.kids(~Parse.tag.step, f, body)
    case TTree{}:
      Parse.kids(~Parse.tree.step, f, body)
    case TBlob{}:
      Kids{Nil{}, True{}}
    case TMissing{}:
      Kids{Nil{}, True{}}
    case TBad{}:
      Kids{Nil{}, False{}}
