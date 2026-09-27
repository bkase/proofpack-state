# adapters/git/bytes.bend -- reading raw bytes.
#
# Everything Git hands back crosses the boundary as a list of bytes
# (host/proc.bend), because `git cat-file --batch` frames its records by a
# declared byte length and a UTF-8 decode would shift them. So the parser
# works in bytes and only renders text at the very end.
#
# Each reader answers what it consumed *and* the rest of the input, because
# the list is affine: there is no rewinding, and a reader that dropped the
# remainder would end the parse.

import Base
import ../../core/count.bend as C

def Bytes() -> Data:
  List<&2, U32>

type Cut is Data:
  Cut{taken: Bytes, rest: Bytes, ok: Bool}

# Split off the first `n` bytes. `ok` is False when the input ran out, which
# is a truncated record rather than an empty one.
def Bytes.take(+n: Nat, bs: Bytes, acc: Bytes) -> Cut:
  match n:
    case 0n:
      Cut{List.reverse(&2, U32, acc), bs, True{}}
    case 1n+p:
      match bs:
        case Nil{}:
          Cut{List.reverse(&2, U32, acc), Nil{}, False{}}
        case Con{b, t}:
          Bytes.take(p, t, Con{b, acc})

def Bytes.split(+n: Nat, bs: Bytes) -> Cut:
  Bytes.take(n, bs, Nil{})

# Drop the first `n` bytes.
def Bytes.skip(+n: Nat, bs: Bytes) -> Bytes:
  match n:
    case 0n:
      bs
    case 1n+p:
      match bs:
        case Nil{}:
          Nil{}
        case Con{b, t}:
          Bytes.skip(p, t)

# Is the next byte `sep`? The separator test is computed one step ahead and
# carried into `Bytes.upto`, because Bend forbids mutual recursion and matches
# parameters rather than computed values.
def Bytes.head_is(+bs: Bytes, +sep: U32) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{b, t}:
      U32.is_eq(b, sep)

# Split at the first occurrence of `sep`, which is consumed. `ok` is False
# when `sep` never appears.
def Bytes.upto(+sep: U32, bs: Bytes, acc: Bytes, hit: Bool) -> Cut:
  match bs:
    case Nil{}:
      Cut{List.reverse(&2, U32, acc), Nil{}, False{}}
    case Con{b, t}:
      match hit:
        case True{}:
          Cut{List.reverse(&2, U32, acc), t, True{}}
        case False{}:
          +t2 = t
          Bytes.upto(sep, t2, Con{b, acc}, Bytes.head_is(t2, sep))

# Skip past the first `sep` without copying what was skipped. `Bytes.upto`
# builds the taken part into an accumulator and reverses it, which is two
# allocations a byte -- fine when the caller wants the bytes, wasted when it
# only wants what follows. The inventory scan wants only what follows.
def Bytes.after.go(+sep: U32, bs: Bytes, hit: Bool) -> Bytes:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      match hit:
        case True{}:
          t
        case False{}:
          +tt = t
          Bytes.after.go(sep, tt, Bytes.head_is(tt, sep))

def Bytes.after(+sep: U32, +bs: Bytes) -> Bytes:
  Bytes.after.go(sep, bs, Bytes.head_is(bs, sep))

def Bytes.until(+sep: U32, +bs: Bytes) -> Cut:
  Bytes.upto(sep, bs, Nil{}, Bytes.head_is(bs, sep))

def Bytes.line(+bs: Bytes) -> Cut:
  Bytes.until(10, bs)

def Bytes.word(+bs: Bytes) -> Cut:
  Bytes.until(32, bs)

def Cut.taken(c: Cut) -> Bytes:
  match c:
    case Cut{taken, rest, ok}:
      taken

def Cut.rest(c: Cut) -> Bytes:
  match c:
    case Cut{taken, rest, ok}:
      rest

def Cut.ok(c: Cut) -> Bool:
  match c:
    case Cut{taken, rest, ok}:
      ok

# ---------------------------------------------------------------------------
# Numbers and text.
# ---------------------------------------------------------------------------

def Bytes.digit.pick(+b: U32, ok: Bool) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{U32.to_nat(U32.sub(b, 48))}
    case False{}:
      None{}

def Bytes.digit(+b: U32) -> Maybe<&2, Nat>:
  Bytes.digit.pick(b, Bool.and(U32.is_ge(b, 48), U32.is_le(b, 57)))

def Bytes.head_digit(+bs: Bytes) -> Maybe<&2, Nat>:
  match bs:
    case Nil{}:
      None{}
    case Con{b, t}:
      Bytes.digit(b)

# A decimal number. `ok` is False on an empty run or a non-digit byte, so a
# malformed size is rejected rather than read as zero.
def Bytes.decimal(bs: Bytes, acc: Nat, any: Bool, d: Maybe<&2, Nat>) ->
  Nat & Bool:
  match bs:
    case Nil{}:
      (acc, any)
    case Con{b, t}:
      match d:
        case None{}:
          (acc, False{})
        case Some{v}:
          +t2 = t
          Bytes.decimal(t2, Nat.add(Nat.mul(acc, 10n), v), True{},
            Bytes.head_digit(t2))

def Bytes.number(+bs: Bytes) -> Nat & Bool:
  Bytes.decimal(bs, 0n, False{}, Bytes.head_digit(bs))

def Bytes.to_string(bs: Bytes) -> String:
  match bs:
    case Nil{}:
      SNil{}
    case Con{b, t}:
      SCon{Chr{b}, Bytes.to_string(t)}

def Bytes.of_string(s: String) -> Bytes:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      match c:
        case Chr{x}:
          Con{x, Bytes.of_string(t)}

def Bytes.eq(a: Bytes, b: Bytes, ok: Bool) -> Bool:
  match a:
    case Nil{}:
      Bool.and(ok, List.is_empty(&2, U32, b))
    case Con{x, xt}:
      match b:
        case Nil{}:
          False{}
        case Con{y, yt}:
          match ok:
            case False{}:
              False{}
            case True{}:
              Bytes.eq(xt, yt, U32.is_eq(x, y))

def Bytes.equal(a: Bytes, b: Bytes) -> Bool:
  Bytes.eq(a, b, True{})

def Bytes.starts.go(pre: Bytes, bs: Bytes, ok: Bool) -> Bool:
  match pre:
    case Nil{}:
      ok
    case Con{p, pt}:
      match bs:
        case Nil{}:
          False{}
        case Con{b, bt}:
          match ok:
            case False{}:
              False{}
            case True{}:
              Bytes.starts.go(pt, bt, U32.is_eq(b, p))

def Bytes.starts(pre: Bytes, bs: Bytes) -> Bool:
  Bytes.starts.go(pre, bs, True{})
