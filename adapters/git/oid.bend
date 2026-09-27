# adapters/git/oid.bend -- object identities.
#
# SPEC 2 fixes logical identity as namespace + object format + the *complete*
# object id, never an unscoped ordinal. This module is the complete object id.
#
# An `Oid` is eight `U32` words: SHA-1 fills five and zeroes the rest, SHA-256
# fills all eight. One flat 8-word record rather than a 20- or 32-cell byte
# list, because a million of them is the normal case and the list form would
# cost four times the heap. Both widths are supported through an explicit
# object-format tag (SPEC 8.4) -- the width is a property of the universe, not
# guessed from a length.
#
# Nothing here assumes hash collisions are impossible. Identity is equality of
# the complete key; that those keys name the intended bytes is an external
# premise recorded in TRUST.md (SPEC 8.4).

import Base
import ../../core/count.bend as C
import ./bytes.bend as B

type Oid is Data:
  Oid{w0: U32, w1: U32, w2: U32, w3: U32, w4: U32, w5: U32, w6: U32,
    w7: U32}

type Fmt is Data:
  Sha1{}
  Sha256{}

def Fmt.bytes(f: Fmt) -> Nat:
  match f:
    case Sha1{}:
      20n
    case Sha256{}:
      32n

def Fmt.hex_len(f: Fmt) -> Nat:
  match f:
    case Sha1{}:
      40n
    case Sha256{}:
      64n

def Fmt.name(f: Fmt) -> String:
  match f:
    case Sha1{}:
      "sha1"
    case Sha256{}:
      "sha256"

def Oid.zero() -> Oid:
  Oid{0, 0, 0, 0, 0, 0, 0, 0}

# The first word, big-endian. Object ids are cryptographic digests, so this is
# uniformly distributed -- which is what makes it a sound bucket key for the
# interning table in adapters/git/intern.bend.
def Oid.key(o: Oid) -> U32:
  match o:
    case Oid{w0, w1, w2, w3, w4, w5, w6, w7}:
      w7

def Oid.eq(a: Oid, b: Oid) -> Bool:
  match a:
    case Oid{a0, a1, a2, a3, a4, a5, a6, a7}:
      match b:
        case Oid{b0, b1, b2, b3, b4, b5, b6, b7}:
          Bool.and(U32.is_eq(a0, b0),
            Bool.and(U32.is_eq(a1, b1),
              Bool.and(U32.is_eq(a2, b2),
                Bool.and(U32.is_eq(a3, b3),
                  Bool.and(U32.is_eq(a4, b4),
                    Bool.and(U32.is_eq(a5, b5),
                      Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))))

# ---------------------------------------------------------------------------
# Reading. `Oid.of_bytes` takes a raw object id as it appears inside a tree
# entry; `Oid.of_hex` takes the ASCII form `cat-file` prints. Both fold the
# digest into the record four bytes (or eight hex characters) at a time,
# shifting a completed word in at the low end -- so a 20-byte SHA-1 lands in
# w3..w7 and a 32-byte SHA-256 fills all eight, and `Oid.key` reads the last
# word, which is digest material in either format.
# ---------------------------------------------------------------------------

def Oid.push(+w: U32, o: Oid) -> Oid:
  match o:
    case Oid{w0, w1, w2, w3, w4, w5, w6, w7}:
      Oid{w1, w2, w3, w4, w5, w6, w7, w}

def Oid.of_bytes.go(+n: Nat, bs: B.Bytes, acc: Oid, +cur: U32, k: Nat) ->
  Oid:
  match n:
    case 0n:
      acc
    case 1n+p:
      match bs:
        case Nil{}:
          acc
        case Con{b, t}:
          match k:
            case 0n:
              acc
            case 1n+j:
              match j:
                case 0n:
                  Oid.of_bytes.go(p, t,
                    Oid.push((cur * 256 + b : U32), acc), 0, 4n)
                case 1n+i:
                  Oid.of_bytes.go(p, t, acc, (cur * 256 + b : U32), 1n+i)

def Oid.of_bytes(f: Fmt, bs: B.Bytes) -> Oid:
  Oid.of_bytes.go(Fmt.bytes(f), bs, Oid.zero(), 0, 4n)

def Oid.hex_val.pick(+b: U32, dig: Bool, low: Bool, up: Bool) ->
  Maybe<&2, U32>:
  match dig:
    case True{}:
      Some{U32.sub(b, 48)}
    case False{}:
      match low:
        case True{}:
          Some{U32.sub(b, 87)}
        case False{}:
          match up:
            case True{}:
              Some{U32.sub(b, 55)}
            case False{}:
              None{}

def Oid.hex_val(+b: U32) -> Maybe<&2, U32>:
  Oid.hex_val.pick(b, Bool.and(U32.is_ge(b, 48), U32.is_le(b, 57)),
    Bool.and(U32.is_ge(b, 97), U32.is_le(b, 102)),
    Bool.and(U32.is_ge(b, 65), U32.is_le(b, 70)))

def Oid.head_hex(+bs: List<&2, U32>) -> Maybe<&2, U32>:
  match bs:
    case Nil{}:
      None{}
    case Con{b, t}:
      Oid.hex_val(b)

type OidRead is Data:
  Read{oid: Oid, ok: Bool}

def Oid.of_hex.go(+n: Nat, bs: B.Bytes, acc: Oid, +cur: U32,
  v: Maybe<&2, U32>, k: Nat) -> OidRead:
  match n:
    case 0n:
      Read{acc, True{}}
    case 1n+p:
      match bs:
        case Nil{}:
          Read{acc, False{}}
        case Con{b, t}:
          match v:
            case None{}:
              Read{acc, False{}}
            case Some{d}:
              match k:
                case 0n:
                  Read{acc, False{}}
                case 1n+j:
                  match j:
                    case 0n:
                      +t2 = t
                      Oid.of_hex.go(p, t2,
                        Oid.push((cur * 16 + d : U32), acc), 0,
                        Oid.head_hex(t2), 8n)
                    case 1n+i:
                      +t3 = t
                      Oid.of_hex.go(p, t3, acc, (cur * 16 + d : U32),
                        Oid.head_hex(t3), 1n+i)

# Read exactly `Fmt.hex_len(f)` hex characters. Fewer, or a non-hex byte, is
# `ok = False` -- an invalid object id, never a silently truncated one.
def Oid.of_hex(f: Fmt, +bs: B.Bytes) -> OidRead:
  Oid.of_hex.go(Fmt.hex_len(f), bs, Oid.zero(), 0, Oid.head_hex(bs), 8n)

def OidRead.oid(r: OidRead) -> Oid:
  match r:
    case Read{oid, ok}:
      oid

def OidRead.ok(r: OidRead) -> Bool:
  match r:
    case Read{oid, ok}:
      ok

# ---------------------------------------------------------------------------
# Writing.
# ---------------------------------------------------------------------------

def Oid.hex_chr.pick(+v: U32, dig: Bool) -> Char:
  match dig:
    case True{}:
      Chr{(v + 48 : U32)}
    case False{}:
      Chr{(v + 87 : U32)}

def Oid.hex_chr(+v: U32) -> Char:
  Oid.hex_chr.pick(v, U32.is_lt(v, 10))

def Oid.word_hex(+k: Nat, +w: U32, acc: String) -> String:
  match k:
    case 0n:
      acc
    case 1n+j:
      Oid.word_hex(j, U32.shrn(w, 4n),
        SCon{Oid.hex_chr(U32.and(w, 15)), acc})

def Oid.show.pick(f: Fmt, +w0: U32, +w1: U32, +w2: U32, +w3: U32, +w4: U32,
  +w5: U32, +w6: U32, +w7: U32) -> String:
  match f:
    case Sha1{}:
      Oid.word_hex(8n, w3, Oid.word_hex(8n, w4, Oid.word_hex(8n, w5,
        Oid.word_hex(8n, w6, Oid.word_hex(8n, w7, "")))))
    case Sha256{}:
      Oid.word_hex(8n, w0, Oid.word_hex(8n, w1, Oid.word_hex(8n, w2,
        Oid.word_hex(8n, w3, Oid.word_hex(8n, w4, Oid.word_hex(8n, w5,
          Oid.word_hex(8n, w6, Oid.word_hex(8n, w7, ""))))))))

def Oid.show(f: Fmt, o: Oid) -> String:
  match o:
    case Oid{w0, w1, w2, w3, w4, w5, w6, w7}:
      Oid.show.pick(f, w0, w1, w2, w3, w4, w5, w6, w7)

