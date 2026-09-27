# proofs/parse.bend -- G-01, in part: the parser never reads an id short.
#
# G-01 is soundness and completeness for the *declared* metadata grammar with
# explicit limits (SPEC 8.3), and it is the obligation a proof can least
# reach as a whole: the grammar it has to be complete for is Git's, not this
# tree's, so what would make the whole of it a law is a grammar predicate
# written in Bend and faithful to Git rather than read off the parser -- and
# one read off the parser would make the law true by construction and worth
# nothing.
#
# One part of it does not depend on that, because it is a statement about the
# parser alone, and it is the part the header of `adapters/git/oid.bend`
# claims in prose: an object id is read at exactly the format's width, and
# fewer characters is an invalid id rather than a silently truncated one.
# That is the failure mode that matters, because a short id is a *different*
# id, not a malformed one -- it would intern as a new object and every count
# downstream would be wrong.
#
# So: a hex read that is accepted consumed at least as many bytes as the
# format declares. `Oid.of_hex` asks for `Fmt.hex_len(f)` of them.

import Base
import ./eq.bend as E
import ../core/count.bend as C
import ../adapters/git/bytes.bend as B
import ../adapters/git/oid.bend as O
import ../adapters/git/parse.bend as P

law Oid.hex_read_needs_width:
  for +n: Nat
  for +bs: B.Bytes
  for +acc: O.Oid
  for +cur: U32
  for +v: Maybe<&2, U32>
  for +k: Nat
  for +ok: {O.OidRead.ok(O.Oid.of_hex.go(n, bs, acc, cur, v, k))
    == True{} : Bool}
  {C.Nat.upto(n, List.length(&2, U32, bs)) == True{} : Bool}

def Oid.hex_read_needs_width(n, bs, acc, cur, v, k, ok):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match bs:
        case Nil{}:
          E.Bool.noconf({C.Nat.upto(1n+p, 0n) == True{} : Bool}, ok)
        case Con{b, t}:
          match v:
            case None{}:
              E.Bool.noconf({C.Nat.upto(1n+p,
                1n+List.length(&2, U32, t)) == True{} : Bool}, ok)
            case Some{d}:
              match k:
                case 0n:
                  E.Bool.noconf({C.Nat.upto(1n+p,
                    1n+List.length(&2, U32, t)) == True{} : Bool}, ok)
                case 1n+j:
                  match j:
                    case 0n:
                      Oid.hex_read_needs_width(p, t,
                        O.Oid.push((cur * 16 + d : U32), acc), 0,
                        O.Oid.head_hex(t), 8n, ok)
                    case 1n+i:
                      Oid.hex_read_needs_width(p, t, acc,
                        (cur * 16 + d : U32), O.Oid.head_hex(t), 1n+i, ok)

law Oid.of_hex_needs_width:
  for +f: O.Fmt
  for +bs: B.Bytes
  for +ok: {O.OidRead.ok(O.Oid.of_hex(f, bs)) == True{} : Bool}
  {C.Nat.upto(O.Fmt.hex_len(f), List.length(&2, U32, bs))
    == True{} : Bool}

def Oid.of_hex_needs_width(f, bs, ok):
  Oid.hex_read_needs_width(O.Fmt.hex_len(f), bs, O.Oid.zero(), 0,
    O.Oid.head_hex(bs), 8n, ok)

# ---------------------------------------------------------------------------
# And the other half of "never read short": a body is taken by its declared
# length, and a record whose length overruns the buffer is rejected rather
# than truncated. SPEC 8.3 asks for exactly that -- bodies are read by
# declared length and never by scanning the stream for a terminator.
# ---------------------------------------------------------------------------

law Bytes.take_needs_width:
  for +n: Nat
  for +bs: B.Bytes
  for +acc: B.Bytes
  for +ok: {B.Cut.ok(B.Bytes.take(n, bs, acc)) == True{} : Bool}
  {C.Nat.upto(n, List.length(&2, U32, bs)) == True{} : Bool}

def Bytes.take_needs_width(n, bs, acc, ok):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match bs:
        case Nil{}:
          E.Bool.noconf({C.Nat.upto(1n+p, 0n) == True{} : Bool}, ok)
        case Con{b, t}:
          Bytes.take_needs_width(p, t, Con{b, acc}, ok)

law Bytes.split_needs_width:
  for +n: Nat
  for +bs: B.Bytes
  for +ok: {B.Cut.ok(B.Bytes.split(n, bs)) == True{} : Bool}
  {C.Nat.upto(n, List.length(&2, U32, bs)) == True{} : Bool}

def Bytes.split_needs_width(n, bs, ok):
  Bytes.take_needs_width(n, bs, Nil{}, ok)

def Parse.is_rec(s: P.Step) -> Bool:
  match s:
    case P.SRec{rec, rest}:
      True{}
    case P.SDone{}:
      False{}
    case P.SBad{}:
      False{}

law Parse.take_is_rec:
  for +oid: O.Oid
  for +k: P.GType
  for +c: B.Cut
  for +ok: {Parse.is_rec(P.Parse.recs.step.take(oid, k, c))
    == True{} : Bool}
  {B.Cut.ok(c) == True{} : Bool}

def Parse.take_is_rec(oid, k, c, ok):
  match c:
    case B.Cut{taken, rest, cok}:
      match cok:
        case True{}:
          {==}
        case False{}:
          ok

law Parse.a_record_fits_its_declared_size:
  for +oid: O.Oid
  for +k: P.GType
  for +n: Nat
  for +bs: B.Bytes
  for +ok: {Parse.is_rec(P.Parse.recs.step.take(oid, k,
    B.Bytes.split(n, bs))) == True{} : Bool}
  {C.Nat.upto(n, List.length(&2, U32, bs)) == True{} : Bool}

def Parse.a_record_fits_its_declared_size(oid, k, n, bs, ok):
  Bytes.split_needs_width(n, bs,
    Parse.take_is_rec(oid, k, B.Bytes.split(n, bs), ok))
