# adapters/git/intern.bend -- object identity to ordinal.
#
# A universe generation is a size N and an injective `identify : Fin(N) ->
# ObjectKey` (SPEC 3.1). This module is the inverse direction, built as
# objects are discovered: the first time an object id is mentioned -- as a
# root, or as a child inside a commit, tag or tree -- it is given the next
# ordinal, and every later mention answers the same one. That is what makes
# `identify` injective by construction, and it is why an object can be
# referenced before it is fetched.
#
# The table is a bucket trie keyed on the last word of the digest. Object ids
# are cryptographic hashes, so that word is uniformly distributed and the
# buckets stay short; a bucket still compares the *complete* key, so a
# collision costs a list step and never a wrong answer. No hash-collision
# assumption is made anywhere (SPEC 8.4).

import Base
import ../../core/count.bend as C
import ../../core/trie.bend as T
import ./oid.bend as O

type Slot is Data:
  Slot{oid: O.Oid, ord: U32}

def Bucket() -> Data:
  List<&2, Slot>

# 2^20 buckets. A benchmark parameter: more buckets cost trie nodes, fewer
# cost list steps, and neither changes an answer.
def Uni.bits() -> Nat:
  20n

def Uni.mask() -> U32:
  1048575

def Uni.slot_key(+o: O.Oid) -> U32:
  U32.and(O.Oid.key(o), Uni.mask())

type Universe is Data:
  Uni{fmt: O.Fmt, next: U32, table: T.Trie(Bucket, 20n),
    oids: List<&2, O.Oid>}

def Uni.new(f: O.Fmt) -> Universe:
  Uni{f, 0, T.Trie.gap(Bucket, 20n), Nil{}}

def Slot.match_one.pick(+ord: U32, same: Bool) -> Maybe<&2, U32>:
  match same:
    case True{}:
      Some{ord}
    case False{}:
      None{}

def Slot.match_one(s: Slot, +o: O.Oid) -> Maybe<&2, U32>:
  match s:
    case Slot{sid, ord}:
      Slot.match_one.pick(ord, O.Oid.eq(sid, o))

def Slot.find(bs: List<&2, Slot>, +o: O.Oid, got: Maybe<&2, U32>) ->
  Maybe<&2, U32>:
  match bs:
    case Nil{}:
      got
    case Con{s, t}:
      match got:
        case Some{k}:
          Some{k}
        case None{}:
          Slot.find(t, o, Slot.match_one(s, o))

def Uni.bucket.un(m: Maybe<&2, Bucket>) -> Bucket:
  match m:
    case None{}:
      Nil{}
    case Some{b}:
      b

def Uni.bucket(+t: T.Trie(Bucket, 20n), +k: U32) -> Bucket:
  Uni.bucket.un(T.Trie.at(Bucket, 20n, t, k))

def Uni.find(+t: T.Trie(Bucket, 20n), +o: O.Oid) -> Maybe<&2, U32>:
  Slot.find(Uni.bucket(t, Uni.slot_key(o)), o, None{})

type Interned is Data:
  In{uni: Universe, ord: U32}

def Uni.intern.go(f: O.Fmt, +next: U32, +t: T.Trie(Bucket, 20n),
  oids: List<&2, O.Oid>, +o: O.Oid, found: Maybe<&2, U32>) -> Interned:
  match found:
    case Some{k}:
      In{Uni{f, next, t, oids}, k}
    case None{}:
      +k = Uni.slot_key(o)
      In{Uni{f, (next + 1 : U32),
        T.Trie.set(Bucket, 20n, t, k,
          Con{Slot{o, next}, Uni.bucket(t, k)}), Con{o, oids}}, next}

# The ordinal for `o`, assigning the next one if this is its first mention.
def Uni.intern(u: Universe, +o: O.Oid) -> Interned:
  match u:
    case Uni{f, next, table, oids}:
      +t = table
      Uni.intern.go(f, next, t, oids, o, Uni.find(t, o))

def Interned.uni(i: Interned) -> Universe:
  match i:
    case In{uni, ord}:
      uni

def Interned.ord(i: Interned) -> U32:
  match i:
    case In{uni, ord}:
      ord

def Uni.size(+u: Universe) -> Nat:
  match u:
    case Uni{f, next, table, oids}:
      U32.to_nat(next)

def Uni.fmt(+u: Universe) -> O.Fmt:
  match u:
    case Uni{f, next, table, oids}:
      f

# The object ids in ordinal order. `oids` is accumulated newest-first, so this
# reverses it: ordinal `i` is the i-th element, which is `identify` itself.
def Uni.identify(u: Universe) -> List<&2, O.Oid>:
  match u:
    case Uni{f, next, table, oids}:
      List.reverse(&2, O.Oid, oids)

# The object ids most recently assigned an ordinal, in ordinal order. The
# importer uses this to learn which objects a batch just discovered, without
# rebuilding the whole identity list every round.
def Uni.recent(+u: Universe, +n: Nat) -> List<&2, O.Oid>:
  match u:
    case Uni{f, next, table, oids}:
      List.reverse(&2, O.Oid, List.take(&2, O.Oid, oids, n))
