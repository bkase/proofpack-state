# proofs/trie.bend -- a trie reads back what was written (law U-01, in part).
#
# The identity map is a trie of buckets: interning an object id looks its
# bucket up, and on a first mention writes a new slot and hands back a fresh
# ordinal. For that to round-trip -- interning the same id twice giving the
# same ordinal -- the write has to be visible to the next read.
#
# `Trie.put` and `Trie.get` take the same branch from the same half-width at
# every level, and `put` builds the path it descends, so this needs no
# hypothesis at all: no validity, and no range on the key. That is the
# difference from the set tree, where a leaf's extent matters.

import Base
import ./eq.bend as E
import ../core/trie.bend as T

law Trie.get_put:
  for -A: Data
  for +d: Nat
  for +t: T.Trie<A>
  for +h: U32
  for +x: U32
  for +v: A
  for +b: Bool
  for +eb: {b == U32.is_lt(x, h) : Bool}
  {T.Trie.get(A, d, T.Trie.put(A, d, t, h, x, v, b), h, x)
    == Some{v} : Maybe<&2, A>}

def Trie.get_put(A, d, t, h, x, v, b, eb):
  match d:
    case 0n:
      {==}
    case 1n+p:
      match t:
        case T.TBr{lo, hi}:
          match b:
            case True{}:
              %eb : {T.Trie.get(A, p, T.Trie.pick(A, _,
                  T.Trie.put(A, p, lo, U32.shr(h), x, v,
                    U32.is_lt(x, U32.shr(h))), hi),
                  U32.shr(h), T.Trie.rebase(_, h, x))
                == Some{v} : Maybe<&2, A>}
              Trie.get_put(A, p, lo, U32.shr(h), x, v,
                U32.is_lt(x, U32.shr(h)), {==})
            case False{}:
              %eb : {T.Trie.get(A, p, T.Trie.pick(A, _, lo,
                  T.Trie.put(A, p, hi, U32.shr(h), U32.sub(x, h), v,
                    U32.is_lt(U32.sub(x, h), U32.shr(h)))),
                  U32.shr(h), T.Trie.rebase(_, h, x))
                == Some{v} : Maybe<&2, A>}
              Trie.get_put(A, p, hi, U32.shr(h), U32.sub(x, h), v,
                U32.is_lt(U32.sub(x, h), U32.shr(h)), {==})
        case T.TGap{}:
          match b:
            case True{}:
              %eb : {T.Trie.get(A, p, T.Trie.pick(A, _,
                  T.Trie.put(A, p, T.TGap{}, U32.shr(h), x, v,
                    U32.is_lt(x, U32.shr(h))), T.TGap{}),
                  U32.shr(h), T.Trie.rebase(_, h, x))
                == Some{v} : Maybe<&2, A>}
              Trie.get_put(A, p, T.TGap{}, U32.shr(h), x, v,
                U32.is_lt(x, U32.shr(h)), {==})
            case False{}:
              %eb : {T.Trie.get(A, p, T.Trie.pick(A, _, T.TGap{},
                  T.Trie.put(A, p, T.TGap{}, U32.shr(h), U32.sub(x, h), v,
                    U32.is_lt(U32.sub(x, h), U32.shr(h)))),
                  U32.shr(h), T.Trie.rebase(_, h, x))
                == Some{v} : Maybe<&2, A>}
              Trie.get_put(A, p, T.TGap{}, U32.shr(h), U32.sub(x, h), v,
                U32.is_lt(U32.sub(x, h), U32.shr(h)), {==})
        case T.TVal{old}:
          match b:
            case True{}:
              %eb : {T.Trie.get(A, p, T.Trie.pick(A, _,
                  T.Trie.put(A, p, T.TGap{}, U32.shr(h), x, v,
                    U32.is_lt(x, U32.shr(h))), T.TGap{}),
                  U32.shr(h), T.Trie.rebase(_, h, x))
                == Some{v} : Maybe<&2, A>}
              Trie.get_put(A, p, T.TGap{}, U32.shr(h), x, v,
                U32.is_lt(x, U32.shr(h)), {==})
            case False{}:
              %eb : {T.Trie.get(A, p, T.Trie.pick(A, _, T.TGap{},
                  T.Trie.put(A, p, T.TGap{}, U32.shr(h), U32.sub(x, h), v,
                    U32.is_lt(U32.sub(x, h), U32.shr(h)))),
                  U32.shr(h), T.Trie.rebase(_, h, x))
                == Some{v} : Maybe<&2, A>}
              Trie.get_put(A, p, T.TGap{}, U32.shr(h), U32.sub(x, h), v,
                U32.is_lt(U32.sub(x, h), U32.shr(h)), {==})

law Trie.at_set:
  for -A: Data
  for +d: Nat
  for +t: T.Trie<A>
  for +x: U32
  for +v: A
  {T.Trie.at(A, d, T.Trie.set(A, d, t, x, v), x)
    == Some{v} : Maybe<&2, A>}

def Trie.at_set(A, d, t, x, v):
  Trie.get_put(A, d, t, T.Trie.half(d), x, v,
    U32.is_lt(x, T.Trie.half(d)), {==})
