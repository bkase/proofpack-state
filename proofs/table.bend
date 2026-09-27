# proofs/table.bend -- what a table built from a list answers.
#
# Every per-object table in the index is a trie built in one pass from a list
# in ordinal order: adjacency under each policy, object metadata, the object
# ids. `Trie.build` splits the list in half at each level and `Trie.get`
# descends the same halves, so the answer at an ordinal is determined by the
# list -- which is the fact G-02's lift needs, because the two adjacency
# tables are built from positionally parallel lists and the proved row-level
# law relates the rows at a position.
#
# Stating that as "the element at index `to_nat(x)`" would drag in the whole
# numeric reading of a machine word: that the half-width is a power of two,
# that `U32.sub` is subtraction, that `take` and `drop` at `to_nat(h)` line up
# with the bit test. None of that is needed. What the lift needs is that two
# tables built from parallel lists answer at corresponding positions, and for
# that it is enough to say the answer is whatever the *same descent over the
# list* produces. `List.at_ord` is that descent, and it takes the same branch
# from the same half-width as the trie does, by construction.
#
# So this file is arithmetic-free, and deliberately: the descent is the
# specification, not a numeric index into it.

import Base
import ./eq.bend as E
import ../core/trie.bend as T

# The same walk, on the list. `Trie.build` splits with `take`/`drop` at
# `to_nat(h)` and `Trie.get` picks with `U32.is_lt(x, h)`; this does both,
# in the same order.

def List.pick(-A: Data, b: Bool, lo: List<&2, A>, hi: List<&2, A>) ->
  List<&2, A>:
  match b:
    case True{}:
      lo
    case False{}:
      hi

def List.head_or_none(-A: Data, xs: List<&2, A>) -> Maybe<&2, A>:
  match xs:
    case Nil{}:
      None{}
    case Con{v, rest}:
      Some{v}

def List.at_ord(-A: Data, +d: Nat, xs: List<&2, A>, +h: U32, +x: U32) ->
  Maybe<&2, A>:
  match d:
    case 0n:
      List.head_or_none(A, xs)
    case 1n+p:
      match xs:
        case Nil{}:
          None{}
        case Con{v, rest}:
          +ys = {Con{v, rest} : List<&2, A>}
          +k = U32.to_nat(h)
          +b = U32.is_lt(x, h)
          List.at_ord(A, p,
            List.pick(A, b, List.take(&2, A, ys, k),
              List.drop(&2, A, ys, k)),
            U32.shr(h), T.Trie.rebase(b, h, x))

# Building each half and then choosing is choosing and then building.
law Trie.build_pick:
  for -A: Data
  for +b: Bool
  for +p: Nat
  for +h: U32
  for +lo: List<&2, A>
  for +hi: List<&2, A>
  {T.Trie.pick(A, b, T.Trie.build(A, p, h, lo), T.Trie.build(A, p, h, hi))
    == T.Trie.build(A, p, h, List.pick(A, b, lo, hi)) : T.Trie<A>}

def Trie.build_pick(A, b, p, h, lo, hi):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

law Trie.get_build:
  for -A: Data
  for +d: Nat
  for +xs: List<&2, A>
  for +h: U32
  for +x: U32
  {T.Trie.get(A, d, T.Trie.build(A, d, h, xs), h, x)
    == List.at_ord(A, d, xs, h, x) : Maybe<&2, A>}

def Trie.get_build(A, d, xs, h, x):
  match d:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{v, rest}:
          {==}
    case 1n+p:
      match xs:
        case Nil{}:
          {==}
        case Con{v, rest}:
          %E.Trie.sym(A,
            T.Trie.pick(A, U32.is_lt(x, h),
              T.Trie.build(A, p, U32.shr(h),
                List.take(&2, A, Con{v, rest}, U32.to_nat(h))),
              T.Trie.build(A, p, U32.shr(h),
                List.drop(&2, A, Con{v, rest}, U32.to_nat(h)))),
            T.Trie.build(A, p, U32.shr(h),
              List.pick(A, U32.is_lt(x, h),
                List.take(&2, A, Con{v, rest}, U32.to_nat(h)),
                List.drop(&2, A, Con{v, rest}, U32.to_nat(h)))),
            Trie.build_pick(A, U32.is_lt(x, h), p, U32.shr(h),
              List.take(&2, A, Con{v, rest}, U32.to_nat(h)),
              List.drop(&2, A, Con{v, rest}, U32.to_nat(h))))
            : {T.Trie.get(A, p, _, U32.shr(h),
                T.Trie.rebase(U32.is_lt(x, h), h, x))
              == List.at_ord(A, p,
                   List.pick(A, U32.is_lt(x, h),
                     List.take(&2, A, Con{v, rest}, U32.to_nat(h)),
                     List.drop(&2, A, Con{v, rest}, U32.to_nat(h))),
                   U32.shr(h), T.Trie.rebase(U32.is_lt(x, h), h, x))
              : Maybe<&2, A>}
          Trie.get_build(A, p,
            List.pick(A, U32.is_lt(x, h),
              List.take(&2, A, Con{v, rest}, U32.to_nat(h)),
              List.drop(&2, A, Con{v, rest}, U32.to_nat(h))),
            U32.shr(h), T.Trie.rebase(U32.is_lt(x, h), h, x))

law Trie.at_of_list:
  for -A: Data
  for +d: Nat
  for +xs: List<&2, A>
  for +x: U32
  {T.Trie.at(A, d, T.Trie.of_list(A, d, xs), x)
    == List.at_ord(A, d, xs, T.Trie.half(d), x) : Maybe<&2, A>}

def Trie.at_of_list(A, d, xs, x):
  Trie.get_build(A, d, xs, T.Trie.half(d), x)
