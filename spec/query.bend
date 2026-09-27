# spec/query.bend -- the denotation of a query.
#
# SPEC 3.5: denotation is recursive, and
#
#   [[a u b]]_W = [[a]]_W u [[b]]_W
#   [[Reach(p, a)]]_W = C_{G_p}([[a]]_W)
#
# This module is that, written as directly as it can be: every operator maps
# to the proved set operation of core/set.bend, and `Reach` maps to the
# specification closure of spec/closure.bend -- the one that recomputes post
# over the whole set each round. No rewrites, no pruning, no fusion.
#
# It is the oracle. query/eval.bend is the production evaluator, and the
# compiler contract of SPEC 3.6 is that the two agree:
#
#   observe(execute_b(compile(W, q))) = [[q]]_W
#
# `Full` denotes the universe {x : x < N}, not the representation's `Full`
# node. The two differ once N is not a multiple of a leaf, and SPEC 5.5 is
# explicit that a newly discovered object must not appear in yesterday's
# inventory because unused bitmap capacity happened to contain ones. So the
# universe is built by masking, once, from N.

import Base
import ../core/count.bend as C
import ../core/set.bend as S
import ../core/trie.bend as T
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../closure/graph.bend as G
import ./closure.bend as Sp
import ../index/source.bend as Idx
import ../adapters/git/import.bend as Im
import ../query/ast.bend as A

# ---------------------------------------------------------------------------
# The universe as a set: exactly the ordinals below N, with the tail of the
# straddling leaf masked off.
# ---------------------------------------------------------------------------

def Den.upto(+n: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      Den.upto(p, Con{U32.from_nat(p), acc})

def Den.universe(+n: Nat) -> S.PSet:
  S.PSet.from_list(20n, Den.upto(n, Nil{}))

# ---------------------------------------------------------------------------
# Type filtering. `Filter` is applied *after* reachability, never pushed
# through it: removing commit vertices before traversal erases the paths to
# the blobs they require (SPEC 4.1).
# ---------------------------------------------------------------------------

def Den.keep.pick(+x: U32, rest: List<&2, U32>, hit: Bool) ->
  List<&2, U32>:
  match hit:
    case False{}:
      rest
    case True{}:
      Con{x, rest}

def Den.keep(+src: Idx.Source, +kind: U32, +xs: List<&2, U32>) ->
  List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Den.keep.pick(x, Den.keep(src, kind, t),
        U32.is_eq(Im.Meta.kind(Idx.Source.meta_of(src, x)), kind))

def Den.filter(+src: Idx.Source, +kind: U32, s: S.PSet) ->
  S.PSet:
  S.PSet.from_list(20n, Den.keep(src, kind, S.PSet.to_list(20n, s)))

# ---------------------------------------------------------------------------
# The denotation.
# ---------------------------------------------------------------------------

def Den.eval(+src: Idx.Source, e: A.SetExpr) -> S.PSet:
  match e:
    case A.EEmpty{}:
      S.PSet.empty()
    case A.EFull{}:
      Den.universe(Idx.Source.n(src))
    case A.ELit{set}:
      set
    case A.EUnion{a, b}:
      S.PSet.union(20n, Den.eval(src, a), Den.eval(src, b))
    case A.EInter{a, b}:
      S.PSet.inter(20n, Den.eval(src, a), Den.eval(src, b))
    case A.EDiff{a, b}:
      S.PSet.diff(20n, Den.eval(src, a), Den.eval(src, b))
    case A.EReach{policy, a}:
      Sp.Spec.closure(Idx.Source.n(src), 32n,
        Idx.Source.graph(src, policy), 20n, Den.eval(src, a))
    case A.EFilter{kind, a}:
      Den.filter(src, kind, Den.eval(src, a))
