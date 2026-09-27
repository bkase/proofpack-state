# query/eval.bend -- the production evaluator.
#
# Same expressions as spec/query.bend, same answers, different work:
#
#   * a rewrite pass runs first (query/rewrite.bend),
#   * `Reach` uses the frontier traversal of closure/reach.bend instead of
#     recomputing post over the whole set each round,
#   * and `Stats`, `IsEmpty` and `IsSubset` over a difference are *fused*:
#     `Missing = Required \ Have` is never allocated merely to be measured
#     (SPEC 7.2).
#
# The fused paths are the interesting ones. `Ev.missing_stats` walks the two
# trees together and enumerates only the members of the difference, pruning
# whole intervals where an operand is Zero or Full. `Ev.ready` stops at the
# first required object the inventory does not have. A matrix of a million
# cells does not imply a million full-universe bitmaps.
#
# Reachability is resolved before any ordinal-local work (SPEC 7.2): graph
# paths leave an ordinal tile and come back, so `Reach(R) n I` is not the
# closure of `R n I` inside the induced graph on I. Leaf jobs here only ever
# see established set values.
#
# A traversal that runs out of budget is reported, never rounded off: `Val`
# carries `ok` and an error class, and the CLI turns that into exit 3.

import Base
import ../core/count.bend as C
import ../core/set.bend as S
import ../core/trie.bend as T
import ../closure/graph.bend as G
import ../closure/reach.bend as R
import ../index/source.bend as Idx
import ../adapters/git/import.bend as Im
import ../spec/query.bend as Den
import ./ast.bend as A
import ./rewrite.bend as Rw

type Val is Data:
  V{set: S.PSet, ok: Bool, err: String}

def Val.set(+v: Val) -> S.PSet:
  match v:
    case V{set, ok, err}:
      set

def Val.ok(+v: Val) -> Bool:
  match v:
    case V{set, ok, err}:
      ok

def Val.err(+v: Val) -> String:
  match v:
    case V{set, ok, err}:
      err

def Val.both(a: Val, b: Val, f: Bool) -> Val:
  match f:
    case True{}:
      a
    case False{}:
      b

# ---------------------------------------------------------------------------
# Why this is a machine and not a fold.
#
# The obvious evaluator is structural recursion: `Union(a, b)` evaluates `a`,
# evaluates `b`, and combines. This runtime will not compile that. Two
# non-tail self-calls in one def become a segmented continuation whose frame
# overruns the documented 247-word limit, and `bend x.bend -o x` answers "an
# arity over 247" -- with one self-call it compiles, with two it does not,
# and a parallel let does not help.
#
# So evaluation is an explicit machine: a control word (an expression still to
# evaluate, or a value already computed), a stack of frames, and one tail
# self-call per step. Every step is a tail call, the native stack stays flat,
# and the fuel is derived from the expression's own size -- always enough,
# and `ResourceLimit` rather than a wrong answer if it were not.
# ---------------------------------------------------------------------------

type Frame is Data:
  FRight{op: Nat, rhs: A.SetExpr}
  FComb{op: Nat, lhs: S.PSet}
  FReach{policy: Idx.Policy}
  FFilter{kind: U32}

type Ctl is Data:
  CEval{expr: A.SetExpr}
  CVal{value: S.PSet}

def Ev.apply(sa: S.PSet, sb: S.PSet, op: Nat) -> S.PSet:
  match op:
    case 0n:
      S.PSet.union(20n, sa, sb)
    case 1n+x:
      match x:
        case 0n:
          S.PSet.inter(20n, sa, sb)
        case 1n+y:
          S.PSet.diff(20n, sa, sb)

# The traversal's own answer, and whether it finished. An exhausted budget
# empties the stack, which ends the machine with ok = False.
def Ev.reach.stack(done: Bool, k: List<&2, Frame>) -> List<&2, Frame>:
  match done:
    case True{}:
      k
    case False{}:
      Nil{}

def Ev.reach.err(done: Bool) -> String:
  match done:
    case True{}:
      ""
    case False{}:
      "ResourceLimit: the traversal budget was exhausted before the closure "
        ++ "was complete"

def Ev.size(e: A.SetExpr) -> Nat:
  match e:
    case A.EEmpty{}:
      1n
    case A.EFull{}:
      1n
    case A.ELit{set}:
      1n
    case A.EUnion{a, b}:
      1n+Nat.add(Ev.size(a), Ev.size(b))
    case A.EInter{a, b}:
      1n+Nat.add(Ev.size(a), Ev.size(b))
    case A.EDiff{a, b}:
      1n+Nat.add(Ev.size(a), Ev.size(b))
    case A.EReach{policy, a}:
      1n+Ev.size(a)
    case A.EFilter{kind, a}:
      1n+Ev.size(a)

def Ev.go(+fuel: Nat, +src: Idx.Source, c: Ctl, k: List<&2, Frame>) ->
  Val:
  match fuel:
    case 0n:
      V{S.PSet.empty(), False{},
        "ResourceLimit: the query evaluator ran out of steps"}
    case 1n+g:
      match c:
        case CVal{v}:
          match k:
            case Nil{}:
              V{v, True{}, ""}
            case Con{f, rest}:
              match f:
                case FRight{op, rhs}:
                  Ev.go(g, src, CEval{rhs}, Con{FComb{op, v}, rest})
                case FComb{op, lhs}:
                  Ev.go(g, src, CVal{Ev.apply(lhs, v, op)}, rest)
                case FFilter{kind}:
                  Ev.go(g, src, CVal{Den.Den.filter(src, kind, v)}, rest)
                case FReach{policy}:
                  +out = R.Reach.closure(Idx.Source.n(src), 32n,
                    Idx.Source.graph(src, policy), 20n,
                    S.PSet.to_list(20n, v))
                  Ev.go(g, src, CVal{R.Reach.seen(20n, out)},
                    Ev.reach.stack(R.Reach.done(20n, out), rest))
        case CEval{e}:
          match e:
            case A.EEmpty{}:
              Ev.go(g, src, CVal{S.PSet.empty()}, k)
            case A.EFull{}:
              Ev.go(g, src, CVal{Den.Den.universe(Idx.Source.n(src))}, k)
            case A.ELit{set}:
              Ev.go(g, src, CVal{set}, k)
            case A.EUnion{a, b}:
              Ev.go(g, src, CEval{a}, Con{FRight{0n, b}, k})
            case A.EInter{a, b}:
              Ev.go(g, src, CEval{a}, Con{FRight{1n, b}, k})
            case A.EDiff{a, b}:
              Ev.go(g, src, CEval{a}, Con{FRight{2n, b}, k})
            case A.EReach{policy, a}:
              Ev.go(g, src, CEval{a}, Con{FReach{policy}, k})
            case A.EFilter{kind, a}:
              Ev.go(g, src, CEval{a}, Con{FFilter{kind}, k})

def Ev.set(+src: Idx.Source, e: A.SetExpr) -> Val:
  +ee = e
  Ev.go(1n+Nat.mul(4n, Ev.size(ee)), src, CEval{ee}, Nil{})

def Ev.run(+src: Idx.Source, e: A.SetExpr) -> Val:
  Ev.set(src, Rw.Rw.simplify(e))

# ---------------------------------------------------------------------------
# Statistics over a set, and fused over a difference.
# ---------------------------------------------------------------------------

def Ev.stats.meta(+m: Im.Meta) -> A.Stats:
  A.Stats.of_kind(U32.to_nat(Im.Meta.size(m)), Im.Meta.kind(m))

def Ev.stats.one(+src: Idx.Source, +x: U32) -> A.Stats:
  Ev.stats.meta(Idx.Source.meta_of(src, x))

def Ev.stats.of(+src: Idx.Source, xs: List<&2, U32>, acc: A.Stats) ->
  A.Stats:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      Ev.stats.of(src, t, A.Stats.add(acc, Ev.stats.one(src, x)))

def Ev.stats(+src: Idx.Source, s: S.PSet) -> A.Stats:
  Ev.stats.of(src, S.PSet.to_list(20n, s), A.Stats.zero())

# The fused reduction of SPEC 7.2: the statistics of `a \ b` without
# allocating `a \ b`. `PSet.diff_members` walks the two trees together,
# prunes whole intervals where an operand is Zero or Full, and yields only
# the members of the difference.
def Ev.missing_stats(+src: Idx.Source, a: S.PSet, b: S.PSet) ->
  A.Stats:
  Ev.stats.of(src, S.PSet.missing(20n, a, b), A.Stats.zero())

# Counting only -- no weights, so this never leaves the word kernel:
# popcount(required AND NOT have), accumulated over the tiles.
def Ev.missing_count(a: S.PSet, b: S.PSet) -> Nat:
  S.PSet.missing_count(20n, a, b)

# Readiness: stops at the first required object the inventory lacks.
def Ev.ready(a: S.PSet, b: S.PSet) -> Bool:
  S.PSet.is_subset(20n, a, b)
