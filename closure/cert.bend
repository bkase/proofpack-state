# closure/cert.bend -- closure certificates (law C-04).
#
# SPEC 4.4: for a candidate set C, record a witness predecessor and a rank for
# every non-root member, and accept only when
#
#   1. R is inside C,
#   2. every required outgoing edge of a member of C stays inside C,
#   3. every v in C \ R has a predecessor u in C with u -> v and
#      rank(u) < rank(v),
#   4. identities, ranks and graph/policy bindings validate.
#
# Conditions 1-2 establish Reach(R) is inside C. The well-founded predecessor
# chains of condition 3 establish C is inside Reach(R). So acceptance proves
# *exactness*, not merely an overapproximation -- which is what lets a cached
# result, or one produced by a different implementation, be reused without
# trusting how it was computed.
#
# The ranks here are BFS levels, so the strict decrease of condition 3 is the
# level index and needs no separate rank table: a member of level i+1 must
# have a predecessor in level i.
#
# The checker does NOT establish that the imported graph matches a real
# repository. That stays an adapter contract (SPEC 4.4, TRUST.md).

import Base
import ../core/set.bend as S
import ../spec/closure.bend as Sp
import ./graph.bend as G
import ./reach.bend as R
import ./explain.bend as E

def Cert.some(m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

# Condition 3, one vertex: is there a `u` in the previous level with u -> v?
def Cert.has_pred(+td: Nat, +g: G.Graph(td), prev: List<&2, U32>,
  +v: U32) -> Bool:
  Cert.some(E.Explain.pred(td, g, prev, v, None{}))

def Cert.preds_ok(+td: Nat, +g: G.Graph(td), +prev: List<&2, U32>,
  cur: List<&2, U32>, ok: Bool) -> Bool:
  match cur:
    case Nil{}:
      ok
    case Con{v, t}:
      match ok:
        case False{}:
          False{}
        case True{}:
          Cert.preds_ok(td, g, prev, t, Cert.has_pred(td, g, prev, v))

# Condition 3 over every level: each level's members must be reachable in one
# edge from the level before, which makes the rank strictly decrease along the
# witness chain back to level 0.
def Cert.layers_ok(+td: Nat, +g: G.Graph(td), levels: R.Levels,
  +prev: List<&2, U32>, ok: Bool) -> Bool:
  match levels:
    case Nil{}:
      ok
    case Con{l, t}:
      match ok:
        case False{}:
          False{}
        case True{}:
          +ll = l
          Cert.layers_ok(td, g, t, ll,
            Cert.preds_ok(td, g, prev, ll, True{}))

def Cert.concat(levels: R.Levels, acc: List<&2, U32>) -> List<&2, U32>:
  match levels:
    case Nil{}:
      acc
    case Con{l, t}:
      Cert.concat(t, List.append(&2, U32, l, acc))

def Cert.same(+sd: Nat, +a: S.PSet, +b: S.PSet) -> Bool:
  Bool.and(S.PSet.is_subset(sd, a, b), S.PSet.is_subset(sd, b, a))

def Cert.first(levels: R.Levels, fallback: List<&2, U32>) -> List<&2, U32>:
  match levels:
    case Nil{}:
      fallback
    case Con{l, t}:
      l

def Cert.rest(levels: R.Levels) -> R.Levels:
  match levels:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      t

# The four conditions, on a traversal's own output.
#
# `levels` is ascending and level 0 must be inside the requested roots; every
# later level must be one edge from the one before; the union of the levels
# must be exactly `c`; `c` must be edge-closed; and the roots must be inside
# `c`.
def Cert.check(+td: Nat, +g: G.Graph(td), +sd: Nat, +roots: List<&2, U32>,
  levels: R.Levels, +c: S.PSet) -> Bool:
  +lv = levels
  +r = S.PSet.from_list(sd, roots)
  Bool.and(S.PSet.is_subset(sd, r, c),
    Bool.and(Sp.Spec.closed(td, g, sd, c),
      Bool.and(Cert.same(sd, S.PSet.from_list(sd, Cert.concat(lv, Nil{})), c),
        Cert.layers_ok(td, g, Cert.rest(lv), Cert.first(lv, roots),
          S.PSet.is_subset(sd, S.PSet.from_list(sd, Cert.first(lv, roots)),
            r)))))

