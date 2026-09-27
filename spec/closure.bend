# spec/closure.bend -- the authoritative reachability semantics.
#
# SPEC 3.3 defines C_G(R) = mu X. R u post_G(X), the least edge-closed set
# containing R, and says a simple executable specification starts with X0 = R
# and applies X(k+1) = Xk u post(Xk) until stable. That is exactly what
# `Spec.iter` below does, in the production set representation but with no
# frontier, no certificate and no pruning: it is the oracle the optimized
# traversal in closure/reach.bend is checked against, and the definition every
# closure law in LAWS.bend is stated over.
#
# It is deliberately slow. Each round recomputes post over the whole set.

import Base
import ../core/count.bend as C
import ../core/set.bend as S
import ../closure/graph.bend as G

# post_G(X): the successors of every member of X.
def Spec.post(+td: Nat, +g: G.Graph(), +sd: Nat, +x: S.PSet) ->
  S.PSet:
  G.Graph.post(td, g, sd, S.PSet.to_list(sd, x))

# One round of the fixed-point iteration.
def Spec.step(+td: Nat, +g: G.Graph(), +sd: Nat, +x: S.PSet) ->
  S.PSet:
  S.PSet.union(sd, x, Spec.post(td, g, sd, x))

# `fuel` rounds of it. On a universe of size N at most N strict-growth rounds
# are possible, so `Spec.closure` passes N+1 and the result is stable.
def Spec.iter(+fuel: Nat, +td: Nat, +g: G.Graph(), +sd: Nat,
  x: S.PSet) -> S.PSet:
  match fuel:
    case 0n:
      x
    case 1n+f:
      Spec.iter(f, td, g, sd, Spec.step(td, g, sd, x))

def Spec.closure(+n: Nat, +td: Nat, +g: G.Graph(), +sd: Nat,
  r: S.PSet) -> S.PSet:
  Spec.iter(1n+n, td, g, sd, r)

# ---------------------------------------------------------------------------
# The two predicates the least-fixed-point characterisation is stated with.
# ---------------------------------------------------------------------------

# Is X edge-closed: does every successor of a member stay inside X?
def Spec.closed(+td: Nat, +g: G.Graph(), +sd: Nat, +x: S.PSet) -> Bool:
  S.PSet.is_subset(sd, Spec.post(td, g, sd, x), x)

# Is every member of A also a member of B?
def Spec.contains(+sd: Nat, +a: S.PSet, +b: S.PSet) -> Bool:
  S.PSet.is_subset(sd, a, b)
