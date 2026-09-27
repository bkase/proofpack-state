# proofs/closure.bend -- closure preserves emptiness (law C-03, in part).
#
# SPEC 3.3 defines the closure as the least fixed point of X |-> X u post(X)
# started from the roots, and `spec/closure.bend` computes it by iterating
# that map. Closing nothing gives nothing: there is no member to follow an
# edge from, so every round leaves the empty set where it was.
#
# The rest of C-03 -- extensivity, monotonicity, idempotence and union
# preservation -- is stated in LAWS.pending.bend. Those need the subset test
# to be related to membership, which needs the set-level fused count, and
# that is not proved.

import Base
import ./eq.bend as E
import ../core/count.bend as C
import ../core/set.bend as S
import ../closure/graph.bend as G
import ../spec/closure.bend as Sp

law Spec.step_empty:
  for +td: Nat
  for +g: G.Graph()
  for +p: Nat
  {Sp.Spec.step(td, g, 1n+p, S.PZero{}) == S.PZero{} : S.PSet}

def Spec.step_empty(td, g, p):
  {==}

law Spec.iter_empty:
  for +fuel: Nat
  for +td: Nat
  for +g: G.Graph()
  for +p: Nat
  {Sp.Spec.iter(fuel, td, g, 1n+p, S.PZero{}) == S.PZero{} : S.PSet}

def Spec.iter_empty(fuel, td, g, p):
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      %Spec.step_empty(td, g, p)
        : {Sp.Spec.iter(f, td, g, 1n+p, _) == S.PZero{} : S.PSet}
      Spec.iter_empty(f, td, g, p)

law Spec.closure_empty:
  for +n: Nat
  for +td: Nat
  for +g: G.Graph()
  for +p: Nat
  {Sp.Spec.closure(n, td, g, 1n+p, S.PZero{}) == S.PZero{} : S.PSet}

def Spec.closure_empty(n, td, g, p):
  Spec.iter_empty(1n+n, td, g, p)
