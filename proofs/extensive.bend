# proofs/extensive.bend -- the closure contains what it closes (C-03, part).
#
# SPEC 3.3's closure is extensive: C(R) contains R. The registry states that
# with `PSet.is_subset`, which is a count and not a membership test, and
# relating a count to membership needs the set-level fused-count theorem this
# release has not written. Stated pointwise -- every member of R is a member
# of C(R) -- it needs none of that, and it is the form every other set law in
# LAWS.bend is stated in.
#
# The proof is one round plus induction on the fuel. A round is
# `X |-> X u post(X)`, and union is pointwise, so a member of `X` is a member
# of the round's result whatever `post` contributed. The shape hypothesis
# travels with it: `post` builds a set from a list, so the next round's
# operand is well shaped again.

import Base
import ./eq.bend as E
import ./shape.bend as Sh
import ./setops.bend as So
import ./preserve.bend as Pr
import ./denote.bend as Dn
import ../core/set.bend as S
import ../closure/graph.bend as G
import ../spec/closure.bend as Sp

law Spec.step_keeps_a_member:
  for +td: Nat
  for +g: G.Graph()
  for +r: S.PSet
  for +x: U32
  for +v: {Sh.PSet.wf(20n, r, True{}) == True{} : Bool}
  for +m: {S.PSet.member(20n, r, x) == True{} : Bool}
  {S.PSet.member(20n, Sp.Spec.step(td, g, 20n, r), x) == True{} : Bool}

def Spec.step_keeps_a_member(td, g, r, x, v, m):
  %E.Bool.sym(
    S.PSet.member(20n,
      S.PSet.union(20n, r, Sp.Spec.post(td, g, 20n, r)), x),
    Bool.or(S.PSet.member(20n, r, x),
      S.PSet.member(20n, Sp.Spec.post(td, g, 20n, r), x)),
    So.PSet.union_member(r, Sp.Spec.post(td, g, 20n, r), x, v,
      Dn.Spec.wf_post(td, g, 20n, r)))
    : {_ == True{} : Bool}
  %E.Bool.sym(S.PSet.member(20n, r, x), True{}, m)
    : {Bool.or(_, S.PSet.member(20n, Sp.Spec.post(td, g, 20n, r), x))
      == True{} : Bool}
  {==}

law Spec.iter_keeps_a_member:
  for +fuel: Nat
  for +td: Nat
  for +g: G.Graph()
  for +r: S.PSet
  for +x: U32
  for +v: {Sh.PSet.wf(20n, r, True{}) == True{} : Bool}
  for +m: {S.PSet.member(20n, r, x) == True{} : Bool}
  {S.PSet.member(20n, Sp.Spec.iter(fuel, td, g, 20n, r), x)
    == True{} : Bool}

def Spec.iter_keeps_a_member(fuel, td, g, r, x, v, m):
  match fuel:
    case 0n:
      m
    case 1n+f:
      Spec.iter_keeps_a_member(f, td, g, Sp.Spec.step(td, g, 20n, r), x,
        Dn.Spec.wf_step(td, g, 20n, r, v),
        Spec.step_keeps_a_member(td, g, r, x, v, m))

law Spec.closure_contains_its_roots:
  for +n: Nat
  for +td: Nat
  for +g: G.Graph()
  for +r: S.PSet
  for +x: U32
  for +v: {Sh.PSet.wf(20n, r, True{}) == True{} : Bool}
  for +m: {S.PSet.member(20n, r, x) == True{} : Bool}
  {S.PSet.member(20n, Sp.Spec.closure(n, td, g, 20n, r), x)
    == True{} : Bool}

def Spec.closure_contains_its_roots(n, td, g, r, x, v, m):
  Spec.iter_keeps_a_member(1n+n, td, g, r, x, v, m)

# ---------------------------------------------------------------------------
# C-01, in part -- a round that changes nothing has reached a closed set.
#
# The fixed-point half of C-01 is that the iteration is stable after `n`
# rounds, which needs a pigeonhole argument over the universe and is still
# open. This is the other half of what "fixed point" means, and it needs no
# counting: *if* a round changes nothing, then what it changed nothing about
# is edge-closed -- every successor of a member is a member.
#
# It is stated pointwise, as every set law here is, and the hypothesis is a
# value equality rather than a membership test, which is what a runtime check
# can actually observe: `Spec.step` returns the operand it was given.
# ---------------------------------------------------------------------------

def PSet.member_at(+x: U32, s: S.PSet) -> Bool:
  S.PSet.member(20n, s, x)

law Spec.stable_is_closed:
  for +td: Nat
  for +g: G.Graph()
  for +xs: S.PSet
  for +v: U32
  for +w: {Sh.PSet.wf(20n, xs, True{}) == True{} : Bool}
  for +st: {Sp.Spec.step(td, g, 20n, xs) == xs : S.PSet}
  for +mp: {S.PSet.member(20n, Sp.Spec.post(td, g, 20n, xs), v)
    == True{} : Bool}
  {S.PSet.member(20n, xs, v) == True{} : Bool}

law Spec.or_right:
  for +p: Bool
  for +q: Bool
  for +ok: {q == True{} : Bool}
  {Bool.or(p, q) == True{} : Bool}

def Spec.or_right(p, q, ok):
  match p:
    case True{}:
      {==}
    case False{}:
      ok

def Spec.stable_is_closed(td, g, xs, v, w, st, mp):
  Equal.trans(Bool, S.PSet.member(20n, xs, v),
    Bool.or(S.PSet.member(20n, xs, v),
      S.PSet.member(20n, Sp.Spec.post(td, g, 20n, xs), v)), True{},
    Equal.trans(Bool, S.PSet.member(20n, xs, v),
      S.PSet.member(20n,
        S.PSet.union(20n, xs, Sp.Spec.post(td, g, 20n, xs)), v),
      Bool.or(S.PSet.member(20n, xs, v),
        S.PSet.member(20n, Sp.Spec.post(td, g, 20n, xs), v)),
      Equal.cong(S.PSet, Bool, PSet.member_at(v), xs,
        S.PSet.union(20n, xs, Sp.Spec.post(td, g, 20n, xs)),
        Equal.sym(S.PSet,
          S.PSet.union(20n, xs, Sp.Spec.post(td, g, 20n, xs)), xs, st)),
      So.PSet.union_member(xs, Sp.Spec.post(td, g, 20n, xs), v, w,
        Dn.Spec.wf_post(td, g, 20n, xs))),
    Spec.or_right(S.PSet.member(20n, xs, v),
      S.PSet.member(20n, Sp.Spec.post(td, g, 20n, xs), v), mp))
