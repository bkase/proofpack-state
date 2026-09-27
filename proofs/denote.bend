# proofs/denote.bend -- every denotation is well shaped.
#
# The pointwise set laws take their operands' shape as a hypothesis. An
# induction over a query's syntax has to discharge that hypothesis at every
# node, and the operands there are not given values but results: a union of
# two subexpressions, a closure of a subexpression, a type filter. So the
# first thing such an induction needs is this -- that the denotation of any
# expression is well shaped, provided the literals written into the
# expression are.
#
# The proviso is not avoidable and is where the hypothesis stops: `ELit`
# carries a set value outright (query/ast.bend builds a literal only from a
# resolved, universe-checked name), so an expression can name a badly shaped
# set the same way a decoded file can. `SetExpr.wf_lits` is that condition,
# and everything else -- `Empty`, `Full`, the three Boolean operations,
# reachability and filtering -- is proved.
#
# Reachability is the interesting arm. The specification closure iterates
# `X |-> X u post(X)`, and `post` builds a set from a list of successors, so
# each round is a union of a well-shaped set with a set built by insertion:
# the two preservation results of proofs/preserve.bend, applied once per
# round of the iteration.

import Base
import ./eq.bend as E
import ./shape.bend as Sh
import ./preserve.bend as Pr
import ../core/set.bend as S
import ../closure/graph.bend as G
import ../spec/closure.bend as Sp
import ../spec/query.bend as Q
import ../query/ast.bend as A
import ../index/source.bend as Idx

# ---------------------------------------------------------------------------
# The specification closure.
# ---------------------------------------------------------------------------

law Spec.wf_post:
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +x: S.PSet
  {Sh.PSet.wf(sd, Sp.Spec.post(td, g, sd, x), True{}) == True{} : Bool}

def Spec.wf_post(td, g, sd, x):
  Pr.PSet.wf_from_list(sd,
    G.Graph.gather(td, g, S.PSet.to_list(sd, x), Nil{}))

law Spec.wf_step:
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +x: S.PSet
  for +v: {Sh.PSet.wf(sd, x, True{}) == True{} : Bool}
  {Sh.PSet.wf(sd, Sp.Spec.step(td, g, sd, x), True{}) == True{} : Bool}

def Spec.wf_step(td, g, sd, x, v):
  Pr.PSet.wf_union(sd, x, Sp.Spec.post(td, g, sd, x), v,
    Spec.wf_post(td, g, sd, x))

law Spec.wf_iter:
  for +fuel: Nat
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +x: S.PSet
  for +v: {Sh.PSet.wf(sd, x, True{}) == True{} : Bool}
  {Sh.PSet.wf(sd, Sp.Spec.iter(fuel, td, g, sd, x), True{})
    == True{} : Bool}

def Spec.wf_iter(fuel, td, g, sd, x, v):
  match fuel:
    case 0n:
      v
    case 1n+f:
      Spec.wf_iter(f, td, g, sd, Sp.Spec.step(td, g, sd, x),
        Spec.wf_step(td, g, sd, x, v))

law Spec.wf_closure:
  for +n: Nat
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +r: S.PSet
  for +v: {Sh.PSet.wf(sd, r, True{}) == True{} : Bool}
  {Sh.PSet.wf(sd, Sp.Spec.closure(n, td, g, sd, r), True{})
    == True{} : Bool}

def Spec.wf_closure(n, td, g, sd, r, v):
  Spec.wf_iter(1n+n, td, g, sd, r, v)

# ---------------------------------------------------------------------------
# The literals an expression carries.
# ---------------------------------------------------------------------------

def SetExpr.wf_lits(e: A.SetExpr) -> Bool:
  match e:
    case A.EEmpty{}:
      True{}
    case A.EFull{}:
      True{}
    case A.ELit{set}:
      Sh.PSet.wf(20n, set, True{})
    case A.EUnion{a, b}:
      Bool.and(SetExpr.wf_lits(a), SetExpr.wf_lits(b))
    case A.EInter{a, b}:
      Bool.and(SetExpr.wf_lits(a), SetExpr.wf_lits(b))
    case A.EDiff{a, b}:
      Bool.and(SetExpr.wf_lits(a), SetExpr.wf_lits(b))
    case A.EReach{policy, a}:
      SetExpr.wf_lits(a)
    case A.EFilter{kind, a}:
      SetExpr.wf_lits(a)

law Bool.and_left:
  for +a: Bool
  for +b: Bool
  for +ok: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def Bool.and_left(a, b, ok):
  match a:
    case True{}:
      {==}
    case False{}:
      ok

law Bool.and_right:
  for +a: Bool
  for +b: Bool
  for +ok: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def Bool.and_right(a, b, ok):
  match a:
    case True{}:
      ok
    case False{}:
      E.Bool.noconf({b == True{} : Bool}, ok)

# ---------------------------------------------------------------------------
# The denotation.
# ---------------------------------------------------------------------------

law Eval.wf:
  for +src: Idx.Source
  for +e: A.SetExpr
  for +ok: {SetExpr.wf_lits(e) == True{} : Bool}
  {Sh.PSet.wf(20n, Q.Den.eval(src, e), True{}) == True{} : Bool}

def Eval.wf(src, e, ok):
  match e:
    case A.EEmpty{}:
      Sh.PSet.wf_zero(20n)
    case A.EFull{}:
      Pr.PSet.wf_from_list(20n, Q.Den.upto(Idx.Source.n(src), Nil{}))
    case A.ELit{set}:
      ok
    case A.EUnion{a, b}:
      Pr.PSet.wf_union(20n, Q.Den.eval(src, a), Q.Den.eval(src, b),
        Eval.wf(src, a,
          Bool.and_left(SetExpr.wf_lits(a), SetExpr.wf_lits(b), ok)),
        Eval.wf(src, b,
          Bool.and_right(SetExpr.wf_lits(a), SetExpr.wf_lits(b), ok)))
    case A.EInter{a, b}:
      Pr.PSet.wf_inter(20n, Q.Den.eval(src, a), Q.Den.eval(src, b),
        Eval.wf(src, a,
          Bool.and_left(SetExpr.wf_lits(a), SetExpr.wf_lits(b), ok)),
        Eval.wf(src, b,
          Bool.and_right(SetExpr.wf_lits(a), SetExpr.wf_lits(b), ok)))
    case A.EDiff{a, b}:
      Pr.PSet.wf_diff(20n, Q.Den.eval(src, a), Q.Den.eval(src, b),
        Eval.wf(src, a,
          Bool.and_left(SetExpr.wf_lits(a), SetExpr.wf_lits(b), ok)),
        Eval.wf(src, b,
          Bool.and_right(SetExpr.wf_lits(a), SetExpr.wf_lits(b), ok)))
    case A.EReach{policy, a}:
      Spec.wf_closure(Idx.Source.n(src), 32n,
        Idx.Source.graph(src, policy), 20n, Q.Den.eval(src, a),
        Eval.wf(src, a, ok))
    case A.EFilter{kind, a}:
      Pr.PSet.wf_from_list(20n,
        Q.Den.keep(src, kind, S.PSet.to_list(20n, Q.Den.eval(src, a))))
