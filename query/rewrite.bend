# query/rewrite.bend -- semantics-preserving rewrites (law Q-01).
#
# Every rewrite here is admitted because a law says its denotation is
# unchanged; `OPTIMIZATIONS.md` names the law for each, and `PROOF.bend`
# discharges them pointwise over `PSet.mem`.
#
# What is *not* here matters as much as what is. SPEC 4.1 forbids, in
# general:
#
#     C(A n B) = C(A) n C(B)
#     C(A \ B) = C(A) \ C(B)
#
# with the counterexample a -> x, b -> x: the closures of {a} and {b} meet at
# x although the root sets do not, and closing {a} \ {b} keeps x while
# subtracting the closures removes it. It also forbids pushing a type filter
# through reachability without a separately proved graph-policy
# transformation, because dropping commit vertices before traversal erases
# the paths to the blobs they require.
#
# Those three rewrites are absent by construction, and
# `tests/forbidden.bend` runs the counterexamples so that adding one later
# fails the build rather than quietly changing answers.
#
# Validation happens before this module runs, not inside it: a literal
# carries its set value, so simplifying `Difference(q, q)` cannot hide an
# unresolved input (SPEC 3.5).

import Base
import ../core/count.bend as C
import ../core/set.bend as S
import ../index/source.bend as Idx
import ./ast.bend as A

def Rw.is_empty_expr(e: A.SetExpr) -> Bool:
  match e:
    case A.EEmpty{}:
      True{}
    case A.EFull{}:
      False{}
    case A.ELit{set}:
      S.PSet.empty_p(20n, set)
    case A.EUnion{a, b}:
      False{}
    case A.EInter{a, b}:
      False{}
    case A.EDiff{a, b}:
      False{}
    case A.EReach{policy, a}:
      False{}
    case A.EFilter{kind, a}:
      False{}

# --- union: Empty is the identity (law S-04) -------------------------------

def Rw.union(a: A.SetExpr, b: A.SetExpr, ea: Bool, eb: Bool) -> A.SetExpr:
  match ea:
    case True{}:
      b
    case False{}:
      match eb:
        case True{}:
          a
        case False{}:
          A.EUnion{a, b}

# --- intersection: Empty absorbs (law S-04) --------------------------------

def Rw.inter(a: A.SetExpr, b: A.SetExpr, ea: Bool, eb: Bool) -> A.SetExpr:
  match ea:
    case True{}:
      A.EEmpty{}
    case False{}:
      match eb:
        case True{}:
          A.EEmpty{}
        case False{}:
          A.EInter{a, b}

# --- difference: A \ Empty = A, Empty \ B = Empty (law S-04, M-03) ---------

def Rw.diff(a: A.SetExpr, b: A.SetExpr, ea: Bool, eb: Bool) -> A.SetExpr:
  match ea:
    case True{}:
      A.EEmpty{}
    case False{}:
      match eb:
        case True{}:
          a
        case False{}:
          A.EDiff{a, b}

# --- reachability ----------------------------------------------------------
#
# C(empty) = empty, and C(A u B) = C(A) u C(B) (law C-03). Closure preserves
# finite unions; it is not a Boolean-algebra homomorphism, and the two
# rewrites this module does *not* do are why.

def Rw.reach(p: Idx.Policy, a: A.SetExpr, ea: Bool) -> A.SetExpr:
  match ea:
    case True{}:
      A.EEmpty{}
    case False{}:
      A.EReach{p, a}

def Rw.reach.split(+p: Idx.Policy, a: A.SetExpr) -> A.SetExpr:
  match a:
    case A.EUnion{x, y}:
      A.EUnion{A.EReach{p, x}, A.EReach{p, y}}
    case A.EEmpty{}:
      A.EEmpty{}
    case A.EFull{}:
      A.EReach{p, A.EFull{}}
    case A.ELit{set}:
      A.EReach{p, A.ELit{set}}
    case A.EInter{x, y}:
      A.EReach{p, A.EInter{x, y}}
    case A.EDiff{x, y}:
      A.EReach{p, A.EDiff{x, y}}
    case A.EReach{q, x}:
      A.EReach{p, A.EReach{q, x}}
    case A.EFilter{k, x}:
      A.EReach{p, A.EFilter{k, x}}

# --- the pass --------------------------------------------------------------

def Rw.join.go(+a: A.SetExpr, +b: A.SetExpr, op: Nat) -> A.SetExpr:
  match op:
    case 0n:
      Rw.union(a, b, Rw.is_empty_expr(a), Rw.is_empty_expr(b))
    case 1n+x:
      match x:
        case 0n:
          Rw.inter(a, b, Rw.is_empty_expr(a), Rw.is_empty_expr(b))
        case 1n+y:
          Rw.diff(a, b, Rw.is_empty_expr(a), Rw.is_empty_expr(b))

def Rw.join(a: A.SetExpr, b: A.SetExpr, +op: U32) -> A.SetExpr:
  Rw.join.go(a, b, U32.to_nat(op))

def Rw.close(p: Idx.Policy, +a: A.SetExpr) -> A.SetExpr:
  Rw.reach(p, a, Rw.is_empty_expr(a))

def Rw.simplify(e: A.SetExpr) -> A.SetExpr:
  match e:
    case A.EEmpty{}:
      A.EEmpty{}
    case A.EFull{}:
      A.EFull{}
    case A.ELit{set}:
      A.ELit{set}
    case A.EUnion{a, b}:
      Rw.join(Rw.simplify(a), Rw.simplify(b), 0)
    case A.EInter{a, b}:
      Rw.join(Rw.simplify(a), Rw.simplify(b), 1)
    case A.EDiff{a, b}:
      Rw.join(Rw.simplify(a), Rw.simplify(b), 2)
    case A.EReach{policy, a}:
      Rw.close(policy, Rw.simplify(a))
    case A.EFilter{kind, a}:
      A.EFilter{kind, Rw.simplify(a)}

