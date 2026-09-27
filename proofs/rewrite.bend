# proofs/rewrite.bend -- every admitted rewrite keeps the denotation (Q-01).
#
# `query/rewrite.bend` simplifies an expression before it is compiled. SPEC
# 3.5 admits a rewrite only if a law says the denotation is unchanged, and
# this file is those laws: for each rewrite the optimizer performs, the
# expression it produces has exactly the members the expression it replaced
# had -- at the production depth, for every ordinal, with no side condition
# beyond the operands being well shaped.
#
# The pattern is the same throughout. The rewriter decides with
# `Rw.is_empty_expr`, which answers `True{}` only for `Empty` itself and for
# a literal whose set has no members; the proofs carry that decision as a
# parameter with an equation naming it, because Bend matches parameters
# rather than computed values. Each arm is then one of the pointwise set laws
# with a `False{}` substituted on one side.
#
# Validation is not part of this: a literal carries its set value, so an
# expression with an unresolved input cannot be built in the first place, and
# no rewrite here can skip a check that has already happened. That is SPEC
# 3.5's "validation precedes elimination", and it is structural rather than
# proved.
#
# What is deliberately absent: the two closure rewrites SPEC 4.1 forbids --
# C(A n B) = C(A) n C(B) and C(A \ B) = C(A) \ C(B) -- and pushing a type
# filter through reachability. `tests/forbidden.bend` runs the
# counterexamples, so adding one later fails the build.

import Base
import ./eq.bend as E
import ./shape.bend as Sh
import ./setops.bend as So
import ./empty.bend as Em
import ./denote.bend as Dn
import ./nothing.bend as No
import ../core/set.bend as S
import ../spec/closure.bend as Sp
import ../spec/query.bend as Q
import ../query/ast.bend as A
import ../query/rewrite.bend as R
import ../index/source.bend as Idx

# ---------------------------------------------------------------------------
# What the rewriter's emptiness test means.
#
# `Rw.is_empty_expr` is a syntactic test with one semantic case: a literal,
# where it asks the set itself. Everything else it answers `False{}` for, so
# there is nothing to prove there and the hypothesis discharges the rest.
# ---------------------------------------------------------------------------

law Simp.empty_expr_is_empty:
  for +src: Idx.Source
  for +e: A.SetExpr
  for +z: {R.Rw.is_empty_expr(e) == True{} : Bool}
  {S.PSet.empty_p(20n, Q.Den.eval(src, e)) == True{} : Bool}

def Simp.empty_expr_is_empty(src, e, z):
  match e:
    case A.EEmpty{}:
      {==}
    case A.ELit{set}:
      z
    case A.EFull{}:
      E.Bool.noconf({S.PSet.empty_p(20n, Q.Den.eval(src, A.EFull{}))
        == True{} : Bool}, z)
    case A.EUnion{a, b}:
      E.Bool.noconf({S.PSet.empty_p(20n, Q.Den.eval(src, A.EUnion{a, b}))
        == True{} : Bool}, z)
    case A.EInter{a, b}:
      E.Bool.noconf({S.PSet.empty_p(20n, Q.Den.eval(src, A.EInter{a, b}))
        == True{} : Bool}, z)
    case A.EDiff{a, b}:
      E.Bool.noconf({S.PSet.empty_p(20n, Q.Den.eval(src, A.EDiff{a, b}))
        == True{} : Bool}, z)
    case A.EReach{p, a}:
      E.Bool.noconf({S.PSet.empty_p(20n, Q.Den.eval(src, A.EReach{p, a}))
        == True{} : Bool}, z)
    case A.EFilter{k, a}:
      E.Bool.noconf({S.PSet.empty_p(20n, Q.Den.eval(src, A.EFilter{k, a}))
        == True{} : Bool}, z)

law Simp.empty_expr_has_no_members:
  for +src: Idx.Source
  for +e: A.SetExpr
  for +x: U32
  for +z: {R.Rw.is_empty_expr(e) == True{} : Bool}
  {S.PSet.member(20n, Q.Den.eval(src, e), x) == False{} : Bool}

def Simp.empty_expr_has_no_members(src, e, x, z):
  match e:
    case A.EEmpty{}:
      {==}
    case A.ELit{set}:
      Em.PSet.empty_no_member(20n, set, S.PSet.half(20n), x, z,
        U32.is_lt(x, S.PSet.half(20n)), {==})
    case A.EFull{}:
      E.Bool.noconf({S.PSet.member(20n, Q.Den.eval(src, A.EFull{}), x)
        == False{} : Bool}, z)
    case A.EUnion{a, b}:
      E.Bool.noconf({S.PSet.member(20n, Q.Den.eval(src, A.EUnion{a, b}), x)
        == False{} : Bool}, z)
    case A.EInter{a, b}:
      E.Bool.noconf({S.PSet.member(20n, Q.Den.eval(src, A.EInter{a, b}), x)
        == False{} : Bool}, z)
    case A.EDiff{a, b}:
      E.Bool.noconf({S.PSet.member(20n, Q.Den.eval(src, A.EDiff{a, b}), x)
        == False{} : Bool}, z)
    case A.EReach{p, a}:
      E.Bool.noconf({S.PSet.member(20n, Q.Den.eval(src, A.EReach{p, a}), x)
        == False{} : Bool}, z)
    case A.EFilter{k, a}:
      E.Bool.noconf({S.PSet.member(20n, Q.Den.eval(src, A.EFilter{k, a}), x)
        == False{} : Bool}, z)

# ---------------------------------------------------------------------------
# Union: `Empty u B = B` and `A u Empty = A` (law S-04).
# ---------------------------------------------------------------------------

law Bool.or_false:
  for +p: Bool
  {Bool.or(p, False{}) == p : Bool}

def Bool.or_false(p):
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

law Simp.union_sound.on:
  for +src: Idx.Source
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +x: U32
  for +ea: Bool
  for +eb: Bool
  for +qa: {ea == R.Rw.is_empty_expr(a) : Bool}
  for +qb: {eb == R.Rw.is_empty_expr(b) : Bool}
  for +va: {Sh.PSet.wf(20n, Q.Den.eval(src, a), True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(20n, Q.Den.eval(src, b), True{}) == True{} : Bool}
  {S.PSet.member(20n, Q.Den.eval(src, R.Rw.union(a, b, ea, eb)), x)
    == S.PSet.member(20n, Q.Den.eval(src, A.EUnion{a, b}), x) : Bool}

def Simp.union_sound.on(src, a, b, x, ea, eb, qa, qb, va, vb):
  match ea:
    case True{}:
      %E.Bool.sym(S.PSet.member(20n,
          S.PSet.union(20n, Q.Den.eval(src, a), Q.Den.eval(src, b)), x),
        Bool.or(S.PSet.member(20n, Q.Den.eval(src, a), x),
          S.PSet.member(20n, Q.Den.eval(src, b), x)),
        So.PSet.union_member(Q.Den.eval(src, a), Q.Den.eval(src, b), x,
          va, vb))
        : {S.PSet.member(20n, Q.Den.eval(src, b), x) == _ : Bool}
      %E.Bool.sym(S.PSet.member(20n, Q.Den.eval(src, a), x), False{},
        Simp.empty_expr_has_no_members(src, a, x,
          E.Bool.sym(ea, R.Rw.is_empty_expr(a), qa)))
        : {S.PSet.member(20n, Q.Den.eval(src, b), x)
          == Bool.or(_, S.PSet.member(20n, Q.Den.eval(src, b), x)) : Bool}
      {==}
    case False{}:
      match eb:
        case True{}:
          %E.Bool.sym(S.PSet.member(20n,
              S.PSet.union(20n, Q.Den.eval(src, a), Q.Den.eval(src, b)), x),
            Bool.or(S.PSet.member(20n, Q.Den.eval(src, a), x),
              S.PSet.member(20n, Q.Den.eval(src, b), x)),
            So.PSet.union_member(Q.Den.eval(src, a), Q.Den.eval(src, b), x,
              va, vb))
            : {S.PSet.member(20n, Q.Den.eval(src, a), x) == _ : Bool}
          %E.Bool.sym(S.PSet.member(20n, Q.Den.eval(src, b), x), False{},
            Simp.empty_expr_has_no_members(src, b, x,
              E.Bool.sym(eb, R.Rw.is_empty_expr(b), qb)))
            : {S.PSet.member(20n, Q.Den.eval(src, a), x)
              == Bool.or(S.PSet.member(20n, Q.Den.eval(src, a), x), _)
              : Bool}
          E.Bool.sym(
            Bool.or(S.PSet.member(20n, Q.Den.eval(src, a), x), False{}),
            S.PSet.member(20n, Q.Den.eval(src, a), x),
            Bool.or_false(S.PSet.member(20n, Q.Den.eval(src, a), x)))
        case False{}:
          {==}

law Simp.union_sound:
  for +src: Idx.Source
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +x: U32
  for +va: {Sh.PSet.wf(20n, Q.Den.eval(src, a), True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(20n, Q.Den.eval(src, b), True{}) == True{} : Bool}
  {S.PSet.member(20n, Q.Den.eval(src,
      R.Rw.union(a, b, R.Rw.is_empty_expr(a), R.Rw.is_empty_expr(b))), x)
    == S.PSet.member(20n, Q.Den.eval(src, A.EUnion{a, b}), x) : Bool}

def Simp.union_sound(src, a, b, x, va, vb):
  Simp.union_sound.on(src, a, b, x, R.Rw.is_empty_expr(a),
    R.Rw.is_empty_expr(b), {==}, {==}, va, vb)

law Bool.and_false:
  for +p: Bool
  {Bool.and(p, False{}) == False{} : Bool}

def Bool.and_false(p):
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

law Bool.and_true:
  for +p: Bool
  {Bool.and(p, True{}) == p : Bool}

def Bool.and_true(p):
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

# ---------------------------------------------------------------------------
# Intersection: `Empty n B = Empty` and `A n Empty = Empty` (law S-04).
# ---------------------------------------------------------------------------

law Simp.inter_sound.on:
  for +src: Idx.Source
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +x: U32
  for +ea: Bool
  for +eb: Bool
  for +qa: {ea == R.Rw.is_empty_expr(a) : Bool}
  for +qb: {eb == R.Rw.is_empty_expr(b) : Bool}
  for +va: {Sh.PSet.wf(20n, Q.Den.eval(src, a), True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(20n, Q.Den.eval(src, b), True{}) == True{} : Bool}
  {S.PSet.member(20n, Q.Den.eval(src, R.Rw.inter(a, b, ea, eb)), x)
    == S.PSet.member(20n, Q.Den.eval(src, A.EInter{a, b}), x) : Bool}

def Simp.inter_sound.on(src, a, b, x, ea, eb, qa, qb, va, vb):
  match ea:
    case True{}:
      %E.Bool.sym(S.PSet.member(20n,
          S.PSet.inter(20n, Q.Den.eval(src, a), Q.Den.eval(src, b)), x),
        Bool.and(S.PSet.member(20n, Q.Den.eval(src, a), x),
          S.PSet.member(20n, Q.Den.eval(src, b), x)),
        So.PSet.inter_member(Q.Den.eval(src, a), Q.Den.eval(src, b), x,
          va, vb))
        : {False{} == _ : Bool}
      %E.Bool.sym(S.PSet.member(20n, Q.Den.eval(src, a), x), False{},
        Simp.empty_expr_has_no_members(src, a, x,
          E.Bool.sym(ea, R.Rw.is_empty_expr(a), qa)))
        : {False{} == Bool.and(_,
            S.PSet.member(20n, Q.Den.eval(src, b), x)) : Bool}
      {==}
    case False{}:
      match eb:
        case True{}:
          %E.Bool.sym(S.PSet.member(20n,
              S.PSet.inter(20n, Q.Den.eval(src, a), Q.Den.eval(src, b)), x),
            Bool.and(S.PSet.member(20n, Q.Den.eval(src, a), x),
              S.PSet.member(20n, Q.Den.eval(src, b), x)),
            So.PSet.inter_member(Q.Den.eval(src, a), Q.Den.eval(src, b), x,
              va, vb))
            : {False{} == _ : Bool}
          %E.Bool.sym(S.PSet.member(20n, Q.Den.eval(src, b), x), False{},
            Simp.empty_expr_has_no_members(src, b, x,
              E.Bool.sym(eb, R.Rw.is_empty_expr(b), qb)))
            : {False{} == Bool.and(
                S.PSet.member(20n, Q.Den.eval(src, a), x), _) : Bool}
          E.Bool.sym(
            Bool.and(S.PSet.member(20n, Q.Den.eval(src, a), x), False{}),
            False{},
            Bool.and_false(S.PSet.member(20n, Q.Den.eval(src, a), x)))
        case False{}:
          {==}

law Simp.inter_sound:
  for +src: Idx.Source
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +x: U32
  for +va: {Sh.PSet.wf(20n, Q.Den.eval(src, a), True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(20n, Q.Den.eval(src, b), True{}) == True{} : Bool}
  {S.PSet.member(20n, Q.Den.eval(src,
      R.Rw.inter(a, b, R.Rw.is_empty_expr(a), R.Rw.is_empty_expr(b))), x)
    == S.PSet.member(20n, Q.Den.eval(src, A.EInter{a, b}), x) : Bool}

def Simp.inter_sound(src, a, b, x, va, vb):
  Simp.inter_sound.on(src, a, b, x, R.Rw.is_empty_expr(a),
    R.Rw.is_empty_expr(b), {==}, {==}, va, vb)

# ---------------------------------------------------------------------------
# Difference: `Empty \ B = Empty` and `A \ Empty = A` (laws S-04, M-03).
# ---------------------------------------------------------------------------

law Simp.diff_sound.on:
  for +src: Idx.Source
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +x: U32
  for +ea: Bool
  for +eb: Bool
  for +qa: {ea == R.Rw.is_empty_expr(a) : Bool}
  for +qb: {eb == R.Rw.is_empty_expr(b) : Bool}
  for +va: {Sh.PSet.wf(20n, Q.Den.eval(src, a), True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(20n, Q.Den.eval(src, b), True{}) == True{} : Bool}
  {S.PSet.member(20n, Q.Den.eval(src, R.Rw.diff(a, b, ea, eb)), x)
    == S.PSet.member(20n, Q.Den.eval(src, A.EDiff{a, b}), x) : Bool}

def Simp.diff_sound.on(src, a, b, x, ea, eb, qa, qb, va, vb):
  match ea:
    case True{}:
      %E.Bool.sym(S.PSet.member(20n,
          S.PSet.diff(20n, Q.Den.eval(src, a), Q.Den.eval(src, b)), x),
        Bool.and(S.PSet.member(20n, Q.Den.eval(src, a), x),
          Bool.not(S.PSet.member(20n, Q.Den.eval(src, b), x))),
        So.PSet.diff_member(Q.Den.eval(src, a), Q.Den.eval(src, b), x,
          va, vb))
        : {False{} == _ : Bool}
      %E.Bool.sym(S.PSet.member(20n, Q.Den.eval(src, a), x), False{},
        Simp.empty_expr_has_no_members(src, a, x,
          E.Bool.sym(ea, R.Rw.is_empty_expr(a), qa)))
        : {False{} == Bool.and(_,
            Bool.not(S.PSet.member(20n, Q.Den.eval(src, b), x))) : Bool}
      {==}
    case False{}:
      match eb:
        case True{}:
          %E.Bool.sym(S.PSet.member(20n,
              S.PSet.diff(20n, Q.Den.eval(src, a), Q.Den.eval(src, b)), x),
            Bool.and(S.PSet.member(20n, Q.Den.eval(src, a), x),
              Bool.not(S.PSet.member(20n, Q.Den.eval(src, b), x))),
            So.PSet.diff_member(Q.Den.eval(src, a), Q.Den.eval(src, b), x,
              va, vb))
            : {S.PSet.member(20n, Q.Den.eval(src, a), x) == _ : Bool}
          %E.Bool.sym(S.PSet.member(20n, Q.Den.eval(src, b), x), False{},
            Simp.empty_expr_has_no_members(src, b, x,
              E.Bool.sym(eb, R.Rw.is_empty_expr(b), qb)))
            : {S.PSet.member(20n, Q.Den.eval(src, a), x)
              == Bool.and(S.PSet.member(20n, Q.Den.eval(src, a), x),
                   Bool.not(_)) : Bool}
          E.Bool.sym(
            Bool.and(S.PSet.member(20n, Q.Den.eval(src, a), x), True{}),
            S.PSet.member(20n, Q.Den.eval(src, a), x),
            Bool.and_true(S.PSet.member(20n, Q.Den.eval(src, a), x)))
        case False{}:
          {==}

law Simp.diff_sound:
  for +src: Idx.Source
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +x: U32
  for +va: {Sh.PSet.wf(20n, Q.Den.eval(src, a), True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(20n, Q.Den.eval(src, b), True{}) == True{} : Bool}
  {S.PSet.member(20n, Q.Den.eval(src,
      R.Rw.diff(a, b, R.Rw.is_empty_expr(a), R.Rw.is_empty_expr(b))), x)
    == S.PSet.member(20n, Q.Den.eval(src, A.EDiff{a, b}), x) : Bool}

def Simp.diff_sound(src, a, b, x, va, vb):
  Simp.diff_sound.on(src, a, b, x, R.Rw.is_empty_expr(a),
    R.Rw.is_empty_expr(b), {==}, {==}, va, vb)

# ---------------------------------------------------------------------------
# Reachability: `Reach(p, Empty) = Empty` (law C-03).
#
# The one rewrite here that is not a Boolean identity, and the only one that
# needs to know something about the traversal rather than about the set
# algebra: closing a set with no members gives a set with no members
# (proofs/nothing.bend).
# ---------------------------------------------------------------------------

law Simp.reach_sound.on:
  for +src: Idx.Source
  for +p: Idx.Policy
  for +a: A.SetExpr
  for +x: U32
  for +ea: Bool
  for +qa: {ea == R.Rw.is_empty_expr(a) : Bool}
  {S.PSet.member(20n, Q.Den.eval(src, R.Rw.reach(p, a, ea)), x)
    == S.PSet.member(20n, Q.Den.eval(src, A.EReach{p, a}), x) : Bool}

def Simp.reach_sound.on(src, p, a, x, ea, qa):
  match ea:
    case True{}:
      E.Bool.sym(
        S.PSet.member(20n, Q.Den.eval(src, A.EReach{p, a}), x), False{},
        Em.PSet.empty_no_member(20n,
          Sp.Spec.closure(Idx.Source.n(src), 32n,
            Idx.Source.graph(src, p), 20n, Q.Den.eval(src, a)),
          S.PSet.half(20n), x,
          No.Spec.closure_of_empty(Idx.Source.n(src), 32n,
            Idx.Source.graph(src, p), 19n, Q.Den.eval(src, a),
            Simp.empty_expr_is_empty(src, a,
              E.Bool.sym(ea, R.Rw.is_empty_expr(a), qa))),
          U32.is_lt(x, S.PSet.half(20n)), {==}))
    case False{}:
      {==}

law Simp.reach_sound:
  for +src: Idx.Source
  for +p: Idx.Policy
  for +a: A.SetExpr
  for +x: U32
  {S.PSet.member(20n, Q.Den.eval(src,
      R.Rw.reach(p, a, R.Rw.is_empty_expr(a))), x)
    == S.PSet.member(20n, Q.Den.eval(src, A.EReach{p, a}), x) : Bool}

def Simp.reach_sound(src, p, a, x):
  Simp.reach_sound.on(src, p, a, x, R.Rw.is_empty_expr(a), {==})
