# proofs/rwpass.bend -- the whole optimizer pass, not just its rewrites.
#
# Each rewrite `Rw.simplify` performs is already proved to keep every member
# (proofs/rewrite.bend). What was open is the pass: `Rw.simplify` also
# recurses *inside* `Reach` and `Filter`, and there the induction needs
# something the per-rewrite laws do not give -- that a subexpression which
# has been simplified to a set with the same *members*, not the same
# representation, closes and filters to a set with the same members.
#
# That is a congruence, and it needs an equality on sets a proof can carry.
# `PSet.same` -- mutual `PSet.is_subset` -- is that equality, and the bridge
# from "these two sets agree at every ordinal either enumerates" to
# `PSet.same` is what lets the per-rewrite laws, which are pointwise, be used
# inside it.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./shape.bend as Sh
import ./shift.bend as Sf
import ./subsetconv.bend as Sc
import ./subsetalg.bend as Sa
import ./setops.bend as So
import ./split_add.bend as Sa2
import ./validshape.bend as Vs
import ./validkeep.bend as Vk
import ./insertvalid.bend as Iv
import ./listset.bend as Ls
import ./graphrange.bend as Gr
import ./lfp.bend as Lp
import ./closalg.bend as Ca
import ./denote.bend as Dn
import ./rewrite.bend as Rs
import ../core/count.bend as C
import ../core/set.bend as S
import ../query/ast.bend as A
import ../query/rewrite.bend as R
import ../spec/query.bend as Q
import ../spec/closure.bend as Sp
import ../closure/graph.bend as G
import ../index/source.bend as Idx
import ../adapters/git/import.bend as Im

# ---------------------------------------------------------------------------
# From pointwise agreement to `PSet.same`.
# ---------------------------------------------------------------------------

def Bool.same(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

law Bool.same_of_eq:
  for +a: Bool
  for +b: Bool
  for +e: {a == b : Bool}
  {Bool.same(a, b) == True{} : Bool}

def Bool.same_of_eq(a, b, e):
  match a:
    case True{}:
      E.Bool.sym(True{}, b, e)
    case False{}:
      %e : {Bool.not(_) == True{} : Bool}
      {==}

law Bool.on_of_same:
  for +a: Bool
  for +b: Bool
  for +ea: {a == True{} : Bool}
  for +sm: {Bool.same(a, b) == True{} : Bool}
  {b == True{} : Bool}

def Bool.on_of_same(a, b, ea, sm):
  match a:
    case True{}:
      sm
    case False{}:
      E.Bool.noconf({b == True{} : Bool}, ea)

law Bool.on_of_same_r:
  for +a: Bool
  for +b: Bool
  for +eb: {b == True{} : Bool}
  for +sm: {Bool.same(a, b) == True{} : Bool}
  {a == True{} : Bool}

def Bool.on_of_same_r(a, b, eb, sm):
  match a:
    case True{}:
      {==}
    case False{}:
      %eb : {Bool.not(_) == True{} : Bool}
      sm

def PSet.agree(+d: Nat, +p: S.PSet, +q: S.PSet,
  +l: List<&2, U32>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case Con{y, u}:
      Bool.and(Bool.same(S.PSet.member(d, p, y),
        S.PSet.member(d, q, y)), PSet.agree(d, p, q, u))

law Ords.all_mem_of_agree:
  for +l: List<&2, U32>
  for +d: Nat
  for +p: S.PSet
  for +q: S.PSet
  for +vp: {S.PSet.valid(d, p, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ag: {PSet.agree(d, p, q, l) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l, S.PSet.to_list(d, p)) == True{} : Bool}
  {Sc.Ords.all_mem(l, d, q) == True{} : Bool}

def Ords.all_mem_of_agree(l, d, p, q, vp, lt, ag, ai):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(S.PSet.member(d, q, y),
        Sc.Ords.all_mem(u, d, q),
        Bool.on_of_same(S.PSet.member(d, p, y),
          S.PSet.member(d, q, y),
          Sa.PSet.member_of_to_list(d, p, y, vp, lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(d, p), y),
              Sa.Ords.all_in(u, S.PSet.to_list(d, p)), ai)),
          E.Bool.and_l(Bool.same(S.PSet.member(d, p, y),
            S.PSet.member(d, q, y)), PSet.agree(d, p, q, u), ag)),
        Ords.all_mem_of_agree(u, d, p, q, vp, lt,
          E.Bool.and_r(Bool.same(S.PSet.member(d, p, y),
            S.PSet.member(d, q, y)), PSet.agree(d, p, q, u), ag),
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(d, p), y),
            Sa.Ords.all_in(u, S.PSet.to_list(d, p)), ai)))

law Ords.all_mem_of_agree_r:
  for +l: List<&2, U32>
  for +d: Nat
  for +p: S.PSet
  for +q: S.PSet
  for +vq: {S.PSet.valid(d, q, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ag: {PSet.agree(d, p, q, l) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l, S.PSet.to_list(d, q)) == True{} : Bool}
  {Sc.Ords.all_mem(l, d, p) == True{} : Bool}

def Ords.all_mem_of_agree_r(l, d, p, q, vq, lt, ag, ai):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(S.PSet.member(d, p, y),
        Sc.Ords.all_mem(u, d, p),
        Bool.on_of_same_r(S.PSet.member(d, p, y),
          S.PSet.member(d, q, y),
          Sa.PSet.member_of_to_list(d, q, y, vq, lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(d, q), y),
              Sa.Ords.all_in(u, S.PSet.to_list(d, q)), ai)),
          E.Bool.and_l(Bool.same(S.PSet.member(d, p, y),
            S.PSet.member(d, q, y)), PSet.agree(d, p, q, u), ag)),
        Ords.all_mem_of_agree_r(u, d, p, q, vq, lt,
          E.Bool.and_r(Bool.same(S.PSet.member(d, p, y),
            S.PSet.member(d, q, y)), PSet.agree(d, p, q, u), ag),
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(d, q), y),
            Sa.Ords.all_in(u, S.PSet.to_list(d, q)), ai)))

law PSet.same_of_agree:
  for +d: Nat
  for +p: S.PSet
  for +q: S.PSet
  for +vp: {S.PSet.valid(d, p, True{}) == True{} : Bool}
  for +vq: {S.PSet.valid(d, q, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ap: {PSet.agree(d, p, q, S.PSet.to_list(d, p)) == True{}
    : Bool}
  for +aq: {PSet.agree(d, p, q, S.PSet.to_list(d, q)) == True{}
    : Bool}
  {Ca.PSet.same(d, p, q) == True{} : Bool}

def PSet.same_of_agree(d, p, q, vp, vq, lt, ap, aq):
  E.Bool.and_both(S.PSet.is_subset(d, p, q),
    S.PSet.is_subset(d, q, p),
    Sc.PSet.subset_of_members(d, p, q, vp, vq, lt,
      Ords.all_mem_of_agree(S.PSet.to_list(d, p), d, p, q, vp, lt,
        ap, Sa.Ords.all_in_self(S.PSet.to_list(d, p)))),
    Sc.PSet.subset_of_members(d, q, p, vq, vp, lt,
      Ords.all_mem_of_agree_r(S.PSet.to_list(d, q), d, p, q, vq, lt,
        aq, Sa.Ords.all_in_self(S.PSet.to_list(d, q)))))

# ---------------------------------------------------------------------------
# Every denotation is a set the store would accept.
# ---------------------------------------------------------------------------

def SetExpr.valid_lits(e: A.SetExpr) -> Bool:
  match e:
    case A.EEmpty{}:
      True{}
    case A.EFull{}:
      True{}
    case A.ELit{set}:
      S.PSet.valid(20n, set, True{})
    case A.EUnion{a, b}:
      Bool.and(SetExpr.valid_lits(a), SetExpr.valid_lits(b))
    case A.EInter{a, b}:
      Bool.and(SetExpr.valid_lits(a), SetExpr.valid_lits(b))
    case A.EDiff{a, b}:
      Bool.and(SetExpr.valid_lits(a), SetExpr.valid_lits(b))
    case A.EReach{policy, a}:
      SetExpr.valid_lits(a)
    case A.EFilter{kind, a}:
      SetExpr.valid_lits(a)

def Src.graphs_fit(+src: Idx.Source) -> Bool:
  Bool.and(Gr.Graph.succs_fit(20n,
    Idx.Source.graph(src, Idx.PFull{})),
    Gr.Graph.succs_fit(20n,
      Idx.Source.graph(src, Idx.PTreeData{})))

law Src.graph_fit:
  for +src: Idx.Source
  for +p: Idx.Policy
  for +gf: {Src.graphs_fit(src) == True{} : Bool}
  {Gr.Graph.succs_fit(20n, Idx.Source.graph(src, p)) == True{}
    : Bool}

def Src.graph_fit(src, p, gf):
  match p:
    case Idx.PFull{}:
      E.Bool.and_l(Gr.Graph.succs_fit(20n,
        Idx.Source.graph(src, Idx.PFull{})),
        Gr.Graph.succs_fit(20n,
          Idx.Source.graph(src, Idx.PTreeData{})), gf)
    case Idx.PTreeData{}:
      E.Bool.and_r(Gr.Graph.succs_fit(20n,
        Idx.Source.graph(src, Idx.PFull{})),
        Gr.Graph.succs_fit(20n,
          Idx.Source.graph(src, Idx.PTreeData{})), gf)

law Ords.all_fit_32:
  for +l: List<&2, U32>
  {Sf.Ords.all_fit(l, 32n) == True{} : Bool}

def Ords.all_fit_32(l):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(Dc.U32.hi_zero(y, 32n),
        Sf.Ords.all_fit(u, 32n), Dc.U32.hi_zero_full(y),
        Ords.all_fit_32(u))

law Eval.valid:
  for +e: A.SetExpr
  for +src: Idx.Source
  for +vl: {SetExpr.valid_lits(e) == True{} : Bool}
  for +gf: {Src.graphs_fit(src) == True{} : Bool}
  {S.PSet.valid(20n, Q.Den.eval(src, e), True{}) == True{} : Bool}

def Eval.valid(e, src, vl, gf):
  match e:
    case A.EEmpty{}:
      Vk.PSet.valid_zero(20n)
    case A.EFull{}:
      Iv.PSet.valid_from_list(
        Q.Den.upto(Idx.Source.n(src), Nil{}), 20n, {==},
        Ords.all_fit_32(Q.Den.upto(Idx.Source.n(src), Nil{})))
    case A.ELit{set}:
      vl
    case A.EUnion{a, b}:
      Vk.PSet.valid_union(20n, Q.Den.eval(src, a),
        Q.Den.eval(src, b),
        Eval.valid(a, src,
          E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl), gf),
        Eval.valid(b, src,
          E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl), gf))
    case A.EInter{a, b}:
      Vk.PSet.valid_inter(20n, Q.Den.eval(src, a),
        Q.Den.eval(src, b),
        Eval.valid(a, src,
          E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl), gf),
        Eval.valid(b, src,
          E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl), gf))
    case A.EDiff{a, b}:
      Vk.PSet.valid_diff(20n, Q.Den.eval(src, a),
        Q.Den.eval(src, b),
        Eval.valid(a, src,
          E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl), gf),
        Eval.valid(b, src,
          E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl), gf))
    case A.EReach{policy, a}:
      Lp.Spec.closure_valid(Idx.Source.n(src), 32n, 20n,
        Idx.Source.graph(src, policy), Q.Den.eval(src, a),
        Src.graph_fit(src, policy, gf), {==},
        Eval.valid(a, src, vl, gf))
    case A.EFilter{kind, a}:
      Iv.PSet.valid_from_list(
        Q.Den.keep(src, kind, S.PSet.to_list(20n,
          Q.Den.eval(src, a))), 20n, {==},
        Ords.all_fit_32(Q.Den.keep(src, kind,
          S.PSet.to_list(20n, Q.Den.eval(src, a)))))

# ---------------------------------------------------------------------------
# The operators are congruences for `PSet.same`.
# ---------------------------------------------------------------------------

def Ords.member_eq_union(+pa: S.PSet, +pb: S.PSet, +qa: S.PSet,
  +qb: S.PSet, +y: U32,
  +vpa: {S.PSet.valid(20n, pa, True{}) == True{} : Bool},
  +vpb: {S.PSet.valid(20n, pb, True{}) == True{} : Bool},
  +vqa: {S.PSet.valid(20n, qa, True{}) == True{} : Bool},
  +vqb: {S.PSet.valid(20n, qb, True{}) == True{} : Bool},
  +sa: {Ca.PSet.same(20n, pa, qa) == True{} : Bool},
  +sb: {Ca.PSet.same(20n, pb, qb) == True{} : Bool})
  -> {S.PSet.member(20n, S.PSet.union(20n, pa, pb), y)
    == S.PSet.member(20n, S.PSet.union(20n, qa, qb), y) : Bool}:
  Equal.trans(Bool, S.PSet.member(20n, S.PSet.union(20n, pa, pb), y),
    Bool.or(S.PSet.member(20n, pa, y), S.PSet.member(20n, pb, y)),
    S.PSet.member(20n, S.PSet.union(20n, qa, qb), y),
    So.PSet.union_pointwise(20n, pa, pb, S.PSet.half(20n), y, {==},
      {==}, Sh.PSet.valid_wf(20n, pa, vpa),
      Sh.PSet.valid_wf(20n, pb, vpb), Dc.U32.hi_zero_full(y),
      U32.is_lt(y, S.PSet.half(20n)), {==}),
    Equal.trans(Bool,
      Bool.or(S.PSet.member(20n, pa, y), S.PSet.member(20n, pb, y)),
      Bool.or(S.PSet.member(20n, qa, y), S.PSet.member(20n, qb, y)),
      S.PSet.member(20n, S.PSet.union(20n, qa, qb), y),
      %Ca.PSet.member_same(20n, pa, qa, y, vpa, vqa, {==},
        Dc.U32.hi_zero_full(y), sa)
        : {Bool.or(S.PSet.member(20n, pa, y),
            S.PSet.member(20n, pb, y))
          == Bool.or(_, S.PSet.member(20n, qb, y)) : Bool}
      %Ca.PSet.member_same(20n, pb, qb, y, vpb, vqb, {==},
        Dc.U32.hi_zero_full(y), sb)
        : {Bool.or(S.PSet.member(20n, pa, y),
            S.PSet.member(20n, pb, y))
          == Bool.or(S.PSet.member(20n, pa, y), _) : Bool}
      {==},
      E.Bool.sym(S.PSet.member(20n, S.PSet.union(20n, qa, qb), y),
        Bool.or(S.PSet.member(20n, qa, y),
          S.PSet.member(20n, qb, y)),
        So.PSet.union_pointwise(20n, qa, qb, S.PSet.half(20n), y,
          {==}, {==}, Sh.PSet.valid_wf(20n, qa, vqa),
          Sh.PSet.valid_wf(20n, qb, vqb), Dc.U32.hi_zero_full(y),
          U32.is_lt(y, S.PSet.half(20n)), {==}))))

def Ords.member_eq_inter(+pa: S.PSet, +pb: S.PSet, +qa: S.PSet,
  +qb: S.PSet, +y: U32,
  +vpa: {S.PSet.valid(20n, pa, True{}) == True{} : Bool},
  +vpb: {S.PSet.valid(20n, pb, True{}) == True{} : Bool},
  +vqa: {S.PSet.valid(20n, qa, True{}) == True{} : Bool},
  +vqb: {S.PSet.valid(20n, qb, True{}) == True{} : Bool},
  +sa: {Ca.PSet.same(20n, pa, qa) == True{} : Bool},
  +sb: {Ca.PSet.same(20n, pb, qb) == True{} : Bool})
  -> {S.PSet.member(20n, S.PSet.inter(20n, pa, pb), y)
    == S.PSet.member(20n, S.PSet.inter(20n, qa, qb), y) : Bool}:
  Equal.trans(Bool, S.PSet.member(20n, S.PSet.inter(20n, pa, pb), y),
    Bool.and(S.PSet.member(20n, pa, y), S.PSet.member(20n, pb, y)),
    S.PSet.member(20n, S.PSet.inter(20n, qa, qb), y),
    So.PSet.inter_pointwise(20n, pa, pb, S.PSet.half(20n), y, {==},
      {==}, Sh.PSet.valid_wf(20n, pa, vpa),
      Sh.PSet.valid_wf(20n, pb, vpb), Dc.U32.hi_zero_full(y),
      U32.is_lt(y, S.PSet.half(20n)), {==}),
    Equal.trans(Bool,
      Bool.and(S.PSet.member(20n, pa, y), S.PSet.member(20n, pb, y)),
      Bool.and(S.PSet.member(20n, qa, y), S.PSet.member(20n, qb, y)),
      S.PSet.member(20n, S.PSet.inter(20n, qa, qb), y),
      %Ca.PSet.member_same(20n, pa, qa, y, vpa, vqa, {==},
        Dc.U32.hi_zero_full(y), sa)
        : {Bool.and(S.PSet.member(20n, pa, y),
            S.PSet.member(20n, pb, y))
          == Bool.and(_, S.PSet.member(20n, qb, y)) : Bool}
      %Ca.PSet.member_same(20n, pb, qb, y, vpb, vqb, {==},
        Dc.U32.hi_zero_full(y), sb)
        : {Bool.and(S.PSet.member(20n, pa, y),
            S.PSet.member(20n, pb, y))
          == Bool.and(S.PSet.member(20n, pa, y), _) : Bool}
      {==},
      E.Bool.sym(S.PSet.member(20n, S.PSet.inter(20n, qa, qb), y),
        Bool.and(S.PSet.member(20n, qa, y),
          S.PSet.member(20n, qb, y)),
        So.PSet.inter_pointwise(20n, qa, qb, S.PSet.half(20n), y,
          {==}, {==}, Sh.PSet.valid_wf(20n, qa, vqa),
          Sh.PSet.valid_wf(20n, qb, vqb), Dc.U32.hi_zero_full(y),
          U32.is_lt(y, S.PSet.half(20n)), {==}))))

def Ords.member_eq_diff(+pa: S.PSet, +pb: S.PSet, +qa: S.PSet,
  +qb: S.PSet, +y: U32,
  +vpa: {S.PSet.valid(20n, pa, True{}) == True{} : Bool},
  +vpb: {S.PSet.valid(20n, pb, True{}) == True{} : Bool},
  +vqa: {S.PSet.valid(20n, qa, True{}) == True{} : Bool},
  +vqb: {S.PSet.valid(20n, qb, True{}) == True{} : Bool},
  +sa: {Ca.PSet.same(20n, pa, qa) == True{} : Bool},
  +sb: {Ca.PSet.same(20n, pb, qb) == True{} : Bool})
  -> {S.PSet.member(20n, S.PSet.diff(20n, pa, pb), y)
    == S.PSet.member(20n, S.PSet.diff(20n, qa, qb), y) : Bool}:
  Equal.trans(Bool, S.PSet.member(20n, S.PSet.diff(20n, pa, pb), y),
    Bool.and(S.PSet.member(20n, pa, y),
      Bool.not(S.PSet.member(20n, pb, y))),
    S.PSet.member(20n, S.PSet.diff(20n, qa, qb), y),
    So.PSet.diff_pointwise(20n, pa, pb, S.PSet.half(20n), y, {==},
      {==}, Sh.PSet.valid_wf(20n, pa, vpa),
      Sh.PSet.valid_wf(20n, pb, vpb), Dc.U32.hi_zero_full(y),
      U32.is_lt(y, S.PSet.half(20n)), {==}),
    Equal.trans(Bool,
      Bool.and(S.PSet.member(20n, pa, y),
        Bool.not(S.PSet.member(20n, pb, y))),
      Bool.and(S.PSet.member(20n, qa, y),
        Bool.not(S.PSet.member(20n, qb, y))),
      S.PSet.member(20n, S.PSet.diff(20n, qa, qb), y),
      %Ca.PSet.member_same(20n, pa, qa, y, vpa, vqa, {==},
        Dc.U32.hi_zero_full(y), sa)
        : {Bool.and(S.PSet.member(20n, pa, y),
            Bool.not(S.PSet.member(20n, pb, y)))
          == Bool.and(_, Bool.not(S.PSet.member(20n, qb, y)))
          : Bool}
      %Ca.PSet.member_same(20n, pb, qb, y, vpb, vqb, {==},
        Dc.U32.hi_zero_full(y), sb)
        : {Bool.and(S.PSet.member(20n, pa, y),
            Bool.not(S.PSet.member(20n, pb, y)))
          == Bool.and(S.PSet.member(20n, pa, y), Bool.not(_))
          : Bool}
      {==},
      E.Bool.sym(S.PSet.member(20n, S.PSet.diff(20n, qa, qb), y),
        Bool.and(S.PSet.member(20n, qa, y),
          Bool.not(S.PSet.member(20n, qb, y))),
        So.PSet.diff_pointwise(20n, qa, qb, S.PSet.half(20n), y,
          {==}, {==}, Sh.PSet.valid_wf(20n, qa, vqa),
          Sh.PSet.valid_wf(20n, qb, vqb), Dc.U32.hi_zero_full(y),
          U32.is_lt(y, S.PSet.half(20n)), {==}))))

# ---------------------------------------------------------------------------
# Lifting each to `PSet.same`.
# ---------------------------------------------------------------------------

law Ords.agree_union:
  for +l: List<&2, U32>
  for +pa: S.PSet
  for +pb: S.PSet
  for +qa: S.PSet
  for +qb: S.PSet
  for +vpa: {S.PSet.valid(20n, pa, True{}) == True{} : Bool}
  for +vpb: {S.PSet.valid(20n, pb, True{}) == True{} : Bool}
  for +vqa: {S.PSet.valid(20n, qa, True{}) == True{} : Bool}
  for +vqb: {S.PSet.valid(20n, qb, True{}) == True{} : Bool}
  for +sa: {Ca.PSet.same(20n, pa, qa) == True{} : Bool}
  for +sb: {Ca.PSet.same(20n, pb, qb) == True{} : Bool}
  {PSet.agree(20n, S.PSet.union(20n, pa, pb),
    S.PSet.union(20n, qa, qb), l) == True{} : Bool}

def Ords.agree_union(l, pa, pb, qa, qb, vpa, vpb, vqa, vqb, sa, sb):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(
        Bool.same(S.PSet.member(20n, S.PSet.union(20n, pa, pb), y),
          S.PSet.member(20n, S.PSet.union(20n, qa, qb), y)),
        PSet.agree(20n, S.PSet.union(20n, pa, pb),
          S.PSet.union(20n, qa, qb), u),
        Bool.same_of_eq(
          S.PSet.member(20n, S.PSet.union(20n, pa, pb), y),
          S.PSet.member(20n, S.PSet.union(20n, qa, qb), y),
          Ords.member_eq_union(pa, pb, qa, qb, y, vpa, vpb, vqa,
            vqb, sa, sb)),
        Ords.agree_union(u, pa, pb, qa, qb, vpa, vpb, vqa, vqb, sa,
          sb))

law PSet.same_union:
  for +pa: S.PSet
  for +pb: S.PSet
  for +qa: S.PSet
  for +qb: S.PSet
  for +vpa: {S.PSet.valid(20n, pa, True{}) == True{} : Bool}
  for +vpb: {S.PSet.valid(20n, pb, True{}) == True{} : Bool}
  for +vqa: {S.PSet.valid(20n, qa, True{}) == True{} : Bool}
  for +vqb: {S.PSet.valid(20n, qb, True{}) == True{} : Bool}
  for +sa: {Ca.PSet.same(20n, pa, qa) == True{} : Bool}
  for +sb: {Ca.PSet.same(20n, pb, qb) == True{} : Bool}
  {Ca.PSet.same(20n, S.PSet.union(20n, pa, pb),
    S.PSet.union(20n, qa, qb)) == True{} : Bool}

def PSet.same_union(pa, pb, qa, qb, vpa, vpb, vqa, vqb, sa, sb):
  PSet.same_of_agree(20n, S.PSet.union(20n, pa, pb),
    S.PSet.union(20n, qa, qb),
    Vk.PSet.valid_union(20n, pa, pb, vpa, vpb),
    Vk.PSet.valid_union(20n, qa, qb, vqa, vqb), {==},
    Ords.agree_union(S.PSet.to_list(20n,
      S.PSet.union(20n, pa, pb)), pa, pb, qa, qb, vpa, vpb, vqa,
      vqb, sa, sb),
    Ords.agree_union(S.PSet.to_list(20n,
      S.PSet.union(20n, qa, qb)), pa, pb, qa, qb, vpa, vpb, vqa,
      vqb, sa, sb))

law Ords.agree_inter:
  for +l: List<&2, U32>
  for +pa: S.PSet
  for +pb: S.PSet
  for +qa: S.PSet
  for +qb: S.PSet
  for +vpa: {S.PSet.valid(20n, pa, True{}) == True{} : Bool}
  for +vpb: {S.PSet.valid(20n, pb, True{}) == True{} : Bool}
  for +vqa: {S.PSet.valid(20n, qa, True{}) == True{} : Bool}
  for +vqb: {S.PSet.valid(20n, qb, True{}) == True{} : Bool}
  for +sa: {Ca.PSet.same(20n, pa, qa) == True{} : Bool}
  for +sb: {Ca.PSet.same(20n, pb, qb) == True{} : Bool}
  {PSet.agree(20n, S.PSet.inter(20n, pa, pb),
    S.PSet.inter(20n, qa, qb), l) == True{} : Bool}

def Ords.agree_inter(l, pa, pb, qa, qb, vpa, vpb, vqa, vqb, sa, sb):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(
        Bool.same(S.PSet.member(20n, S.PSet.inter(20n, pa, pb), y),
          S.PSet.member(20n, S.PSet.inter(20n, qa, qb), y)),
        PSet.agree(20n, S.PSet.inter(20n, pa, pb),
          S.PSet.inter(20n, qa, qb), u),
        Bool.same_of_eq(
          S.PSet.member(20n, S.PSet.inter(20n, pa, pb), y),
          S.PSet.member(20n, S.PSet.inter(20n, qa, qb), y),
          Ords.member_eq_inter(pa, pb, qa, qb, y, vpa, vpb, vqa,
            vqb, sa, sb)),
        Ords.agree_inter(u, pa, pb, qa, qb, vpa, vpb, vqa, vqb, sa,
          sb))

law PSet.same_inter:
  for +pa: S.PSet
  for +pb: S.PSet
  for +qa: S.PSet
  for +qb: S.PSet
  for +vpa: {S.PSet.valid(20n, pa, True{}) == True{} : Bool}
  for +vpb: {S.PSet.valid(20n, pb, True{}) == True{} : Bool}
  for +vqa: {S.PSet.valid(20n, qa, True{}) == True{} : Bool}
  for +vqb: {S.PSet.valid(20n, qb, True{}) == True{} : Bool}
  for +sa: {Ca.PSet.same(20n, pa, qa) == True{} : Bool}
  for +sb: {Ca.PSet.same(20n, pb, qb) == True{} : Bool}
  {Ca.PSet.same(20n, S.PSet.inter(20n, pa, pb),
    S.PSet.inter(20n, qa, qb)) == True{} : Bool}

def PSet.same_inter(pa, pb, qa, qb, vpa, vpb, vqa, vqb, sa, sb):
  PSet.same_of_agree(20n, S.PSet.inter(20n, pa, pb),
    S.PSet.inter(20n, qa, qb),
    Vk.PSet.valid_inter(20n, pa, pb, vpa, vpb),
    Vk.PSet.valid_inter(20n, qa, qb, vqa, vqb), {==},
    Ords.agree_inter(S.PSet.to_list(20n,
      S.PSet.inter(20n, pa, pb)), pa, pb, qa, qb, vpa, vpb, vqa,
      vqb, sa, sb),
    Ords.agree_inter(S.PSet.to_list(20n,
      S.PSet.inter(20n, qa, qb)), pa, pb, qa, qb, vpa, vpb, vqa,
      vqb, sa, sb))

law Ords.agree_diff:
  for +l: List<&2, U32>
  for +pa: S.PSet
  for +pb: S.PSet
  for +qa: S.PSet
  for +qb: S.PSet
  for +vpa: {S.PSet.valid(20n, pa, True{}) == True{} : Bool}
  for +vpb: {S.PSet.valid(20n, pb, True{}) == True{} : Bool}
  for +vqa: {S.PSet.valid(20n, qa, True{}) == True{} : Bool}
  for +vqb: {S.PSet.valid(20n, qb, True{}) == True{} : Bool}
  for +sa: {Ca.PSet.same(20n, pa, qa) == True{} : Bool}
  for +sb: {Ca.PSet.same(20n, pb, qb) == True{} : Bool}
  {PSet.agree(20n, S.PSet.diff(20n, pa, pb),
    S.PSet.diff(20n, qa, qb), l) == True{} : Bool}

def Ords.agree_diff(l, pa, pb, qa, qb, vpa, vpb, vqa, vqb, sa, sb):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(
        Bool.same(S.PSet.member(20n, S.PSet.diff(20n, pa, pb), y),
          S.PSet.member(20n, S.PSet.diff(20n, qa, qb), y)),
        PSet.agree(20n, S.PSet.diff(20n, pa, pb),
          S.PSet.diff(20n, qa, qb), u),
        Bool.same_of_eq(
          S.PSet.member(20n, S.PSet.diff(20n, pa, pb), y),
          S.PSet.member(20n, S.PSet.diff(20n, qa, qb), y),
          Ords.member_eq_diff(pa, pb, qa, qb, y, vpa, vpb, vqa,
            vqb, sa, sb)),
        Ords.agree_diff(u, pa, pb, qa, qb, vpa, vpb, vqa, vqb, sa,
          sb))

law PSet.same_diff:
  for +pa: S.PSet
  for +pb: S.PSet
  for +qa: S.PSet
  for +qb: S.PSet
  for +vpa: {S.PSet.valid(20n, pa, True{}) == True{} : Bool}
  for +vpb: {S.PSet.valid(20n, pb, True{}) == True{} : Bool}
  for +vqa: {S.PSet.valid(20n, qa, True{}) == True{} : Bool}
  for +vqb: {S.PSet.valid(20n, qb, True{}) == True{} : Bool}
  for +sa: {Ca.PSet.same(20n, pa, qa) == True{} : Bool}
  for +sb: {Ca.PSet.same(20n, pb, qb) == True{} : Bool}
  {Ca.PSet.same(20n, S.PSet.diff(20n, pa, pb),
    S.PSet.diff(20n, qa, qb)) == True{} : Bool}

def PSet.same_diff(pa, pb, qa, qb, vpa, vpb, vqa, vqb, sa, sb):
  PSet.same_of_agree(20n, S.PSet.diff(20n, pa, pb),
    S.PSet.diff(20n, qa, qb),
    Vk.PSet.valid_diff(20n, pa, pb, vpa, vpb),
    Vk.PSet.valid_diff(20n, qa, qb, vqa, vqb), {==},
    Ords.agree_diff(S.PSet.to_list(20n,
      S.PSet.diff(20n, pa, pb)), pa, pb, qa, qb, vpa, vpb, vqa,
      vqb, sa, sb),
    Ords.agree_diff(S.PSet.to_list(20n,
      S.PSet.diff(20n, qa, qb)), pa, pb, qa, qb, vpa, vpb, vqa,
      vqb, sa, sb))

# ---------------------------------------------------------------------------
# A set built from a list holds exactly that list.
# ---------------------------------------------------------------------------

law PSet.member_from_list:
  for +l: List<&2, U32>
  for +d: Nat
  for +y: U32
  for +m: Bool
  for +c: Bool
  for +em: {m == S.PSet.member(d, S.PSet.from_list(d, l), y) : Bool}
  for +ec: {c == List.contains(~U32, ~U32.is_eq, l, y) : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(y, 12n+d) == True{} : Bool}
  for +fits: {Sf.Ords.all_fit(l, 12n+d) == True{} : Bool}
  {S.PSet.member(d, S.PSet.from_list(d, l), y)
    == List.contains(~U32, ~U32.is_eq, l, y) : Bool}

def PSet.member_from_list(l, d, y, m, c, em, ec, lt, inv, fits):
  match m:
    case True{}:
      match c:
        case True{}:
          %em : {_ == List.contains(~U32, ~U32.is_eq, l, y) : Bool}
          ec
        case False{}:
          E.Bool.noconf({S.PSet.member(d, S.PSet.from_list(d, l), y)
            == List.contains(~U32, ~U32.is_eq, l, y) : Bool},
            %Ls.PSet.from_list_only_at(l, d, y, lt, inv, fits,
              E.Bool.sym(True{},
                S.PSet.member(d, S.PSet.from_list(d, l), y), em))
              : {False{} == _ : Bool}
            ec)
    case False{}:
      match c:
        case True{}:
          E.Bool.noconf({S.PSet.member(d, S.PSet.from_list(d, l), y)
            == List.contains(~U32, ~U32.is_eq, l, y) : Bool},
            %Ls.PSet.from_list_contains_at(l, d, y, lt, inv,
              E.Bool.sym(True{},
                List.contains(~U32, ~U32.is_eq, l, y), ec))
              : {False{} == _ : Bool}
            em)
        case False{}:
          %em : {_ == List.contains(~U32, ~U32.is_eq, l, y) : Bool}
          ec

law PSet.member_of_list:
  for +l: List<&2, U32>
  for +d: Nat
  for +y: U32
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(y, 12n+d) == True{} : Bool}
  for +fits: {Sf.Ords.all_fit(l, 12n+d) == True{} : Bool}
  {S.PSet.member(d, S.PSet.from_list(d, l), y)
    == List.contains(~U32, ~U32.is_eq, l, y) : Bool}

def PSet.member_of_list(l, d, y, lt, inv, fits):
  PSet.member_from_list(l, d, y,
    S.PSet.member(d, S.PSet.from_list(d, l), y),
    List.contains(~U32, ~U32.is_eq, l, y), {==}, {==}, lt, inv,
    fits)

# ---------------------------------------------------------------------------
# What the kind filter keeps.
# ---------------------------------------------------------------------------

def Den.hit(+src: Idx.Source, +kind: U32, +x: U32) -> Bool:
  U32.is_eq(Im.Meta.kind(Idx.Source.meta_of(src, x)), kind)

law Den.contains_keep:
  for +l: List<&2, U32>
  for +src: Idx.Source
  for +kind: U32
  for +y: U32
  {List.contains(~U32, ~U32.is_eq, Q.Den.keep(src, kind, l), y)
    == Bool.and(List.contains(~U32, ~U32.is_eq, l, y),
         Den.hit(src, kind, y)) : Bool}

def Den.contains_keep.hit(+t: List<&2, U32>, +src: Idx.Source,
  +kind: U32, +x: U32, +y: U32, +hx: Bool,
  +ehx: {hx == Den.hit(src, kind, x) : Bool},
  +eex: {True{} == U32.is_eq(x, y) : Bool},
  +ih: {List.contains(~U32, ~U32.is_eq, Q.Den.keep(src, kind, t), y)
    == Bool.and(List.contains(~U32, ~U32.is_eq, t, y),
         Den.hit(src, kind, y)) : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
    Q.Den.keep.pick(x, Q.Den.keep(src, kind, t), hx), y)
    == Bool.and(Bool.or(True{},
         List.contains(~U32, ~U32.is_eq, t, y)), hx) : Bool}:
  match hx:
    case True{}:
      %eex
        : {Bool.or(_, List.contains(~U32, ~U32.is_eq,
            Q.Den.keep(src, kind, t), y)) == True{} : Bool}
      {==}
    case False{}:
      Equal.trans(Bool,
        List.contains(~U32, ~U32.is_eq, Q.Den.keep(src, kind, t), y),
        Bool.and(List.contains(~U32, ~U32.is_eq, t, y),
          Den.hit(src, kind, y)), False{}, ih,
        %E.U32.eq_reflect(x, y,
          E.Bool.sym(True{}, U32.is_eq(x, y), eex))
          : {Bool.and(List.contains(~U32, ~U32.is_eq, t, y),
              Den.hit(src, kind, _)) == False{} : Bool}
        %ehx
          : {Bool.and(List.contains(~U32, ~U32.is_eq, t, y), _)
            == False{} : Bool}
        Sa2.Word.and_false_r(
          List.contains(~U32, ~U32.is_eq, t, y)))

def Den.contains_keep.miss(+t: List<&2, U32>, +src: Idx.Source,
  +kind: U32, +x: U32, +y: U32, +hx: Bool,
  +eex: {False{} == U32.is_eq(x, y) : Bool},
  +ih: {List.contains(~U32, ~U32.is_eq, Q.Den.keep(src, kind, t), y)
    == Bool.and(List.contains(~U32, ~U32.is_eq, t, y),
         Den.hit(src, kind, y)) : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
    Q.Den.keep.pick(x, Q.Den.keep(src, kind, t), hx), y)
    == Bool.and(Bool.or(False{},
         List.contains(~U32, ~U32.is_eq, t, y)),
         Den.hit(src, kind, y)) : Bool}:
  match hx:
    case True{}:
      %eex
        : {Bool.or(_, List.contains(~U32, ~U32.is_eq,
            Q.Den.keep(src, kind, t), y))
          == Bool.and(List.contains(~U32, ~U32.is_eq, t, y),
               Den.hit(src, kind, y)) : Bool}
      ih
    case False{}:
      ih

def Den.contains_keep.step(+t: List<&2, U32>, +src: Idx.Source,
  +kind: U32, +x: U32, +y: U32, +hx: Bool,
  +ehx: {hx == Den.hit(src, kind, x) : Bool}, +ex: Bool,
  +eex: {ex == U32.is_eq(x, y) : Bool},
  +ih: {List.contains(~U32, ~U32.is_eq, Q.Den.keep(src, kind, t), y)
    == Bool.and(List.contains(~U32, ~U32.is_eq, t, y),
         Den.hit(src, kind, y)) : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
    Q.Den.keep(src, kind, Con{x, t}), y)
    == Bool.and(List.contains(~U32, ~U32.is_eq, Con{x, t}, y),
         Den.hit(src, kind, y)) : Bool}:
  match ex:
    case True{}:
      %E.U32.eq_reflect(x, y,
        E.Bool.sym(True{}, U32.is_eq(x, y), eex))
        : {List.contains(~U32, ~U32.is_eq,
            Q.Den.keep(src, kind, Con{x, t}), y)
          == Bool.and(List.contains(~U32, ~U32.is_eq, Con{x, t}, y),
               Den.hit(src, kind, _)) : Bool}
      %eex : {List.contains(~U32, ~U32.is_eq,
          Q.Den.keep(src, kind, Con{x, t}), y)
        == Bool.and(Bool.or(_,
             List.contains(~U32, ~U32.is_eq, t, y)),
             Den.hit(src, kind, x)) : Bool}
      %ehx : {List.contains(~U32, ~U32.is_eq,
          Q.Den.keep.pick(x, Q.Den.keep(src, kind, t), _), y)
        == Bool.and(Bool.or(True{},
             List.contains(~U32, ~U32.is_eq, t, y)), _) : Bool}
      Den.contains_keep.hit(t, src, kind, x, y, hx, ehx, eex, ih)
    case False{}:
      %eex : {List.contains(~U32, ~U32.is_eq,
          Q.Den.keep(src, kind, Con{x, t}), y)
        == Bool.and(Bool.or(_,
             List.contains(~U32, ~U32.is_eq, t, y)),
             Den.hit(src, kind, y)) : Bool}
      %ehx : {List.contains(~U32, ~U32.is_eq,
          Q.Den.keep.pick(x, Q.Den.keep(src, kind, t), _), y)
        == Bool.and(Bool.or(False{},
             List.contains(~U32, ~U32.is_eq, t, y)),
             Den.hit(src, kind, y)) : Bool}
      Den.contains_keep.miss(t, src, kind, x, y, hx, eex, ih)

def Den.contains_keep(l, src, kind, y):
  match l:
    case Nil{}:
      {==}
    case Con{x, t}:
      Den.contains_keep.step(t, src, kind, x, y,
        Den.hit(src, kind, x), {==}, U32.is_eq(x, y), {==},
        Den.contains_keep(t, src, kind, y))

# ---------------------------------------------------------------------------
# Filtering and closing are congruences too.
# ---------------------------------------------------------------------------

def Ords.member_eq_filter(+src: Idx.Source, +kind: U32, +p: S.PSet,
  +q: S.PSet, +y: U32,
  +vp: {S.PSet.valid(20n, p, True{}) == True{} : Bool},
  +vq: {S.PSet.valid(20n, q, True{}) == True{} : Bool},
  +sm: {Ca.PSet.same(20n, p, q) == True{} : Bool})
  -> {S.PSet.member(20n, Q.Den.filter(src, kind, p), y)
    == S.PSet.member(20n, Q.Den.filter(src, kind, q), y) : Bool}:
  %E.Bool.sym(S.PSet.member(20n, S.PSet.from_list(20n,
      Q.Den.keep(src, kind, S.PSet.to_list(20n, p))), y),
    List.contains(~U32, ~U32.is_eq,
      Q.Den.keep(src, kind, S.PSet.to_list(20n, p)), y),
    PSet.member_of_list(
      Q.Den.keep(src, kind, S.PSet.to_list(20n, p)), 20n, y, {==},
      Dc.U32.hi_zero_full(y),
      Ords.all_fit_32(
        Q.Den.keep(src, kind, S.PSet.to_list(20n, p)))))
    : {_ == S.PSet.member(20n, Q.Den.filter(src, kind, q), y)
      : Bool}
  %E.Bool.sym(S.PSet.member(20n, S.PSet.from_list(20n,
      Q.Den.keep(src, kind, S.PSet.to_list(20n, q))), y),
    List.contains(~U32, ~U32.is_eq,
      Q.Den.keep(src, kind, S.PSet.to_list(20n, q)), y),
    PSet.member_of_list(
      Q.Den.keep(src, kind, S.PSet.to_list(20n, q)), 20n, y, {==},
      Dc.U32.hi_zero_full(y),
      Ords.all_fit_32(
        Q.Den.keep(src, kind, S.PSet.to_list(20n, q)))))
    : {List.contains(~U32, ~U32.is_eq,
        Q.Den.keep(src, kind, S.PSet.to_list(20n, p)), y) == _
      : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      Q.Den.keep(src, kind, S.PSet.to_list(20n, p)), y),
    Bool.and(List.contains(~U32, ~U32.is_eq,
      S.PSet.to_list(20n, p), y), Den.hit(src, kind, y)),
    Den.contains_keep(S.PSet.to_list(20n, p), src, kind, y))
    : {_ == List.contains(~U32, ~U32.is_eq,
        Q.Den.keep(src, kind, S.PSet.to_list(20n, q)), y) : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      Q.Den.keep(src, kind, S.PSet.to_list(20n, q)), y),
    Bool.and(List.contains(~U32, ~U32.is_eq,
      S.PSet.to_list(20n, q), y), Den.hit(src, kind, y)),
    Den.contains_keep(S.PSet.to_list(20n, q), src, kind, y))
    : {Bool.and(List.contains(~U32, ~U32.is_eq,
        S.PSet.to_list(20n, p), y), Den.hit(src, kind, y)) == _
      : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      S.PSet.to_list(20n, p), y), S.PSet.member(20n, p, y),
    Vs.PSet.to_list_member_of_valid(20n, p, y, vp, {==},
      Dc.U32.hi_zero_full(y)))
    : {Bool.and(_, Den.hit(src, kind, y))
      == Bool.and(List.contains(~U32, ~U32.is_eq,
           S.PSet.to_list(20n, q), y), Den.hit(src, kind, y))
      : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      S.PSet.to_list(20n, q), y), S.PSet.member(20n, q, y),
    Vs.PSet.to_list_member_of_valid(20n, q, y, vq, {==},
      Dc.U32.hi_zero_full(y)))
    : {Bool.and(S.PSet.member(20n, p, y), Den.hit(src, kind, y))
      == Bool.and(_, Den.hit(src, kind, y)) : Bool}
  %Ca.PSet.member_same(20n, p, q, y, vp, vq, {==},
    Dc.U32.hi_zero_full(y), sm)
    : {Bool.and(S.PSet.member(20n, p, y), Den.hit(src, kind, y))
      == Bool.and(_, Den.hit(src, kind, y)) : Bool}
  {==}

law Ords.agree_filter:
  for +l: List<&2, U32>
  for +src: Idx.Source
  for +kind: U32
  for +p: S.PSet
  for +q: S.PSet
  for +vp: {S.PSet.valid(20n, p, True{}) == True{} : Bool}
  for +vq: {S.PSet.valid(20n, q, True{}) == True{} : Bool}
  for +sm: {Ca.PSet.same(20n, p, q) == True{} : Bool}
  {PSet.agree(20n, Q.Den.filter(src, kind, p),
    Q.Den.filter(src, kind, q), l) == True{} : Bool}

def Ords.agree_filter(l, src, kind, p, q, vp, vq, sm):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(
        Bool.same(S.PSet.member(20n, Q.Den.filter(src, kind, p), y),
          S.PSet.member(20n, Q.Den.filter(src, kind, q), y)),
        PSet.agree(20n, Q.Den.filter(src, kind, p),
          Q.Den.filter(src, kind, q), u),
        Bool.same_of_eq(
          S.PSet.member(20n, Q.Den.filter(src, kind, p), y),
          S.PSet.member(20n, Q.Den.filter(src, kind, q), y),
          Ords.member_eq_filter(src, kind, p, q, y, vp, vq, sm)),
        Ords.agree_filter(u, src, kind, p, q, vp, vq, sm))

law PSet.same_filter:
  for +src: Idx.Source
  for +kind: U32
  for +p: S.PSet
  for +q: S.PSet
  for +vp: {S.PSet.valid(20n, p, True{}) == True{} : Bool}
  for +vq: {S.PSet.valid(20n, q, True{}) == True{} : Bool}
  for +sm: {Ca.PSet.same(20n, p, q) == True{} : Bool}
  {Ca.PSet.same(20n, Q.Den.filter(src, kind, p),
    Q.Den.filter(src, kind, q)) == True{} : Bool}

def PSet.same_filter(src, kind, p, q, vp, vq, sm):
  PSet.same_of_agree(20n, Q.Den.filter(src, kind, p),
    Q.Den.filter(src, kind, q),
    Iv.PSet.valid_from_list(
      Q.Den.keep(src, kind, S.PSet.to_list(20n, p)), 20n, {==},
      Ords.all_fit_32(
        Q.Den.keep(src, kind, S.PSet.to_list(20n, p)))),
    Iv.PSet.valid_from_list(
      Q.Den.keep(src, kind, S.PSet.to_list(20n, q)), 20n, {==},
      Ords.all_fit_32(
        Q.Den.keep(src, kind, S.PSet.to_list(20n, q)))), {==},
    Ords.agree_filter(S.PSet.to_list(20n,
      Q.Den.filter(src, kind, p)), src, kind, p, q, vp, vq, sm),
    Ords.agree_filter(S.PSet.to_list(20n,
      Q.Den.filter(src, kind, q)), src, kind, p, q, vp, vq, sm))

law PSet.same_reach:
  for +n: Nat
  for +g: G.Graph()
  for +p: S.PSet
  for +q: S.PSet
  for +vp: {S.PSet.valid(20n, p, True{}) == True{} : Bool}
  for +vq: {S.PSet.valid(20n, q, True{}) == True{} : Bool}
  for +gf: {Gr.Graph.succs_fit(20n, g) == True{} : Bool}
  for +sm: {Ca.PSet.same(20n, p, q) == True{} : Bool}
  {Ca.PSet.same(20n, Sp.Spec.closure(n, 32n, g, 20n, p),
    Sp.Spec.closure(n, 32n, g, 20n, q)) == True{} : Bool}

def PSet.same_reach(n, g, p, q, vp, vq, gf, sm):
  Ca.Spec.iter_same(1n+n, 32n, 20n, g, p, q, gf, {==}, vp, vq, sm)

# ---------------------------------------------------------------------------
# The rewrites keep the literals well shaped.
# ---------------------------------------------------------------------------

law SetExpr.wf_of_valid_lits:
  for +e: A.SetExpr
  for +vl: {SetExpr.valid_lits(e) == True{} : Bool}
  {Dn.SetExpr.wf_lits(e) == True{} : Bool}

def SetExpr.wf_of_valid_lits(e, vl):
  match e:
    case A.EEmpty{}:
      {==}
    case A.EFull{}:
      {==}
    case A.ELit{set}:
      Sh.PSet.valid_wf(20n, set, vl)
    case A.EUnion{a, b}:
      E.Bool.and_both(Dn.SetExpr.wf_lits(a), Dn.SetExpr.wf_lits(b),
        SetExpr.wf_of_valid_lits(a,
          E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)),
        SetExpr.wf_of_valid_lits(b,
          E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)))
    case A.EInter{a, b}:
      E.Bool.and_both(Dn.SetExpr.wf_lits(a), Dn.SetExpr.wf_lits(b),
        SetExpr.wf_of_valid_lits(a,
          E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)),
        SetExpr.wf_of_valid_lits(b,
          E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)))
    case A.EDiff{a, b}:
      E.Bool.and_both(Dn.SetExpr.wf_lits(a), Dn.SetExpr.wf_lits(b),
        SetExpr.wf_of_valid_lits(a,
          E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)),
        SetExpr.wf_of_valid_lits(b,
          E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)))
    case A.EReach{policy, a}:
      SetExpr.wf_of_valid_lits(a, vl)
    case A.EFilter{kind, a}:
      SetExpr.wf_of_valid_lits(a, vl)

law Rw.union_lits:
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +ea: Bool
  for +eb: Bool
  for +la: {SetExpr.valid_lits(a) == True{} : Bool}
  for +lb: {SetExpr.valid_lits(b) == True{} : Bool}
  {SetExpr.valid_lits(R.Rw.union(a, b, ea, eb)) == True{} : Bool}

def Rw.union_lits(a, b, ea, eb, la, lb):
  match ea:
    case True{}:
      lb
    case False{}:
      match eb:
        case True{}:
          la
        case False{}:
          E.Bool.and_both(SetExpr.valid_lits(a),
            SetExpr.valid_lits(b), la, lb)

law Rw.inter_lits:
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +ea: Bool
  for +eb: Bool
  for +la: {SetExpr.valid_lits(a) == True{} : Bool}
  for +lb: {SetExpr.valid_lits(b) == True{} : Bool}
  {SetExpr.valid_lits(R.Rw.inter(a, b, ea, eb)) == True{} : Bool}

def Rw.inter_lits(a, b, ea, eb, la, lb):
  match ea:
    case True{}:
      {==}
    case False{}:
      match eb:
        case True{}:
          {==}
        case False{}:
          E.Bool.and_both(SetExpr.valid_lits(a),
            SetExpr.valid_lits(b), la, lb)

law Rw.diff_lits:
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +ea: Bool
  for +eb: Bool
  for +la: {SetExpr.valid_lits(a) == True{} : Bool}
  for +lb: {SetExpr.valid_lits(b) == True{} : Bool}
  {SetExpr.valid_lits(R.Rw.diff(a, b, ea, eb)) == True{} : Bool}

def Rw.diff_lits(a, b, ea, eb, la, lb):
  match ea:
    case True{}:
      {==}
    case False{}:
      match eb:
        case True{}:
          la
        case False{}:
          E.Bool.and_both(SetExpr.valid_lits(a),
            SetExpr.valid_lits(b), la, lb)

law Rw.reach_lits:
  for +p: Idx.Policy
  for +a: A.SetExpr
  for +ea: Bool
  for +la: {SetExpr.valid_lits(a) == True{} : Bool}
  {SetExpr.valid_lits(R.Rw.reach(p, a, ea)) == True{} : Bool}

def Rw.reach_lits(p, a, ea, la):
  match ea:
    case True{}:
      {==}
    case False{}:
      la

law Rw.join_lits:
  for +op: Nat
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +la: {SetExpr.valid_lits(a) == True{} : Bool}
  for +lb: {SetExpr.valid_lits(b) == True{} : Bool}
  {SetExpr.valid_lits(R.Rw.join.go(a, b, op)) == True{} : Bool}

def Rw.join_lits(op, a, b, la, lb):
  match op:
    case 0n:
      Rw.union_lits(a, b, R.Rw.is_empty_expr(a),
        R.Rw.is_empty_expr(b), la, lb)
    case 1n+x:
      match x:
        case 0n:
          Rw.inter_lits(a, b, R.Rw.is_empty_expr(a),
            R.Rw.is_empty_expr(b), la, lb)
        case 1n+y:
          Rw.diff_lits(a, b, R.Rw.is_empty_expr(a),
            R.Rw.is_empty_expr(b), la, lb)

law Rw.simplify_lits:
  for +e: A.SetExpr
  for +vl: {SetExpr.valid_lits(e) == True{} : Bool}
  {SetExpr.valid_lits(R.Rw.simplify(e)) == True{} : Bool}

def Rw.simplify_lits(e, vl):
  match e:
    case A.EEmpty{}:
      {==}
    case A.EFull{}:
      {==}
    case A.ELit{set}:
      vl
    case A.EUnion{a, b}:
      Rw.join_lits(U32.to_nat(0), R.Rw.simplify(a),
        R.Rw.simplify(b),
        Rw.simplify_lits(a,
          E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)),
        Rw.simplify_lits(b,
          E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)))
    case A.EInter{a, b}:
      Rw.join_lits(U32.to_nat(1), R.Rw.simplify(a),
        R.Rw.simplify(b),
        Rw.simplify_lits(a,
          E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)),
        Rw.simplify_lits(b,
          E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)))
    case A.EDiff{a, b}:
      Rw.join_lits(U32.to_nat(2), R.Rw.simplify(a),
        R.Rw.simplify(b),
        Rw.simplify_lits(a,
          E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)),
        Rw.simplify_lits(b,
          E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)))
    case A.EReach{policy, a}:
      Rw.reach_lits(policy, R.Rw.simplify(a),
        R.Rw.is_empty_expr(R.Rw.simplify(a)),
        Rw.simplify_lits(a, vl))
    case A.EFilter{kind, a}:
      Rw.simplify_lits(a, vl)

# ---------------------------------------------------------------------------
# Each rewrite, as an equality of sets.
# ---------------------------------------------------------------------------

law Ords.agree_rw_union:
  for +l: List<&2, U32>
  for +src: Idx.Source
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +la: {SetExpr.valid_lits(a) == True{} : Bool}
  for +lb: {SetExpr.valid_lits(b) == True{} : Bool}
  {PSet.agree(20n, Q.Den.eval(src, R.Rw.union(a, b,
    R.Rw.is_empty_expr(a), R.Rw.is_empty_expr(b))),
    Q.Den.eval(src, A.EUnion{a, b}), l) == True{} : Bool}

def Ords.agree_rw_union(l, src, a, b, la, lb):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(
        Bool.same(S.PSet.member(20n, Q.Den.eval(src,
          R.Rw.union(a, b, R.Rw.is_empty_expr(a),
            R.Rw.is_empty_expr(b))), y),
          S.PSet.member(20n, Q.Den.eval(src, A.EUnion{a, b}), y)),
        PSet.agree(20n, Q.Den.eval(src, R.Rw.union(a, b,
          R.Rw.is_empty_expr(a), R.Rw.is_empty_expr(b))),
          Q.Den.eval(src, A.EUnion{a, b}), u),
        Bool.same_of_eq(S.PSet.member(20n, Q.Den.eval(src,
          R.Rw.union(a, b, R.Rw.is_empty_expr(a),
            R.Rw.is_empty_expr(b))), y),
          S.PSet.member(20n, Q.Den.eval(src, A.EUnion{a, b}), y),
          Rs.Simp.union_sound(src, a, b, y,
            Dn.Eval.wf(src, a, SetExpr.wf_of_valid_lits(a, la)),
            Dn.Eval.wf(src, b, SetExpr.wf_of_valid_lits(b, lb)))),
        Ords.agree_rw_union(u, src, a, b, la, lb))

law PSet.same_rw_union:
  for +src: Idx.Source
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +la: {SetExpr.valid_lits(a) == True{} : Bool}
  for +lb: {SetExpr.valid_lits(b) == True{} : Bool}
  for +gf: {Src.graphs_fit(src) == True{} : Bool}
  {Ca.PSet.same(20n, Q.Den.eval(src, R.Rw.union(a, b,
    R.Rw.is_empty_expr(a), R.Rw.is_empty_expr(b))),
    Q.Den.eval(src, A.EUnion{a, b})) == True{} : Bool}

def PSet.same_rw_union(src, a, b, la, lb, gf):
  PSet.same_of_agree(20n, Q.Den.eval(src, R.Rw.union(a, b,
    R.Rw.is_empty_expr(a), R.Rw.is_empty_expr(b))),
    Q.Den.eval(src, A.EUnion{a, b}),
    Eval.valid(R.Rw.union(a, b, R.Rw.is_empty_expr(a),
      R.Rw.is_empty_expr(b)), src,
      Rw.union_lits(a, b, R.Rw.is_empty_expr(a),
        R.Rw.is_empty_expr(b), la, lb), gf),
    Eval.valid(A.EUnion{a, b}, src,
      E.Bool.and_both(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
        la, lb), gf), {==},
    Ords.agree_rw_union(S.PSet.to_list(20n, Q.Den.eval(src,
      R.Rw.union(a, b, R.Rw.is_empty_expr(a),
        R.Rw.is_empty_expr(b)))), src, a, b, la, lb),
    Ords.agree_rw_union(S.PSet.to_list(20n,
      Q.Den.eval(src, A.EUnion{a, b})), src, a, b, la, lb))

law Ords.agree_rw_inter:
  for +l: List<&2, U32>
  for +src: Idx.Source
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +la: {SetExpr.valid_lits(a) == True{} : Bool}
  for +lb: {SetExpr.valid_lits(b) == True{} : Bool}
  {PSet.agree(20n, Q.Den.eval(src, R.Rw.inter(a, b,
    R.Rw.is_empty_expr(a), R.Rw.is_empty_expr(b))),
    Q.Den.eval(src, A.EInter{a, b}), l) == True{} : Bool}

def Ords.agree_rw_inter(l, src, a, b, la, lb):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(
        Bool.same(S.PSet.member(20n, Q.Den.eval(src,
          R.Rw.inter(a, b, R.Rw.is_empty_expr(a),
            R.Rw.is_empty_expr(b))), y),
          S.PSet.member(20n, Q.Den.eval(src, A.EInter{a, b}), y)),
        PSet.agree(20n, Q.Den.eval(src, R.Rw.inter(a, b,
          R.Rw.is_empty_expr(a), R.Rw.is_empty_expr(b))),
          Q.Den.eval(src, A.EInter{a, b}), u),
        Bool.same_of_eq(S.PSet.member(20n, Q.Den.eval(src,
          R.Rw.inter(a, b, R.Rw.is_empty_expr(a),
            R.Rw.is_empty_expr(b))), y),
          S.PSet.member(20n, Q.Den.eval(src, A.EInter{a, b}), y),
          Rs.Simp.inter_sound(src, a, b, y,
            Dn.Eval.wf(src, a, SetExpr.wf_of_valid_lits(a, la)),
            Dn.Eval.wf(src, b, SetExpr.wf_of_valid_lits(b, lb)))),
        Ords.agree_rw_inter(u, src, a, b, la, lb))

law PSet.same_rw_inter:
  for +src: Idx.Source
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +la: {SetExpr.valid_lits(a) == True{} : Bool}
  for +lb: {SetExpr.valid_lits(b) == True{} : Bool}
  for +gf: {Src.graphs_fit(src) == True{} : Bool}
  {Ca.PSet.same(20n, Q.Den.eval(src, R.Rw.inter(a, b,
    R.Rw.is_empty_expr(a), R.Rw.is_empty_expr(b))),
    Q.Den.eval(src, A.EInter{a, b})) == True{} : Bool}

def PSet.same_rw_inter(src, a, b, la, lb, gf):
  PSet.same_of_agree(20n, Q.Den.eval(src, R.Rw.inter(a, b,
    R.Rw.is_empty_expr(a), R.Rw.is_empty_expr(b))),
    Q.Den.eval(src, A.EInter{a, b}),
    Eval.valid(R.Rw.inter(a, b, R.Rw.is_empty_expr(a),
      R.Rw.is_empty_expr(b)), src,
      Rw.inter_lits(a, b, R.Rw.is_empty_expr(a),
        R.Rw.is_empty_expr(b), la, lb), gf),
    Eval.valid(A.EInter{a, b}, src,
      E.Bool.and_both(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
        la, lb), gf), {==},
    Ords.agree_rw_inter(S.PSet.to_list(20n, Q.Den.eval(src,
      R.Rw.inter(a, b, R.Rw.is_empty_expr(a),
        R.Rw.is_empty_expr(b)))), src, a, b, la, lb),
    Ords.agree_rw_inter(S.PSet.to_list(20n,
      Q.Den.eval(src, A.EInter{a, b})), src, a, b, la, lb))

law Ords.agree_rw_diff:
  for +l: List<&2, U32>
  for +src: Idx.Source
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +la: {SetExpr.valid_lits(a) == True{} : Bool}
  for +lb: {SetExpr.valid_lits(b) == True{} : Bool}
  {PSet.agree(20n, Q.Den.eval(src, R.Rw.diff(a, b,
    R.Rw.is_empty_expr(a), R.Rw.is_empty_expr(b))),
    Q.Den.eval(src, A.EDiff{a, b}), l) == True{} : Bool}

def Ords.agree_rw_diff(l, src, a, b, la, lb):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(
        Bool.same(S.PSet.member(20n, Q.Den.eval(src,
          R.Rw.diff(a, b, R.Rw.is_empty_expr(a),
            R.Rw.is_empty_expr(b))), y),
          S.PSet.member(20n, Q.Den.eval(src, A.EDiff{a, b}), y)),
        PSet.agree(20n, Q.Den.eval(src, R.Rw.diff(a, b,
          R.Rw.is_empty_expr(a), R.Rw.is_empty_expr(b))),
          Q.Den.eval(src, A.EDiff{a, b}), u),
        Bool.same_of_eq(S.PSet.member(20n, Q.Den.eval(src,
          R.Rw.diff(a, b, R.Rw.is_empty_expr(a),
            R.Rw.is_empty_expr(b))), y),
          S.PSet.member(20n, Q.Den.eval(src, A.EDiff{a, b}), y),
          Rs.Simp.diff_sound(src, a, b, y,
            Dn.Eval.wf(src, a, SetExpr.wf_of_valid_lits(a, la)),
            Dn.Eval.wf(src, b, SetExpr.wf_of_valid_lits(b, lb)))),
        Ords.agree_rw_diff(u, src, a, b, la, lb))

law PSet.same_rw_diff:
  for +src: Idx.Source
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +la: {SetExpr.valid_lits(a) == True{} : Bool}
  for +lb: {SetExpr.valid_lits(b) == True{} : Bool}
  for +gf: {Src.graphs_fit(src) == True{} : Bool}
  {Ca.PSet.same(20n, Q.Den.eval(src, R.Rw.diff(a, b,
    R.Rw.is_empty_expr(a), R.Rw.is_empty_expr(b))),
    Q.Den.eval(src, A.EDiff{a, b})) == True{} : Bool}

def PSet.same_rw_diff(src, a, b, la, lb, gf):
  PSet.same_of_agree(20n, Q.Den.eval(src, R.Rw.diff(a, b,
    R.Rw.is_empty_expr(a), R.Rw.is_empty_expr(b))),
    Q.Den.eval(src, A.EDiff{a, b}),
    Eval.valid(R.Rw.diff(a, b, R.Rw.is_empty_expr(a),
      R.Rw.is_empty_expr(b)), src,
      Rw.diff_lits(a, b, R.Rw.is_empty_expr(a),
        R.Rw.is_empty_expr(b), la, lb), gf),
    Eval.valid(A.EDiff{a, b}, src,
      E.Bool.and_both(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
        la, lb), gf), {==},
    Ords.agree_rw_diff(S.PSet.to_list(20n, Q.Den.eval(src,
      R.Rw.diff(a, b, R.Rw.is_empty_expr(a),
        R.Rw.is_empty_expr(b)))), src, a, b, la, lb),
    Ords.agree_rw_diff(S.PSet.to_list(20n,
      Q.Den.eval(src, A.EDiff{a, b})), src, a, b, la, lb))

law Ords.agree_rw_reach:
  for +l: List<&2, U32>
  for +src: Idx.Source
  for +p: Idx.Policy
  for +a: A.SetExpr
  {PSet.agree(20n,
    Q.Den.eval(src, R.Rw.reach(p, a, R.Rw.is_empty_expr(a))),
    Q.Den.eval(src, A.EReach{p, a}), l) == True{} : Bool}

def Ords.agree_rw_reach(l, src, p, a):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(
        Bool.same(S.PSet.member(20n, Q.Den.eval(src,
          R.Rw.reach(p, a, R.Rw.is_empty_expr(a))), y),
          S.PSet.member(20n, Q.Den.eval(src, A.EReach{p, a}), y)),
        PSet.agree(20n, Q.Den.eval(src,
          R.Rw.reach(p, a, R.Rw.is_empty_expr(a))),
          Q.Den.eval(src, A.EReach{p, a}), u),
        Bool.same_of_eq(S.PSet.member(20n, Q.Den.eval(src,
          R.Rw.reach(p, a, R.Rw.is_empty_expr(a))), y),
          S.PSet.member(20n, Q.Den.eval(src, A.EReach{p, a}), y),
          Rs.Simp.reach_sound(src, p, a, y)),
        Ords.agree_rw_reach(u, src, p, a))

law PSet.same_rw_reach:
  for +src: Idx.Source
  for +p: Idx.Policy
  for +a: A.SetExpr
  for +la: {SetExpr.valid_lits(a) == True{} : Bool}
  for +gf: {Src.graphs_fit(src) == True{} : Bool}
  {Ca.PSet.same(20n,
    Q.Den.eval(src, R.Rw.reach(p, a, R.Rw.is_empty_expr(a))),
    Q.Den.eval(src, A.EReach{p, a})) == True{} : Bool}

def PSet.same_rw_reach(src, p, a, la, gf):
  PSet.same_of_agree(20n,
    Q.Den.eval(src, R.Rw.reach(p, a, R.Rw.is_empty_expr(a))),
    Q.Den.eval(src, A.EReach{p, a}),
    Eval.valid(R.Rw.reach(p, a, R.Rw.is_empty_expr(a)), src,
      Rw.reach_lits(p, a, R.Rw.is_empty_expr(a), la), gf),
    Eval.valid(A.EReach{p, a}, src, la, gf), {==},
    Ords.agree_rw_reach(S.PSet.to_list(20n, Q.Den.eval(src,
      R.Rw.reach(p, a, R.Rw.is_empty_expr(a)))), src, p, a),
    Ords.agree_rw_reach(S.PSet.to_list(20n,
      Q.Den.eval(src, A.EReach{p, a})), src, p, a))

# ---------------------------------------------------------------------------
# The whole pass.
# ---------------------------------------------------------------------------

law Rw.simplify_same:
  for +e: A.SetExpr
  for +src: Idx.Source
  for +vl: {SetExpr.valid_lits(e) == True{} : Bool}
  for +gf: {Src.graphs_fit(src) == True{} : Bool}
  {Ca.PSet.same(20n, Q.Den.eval(src, R.Rw.simplify(e)),
    Q.Den.eval(src, e)) == True{} : Bool}

def Rw.simplify_same.join(+src: Idx.Source, +a: A.SetExpr,
  +b: A.SetExpr, +a2: A.SetExpr, +b2: A.SetExpr,
  +la: {SetExpr.valid_lits(a) == True{} : Bool},
  +lb: {SetExpr.valid_lits(b) == True{} : Bool},
  +la2: {SetExpr.valid_lits(a2) == True{} : Bool},
  +lb2: {SetExpr.valid_lits(b2) == True{} : Bool},
  +gf: {Src.graphs_fit(src) == True{} : Bool},
  +sa: {Ca.PSet.same(20n, Q.Den.eval(src, a2),
    Q.Den.eval(src, a)) == True{} : Bool},
  +sb: {Ca.PSet.same(20n, Q.Den.eval(src, b2),
    Q.Den.eval(src, b)) == True{} : Bool},
  +one: {Ca.PSet.same(20n, Q.Den.eval(src, R.Rw.union(a2, b2,
    R.Rw.is_empty_expr(a2), R.Rw.is_empty_expr(b2))),
    Q.Den.eval(src, A.EUnion{a2, b2})) == True{} : Bool})
  -> {Ca.PSet.same(20n, Q.Den.eval(src, R.Rw.union(a2, b2,
    R.Rw.is_empty_expr(a2), R.Rw.is_empty_expr(b2))),
    Q.Den.eval(src, A.EUnion{a, b})) == True{} : Bool}:
  Ca.PSet.same_trans(20n, Q.Den.eval(src, R.Rw.union(a2, b2,
    R.Rw.is_empty_expr(a2), R.Rw.is_empty_expr(b2))),
    Q.Den.eval(src, A.EUnion{a2, b2}),
    Q.Den.eval(src, A.EUnion{a, b}),
    Eval.valid(R.Rw.union(a2, b2, R.Rw.is_empty_expr(a2),
      R.Rw.is_empty_expr(b2)), src,
      Rw.union_lits(a2, b2, R.Rw.is_empty_expr(a2),
        R.Rw.is_empty_expr(b2), la2, lb2), gf),
    Eval.valid(A.EUnion{a2, b2}, src,
      E.Bool.and_both(SetExpr.valid_lits(a2),
        SetExpr.valid_lits(b2), la2, lb2), gf),
    Eval.valid(A.EUnion{a, b}, src,
      E.Bool.and_both(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
        la, lb), gf), {==}, one,
    PSet.same_union(Q.Den.eval(src, a2), Q.Den.eval(src, b2),
      Q.Den.eval(src, a), Q.Den.eval(src, b),
      Eval.valid(a2, src, la2, gf), Eval.valid(b2, src, lb2, gf),
      Eval.valid(a, src, la, gf), Eval.valid(b, src, lb, gf), sa,
      sb))

def Rw.simplify_same.meet(+src: Idx.Source, +a: A.SetExpr,
  +b: A.SetExpr, +a2: A.SetExpr, +b2: A.SetExpr,
  +la: {SetExpr.valid_lits(a) == True{} : Bool},
  +lb: {SetExpr.valid_lits(b) == True{} : Bool},
  +la2: {SetExpr.valid_lits(a2) == True{} : Bool},
  +lb2: {SetExpr.valid_lits(b2) == True{} : Bool},
  +gf: {Src.graphs_fit(src) == True{} : Bool},
  +sa: {Ca.PSet.same(20n, Q.Den.eval(src, a2),
    Q.Den.eval(src, a)) == True{} : Bool},
  +sb: {Ca.PSet.same(20n, Q.Den.eval(src, b2),
    Q.Den.eval(src, b)) == True{} : Bool},
  +one: {Ca.PSet.same(20n, Q.Den.eval(src, R.Rw.inter(a2, b2,
    R.Rw.is_empty_expr(a2), R.Rw.is_empty_expr(b2))),
    Q.Den.eval(src, A.EInter{a2, b2})) == True{} : Bool})
  -> {Ca.PSet.same(20n, Q.Den.eval(src, R.Rw.inter(a2, b2,
    R.Rw.is_empty_expr(a2), R.Rw.is_empty_expr(b2))),
    Q.Den.eval(src, A.EInter{a, b})) == True{} : Bool}:
  Ca.PSet.same_trans(20n, Q.Den.eval(src, R.Rw.inter(a2, b2,
    R.Rw.is_empty_expr(a2), R.Rw.is_empty_expr(b2))),
    Q.Den.eval(src, A.EInter{a2, b2}),
    Q.Den.eval(src, A.EInter{a, b}),
    Eval.valid(R.Rw.inter(a2, b2, R.Rw.is_empty_expr(a2),
      R.Rw.is_empty_expr(b2)), src,
      Rw.inter_lits(a2, b2, R.Rw.is_empty_expr(a2),
        R.Rw.is_empty_expr(b2), la2, lb2), gf),
    Eval.valid(A.EInter{a2, b2}, src,
      E.Bool.and_both(SetExpr.valid_lits(a2),
        SetExpr.valid_lits(b2), la2, lb2), gf),
    Eval.valid(A.EInter{a, b}, src,
      E.Bool.and_both(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
        la, lb), gf), {==}, one,
    PSet.same_inter(Q.Den.eval(src, a2), Q.Den.eval(src, b2),
      Q.Den.eval(src, a), Q.Den.eval(src, b),
      Eval.valid(a2, src, la2, gf), Eval.valid(b2, src, lb2, gf),
      Eval.valid(a, src, la, gf), Eval.valid(b, src, lb, gf), sa,
      sb))

def Rw.simplify_same.less(+src: Idx.Source, +a: A.SetExpr,
  +b: A.SetExpr, +a2: A.SetExpr, +b2: A.SetExpr,
  +la: {SetExpr.valid_lits(a) == True{} : Bool},
  +lb: {SetExpr.valid_lits(b) == True{} : Bool},
  +la2: {SetExpr.valid_lits(a2) == True{} : Bool},
  +lb2: {SetExpr.valid_lits(b2) == True{} : Bool},
  +gf: {Src.graphs_fit(src) == True{} : Bool},
  +sa: {Ca.PSet.same(20n, Q.Den.eval(src, a2),
    Q.Den.eval(src, a)) == True{} : Bool},
  +sb: {Ca.PSet.same(20n, Q.Den.eval(src, b2),
    Q.Den.eval(src, b)) == True{} : Bool},
  +one: {Ca.PSet.same(20n, Q.Den.eval(src, R.Rw.diff(a2, b2,
    R.Rw.is_empty_expr(a2), R.Rw.is_empty_expr(b2))),
    Q.Den.eval(src, A.EDiff{a2, b2})) == True{} : Bool})
  -> {Ca.PSet.same(20n, Q.Den.eval(src, R.Rw.diff(a2, b2,
    R.Rw.is_empty_expr(a2), R.Rw.is_empty_expr(b2))),
    Q.Den.eval(src, A.EDiff{a, b})) == True{} : Bool}:
  Ca.PSet.same_trans(20n, Q.Den.eval(src, R.Rw.diff(a2, b2,
    R.Rw.is_empty_expr(a2), R.Rw.is_empty_expr(b2))),
    Q.Den.eval(src, A.EDiff{a2, b2}),
    Q.Den.eval(src, A.EDiff{a, b}),
    Eval.valid(R.Rw.diff(a2, b2, R.Rw.is_empty_expr(a2),
      R.Rw.is_empty_expr(b2)), src,
      Rw.diff_lits(a2, b2, R.Rw.is_empty_expr(a2),
        R.Rw.is_empty_expr(b2), la2, lb2), gf),
    Eval.valid(A.EDiff{a2, b2}, src,
      E.Bool.and_both(SetExpr.valid_lits(a2),
        SetExpr.valid_lits(b2), la2, lb2), gf),
    Eval.valid(A.EDiff{a, b}, src,
      E.Bool.and_both(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
        la, lb), gf), {==}, one,
    PSet.same_diff(Q.Den.eval(src, a2), Q.Den.eval(src, b2),
      Q.Den.eval(src, a), Q.Den.eval(src, b),
      Eval.valid(a2, src, la2, gf), Eval.valid(b2, src, lb2, gf),
      Eval.valid(a, src, la, gf), Eval.valid(b, src, lb, gf), sa,
      sb))

def Rw.simplify_same.close(+src: Idx.Source, +p: Idx.Policy,
  +a: A.SetExpr, +a2: A.SetExpr,
  +la: {SetExpr.valid_lits(a) == True{} : Bool},
  +la2: {SetExpr.valid_lits(a2) == True{} : Bool},
  +gf: {Src.graphs_fit(src) == True{} : Bool},
  +sa: {Ca.PSet.same(20n, Q.Den.eval(src, a2),
    Q.Den.eval(src, a)) == True{} : Bool})
  -> {Ca.PSet.same(20n,
    Q.Den.eval(src, R.Rw.reach(p, a2, R.Rw.is_empty_expr(a2))),
    Q.Den.eval(src, A.EReach{p, a})) == True{} : Bool}:
  Ca.PSet.same_trans(20n,
    Q.Den.eval(src, R.Rw.reach(p, a2, R.Rw.is_empty_expr(a2))),
    Q.Den.eval(src, A.EReach{p, a2}),
    Q.Den.eval(src, A.EReach{p, a}),
    Eval.valid(R.Rw.reach(p, a2, R.Rw.is_empty_expr(a2)), src,
      Rw.reach_lits(p, a2, R.Rw.is_empty_expr(a2), la2), gf),
    Eval.valid(A.EReach{p, a2}, src, la2, gf),
    Eval.valid(A.EReach{p, a}, src, la, gf), {==},
    PSet.same_rw_reach(src, p, a2, la2, gf),
    PSet.same_reach(Idx.Source.n(src), Idx.Source.graph(src, p),
      Q.Den.eval(src, a2), Q.Den.eval(src, a),
      Eval.valid(a2, src, la2, gf), Eval.valid(a, src, la, gf),
      Src.graph_fit(src, p, gf), sa))

def Rw.simplify_same(e, src, vl, gf):
  match e:
    case A.EEmpty{}:
      Ca.PSet.same_refl(20n, Q.Den.eval(src, A.EEmpty{}),
        Eval.valid(A.EEmpty{}, src, vl, gf), {==})
    case A.EFull{}:
      Ca.PSet.same_refl(20n, Q.Den.eval(src, A.EFull{}),
        Eval.valid(A.EFull{}, src, vl, gf), {==})
    case A.ELit{set}:
      Ca.PSet.same_refl(20n, Q.Den.eval(src, A.ELit{set}),
        Eval.valid(A.ELit{set}, src, vl, gf), {==})
    case A.EUnion{a, b}:
      Rw.simplify_same.join(src, a, b, R.Rw.simplify(a),
        R.Rw.simplify(b),
        E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
          vl),
        E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
          vl),
        Rw.simplify_lits(a,
          E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)),
        Rw.simplify_lits(b,
          E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)), gf,
        Rw.simplify_same(a, src,
          E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl), gf),
        Rw.simplify_same(b, src,
          E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl), gf),
        PSet.same_rw_union(src, R.Rw.simplify(a), R.Rw.simplify(b),
          Rw.simplify_lits(a,
            E.Bool.and_l(SetExpr.valid_lits(a),
              SetExpr.valid_lits(b), vl)),
          Rw.simplify_lits(b,
            E.Bool.and_r(SetExpr.valid_lits(a),
              SetExpr.valid_lits(b), vl)), gf))
    case A.EInter{a, b}:
      Rw.simplify_same.meet(src, a, b, R.Rw.simplify(a),
        R.Rw.simplify(b),
        E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
          vl),
        E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
          vl),
        Rw.simplify_lits(a,
          E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)),
        Rw.simplify_lits(b,
          E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)), gf,
        Rw.simplify_same(a, src,
          E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl), gf),
        Rw.simplify_same(b, src,
          E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl), gf),
        PSet.same_rw_inter(src, R.Rw.simplify(a), R.Rw.simplify(b),
          Rw.simplify_lits(a,
            E.Bool.and_l(SetExpr.valid_lits(a),
              SetExpr.valid_lits(b), vl)),
          Rw.simplify_lits(b,
            E.Bool.and_r(SetExpr.valid_lits(a),
              SetExpr.valid_lits(b), vl)), gf))
    case A.EDiff{a, b}:
      Rw.simplify_same.less(src, a, b, R.Rw.simplify(a),
        R.Rw.simplify(b),
        E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
          vl),
        E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
          vl),
        Rw.simplify_lits(a,
          E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)),
        Rw.simplify_lits(b,
          E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl)), gf,
        Rw.simplify_same(a, src,
          E.Bool.and_l(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl), gf),
        Rw.simplify_same(b, src,
          E.Bool.and_r(SetExpr.valid_lits(a), SetExpr.valid_lits(b),
            vl), gf),
        PSet.same_rw_diff(src, R.Rw.simplify(a), R.Rw.simplify(b),
          Rw.simplify_lits(a,
            E.Bool.and_l(SetExpr.valid_lits(a),
              SetExpr.valid_lits(b), vl)),
          Rw.simplify_lits(b,
            E.Bool.and_r(SetExpr.valid_lits(a),
              SetExpr.valid_lits(b), vl)), gf))
    case A.EReach{policy, a}:
      Rw.simplify_same.close(src, policy, a, R.Rw.simplify(a), vl,
        Rw.simplify_lits(a, vl), gf,
        Rw.simplify_same(a, src, vl, gf))
    case A.EFilter{kind, a}:
      PSet.same_filter(src, kind, Q.Den.eval(src, R.Rw.simplify(a)),
        Q.Den.eval(src, a),
        Eval.valid(R.Rw.simplify(a), src,
          Rw.simplify_lits(a, vl), gf),
        Eval.valid(a, src, vl, gf),
        Rw.simplify_same(a, src, vl, gf))

law Rw.simplify_member:
  for +src: Idx.Source
  for +e: A.SetExpr
  for +x: U32
  for +vl: {SetExpr.valid_lits(e) == True{} : Bool}
  for +gf: {Src.graphs_fit(src) == True{} : Bool}
  {S.PSet.member(20n, Q.Den.eval(src, R.Rw.simplify(e)), x)
    == S.PSet.member(20n, Q.Den.eval(src, e), x) : Bool}

def Rw.simplify_member(src, e, x, vl, gf):
  Ca.PSet.member_same(20n, Q.Den.eval(src, R.Rw.simplify(e)),
    Q.Den.eval(src, e), x,
    Eval.valid(R.Rw.simplify(e), src, Rw.simplify_lits(e, vl), gf),
    Eval.valid(e, src, vl, gf), {==}, Dc.U32.hi_zero_full(x),
    Rw.simplify_same(e, src, vl, gf))
