# proofs/evalmach.bend -- the production evaluator computes the denotation
# (law Q-03).
#
# `Ev.go` is an explicit machine -- a control word, a stack of frames, one
# tail call per step -- because this runtime will not compile the obvious
# two-self-call fold. So the proof is the usual one for such a machine: give
# the stack a meaning, and show every step keeps the meaning of the whole
# configuration.
#
# `Ev.plug` is that meaning: the denotation the frames would produce from a
# set handed to them. Every step but one is then definitional -- pushing a
# frame and evaluating a subexpression is exactly what `plug` unfolds to. The
# one step that is not is `Reach`, where the machine runs the frontier
# traversal and `plug` names the specification closure; law C-02 is what
# closes that gap, and it is why the equality carried is `PSet.same` rather
# than a value equality.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./shift.bend as Sf
import ./shape.bend as Sh
import ./setops.bend as So
import ./treeenum.bend as Te
import ./split_add.bend as Sa2
import ./subsetconv.bend as Sc
import ./subsetalg.bend as Sa
import ./validkeep.bend as Vk
import ./listset.bend as Ls
import ./insertvalid.bend as Iv
import ./listsub.bend as Lb
import ./graphrange.bend as Gr
import ./postmono.bend as Pm
import ./lfp.bend as Lp
import ./closalg.bend as Ca
import ./settle.bend as St
import ./traversal.bend as Tl
import ./validshape.bend as Vs
import ./rwpass.bend as Rp
import ../core/count.bend as C
import ../core/set.bend as S
import ../closure/graph.bend as G
import ../closure/reach.bend as R
import ../spec/closure.bend as Sp
import ../spec/query.bend as Q
import ../query/ast.bend as A
import ../query/eval.bend as Qe
import ../query/rewrite.bend as Rw
import ../index/source.bend as Idx

# ---------------------------------------------------------------------------
# What a stack means.
# ---------------------------------------------------------------------------

def Ev.plug(+src: Idx.Source, k: List<&2, Qe.Frame>,
  s: S.PSet) -> S.PSet:
  match k:
    case Nil{}:
      s
    case Con{f, rest}:
      match f:
        case Qe.FRight{op, rhs}:
          Ev.plug(src, rest,
            Qe.Ev.apply(s, Q.Den.eval(src, rhs), op))
        case Qe.FComb{op, lhs}:
          Ev.plug(src, rest, Qe.Ev.apply(lhs, s, op))
        case Qe.FFilter{kind}:
          Ev.plug(src, rest, Q.Den.filter(src, kind, s))
        case Qe.FReach{policy}:
          Ev.plug(src, rest,
            Sp.Spec.closure(Idx.Source.n(src), 32n,
              Idx.Source.graph(src, policy), 20n, s))

def Ev.ctl(+src: Idx.Source, c: Qe.Ctl) -> S.PSet:
  match c:
    case Qe.CEval{e}:
      Q.Den.eval(src, e)
    case Qe.CVal{v}:
      v

def Ev.lits_in(+uu: S.PSet, +e: A.SetExpr) -> Bool:
  match e:
    case A.EEmpty{}:
      True{}
    case A.EFull{}:
      True{}
    case A.ELit{set}:
      S.PSet.is_subset(20n, set, uu)
    case A.EUnion{a, b}:
      Bool.and(Ev.lits_in(uu, a), Ev.lits_in(uu, b))
    case A.EInter{a, b}:
      Bool.and(Ev.lits_in(uu, a), Ev.lits_in(uu, b))
    case A.EDiff{a, b}:
      Bool.and(Ev.lits_in(uu, a), Ev.lits_in(uu, b))
    case A.EReach{policy, a}:
      Ev.lits_in(uu, a)
    case A.EFilter{kind, a}:
      Ev.lits_in(uu, a)

def Ev.frame_ok(+uu: S.PSet, +f: Qe.Frame) -> Bool:
  match f:
    case Qe.FRight{op, rhs}:
      Bool.and(Rp.SetExpr.valid_lits(rhs), Ev.lits_in(uu, rhs))
    case Qe.FComb{op, lhs}:
      Bool.and(S.PSet.valid(20n, lhs, True{}),
        S.PSet.is_subset(20n, lhs, uu))
    case Qe.FFilter{kind}:
      True{}
    case Qe.FReach{policy}:
      True{}

def Ev.stack_ok(+uu: S.PSet, +k: List<&2, Qe.Frame>) -> Bool:
  match k:
    case Nil{}:
      True{}
    case Con{f, rest}:
      Bool.and(Ev.frame_ok(uu, f), Ev.stack_ok(uu, rest))

def Ev.ctl_ok(+uu: S.PSet, +c: Qe.Ctl) -> Bool:
  match c:
    case Qe.CEval{e}:
      Bool.and(Rp.SetExpr.valid_lits(e), Ev.lits_in(uu, e))
    case Qe.CVal{v}:
      Bool.and(S.PSet.valid(20n, v, True{}),
        S.PSet.is_subset(20n, v, uu))

law Ev.go_not_ok:
  for +fuel: Nat
  for +src: Idx.Source
  for +c: Qe.Ctl
  for +k: List<&2, Qe.Frame>
  {Qe.Val.ok(Qe.Ev.go(fuel, src, c, k, False{})) == False{} : Bool}

def Ev.go_not_ok(fuel, src, c, k):
  match fuel:
    case 0n:
      {==}
    case 1n+g:
      match c:
        case Qe.CVal{v}:
          match k:
            case Nil{}:
              {==}
            case Con{f, rest}:
              match f:
                case Qe.FRight{op, rhs}:
                  Ev.go_not_ok(g, src, Qe.CEval{rhs},
                    Con{Qe.FComb{op, v}, rest})
                case Qe.FComb{op, lhs}:
                  Ev.go_not_ok(g, src,
                    Qe.CVal{Qe.Ev.apply(lhs, v, op)}, rest)
                case Qe.FFilter{kind}:
                  Ev.go_not_ok(g, src,
                    Qe.CVal{Q.Den.filter(src, kind, v)}, rest)
                case Qe.FReach{policy}:
                  Ev.go_not_ok(g, src,
                    Qe.CVal{R.Reach.seen(20n,
                      R.Reach.closure(Idx.Source.n(src), 32n,
                        Idx.Source.graph(src, policy), 20n,
                        S.PSet.to_list(20n, v)))},
                    Qe.Ev.reach.stack(R.Reach.done(20n,
                      R.Reach.closure(Idx.Source.n(src), 32n,
                        Idx.Source.graph(src, policy), 20n,
                        S.PSet.to_list(20n, v))), rest))
        case Qe.CEval{e}:
          match e:
            case A.EEmpty{}:
              Ev.go_not_ok(g, src, Qe.CVal{S.PSet.empty()}, k)
            case A.EFull{}:
              Ev.go_not_ok(g, src,
                Qe.CVal{Q.Den.universe(Idx.Source.n(src))}, k)
            case A.ELit{set}:
              Ev.go_not_ok(g, src, Qe.CVal{set}, k)
            case A.EUnion{a, b}:
              Ev.go_not_ok(g, src, Qe.CEval{a},
                Con{Qe.FRight{0n, b}, k})
            case A.EInter{a, b}:
              Ev.go_not_ok(g, src, Qe.CEval{a},
                Con{Qe.FRight{1n, b}, k})
            case A.EDiff{a, b}:
              Ev.go_not_ok(g, src, Qe.CEval{a},
                Con{Qe.FRight{2n, b}, k})
            case A.EReach{policy, a}:
              Ev.go_not_ok(g, src, Qe.CEval{a},
                Con{Qe.FReach{policy}, k})
            case A.EFilter{kind, a}:
              Ev.go_not_ok(g, src, Qe.CEval{a},
                Con{Qe.FFilter{kind}, k})

# ---------------------------------------------------------------------------
# Small set facts the machine needs.
# ---------------------------------------------------------------------------

law PSet.subset_zero:
  for +d: Nat
  for +xx: S.PSet
  for +vx: {S.PSet.valid(d, xx, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {S.PSet.is_subset(d, S.PZero{}, xx) == True{} : Bool}

law PSet.to_list_zero:
  for +d: Nat
  {S.PSet.to_list(d, S.PZero{}) == Nil{} : List<&2, U32>}

def PSet.to_list_zero(d):
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

def PSet.subset_zero(d, xx, vx, lt):
  Sc.PSet.subset_of_members(d, S.PZero{}, xx, Vk.PSet.valid_zero(d),
    vx, lt,
    %E.List.sym(U32, S.PSet.to_list(d, S.PZero{}), Nil{},
      PSet.to_list_zero(d))
      : {Sc.Ords.all_mem(_, d, xx) == True{} : Bool}
    {==})

law Ords.all_mem_inter:
  for +l: List<&2, U32>
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l,
    S.PSet.to_list(d, S.PSet.inter(d, a, b))) == True{} : Bool}
  {Sc.Ords.all_mem(l, d, a) == True{} : Bool}

def Ords.all_mem_inter(l, d, a, b, va, vb, lt, ai):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(S.PSet.member(d, a, y),
        Sc.Ords.all_mem(u, d, a),
        E.Bool.and_l(S.PSet.member(d, a, y), S.PSet.member(d, b, y),
          %So.PSet.inter_pointwise(d, a, b, S.PSet.half(d), y, {==},
            lt, Sh.PSet.valid_wf(d, a, va),
            Sh.PSet.valid_wf(d, b, vb),
            Sa.PSet.in_range_of_to_list(d, S.PSet.inter(d, a, b), y,
              Vk.PSet.valid_inter(d, a, b, va, vb), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(d, S.PSet.inter(d, a, b)), y),
                Sa.Ords.all_in(u, S.PSet.to_list(d,
                  S.PSet.inter(d, a, b))), ai)),
            U32.is_lt(y, S.PSet.half(d)), {==})
            : {_ == True{} : Bool}
          Sa.PSet.member_of_to_list(d, S.PSet.inter(d, a, b), y,
            Vk.PSet.valid_inter(d, a, b, va, vb), lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(d, S.PSet.inter(d, a, b)), y),
              Sa.Ords.all_in(u, S.PSet.to_list(d,
                S.PSet.inter(d, a, b))), ai))),
        Ords.all_mem_inter(u, d, a, b, va, vb, lt,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(d, S.PSet.inter(d, a, b)), y),
            Sa.Ords.all_in(u, S.PSet.to_list(d,
              S.PSet.inter(d, a, b))), ai)))

law PSet.subset_inter_l:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {S.PSet.is_subset(d, S.PSet.inter(d, a, b), a) == True{} : Bool}

def PSet.subset_inter_l(d, a, b, va, vb, lt):
  Sc.PSet.subset_of_members(d, S.PSet.inter(d, a, b), a,
    Vk.PSet.valid_inter(d, a, b, va, vb), va, lt,
    Ords.all_mem_inter(S.PSet.to_list(d, S.PSet.inter(d, a, b)), d,
      a, b, va, vb, lt,
      Sa.Ords.all_in_self(S.PSet.to_list(d, S.PSet.inter(d, a, b)))))

law Ords.all_mem_diff:
  for +l: List<&2, U32>
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l,
    S.PSet.to_list(d, S.PSet.diff(d, a, b))) == True{} : Bool}
  {Sc.Ords.all_mem(l, d, a) == True{} : Bool}

def Ords.all_mem_diff(l, d, a, b, va, vb, lt, ai):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(S.PSet.member(d, a, y),
        Sc.Ords.all_mem(u, d, a),
        E.Bool.and_l(S.PSet.member(d, a, y),
          Bool.not(S.PSet.member(d, b, y)),
          %So.PSet.diff_pointwise(d, a, b, S.PSet.half(d), y, {==},
            lt, Sh.PSet.valid_wf(d, a, va),
            Sh.PSet.valid_wf(d, b, vb),
            Sa.PSet.in_range_of_to_list(d, S.PSet.diff(d, a, b), y,
              Vk.PSet.valid_diff(d, a, b, va, vb), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(d, S.PSet.diff(d, a, b)), y),
                Sa.Ords.all_in(u, S.PSet.to_list(d,
                  S.PSet.diff(d, a, b))), ai)),
            U32.is_lt(y, S.PSet.half(d)), {==})
            : {_ == True{} : Bool}
          Sa.PSet.member_of_to_list(d, S.PSet.diff(d, a, b), y,
            Vk.PSet.valid_diff(d, a, b, va, vb), lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(d, S.PSet.diff(d, a, b)), y),
              Sa.Ords.all_in(u, S.PSet.to_list(d,
                S.PSet.diff(d, a, b))), ai))),
        Ords.all_mem_diff(u, d, a, b, va, vb, lt,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(d, S.PSet.diff(d, a, b)), y),
            Sa.Ords.all_in(u, S.PSet.to_list(d,
              S.PSet.diff(d, a, b))), ai)))

law PSet.subset_diff_l:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {S.PSet.is_subset(d, S.PSet.diff(d, a, b), a) == True{} : Bool}

def PSet.subset_diff_l(d, a, b, va, vb, lt):
  Sc.PSet.subset_of_members(d, S.PSet.diff(d, a, b), a,
    Vk.PSet.valid_diff(d, a, b, va, vb), va, lt,
    Ords.all_mem_diff(S.PSet.to_list(d, S.PSet.diff(d, a, b)), d, a,
      b, va, vb, lt,
      Sa.Ords.all_in_self(S.PSet.to_list(d, S.PSet.diff(d, a, b)))))

law PSet.valid_apply:
  for +op: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(20n, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(20n, b, True{}) == True{} : Bool}
  {S.PSet.valid(20n, Qe.Ev.apply(a, b, op), True{}) == True{} : Bool}

def PSet.valid_apply(op, a, b, va, vb):
  match op:
    case 0n:
      Vk.PSet.valid_union(20n, a, b, va, vb)
    case 1n+x:
      match x:
        case 0n:
          Vk.PSet.valid_inter(20n, a, b, va, vb)
        case 1n+y:
          Vk.PSet.valid_diff(20n, a, b, va, vb)

law PSet.apply_inside:
  for +op: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +uu: S.PSet
  for +va: {S.PSet.valid(20n, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(20n, b, True{}) == True{} : Bool}
  for +vu: {S.PSet.valid(20n, uu, True{}) == True{} : Bool}
  for +au: {S.PSet.is_subset(20n, a, uu) == True{} : Bool}
  for +bu: {S.PSet.is_subset(20n, b, uu) == True{} : Bool}
  {S.PSet.is_subset(20n, Qe.Ev.apply(a, b, op), uu) == True{} : Bool}

def PSet.apply_inside(op, a, b, uu, va, vb, vu, au, bu):
  match op:
    case 0n:
      Sa.PSet.subset_union(20n, a, b, uu, va, vb, vu, {==}, au, bu)
    case 1n+x:
      match x:
        case 0n:
          Sa.PSet.subset_trans(20n, S.PSet.inter(20n, a, b), a, uu,
            Vk.PSet.valid_inter(20n, a, b, va, vb), va, vu, {==},
            PSet.subset_inter_l(20n, a, b, va, vb, {==}), au)
        case 1n+y:
          Sa.PSet.subset_trans(20n, S.PSet.diff(20n, a, b), a, uu,
            Vk.PSet.valid_diff(20n, a, b, va, vb), va, vu, {==},
            PSet.subset_diff_l(20n, a, b, va, vb, {==}), au)

law PSet.same_apply:
  for +op: Nat
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
  {Ca.PSet.same(20n, Qe.Ev.apply(pa, pb, op),
    Qe.Ev.apply(qa, qb, op)) == True{} : Bool}

def PSet.same_apply(op, pa, pb, qa, qb, vpa, vpb, vqa, vqb, sa, sb):
  match op:
    case 0n:
      Rp.PSet.same_union(pa, pb, qa, qb, vpa, vpb, vqa, vqb, sa, sb)
    case 1n+x:
      match x:
        case 0n:
          Rp.PSet.same_inter(pa, pb, qa, qb, vpa, vpb, vqa, vqb, sa,
            sb)
        case 1n+y:
          Rp.PSet.same_diff(pa, pb, qa, qb, vpa, vpb, vqa, vqb, sa,
            sb)

law Ords.all_mem_keep:
  for +l: List<&2, U32>
  for +src: Idx.Source
  for +kind: U32
  for +s: S.PSet
  for +vs: {S.PSet.valid(20n, s, True{}) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l, S.PSet.to_list(20n, s)) == True{}
    : Bool}
  {Sc.Ords.all_mem(Q.Den.keep(src, kind, l), 20n, s) == True{}
    : Bool}

def Ords.all_mem_keep.pick(+t: List<&2, U32>, +src: Idx.Source,
  +kind: U32, +s: S.PSet, +y: U32, +hx: Bool,
  +ehx: {hx == Rp.Den.hit(src, kind, y) : Bool},
  +my: {S.PSet.member(20n, s, y) == True{} : Bool},
  +ih: {Sc.Ords.all_mem(Q.Den.keep(src, kind, t), 20n, s)
    == True{} : Bool})
  -> {Sc.Ords.all_mem(Q.Den.keep.pick(y,
    Q.Den.keep(src, kind, t), hx), 20n, s) == True{} : Bool}:
  match hx:
    case True{}:
      E.Bool.and_both(S.PSet.member(20n, s, y),
        Sc.Ords.all_mem(Q.Den.keep(src, kind, t), 20n, s), my, ih)
    case False{}:
      ih

def Ords.all_mem_keep(l, src, kind, s, vs, ai):
  match l:
    case Nil{}:
      {==}
    case Con{y, t}:
      Ords.all_mem_keep.pick(t, src, kind, s, y,
        Rp.Den.hit(src, kind, y), {==},
        Sa.PSet.member_of_to_list(20n, s, y, vs, {==},
          E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(20n, s), y),
            Sa.Ords.all_in(t, S.PSet.to_list(20n, s)), ai)),
        Ords.all_mem_keep(t, src, kind, s, vs,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(20n, s), y),
            Sa.Ords.all_in(t, S.PSet.to_list(20n, s)), ai)))

law PSet.subset_filter:
  for +src: Idx.Source
  for +kind: U32
  for +s: S.PSet
  for +vs: {S.PSet.valid(20n, s, True{}) == True{} : Bool}
  {S.PSet.is_subset(20n, Q.Den.filter(src, kind, s), s) == True{}
    : Bool}

def PSet.subset_filter(src, kind, s, vs):
  Lb.PSet.subset_of_list_mem(
    Q.Den.keep(src, kind, S.PSet.to_list(20n, s)), 20n, s, {==},
    Rp.Ords.all_fit_32(
      Q.Den.keep(src, kind, S.PSet.to_list(20n, s))), vs,
    Ords.all_mem_keep(S.PSet.to_list(20n, s), src, kind, s, vs,
      Sa.Ords.all_in_self(S.PSet.to_list(20n, s))))

law Spec.iter_in:
  for +f: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +uu: S.PSet
  for +x: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +su: {Gr.Graph.succs_in(sd, uu, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vu: {S.PSet.valid(sd, uu, True{}) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool}
  for +xu: {S.PSet.is_subset(sd, x, uu) == True{} : Bool}
  {S.PSet.is_subset(sd, Sp.Spec.iter(f, td, g, sd, x), uu) == True{}
    : Bool}

def Spec.iter_in(f, td, sd, g, uu, x, gf, su, lt, vu, vx, xu):
  match f:
    case 0n:
      xu
    case 1n+p:
      Spec.iter_in(p, td, sd, g, uu, Sp.Spec.step(td, g, sd, x), gf,
        su, lt, vu, Lp.Spec.step_valid(td, sd, g, x, gf, lt, vx),
        St.Spec.step_in(td, sd, g, uu, x, gf, su, lt, vu, vx, xu))

law PSet.agree_roundtrip:
  for +l: List<&2, U32>
  for +s: S.PSet
  for +vs: {S.PSet.valid(20n, s, True{}) == True{} : Bool}
  {Rp.PSet.agree(20n,
    S.PSet.from_list(20n, S.PSet.to_list(20n, s)), s, l) == True{}
    : Bool}

def PSet.agree_roundtrip(l, s, vs):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(Rp.Bool.same(S.PSet.member(20n,
        S.PSet.from_list(20n, S.PSet.to_list(20n, s)), y),
        S.PSet.member(20n, s, y)),
        Rp.PSet.agree(20n,
          S.PSet.from_list(20n, S.PSet.to_list(20n, s)), s, u),
        Rp.Bool.same_of_eq(S.PSet.member(20n,
          S.PSet.from_list(20n, S.PSet.to_list(20n, s)), y),
          S.PSet.member(20n, s, y),
          Equal.trans(Bool, S.PSet.member(20n,
            S.PSet.from_list(20n, S.PSet.to_list(20n, s)), y),
            List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(20n, s), y), S.PSet.member(20n, s, y),
            Rp.PSet.member_of_list(S.PSet.to_list(20n, s), 20n, y,
              {==}, Dc.U32.hi_zero_full(y),
              Rp.Ords.all_fit_32(S.PSet.to_list(20n, s))),
            Vs.PSet.to_list_member_of_valid(20n, s, y, vs, {==},
              Dc.U32.hi_zero_full(y)))),
        PSet.agree_roundtrip(u, s, vs))

law PSet.same_roundtrip:
  for +s: S.PSet
  for +vs: {S.PSet.valid(20n, s, True{}) == True{} : Bool}
  {Ca.PSet.same(20n,
    S.PSet.from_list(20n, S.PSet.to_list(20n, s)), s) == True{}
    : Bool}

def PSet.same_roundtrip(s, vs):
  Rp.PSet.same_of_agree(20n,
    S.PSet.from_list(20n, S.PSet.to_list(20n, s)), s,
    Iv.PSet.valid_from_list(S.PSet.to_list(20n, s), 20n, {==},
      Rp.Ords.all_fit_32(S.PSet.to_list(20n, s))), vs, {==},
    PSet.agree_roundtrip(S.PSet.to_list(20n,
      S.PSet.from_list(20n, S.PSet.to_list(20n, s))), s, vs),
    PSet.agree_roundtrip(S.PSet.to_list(20n, s), s, vs))

# ---------------------------------------------------------------------------
# The stack's meaning is a valid set, and a congruence.
# ---------------------------------------------------------------------------

law Ev.plug_valid:
  for +k: List<&2, Qe.Frame>
  for +src: Idx.Source
  for +uu: S.PSet
  for +s: S.PSet
  for +gf: {Rp.Src.graphs_fit(src) == True{} : Bool}
  for +ko: {Ev.stack_ok(uu, k) == True{} : Bool}
  for +vs: {S.PSet.valid(20n, s, True{}) == True{} : Bool}
  {S.PSet.valid(20n, Ev.plug(src, k, s), True{}) == True{} : Bool}

def Ev.plug_valid(k, src, uu, s, gf, ko, vs):
  match k:
    case Nil{}:
      vs
    case Con{f, rest}:
      match f:
        case Qe.FRight{op, rhs}:
          Ev.plug_valid(rest, src, uu,
            Qe.Ev.apply(s, Q.Den.eval(src, rhs), op), gf,
            E.Bool.and_r(Ev.frame_ok(uu, Qe.FRight{op, rhs}),
              Ev.stack_ok(uu, rest), ko),
            PSet.valid_apply(op, s, Q.Den.eval(src, rhs), vs,
              Rp.Eval.valid(rhs, src,
                E.Bool.and_l(Rp.SetExpr.valid_lits(rhs),
                  Ev.lits_in(uu, rhs),
                  E.Bool.and_l(Ev.frame_ok(uu, Qe.FRight{op, rhs}),
                    Ev.stack_ok(uu, rest), ko)), gf)))
        case Qe.FComb{op, lhs}:
          Ev.plug_valid(rest, src, uu, Qe.Ev.apply(lhs, s, op), gf,
            E.Bool.and_r(Ev.frame_ok(uu, Qe.FComb{op, lhs}),
              Ev.stack_ok(uu, rest), ko),
            PSet.valid_apply(op, lhs, s,
              E.Bool.and_l(S.PSet.valid(20n, lhs, True{}),
                S.PSet.is_subset(20n, lhs, uu),
                E.Bool.and_l(Ev.frame_ok(uu, Qe.FComb{op, lhs}),
                  Ev.stack_ok(uu, rest), ko)), vs))
        case Qe.FFilter{kind}:
          Ev.plug_valid(rest, src, uu, Q.Den.filter(src, kind, s),
            gf,
            E.Bool.and_r(Ev.frame_ok(uu, Qe.FFilter{kind}),
              Ev.stack_ok(uu, rest), ko),
            Iv.PSet.valid_from_list(
              Q.Den.keep(src, kind, S.PSet.to_list(20n, s)), 20n,
              {==}, Rp.Ords.all_fit_32(
                Q.Den.keep(src, kind, S.PSet.to_list(20n, s)))))
        case Qe.FReach{policy}:
          Ev.plug_valid(rest, src, uu,
            Sp.Spec.closure(Idx.Source.n(src), 32n,
              Idx.Source.graph(src, policy), 20n, s), gf,
            E.Bool.and_r(Ev.frame_ok(uu, Qe.FReach{policy}),
              Ev.stack_ok(uu, rest), ko),
            Lp.Spec.closure_valid(Idx.Source.n(src), 32n, 20n,
              Idx.Source.graph(src, policy), s,
              Rp.Src.graph_fit(src, policy, gf), {==}, vs))

law Ev.plug_same:
  for +k: List<&2, Qe.Frame>
  for +src: Idx.Source
  for +uu: S.PSet
  for +s: S.PSet
  for +s2: S.PSet
  for +gf: {Rp.Src.graphs_fit(src) == True{} : Bool}
  for +ko: {Ev.stack_ok(uu, k) == True{} : Bool}
  for +vs: {S.PSet.valid(20n, s, True{}) == True{} : Bool}
  for +vs2: {S.PSet.valid(20n, s2, True{}) == True{} : Bool}
  for +sm: {Ca.PSet.same(20n, s, s2) == True{} : Bool}
  {Ca.PSet.same(20n, Ev.plug(src, k, s), Ev.plug(src, k, s2))
    == True{} : Bool}

def Ev.plug_same(k, src, uu, s, s2, gf, ko, vs, vs2, sm):
  match k:
    case Nil{}:
      sm
    case Con{f, rest}:
      match f:
        case Qe.FRight{op, rhs}:
          Ev.plug_same(rest, src, uu,
            Qe.Ev.apply(s, Q.Den.eval(src, rhs), op),
            Qe.Ev.apply(s2, Q.Den.eval(src, rhs), op), gf,
            E.Bool.and_r(Ev.frame_ok(uu, Qe.FRight{op, rhs}),
              Ev.stack_ok(uu, rest), ko),
            PSet.valid_apply(op, s, Q.Den.eval(src, rhs), vs,
              Rp.Eval.valid(rhs, src,
                E.Bool.and_l(Rp.SetExpr.valid_lits(rhs),
                  Ev.lits_in(uu, rhs),
                  E.Bool.and_l(Ev.frame_ok(uu, Qe.FRight{op, rhs}),
                    Ev.stack_ok(uu, rest), ko)), gf)),
            PSet.valid_apply(op, s2, Q.Den.eval(src, rhs), vs2,
              Rp.Eval.valid(rhs, src,
                E.Bool.and_l(Rp.SetExpr.valid_lits(rhs),
                  Ev.lits_in(uu, rhs),
                  E.Bool.and_l(Ev.frame_ok(uu, Qe.FRight{op, rhs}),
                    Ev.stack_ok(uu, rest), ko)), gf)),
            PSet.same_apply(op, s, Q.Den.eval(src, rhs), s2,
              Q.Den.eval(src, rhs), vs,
              Rp.Eval.valid(rhs, src,
                E.Bool.and_l(Rp.SetExpr.valid_lits(rhs),
                  Ev.lits_in(uu, rhs),
                  E.Bool.and_l(Ev.frame_ok(uu, Qe.FRight{op, rhs}),
                    Ev.stack_ok(uu, rest), ko)), gf), vs2,
              Rp.Eval.valid(rhs, src,
                E.Bool.and_l(Rp.SetExpr.valid_lits(rhs),
                  Ev.lits_in(uu, rhs),
                  E.Bool.and_l(Ev.frame_ok(uu, Qe.FRight{op, rhs}),
                    Ev.stack_ok(uu, rest), ko)), gf), sm,
              Ca.PSet.same_refl(20n, Q.Den.eval(src, rhs),
                Rp.Eval.valid(rhs, src,
                  E.Bool.and_l(Rp.SetExpr.valid_lits(rhs),
                    Ev.lits_in(uu, rhs),
                    E.Bool.and_l(Ev.frame_ok(uu, Qe.FRight{op, rhs}),
                      Ev.stack_ok(uu, rest), ko)), gf), {==})))
        case Qe.FComb{op, lhs}:
          Ev.plug_same(rest, src, uu, Qe.Ev.apply(lhs, s, op),
            Qe.Ev.apply(lhs, s2, op), gf,
            E.Bool.and_r(Ev.frame_ok(uu, Qe.FComb{op, lhs}),
              Ev.stack_ok(uu, rest), ko),
            PSet.valid_apply(op, lhs, s,
              E.Bool.and_l(S.PSet.valid(20n, lhs, True{}),
                S.PSet.is_subset(20n, lhs, uu),
                E.Bool.and_l(Ev.frame_ok(uu, Qe.FComb{op, lhs}),
                  Ev.stack_ok(uu, rest), ko)), vs),
            PSet.valid_apply(op, lhs, s2,
              E.Bool.and_l(S.PSet.valid(20n, lhs, True{}),
                S.PSet.is_subset(20n, lhs, uu),
                E.Bool.and_l(Ev.frame_ok(uu, Qe.FComb{op, lhs}),
                  Ev.stack_ok(uu, rest), ko)), vs2),
            PSet.same_apply(op, lhs, s, lhs, s2,
              E.Bool.and_l(S.PSet.valid(20n, lhs, True{}),
                S.PSet.is_subset(20n, lhs, uu),
                E.Bool.and_l(Ev.frame_ok(uu, Qe.FComb{op, lhs}),
                  Ev.stack_ok(uu, rest), ko)), vs,
              E.Bool.and_l(S.PSet.valid(20n, lhs, True{}),
                S.PSet.is_subset(20n, lhs, uu),
                E.Bool.and_l(Ev.frame_ok(uu, Qe.FComb{op, lhs}),
                  Ev.stack_ok(uu, rest), ko)), vs2,
              Ca.PSet.same_refl(20n, lhs,
                E.Bool.and_l(S.PSet.valid(20n, lhs, True{}),
                  S.PSet.is_subset(20n, lhs, uu),
                  E.Bool.and_l(Ev.frame_ok(uu, Qe.FComb{op, lhs}),
                    Ev.stack_ok(uu, rest), ko)), {==}), sm))
        case Qe.FFilter{kind}:
          Ev.plug_same(rest, src, uu, Q.Den.filter(src, kind, s),
            Q.Den.filter(src, kind, s2), gf,
            E.Bool.and_r(Ev.frame_ok(uu, Qe.FFilter{kind}),
              Ev.stack_ok(uu, rest), ko),
            Iv.PSet.valid_from_list(
              Q.Den.keep(src, kind, S.PSet.to_list(20n, s)), 20n,
              {==}, Rp.Ords.all_fit_32(
                Q.Den.keep(src, kind, S.PSet.to_list(20n, s)))),
            Iv.PSet.valid_from_list(
              Q.Den.keep(src, kind, S.PSet.to_list(20n, s2)), 20n,
              {==}, Rp.Ords.all_fit_32(
                Q.Den.keep(src, kind, S.PSet.to_list(20n, s2)))),
            Rp.PSet.same_filter(src, kind, s, s2, vs, vs2, sm))
        case Qe.FReach{policy}:
          Ev.plug_same(rest, src, uu,
            Sp.Spec.closure(Idx.Source.n(src), 32n,
              Idx.Source.graph(src, policy), 20n, s),
            Sp.Spec.closure(Idx.Source.n(src), 32n,
              Idx.Source.graph(src, policy), 20n, s2), gf,
            E.Bool.and_r(Ev.frame_ok(uu, Qe.FReach{policy}),
              Ev.stack_ok(uu, rest), ko),
            Lp.Spec.closure_valid(Idx.Source.n(src), 32n, 20n,
              Idx.Source.graph(src, policy), s,
              Rp.Src.graph_fit(src, policy, gf), {==}, vs),
            Lp.Spec.closure_valid(Idx.Source.n(src), 32n, 20n,
              Idx.Source.graph(src, policy), s2,
              Rp.Src.graph_fit(src, policy, gf), {==}, vs2),
            Rp.PSet.same_reach(Idx.Source.n(src),
              Idx.Source.graph(src, policy), s, s2, vs, vs2,
              Rp.Src.graph_fit(src, policy, gf), sm))

# ---------------------------------------------------------------------------
# The source's graphs stay inside the bounding set.
# ---------------------------------------------------------------------------

def Src.graphs_in(+src: Idx.Source, +uu: S.PSet) -> Bool:
  Bool.and(Gr.Graph.succs_in(20n, uu,
    Idx.Source.graph(src, Idx.PFull{})),
    Gr.Graph.succs_in(20n, uu,
      Idx.Source.graph(src, Idx.PTreeData{})))

law Src.graph_in:
  for +src: Idx.Source
  for +uu: S.PSet
  for +p: Idx.Policy
  for +su: {Src.graphs_in(src, uu) == True{} : Bool}
  {Gr.Graph.succs_in(20n, uu, Idx.Source.graph(src, p)) == True{}
    : Bool}

def Src.graph_in(src, uu, p, su):
  match p:
    case Idx.PFull{}:
      E.Bool.and_l(Gr.Graph.succs_in(20n, uu,
        Idx.Source.graph(src, Idx.PFull{})),
        Gr.Graph.succs_in(20n, uu,
          Idx.Source.graph(src, Idx.PTreeData{})), su)
    case Idx.PTreeData{}:
      E.Bool.and_r(Gr.Graph.succs_in(20n, uu,
        Idx.Source.graph(src, Idx.PFull{})),
        Gr.Graph.succs_in(20n, uu,
          Idx.Source.graph(src, Idx.PTreeData{})), su)

# The traversal's own answer, as a set: valid, inside the bound, and the same
# set as the specification closure of the value it started from.
def Ev.seen_of(+src: Idx.Source, +policy: Idx.Policy, +v: S.PSet)
  -> S.PSet:
  R.Reach.seen(20n, R.Reach.closure(Idx.Source.n(src), 32n,
    Idx.Source.graph(src, policy), 20n, S.PSet.to_list(20n, v)))

law Ev.seen_valid:
  for +src: Idx.Source
  for +policy: Idx.Policy
  for +v: S.PSet
  for +gf: {Rp.Src.graphs_fit(src) == True{} : Bool}
  for +vv: {S.PSet.valid(20n, v, True{}) == True{} : Bool}
  {S.PSet.valid(20n, Ev.seen_of(src, policy, v), True{}) == True{}
    : Bool}

def Ev.seen_valid(src, policy, v, gf, vv):
  Tl.Reach.go_valid(2n+Nat.add(Idx.Source.n(src),
    Idx.Source.n(src)), 32n, 20n, Idx.Source.graph(src, policy),
    S.PSet.from_list(20n, S.PSet.to_list(20n, v)),
    S.PSet.to_list(20n, v), Nil{},
    Con{S.PSet.to_list(20n, v), Nil{}}, 0n,
    Rp.Src.graph_fit(src, policy, gf), {==},
    Iv.PSet.valid_from_list(S.PSet.to_list(20n, v), 20n, {==},
      Rp.Ords.all_fit_32(S.PSet.to_list(20n, v))),
    Rp.Ords.all_fit_32(S.PSet.to_list(20n, v)), {==})

law Ev.seen_same:
  for +src: Idx.Source
  for +policy: Idx.Policy
  for +v: S.PSet
  for +uu: S.PSet
  for +gf: {Rp.Src.graphs_fit(src) == True{} : Bool}
  for +su: {Src.graphs_in(src, uu) == True{} : Bool}
  for +vu: {S.PSet.valid(20n, uu, True{}) == True{} : Bool}
  for +vv: {S.PSet.valid(20n, v, True{}) == True{} : Bool}
  for +vin: {S.PSet.is_subset(20n, v, uu) == True{} : Bool}
  for +fuelc: {C.Nat.upto(S.PSet.count(20n, uu, S.PSet.half(20n)),
    1n+Idx.Source.n(src)) == True{} : Bool}
  for +done: {R.Reach.done(20n,
    R.Reach.closure(Idx.Source.n(src), 32n,
      Idx.Source.graph(src, policy), 20n,
      S.PSet.to_list(20n, v))) == True{} : Bool}
  {Ca.PSet.same(20n, Ev.seen_of(src, policy, v),
    Sp.Spec.closure(Idx.Source.n(src), 32n,
      Idx.Source.graph(src, policy), 20n, v)) == True{} : Bool}

def Ev.seen_same(src, policy, v, uu, gf, su, vu, vv, vin, fuelc,
  done):
  Ca.PSet.same_trans(20n, Ev.seen_of(src, policy, v),
    Sp.Spec.closure(Idx.Source.n(src), 32n,
      Idx.Source.graph(src, policy), 20n,
      S.PSet.from_list(20n, S.PSet.to_list(20n, v))),
    Sp.Spec.closure(Idx.Source.n(src), 32n,
      Idx.Source.graph(src, policy), 20n, v),
    Ev.seen_valid(src, policy, v, gf, vv),
    Lp.Spec.closure_valid(Idx.Source.n(src), 32n, 20n,
      Idx.Source.graph(src, policy),
      S.PSet.from_list(20n, S.PSet.to_list(20n, v)),
      Rp.Src.graph_fit(src, policy, gf), {==},
      Iv.PSet.valid_from_list(S.PSet.to_list(20n, v), 20n, {==},
        Rp.Ords.all_fit_32(S.PSet.to_list(20n, v)))),
    Lp.Spec.closure_valid(Idx.Source.n(src), 32n, 20n,
      Idx.Source.graph(src, policy), v,
      Rp.Src.graph_fit(src, policy, gf), {==}, vv), {==},
    Tl.Reach.closure_same(Idx.Source.n(src), 32n, 20n,
      Idx.Source.graph(src, policy), S.PSet.to_list(20n, v), uu,
      Rp.Src.graph_fit(src, policy, gf),
      Src.graph_in(src, uu, policy, su), {==},
      Rp.Ords.all_fit_32(S.PSet.to_list(20n, v)), vu,
      Sa.PSet.subset_trans(20n,
        S.PSet.from_list(20n, S.PSet.to_list(20n, v)), v, uu,
        Iv.PSet.valid_from_list(S.PSet.to_list(20n, v), 20n, {==},
          Rp.Ords.all_fit_32(S.PSet.to_list(20n, v))), vv, vu, {==},
        Ca.PSet.same_l(20n,
          S.PSet.from_list(20n, S.PSet.to_list(20n, v)), v,
          PSet.same_roundtrip(v, vv)), vin), fuelc, done),
    Rp.PSet.same_reach(Idx.Source.n(src),
      Idx.Source.graph(src, policy),
      S.PSet.from_list(20n, S.PSet.to_list(20n, v)), v,
      Iv.PSet.valid_from_list(S.PSet.to_list(20n, v), 20n, {==},
        Rp.Ords.all_fit_32(S.PSet.to_list(20n, v))), vv,
      Rp.Src.graph_fit(src, policy, gf),
      PSet.same_roundtrip(v, vv)))

law Ev.seen_inside:
  for +src: Idx.Source
  for +policy: Idx.Policy
  for +v: S.PSet
  for +uu: S.PSet
  for +gf: {Rp.Src.graphs_fit(src) == True{} : Bool}
  for +su: {Src.graphs_in(src, uu) == True{} : Bool}
  for +vu: {S.PSet.valid(20n, uu, True{}) == True{} : Bool}
  for +vv: {S.PSet.valid(20n, v, True{}) == True{} : Bool}
  for +vin: {S.PSet.is_subset(20n, v, uu) == True{} : Bool}
  {S.PSet.is_subset(20n, Ev.seen_of(src, policy, v), uu) == True{}
    : Bool}

def Ev.seen_inside.start(+src: Idx.Source, +v: S.PSet, +uu: S.PSet,
  +vu: {S.PSet.valid(20n, uu, True{}) == True{} : Bool},
  +vv: {S.PSet.valid(20n, v, True{}) == True{} : Bool},
  +vin: {S.PSet.is_subset(20n, v, uu) == True{} : Bool})
  -> {S.PSet.is_subset(20n,
    S.PSet.from_list(20n, S.PSet.to_list(20n, v)), uu) == True{}
    : Bool}:
  Sa.PSet.subset_trans(20n,
    S.PSet.from_list(20n, S.PSet.to_list(20n, v)), v, uu,
    Iv.PSet.valid_from_list(S.PSet.to_list(20n, v), 20n, {==},
      Rp.Ords.all_fit_32(S.PSet.to_list(20n, v))), vv, vu, {==},
    Ca.PSet.same_l(20n,
      S.PSet.from_list(20n, S.PSet.to_list(20n, v)), v,
      PSet.same_roundtrip(v, vv)), vin)

def Ev.seen_inside(src, policy, v, uu, gf, su, vu, vv, vin):
  Tl.Reach.go_inside(2n+Nat.add(Idx.Source.n(src),
    Idx.Source.n(src)), 32n, 20n, Idx.Source.graph(src, policy), uu,
    S.PSet.from_list(20n, S.PSet.to_list(20n, v)),
    S.PSet.to_list(20n, v), Nil{},
    Con{S.PSet.to_list(20n, v), Nil{}}, 0n,
    Rp.Src.graph_fit(src, policy, gf), {==}, vu,
    Iv.PSet.valid_from_list(S.PSet.to_list(20n, v), 20n, {==},
      Rp.Ords.all_fit_32(S.PSet.to_list(20n, v))),
    Pm.Spec.post_in(32n, 20n, Idx.Source.graph(src, policy), uu, uu,
      Rp.Src.graph_fit(src, policy, gf),
      Src.graph_in(src, uu, policy, su), {==}, vu),
    Ev.seen_inside.start(src, v, uu, vu, vv, vin),
    Tl.Ords.all_mem_roots(S.PSet.to_list(20n, v), 20n, uu,
      S.PSet.to_list(20n, v), {==},
      Rp.Ords.all_fit_32(S.PSet.to_list(20n, v)), vu,
      Ev.seen_inside.start(src, v, uu, vu, vv, vin),
      Sa.Ords.all_in_self(S.PSet.to_list(20n, v))), {==},
    Rp.Ords.all_fit_32(S.PSet.to_list(20n, v)), {==})

law Ev.go_spec:
  for +fuel: Nat
  for +src: Idx.Source
  for +c: Qe.Ctl
  for +k: List<&2, Qe.Frame>
  for +ok: Bool
  for +uu: S.PSet
  for +gf: {Rp.Src.graphs_fit(src) == True{} : Bool}
  for +su: {Src.graphs_in(src, uu) == True{} : Bool}
  for +vu: {S.PSet.valid(20n, uu, True{}) == True{} : Bool}
  for +fu: {S.PSet.is_subset(20n,
    Q.Den.universe(Idx.Source.n(src)), uu) == True{} : Bool}
  for +fuelc: {C.Nat.upto(S.PSet.count(20n, uu, S.PSet.half(20n)),
    1n+Idx.Source.n(src)) == True{} : Bool}
  for +ko: {Ev.stack_ok(uu, k) == True{} : Bool}
  for +co: {Ev.ctl_ok(uu, c) == True{} : Bool}
  for +okT: {ok == True{} : Bool}
  for fin: {Qe.Val.ok(Qe.Ev.go(fuel, src, c, k, ok)) == True{}
    : Bool}
  {Ca.PSet.same(20n, Qe.Val.set(Qe.Ev.go(fuel, src, c, k, ok)),
    Ev.plug(src, k, Ev.ctl(src, c))) == True{} : Bool}

def Ev.frame_v(+f: Qe.Frame) -> Bool:
  match f:
    case Qe.FRight{op, rhs}:
      Rp.SetExpr.valid_lits(rhs)
    case Qe.FComb{op, lhs}:
      S.PSet.valid(20n, lhs, True{})
    case Qe.FFilter{kind}:
      True{}
    case Qe.FReach{policy}:
      True{}

def Ev.stack_v(+k: List<&2, Qe.Frame>) -> Bool:
  match k:
    case Nil{}:
      True{}
    case Con{f, rest}:
      Bool.and(Ev.frame_v(f), Ev.stack_v(rest))

def Ev.ctl_v(+c: Qe.Ctl) -> Bool:
  match c:
    case Qe.CEval{e}:
      Rp.SetExpr.valid_lits(e)
    case Qe.CVal{v}:
      S.PSet.valid(20n, v, True{})

law Ev.stack_v_of_ok:
  for +k: List<&2, Qe.Frame>
  for +uu: S.PSet
  for +ko: {Ev.stack_ok(uu, k) == True{} : Bool}
  {Ev.stack_v(k) == True{} : Bool}

def Ev.frame_v_of_ok(+uu: S.PSet, +f: Qe.Frame,
  +fo: {Ev.frame_ok(uu, f) == True{} : Bool})
  -> {Ev.frame_v(f) == True{} : Bool}:
  match f:
    case Qe.FRight{op, rhs}:
      E.Bool.and_l(Rp.SetExpr.valid_lits(rhs), Ev.lits_in(uu, rhs),
        fo)
    case Qe.FComb{op, lhs}:
      E.Bool.and_l(S.PSet.valid(20n, lhs, True{}),
        S.PSet.is_subset(20n, lhs, uu), fo)
    case Qe.FFilter{kind}:
      {==}
    case Qe.FReach{policy}:
      {==}

def Ev.stack_v_of_ok(k, uu, ko):
  match k:
    case Nil{}:
      {==}
    case Con{f, rest}:
      E.Bool.and_both(Ev.frame_v(f), Ev.stack_v(rest),
        Ev.frame_v_of_ok(uu, f,
          E.Bool.and_l(Ev.frame_ok(uu, f), Ev.stack_ok(uu, rest),
            ko)),
        Ev.stack_v_of_ok(rest, uu,
          E.Bool.and_r(Ev.frame_ok(uu, f), Ev.stack_ok(uu, rest),
            ko)))

law Ev.ctl_v_of_ok:
  for +c: Qe.Ctl
  for +uu: S.PSet
  for +co: {Ev.ctl_ok(uu, c) == True{} : Bool}
  {Ev.ctl_v(c) == True{} : Bool}

def Ev.ctl_v_of_ok(c, uu, co):
  match c:
    case Qe.CEval{e}:
      E.Bool.and_l(Rp.SetExpr.valid_lits(e), Ev.lits_in(uu, e), co)
    case Qe.CVal{v}:
      E.Bool.and_l(S.PSet.valid(20n, v, True{}),
        S.PSet.is_subset(20n, v, uu), co)

law Ev.go_valid:
  for +fuel: Nat
  for +src: Idx.Source
  for +c: Qe.Ctl
  for +k: List<&2, Qe.Frame>
  for +ok: Bool
  for +gf: {Rp.Src.graphs_fit(src) == True{} : Bool}
  for +ko: {Ev.stack_v(k) == True{} : Bool}
  for +co: {Ev.ctl_v(c) == True{} : Bool}
  {S.PSet.valid(20n, Qe.Val.set(Qe.Ev.go(fuel, src, c, k, ok)),
    True{}) == True{} : Bool}

def Ev.go_valid.done(+v: S.PSet, +ok: Bool,
  +vv: {S.PSet.valid(20n, v, True{}) == True{} : Bool})
  -> {S.PSet.valid(20n, Qe.Val.set(Qe.Ev.done(v, ok)), True{})
    == True{} : Bool}:
  match ok:
    case True{}:
      vv
    case False{}:
      vv

def Ev.go_valid.reach(+g2: Nat, +src: Idx.Source, +v: S.PSet,
  +rest: List<&2, Qe.Frame>, +ok: Bool, +policy: Idx.Policy,
  +fin2: Bool,
  +onT: {S.PSet.valid(20n, Qe.Val.set(Qe.Ev.go(g2, src,
    Qe.CVal{Ev.seen_of(src, policy, v)}, rest, Bool.and(ok, fin2))),
    True{}) == True{} : Bool},
  +onF: {S.PSet.valid(20n, Qe.Val.set(Qe.Ev.go(g2, src,
    Qe.CVal{Ev.seen_of(src, policy, v)}, Nil{}, Bool.and(ok, fin2))),
    True{}) == True{} : Bool})
  -> {S.PSet.valid(20n, Qe.Val.set(Qe.Ev.go(g2, src,
    Qe.CVal{Ev.seen_of(src, policy, v)},
    Qe.Ev.reach.stack(fin2, rest), Bool.and(ok, fin2))), True{})
    == True{} : Bool}:
  match fin2:
    case True{}:
      onT
    case False{}:
      onF

def Ev.go_valid(fuel, src, c, k, ok, gf, ko, co):
  match fuel:
    case 0n:
      Vk.PSet.valid_zero(20n)
    case 1n+g:
      match c:
        case Qe.CVal{v}:
          match k:
            case Nil{}:
              Ev.go_valid.done(v, ok, co)
            case Con{f, rest}:
              match f:
                case Qe.FRight{op, rhs}:
                  Ev.go_valid(g, src, Qe.CEval{rhs},
                    Con{Qe.FComb{op, v}, rest}, ok, gf,
                    E.Bool.and_both(Ev.frame_v(Qe.FComb{op, v}),
                      Ev.stack_v(rest), co,
                      E.Bool.and_r(Ev.frame_v(Qe.FRight{op, rhs}),
                        Ev.stack_v(rest), ko)),
                    E.Bool.and_l(Ev.frame_v(Qe.FRight{op, rhs}),
                      Ev.stack_v(rest), ko))
                case Qe.FComb{op, lhs}:
                  Ev.go_valid(g, src,
                    Qe.CVal{Qe.Ev.apply(lhs, v, op)}, rest, ok, gf,
                    E.Bool.and_r(Ev.frame_v(Qe.FComb{op, lhs}),
                      Ev.stack_v(rest), ko),
                    PSet.valid_apply(op, lhs, v,
                      E.Bool.and_l(Ev.frame_v(Qe.FComb{op, lhs}),
                        Ev.stack_v(rest), ko), co))
                case Qe.FFilter{kind}:
                  Ev.go_valid(g, src,
                    Qe.CVal{Q.Den.filter(src, kind, v)}, rest, ok,
                    gf,
                    E.Bool.and_r(Ev.frame_v(Qe.FFilter{kind}),
                      Ev.stack_v(rest), ko),
                    Iv.PSet.valid_from_list(Q.Den.keep(src, kind,
                      S.PSet.to_list(20n, v)), 20n, {==},
                      Rp.Ords.all_fit_32(Q.Den.keep(src, kind,
                        S.PSet.to_list(20n, v)))))
                case Qe.FReach{policy}:
                  Ev.go_valid.reach(g, src, v, rest, ok, policy,
                    R.Reach.done(20n,
                      R.Reach.closure(Idx.Source.n(src), 32n,
                        Idx.Source.graph(src, policy), 20n,
                        S.PSet.to_list(20n, v))),
                    Ev.go_valid(g, src,
                      Qe.CVal{Ev.seen_of(src, policy, v)}, rest,
                      Bool.and(ok, R.Reach.done(20n,
                        R.Reach.closure(Idx.Source.n(src), 32n,
                          Idx.Source.graph(src, policy), 20n,
                          S.PSet.to_list(20n, v)))), gf,
                      E.Bool.and_r(Ev.frame_v(Qe.FReach{policy}),
                        Ev.stack_v(rest), ko),
                      Ev.seen_valid(src, policy, v, gf, co)),
                    Ev.go_valid(g, src,
                      Qe.CVal{Ev.seen_of(src, policy, v)}, Nil{},
                      Bool.and(ok, R.Reach.done(20n,
                        R.Reach.closure(Idx.Source.n(src), 32n,
                          Idx.Source.graph(src, policy), 20n,
                          S.PSet.to_list(20n, v)))), gf, {==},
                      Ev.seen_valid(src, policy, v, gf, co)))
        case Qe.CEval{e}:
          match e:
            case A.EEmpty{}:
              Ev.go_valid(g, src, Qe.CVal{S.PSet.empty()}, k, ok, gf,
                ko, Vk.PSet.valid_zero(20n))
            case A.EFull{}:
              Ev.go_valid(g, src,
                Qe.CVal{Q.Den.universe(Idx.Source.n(src))}, k, ok,
                gf, ko, Rp.Eval.valid(A.EFull{}, src, {==}, gf))
            case A.ELit{set}:
              Ev.go_valid(g, src, Qe.CVal{set}, k, ok, gf, ko, co)
            case A.EUnion{a, b}:
              Ev.go_valid(g, src, Qe.CEval{a},
                Con{Qe.FRight{0n, b}, k}, ok, gf,
                E.Bool.and_both(Ev.frame_v(Qe.FRight{0n, b}),
                  Ev.stack_v(k),
                  E.Bool.and_r(Rp.SetExpr.valid_lits(a),
                    Rp.SetExpr.valid_lits(b), co), ko),
                E.Bool.and_l(Rp.SetExpr.valid_lits(a),
                  Rp.SetExpr.valid_lits(b), co))
            case A.EInter{a, b}:
              Ev.go_valid(g, src, Qe.CEval{a},
                Con{Qe.FRight{1n, b}, k}, ok, gf,
                E.Bool.and_both(Ev.frame_v(Qe.FRight{1n, b}),
                  Ev.stack_v(k),
                  E.Bool.and_r(Rp.SetExpr.valid_lits(a),
                    Rp.SetExpr.valid_lits(b), co), ko),
                E.Bool.and_l(Rp.SetExpr.valid_lits(a),
                  Rp.SetExpr.valid_lits(b), co))
            case A.EDiff{a, b}:
              Ev.go_valid(g, src, Qe.CEval{a},
                Con{Qe.FRight{2n, b}, k}, ok, gf,
                E.Bool.and_both(Ev.frame_v(Qe.FRight{2n, b}),
                  Ev.stack_v(k),
                  E.Bool.and_r(Rp.SetExpr.valid_lits(a),
                    Rp.SetExpr.valid_lits(b), co), ko),
                E.Bool.and_l(Rp.SetExpr.valid_lits(a),
                  Rp.SetExpr.valid_lits(b), co))
            case A.EReach{policy, a}:
              Ev.go_valid(g, src, Qe.CEval{a},
                Con{Qe.FReach{policy}, k}, ok, gf,
                E.Bool.and_both(Ev.frame_v(Qe.FReach{policy}),
                  Ev.stack_v(k), {==}, ko), co)
            case A.EFilter{kind, a}:
              Ev.go_valid(g, src, Qe.CEval{a},
                Con{Qe.FFilter{kind}, k}, ok, gf,
                E.Bool.and_both(Ev.frame_v(Qe.FFilter{kind}),
                  Ev.stack_v(k), {==}, ko), co)

def Ev.go_spec.reach(+g2: Nat, +src: Idx.Source, +v: S.PSet,
  +rest: List<&2, Qe.Frame>, +ok: Bool, +uu: S.PSet,
  +policy: Idx.Policy, +fin2: Bool,
  +efin: {fin2 == R.Reach.done(20n,
    R.Reach.closure(Idx.Source.n(src), 32n,
      Idx.Source.graph(src, policy), 20n,
      S.PSet.to_list(20n, v))) : Bool},
  +gf: {Rp.Src.graphs_fit(src) == True{} : Bool},
  +su: {Src.graphs_in(src, uu) == True{} : Bool},
  +vu: {S.PSet.valid(20n, uu, True{}) == True{} : Bool},
  +vv: {S.PSet.valid(20n, v, True{}) == True{} : Bool},
  +vin: {S.PSet.is_subset(20n, v, uu) == True{} : Bool},
  +fuelc: {C.Nat.upto(S.PSet.count(20n, uu, S.PSet.half(20n)),
    1n+Idx.Source.n(src)) == True{} : Bool},
  +ko: {Ev.stack_ok(uu, rest) == True{} : Bool},
  +okT: {ok == True{} : Bool},
  ih: {Qe.Val.ok(Qe.Ev.go(g2, src,
      Qe.CVal{Ev.seen_of(src, policy, v)}, rest, ok)) == True{}
    : Bool} ->
    {Ca.PSet.same(20n, Qe.Val.set(Qe.Ev.go(g2, src,
      Qe.CVal{Ev.seen_of(src, policy, v)}, rest, ok)),
    Ev.plug(src, rest, Ev.seen_of(src, policy, v))) == True{}
    : Bool},
  fin: {Qe.Val.ok(Qe.Ev.go(g2, src,
    Qe.CVal{Ev.seen_of(src, policy, v)},
    Qe.Ev.reach.stack(fin2, rest), Bool.and(ok, fin2))) == True{}
    : Bool})
  -> {Ca.PSet.same(20n, Qe.Val.set(Qe.Ev.go(g2, src,
    Qe.CVal{Ev.seen_of(src, policy, v)},
    Qe.Ev.reach.stack(fin2, rest), Bool.and(ok, fin2))),
    Ev.plug(src, rest, Sp.Spec.closure(Idx.Source.n(src), 32n,
      Idx.Source.graph(src, policy), 20n, v))) == True{} : Bool}:
  match fin2:
    case False{}:
      E.Bool.noconf({Ca.PSet.same(20n, Qe.Val.set(Qe.Ev.go(g2, src,
        Qe.CVal{Ev.seen_of(src, policy, v)}, Nil{},
        Bool.and(ok, False{}))),
        Ev.plug(src, rest,
          Sp.Spec.closure(Idx.Source.n(src), 32n,
            Idx.Source.graph(src, policy), 20n, v))) == True{}
        : Bool},
        %Ev.go_not_ok(g2, src,
          Qe.CVal{Ev.seen_of(src, policy, v)}, Nil{})
          : {_ == True{} : Bool}
        %Sa2.Word.and_false_r(ok)
          : {Qe.Val.ok(Qe.Ev.go(g2, src,
            Qe.CVal{Ev.seen_of(src, policy, v)}, Nil{}, _))
            == True{} : Bool}
        fin)
    case True{}:
      %E.Bool.sym(Bool.and(ok, True{}), ok, Te.Bool.and_true_r(ok))
        : {Ca.PSet.same(20n, Qe.Val.set(Qe.Ev.go(g2, src,
          Qe.CVal{Ev.seen_of(src, policy, v)}, rest, _)),
          Ev.plug(src, rest,
            Sp.Spec.closure(Idx.Source.n(src), 32n,
              Idx.Source.graph(src, policy), 20n, v))) == True{}
          : Bool}
      Ca.PSet.same_trans(20n, Qe.Val.set(Qe.Ev.go(g2, src,
        Qe.CVal{Ev.seen_of(src, policy, v)}, rest, ok)),
        Ev.plug(src, rest, Ev.seen_of(src, policy, v)),
        Ev.plug(src, rest,
          Sp.Spec.closure(Idx.Source.n(src), 32n,
            Idx.Source.graph(src, policy), 20n, v)),
        Ev.go_valid(g2, src, Qe.CVal{Ev.seen_of(src, policy, v)},
          rest, ok, gf, Ev.stack_v_of_ok(rest, uu, ko),
          Ev.seen_valid(src, policy, v, gf, vv)),
        Ev.plug_valid(rest, src, uu, Ev.seen_of(src, policy, v), gf,
          ko, Ev.seen_valid(src, policy, v, gf, vv)),
        Ev.plug_valid(rest, src, uu,
          Sp.Spec.closure(Idx.Source.n(src), 32n,
            Idx.Source.graph(src, policy), 20n, v), gf, ko,
          Lp.Spec.closure_valid(Idx.Source.n(src), 32n, 20n,
            Idx.Source.graph(src, policy), v,
            Rp.Src.graph_fit(src, policy, gf), {==}, vv)), {==},
        ih(%Te.Bool.and_true_r(ok)
            : {Qe.Val.ok(Qe.Ev.go(g2, src,
              Qe.CVal{Ev.seen_of(src, policy, v)}, rest, _))
              == True{} : Bool}
          fin),
        Ev.plug_same(rest, src, uu, Ev.seen_of(src, policy, v),
          Sp.Spec.closure(Idx.Source.n(src), 32n,
            Idx.Source.graph(src, policy), 20n, v), gf, ko,
          Ev.seen_valid(src, policy, v, gf, vv),
          Lp.Spec.closure_valid(Idx.Source.n(src), 32n, 20n,
            Idx.Source.graph(src, policy), v,
            Rp.Src.graph_fit(src, policy, gf), {==}, vv),
          Ev.seen_same(src, policy, v, uu, gf, su, vu, vv, vin,
            fuelc, E.Bool.sym(True{}, R.Reach.done(20n,
              R.Reach.closure(Idx.Source.n(src), 32n,
                Idx.Source.graph(src, policy), 20n,
                S.PSet.to_list(20n, v))), efin))))

def Ev.reach_ctl(+src: Idx.Source, +policy: Idx.Policy, +v: S.PSet,
  +uu: S.PSet,
  +gf: {Rp.Src.graphs_fit(src) == True{} : Bool},
  +su: {Src.graphs_in(src, uu) == True{} : Bool},
  +vu: {S.PSet.valid(20n, uu, True{}) == True{} : Bool},
  +vv: {S.PSet.valid(20n, v, True{}) == True{} : Bool},
  +vin: {S.PSet.is_subset(20n, v, uu) == True{} : Bool},
  +fuelc: {C.Nat.upto(S.PSet.count(20n, uu, S.PSet.half(20n)),
    1n+Idx.Source.n(src)) == True{} : Bool})
  -> {Ev.ctl_ok(uu, Qe.CVal{Ev.seen_of(src, policy, v)}) == True{}
    : Bool}:
  E.Bool.and_both(
    S.PSet.valid(20n, Ev.seen_of(src, policy, v), True{}),
    S.PSet.is_subset(20n, Ev.seen_of(src, policy, v), uu),
    Ev.seen_valid(src, policy, v, gf, vv),
    Ev.seen_inside(src, policy, v, uu, gf, su, vu, vv, vin))

def Ev.go_valid.left(+uu: S.PSet, +a: A.SetExpr, +b: A.SetExpr,
  +co: {Bool.and(Bool.and(Rp.SetExpr.valid_lits(a),
    Rp.SetExpr.valid_lits(b)),
    Bool.and(Ev.lits_in(uu, a), Ev.lits_in(uu, b))) == True{}
    : Bool})
  -> {Bool.and(Rp.SetExpr.valid_lits(a), Ev.lits_in(uu, a))
    == True{} : Bool}:
  E.Bool.and_both(Rp.SetExpr.valid_lits(a), Ev.lits_in(uu, a),
    E.Bool.and_l(Rp.SetExpr.valid_lits(a),
      Rp.SetExpr.valid_lits(b),
      E.Bool.and_l(Bool.and(Rp.SetExpr.valid_lits(a),
        Rp.SetExpr.valid_lits(b)),
        Bool.and(Ev.lits_in(uu, a), Ev.lits_in(uu, b)), co)),
    E.Bool.and_l(Ev.lits_in(uu, a), Ev.lits_in(uu, b),
      E.Bool.and_r(Bool.and(Rp.SetExpr.valid_lits(a),
        Rp.SetExpr.valid_lits(b)),
        Bool.and(Ev.lits_in(uu, a), Ev.lits_in(uu, b)), co)))

def Ev.go_valid.right(+uu: S.PSet, +a: A.SetExpr, +b: A.SetExpr,
  +co: {Bool.and(Bool.and(Rp.SetExpr.valid_lits(a),
    Rp.SetExpr.valid_lits(b)),
    Bool.and(Ev.lits_in(uu, a), Ev.lits_in(uu, b))) == True{}
    : Bool})
  -> {Bool.and(Rp.SetExpr.valid_lits(b), Ev.lits_in(uu, b))
    == True{} : Bool}:
  E.Bool.and_both(Rp.SetExpr.valid_lits(b), Ev.lits_in(uu, b),
    E.Bool.and_r(Rp.SetExpr.valid_lits(a),
      Rp.SetExpr.valid_lits(b),
      E.Bool.and_l(Bool.and(Rp.SetExpr.valid_lits(a),
        Rp.SetExpr.valid_lits(b)),
        Bool.and(Ev.lits_in(uu, a), Ev.lits_in(uu, b)), co)),
    E.Bool.and_r(Ev.lits_in(uu, a), Ev.lits_in(uu, b),
      E.Bool.and_r(Bool.and(Rp.SetExpr.valid_lits(a),
        Rp.SetExpr.valid_lits(b)),
        Bool.and(Ev.lits_in(uu, a), Ev.lits_in(uu, b)), co)))

def Ev.go_spec(fuel, src, c, k, ok, uu, gf, su, vu, fu, fuelc, ko,
  co, okT, fin):
  match fuel:
    case 0n:
      E.Bool.noconf({Ca.PSet.same(20n, S.PSet.empty(),
        Ev.plug(src, k, Ev.ctl(src, c))) == True{} : Bool}, fin)
    case 1n+g:
      match c:
        case Qe.CVal{v}:
          match k:
            case Nil{}:
              %E.Bool.sym(ok, True{}, okT)
                : {Ca.PSet.same(20n,
                  Qe.Val.set(Qe.Ev.done(v, _)), v) == True{} : Bool}
              Ca.PSet.same_refl(20n, v,
                E.Bool.and_l(S.PSet.valid(20n, v, True{}),
                  S.PSet.is_subset(20n, v, uu), co), {==})
            case Con{f, rest}:
              match f:
                case Qe.FRight{op, rhs}:
                  Ev.go_spec(g, src, Qe.CEval{rhs},
                    Con{Qe.FComb{op, v}, rest}, ok, uu, gf, su, vu,
                    fu, fuelc,
                    E.Bool.and_both(
                      Ev.frame_ok(uu, Qe.FComb{op, v}),
                      Ev.stack_ok(uu, rest), co,
                      E.Bool.and_r(
                        Ev.frame_ok(uu, Qe.FRight{op, rhs}),
                        Ev.stack_ok(uu, rest), ko)),
                    E.Bool.and_l(
                      Ev.frame_ok(uu, Qe.FRight{op, rhs}),
                      Ev.stack_ok(uu, rest), ko), okT, fin)
                case Qe.FComb{op, lhs}:
                  Ev.go_spec(g, src,
                    Qe.CVal{Qe.Ev.apply(lhs, v, op)}, rest, ok, uu,
                    gf, su, vu, fu, fuelc,
                    E.Bool.and_r(Ev.frame_ok(uu, Qe.FComb{op, lhs}),
                      Ev.stack_ok(uu, rest), ko),
                    E.Bool.and_both(S.PSet.valid(20n,
                      Qe.Ev.apply(lhs, v, op), True{}),
                      S.PSet.is_subset(20n,
                        Qe.Ev.apply(lhs, v, op), uu),
                      PSet.valid_apply(op, lhs, v,
                        E.Bool.and_l(S.PSet.valid(20n, lhs, True{}),
                          S.PSet.is_subset(20n, lhs, uu),
                          E.Bool.and_l(Ev.frame_ok(uu,
                            Qe.FComb{op, lhs}),
                            Ev.stack_ok(uu, rest), ko)),
                        E.Bool.and_l(S.PSet.valid(20n, v, True{}),
                          S.PSet.is_subset(20n, v, uu), co)),
                      PSet.apply_inside(op, lhs, v, uu,
                        E.Bool.and_l(S.PSet.valid(20n, lhs, True{}),
                          S.PSet.is_subset(20n, lhs, uu),
                          E.Bool.and_l(Ev.frame_ok(uu,
                            Qe.FComb{op, lhs}),
                            Ev.stack_ok(uu, rest), ko)),
                        E.Bool.and_l(S.PSet.valid(20n, v, True{}),
                          S.PSet.is_subset(20n, v, uu), co), vu,
                        E.Bool.and_r(S.PSet.valid(20n, lhs, True{}),
                          S.PSet.is_subset(20n, lhs, uu),
                          E.Bool.and_l(Ev.frame_ok(uu,
                            Qe.FComb{op, lhs}),
                            Ev.stack_ok(uu, rest), ko)),
                        E.Bool.and_r(S.PSet.valid(20n, v, True{}),
                          S.PSet.is_subset(20n, v, uu), co))),
                    okT, fin)
                case Qe.FFilter{kind}:
                  Ev.go_spec(g, src,
                    Qe.CVal{Q.Den.filter(src, kind, v)}, rest, ok,
                    uu, gf, su, vu, fu, fuelc,
                    E.Bool.and_r(Ev.frame_ok(uu, Qe.FFilter{kind}),
                      Ev.stack_ok(uu, rest), ko),
                    E.Bool.and_both(S.PSet.valid(20n,
                      Q.Den.filter(src, kind, v), True{}),
                      S.PSet.is_subset(20n,
                        Q.Den.filter(src, kind, v), uu),
                      Iv.PSet.valid_from_list(Q.Den.keep(src, kind,
                        S.PSet.to_list(20n, v)), 20n, {==},
                        Rp.Ords.all_fit_32(Q.Den.keep(src, kind,
                          S.PSet.to_list(20n, v)))),
                      Sa.PSet.subset_trans(20n,
                        Q.Den.filter(src, kind, v), v, uu,
                        Iv.PSet.valid_from_list(Q.Den.keep(src, kind,
                          S.PSet.to_list(20n, v)), 20n, {==},
                          Rp.Ords.all_fit_32(Q.Den.keep(src, kind,
                            S.PSet.to_list(20n, v)))),
                        E.Bool.and_l(S.PSet.valid(20n, v, True{}),
                          S.PSet.is_subset(20n, v, uu), co), vu,
                        {==},
                        PSet.subset_filter(src, kind, v,
                          E.Bool.and_l(S.PSet.valid(20n, v, True{}),
                            S.PSet.is_subset(20n, v, uu), co)),
                        E.Bool.and_r(S.PSet.valid(20n, v, True{}),
                          S.PSet.is_subset(20n, v, uu), co))),
                    okT, fin)
                case Qe.FReach{policy}:
                  Ev.go_spec.reach(g, src, v, rest, ok, uu, policy,
                    R.Reach.done(20n,
                      R.Reach.closure(Idx.Source.n(src), 32n,
                        Idx.Source.graph(src, policy), 20n,
                        S.PSet.to_list(20n, v))), {==}, gf, su, vu,
                    E.Bool.and_l(S.PSet.valid(20n, v, True{}),
                      S.PSet.is_subset(20n, v, uu), co),
                    E.Bool.and_r(S.PSet.valid(20n, v, True{}),
                      S.PSet.is_subset(20n, v, uu), co), fuelc,
                    E.Bool.and_r(Ev.frame_ok(uu, Qe.FReach{policy}),
                      Ev.stack_ok(uu, rest), ko), okT,
                    Ev.go_spec(g, src,
                      Qe.CVal{Ev.seen_of(src, policy, v)}, rest, ok,
                      uu, gf, su, vu, fu, fuelc,
                      E.Bool.and_r(Ev.frame_ok(uu,
                        Qe.FReach{policy}), Ev.stack_ok(uu, rest),
                        ko),
                      Ev.reach_ctl(src, policy, v, uu, gf, su, vu,
                        E.Bool.and_l(S.PSet.valid(20n, v, True{}),
                          S.PSet.is_subset(20n, v, uu), co),
                        E.Bool.and_r(S.PSet.valid(20n, v, True{}),
                          S.PSet.is_subset(20n, v, uu), co),
                        fuelc), okT), fin)
        case Qe.CEval{e}:
          match e:
            case A.EEmpty{}:
              Ev.go_spec(g, src, Qe.CVal{S.PSet.empty()}, k, ok, uu,
                gf, su, vu, fu, fuelc, ko,
                E.Bool.and_both(
                  S.PSet.valid(20n, S.PZero{}, True{}),
                  S.PSet.is_subset(20n, S.PZero{}, uu),
                  Vk.PSet.valid_zero(20n),
                  PSet.subset_zero(20n, uu, vu, {==})), okT, fin)
            case A.EFull{}:
              Ev.go_spec(g, src,
                Qe.CVal{Q.Den.universe(Idx.Source.n(src))}, k, ok,
                uu, gf, su, vu, fu, fuelc, ko,
                E.Bool.and_both(S.PSet.valid(20n,
                  Q.Den.universe(Idx.Source.n(src)), True{}),
                  S.PSet.is_subset(20n,
                    Q.Den.universe(Idx.Source.n(src)), uu),
                  Rp.Eval.valid(A.EFull{}, src, {==}, gf), fu), okT,
                fin)
            case A.ELit{set}:
              Ev.go_spec(g, src, Qe.CVal{set}, k, ok, uu, gf, su,
                vu, fu, fuelc, ko, co, okT, fin)
            case A.EUnion{a, b}:
              Ev.go_spec(g, src, Qe.CEval{a},
                Con{Qe.FRight{0n, b}, k}, ok, uu, gf, su, vu, fu,
                fuelc,
                E.Bool.and_both(Ev.frame_ok(uu, Qe.FRight{0n, b}),
                  Ev.stack_ok(uu, k),
                  Ev.go_valid.right(uu, a, b, co), ko),
                Ev.go_valid.left(uu, a, b, co), okT, fin)
            case A.EInter{a, b}:
              Ev.go_spec(g, src, Qe.CEval{a},
                Con{Qe.FRight{1n, b}, k}, ok, uu, gf, su, vu, fu,
                fuelc,
                E.Bool.and_both(Ev.frame_ok(uu, Qe.FRight{1n, b}),
                  Ev.stack_ok(uu, k),
                  Ev.go_valid.right(uu, a, b, co), ko),
                Ev.go_valid.left(uu, a, b, co), okT, fin)
            case A.EDiff{a, b}:
              Ev.go_spec(g, src, Qe.CEval{a},
                Con{Qe.FRight{2n, b}, k}, ok, uu, gf, su, vu, fu,
                fuelc,
                E.Bool.and_both(Ev.frame_ok(uu, Qe.FRight{2n, b}),
                  Ev.stack_ok(uu, k),
                  Ev.go_valid.right(uu, a, b, co), ko),
                Ev.go_valid.left(uu, a, b, co), okT, fin)
            case A.EReach{policy, a}:
              Ev.go_spec(g, src, Qe.CEval{a},
                Con{Qe.FReach{policy}, k}, ok, uu, gf, su, vu, fu,
                fuelc,
                E.Bool.and_both(Ev.frame_ok(uu, Qe.FReach{policy}),
                  Ev.stack_ok(uu, k), {==}, ko), co, okT, fin)
            case A.EFilter{kind, a}:
              Ev.go_spec(g, src, Qe.CEval{a},
                Con{Qe.FFilter{kind}, k}, ok, uu, gf, su, vu, fu,
                fuelc,
                E.Bool.and_both(Ev.frame_ok(uu, Qe.FFilter{kind}),
                  Ev.stack_ok(uu, k), {==}, ko), co, okT, fin)

# ---------------------------------------------------------------------------
# The rewrites keep the literals inside the bound.
# ---------------------------------------------------------------------------

law Simp.union_in:
  for +uu: S.PSet
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +ea: Bool
  for +eb: Bool
  for +la: {Ev.lits_in(uu, a) == True{} : Bool}
  for +lb: {Ev.lits_in(uu, b) == True{} : Bool}
  {Ev.lits_in(uu, Rw.Rw.union(a, b, ea, eb)) == True{} : Bool}

def Simp.union_in(uu, a, b, ea, eb, la, lb):
  match ea:
    case True{}:
      lb
    case False{}:
      match eb:
        case True{}:
          la
        case False{}:
          E.Bool.and_both(Ev.lits_in(uu, a), Ev.lits_in(uu, b), la,
            lb)

law Simp.inter_in:
  for +uu: S.PSet
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +ea: Bool
  for +eb: Bool
  for +la: {Ev.lits_in(uu, a) == True{} : Bool}
  for +lb: {Ev.lits_in(uu, b) == True{} : Bool}
  {Ev.lits_in(uu, Rw.Rw.inter(a, b, ea, eb)) == True{} : Bool}

def Simp.inter_in(uu, a, b, ea, eb, la, lb):
  match ea:
    case True{}:
      {==}
    case False{}:
      match eb:
        case True{}:
          {==}
        case False{}:
          E.Bool.and_both(Ev.lits_in(uu, a), Ev.lits_in(uu, b), la,
            lb)

law Simp.diff_in:
  for +uu: S.PSet
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +ea: Bool
  for +eb: Bool
  for +la: {Ev.lits_in(uu, a) == True{} : Bool}
  for +lb: {Ev.lits_in(uu, b) == True{} : Bool}
  {Ev.lits_in(uu, Rw.Rw.diff(a, b, ea, eb)) == True{} : Bool}

def Simp.diff_in(uu, a, b, ea, eb, la, lb):
  match ea:
    case True{}:
      {==}
    case False{}:
      match eb:
        case True{}:
          la
        case False{}:
          E.Bool.and_both(Ev.lits_in(uu, a), Ev.lits_in(uu, b), la,
            lb)

law Simp.reach_in:
  for +uu: S.PSet
  for +p: Idx.Policy
  for +a: A.SetExpr
  for +ea: Bool
  for +la: {Ev.lits_in(uu, a) == True{} : Bool}
  {Ev.lits_in(uu, Rw.Rw.reach(p, a, ea)) == True{} : Bool}

def Simp.reach_in(uu, p, a, ea, la):
  match ea:
    case True{}:
      {==}
    case False{}:
      la

law Simp.join_in:
  for +op: Nat
  for +uu: S.PSet
  for +a: A.SetExpr
  for +b: A.SetExpr
  for +la: {Ev.lits_in(uu, a) == True{} : Bool}
  for +lb: {Ev.lits_in(uu, b) == True{} : Bool}
  {Ev.lits_in(uu, Rw.Rw.join.go(a, b, op)) == True{} : Bool}

def Simp.join_in(op, uu, a, b, la, lb):
  match op:
    case 0n:
      Simp.union_in(uu, a, b, Rw.Rw.is_empty_expr(a),
        Rw.Rw.is_empty_expr(b), la, lb)
    case 1n+x:
      match x:
        case 0n:
          Simp.inter_in(uu, a, b, Rw.Rw.is_empty_expr(a),
            Rw.Rw.is_empty_expr(b), la, lb)
        case 1n+y:
          Simp.diff_in(uu, a, b, Rw.Rw.is_empty_expr(a),
            Rw.Rw.is_empty_expr(b), la, lb)

law Simp.simplify_in:
  for +e: A.SetExpr
  for +uu: S.PSet
  for +le: {Ev.lits_in(uu, e) == True{} : Bool}
  {Ev.lits_in(uu, Rw.Rw.simplify(e)) == True{} : Bool}

def Simp.simplify_in(e, uu, le):
  match e:
    case A.EEmpty{}:
      {==}
    case A.EFull{}:
      {==}
    case A.ELit{set}:
      le
    case A.EUnion{a, b}:
      Simp.join_in(U32.to_nat(0), uu, Rw.Rw.simplify(a),
        Rw.Rw.simplify(b),
        Simp.simplify_in(a, uu,
          E.Bool.and_l(Ev.lits_in(uu, a), Ev.lits_in(uu, b), le)),
        Simp.simplify_in(b, uu,
          E.Bool.and_r(Ev.lits_in(uu, a), Ev.lits_in(uu, b), le)))
    case A.EInter{a, b}:
      Simp.join_in(U32.to_nat(1), uu, Rw.Rw.simplify(a),
        Rw.Rw.simplify(b),
        Simp.simplify_in(a, uu,
          E.Bool.and_l(Ev.lits_in(uu, a), Ev.lits_in(uu, b), le)),
        Simp.simplify_in(b, uu,
          E.Bool.and_r(Ev.lits_in(uu, a), Ev.lits_in(uu, b), le)))
    case A.EDiff{a, b}:
      Simp.join_in(U32.to_nat(2), uu, Rw.Rw.simplify(a),
        Rw.Rw.simplify(b),
        Simp.simplify_in(a, uu,
          E.Bool.and_l(Ev.lits_in(uu, a), Ev.lits_in(uu, b), le)),
        Simp.simplify_in(b, uu,
          E.Bool.and_r(Ev.lits_in(uu, a), Ev.lits_in(uu, b), le)))
    case A.EReach{policy, a}:
      Simp.reach_in(uu, policy, Rw.Rw.simplify(a),
        Rw.Rw.is_empty_expr(Rw.Rw.simplify(a)),
        Simp.simplify_in(a, uu, le))
    case A.EFilter{kind, a}:
      Simp.simplify_in(a, uu, le)

# ---------------------------------------------------------------------------
# Q-03.
# ---------------------------------------------------------------------------

law Ev.run_member:
  for +src: Idx.Source
  for +e: A.SetExpr
  for +x: U32
  for +uu: S.PSet
  for +gf: {Rp.Src.graphs_fit(src) == True{} : Bool}
  for +su: {Src.graphs_in(src, uu) == True{} : Bool}
  for +vu: {S.PSet.valid(20n, uu, True{}) == True{} : Bool}
  for +fu: {S.PSet.is_subset(20n,
    Q.Den.universe(Idx.Source.n(src)), uu) == True{} : Bool}
  for +fuelc: {C.Nat.upto(S.PSet.count(20n, uu, S.PSet.half(20n)),
    1n+Idx.Source.n(src)) == True{} : Bool}
  for +vl: {Rp.SetExpr.valid_lits(e) == True{} : Bool}
  for +le: {Ev.lits_in(uu, e) == True{} : Bool}
  for ok: {Qe.Val.ok(Qe.Ev.run(src, e)) == True{} : Bool}
  {S.PSet.member(20n, Qe.Val.set(Qe.Ev.run(src, e)), x)
    == S.PSet.member(20n, Q.Den.eval(src, e), x) : Bool}

def Ev.run_member(src, e, x, uu, gf, su, vu, fu, fuelc, vl, le, ok):
  Ca.PSet.member_same(20n, Qe.Val.set(Qe.Ev.run(src, e)),
    Q.Den.eval(src, e), x,
    Ev.go_valid(1n+Nat.mul(4n, Qe.Ev.size(Rw.Rw.simplify(e))), src,
      Qe.CEval{Rw.Rw.simplify(e)}, Nil{}, True{}, gf, {==},
      Rp.Rw.simplify_lits(e, vl)),
    Rp.Eval.valid(e, src, vl, gf), {==}, Dc.U32.hi_zero_full(x),
    Ca.PSet.same_trans(20n, Qe.Val.set(Qe.Ev.run(src, e)),
      Q.Den.eval(src, Rw.Rw.simplify(e)), Q.Den.eval(src, e),
      Ev.go_valid(1n+Nat.mul(4n, Qe.Ev.size(Rw.Rw.simplify(e))),
        src, Qe.CEval{Rw.Rw.simplify(e)}, Nil{}, True{}, gf, {==},
        Rp.Rw.simplify_lits(e, vl)),
      Rp.Eval.valid(Rw.Rw.simplify(e), src,
        Rp.Rw.simplify_lits(e, vl), gf),
      Rp.Eval.valid(e, src, vl, gf), {==},
      Ev.go_spec(1n+Nat.mul(4n, Qe.Ev.size(Rw.Rw.simplify(e))), src,
        Qe.CEval{Rw.Rw.simplify(e)}, Nil{}, True{}, uu, gf, su, vu,
        fu, fuelc, {==},
        E.Bool.and_both(Rp.SetExpr.valid_lits(Rw.Rw.simplify(e)),
          Ev.lits_in(uu, Rw.Rw.simplify(e)),
          Rp.Rw.simplify_lits(e, vl), Simp.simplify_in(e, uu, le)),
        {==}, ok),
      Rp.Rw.simplify_same(e, src, vl, gf)))
