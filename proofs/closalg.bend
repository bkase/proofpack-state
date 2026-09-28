# proofs/closalg.bend -- the closure algebra above the chain.
#
# Three of C-03's five properties are about the chain rather than about the
# fixed point, and they hold at every fuel:
#
#   * the closure is monotone in its roots, because a round is monotone -- a
#     union of monotone things and `post`, which proofs/postmono.bend shows is
#     monotone;
#   * the closure of a union is the union of the closures, because a round
#     distributes over a union: `post` does, and union is associative and
#     commutative up to membership;
#   * and the rounds compose, `iter(a + b)` being `iter(a)` after `iter(b)`,
#     which is what makes "run more rounds" mean what it looks like.
#
# The vehicle is `PSet.same` -- mutual `PSet.is_subset`, so a decidable
# equality on sets that a proof can carry and an induction can use twice.
# Two sets that are `PSet.same` have the same members at every ordinal, which
# is how the pointwise laws in LAWS.bend are recovered at the end.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./shape.bend as Sh
import ./leafenum.bend as Le
import ./enum.bend as En
import ./setops.bend as So
import ./treeenum.bend as Te
import ./subsetconv.bend as Sc
import ./subsetalg.bend as Sa
import ./validkeep.bend as Vk
import ./graphrange.bend as Gr
import ./postmono.bend as Pm
import ./lfp.bend as Lp
import ../core/count.bend as C
import ../core/set.bend as S
import ../closure/graph.bend as G
import ../spec/closure.bend as Sp

# ---------------------------------------------------------------------------
# A set is inside any union it is an operand of -- the right operand too.
# ---------------------------------------------------------------------------

def PSet.member_right2(+d: Nat, +a: S.PSet, +b: S.PSet, +y: U32,
  +va: {S.PSet.valid(d, a, True{}) == True{} : Bool},
  +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +inv: {Dc.U32.hi_zero(y, 12n+d) == True{} : Bool},
  +mb: {S.PSet.member(d, b, y) == True{} : Bool})
  -> {S.PSet.member(d, S.PSet.union(d, a, b), y) == True{} : Bool}:
  %E.Bool.sym(S.PSet.member(d, S.PSet.union(d, a, b), y),
    Bool.or(S.PSet.member(d, a, y), S.PSet.member(d, b, y)),
    So.PSet.union_pointwise(d, a, b, S.PSet.half(d), y, {==}, lt,
      Sh.PSet.valid_wf(d, a, va), Sh.PSet.valid_wf(d, b, vb), inv,
      U32.is_lt(y, S.PSet.half(d)), {==})) : {_ == True{} : Bool}
  Sa.Ords.or_right(S.PSet.member(d, a, y), S.PSet.member(d, b, y),
    mb)

law Ords.all_mem_right:
  for +l: List<&2, U32>
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l, S.PSet.to_list(d, b)) == True{} : Bool}
  {Sc.Ords.all_mem(l, d, S.PSet.union(d, a, b)) == True{} : Bool}

def Ords.all_mem_right(l, d, a, b, va, vb, lt, ai):
  match l:
    case Nil{}:
      {==}
    case Con{y, t}:
      E.Bool.and_both(S.PSet.member(d, S.PSet.union(d, a, b), y),
        Sc.Ords.all_mem(t, d, S.PSet.union(d, a, b)),
        PSet.member_right2(d, a, b, y, va, vb, lt,
          Sa.PSet.in_range_of_to_list(d, b, y, vb, lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(d, b), y),
              Sa.Ords.all_in(t, S.PSet.to_list(d, b)), ai)),
          Sa.PSet.member_of_to_list(d, b, y, vb, lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(d, b), y),
              Sa.Ords.all_in(t, S.PSet.to_list(d, b)), ai))),
        Ords.all_mem_right(t, d, a, b, va, vb, lt,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(d, b), y),
            Sa.Ords.all_in(t, S.PSet.to_list(d, b)), ai)))

law PSet.subset_union_r:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {S.PSet.is_subset(d, b, S.PSet.union(d, a, b)) == True{} : Bool}

def PSet.subset_union_r(d, a, b, va, vb, lt):
  Sc.PSet.subset_of_members(d, b, S.PSet.union(d, a, b), vb,
    Vk.PSet.valid_union(d, a, b, va, vb), lt,
    Ords.all_mem_right(S.PSet.to_list(d, b), d, a, b, va, vb, lt,
      Sa.Ords.all_in_self(S.PSet.to_list(d, b))))

# ---------------------------------------------------------------------------
# Mutual inclusion, as a decidable equality on sets.
# ---------------------------------------------------------------------------

def PSet.same(+d: Nat, +a: S.PSet, +b: S.PSet) -> Bool:
  Bool.and(S.PSet.is_subset(d, a, b), S.PSet.is_subset(d, b, a))

def PSet.same_l(+d: Nat, +a: S.PSet, +b: S.PSet,
  +sm: {PSet.same(d, a, b) == True{} : Bool})
  -> {S.PSet.is_subset(d, a, b) == True{} : Bool}:
  E.Bool.and_l(S.PSet.is_subset(d, a, b),
    S.PSet.is_subset(d, b, a), sm)

def PSet.same_r(+d: Nat, +a: S.PSet, +b: S.PSet,
  +sm: {PSet.same(d, a, b) == True{} : Bool})
  -> {S.PSet.is_subset(d, b, a) == True{} : Bool}:
  E.Bool.and_r(S.PSet.is_subset(d, a, b),
    S.PSet.is_subset(d, b, a), sm)

law PSet.same_refl:
  for +d: Nat
  for +a: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {PSet.same(d, a, a) == True{} : Bool}

def PSet.same_refl(d, a, va, lt):
  E.Bool.and_both(S.PSet.is_subset(d, a, a),
    S.PSet.is_subset(d, a, a), Lp.PSet.subset_refl(d, a, va, lt),
    Lp.PSet.subset_refl(d, a, va, lt))

law PSet.same_sym:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +sm: {PSet.same(d, a, b) == True{} : Bool}
  {PSet.same(d, b, a) == True{} : Bool}

def PSet.same_sym(d, a, b, sm):
  E.Bool.and_both(S.PSet.is_subset(d, b, a),
    S.PSet.is_subset(d, a, b), PSet.same_r(d, a, b, sm),
    PSet.same_l(d, a, b, sm))

law PSet.same_trans:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +c: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +vc: {S.PSet.valid(d, c, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ab: {PSet.same(d, a, b) == True{} : Bool}
  for +bc: {PSet.same(d, b, c) == True{} : Bool}
  {PSet.same(d, a, c) == True{} : Bool}

def PSet.same_trans(d, a, b, c, va, vb, vc, lt, ab, bc):
  E.Bool.and_both(S.PSet.is_subset(d, a, c),
    S.PSet.is_subset(d, c, a),
    Sa.PSet.subset_trans(d, a, b, c, va, vb, vc, lt,
      PSet.same_l(d, a, b, ab), PSet.same_l(d, b, c, bc)),
    Sa.PSet.subset_trans(d, c, b, a, vc, vb, va, lt,
      PSet.same_r(d, b, c, bc), PSet.same_r(d, a, b, ab)))

# Two sets that include each other agree at every ordinal.
law PSet.member_of_same:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +e: Bool
  for +f: Bool
  for +ee: {e == S.PSet.member(d, a, x) : Bool}
  for +ff: {f == S.PSet.member(d, b, x) : Bool}
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +sm: {PSet.same(d, a, b) == True{} : Bool}
  {S.PSet.member(d, a, x) == S.PSet.member(d, b, x) : Bool}

def PSet.member_of_same(d, a, b, x, e, f, ee, ff, va, vb, lt, inv,
  sm):
  match e:
    case True{}:
      match f:
        case True{}:
          %ee : {_ == S.PSet.member(d, b, x) : Bool}
          ff
        case False{}:
          E.Bool.noconf({S.PSet.member(d, a, x)
            == S.PSet.member(d, b, x) : Bool},
            %Sa.PSet.subset_member_at(d, a, b, x, va, vb, lt, inv,
              PSet.same_l(d, a, b, sm),
              E.Bool.sym(True{}, S.PSet.member(d, a, x), ee))
              : {False{} == _ : Bool}
            ff)
    case False{}:
      match f:
        case True{}:
          E.Bool.noconf({S.PSet.member(d, a, x)
            == S.PSet.member(d, b, x) : Bool},
            %Sa.PSet.subset_member_at(d, b, a, x, vb, va, lt, inv,
              PSet.same_r(d, a, b, sm),
              E.Bool.sym(True{}, S.PSet.member(d, b, x), ff))
              : {False{} == _ : Bool}
            ee)
        case False{}:
          %ee : {_ == S.PSet.member(d, b, x) : Bool}
          ff

law PSet.member_same:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +sm: {PSet.same(d, a, b) == True{} : Bool}
  {S.PSet.member(d, a, x) == S.PSet.member(d, b, x) : Bool}

def PSet.member_same(d, a, b, x, va, vb, lt, inv, sm):
  PSet.member_of_same(d, a, b, x, S.PSet.member(d, a, x),
    S.PSet.member(d, b, x), {==}, {==}, va, vb, lt, inv, sm)

# ---------------------------------------------------------------------------
# A round is monotone.
# ---------------------------------------------------------------------------

def Spec.sub_step(+td: Nat, +sd: Nat, +g: G.Graph(), +x: S.PSet,
  +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool})
  -> {S.PSet.is_subset(sd, x, Sp.Spec.step(td, g, sd, x)) == True{}
    : Bool}:
  Lp.PSet.subset_union_l(sd, x, Sp.Spec.post(td, g, sd, x), vx,
    Pm.Spec.post_valid(td, sd, g, x, gf, lt), lt)

def Spec.post_sub_step(+td: Nat, +sd: Nat, +g: G.Graph(),
  +x: S.PSet,
  +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool})
  -> {S.PSet.is_subset(sd, Sp.Spec.post(td, g, sd, x),
    Sp.Spec.step(td, g, sd, x)) == True{} : Bool}:
  PSet.subset_union_r(sd, x, Sp.Spec.post(td, g, sd, x), vx,
    Pm.Spec.post_valid(td, sd, g, x, gf, lt), lt)

law Spec.step_mono:
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +x: S.PSet
  for +y: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool}
  for +vy: {S.PSet.valid(sd, y, True{}) == True{} : Bool}
  for +xy: {S.PSet.is_subset(sd, x, y) == True{} : Bool}
  {S.PSet.is_subset(sd, Sp.Spec.step(td, g, sd, x),
    Sp.Spec.step(td, g, sd, y)) == True{} : Bool}

def Spec.step_mono(td, sd, g, x, y, gf, lt, vx, vy, xy):
  Sa.PSet.subset_union(sd, x, Sp.Spec.post(td, g, sd, x),
    Sp.Spec.step(td, g, sd, y), vx,
    Pm.Spec.post_valid(td, sd, g, x, gf, lt),
    Lp.Spec.step_valid(td, sd, g, y, gf, lt, vy), lt,
    Sa.PSet.subset_trans(sd, x, y, Sp.Spec.step(td, g, sd, y), vx,
      vy, Lp.Spec.step_valid(td, sd, g, y, gf, lt, vy), lt, xy,
      Spec.sub_step(td, sd, g, y, gf, lt, vy)),
    Sa.PSet.subset_trans(sd, Sp.Spec.post(td, g, sd, x),
      Sp.Spec.post(td, g, sd, y), Sp.Spec.step(td, g, sd, y),
      Pm.Spec.post_valid(td, sd, g, x, gf, lt),
      Pm.Spec.post_valid(td, sd, g, y, gf, lt),
      Lp.Spec.step_valid(td, sd, g, y, gf, lt, vy), lt,
      Pm.Spec.post_mono(td, sd, g, x, y, gf, lt, vx, vy, xy),
      Spec.post_sub_step(td, sd, g, y, gf, lt, vy)))

law Spec.iter_mono:
  for +f: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +x: S.PSet
  for +y: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool}
  for +vy: {S.PSet.valid(sd, y, True{}) == True{} : Bool}
  for +xy: {S.PSet.is_subset(sd, x, y) == True{} : Bool}
  {S.PSet.is_subset(sd, Sp.Spec.iter(f, td, g, sd, x),
    Sp.Spec.iter(f, td, g, sd, y)) == True{} : Bool}

def Spec.iter_mono(f, td, sd, g, x, y, gf, lt, vx, vy, xy):
  match f:
    case 0n:
      xy
    case 1n+p:
      Spec.iter_mono(p, td, sd, g, Sp.Spec.step(td, g, sd, x),
        Sp.Spec.step(td, g, sd, y), gf, lt,
        Lp.Spec.step_valid(td, sd, g, x, gf, lt, vx),
        Lp.Spec.step_valid(td, sd, g, y, gf, lt, vy),
        Spec.step_mono(td, sd, g, x, y, gf, lt, vx, vy, xy))

law Spec.closure_mono:
  for +n: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +x: S.PSet
  for +y: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool}
  for +vy: {S.PSet.valid(sd, y, True{}) == True{} : Bool}
  for +xy: {S.PSet.is_subset(sd, x, y) == True{} : Bool}
  {S.PSet.is_subset(sd, Sp.Spec.closure(n, td, g, sd, x),
    Sp.Spec.closure(n, td, g, sd, y)) == True{} : Bool}

def Spec.closure_mono(n, td, sd, g, x, y, gf, lt, vx, vy, xy):
  Spec.iter_mono(1n+n, td, sd, g, x, y, gf, lt, vx, vy, xy)

law Spec.iter_same:
  for +f: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +x: S.PSet
  for +y: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool}
  for +vy: {S.PSet.valid(sd, y, True{}) == True{} : Bool}
  for +sm: {PSet.same(sd, x, y) == True{} : Bool}
  {PSet.same(sd, Sp.Spec.iter(f, td, g, sd, x),
    Sp.Spec.iter(f, td, g, sd, y)) == True{} : Bool}

def Spec.iter_same(f, td, sd, g, x, y, gf, lt, vx, vy, sm):
  E.Bool.and_both(
    S.PSet.is_subset(sd, Sp.Spec.iter(f, td, g, sd, x),
      Sp.Spec.iter(f, td, g, sd, y)),
    S.PSet.is_subset(sd, Sp.Spec.iter(f, td, g, sd, y),
      Sp.Spec.iter(f, td, g, sd, x)),
    Spec.iter_mono(f, td, sd, g, x, y, gf, lt, vx, vy,
      PSet.same_l(sd, x, y, sm)),
    Spec.iter_mono(f, td, sd, g, y, x, gf, lt, vy, vx,
      PSet.same_r(sd, x, y, sm)))

# ---------------------------------------------------------------------------
# A round distributes over a union.
# ---------------------------------------------------------------------------

law Graph.any_succ_append:
  for +l1: List<&2, U32>
  for +l2: List<&2, U32>
  for +td: Nat
  for +g: G.Graph()
  for +z: U32
  {Gr.Graph.any_succ(td, g, List.append(&2, U32, l1, l2), z)
    == Bool.or(Gr.Graph.any_succ(td, g, l1, z),
         Gr.Graph.any_succ(td, g, l2, z)) : Bool}

def Graph.any_succ_append(l1, l2, td, g, z):
  match l1:
    case Nil{}:
      {==}
    case Con{v, t}:
      %E.Bool.sym(
        Gr.Graph.any_succ(td, g, List.append(&2, U32, t, l2), z),
        Bool.or(Gr.Graph.any_succ(td, g, t, z),
          Gr.Graph.any_succ(td, g, l2, z)),
        Graph.any_succ_append(t, l2, td, g, z))
        : {Bool.or(List.contains(~U32, ~U32.is_eq,
             G.Graph.succ(td, g, v), z), _)
          == Bool.or(Bool.or(List.contains(~U32, ~U32.is_eq,
               G.Graph.succ(td, g, v), z),
               Gr.Graph.any_succ(td, g, t, z)),
               Gr.Graph.any_succ(td, g, l2, z)) : Bool}
      En.Bool.or_assoc(List.contains(~U32, ~U32.is_eq,
        G.Graph.succ(td, g, v), z), Gr.Graph.any_succ(td, g, t, z),
        Gr.Graph.any_succ(td, g, l2, z))

def Ords.in_append(+a: List<&2, U32>, +b: List<&2, U32>, +y: U32,
  +ou: {Bool.or(List.contains(~U32, ~U32.is_eq, a, y),
    List.contains(~U32, ~U32.is_eq, b, y)) == True{} : Bool})
  -> {List.contains(~U32, ~U32.is_eq, List.append(&2, U32, a, b), y)
    == True{} : Bool}:
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      List.append(&2, U32, a, b), y),
    Bool.or(List.contains(~U32, ~U32.is_eq, a, y),
      List.contains(~U32, ~U32.is_eq, b, y)),
    Le.List.contains_append(a, b, y)) : {_ == True{} : Bool}
  ou

def Ords.in_append_of_union(+d: Nat, +a: S.PSet, +b: S.PSet,
  +y: U32, +e: Bool,
  +ee: {e == S.PSet.member(d, a, y) : Bool},
  +va: {S.PSet.valid(d, a, True{}) == True{} : Bool},
  +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +inv: {Dc.U32.hi_zero(y, 12n+d) == True{} : Bool},
  +ou: {Bool.or(S.PSet.member(d, a, y), S.PSet.member(d, b, y))
    == True{} : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
    List.append(&2, U32, S.PSet.to_list(d, a), S.PSet.to_list(d, b)),
    y) == True{} : Bool}:
  match e:
    case True{}:
      Ords.in_append(S.PSet.to_list(d, a), S.PSet.to_list(d, b), y,
        Sa.Ords.or_left(List.contains(~U32, ~U32.is_eq,
          S.PSet.to_list(d, a), y),
          List.contains(~U32, ~U32.is_eq, S.PSet.to_list(d, b), y),
          Pm.Ords.in_of_member(d, a, y, va, lt, inv,
            E.Bool.sym(True{}, S.PSet.member(d, a, y), ee))))
    case False{}:
      Ords.in_append(S.PSet.to_list(d, a), S.PSet.to_list(d, b), y,
        Sa.Ords.or_right(List.contains(~U32, ~U32.is_eq,
          S.PSet.to_list(d, a), y),
          List.contains(~U32, ~U32.is_eq, S.PSet.to_list(d, b), y),
          Pm.Ords.in_of_member(d, b, y, vb, lt, inv,
            Sa.PSet.member_right(d, a, b, y, ee, ou))))

law Ords.all_in_union:
  for +l: List<&2, U32>
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l,
    S.PSet.to_list(d, S.PSet.union(d, a, b))) == True{} : Bool}
  {Sa.Ords.all_in(l, List.append(&2, U32, S.PSet.to_list(d, a),
    S.PSet.to_list(d, b))) == True{} : Bool}

def Ords.all_in_union(l, d, a, b, va, vb, lt, ai):
  match l:
    case Nil{}:
      {==}
    case Con{y, t}:
      E.Bool.and_both(List.contains(~U32, ~U32.is_eq,
        List.append(&2, U32, S.PSet.to_list(d, a),
          S.PSet.to_list(d, b)), y),
        Sa.Ords.all_in(t, List.append(&2, U32, S.PSet.to_list(d, a),
          S.PSet.to_list(d, b))),
        Ords.in_append_of_union(d, a, b, y,
          S.PSet.member(d, a, y), {==}, va, vb, lt,
          Sa.PSet.in_range_of_to_list(d, S.PSet.union(d, a, b), y,
            Vk.PSet.valid_union(d, a, b, va, vb), lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(d, S.PSet.union(d, a, b)), y),
              Sa.Ords.all_in(t,
                S.PSet.to_list(d, S.PSet.union(d, a, b))), ai)),
          Sa.PSet.member_union(d, a, b, y, va, vb, lt,
            Sa.PSet.in_range_of_to_list(d, S.PSet.union(d, a, b), y,
              Vk.PSet.valid_union(d, a, b, va, vb), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(d, S.PSet.union(d, a, b)), y),
                Sa.Ords.all_in(t,
                  S.PSet.to_list(d, S.PSet.union(d, a, b))), ai)),
            Sa.PSet.member_of_to_list(d, S.PSet.union(d, a, b), y,
              Vk.PSet.valid_union(d, a, b, va, vb), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(d, S.PSet.union(d, a, b)), y),
                Sa.Ords.all_in(t,
                  S.PSet.to_list(d, S.PSet.union(d, a, b))), ai)))),
        Ords.all_in_union(t, d, a, b, va, vb, lt,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(d, S.PSet.union(d, a, b)), y),
            Sa.Ords.all_in(t,
              S.PSet.to_list(d, S.PSet.union(d, a, b))), ai)))

def Spec.member_of_post_side(+td: Nat, +sd: Nat, +g: G.Graph(),
  +a: S.PSet, +b: S.PSet, +z: U32, +e: Bool,
  +ee: {e == Gr.Graph.any_succ(td, g, S.PSet.to_list(sd, a), z)
    : Bool},
  +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +va: {S.PSet.valid(sd, a, True{}) == True{} : Bool},
  +vb: {S.PSet.valid(sd, b, True{}) == True{} : Bool},
  +inv: {Dc.U32.hi_zero(z, 12n+sd) == True{} : Bool},
  +ou: {Bool.or(Gr.Graph.any_succ(td, g, S.PSet.to_list(sd, a), z),
    Gr.Graph.any_succ(td, g, S.PSet.to_list(sd, b), z)) == True{}
    : Bool})
  -> {S.PSet.member(sd, S.PSet.union(sd,
    Sp.Spec.post(td, g, sd, a), Sp.Spec.post(td, g, sd, b)), z)
    == True{} : Bool}:
  match e:
    case True{}:
      Lp.PSet.member_left(sd, Sp.Spec.post(td, g, sd, a),
        Sp.Spec.post(td, g, sd, b), z,
        Pm.Spec.post_valid(td, sd, g, a, gf, lt),
        Pm.Spec.post_valid(td, sd, g, b, gf, lt), lt, inv,
        Pm.Spec.post_of_any(td, sd, g, a, z, lt, inv,
          E.Bool.sym(True{},
            Gr.Graph.any_succ(td, g, S.PSet.to_list(sd, a), z), ee)))
    case False{}:
      PSet.member_right2(sd, Sp.Spec.post(td, g, sd, a),
        Sp.Spec.post(td, g, sd, b), z,
        Pm.Spec.post_valid(td, sd, g, a, gf, lt),
        Pm.Spec.post_valid(td, sd, g, b, gf, lt), lt, inv,
        Pm.Spec.post_of_any(td, sd, g, b, z, lt, inv,
          %E.Bool.sym(False{},
            Gr.Graph.any_succ(td, g, S.PSet.to_list(sd, a), z), ee)
            : {Bool.or(_,
              Gr.Graph.any_succ(td, g, S.PSet.to_list(sd, b), z))
              == True{} : Bool}
          ou))

def Spec.any_of_union(+td: Nat, +sd: Nat, +g: G.Graph(),
  +a: S.PSet, +b: S.PSet, +z: U32,
  +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +va: {S.PSet.valid(sd, a, True{}) == True{} : Bool},
  +vb: {S.PSet.valid(sd, b, True{}) == True{} : Bool},
  +inv: {Dc.U32.hi_zero(z, 12n+sd) == True{} : Bool},
  +m: {S.PSet.member(sd,
    Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)), z) == True{}
    : Bool})
  -> {Bool.or(Gr.Graph.any_succ(td, g, S.PSet.to_list(sd, a), z),
    Gr.Graph.any_succ(td, g, S.PSet.to_list(sd, b), z)) == True{}
    : Bool}:
  %Graph.any_succ_append(S.PSet.to_list(sd, a),
    S.PSet.to_list(sd, b), td, g, z) : {_ == True{} : Bool}
  Gr.Graph.any_succ_mono(S.PSet.to_list(sd, S.PSet.union(sd, a, b)),
    List.append(&2, U32, S.PSet.to_list(sd, a),
      S.PSet.to_list(sd, b)), td, g, z,
    Ords.all_in_union(S.PSet.to_list(sd, S.PSet.union(sd, a, b)), sd,
      a, b, va, vb, lt,
      Sa.Ords.all_in_self(
        S.PSet.to_list(sd, S.PSet.union(sd, a, b)))),
    Pm.Spec.any_of_post(td, sd, g, S.PSet.union(sd, a, b), z, gf, lt,
      inv, m))

law Ords.all_mem_post_union:
  for +l: List<&2, U32>
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +a: S.PSet
  for +b: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +va: {S.PSet.valid(sd, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(sd, b, True{}) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l, S.PSet.to_list(sd,
    Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)))) == True{}
    : Bool}
  {Sc.Ords.all_mem(l, sd, S.PSet.union(sd,
    Sp.Spec.post(td, g, sd, a), Sp.Spec.post(td, g, sd, b)))
    == True{} : Bool}

def Ords.all_mem_post_union(l, td, sd, g, a, b, gf, lt, va, vb, ai):
  match l:
    case Nil{}:
      {==}
    case Con{z, t}:
      E.Bool.and_both(S.PSet.member(sd, S.PSet.union(sd,
        Sp.Spec.post(td, g, sd, a), Sp.Spec.post(td, g, sd, b)), z),
        Sc.Ords.all_mem(t, sd, S.PSet.union(sd,
          Sp.Spec.post(td, g, sd, a), Sp.Spec.post(td, g, sd, b))),
        Spec.member_of_post_side(td, sd, g, a, b, z,
          Gr.Graph.any_succ(td, g, S.PSet.to_list(sd, a), z), {==},
          gf, lt, va, vb,
          Sa.PSet.in_range_of_to_list(sd,
            Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)), z,
            Pm.Spec.post_valid(td, sd, g, S.PSet.union(sd, a, b), gf,
              lt), lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(sd,
                Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b))), z),
              Sa.Ords.all_in(t, S.PSet.to_list(sd,
                Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)))),
              ai)),
          Spec.any_of_union(td, sd, g, a, b, z, gf, lt, va, vb,
            Sa.PSet.in_range_of_to_list(sd,
              Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)), z,
              Pm.Spec.post_valid(td, sd, g, S.PSet.union(sd, a, b),
                gf, lt), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(sd,
                  Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b))),
                z),
                Sa.Ords.all_in(t, S.PSet.to_list(sd,
                  Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)))),
                ai)),
            Sa.PSet.member_of_to_list(sd,
              Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)), z,
              Pm.Spec.post_valid(td, sd, g, S.PSet.union(sd, a, b),
                gf, lt), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(sd,
                  Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b))),
                z),
                Sa.Ords.all_in(t, S.PSet.to_list(sd,
                  Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)))),
                ai)))),
        Ords.all_mem_post_union(t, td, sd, g, a, b, gf, lt, va, vb,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(sd,
              Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b))), z),
            Sa.Ords.all_in(t, S.PSet.to_list(sd,
              Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)))),
            ai)))

law Spec.post_union:
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +a: S.PSet
  for +b: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +va: {S.PSet.valid(sd, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(sd, b, True{}) == True{} : Bool}
  {PSet.same(sd, Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)),
    S.PSet.union(sd, Sp.Spec.post(td, g, sd, a),
      Sp.Spec.post(td, g, sd, b))) == True{} : Bool}

def Spec.post_union(td, sd, g, a, b, gf, lt, va, vb):
  E.Bool.and_both(
    S.PSet.is_subset(sd,
      Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)),
      S.PSet.union(sd, Sp.Spec.post(td, g, sd, a),
        Sp.Spec.post(td, g, sd, b))),
    S.PSet.is_subset(sd,
      S.PSet.union(sd, Sp.Spec.post(td, g, sd, a),
        Sp.Spec.post(td, g, sd, b)),
      Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b))),
    Sc.PSet.subset_of_members(sd,
      Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)),
      S.PSet.union(sd, Sp.Spec.post(td, g, sd, a),
        Sp.Spec.post(td, g, sd, b)),
      Pm.Spec.post_valid(td, sd, g, S.PSet.union(sd, a, b), gf, lt),
      Vk.PSet.valid_union(sd, Sp.Spec.post(td, g, sd, a),
        Sp.Spec.post(td, g, sd, b),
        Pm.Spec.post_valid(td, sd, g, a, gf, lt),
        Pm.Spec.post_valid(td, sd, g, b, gf, lt)), lt,
      Ords.all_mem_post_union(S.PSet.to_list(sd,
        Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b))), td, sd, g,
        a, b, gf, lt, va, vb,
        Sa.Ords.all_in_self(S.PSet.to_list(sd,
          Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)))))),
    Sa.PSet.subset_union(sd, Sp.Spec.post(td, g, sd, a),
      Sp.Spec.post(td, g, sd, b),
      Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)),
      Pm.Spec.post_valid(td, sd, g, a, gf, lt),
      Pm.Spec.post_valid(td, sd, g, b, gf, lt),
      Pm.Spec.post_valid(td, sd, g, S.PSet.union(sd, a, b), gf, lt),
      lt,
      Pm.Spec.post_mono(td, sd, g, a, S.PSet.union(sd, a, b), gf, lt,
        va, Vk.PSet.valid_union(sd, a, b, va, vb),
        Lp.PSet.subset_union_l(sd, a, b, va, vb, lt)),
      Pm.Spec.post_mono(td, sd, g, b, S.PSet.union(sd, a, b), gf, lt,
        vb, Vk.PSet.valid_union(sd, a, b, va, vb),
        PSet.subset_union_r(sd, a, b, va, vb, lt))))

law Spec.step_union:
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +a: S.PSet
  for +b: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +va: {S.PSet.valid(sd, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(sd, b, True{}) == True{} : Bool}
  {PSet.same(sd, Sp.Spec.step(td, g, sd, S.PSet.union(sd, a, b)),
    S.PSet.union(sd, Sp.Spec.step(td, g, sd, a),
      Sp.Spec.step(td, g, sd, b))) == True{} : Bool}

def Spec.step_union(td, sd, g, a, b, gf, lt, va, vb):
  E.Bool.and_both(
    S.PSet.is_subset(sd,
      Sp.Spec.step(td, g, sd, S.PSet.union(sd, a, b)),
      S.PSet.union(sd, Sp.Spec.step(td, g, sd, a),
        Sp.Spec.step(td, g, sd, b))),
    S.PSet.is_subset(sd,
      S.PSet.union(sd, Sp.Spec.step(td, g, sd, a),
        Sp.Spec.step(td, g, sd, b)),
      Sp.Spec.step(td, g, sd, S.PSet.union(sd, a, b))),
    Sa.PSet.subset_union(sd, S.PSet.union(sd, a, b),
      Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)),
      S.PSet.union(sd, Sp.Spec.step(td, g, sd, a),
        Sp.Spec.step(td, g, sd, b)),
      Vk.PSet.valid_union(sd, a, b, va, vb),
      Pm.Spec.post_valid(td, sd, g, S.PSet.union(sd, a, b), gf, lt),
      Vk.PSet.valid_union(sd, Sp.Spec.step(td, g, sd, a),
        Sp.Spec.step(td, g, sd, b),
        Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
        Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb)), lt,
      Sa.PSet.subset_union(sd, a, b,
        S.PSet.union(sd, Sp.Spec.step(td, g, sd, a),
          Sp.Spec.step(td, g, sd, b)), va, vb,
        Vk.PSet.valid_union(sd, Sp.Spec.step(td, g, sd, a),
          Sp.Spec.step(td, g, sd, b),
          Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
          Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb)), lt,
        Sa.PSet.subset_trans(sd, a, Sp.Spec.step(td, g, sd, a),
          S.PSet.union(sd, Sp.Spec.step(td, g, sd, a),
            Sp.Spec.step(td, g, sd, b)), va,
          Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
          Vk.PSet.valid_union(sd, Sp.Spec.step(td, g, sd, a),
            Sp.Spec.step(td, g, sd, b),
            Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
            Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb)), lt,
          Spec.sub_step(td, sd, g, a, gf, lt, va),
          Lp.PSet.subset_union_l(sd, Sp.Spec.step(td, g, sd, a),
            Sp.Spec.step(td, g, sd, b),
            Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
            Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb), lt)),
        Sa.PSet.subset_trans(sd, b, Sp.Spec.step(td, g, sd, b),
          S.PSet.union(sd, Sp.Spec.step(td, g, sd, a),
            Sp.Spec.step(td, g, sd, b)), vb,
          Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb),
          Vk.PSet.valid_union(sd, Sp.Spec.step(td, g, sd, a),
            Sp.Spec.step(td, g, sd, b),
            Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
            Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb)), lt,
          Spec.sub_step(td, sd, g, b, gf, lt, vb),
          PSet.subset_union_r(sd, Sp.Spec.step(td, g, sd, a),
            Sp.Spec.step(td, g, sd, b),
            Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
            Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb), lt))),
      Sa.PSet.subset_trans(sd,
        Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)),
        S.PSet.union(sd, Sp.Spec.post(td, g, sd, a),
          Sp.Spec.post(td, g, sd, b)),
        S.PSet.union(sd, Sp.Spec.step(td, g, sd, a),
          Sp.Spec.step(td, g, sd, b)),
        Pm.Spec.post_valid(td, sd, g, S.PSet.union(sd, a, b), gf,
          lt),
        Vk.PSet.valid_union(sd, Sp.Spec.post(td, g, sd, a),
          Sp.Spec.post(td, g, sd, b),
          Pm.Spec.post_valid(td, sd, g, a, gf, lt),
          Pm.Spec.post_valid(td, sd, g, b, gf, lt)),
        Vk.PSet.valid_union(sd, Sp.Spec.step(td, g, sd, a),
          Sp.Spec.step(td, g, sd, b),
          Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
          Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb)), lt,
        PSet.same_l(sd,
          Sp.Spec.post(td, g, sd, S.PSet.union(sd, a, b)),
          S.PSet.union(sd, Sp.Spec.post(td, g, sd, a),
            Sp.Spec.post(td, g, sd, b)),
          Spec.post_union(td, sd, g, a, b, gf, lt, va, vb)),
        Sa.PSet.subset_union(sd, Sp.Spec.post(td, g, sd, a),
          Sp.Spec.post(td, g, sd, b),
          S.PSet.union(sd, Sp.Spec.step(td, g, sd, a),
            Sp.Spec.step(td, g, sd, b)),
          Pm.Spec.post_valid(td, sd, g, a, gf, lt),
          Pm.Spec.post_valid(td, sd, g, b, gf, lt),
          Vk.PSet.valid_union(sd, Sp.Spec.step(td, g, sd, a),
            Sp.Spec.step(td, g, sd, b),
            Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
            Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb)), lt,
          Sa.PSet.subset_trans(sd, Sp.Spec.post(td, g, sd, a),
            Sp.Spec.step(td, g, sd, a),
            S.PSet.union(sd, Sp.Spec.step(td, g, sd, a),
              Sp.Spec.step(td, g, sd, b)),
            Pm.Spec.post_valid(td, sd, g, a, gf, lt),
            Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
            Vk.PSet.valid_union(sd, Sp.Spec.step(td, g, sd, a),
              Sp.Spec.step(td, g, sd, b),
              Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
              Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb)), lt,
            Spec.post_sub_step(td, sd, g, a, gf, lt, va),
            Lp.PSet.subset_union_l(sd, Sp.Spec.step(td, g, sd, a),
              Sp.Spec.step(td, g, sd, b),
              Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
              Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb), lt)),
          Sa.PSet.subset_trans(sd, Sp.Spec.post(td, g, sd, b),
            Sp.Spec.step(td, g, sd, b),
            S.PSet.union(sd, Sp.Spec.step(td, g, sd, a),
              Sp.Spec.step(td, g, sd, b)),
            Pm.Spec.post_valid(td, sd, g, b, gf, lt),
            Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb),
            Vk.PSet.valid_union(sd, Sp.Spec.step(td, g, sd, a),
              Sp.Spec.step(td, g, sd, b),
              Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
              Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb)), lt,
            Spec.post_sub_step(td, sd, g, b, gf, lt, vb),
            PSet.subset_union_r(sd, Sp.Spec.step(td, g, sd, a),
              Sp.Spec.step(td, g, sd, b),
              Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
              Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb), lt))))),
    Sa.PSet.subset_union(sd, Sp.Spec.step(td, g, sd, a),
      Sp.Spec.step(td, g, sd, b),
      Sp.Spec.step(td, g, sd, S.PSet.union(sd, a, b)),
      Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
      Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb),
      Lp.Spec.step_valid(td, sd, g, S.PSet.union(sd, a, b), gf, lt,
        Vk.PSet.valid_union(sd, a, b, va, vb)), lt,
      Spec.step_mono(td, sd, g, a, S.PSet.union(sd, a, b), gf, lt,
        va, Vk.PSet.valid_union(sd, a, b, va, vb),
        Lp.PSet.subset_union_l(sd, a, b, va, vb, lt)),
      Spec.step_mono(td, sd, g, b, S.PSet.union(sd, a, b), gf, lt,
        vb, Vk.PSet.valid_union(sd, a, b, va, vb),
        PSet.subset_union_r(sd, a, b, va, vb, lt))))

law Spec.iter_union:
  for +f: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +a: S.PSet
  for +b: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +va: {S.PSet.valid(sd, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(sd, b, True{}) == True{} : Bool}
  {PSet.same(sd, Sp.Spec.iter(f, td, g, sd, S.PSet.union(sd, a, b)),
    S.PSet.union(sd, Sp.Spec.iter(f, td, g, sd, a),
      Sp.Spec.iter(f, td, g, sd, b))) == True{} : Bool}

def Spec.iter_union(f, td, sd, g, a, b, gf, lt, va, vb):
  match f:
    case 0n:
      PSet.same_refl(sd, S.PSet.union(sd, a, b),
        Vk.PSet.valid_union(sd, a, b, va, vb), lt)
    case 1n+p:
      PSet.same_trans(sd,
        Sp.Spec.iter(p, td, g, sd,
          Sp.Spec.step(td, g, sd, S.PSet.union(sd, a, b))),
        Sp.Spec.iter(p, td, g, sd,
          S.PSet.union(sd, Sp.Spec.step(td, g, sd, a),
            Sp.Spec.step(td, g, sd, b))),
        S.PSet.union(sd,
          Sp.Spec.iter(p, td, g, sd, Sp.Spec.step(td, g, sd, a)),
          Sp.Spec.iter(p, td, g, sd, Sp.Spec.step(td, g, sd, b))),
        Lp.Spec.iter_valid(p, td, sd, g,
          Sp.Spec.step(td, g, sd, S.PSet.union(sd, a, b)), gf, lt,
          Lp.Spec.step_valid(td, sd, g, S.PSet.union(sd, a, b), gf,
            lt, Vk.PSet.valid_union(sd, a, b, va, vb))),
        Lp.Spec.iter_valid(p, td, sd, g,
          S.PSet.union(sd, Sp.Spec.step(td, g, sd, a),
            Sp.Spec.step(td, g, sd, b)), gf, lt,
          Vk.PSet.valid_union(sd, Sp.Spec.step(td, g, sd, a),
            Sp.Spec.step(td, g, sd, b),
            Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
            Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb))),
        Vk.PSet.valid_union(sd,
          Sp.Spec.iter(p, td, g, sd, Sp.Spec.step(td, g, sd, a)),
          Sp.Spec.iter(p, td, g, sd, Sp.Spec.step(td, g, sd, b)),
          Lp.Spec.iter_valid(p, td, sd, g,
            Sp.Spec.step(td, g, sd, a), gf, lt,
            Lp.Spec.step_valid(td, sd, g, a, gf, lt, va)),
          Lp.Spec.iter_valid(p, td, sd, g,
            Sp.Spec.step(td, g, sd, b), gf, lt,
            Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb))), lt,
        Spec.iter_same(p, td, sd, g,
          Sp.Spec.step(td, g, sd, S.PSet.union(sd, a, b)),
          S.PSet.union(sd, Sp.Spec.step(td, g, sd, a),
            Sp.Spec.step(td, g, sd, b)), gf, lt,
          Lp.Spec.step_valid(td, sd, g, S.PSet.union(sd, a, b), gf,
            lt, Vk.PSet.valid_union(sd, a, b, va, vb)),
          Vk.PSet.valid_union(sd, Sp.Spec.step(td, g, sd, a),
            Sp.Spec.step(td, g, sd, b),
            Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
            Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb)),
          Spec.step_union(td, sd, g, a, b, gf, lt, va, vb)),
        Spec.iter_union(p, td, sd, g, Sp.Spec.step(td, g, sd, a),
          Sp.Spec.step(td, g, sd, b), gf, lt,
          Lp.Spec.step_valid(td, sd, g, a, gf, lt, va),
          Lp.Spec.step_valid(td, sd, g, b, gf, lt, vb)))

law Spec.closure_union:
  for +n: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +va: {S.PSet.valid(sd, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(sd, b, True{}) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+sd) == True{} : Bool}
  {S.PSet.member(sd,
      Sp.Spec.closure(n, td, g, sd, S.PSet.union(sd, a, b)), x)
    == S.PSet.member(sd, S.PSet.union(sd,
         Sp.Spec.closure(n, td, g, sd, a),
         Sp.Spec.closure(n, td, g, sd, b)), x) : Bool}

def Spec.closure_union(n, td, sd, g, a, b, x, gf, lt, va, vb, inv):
  PSet.member_same(sd,
    Sp.Spec.closure(n, td, g, sd, S.PSet.union(sd, a, b)),
    S.PSet.union(sd, Sp.Spec.closure(n, td, g, sd, a),
      Sp.Spec.closure(n, td, g, sd, b)), x,
    Lp.Spec.closure_valid(n, td, sd, g, S.PSet.union(sd, a, b), gf,
      lt, Vk.PSet.valid_union(sd, a, b, va, vb)),
    Vk.PSet.valid_union(sd, Sp.Spec.closure(n, td, g, sd, a),
      Sp.Spec.closure(n, td, g, sd, b),
      Lp.Spec.closure_valid(n, td, sd, g, a, gf, lt, va),
      Lp.Spec.closure_valid(n, td, sd, g, b, gf, lt, vb)), lt, inv,
    Spec.iter_union(1n+n, td, sd, g, a, b, gf, lt, va, vb))
