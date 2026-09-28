# proofs/lfp.bend -- the closure iteration, as a growing chain.
#
# `Spec.closure` is `Spec.iter` with one more round than the universe has
# members, and each round is `x u post(x)`. Two facts about the chain follow
# from nothing but the set algebra and the monotonicity of `post`, and they
# are what the least-fixed-point characterisation is built out of:
#
#   * every round is a valid set, so the laws that need `PSet.valid` can be
#     applied at every round rather than only at the first;
#   * the chain only grows, so the closure contains its roots -- counted,
#     with `PSet.is_subset`, not just tested at one ordinal.
#
# The hypotheses are the ones the product establishes rather than assumes:
# the graph's successors are ordinals of the universe (`Store.succ` rejects a
# generation where they are not), the depth is the production depth or less,
# and the roots are a set that passed `PSet.valid`.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./shape.bend as Sh
import ./setops.bend as So
import ./subsetconv.bend as Sc
import ./subsetalg.bend as Sa
import ./validkeep.bend as Vk
import ./graphrange.bend as Gr
import ./postmono.bend as Pm
import ../core/count.bend as C
import ../core/set.bend as S
import ../closure/graph.bend as G
import ../spec/closure.bend as Sp

# ---------------------------------------------------------------------------
# Reflexivity.
# ---------------------------------------------------------------------------

law Ords.all_mem_self:
  for +l: List<&2, U32>
  for +d: Nat
  for +a: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l, S.PSet.to_list(d, a)) == True{} : Bool}
  {Sc.Ords.all_mem(l, d, a) == True{} : Bool}

def Ords.all_mem_self(l, d, a, va, lt, ai):
  match l:
    case Nil{}:
      {==}
    case Con{y, t}:
      E.Bool.and_both(S.PSet.member(d, a, y),
        Sc.Ords.all_mem(t, d, a),
        Sa.PSet.member_of_to_list(d, a, y, va, lt,
          E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(d, a), y),
            Sa.Ords.all_in(t, S.PSet.to_list(d, a)), ai)),
        Ords.all_mem_self(t, d, a, va, lt,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(d, a), y),
            Sa.Ords.all_in(t, S.PSet.to_list(d, a)), ai)))

law PSet.subset_refl:
  for +d: Nat
  for +a: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {S.PSet.is_subset(d, a, a) == True{} : Bool}

def PSet.subset_refl(d, a, va, lt):
  Sc.PSet.subset_of_members(d, a, a, va, va, lt,
    Ords.all_mem_self(S.PSet.to_list(d, a), d, a, va, lt,
      Sa.Ords.all_in_self(S.PSet.to_list(d, a))))

# ---------------------------------------------------------------------------
# A set is inside any union it is an operand of.
# ---------------------------------------------------------------------------

def PSet.member_left(+d: Nat, +a: S.PSet, +b: S.PSet, +y: U32,
  +va: {S.PSet.valid(d, a, True{}) == True{} : Bool},
  +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +inv: {Dc.U32.hi_zero(y, 12n+d) == True{} : Bool},
  +ma: {S.PSet.member(d, a, y) == True{} : Bool})
  -> {S.PSet.member(d, S.PSet.union(d, a, b), y) == True{} : Bool}:
  %E.Bool.sym(S.PSet.member(d, S.PSet.union(d, a, b), y),
    Bool.or(S.PSet.member(d, a, y), S.PSet.member(d, b, y)),
    So.PSet.union_pointwise(d, a, b, S.PSet.half(d), y, {==}, lt,
      Sh.PSet.valid_wf(d, a, va), Sh.PSet.valid_wf(d, b, vb), inv,
      U32.is_lt(y, S.PSet.half(d)), {==})) : {_ == True{} : Bool}
  Sa.Ords.or_left(S.PSet.member(d, a, y), S.PSet.member(d, b, y), ma)

law Ords.all_mem_left:
  for +l: List<&2, U32>
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l, S.PSet.to_list(d, a)) == True{} : Bool}
  {Sc.Ords.all_mem(l, d, S.PSet.union(d, a, b)) == True{} : Bool}

def Ords.all_mem_left(l, d, a, b, va, vb, lt, ai):
  match l:
    case Nil{}:
      {==}
    case Con{y, t}:
      E.Bool.and_both(S.PSet.member(d, S.PSet.union(d, a, b), y),
        Sc.Ords.all_mem(t, d, S.PSet.union(d, a, b)),
        PSet.member_left(d, a, b, y, va, vb, lt,
          Sa.PSet.in_range_of_to_list(d, a, y, va, lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(d, a), y),
              Sa.Ords.all_in(t, S.PSet.to_list(d, a)), ai)),
          Sa.PSet.member_of_to_list(d, a, y, va, lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(d, a), y),
              Sa.Ords.all_in(t, S.PSet.to_list(d, a)), ai))),
        Ords.all_mem_left(t, d, a, b, va, vb, lt,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(d, a), y),
            Sa.Ords.all_in(t, S.PSet.to_list(d, a)), ai)))

law PSet.subset_union_l:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  {S.PSet.is_subset(d, a, S.PSet.union(d, a, b)) == True{} : Bool}

def PSet.subset_union_l(d, a, b, va, vb, lt):
  Sc.PSet.subset_of_members(d, a, S.PSet.union(d, a, b), va,
    Vk.PSet.valid_union(d, a, b, va, vb), lt,
    Ords.all_mem_left(S.PSet.to_list(d, a), d, a, b, va, vb, lt,
      Sa.Ords.all_in_self(S.PSet.to_list(d, a))))

# ---------------------------------------------------------------------------
# Every round is a valid set.
# ---------------------------------------------------------------------------

law Spec.step_valid:
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +x: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool}
  {S.PSet.valid(sd, Sp.Spec.step(td, g, sd, x), True{}) == True{}
    : Bool}

def Spec.step_valid(td, sd, g, x, gf, lt, vx):
  Vk.PSet.valid_union(sd, x, Sp.Spec.post(td, g, sd, x), vx,
    Pm.Spec.post_valid(td, sd, g, x, gf, lt))

law Spec.iter_valid:
  for +f: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +x: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool}
  {S.PSet.valid(sd, Sp.Spec.iter(f, td, g, sd, x), True{}) == True{}
    : Bool}

def Spec.iter_valid(f, td, sd, g, x, gf, lt, vx):
  match f:
    case 0n:
      vx
    case 1n+p:
      Spec.iter_valid(p, td, sd, g, Sp.Spec.step(td, g, sd, x), gf,
        lt, Spec.step_valid(td, sd, g, x, gf, lt, vx))

# ---------------------------------------------------------------------------
# The chain only grows.
# ---------------------------------------------------------------------------

law Spec.iter_grows:
  for +f: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +x: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool}
  {S.PSet.is_subset(sd, x, Sp.Spec.iter(f, td, g, sd, x)) == True{}
    : Bool}

def Spec.iter_grows(f, td, sd, g, x, gf, lt, vx):
  match f:
    case 0n:
      PSet.subset_refl(sd, x, vx, lt)
    case 1n+p:
      Sa.PSet.subset_trans(sd, x, Sp.Spec.step(td, g, sd, x),
        Sp.Spec.iter(p, td, g, sd, Sp.Spec.step(td, g, sd, x)), vx,
        Spec.step_valid(td, sd, g, x, gf, lt, vx),
        Spec.iter_valid(p, td, sd, g, Sp.Spec.step(td, g, sd, x), gf,
          lt, Spec.step_valid(td, sd, g, x, gf, lt, vx)), lt,
        PSet.subset_union_l(sd, x, Sp.Spec.post(td, g, sd, x), vx,
          Pm.Spec.post_valid(td, sd, g, x, gf, lt), lt),
        Spec.iter_grows(p, td, sd, g, Sp.Spec.step(td, g, sd, x), gf,
          lt, Spec.step_valid(td, sd, g, x, gf, lt, vx)))

law Spec.closure_valid:
  for +n: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +r: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vr: {S.PSet.valid(sd, r, True{}) == True{} : Bool}
  {S.PSet.valid(sd, Sp.Spec.closure(n, td, g, sd, r), True{})
    == True{} : Bool}

def Spec.closure_valid(n, td, sd, g, r, gf, lt, vr):
  Spec.iter_valid(1n+n, td, sd, g, r, gf, lt, vr)

law Spec.closure_contains_roots:
  for +n: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +r: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vr: {S.PSet.valid(sd, r, True{}) == True{} : Bool}
  {S.PSet.is_subset(sd, r, Sp.Spec.closure(n, td, g, sd, r))
    == True{} : Bool}

def Spec.closure_contains_roots(n, td, sd, g, r, gf, lt, vr):
  Spec.iter_grows(1n+n, td, sd, g, r, gf, lt, vr)

# ---------------------------------------------------------------------------
# Leastness: the chain never leaves an edge-closed set that holds the roots.
# ---------------------------------------------------------------------------

law Spec.post_inside:
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +r: S.PSet
  for +xx: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vr: {S.PSet.valid(sd, r, True{}) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, xx, True{}) == True{} : Bool}
  for +cl: {Sp.Spec.closed(td, g, sd, xx) == True{} : Bool}
  for +rx: {S.PSet.is_subset(sd, r, xx) == True{} : Bool}
  {S.PSet.is_subset(sd, Sp.Spec.post(td, g, sd, r), xx) == True{}
    : Bool}

def Spec.post_inside(td, sd, g, r, xx, gf, lt, vr, vx, cl, rx):
  Sa.PSet.subset_trans(sd, Sp.Spec.post(td, g, sd, r),
    Sp.Spec.post(td, g, sd, xx), xx,
    Pm.Spec.post_valid(td, sd, g, r, gf, lt),
    Pm.Spec.post_valid(td, sd, g, xx, gf, lt), vx, lt,
    Pm.Spec.post_mono(td, sd, g, r, xx, gf, lt, vr, vx, rx), cl)

law Spec.step_inside:
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +r: S.PSet
  for +xx: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vr: {S.PSet.valid(sd, r, True{}) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, xx, True{}) == True{} : Bool}
  for +cl: {Sp.Spec.closed(td, g, sd, xx) == True{} : Bool}
  for +rx: {S.PSet.is_subset(sd, r, xx) == True{} : Bool}
  {S.PSet.is_subset(sd, Sp.Spec.step(td, g, sd, r), xx) == True{}
    : Bool}

def Spec.step_inside(td, sd, g, r, xx, gf, lt, vr, vx, cl, rx):
  Sa.PSet.subset_union(sd, r, Sp.Spec.post(td, g, sd, r), xx, vr,
    Pm.Spec.post_valid(td, sd, g, r, gf, lt), vx, lt, rx,
    Spec.post_inside(td, sd, g, r, xx, gf, lt, vr, vx, cl, rx))

law Spec.iter_least:
  for +f: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +r: S.PSet
  for +xx: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vr: {S.PSet.valid(sd, r, True{}) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, xx, True{}) == True{} : Bool}
  for +cl: {Sp.Spec.closed(td, g, sd, xx) == True{} : Bool}
  for +rx: {S.PSet.is_subset(sd, r, xx) == True{} : Bool}
  {S.PSet.is_subset(sd, Sp.Spec.iter(f, td, g, sd, r), xx) == True{}
    : Bool}

def Spec.iter_least(f, td, sd, g, r, xx, gf, lt, vr, vx, cl, rx):
  match f:
    case 0n:
      rx
    case 1n+p:
      Spec.iter_least(p, td, sd, g, Sp.Spec.step(td, g, sd, r), xx,
        gf, lt, Spec.step_valid(td, sd, g, r, gf, lt, vr), vx, cl,
        Spec.step_inside(td, sd, g, r, xx, gf, lt, vr, vx, cl, rx))

law Spec.closure_least:
  for +n: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +r: S.PSet
  for +xx: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vr: {S.PSet.valid(sd, r, True{}) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, xx, True{}) == True{} : Bool}
  for +cl: {Sp.Spec.closed(td, g, sd, xx) == True{} : Bool}
  for +rx: {S.PSet.is_subset(sd, r, xx) == True{} : Bool}
  {S.PSet.is_subset(sd, Sp.Spec.closure(n, td, g, sd, r), xx)
    == True{} : Bool}

def Spec.closure_least(n, td, sd, g, r, xx, gf, lt, vr, vx, cl, rx):
  Spec.iter_least(1n+n, td, sd, g, r, xx, gf, lt, vr, vx, cl, rx)
