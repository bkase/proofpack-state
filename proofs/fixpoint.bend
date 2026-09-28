# proofs/fixpoint.bend -- what the fixed point gives.
#
# With `Spec.closure_is_closed` the specification closure is an actual fixed
# point, not just a chain that has run for a while. Three things follow that
# the release states as laws: the answer is edge-closed at every edge, not
# just as a counted subset; closing it again changes nothing; and together
# with extensivity and leastness it is *the* least edge-closed set containing
# the roots.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./shift.bend as Sf
import ./graphrange.bend as Gr
import ./subsetconv.bend as Sc
import ./subsetalg.bend as Sa
import ./postmono.bend as Pm
import ./lfp.bend as Lp
import ./closalg.bend as Ca
import ./settle.bend as St
import ../core/count.bend as C
import ../core/set.bend as S
import ../closure/graph.bend as G
import ../spec/closure.bend as Sp

law Ords.fit_of_contains:
  for +l: List<&2, U32>
  for +k: Nat
  for +y: U32
  for +fl: {Sf.Ords.all_fit(l, k) == True{} : Bool}
  for c: {List.contains(~U32, ~U32.is_eq, l, y) == True{} : Bool}
  {Dc.U32.hi_zero(y, k) == True{} : Bool}

def Ords.fit_of_contains.pick(+u: List<&2, U32>, +k: Nat, +y: U32,
  +z: U32, +e: Bool, +ee: {e == U32.is_eq(z, y) : Bool},
  +fz: {Dc.U32.hi_zero(z, k) == True{} : Bool},
  ih: {List.contains(~U32, ~U32.is_eq, u, y) == True{} : Bool} ->
    {Dc.U32.hi_zero(y, k) == True{} : Bool},
  +c: {List.contains(~U32, ~U32.is_eq, Con{z, u}, y) == True{}
    : Bool})
  -> {Dc.U32.hi_zero(y, k) == True{} : Bool}:
  match e:
    case True{}:
      %E.U32.eq_reflect(z, y,
        E.Bool.sym(True{}, U32.is_eq(z, y), ee))
        : {Dc.U32.hi_zero(_, k) == True{} : Bool}
      fz
    case False{}:
      ih(Sc.Ords.contains_tail(z, u, y, ee, c))

def Ords.fit_of_contains(l, k, y, fl, c):
  match l:
    case Nil{}:
      E.Bool.noconf({Dc.U32.hi_zero(y, k) == True{} : Bool}, c)
    case Con{z, u}:
      Ords.fit_of_contains.pick(u, k, y, z, U32.is_eq(z, y), {==},
        E.Bool.and_l(Dc.U32.hi_zero(z, k), Sf.Ords.all_fit(u, k), fl),
        Ords.fit_of_contains(u, k, y,
          E.Bool.and_r(Dc.U32.hi_zero(z, k), Sf.Ords.all_fit(u, k),
            fl)), c)

law Spec.closure_edge:
  for +n: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +r: S.PSet
  for +u: U32
  for +v: U32
  for +uu: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +su: {Gr.Graph.succs_in(sd, uu, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vu: {S.PSet.valid(sd, uu, True{}) == True{} : Bool}
  for +vr: {S.PSet.valid(sd, r, True{}) == True{} : Bool}
  for +ru: {S.PSet.is_subset(sd, r, uu) == True{} : Bool}
  for +invu: {Dc.U32.hi_zero(u, 12n+sd) == True{} : Bool}
  for +fuel: {C.Nat.upto(S.PSet.count(sd, uu, S.PSet.half(sd)),
    1n+n) == True{} : Bool}
  for +mu: {S.PSet.member(sd, Sp.Spec.closure(n, td, g, sd, r), u)
    == True{} : Bool}
  for +e: {G.Graph.edge(td, g, u, v) == True{} : Bool}
  {S.PSet.member(sd, Sp.Spec.closure(n, td, g, sd, r), v)
    == True{} : Bool}

def Spec.closure_edge.fits(+td: Nat, +sd: Nat, +g: G.Graph(),
  +u: U32, +v: U32,
  +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool},
  +e: {G.Graph.edge(td, g, u, v) == True{} : Bool})
  -> {Dc.U32.hi_zero(v, 12n+sd) == True{} : Bool}:
  Ords.fit_of_contains(G.Graph.succ(td, g, u), 12n+sd, v,
    Gr.Graph.succ_fits(td, sd, g, u, gf), e)

def Spec.closure_edge(n, td, sd, g, r, u, v, uu, gf, su, lt, vu, vr,
  ru, invu, fuel, mu, e):
  Sa.PSet.subset_member_at(sd,
    Sp.Spec.post(td, g, sd, Sp.Spec.closure(n, td, g, sd, r)),
    Sp.Spec.closure(n, td, g, sd, r), v,
    Pm.Spec.post_valid(td, sd, g,
      Sp.Spec.closure(n, td, g, sd, r), gf, lt),
    Lp.Spec.closure_valid(n, td, sd, g, r, gf, lt, vr), lt,
    Spec.closure_edge.fits(td, sd, g, u, v, gf, e),
    St.Spec.closure_is_closed(n, td, sd, g, uu, r, gf, su, lt, vu,
      vr, ru, fuel),
    Pm.Spec.post_of_any(td, sd, g,
      Sp.Spec.closure(n, td, g, sd, r), v, lt,
      Spec.closure_edge.fits(td, sd, g, u, v, gf, e),
      Gr.Graph.any_succ_of_member(
        S.PSet.to_list(sd, Sp.Spec.closure(n, td, g, sd, r)), td,
        g, u, v,
        Sc.Ords.head_eq(
          S.PSet.to_list(sd, Sp.Spec.closure(n, td, g, sd, r)), u),
        {==},
        Pm.Ords.in_of_member(sd,
          Sp.Spec.closure(n, td, g, sd, r), u,
          Lp.Spec.closure_valid(n, td, sd, g, r, gf, lt, vr),
          lt, invu, mu), e)))

law Spec.closure_idem:
  for +n: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +r: S.PSet
  for +x: U32
  for +uu: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +su: {Gr.Graph.succs_in(sd, uu, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vu: {S.PSet.valid(sd, uu, True{}) == True{} : Bool}
  for +vr: {S.PSet.valid(sd, r, True{}) == True{} : Bool}
  for +ru: {S.PSet.is_subset(sd, r, uu) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+sd) == True{} : Bool}
  for +fuel: {C.Nat.upto(S.PSet.count(sd, uu, S.PSet.half(sd)),
    1n+n) == True{} : Bool}
  {S.PSet.member(sd, Sp.Spec.closure(n, td, g, sd,
      Sp.Spec.closure(n, td, g, sd, r)), x)
    == S.PSet.member(sd, Sp.Spec.closure(n, td, g, sd, r), x) : Bool}

def Spec.closure_idem(n, td, sd, g, r, x, uu, gf, su, lt, vu, vr, ru,
  inv, fuel):
  Ca.PSet.member_same(sd,
    Sp.Spec.closure(n, td, g, sd, Sp.Spec.closure(n, td, g, sd, r)),
    Sp.Spec.closure(n, td, g, sd, r), x,
    Lp.Spec.closure_valid(n, td, sd, g,
      Sp.Spec.closure(n, td, g, sd, r), gf, lt,
      Lp.Spec.closure_valid(n, td, sd, g, r, gf, lt, vr)),
    Lp.Spec.closure_valid(n, td, sd, g, r, gf, lt, vr), lt, inv,
    E.Bool.and_both(
      S.PSet.is_subset(sd, Sp.Spec.closure(n, td, g, sd,
        Sp.Spec.closure(n, td, g, sd, r)),
        Sp.Spec.closure(n, td, g, sd, r)),
      S.PSet.is_subset(sd, Sp.Spec.closure(n, td, g, sd, r),
        Sp.Spec.closure(n, td, g, sd,
          Sp.Spec.closure(n, td, g, sd, r))),
      Lp.Spec.closure_least(n, td, sd, g,
        Sp.Spec.closure(n, td, g, sd, r),
        Sp.Spec.closure(n, td, g, sd, r), gf, lt,
        Lp.Spec.closure_valid(n, td, sd, g, r, gf, lt, vr),
        Lp.Spec.closure_valid(n, td, sd, g, r, gf, lt, vr),
        St.Spec.closure_is_closed(n, td, sd, g, uu, r, gf, su, lt,
          vu, vr, ru, fuel),
        Lp.PSet.subset_refl(sd, Sp.Spec.closure(n, td, g, sd, r),
          Lp.Spec.closure_valid(n, td, sd, g, r, gf, lt, vr), lt)),
      Lp.Spec.closure_contains_roots(n, td, sd, g,
        Sp.Spec.closure(n, td, g, sd, r), gf, lt,
        Lp.Spec.closure_valid(n, td, sd, g, r, gf, lt, vr))))
