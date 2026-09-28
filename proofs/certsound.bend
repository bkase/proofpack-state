# proofs/certsound.bend -- an accepted certificate is an exact closure
# (law C-04).
#
# SPEC 4.4's four conditions split into two halves, and each half gives one
# inclusion.
#
# Conditions 1 and 2 -- the roots are inside `c`, and `c` is edge-closed --
# make `c` an edge-closed set containing the roots, and the closure is the
# least such set. So the closure is inside `c`.
#
# Condition 3 -- every member of a level has a predecessor in the level
# before, and level 0 is inside the roots -- walks the other way. Level 0 is
# inside the closure because the closure contains the roots; every later
# level is inside it because the closure is edge-closed and each member is one
# edge from the level before. The levels' union is `c`, so `c` is inside the
# closure.
#
# That is why acceptance proves exactness rather than an overapproximation,
# and why a cached or externally produced answer can be reused without
# trusting how it was computed.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./shift.bend as Sf
import ./subsetconv.bend as Sc
import ./subsetalg.bend as Sa
import ./listset.bend as Ls
import ./insertvalid.bend as Iv
import ./graphrange.bend as Gr
import ./postmono.bend as Pm
import ./lfp.bend as Lp
import ./closalg.bend as Ca
import ./settle.bend as St
import ./fixpoint.bend as Fx
import ./traversal.bend as Tl
import ../core/count.bend as C
import ../core/set.bend as S
import ../closure/graph.bend as G
import ../closure/reach.bend as R
import ../closure/explain.bend as Ex
import ../closure/cert.bend as Ct
import ../spec/closure.bend as Sp

def Cert.levels_fit(+levels: R.Levels, +k: Nat) -> Bool:
  match levels:
    case Nil{}:
      True{}
    case Con{l, t}:
      Bool.and(Sf.Ords.all_fit(l, k), Cert.levels_fit(t, k))

law Ords.all_mem_append:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +sd: Nat
  for +xx: S.PSet
  for +am: {Sc.Ords.all_mem(a, sd, xx) == True{} : Bool}
  for +bm: {Sc.Ords.all_mem(b, sd, xx) == True{} : Bool}
  {Sc.Ords.all_mem(List.append(&2, U32, a, b), sd, xx) == True{}
    : Bool}

def Ords.all_mem_append(a, b, sd, xx, am, bm):
  match a:
    case Nil{}:
      bm
    case Con{y, u}:
      E.Bool.and_both(S.PSet.member(sd, xx, y),
        Sc.Ords.all_mem(List.append(&2, U32, u, b), sd, xx),
        E.Bool.and_l(S.PSet.member(sd, xx, y),
          Sc.Ords.all_mem(u, sd, xx), am),
        Ords.all_mem_append(u, b, sd, xx,
          E.Bool.and_r(S.PSet.member(sd, xx, y),
            Sc.Ords.all_mem(u, sd, xx), am), bm))

# ---------------------------------------------------------------------------
# Condition 3, one vertex.
# ---------------------------------------------------------------------------

law Cert.pred_inside:
  for +cands: List<&2, U32>
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +xx: S.PSet
  for +target: U32
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, xx, True{}) == True{} : Bool}
  for +cl: {Sp.Spec.closed(td, g, sd, xx) == True{} : Bool}
  for +cin: {Sc.Ords.all_mem(cands, sd, xx) == True{} : Bool}
  for +cfit: {Sf.Ords.all_fit(cands, 12n+sd) == True{} : Bool}
  for sm: {Ct.Cert.some(Ex.Explain.pred(td, g, cands, target,
    None{})) == True{} : Bool}
  {S.PSet.member(sd, xx, target) == True{} : Bool}

def Cert.pred_inside.pick(+t: List<&2, U32>, +td: Nat, +sd: Nat,
  +g: G.Graph(), +xx: S.PSet, +target: U32, +u: U32, +e: Bool,
  +ee: {e == G.Graph.edge(td, g, u, target) : Bool},
  +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +vx: {S.PSet.valid(sd, xx, True{}) == True{} : Bool},
  +cl: {Sp.Spec.closed(td, g, sd, xx) == True{} : Bool},
  +mu: {S.PSet.member(sd, xx, u) == True{} : Bool},
  +invu: {Dc.U32.hi_zero(u, 12n+sd) == True{} : Bool},
  ih: {Ct.Cert.some(Ex.Explain.pred(td, g, t, target, None{}))
    == True{} : Bool} ->
    {S.PSet.member(sd, xx, target) == True{} : Bool},
  sm: {Ct.Cert.some(Ex.Explain.pred(td, g, t, target,
    Ex.Explain.opt(u, e))) == True{} : Bool})
  -> {S.PSet.member(sd, xx, target) == True{} : Bool}:
  match e:
    case True{}:
      E.Bool.and_l(S.PSet.member(sd, xx, target),
        Sc.Ords.all_mem(Nil{}, sd, xx),
        Tl.Ords.succ_inside(Con{target, Nil{}}, td, sd, g, xx, u, gf,
          lt, vx, cl, mu, invu,
          E.Bool.and_both(List.contains(~U32, ~U32.is_eq,
            G.Graph.succ(td, g, u), target),
            Sa.Ords.all_in(Nil{}, G.Graph.succ(td, g, u)),
            E.Bool.sym(True{}, G.Graph.edge(td, g, u, target), ee),
            {==})))
    case False{}:
      ih(sm)

def Cert.pred_inside(cands, td, sd, g, xx, target, gf, lt, vx, cl,
  cin, cfit, sm):
  match cands:
    case Nil{}:
      E.Bool.noconf({S.PSet.member(sd, xx, target) == True{} : Bool},
        sm)
    case Con{u, t}:
      Cert.pred_inside.pick(t, td, sd, g, xx, target, u,
        G.Graph.edge(td, g, u, target), {==}, gf, lt, vx, cl,
        E.Bool.and_l(S.PSet.member(sd, xx, u),
          Sc.Ords.all_mem(t, sd, xx), cin),
        E.Bool.and_l(Dc.U32.hi_zero(u, 12n+sd),
          Sf.Ords.all_fit(t, 12n+sd), cfit),
        Cert.pred_inside(t, td, sd, g, xx, target, gf, lt, vx, cl,
          E.Bool.and_r(S.PSet.member(sd, xx, u),
            Sc.Ords.all_mem(t, sd, xx), cin),
          E.Bool.and_r(Dc.U32.hi_zero(u, 12n+sd),
            Sf.Ords.all_fit(t, 12n+sd), cfit)), sm)

# ---------------------------------------------------------------------------
# Condition 3, one level and then all of them.
# ---------------------------------------------------------------------------

law Cert.preds_acc:
  for +cur: List<&2, U32>
  for +td: Nat
  for +g: G.Graph()
  for +prev: List<&2, U32>
  for +ok: Bool
  for +v: {Ct.Cert.preds_ok(td, g, prev, cur, ok) == True{} : Bool}
  {ok == True{} : Bool}

def Cert.preds_acc(cur, td, g, prev, ok, v):
  match cur:
    case Nil{}:
      v
    case Con{x, t}:
      match ok:
        case False{}:
          E.Bool.noconf({False{} == True{} : Bool}, v)
        case True{}:
          {==}

law Cert.layers_acc:
  for +levels: R.Levels
  for +td: Nat
  for +g: G.Graph()
  for +prev: List<&2, U32>
  for +ok: Bool
  for +v: {Ct.Cert.layers_ok(td, g, levels, prev, ok) == True{}
    : Bool}
  {ok == True{} : Bool}

def Cert.layers_acc(levels, td, g, prev, ok, v):
  match levels:
    case Nil{}:
      v
    case Con{l, t}:
      match ok:
        case False{}:
          E.Bool.noconf({False{} == True{} : Bool}, v)
        case True{}:
          {==}

law Cert.preds_inside:
  for +cur: List<&2, U32>
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +xx: S.PSet
  for +prev: List<&2, U32>
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, xx, True{}) == True{} : Bool}
  for +cl: {Sp.Spec.closed(td, g, sd, xx) == True{} : Bool}
  for +pin: {Sc.Ords.all_mem(prev, sd, xx) == True{} : Bool}
  for +pfit: {Sf.Ords.all_fit(prev, 12n+sd) == True{} : Bool}
  for +pok: {Ct.Cert.preds_ok(td, g, prev, cur, True{}) == True{}
    : Bool}
  {Sc.Ords.all_mem(cur, sd, xx) == True{} : Bool}

def Cert.preds_inside(cur, td, sd, g, xx, prev, gf, lt, vx, cl, pin,
  pfit, pok):
  match cur:
    case Nil{}:
      {==}
    case Con{v, t}:
      E.Bool.and_both(S.PSet.member(sd, xx, v),
        Sc.Ords.all_mem(t, sd, xx),
        Cert.pred_inside(prev, td, sd, g, xx, v, gf, lt, vx, cl, pin,
          pfit,
          Cert.preds_acc(t, td, g, prev,
            Ct.Cert.has_pred(td, g, prev, v), pok)),
        Cert.preds_inside(t, td, sd, g, xx, prev, gf, lt, vx, cl,
          pin, pfit,
          %Cert.preds_acc(t, td, g, prev,
            Ct.Cert.has_pred(td, g, prev, v), pok)
            : {Ct.Cert.preds_ok(td, g, prev, t, _) == True{} : Bool}
          pok))

law Cert.layers_inside:
  for +levels: R.Levels
  for +acc: List<&2, U32>
  for +prev: List<&2, U32>
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +xx: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, xx, True{}) == True{} : Bool}
  for +cl: {Sp.Spec.closed(td, g, sd, xx) == True{} : Bool}
  for +pin: {Sc.Ords.all_mem(prev, sd, xx) == True{} : Bool}
  for +pfit: {Sf.Ords.all_fit(prev, 12n+sd) == True{} : Bool}
  for +ain: {Sc.Ords.all_mem(acc, sd, xx) == True{} : Bool}
  for +lfit: {Cert.levels_fit(levels, 12n+sd) == True{} : Bool}
  for +lok: {Ct.Cert.layers_ok(td, g, levels, prev, True{})
    == True{} : Bool}
  {Sc.Ords.all_mem(Ct.Cert.concat(levels, acc), sd, xx) == True{}
    : Bool}

def Cert.layers_inside(levels, acc, prev, td, sd, g, xx, gf, lt, vx,
  cl, pin, pfit, ain, lfit, lok):
  match levels:
    case Nil{}:
      ain
    case Con{l, t}:
      Cert.layers_inside(t, List.append(&2, U32, l, acc), l, td, sd,
        g, xx, gf, lt, vx, cl,
        Cert.preds_inside(l, td, sd, g, xx, prev, gf, lt, vx, cl,
          pin, pfit,
          Cert.layers_acc(t, td, g, l,
            Ct.Cert.preds_ok(td, g, prev, l, True{}), lok)),
        E.Bool.and_l(Sf.Ords.all_fit(l, 12n+sd),
          Cert.levels_fit(t, 12n+sd), lfit),
        Ords.all_mem_append(l, acc, sd, xx,
          Cert.preds_inside(l, td, sd, g, xx, prev, gf, lt, vx, cl,
            pin, pfit,
            Cert.layers_acc(t, td, g, l,
              Ct.Cert.preds_ok(td, g, prev, l, True{}), lok)), ain),
        E.Bool.and_r(Sf.Ords.all_fit(l, 12n+sd),
          Cert.levels_fit(t, 12n+sd), lfit),
        %Cert.layers_acc(t, td, g, l,
          Ct.Cert.preds_ok(td, g, prev, l, True{}), lok)
          : {Ct.Cert.layers_ok(td, g, t, l, _) == True{} : Bool}
        lok)

law Cert.concat_fit:
  for +levels: R.Levels
  for +acc: List<&2, U32>
  for +k: Nat
  for +lfit: {Cert.levels_fit(levels, k) == True{} : Bool}
  for +afit: {Sf.Ords.all_fit(acc, k) == True{} : Bool}
  {Sf.Ords.all_fit(Ct.Cert.concat(levels, acc), k) == True{} : Bool}

def Cert.concat_fit(levels, acc, k, lfit, afit):
  match levels:
    case Nil{}:
      afit
    case Con{l, t}:
      Cert.concat_fit(t, List.append(&2, U32, l, acc), k,
        E.Bool.and_r(Sf.Ords.all_fit(l, k), Cert.levels_fit(t, k),
          lfit),
        Gr.Ords.all_fit_append(l, acc, k,
          E.Bool.and_l(Sf.Ords.all_fit(l, k), Cert.levels_fit(t, k),
            lfit), afit))

law Ords.all_mem_of_from_list:
  for +l2: List<&2, U32>
  for +l: List<&2, U32>
  for +sd: Nat
  for +xx: S.PSet
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +lfit: {Sf.Ords.all_fit(l, 12n+sd) == True{} : Bool}
  for +am: {Sc.Ords.all_mem(l, sd, xx) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l2,
    S.PSet.to_list(sd, S.PSet.from_list(sd, l))) == True{} : Bool}
  {Sc.Ords.all_mem(l2, sd, xx) == True{} : Bool}

def Ords.all_mem_of_from_list(l2, l, sd, xx, lt, lfit, am, ai):
  match l2:
    case Nil{}:
      {==}
    case Con{u, rest}:
      E.Bool.and_both(S.PSet.member(sd, xx, u),
        Sc.Ords.all_mem(rest, sd, xx),
        Sc.Ords.all_mem_at(l, sd, xx, u, Sc.Ords.head_eq(l, u),
          {==}, am,
          Ls.PSet.from_list_only_at(l, sd, u, lt,
            Sa.PSet.in_range_of_to_list(sd, S.PSet.from_list(sd, l),
              u, Iv.PSet.valid_from_list(l, sd, lt, lfit), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(sd, S.PSet.from_list(sd, l)), u),
                Sa.Ords.all_in(rest, S.PSet.to_list(sd,
                  S.PSet.from_list(sd, l))), ai)), lfit,
            Sa.PSet.member_of_to_list(sd, S.PSet.from_list(sd, l), u,
              Iv.PSet.valid_from_list(l, sd, lt, lfit), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(sd, S.PSet.from_list(sd, l)), u),
                Sa.Ords.all_in(rest, S.PSet.to_list(sd,
                  S.PSet.from_list(sd, l))), ai)))),
        Ords.all_mem_of_from_list(rest, l, sd, xx, lt, lfit, am,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(sd, S.PSet.from_list(sd, l)), u),
            Sa.Ords.all_in(rest, S.PSet.to_list(sd,
              S.PSet.from_list(sd, l))), ai)))

law PSet.subset_of_list_mem:
  for +l: List<&2, U32>
  for +sd: Nat
  for +xx: S.PSet
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +lfit: {Sf.Ords.all_fit(l, 12n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, xx, True{}) == True{} : Bool}
  for +am: {Sc.Ords.all_mem(l, sd, xx) == True{} : Bool}
  {S.PSet.is_subset(sd, S.PSet.from_list(sd, l), xx) == True{}
    : Bool}

def PSet.subset_of_list_mem(l, sd, xx, lt, lfit, vx, am):
  Sc.PSet.subset_of_members(sd, S.PSet.from_list(sd, l), xx,
    Iv.PSet.valid_from_list(l, sd, lt, lfit), vx, lt,
    Ords.all_mem_of_from_list(
      S.PSet.to_list(sd, S.PSet.from_list(sd, l)), l, sd, xx, lt,
      lfit, am,
      Sa.Ords.all_in_self(
        S.PSet.to_list(sd, S.PSet.from_list(sd, l)))))

# ---------------------------------------------------------------------------
# The union of the levels is inside the closure.
# ---------------------------------------------------------------------------

law Cert.concat_inside:
  for +levels: R.Levels
  for +roots: List<&2, U32>
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +xx: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, xx, True{}) == True{} : Bool}
  for +cl: {Sp.Spec.closed(td, g, sd, xx) == True{} : Bool}
  for +rfit: {Sf.Ords.all_fit(roots, 12n+sd) == True{} : Bool}
  for +lfit: {Cert.levels_fit(levels, 12n+sd) == True{} : Bool}
  for +z0: {S.PSet.is_subset(sd,
    S.PSet.from_list(sd, Ct.Cert.first(levels, roots)), xx)
    == True{} : Bool}
  for +lok: {Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
    Ct.Cert.first(levels, roots), True{}) == True{} : Bool}
  {Sc.Ords.all_mem(Ct.Cert.concat(levels, Nil{}), sd, xx) == True{}
    : Bool}

def Cert.concat_inside(levels, roots, td, sd, g, xx, gf, lt, vx, cl,
  rfit, lfit, z0, lok):
  match levels:
    case Nil{}:
      {==}
    case Con{l0, t}:
      Cert.layers_inside(t, List.append(&2, U32, l0, Nil{}), l0, td,
        sd, g, xx, gf, lt, vx, cl,
        Tl.Ords.all_mem_roots(l0, sd, xx, l0, lt,
          E.Bool.and_l(Sf.Ords.all_fit(l0, 12n+sd),
            Cert.levels_fit(t, 12n+sd), lfit), vx, z0,
          Sa.Ords.all_in_self(l0)),
        E.Bool.and_l(Sf.Ords.all_fit(l0, 12n+sd),
          Cert.levels_fit(t, 12n+sd), lfit),
        Ords.all_mem_append(l0, Nil{}, sd, xx,
          Tl.Ords.all_mem_roots(l0, sd, xx, l0, lt,
            E.Bool.and_l(Sf.Ords.all_fit(l0, 12n+sd),
              Cert.levels_fit(t, 12n+sd), lfit), vx, z0,
            Sa.Ords.all_in_self(l0)), {==}),
        E.Bool.and_r(Sf.Ords.all_fit(l0, 12n+sd),
          Cert.levels_fit(t, 12n+sd), lfit), lok)

law Cert.first_fit:
  for +levels: R.Levels
  for +roots: List<&2, U32>
  for +k: Nat
  for +lfit: {Cert.levels_fit(levels, k) == True{} : Bool}
  for +rfit: {Sf.Ords.all_fit(roots, k) == True{} : Bool}
  {Sf.Ords.all_fit(Ct.Cert.first(levels, roots), k) == True{} : Bool}

def Cert.first_fit(levels, roots, k, lfit, rfit):
  match levels:
    case Nil{}:
      rfit
    case Con{l, t}:
      E.Bool.and_l(Sf.Ords.all_fit(l, k), Cert.levels_fit(t, k),
        lfit)

def Cert.cond1(+td: Nat, +sd: Nat, +g: G.Graph(),
  +roots: List<&2, U32>, +levels: R.Levels, +c: S.PSet,
  +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool})
  -> {S.PSet.is_subset(sd, S.PSet.from_list(sd, roots), c)
    == True{} : Bool}:
  E.Bool.and_l(
    S.PSet.is_subset(sd, S.PSet.from_list(sd, roots), c),
    Bool.and(Sp.Spec.closed(td, g, sd, c),
      Bool.and(Ct.Cert.same(sd, S.PSet.from_list(sd,
        Ct.Cert.concat(levels, Nil{})), c),
        Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
          Ct.Cert.first(levels, roots),
          S.PSet.is_subset(sd, S.PSet.from_list(sd,
            Ct.Cert.first(levels, roots)),
            S.PSet.from_list(sd, roots))))), ok)

def Cert.tail1(+td: Nat, +sd: Nat, +g: G.Graph(),
  +roots: List<&2, U32>, +levels: R.Levels, +c: S.PSet,
  +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool})
  -> {Bool.and(Sp.Spec.closed(td, g, sd, c),
    Bool.and(Ct.Cert.same(sd, S.PSet.from_list(sd,
      Ct.Cert.concat(levels, Nil{})), c),
      Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
        Ct.Cert.first(levels, roots),
        S.PSet.is_subset(sd, S.PSet.from_list(sd,
          Ct.Cert.first(levels, roots)),
          S.PSet.from_list(sd, roots))))) == True{} : Bool}:
  E.Bool.and_r(
    S.PSet.is_subset(sd, S.PSet.from_list(sd, roots), c),
    Bool.and(Sp.Spec.closed(td, g, sd, c),
      Bool.and(Ct.Cert.same(sd, S.PSet.from_list(sd,
        Ct.Cert.concat(levels, Nil{})), c),
        Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
          Ct.Cert.first(levels, roots),
          S.PSet.is_subset(sd, S.PSet.from_list(sd,
            Ct.Cert.first(levels, roots)),
            S.PSet.from_list(sd, roots))))), ok)

def Cert.cond2(+td: Nat, +sd: Nat, +g: G.Graph(),
  +roots: List<&2, U32>, +levels: R.Levels, +c: S.PSet,
  +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool})
  -> {Sp.Spec.closed(td, g, sd, c) == True{} : Bool}:
  E.Bool.and_l(Sp.Spec.closed(td, g, sd, c),
    Bool.and(Ct.Cert.same(sd, S.PSet.from_list(sd,
      Ct.Cert.concat(levels, Nil{})), c),
      Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
        Ct.Cert.first(levels, roots),
        S.PSet.is_subset(sd, S.PSet.from_list(sd,
          Ct.Cert.first(levels, roots)),
          S.PSet.from_list(sd, roots)))),
    Cert.tail1(td, sd, g, roots, levels, c, ok))

def Cert.tail2(+td: Nat, +sd: Nat, +g: G.Graph(),
  +roots: List<&2, U32>, +levels: R.Levels, +c: S.PSet,
  +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool})
  -> {Bool.and(Ct.Cert.same(sd, S.PSet.from_list(sd,
    Ct.Cert.concat(levels, Nil{})), c),
    Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
      Ct.Cert.first(levels, roots),
      S.PSet.is_subset(sd, S.PSet.from_list(sd,
        Ct.Cert.first(levels, roots)),
        S.PSet.from_list(sd, roots)))) == True{} : Bool}:
  E.Bool.and_r(Sp.Spec.closed(td, g, sd, c),
    Bool.and(Ct.Cert.same(sd, S.PSet.from_list(sd,
      Ct.Cert.concat(levels, Nil{})), c),
      Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
        Ct.Cert.first(levels, roots),
        S.PSet.is_subset(sd, S.PSet.from_list(sd,
          Ct.Cert.first(levels, roots)),
          S.PSet.from_list(sd, roots)))),
    Cert.tail1(td, sd, g, roots, levels, c, ok))

def Cert.cond3(+td: Nat, +sd: Nat, +g: G.Graph(),
  +roots: List<&2, U32>, +levels: R.Levels, +c: S.PSet,
  +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool})
  -> {S.PSet.is_subset(sd, c, S.PSet.from_list(sd,
    Ct.Cert.concat(levels, Nil{}))) == True{} : Bool}:
  E.Bool.and_r(S.PSet.is_subset(sd, S.PSet.from_list(sd,
    Ct.Cert.concat(levels, Nil{})), c),
    S.PSet.is_subset(sd, c, S.PSet.from_list(sd,
      Ct.Cert.concat(levels, Nil{}))),
    E.Bool.and_l(Ct.Cert.same(sd, S.PSet.from_list(sd,
      Ct.Cert.concat(levels, Nil{})), c),
      Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
        Ct.Cert.first(levels, roots),
        S.PSet.is_subset(sd, S.PSet.from_list(sd,
          Ct.Cert.first(levels, roots)),
          S.PSet.from_list(sd, roots))),
      Cert.tail2(td, sd, g, roots, levels, c, ok)))

def Cert.cond4(+td: Nat, +sd: Nat, +g: G.Graph(),
  +roots: List<&2, U32>, +levels: R.Levels, +c: S.PSet,
  +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool})
  -> {Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
    Ct.Cert.first(levels, roots),
    S.PSet.is_subset(sd, S.PSet.from_list(sd,
      Ct.Cert.first(levels, roots)), S.PSet.from_list(sd, roots)))
    == True{} : Bool}:
  E.Bool.and_r(Ct.Cert.same(sd, S.PSet.from_list(sd,
    Ct.Cert.concat(levels, Nil{})), c),
    Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
      Ct.Cert.first(levels, roots),
      S.PSet.is_subset(sd, S.PSet.from_list(sd,
        Ct.Cert.first(levels, roots)),
        S.PSet.from_list(sd, roots))),
    Cert.tail2(td, sd, g, roots, levels, c, ok))

def Cert.zero_ok(+td: Nat, +sd: Nat, +g: G.Graph(),
  +roots: List<&2, U32>, +levels: R.Levels, +c: S.PSet,
  +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool})
  -> {S.PSet.is_subset(sd, S.PSet.from_list(sd,
    Ct.Cert.first(levels, roots)), S.PSet.from_list(sd, roots))
    == True{} : Bool}:
  Cert.layers_acc(Ct.Cert.rest(levels), td, g,
    Ct.Cert.first(levels, roots),
    S.PSet.is_subset(sd, S.PSet.from_list(sd,
      Ct.Cert.first(levels, roots)), S.PSet.from_list(sd, roots)),
    Cert.cond4(td, sd, g, roots, levels, c, ok))

def Cert.layers_true(+td: Nat, +sd: Nat, +g: G.Graph(),
  +roots: List<&2, U32>, +levels: R.Levels, +c: S.PSet,
  +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool})
  -> {Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
    Ct.Cert.first(levels, roots), True{}) == True{} : Bool}:
  %Cert.zero_ok(td, sd, g, roots, levels, c, ok)
    : {Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
      Ct.Cert.first(levels, roots), _) == True{} : Bool}
  Cert.cond4(td, sd, g, roots, levels, c, ok)

law Cert.exact:
  for +n: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +roots: List<&2, U32>
  for +levels: R.Levels
  for +c: S.PSet
  for +x: U32
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +rfit: {Sf.Ords.all_fit(roots, 12n+sd) == True{} : Bool}
  for +lfit: {Cert.levels_fit(levels, 12n+sd) == True{} : Bool}
  for +vc: {S.PSet.valid(sd, c, True{}) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+sd) == True{} : Bool}
  for +fuel: {C.Nat.upto(
    S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)), 1n+n) == True{}
    : Bool}
  for +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{}
    : Bool}
  {S.PSet.member(sd, c, x)
    == S.PSet.member(sd, Sp.Spec.closure(n, td, g, sd,
         S.PSet.from_list(sd, roots)), x) : Bool}

def Cert.exact(n, td, sd, g, roots, levels, c, x, gf, lt, rfit,
  lfit, vc, inv, fuel, ok):
  Ca.PSet.member_same(sd, c,
    Sp.Spec.closure(n, td, g, sd, S.PSet.from_list(sd, roots)), x,
    vc,
    Lp.Spec.closure_valid(n, td, sd, g, S.PSet.from_list(sd, roots),
      gf, lt, Iv.PSet.valid_from_list(roots, sd, lt, rfit)), lt, inv,
    E.Bool.and_both(S.PSet.is_subset(sd, c,
      Sp.Spec.closure(n, td, g, sd, S.PSet.from_list(sd, roots))),
      S.PSet.is_subset(sd, Sp.Spec.closure(n, td, g, sd,
        S.PSet.from_list(sd, roots)), c),
      Sa.PSet.subset_trans(sd, c,
        S.PSet.from_list(sd, Ct.Cert.concat(levels, Nil{})),
        Sp.Spec.closure(n, td, g, sd, S.PSet.from_list(sd, roots)),
        vc,
        Iv.PSet.valid_from_list(Ct.Cert.concat(levels, Nil{}), sd,
          lt, Cert.concat_fit(levels, Nil{}, 12n+sd, lfit, {==})),
        Lp.Spec.closure_valid(n, td, sd, g,
          S.PSet.from_list(sd, roots), gf, lt,
          Iv.PSet.valid_from_list(roots, sd, lt, rfit)), lt,
        Cert.cond3(td, sd, g, roots, levels, c, ok),
        PSet.subset_of_list_mem(Ct.Cert.concat(levels, Nil{}), sd,
          Sp.Spec.closure(n, td, g, sd, S.PSet.from_list(sd, roots)),
          lt, Cert.concat_fit(levels, Nil{}, 12n+sd, lfit, {==}),
          Lp.Spec.closure_valid(n, td, sd, g,
            S.PSet.from_list(sd, roots), gf, lt,
            Iv.PSet.valid_from_list(roots, sd, lt, rfit)),
          Cert.concat_inside(levels, roots, td, sd, g,
            Sp.Spec.closure(n, td, g, sd,
              S.PSet.from_list(sd, roots)), gf, lt,
            Lp.Spec.closure_valid(n, td, sd, g,
              S.PSet.from_list(sd, roots), gf, lt,
              Iv.PSet.valid_from_list(roots, sd, lt, rfit)),
            St.Spec.closure_is_closed(n, td, sd, g,
              S.PSet.from_list(sd, roots), gf, lt,
              Iv.PSet.valid_from_list(roots, sd, lt, rfit), fuel),
            rfit, lfit,
            Sa.PSet.subset_trans(sd,
              S.PSet.from_list(sd, Ct.Cert.first(levels, roots)),
              S.PSet.from_list(sd, roots),
              Sp.Spec.closure(n, td, g, sd,
                S.PSet.from_list(sd, roots)),
              Iv.PSet.valid_from_list(
                Ct.Cert.first(levels, roots), sd, lt,
                Cert.first_fit(levels, roots, 12n+sd, lfit, rfit)),
              Iv.PSet.valid_from_list(roots, sd, lt, rfit),
              Lp.Spec.closure_valid(n, td, sd, g,
                S.PSet.from_list(sd, roots), gf, lt,
                Iv.PSet.valid_from_list(roots, sd, lt, rfit)), lt,
              Cert.zero_ok(td, sd, g, roots, levels, c, ok),
              Lp.Spec.closure_contains_roots(n, td, sd, g,
                S.PSet.from_list(sd, roots), gf, lt,
                Iv.PSet.valid_from_list(roots, sd, lt, rfit))),
            Cert.layers_true(td, sd, g, roots, levels, c, ok)))),
      Lp.Spec.closure_least(n, td, sd, g,
        S.PSet.from_list(sd, roots), c, gf, lt,
        Iv.PSet.valid_from_list(roots, sd, lt, rfit), vc,
        Cert.cond2(td, sd, g, roots, levels, c, ok),
        Cert.cond1(td, sd, g, roots, levels, c, ok))))
