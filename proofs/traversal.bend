# proofs/traversal.bend -- the production traversal is the specification
# closure (law C-02).
#
# Two inclusions, and they are proved by opposite means.
#
# The traversal never leaves the closure, because every vertex it adds is a
# successor of one it had already accepted: that is an invariant of the
# frontier walk, and the closure is edge-closed, so the walk cannot escape.
#
# The closure never leaves the traversal, because a finished traversal is
# itself edge-closed and holds the roots -- and the closure is the least such
# set. What makes a finished traversal edge-closed is the invariant the
# frontier exists to maintain: every vertex `seen` either has all its
# successors in `seen` already, or is still waiting on a frontier. When both
# frontiers are empty, the first disjunct holds everywhere.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./shift.bend as Sf
import ./shape.bend as Sh
import ./leafenum.bend as Le
import ./treeenum.bend as Te
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
import ./validshape.bend as Vs
import ../core/count.bend as C
import ../core/set.bend as S
import ../closure/graph.bend as G
import ../closure/reach.bend as R
import ../spec/closure.bend as Sp

# ---------------------------------------------------------------------------
# Every successor of a member of an edge-closed set is in it.
# ---------------------------------------------------------------------------

law Ords.succ_inside:
  for +l: List<&2, U32>
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +xx: S.PSet
  for +v: U32
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, xx, True{}) == True{} : Bool}
  for +cl: {Sp.Spec.closed(td, g, sd, xx) == True{} : Bool}
  for +mv: {S.PSet.member(sd, xx, v) == True{} : Bool}
  for +invv: {Dc.U32.hi_zero(v, 12n+sd) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l, G.Graph.succ(td, g, v)) == True{}
    : Bool}
  {Sc.Ords.all_mem(l, sd, xx) == True{} : Bool}

def Ords.succ_inside(l, td, sd, g, xx, v, gf, lt, vx, cl, mv, invv,
  ai):
  match l:
    case Nil{}:
      {==}
    case Con{w, u}:
      E.Bool.and_both(S.PSet.member(sd, xx, w),
        Sc.Ords.all_mem(u, sd, xx),
        Sa.PSet.subset_member_at(sd, Sp.Spec.post(td, g, sd, xx),
          xx, w, Pm.Spec.post_valid(td, sd, g, xx, gf, lt), vx, lt,
          Fx.Ords.fit_of_contains(G.Graph.succ(td, g, v), 12n+sd, w,
            Gr.Graph.succ_fits(td, sd, g, v, gf),
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              G.Graph.succ(td, g, v), w),
              Sa.Ords.all_in(u, G.Graph.succ(td, g, v)), ai)),
          cl,
          Pm.Spec.post_of_any(td, sd, g, xx, w, lt,
            Fx.Ords.fit_of_contains(G.Graph.succ(td, g, v), 12n+sd,
              w, Gr.Graph.succ_fits(td, sd, g, v, gf),
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                G.Graph.succ(td, g, v), w),
                Sa.Ords.all_in(u, G.Graph.succ(td, g, v)), ai)),
            Gr.Graph.any_succ_of_member(S.PSet.to_list(sd, xx), td,
              g, v, w, Sc.Ords.head_eq(S.PSet.to_list(sd, xx), v),
              {==},
              Pm.Ords.in_of_member(sd, xx, v, vx, lt, invv, mv),
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                G.Graph.succ(td, g, v), w),
                Sa.Ords.all_in(u, G.Graph.succ(td, g, v)), ai)))),
        Ords.succ_inside(u, td, sd, g, xx, v, gf, lt, vx, cl, mv,
          invv,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            G.Graph.succ(td, g, v), w),
            Sa.Ords.all_in(u, G.Graph.succ(td, g, v)), ai)))

# ---------------------------------------------------------------------------
# Inserting into a set.
# ---------------------------------------------------------------------------

law Ords.all_mem_insert:
  for +l: List<&2, U32>
  for +d: Nat
  for +s: S.PSet
  for +y: U32
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +invy: {Dc.U32.hi_zero(y, 12n+d) == True{} : Bool}
  for +vs: {S.PSet.valid(d, s, True{}) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l, S.PSet.to_list(d, s)) == True{} : Bool}
  {Sc.Ords.all_mem(l, d, S.PSet.insert(d, s, y)) == True{} : Bool}

def Ords.all_mem_insert(l, d, s, y, lt, invy, vs, ai):
  match l:
    case Nil{}:
      {==}
    case Con{x, u}:
      E.Bool.and_both(S.PSet.member(d, S.PSet.insert(d, s, y), x),
        Sc.Ords.all_mem(u, d, S.PSet.insert(d, s, y)),
        Ls.PSet.insert_keeps_at(d, s, y, x, lt,
          Sa.PSet.in_range_of_to_list(d, s, x, vs, lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(d, s), x),
              Sa.Ords.all_in(u, S.PSet.to_list(d, s)), ai)),
          Sh.PSet.valid_wf(d, s, vs),
          Sa.PSet.member_of_to_list(d, s, x, vs, lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(d, s), x),
              Sa.Ords.all_in(u, S.PSet.to_list(d, s)), ai))),
        Ords.all_mem_insert(u, d, s, y, lt, invy, vs,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(d, s), x),
            Sa.Ords.all_in(u, S.PSet.to_list(d, s)), ai)))

law PSet.subset_insert:
  for +d: Nat
  for +s: S.PSet
  for +y: U32
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +invy: {Dc.U32.hi_zero(y, 12n+d) == True{} : Bool}
  for +vs: {S.PSet.valid(d, s, True{}) == True{} : Bool}
  {S.PSet.is_subset(d, s, S.PSet.insert(d, s, y)) == True{} : Bool}

def PSet.subset_insert(d, s, y, lt, invy, vs):
  Sc.PSet.subset_of_members(d, s, S.PSet.insert(d, s, y), vs,
    Iv.PSet.valid_insert(d, s, y, lt, invy, vs), lt,
    Ords.all_mem_insert(S.PSet.to_list(d, s), d, s, y, lt, invy, vs,
      Sa.Ords.all_in_self(S.PSet.to_list(d, s))))

def PSet.insert_side(+d: Nat, +s: S.PSet, +y: U32, +u: U32,
  +xx: S.PSet, +e: Bool, +ee: {e == U32.is_eq(y, u) : Bool},
  +my: {S.PSet.member(d, xx, y) == True{} : Bool},
  +ou: {Bool.or(U32.is_eq(y, u), S.PSet.member(d, s, u)) == True{}
    : Bool},
  +sx: {S.PSet.is_subset(d, s, xx) == True{} : Bool},
  +vs: {S.PSet.valid(d, s, True{}) == True{} : Bool},
  +vx: {S.PSet.valid(d, xx, True{}) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +invu: {Dc.U32.hi_zero(u, 12n+d) == True{} : Bool})
  -> {S.PSet.member(d, xx, u) == True{} : Bool}:
  match e:
    case True{}:
      %E.U32.eq_reflect(y, u,
        E.Bool.sym(True{}, U32.is_eq(y, u), ee))
        : {S.PSet.member(d, xx, _) == True{} : Bool}
      my
    case False{}:
      Sa.PSet.subset_member_at(d, s, xx, u, vs, vx, lt, invu, sx,
        %E.Bool.sym(False{}, U32.is_eq(y, u), ee)
          : {Bool.or(_, S.PSet.member(d, s, u)) == True{} : Bool}
        ou)

law Ords.all_mem_of_insert:
  for +l: List<&2, U32>
  for +d: Nat
  for +s: S.PSet
  for +y: U32
  for +xx: S.PSet
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +invy: {Dc.U32.hi_zero(y, 12n+d) == True{} : Bool}
  for +vs: {S.PSet.valid(d, s, True{}) == True{} : Bool}
  for +vx: {S.PSet.valid(d, xx, True{}) == True{} : Bool}
  for +sx: {S.PSet.is_subset(d, s, xx) == True{} : Bool}
  for +my: {S.PSet.member(d, xx, y) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l,
    S.PSet.to_list(d, S.PSet.insert(d, s, y))) == True{} : Bool}
  {Sc.Ords.all_mem(l, d, xx) == True{} : Bool}

def Ords.all_mem_of_insert(l, d, s, y, xx, lt, invy, vs, vx, sx, my,
  ai):
  match l:
    case Nil{}:
      {==}
    case Con{u, t}:
      E.Bool.and_both(S.PSet.member(d, xx, u),
        Sc.Ords.all_mem(t, d, xx),
        PSet.insert_side(d, s, y, u, xx, U32.is_eq(y, u), {==}, my,
          Ls.PSet.insert_only_at(d, s, y, u, lt,
            Sa.PSet.in_range_of_to_list(d, S.PSet.insert(d, s, y), u,
              Iv.PSet.valid_insert(d, s, y, lt, invy, vs), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(d, S.PSet.insert(d, s, y)), u),
                Sa.Ords.all_in(t,
                  S.PSet.to_list(d, S.PSet.insert(d, s, y))), ai)),
            invy, Sh.PSet.valid_wf(d, s, vs),
            Sa.PSet.member_of_to_list(d, S.PSet.insert(d, s, y), u,
              Iv.PSet.valid_insert(d, s, y, lt, invy, vs), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(d, S.PSet.insert(d, s, y)), u),
                Sa.Ords.all_in(t,
                  S.PSet.to_list(d, S.PSet.insert(d, s, y))), ai))),
          sx, vs, vx, lt,
          Sa.PSet.in_range_of_to_list(d, S.PSet.insert(d, s, y), u,
            Iv.PSet.valid_insert(d, s, y, lt, invy, vs), lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(d, S.PSet.insert(d, s, y)), u),
              Sa.Ords.all_in(t,
                S.PSet.to_list(d, S.PSet.insert(d, s, y))), ai))),
        Ords.all_mem_of_insert(t, d, s, y, xx, lt, invy, vs, vx, sx,
          my,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(d, S.PSet.insert(d, s, y)), u),
            Sa.Ords.all_in(t,
              S.PSet.to_list(d, S.PSet.insert(d, s, y))), ai)))

law PSet.subset_of_insert:
  for +d: Nat
  for +s: S.PSet
  for +y: U32
  for +xx: S.PSet
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +invy: {Dc.U32.hi_zero(y, 12n+d) == True{} : Bool}
  for +vs: {S.PSet.valid(d, s, True{}) == True{} : Bool}
  for +vx: {S.PSet.valid(d, xx, True{}) == True{} : Bool}
  for +sx: {S.PSet.is_subset(d, s, xx) == True{} : Bool}
  for +my: {S.PSet.member(d, xx, y) == True{} : Bool}
  {S.PSet.is_subset(d, S.PSet.insert(d, s, y), xx) == True{} : Bool}

def PSet.subset_of_insert(d, s, y, xx, lt, invy, vs, vx, sx, my):
  Sc.PSet.subset_of_members(d, S.PSet.insert(d, s, y), xx,
    Iv.PSet.valid_insert(d, s, y, lt, invy, vs), vx, lt,
    Ords.all_mem_of_insert(
      S.PSet.to_list(d, S.PSet.insert(d, s, y)), d, s, y, xx, lt,
      invy, vs, vx, sx, my,
      Sa.Ords.all_in_self(
        S.PSet.to_list(d, S.PSet.insert(d, s, y)))))

# ---------------------------------------------------------------------------
# The successor fold.
# ---------------------------------------------------------------------------

law Reach.push_valid:
  for +ws: List<&2, U32>
  for +sd: Nat
  for +seen: S.PSet
  for +next: List<&2, U32>
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +fw: {Sf.Ords.all_fit(ws, 12n+sd) == True{} : Bool}
  for +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool}
  {S.PSet.valid(sd,
    R.Push.seen(R.Reach.push(sd, ws, R.Pu{seen, next})), True{})
    == True{} : Bool}

def Reach.push_valid.step(+t: List<&2, U32>, +sd: Nat,
  +seen: S.PSet, +next: List<&2, U32>, +w: U32, +have: Bool,
  +onT: {S.PSet.valid(sd,
    R.Push.seen(R.Reach.push(sd, t, R.Pu{seen, next})), True{})
    == True{} : Bool},
  +onF: {S.PSet.valid(sd, R.Push.seen(R.Reach.push(sd, t,
    R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), True{})
    == True{} : Bool})
  -> {S.PSet.valid(sd, R.Push.seen(R.Reach.push(sd, t,
    R.Reach.push.add(sd, w, seen, next, have))), True{}) == True{}
    : Bool}:
  match have:
    case True{}:
      onT
    case False{}:
      onF

def Reach.push_valid(ws, sd, seen, next, lt, fw, vs):
  match ws:
    case Nil{}:
      vs
    case Con{w, t}:
      Reach.push_valid.step(t, sd, seen, next, w,
        S.PSet.member(sd, seen, w),
        Reach.push_valid(t, sd, seen, next, lt,
          E.Bool.and_r(Dc.U32.hi_zero(w, 12n+sd),
            Sf.Ords.all_fit(t, 12n+sd), fw), vs),
        Reach.push_valid(t, sd, S.PSet.insert(sd, seen, w),
          Con{w, next}, lt,
          E.Bool.and_r(Dc.U32.hi_zero(w, 12n+sd),
            Sf.Ords.all_fit(t, 12n+sd), fw),
          Iv.PSet.valid_insert(sd, seen, w, lt,
            E.Bool.and_l(Dc.U32.hi_zero(w, 12n+sd),
              Sf.Ords.all_fit(t, 12n+sd), fw), vs)))

law Reach.push_grows:
  for +ws: List<&2, U32>
  for +sd: Nat
  for +seen: S.PSet
  for +next: List<&2, U32>
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +fw: {Sf.Ords.all_fit(ws, 12n+sd) == True{} : Bool}
  for +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool}
  {S.PSet.is_subset(sd, seen,
    R.Push.seen(R.Reach.push(sd, ws, R.Pu{seen, next}))) == True{}
    : Bool}

def Reach.push_grows.step(+t: List<&2, U32>, +sd: Nat,
  +seen: S.PSet, +next: List<&2, U32>, +w: U32, +have: Bool,
  +onT: {S.PSet.is_subset(sd, seen,
    R.Push.seen(R.Reach.push(sd, t, R.Pu{seen, next}))) == True{}
    : Bool},
  +onF: {S.PSet.is_subset(sd, seen,
    R.Push.seen(R.Reach.push(sd, t,
      R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}}))) == True{}
    : Bool})
  -> {S.PSet.is_subset(sd, seen, R.Push.seen(R.Reach.push(sd, t,
    R.Reach.push.add(sd, w, seen, next, have)))) == True{} : Bool}:
  match have:
    case True{}:
      onT
    case False{}:
      onF

def Reach.push_grows(ws, sd, seen, next, lt, fw, vs):
  match ws:
    case Nil{}:
      Lp.PSet.subset_refl(sd, seen, vs, lt)
    case Con{w, t}:
      Reach.push_grows.step(t, sd, seen, next, w,
        S.PSet.member(sd, seen, w),
        Reach.push_grows(t, sd, seen, next, lt,
          E.Bool.and_r(Dc.U32.hi_zero(w, 12n+sd),
            Sf.Ords.all_fit(t, 12n+sd), fw), vs),
        Sa.PSet.subset_trans(sd, seen, S.PSet.insert(sd, seen, w),
          R.Push.seen(R.Reach.push(sd, t,
            R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), vs,
          Iv.PSet.valid_insert(sd, seen, w, lt,
            E.Bool.and_l(Dc.U32.hi_zero(w, 12n+sd),
              Sf.Ords.all_fit(t, 12n+sd), fw), vs),
          Reach.push_valid(t, sd, S.PSet.insert(sd, seen, w),
            Con{w, next}, lt,
            E.Bool.and_r(Dc.U32.hi_zero(w, 12n+sd),
              Sf.Ords.all_fit(t, 12n+sd), fw),
            Iv.PSet.valid_insert(sd, seen, w, lt,
              E.Bool.and_l(Dc.U32.hi_zero(w, 12n+sd),
                Sf.Ords.all_fit(t, 12n+sd), fw), vs)), lt,
          PSet.subset_insert(sd, seen, w, lt,
            E.Bool.and_l(Dc.U32.hi_zero(w, 12n+sd),
              Sf.Ords.all_fit(t, 12n+sd), fw), vs),
          Reach.push_grows(t, sd, S.PSet.insert(sd, seen, w),
            Con{w, next}, lt,
            E.Bool.and_r(Dc.U32.hi_zero(w, 12n+sd),
              Sf.Ords.all_fit(t, 12n+sd), fw),
            Iv.PSet.valid_insert(sd, seen, w, lt,
              E.Bool.and_l(Dc.U32.hi_zero(w, 12n+sd),
                Sf.Ords.all_fit(t, 12n+sd), fw), vs))))

law Reach.push_covers:
  for +ws: List<&2, U32>
  for +sd: Nat
  for +seen: S.PSet
  for +next: List<&2, U32>
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +fw: {Sf.Ords.all_fit(ws, 12n+sd) == True{} : Bool}
  for +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool}
  {Sc.Ords.all_mem(ws, sd,
    R.Push.seen(R.Reach.push(sd, ws, R.Pu{seen, next}))) == True{}
    : Bool}

def Reach.push_covers.step(+t: List<&2, U32>, +sd: Nat,
  +seen: S.PSet, +next: List<&2, U32>, +w: U32, +have: Bool,
  +eh: {have == S.PSet.member(sd, seen, w) : Bool},
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +fitw: {Dc.U32.hi_zero(w, 12n+sd) == True{} : Bool},
  +ft: {Sf.Ords.all_fit(t, 12n+sd) == True{} : Bool},
  +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool},
  +onT: {Sc.Ords.all_mem(t, sd,
    R.Push.seen(R.Reach.push(sd, t, R.Pu{seen, next}))) == True{}
    : Bool},
  +onF: {Sc.Ords.all_mem(t, sd, R.Push.seen(R.Reach.push(sd, t,
    R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}}))) == True{}
    : Bool})
  -> {Sc.Ords.all_mem(Con{w, t}, sd,
    R.Push.seen(R.Reach.push(sd, t,
      R.Reach.push.add(sd, w, seen, next, have)))) == True{} : Bool}:
  match have:
    case True{}:
      E.Bool.and_both(S.PSet.member(sd,
        R.Push.seen(R.Reach.push(sd, t, R.Pu{seen, next})), w),
        Sc.Ords.all_mem(t, sd,
          R.Push.seen(R.Reach.push(sd, t, R.Pu{seen, next}))),
        Sa.PSet.subset_member_at(sd, seen,
          R.Push.seen(R.Reach.push(sd, t, R.Pu{seen, next})), w, vs,
          Reach.push_valid(t, sd, seen, next, lt, ft, vs), lt, fitw,
          Reach.push_grows(t, sd, seen, next, lt, ft, vs),
          E.Bool.sym(True{}, S.PSet.member(sd, seen, w), eh)), onT)
    case False{}:
      E.Bool.and_both(S.PSet.member(sd,
        R.Push.seen(R.Reach.push(sd, t,
          R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), w),
        Sc.Ords.all_mem(t, sd, R.Push.seen(R.Reach.push(sd, t,
          R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}}))),
        Sa.PSet.subset_member_at(sd, S.PSet.insert(sd, seen, w),
          R.Push.seen(R.Reach.push(sd, t,
            R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), w,
          Iv.PSet.valid_insert(sd, seen, w, lt, fitw, vs),
          Reach.push_valid(t, sd, S.PSet.insert(sd, seen, w),
            Con{w, next}, lt, ft,
            Iv.PSet.valid_insert(sd, seen, w, lt, fitw, vs)), lt,
          fitw,
          Reach.push_grows(t, sd, S.PSet.insert(sd, seen, w),
            Con{w, next}, lt, ft,
            Iv.PSet.valid_insert(sd, seen, w, lt, fitw, vs)),
          Ls.PSet.insert_hit_at(sd, seen, w, w, lt, fitw,
            Sh.PSet.valid_wf(sd, seen, vs), E.U32.is_eq_refl(w))),
        onF)

def Reach.push_covers(ws, sd, seen, next, lt, fw, vs):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      Reach.push_covers.step(t, sd, seen, next, w,
        S.PSet.member(sd, seen, w), {==}, lt,
        E.Bool.and_l(Dc.U32.hi_zero(w, 12n+sd),
          Sf.Ords.all_fit(t, 12n+sd), fw),
        E.Bool.and_r(Dc.U32.hi_zero(w, 12n+sd),
          Sf.Ords.all_fit(t, 12n+sd), fw), vs,
        Reach.push_covers(t, sd, seen, next, lt,
          E.Bool.and_r(Dc.U32.hi_zero(w, 12n+sd),
            Sf.Ords.all_fit(t, 12n+sd), fw), vs),
        Reach.push_covers(t, sd, S.PSet.insert(sd, seen, w),
          Con{w, next}, lt,
          E.Bool.and_r(Dc.U32.hi_zero(w, 12n+sd),
            Sf.Ords.all_fit(t, 12n+sd), fw),
          Iv.PSet.valid_insert(sd, seen, w, lt,
            E.Bool.and_l(Dc.U32.hi_zero(w, 12n+sd),
              Sf.Ords.all_fit(t, 12n+sd), fw), vs)))

law Reach.push_inside:
  for +ws: List<&2, U32>
  for +sd: Nat
  for +seen: S.PSet
  for +next: List<&2, U32>
  for +xx: S.PSet
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +fw: {Sf.Ords.all_fit(ws, 12n+sd) == True{} : Bool}
  for +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, xx, True{}) == True{} : Bool}
  for +wx: {Sc.Ords.all_mem(ws, sd, xx) == True{} : Bool}
  for +sx: {S.PSet.is_subset(sd, seen, xx) == True{} : Bool}
  {S.PSet.is_subset(sd,
    R.Push.seen(R.Reach.push(sd, ws, R.Pu{seen, next})), xx)
    == True{} : Bool}

def Reach.push_inside.step(+t: List<&2, U32>, +sd: Nat,
  +seen: S.PSet, +next: List<&2, U32>, +xx: S.PSet, +w: U32,
  +have: Bool,
  +onT: {S.PSet.is_subset(sd,
    R.Push.seen(R.Reach.push(sd, t, R.Pu{seen, next})), xx)
    == True{} : Bool},
  +onF: {S.PSet.is_subset(sd, R.Push.seen(R.Reach.push(sd, t,
    R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), xx) == True{}
    : Bool})
  -> {S.PSet.is_subset(sd, R.Push.seen(R.Reach.push(sd, t,
    R.Reach.push.add(sd, w, seen, next, have))), xx) == True{}
    : Bool}:
  match have:
    case True{}:
      onT
    case False{}:
      onF

def Reach.push_inside(ws, sd, seen, next, xx, lt, fw, vs, vx, wx,
  sx):
  match ws:
    case Nil{}:
      sx
    case Con{w, t}:
      Reach.push_inside.step(t, sd, seen, next, xx, w,
        S.PSet.member(sd, seen, w),
        Reach.push_inside(t, sd, seen, next, xx, lt,
          E.Bool.and_r(Dc.U32.hi_zero(w, 12n+sd),
            Sf.Ords.all_fit(t, 12n+sd), fw), vs, vx,
          E.Bool.and_r(S.PSet.member(sd, xx, w),
            Sc.Ords.all_mem(t, sd, xx), wx), sx),
        Reach.push_inside(t, sd, S.PSet.insert(sd, seen, w),
          Con{w, next}, xx, lt,
          E.Bool.and_r(Dc.U32.hi_zero(w, 12n+sd),
            Sf.Ords.all_fit(t, 12n+sd), fw),
          Iv.PSet.valid_insert(sd, seen, w, lt,
            E.Bool.and_l(Dc.U32.hi_zero(w, 12n+sd),
              Sf.Ords.all_fit(t, 12n+sd), fw), vs), vx,
          E.Bool.and_r(S.PSet.member(sd, xx, w),
            Sc.Ords.all_mem(t, sd, xx), wx),
          PSet.subset_of_insert(sd, seen, w, xx, lt,
            E.Bool.and_l(Dc.U32.hi_zero(w, 12n+sd),
              Sf.Ords.all_fit(t, 12n+sd), fw), vs, vx, sx,
            E.Bool.and_l(S.PSet.member(sd, xx, w),
              Sc.Ords.all_mem(t, sd, xx), wx))))

law Reach.push_next_inside:
  for +ws: List<&2, U32>
  for +sd: Nat
  for +seen: S.PSet
  for +next: List<&2, U32>
  for +xx: S.PSet
  for +wx: {Sc.Ords.all_mem(ws, sd, xx) == True{} : Bool}
  for +nx: {Sc.Ords.all_mem(next, sd, xx) == True{} : Bool}
  {Sc.Ords.all_mem(
    R.Push.next(R.Reach.push(sd, ws, R.Pu{seen, next})), sd, xx)
    == True{} : Bool}

def Reach.push_next_inside.step(+t: List<&2, U32>, +sd: Nat,
  +seen: S.PSet, +next: List<&2, U32>, +xx: S.PSet, +w: U32,
  +have: Bool,
  +onT: {Sc.Ords.all_mem(
    R.Push.next(R.Reach.push(sd, t, R.Pu{seen, next})), sd, xx)
    == True{} : Bool},
  +onF: {Sc.Ords.all_mem(R.Push.next(R.Reach.push(sd, t,
    R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), sd, xx)
    == True{} : Bool})
  -> {Sc.Ords.all_mem(R.Push.next(R.Reach.push(sd, t,
    R.Reach.push.add(sd, w, seen, next, have))), sd, xx) == True{}
    : Bool}:
  match have:
    case True{}:
      onT
    case False{}:
      onF

def Reach.push_next_inside(ws, sd, seen, next, xx, wx, nx):
  match ws:
    case Nil{}:
      nx
    case Con{w, t}:
      Reach.push_next_inside.step(t, sd, seen, next, xx, w,
        S.PSet.member(sd, seen, w),
        Reach.push_next_inside(t, sd, seen, next, xx,
          E.Bool.and_r(S.PSet.member(sd, xx, w),
            Sc.Ords.all_mem(t, sd, xx), wx), nx),
        Reach.push_next_inside(t, sd, S.PSet.insert(sd, seen, w),
          Con{w, next}, xx,
          E.Bool.and_r(S.PSet.member(sd, xx, w),
            Sc.Ords.all_mem(t, sd, xx), wx),
          E.Bool.and_both(S.PSet.member(sd, xx, w),
            Sc.Ords.all_mem(next, sd, xx),
            E.Bool.and_l(S.PSet.member(sd, xx, w),
              Sc.Ords.all_mem(t, sd, xx), wx), nx)))

law Reach.push_next_grows:
  for +ws: List<&2, U32>
  for +sd: Nat
  for +seen: S.PSet
  for +next: List<&2, U32>
  for +u: U32
  for +c: {List.contains(~U32, ~U32.is_eq, next, u) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq,
    R.Push.next(R.Reach.push(sd, ws, R.Pu{seen, next})), u)
    == True{} : Bool}

def Reach.push_next_grows.step(+t: List<&2, U32>, +sd: Nat,
  +seen: S.PSet, +next: List<&2, U32>, +u: U32, +w: U32,
  +have: Bool,
  +onT: {List.contains(~U32, ~U32.is_eq,
    R.Push.next(R.Reach.push(sd, t, R.Pu{seen, next})), u)
    == True{} : Bool},
  +onF: {List.contains(~U32, ~U32.is_eq,
    R.Push.next(R.Reach.push(sd, t,
      R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), u)
    == True{} : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
    R.Push.next(R.Reach.push(sd, t,
      R.Reach.push.add(sd, w, seen, next, have))), u) == True{}
    : Bool}:
  match have:
    case True{}:
      onT
    case False{}:
      onF

def Reach.push_next_grows(ws, sd, seen, next, u, c):
  match ws:
    case Nil{}:
      c
    case Con{w, t}:
      Reach.push_next_grows.step(t, sd, seen, next, u, w,
        S.PSet.member(sd, seen, w),
        Reach.push_next_grows(t, sd, seen, next, u, c),
        Reach.push_next_grows(t, sd, S.PSet.insert(sd, seen, w),
          Con{w, next}, u,
          Sa.Ords.or_right(U32.is_eq(w, u),
            List.contains(~U32, ~U32.is_eq, next, u), c)))

law Reach.push_split:
  for +ws: List<&2, U32>
  for +sd: Nat
  for +seen: S.PSet
  for +next: List<&2, U32>
  for +u: U32
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +fw: {Sf.Ords.all_fit(ws, 12n+sd) == True{} : Bool}
  for +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(u, 12n+sd) == True{} : Bool}
  for m: {S.PSet.member(sd,
    R.Push.seen(R.Reach.push(sd, ws, R.Pu{seen, next})), u)
    == True{} : Bool}
  {Bool.or(S.PSet.member(sd, seen, u),
    List.contains(~U32, ~U32.is_eq,
      R.Push.next(R.Reach.push(sd, ws, R.Pu{seen, next})), u))
    == True{} : Bool}

def Reach.push_split.fresh(+t: List<&2, U32>, +sd: Nat,
  +seen: S.PSet, +next: List<&2, U32>, +u: U32, +w: U32,
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +fitw: {Dc.U32.hi_zero(w, 12n+sd) == True{} : Bool},
  +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool},
  +inv: {Dc.U32.hi_zero(u, 12n+sd) == True{} : Bool},
  +e2: Bool, +ee2: {e2 == U32.is_eq(w, u) : Bool},
  +e3: Bool,
  +ee3: {e3 == S.PSet.member(sd, S.PSet.insert(sd, seen, w), u)
    : Bool},
  ihF: {S.PSet.member(sd, R.Push.seen(R.Reach.push(sd, t,
      R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), u)
    == True{} : Bool} ->
    {Bool.or(S.PSet.member(sd, S.PSet.insert(sd, seen, w), u),
      List.contains(~U32, ~U32.is_eq,
        R.Push.next(R.Reach.push(sd, t,
          R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), u))
      == True{} : Bool},
  m: {S.PSet.member(sd, R.Push.seen(R.Reach.push(sd, t,
    R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), u) == True{}
    : Bool})
  -> {Bool.or(S.PSet.member(sd, seen, u),
    List.contains(~U32, ~U32.is_eq,
      R.Push.next(R.Reach.push(sd, t,
        R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), u))
    == True{} : Bool}:
  match e2:
    case True{}:
      Sa.Ords.or_right(S.PSet.member(sd, seen, u),
        List.contains(~U32, ~U32.is_eq,
          R.Push.next(R.Reach.push(sd, t,
            R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), u),
        Reach.push_next_grows(t, sd, S.PSet.insert(sd, seen, w),
          Con{w, next}, u,
          Sa.Ords.or_left(U32.is_eq(w, u),
            List.contains(~U32, ~U32.is_eq, next, u),
            E.Bool.sym(True{}, U32.is_eq(w, u), ee2))))
    case False{}:
      match e3:
        case True{}:
          Sa.Ords.or_left(S.PSet.member(sd, seen, u),
            List.contains(~U32, ~U32.is_eq,
              R.Push.next(R.Reach.push(sd, t,
                R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), u),
            %E.Bool.sym(False{}, U32.is_eq(w, u), ee2)
              : {Bool.or(_, S.PSet.member(sd, seen, u)) == True{}
                : Bool}
            Ls.PSet.insert_only_at(sd, seen, w, u, lt, inv, fitw,
              Sh.PSet.valid_wf(sd, seen, vs),
              E.Bool.sym(True{},
                S.PSet.member(sd, S.PSet.insert(sd, seen, w), u),
                ee3)))
        case False{}:
          Sa.Ords.or_right(S.PSet.member(sd, seen, u),
            List.contains(~U32, ~U32.is_eq,
              R.Push.next(R.Reach.push(sd, t,
                R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), u),
            %E.Bool.sym(False{},
              S.PSet.member(sd, S.PSet.insert(sd, seen, w), u), ee3)
              : {Bool.or(_, List.contains(~U32, ~U32.is_eq,
                  R.Push.next(R.Reach.push(sd, t,
                    R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})),
                  u)) == True{} : Bool}
            ihF(m))

def Reach.push_split.step(+t: List<&2, U32>, +sd: Nat,
  +seen: S.PSet, +next: List<&2, U32>, +u: U32, +w: U32,
  +have: Bool,
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +fitw: {Dc.U32.hi_zero(w, 12n+sd) == True{} : Bool},
  +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool},
  +inv: {Dc.U32.hi_zero(u, 12n+sd) == True{} : Bool},
  ihT: {S.PSet.member(sd,
      R.Push.seen(R.Reach.push(sd, t, R.Pu{seen, next})), u)
    == True{} : Bool} ->
    {Bool.or(S.PSet.member(sd, seen, u),
      List.contains(~U32, ~U32.is_eq,
        R.Push.next(R.Reach.push(sd, t, R.Pu{seen, next})), u))
      == True{} : Bool},
  ihF: {S.PSet.member(sd, R.Push.seen(R.Reach.push(sd, t,
      R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), u)
    == True{} : Bool} ->
    {Bool.or(S.PSet.member(sd, S.PSet.insert(sd, seen, w), u),
      List.contains(~U32, ~U32.is_eq,
        R.Push.next(R.Reach.push(sd, t,
          R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), u))
      == True{} : Bool},
  m: {S.PSet.member(sd, R.Push.seen(R.Reach.push(sd, t,
    R.Reach.push.add(sd, w, seen, next, have))), u) == True{}
    : Bool})
  -> {Bool.or(S.PSet.member(sd, seen, u),
    List.contains(~U32, ~U32.is_eq,
      R.Push.next(R.Reach.push(sd, t,
        R.Reach.push.add(sd, w, seen, next, have))), u)) == True{}
    : Bool}:
  match have:
    case True{}:
      ihT(m)
    case False{}:
      Reach.push_split.fresh(t, sd, seen, next, u, w, lt, fitw, vs,
        inv, U32.is_eq(w, u), {==},
        S.PSet.member(sd, S.PSet.insert(sd, seen, w), u), {==}, ihF,
        m)

def Reach.push_split(ws, sd, seen, next, u, lt, fw, vs, inv, m):
  match ws:
    case Nil{}:
      Sa.Ords.or_left(S.PSet.member(sd, seen, u),
        List.contains(~U32, ~U32.is_eq, next, u), m)
    case Con{w, t}:
      Reach.push_split.step(t, sd, seen, next, u, w,
        S.PSet.member(sd, seen, w), lt,
        E.Bool.and_l(Dc.U32.hi_zero(w, 12n+sd),
          Sf.Ords.all_fit(t, 12n+sd), fw), vs, inv,
        Reach.push_split(t, sd, seen, next, u, lt,
          E.Bool.and_r(Dc.U32.hi_zero(w, 12n+sd),
            Sf.Ords.all_fit(t, 12n+sd), fw), vs, inv),
        Reach.push_split(t, sd, S.PSet.insert(sd, seen, w),
          Con{w, next}, u, lt,
          E.Bool.and_r(Dc.U32.hi_zero(w, 12n+sd),
            Sf.Ords.all_fit(t, 12n+sd), fw),
          Iv.PSet.valid_insert(sd, seen, w, lt,
            E.Bool.and_l(Dc.U32.hi_zero(w, 12n+sd),
              Sf.Ords.all_fit(t, 12n+sd), fw), vs), inv), m)

law Reach.push_next_fit:
  for +ws: List<&2, U32>
  for +sd: Nat
  for +seen: S.PSet
  for +next: List<&2, U32>
  for +fw: {Sf.Ords.all_fit(ws, 12n+sd) == True{} : Bool}
  for +fn: {Sf.Ords.all_fit(next, 12n+sd) == True{} : Bool}
  {Sf.Ords.all_fit(
    R.Push.next(R.Reach.push(sd, ws, R.Pu{seen, next})), 12n+sd)
    == True{} : Bool}

def Reach.push_next_fit.step(+t: List<&2, U32>, +sd: Nat,
  +seen: S.PSet, +next: List<&2, U32>, +w: U32, +have: Bool,
  +onT: {Sf.Ords.all_fit(
    R.Push.next(R.Reach.push(sd, t, R.Pu{seen, next})), 12n+sd)
    == True{} : Bool},
  +onF: {Sf.Ords.all_fit(R.Push.next(R.Reach.push(sd, t,
    R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), 12n+sd)
    == True{} : Bool})
  -> {Sf.Ords.all_fit(R.Push.next(R.Reach.push(sd, t,
    R.Reach.push.add(sd, w, seen, next, have))), 12n+sd) == True{}
    : Bool}:
  match have:
    case True{}:
      onT
    case False{}:
      onF

def Reach.push_next_fit(ws, sd, seen, next, fw, fn):
  match ws:
    case Nil{}:
      fn
    case Con{w, t}:
      Reach.push_next_fit.step(t, sd, seen, next, w,
        S.PSet.member(sd, seen, w),
        Reach.push_next_fit(t, sd, seen, next,
          E.Bool.and_r(Dc.U32.hi_zero(w, 12n+sd),
            Sf.Ords.all_fit(t, 12n+sd), fw), fn),
        Reach.push_next_fit(t, sd, S.PSet.insert(sd, seen, w),
          Con{w, next},
          E.Bool.and_r(Dc.U32.hi_zero(w, 12n+sd),
            Sf.Ords.all_fit(t, 12n+sd), fw),
          E.Bool.and_both(Dc.U32.hi_zero(w, 12n+sd),
            Sf.Ords.all_fit(next, 12n+sd),
            E.Bool.and_l(Dc.U32.hi_zero(w, 12n+sd),
              Sf.Ords.all_fit(t, 12n+sd), fw), fn)))

# ---------------------------------------------------------------------------
# The traversal never leaves an edge-closed set it started inside.
# ---------------------------------------------------------------------------

law Reach.go_inside:
  for +fuel: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +xx: S.PSet
  for +seen: S.PSet
  for +front: List<&2, U32>
  for +next: List<&2, U32>
  for +levels: R.Levels
  for +rounds: Nat
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, xx, True{}) == True{} : Bool}
  for +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool}
  for +cl: {Sp.Spec.closed(td, g, sd, xx) == True{} : Bool}
  for +sx: {S.PSet.is_subset(sd, seen, xx) == True{} : Bool}
  for +fx: {Sc.Ords.all_mem(front, sd, xx) == True{} : Bool}
  for +nx: {Sc.Ords.all_mem(next, sd, xx) == True{} : Bool}
  for +ffit: {Sf.Ords.all_fit(front, 12n+sd) == True{} : Bool}
  for +nfit: {Sf.Ords.all_fit(next, 12n+sd) == True{} : Bool}
  {S.PSet.is_subset(sd, R.Reach.seen(sd,
    R.Reach.go(fuel, td, g, sd, seen, front, next, levels, rounds)),
    xx) == True{} : Bool}

def Reach.go_inside(fuel, td, sd, g, xx, seen, front, next, levels,
  rounds, gf, lt, vx, vs, cl, sx, fx, nx, ffit, nfit):
  match fuel:
    case 0n:
      sx
    case 1n+f:
      match front:
        case Con{v, t}:
          Reach.go_inside(f, td, sd, g, xx,
            R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
              R.Pu{seen, next})), t,
            R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
              R.Pu{seen, next})), levels, rounds, gf, lt, vx,
            Reach.push_valid(G.Graph.succ(td, g, v), sd, seen, next,
              lt, Gr.Graph.succ_fits(td, sd, g, v, gf), vs), cl,
            Reach.push_inside(G.Graph.succ(td, g, v), sd, seen, next,
              xx, lt, Gr.Graph.succ_fits(td, sd, g, v, gf), vs, vx,
              Ords.succ_inside(G.Graph.succ(td, g, v), td, sd, g, xx,
                v, gf, lt, vx, cl,
                E.Bool.and_l(S.PSet.member(sd, xx, v),
                  Sc.Ords.all_mem(t, sd, xx), fx),
                E.Bool.and_l(Dc.U32.hi_zero(v, 12n+sd),
                  Sf.Ords.all_fit(t, 12n+sd), ffit),
                Sa.Ords.all_in_self(G.Graph.succ(td, g, v))), sx),
            E.Bool.and_r(S.PSet.member(sd, xx, v),
              Sc.Ords.all_mem(t, sd, xx), fx),
            Reach.push_next_inside(G.Graph.succ(td, g, v), sd, seen,
              next, xx,
              Ords.succ_inside(G.Graph.succ(td, g, v), td, sd, g, xx,
                v, gf, lt, vx, cl,
                E.Bool.and_l(S.PSet.member(sd, xx, v),
                  Sc.Ords.all_mem(t, sd, xx), fx),
                E.Bool.and_l(Dc.U32.hi_zero(v, 12n+sd),
                  Sf.Ords.all_fit(t, 12n+sd), ffit),
                Sa.Ords.all_in_self(G.Graph.succ(td, g, v))), nx),
            E.Bool.and_r(Dc.U32.hi_zero(v, 12n+sd),
              Sf.Ords.all_fit(t, 12n+sd), ffit),
            Reach.push_next_fit(G.Graph.succ(td, g, v), sd, seen,
              next, Gr.Graph.succ_fits(td, sd, g, v, gf), nfit))
        case Nil{}:
          match next:
            case Nil{}:
              sx
            case Con{n0, nt}:
              Reach.go_inside(f, td, sd, g, xx, seen, Con{n0, nt},
                Nil{}, Con{Con{n0, nt}, levels}, 1n+rounds, gf, lt,
                vx, vs, cl, sx, nx, {==}, nfit, {==})

# ---------------------------------------------------------------------------
# What the frontier is for: every vertex seen has either been expanded or is
# still waiting.
# ---------------------------------------------------------------------------

def Reach.settled(+td: Nat, +g: G.Graph(), +sd: Nat, +seen: S.PSet,
  +l: List<&2, U32>, +pend: List<&2, U32>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case Con{v, u}:
      Bool.and(Bool.or(
        Sc.Ords.all_mem(G.Graph.succ(td, g, v), sd, seen),
        List.contains(~U32, ~U32.is_eq, pend, v)),
        Reach.settled(td, g, sd, seen, u, pend))

law Reach.settled_at:
  for +l: List<&2, U32>
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +seen: S.PSet
  for +pend: List<&2, U32>
  for +y: U32
  for +st: {Reach.settled(td, g, sd, seen, l, pend) == True{} : Bool}
  for c: {List.contains(~U32, ~U32.is_eq, l, y) == True{} : Bool}
  {Bool.or(Sc.Ords.all_mem(G.Graph.succ(td, g, y), sd, seen),
    List.contains(~U32, ~U32.is_eq, pend, y)) == True{} : Bool}

def Reach.settled_at.pick(+u: List<&2, U32>, +td: Nat,
  +g: G.Graph(), +sd: Nat, +seen: S.PSet, +pend: List<&2, U32>,
  +y: U32, +v: U32, +e: Bool, +ee: {e == U32.is_eq(v, y) : Bool},
  +hd: {Bool.or(Sc.Ords.all_mem(G.Graph.succ(td, g, v), sd, seen),
    List.contains(~U32, ~U32.is_eq, pend, v)) == True{} : Bool},
  ih: {List.contains(~U32, ~U32.is_eq, u, y) == True{} : Bool} ->
    {Bool.or(Sc.Ords.all_mem(G.Graph.succ(td, g, y), sd, seen),
      List.contains(~U32, ~U32.is_eq, pend, y)) == True{} : Bool},
  +c: {List.contains(~U32, ~U32.is_eq, Con{v, u}, y) == True{}
    : Bool})
  -> {Bool.or(Sc.Ords.all_mem(G.Graph.succ(td, g, y), sd, seen),
    List.contains(~U32, ~U32.is_eq, pend, y)) == True{} : Bool}:
  match e:
    case True{}:
      %E.U32.eq_reflect(v, y,
        E.Bool.sym(True{}, U32.is_eq(v, y), ee))
        : {Bool.or(Sc.Ords.all_mem(G.Graph.succ(td, g, _), sd, seen),
            List.contains(~U32, ~U32.is_eq, pend, _)) == True{}
          : Bool}
      hd
    case False{}:
      ih(Sc.Ords.contains_tail(v, u, y, ee, c))

def Reach.settled_at(l, td, g, sd, seen, pend, y, st, c):
  match l:
    case Nil{}:
      E.Bool.noconf({Bool.or(
        Sc.Ords.all_mem(G.Graph.succ(td, g, y), sd, seen),
        List.contains(~U32, ~U32.is_eq, pend, y)) == True{} : Bool},
        c)
    case Con{v, u}:
      Reach.settled_at.pick(u, td, g, sd, seen, pend, y, v,
        U32.is_eq(v, y), {==},
        E.Bool.and_l(Bool.or(
          Sc.Ords.all_mem(G.Graph.succ(td, g, v), sd, seen),
          List.contains(~U32, ~U32.is_eq, pend, v)),
          Reach.settled(td, g, sd, seen, u, pend), st),
        Reach.settled_at(u, td, g, sd, seen, pend, y,
          E.Bool.and_r(Bool.or(
            Sc.Ords.all_mem(G.Graph.succ(td, g, v), sd, seen),
            List.contains(~U32, ~U32.is_eq, pend, v)),
            Reach.settled(td, g, sd, seen, u, pend), st)), c)

law Ords.all_mem_mono:
  for +l: List<&2, U32>
  for +sd: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +va: {S.PSet.valid(sd, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(sd, b, True{}) == True{} : Bool}
  for +ab: {S.PSet.is_subset(sd, a, b) == True{} : Bool}
  for +fl: {Sf.Ords.all_fit(l, 12n+sd) == True{} : Bool}
  for +am: {Sc.Ords.all_mem(l, sd, a) == True{} : Bool}
  {Sc.Ords.all_mem(l, sd, b) == True{} : Bool}

def Ords.all_mem_mono(l, sd, a, b, lt, va, vb, ab, fl, am):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(S.PSet.member(sd, b, y),
        Sc.Ords.all_mem(u, sd, b),
        Sa.PSet.subset_member_at(sd, a, b, y, va, vb, lt,
          E.Bool.and_l(Dc.U32.hi_zero(y, 12n+sd),
            Sf.Ords.all_fit(u, 12n+sd), fl), ab,
          E.Bool.and_l(S.PSet.member(sd, a, y),
            Sc.Ords.all_mem(u, sd, a), am)),
        Ords.all_mem_mono(u, sd, a, b, lt, va, vb, ab,
          E.Bool.and_r(Dc.U32.hi_zero(y, 12n+sd),
            Sf.Ords.all_fit(u, 12n+sd), fl),
          E.Bool.and_r(S.PSet.member(sd, a, y),
            Sc.Ords.all_mem(u, sd, a), am)))

law Ords.mem_of_any_succ:
  for +l: List<&2, U32>
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +seen: S.PSet
  for +z: U32
  for +st: {Reach.settled(td, g, sd, seen, l, Nil{}) == True{}
    : Bool}
  for any: {Gr.Graph.any_succ(td, g, l, z) == True{} : Bool}
  {S.PSet.member(sd, seen, z) == True{} : Bool}

def Ords.mem_of_any_succ.pick(+u: List<&2, U32>, +td: Nat,
  +sd: Nat, +g: G.Graph(), +seen: S.PSet, +z: U32, +v: U32,
  +e: Bool,
  +ee: {e == List.contains(~U32, ~U32.is_eq,
    G.Graph.succ(td, g, v), z) : Bool},
  +hd: {Bool.or(Sc.Ords.all_mem(G.Graph.succ(td, g, v), sd, seen),
    False{}) == True{} : Bool},
  ih: {Gr.Graph.any_succ(td, g, u, z) == True{} : Bool} ->
    {S.PSet.member(sd, seen, z) == True{} : Bool},
  +any: {Gr.Graph.any_succ(td, g, Con{v, u}, z) == True{} : Bool})
  -> {S.PSet.member(sd, seen, z) == True{} : Bool}:
  match e:
    case True{}:
      Sc.Ords.all_mem_at(G.Graph.succ(td, g, v), sd, seen, z,
        Sc.Ords.head_eq(G.Graph.succ(td, g, v), z), {==},
        %Te.Bool.or_false_r(
          Sc.Ords.all_mem(G.Graph.succ(td, g, v), sd, seen))
          : {_ == True{} : Bool}
        hd,
        E.Bool.sym(True{}, List.contains(~U32, ~U32.is_eq,
          G.Graph.succ(td, g, v), z), ee))
    case False{}:
      ih(%E.Bool.sym(False{}, List.contains(~U32, ~U32.is_eq,
          G.Graph.succ(td, g, v), z), ee)
        : {Bool.or(_, Gr.Graph.any_succ(td, g, u, z)) == True{}
          : Bool}
        any)

def Ords.mem_of_any_succ(l, td, sd, g, seen, z, st, any):
  match l:
    case Nil{}:
      E.Bool.noconf({S.PSet.member(sd, seen, z) == True{} : Bool},
        any)
    case Con{v, u}:
      Ords.mem_of_any_succ.pick(u, td, sd, g, seen, z, v,
        List.contains(~U32, ~U32.is_eq, G.Graph.succ(td, g, v), z),
        {==},
        E.Bool.and_l(Bool.or(
          Sc.Ords.all_mem(G.Graph.succ(td, g, v), sd, seen),
          False{}),
          Reach.settled(td, g, sd, seen, u, Nil{}), st),
        Ords.mem_of_any_succ(u, td, sd, g, seen, z,
          E.Bool.and_r(Bool.or(
            Sc.Ords.all_mem(G.Graph.succ(td, g, v), sd, seen),
            False{}),
            Reach.settled(td, g, sd, seen, u, Nil{}), st)), any)

law Reach.closed_of_settled:
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +seen: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool}
  for +st: {Reach.settled(td, g, sd, seen,
    S.PSet.to_list(sd, seen), Nil{}) == True{} : Bool}
  {Sp.Spec.closed(td, g, sd, seen) == True{} : Bool}

law Ords.all_mem_post_settled:
  for +l: List<&2, U32>
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +seen: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool}
  for +st: {Reach.settled(td, g, sd, seen,
    S.PSet.to_list(sd, seen), Nil{}) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l,
    S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, seen))) == True{}
    : Bool}
  {Sc.Ords.all_mem(l, sd, seen) == True{} : Bool}

def Ords.all_mem_post_settled(l, td, sd, g, seen, gf, lt, vs, st,
  ai):
  match l:
    case Nil{}:
      {==}
    case Con{z, u}:
      E.Bool.and_both(S.PSet.member(sd, seen, z),
        Sc.Ords.all_mem(u, sd, seen),
        Ords.mem_of_any_succ(S.PSet.to_list(sd, seen), td, sd, g,
          seen, z, st,
          Pm.Spec.any_of_post(td, sd, g, seen, z, gf, lt,
            Sa.PSet.in_range_of_to_list(sd,
              Sp.Spec.post(td, g, sd, seen), z,
              Pm.Spec.post_valid(td, sd, g, seen, gf, lt), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, seen)),
                z), Sa.Ords.all_in(u, S.PSet.to_list(sd,
                  Sp.Spec.post(td, g, sd, seen))), ai)),
            Sa.PSet.member_of_to_list(sd,
              Sp.Spec.post(td, g, sd, seen), z,
              Pm.Spec.post_valid(td, sd, g, seen, gf, lt), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, seen)),
                z), Sa.Ords.all_in(u, S.PSet.to_list(sd,
                  Sp.Spec.post(td, g, sd, seen))), ai)))),
        Ords.all_mem_post_settled(u, td, sd, g, seen, gf, lt, vs, st,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, seen)), z),
            Sa.Ords.all_in(u, S.PSet.to_list(sd,
              Sp.Spec.post(td, g, sd, seen))), ai)))

def Reach.closed_of_settled(td, sd, g, seen, gf, lt, vs, st):
  Sc.PSet.subset_of_members(sd, Sp.Spec.post(td, g, sd, seen), seen,
    Pm.Spec.post_valid(td, sd, g, seen, gf, lt), vs, lt,
    Ords.all_mem_post_settled(
      S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, seen)), td, sd, g,
      seen, gf, lt, vs, st,
      Sa.Ords.all_in_self(
        S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, seen)))))

# ---------------------------------------------------------------------------
# One expansion keeps the invariant.
# ---------------------------------------------------------------------------

def Reach.head_new.pick(+td: Nat, +sd: Nat, +g: G.Graph(), +v: U32,
  +t: List<&2, U32>, +next: List<&2, U32>, +seen: S.PSet, +u: U32,
  +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool},
  +d4: Bool,
  +e4: {d4 == List.contains(~U32, ~U32.is_eq, t, u) : Bool},
  +inn: {List.contains(~U32, ~U32.is_eq,
    List.append(&2, U32, t, next), u) == True{} : Bool})
  -> {Bool.or(List.contains(~U32, ~U32.is_eq, t, u),
    List.contains(~U32, ~U32.is_eq,
      R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
        R.Pu{seen, next})), u)) == True{} : Bool}:
  match d4:
    case True{}:
      Sa.Ords.or_left(List.contains(~U32, ~U32.is_eq, t, u),
        List.contains(~U32, ~U32.is_eq,
          R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
            R.Pu{seen, next})), u),
        E.Bool.sym(True{}, List.contains(~U32, ~U32.is_eq, t, u),
          e4))
    case False{}:
      Sa.Ords.or_right(List.contains(~U32, ~U32.is_eq, t, u),
        List.contains(~U32, ~U32.is_eq,
          R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
            R.Pu{seen, next})), u),
        Reach.push_next_grows(G.Graph.succ(td, g, v), sd, seen, next,
          u,
          %E.Bool.sym(False{}, List.contains(~U32, ~U32.is_eq, t, u),
            e4)
            : {Bool.or(_, List.contains(~U32, ~U32.is_eq, next, u))
              == True{} : Bool}
          %Le.List.contains_append(t, next, u) : {_ == True{} : Bool}
          inn))

def Reach.head_new.tail(+td: Nat, +sd: Nat, +g: G.Graph(), +v: U32,
  +t: List<&2, U32>, +next: List<&2, U32>, +seen: S.PSet, +u: U32,
  +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool},
  +invu: {Dc.U32.hi_zero(u, 12n+sd) == True{} : Bool},
  +st: {Reach.settled(td, g, sd, seen, S.PSet.to_list(sd, seen),
    Con{v, List.append(&2, U32, t, next)}) == True{} : Bool},
  +e1: {True{} == S.PSet.member(sd, seen, u) : Bool},
  +e2: {False{}
    == Sc.Ords.all_mem(G.Graph.succ(td, g, u), sd, seen) : Bool},
  +e3: {False{} == U32.is_eq(v, u) : Bool},
  +d4: Bool,
  +e4: {d4 == List.contains(~U32, ~U32.is_eq, t, u) : Bool})
  -> {Bool.or(Sc.Ords.all_mem(G.Graph.succ(td, g, u), sd,
    R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
      R.Pu{seen, next}))),
    List.contains(~U32, ~U32.is_eq, List.append(&2, U32, t,
      R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
        R.Pu{seen, next}))), u)) == True{} : Bool}:
  Sa.Ords.or_right(Sc.Ords.all_mem(G.Graph.succ(td, g, u), sd,
    R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
      R.Pu{seen, next}))),
    List.contains(~U32, ~U32.is_eq, List.append(&2, U32, t,
      R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
        R.Pu{seen, next}))), u),
    %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
        List.append(&2, U32, t,
          R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
            R.Pu{seen, next}))), u),
      Bool.or(List.contains(~U32, ~U32.is_eq, t, u),
        List.contains(~U32, ~U32.is_eq,
          R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
            R.Pu{seen, next})), u)),
      Le.List.contains_append(t,
        R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
          R.Pu{seen, next})), u)) : {_ == True{} : Bool}
    Reach.head_new.pick(td, sd, g, v, t, next, seen, u, gf, lt, vs,
      d4, e4,
      %E.Bool.sym(False{}, U32.is_eq(v, u), e3)
        : {Bool.or(_, List.contains(~U32, ~U32.is_eq,
            List.append(&2, U32, t, next), u)) == True{} : Bool}
      %E.Bool.sym(False{},
        Sc.Ords.all_mem(G.Graph.succ(td, g, u), sd, seen), e2)
        : {Bool.or(_, List.contains(~U32, ~U32.is_eq,
            Con{v, List.append(&2, U32, t, next)}, u)) == True{}
          : Bool}
      Reach.settled_at(S.PSet.to_list(sd, seen), td, g, sd, seen,
        Con{v, List.append(&2, U32, t, next)}, u, st,
        Pm.Ords.in_of_member(sd, seen, u, vs, lt, invu,
          E.Bool.sym(True{}, S.PSet.member(sd, seen, u), e1)))))

def Reach.head_new(+td: Nat, +sd: Nat, +g: G.Graph(), +v: U32,
  +t: List<&2, U32>, +next: List<&2, U32>, +seen: S.PSet, +u: U32,
  +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool},
  +invu: {Dc.U32.hi_zero(u, 12n+sd) == True{} : Bool},
  +st: {Reach.settled(td, g, sd, seen, S.PSet.to_list(sd, seen),
    Con{v, List.append(&2, U32, t, next)}) == True{} : Bool},
  +d1: Bool, +e1: {d1 == S.PSet.member(sd, seen, u) : Bool},
  +d2: Bool,
  +e2: {d2 == Sc.Ords.all_mem(G.Graph.succ(td, g, u), sd, seen)
    : Bool},
  +d3: Bool, +e3: {d3 == U32.is_eq(v, u) : Bool},
  +d4: Bool,
  +e4: {d4 == List.contains(~U32, ~U32.is_eq, t, u) : Bool},
  +sp: {Bool.or(S.PSet.member(sd, seen, u),
    List.contains(~U32, ~U32.is_eq,
      R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
        R.Pu{seen, next})), u)) == True{} : Bool})
  -> {Bool.or(Sc.Ords.all_mem(G.Graph.succ(td, g, u), sd,
    R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
      R.Pu{seen, next}))),
    List.contains(~U32, ~U32.is_eq, List.append(&2, U32, t,
      R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
        R.Pu{seen, next}))), u)) == True{} : Bool}:
  match d1:
    case False{}:
      Sa.Ords.or_right(Sc.Ords.all_mem(G.Graph.succ(td, g, u), sd,
        R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
          R.Pu{seen, next}))),
        List.contains(~U32, ~U32.is_eq, List.append(&2, U32, t,
          R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
            R.Pu{seen, next}))), u),
        %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
            List.append(&2, U32, t,
              R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
                R.Pu{seen, next}))), u),
          Bool.or(List.contains(~U32, ~U32.is_eq, t, u),
            List.contains(~U32, ~U32.is_eq,
              R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
                R.Pu{seen, next})), u)),
          Le.List.contains_append(t,
            R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
              R.Pu{seen, next})), u)) : {_ == True{} : Bool}
        Sa.Ords.or_right(List.contains(~U32, ~U32.is_eq, t, u),
          List.contains(~U32, ~U32.is_eq,
            R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
              R.Pu{seen, next})), u),
          %E.Bool.sym(False{}, S.PSet.member(sd, seen, u), e1)
            : {Bool.or(_, List.contains(~U32, ~U32.is_eq,
                R.Push.next(R.Reach.push(sd,
                  G.Graph.succ(td, g, v), R.Pu{seen, next})), u))
              == True{} : Bool}
          sp))
    case True{}:
      match d2:
        case True{}:
          Sa.Ords.or_left(Sc.Ords.all_mem(G.Graph.succ(td, g, u), sd,
            R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
              R.Pu{seen, next}))),
            List.contains(~U32, ~U32.is_eq, List.append(&2, U32, t,
              R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
                R.Pu{seen, next}))), u),
            Ords.all_mem_mono(G.Graph.succ(td, g, u), sd, seen,
              R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
                R.Pu{seen, next})), lt, vs,
              Reach.push_valid(G.Graph.succ(td, g, v), sd, seen,
                next, lt, Gr.Graph.succ_fits(td, sd, g, v, gf), vs),
              Reach.push_grows(G.Graph.succ(td, g, v), sd, seen,
                next, lt, Gr.Graph.succ_fits(td, sd, g, v, gf), vs),
              Gr.Graph.succ_fits(td, sd, g, u, gf),
              E.Bool.sym(True{},
                Sc.Ords.all_mem(G.Graph.succ(td, g, u), sd, seen),
                e2)))
        case False{}:
          match d3:
            case True{}:
              Sa.Ords.or_left(
                Sc.Ords.all_mem(G.Graph.succ(td, g, u), sd,
                  R.Push.seen(R.Reach.push(sd,
                    G.Graph.succ(td, g, v), R.Pu{seen, next}))),
                List.contains(~U32, ~U32.is_eq,
                  List.append(&2, U32, t,
                    R.Push.next(R.Reach.push(sd,
                      G.Graph.succ(td, g, v), R.Pu{seen, next}))),
                  u),
                %E.U32.eq_reflect(v, u,
                  E.Bool.sym(True{}, U32.is_eq(v, u), e3))
                  : {Sc.Ords.all_mem(G.Graph.succ(td, g, _), sd,
                      R.Push.seen(R.Reach.push(sd,
                        G.Graph.succ(td, g, v), R.Pu{seen, next})))
                    == True{} : Bool}
                Reach.push_covers(G.Graph.succ(td, g, v), sd, seen,
                  next, lt, Gr.Graph.succ_fits(td, sd, g, v, gf),
                  vs))
            case False{}:
              Reach.head_new.tail(td, sd, g, v, t, next, seen, u, gf,
                lt, vs, invu, st, e1, e2, e3, d4, e4)

law List.append_nil:
  for +l: List<&2, U32>
  {List.append(&2, U32, l, Nil{}) == l : List<&2, U32>}

def List.append_nil(l):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      %E.List.sym(U32, List.append(&2, U32, u, Nil{}), u,
        List.append_nil(u))
        : {Con{y, _} == Con{y, u} : List<&2, U32>}
      {==}

law Reach.settled_new:
  for +l: List<&2, U32>
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +v: U32
  for +t: List<&2, U32>
  for +next: List<&2, U32>
  for +seen: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool}
  for +st: {Reach.settled(td, g, sd, seen, S.PSet.to_list(sd, seen),
    Con{v, List.append(&2, U32, t, next)}) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l, S.PSet.to_list(sd,
    R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
      R.Pu{seen, next})))) == True{} : Bool}
  {Reach.settled(td, g, sd,
    R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
      R.Pu{seen, next})), l, List.append(&2, U32, t,
      R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
        R.Pu{seen, next})))) == True{} : Bool}

def Reach.settled_new(l, td, sd, g, v, t, next, seen, gf, lt, vs,
  st, ai):
  match l:
    case Nil{}:
      {==}
    case Con{u, rest}:
      E.Bool.and_both(Bool.or(
        Sc.Ords.all_mem(G.Graph.succ(td, g, u), sd,
          R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
            R.Pu{seen, next}))),
        List.contains(~U32, ~U32.is_eq, List.append(&2, U32, t,
          R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
            R.Pu{seen, next}))), u)),
        Reach.settled(td, g, sd,
          R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
            R.Pu{seen, next})), rest, List.append(&2, U32, t,
            R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
              R.Pu{seen, next})))),
        Reach.head_new(td, sd, g, v, t, next, seen, u, gf, lt, vs,
          Sa.PSet.in_range_of_to_list(sd,
            R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
              R.Pu{seen, next})), u,
            Reach.push_valid(G.Graph.succ(td, g, v), sd, seen, next,
              lt, Gr.Graph.succ_fits(td, sd, g, v, gf), vs), lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(sd,
                R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
                  R.Pu{seen, next}))), u),
              Sa.Ords.all_in(rest, S.PSet.to_list(sd,
                R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
                  R.Pu{seen, next})))), ai)), st,
          S.PSet.member(sd, seen, u), {==},
          Sc.Ords.all_mem(G.Graph.succ(td, g, u), sd, seen), {==},
          U32.is_eq(v, u), {==},
          List.contains(~U32, ~U32.is_eq, t, u), {==},
          Reach.push_split(G.Graph.succ(td, g, v), sd, seen, next, u,
            lt, Gr.Graph.succ_fits(td, sd, g, v, gf), vs,
            Sa.PSet.in_range_of_to_list(sd,
              R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
                R.Pu{seen, next})), u,
              Reach.push_valid(G.Graph.succ(td, g, v), sd, seen,
                next, lt, Gr.Graph.succ_fits(td, sd, g, v, gf), vs),
              lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(sd,
                  R.Push.seen(R.Reach.push(sd,
                    G.Graph.succ(td, g, v), R.Pu{seen, next}))), u),
                Sa.Ords.all_in(rest, S.PSet.to_list(sd,
                  R.Push.seen(R.Reach.push(sd,
                    G.Graph.succ(td, g, v), R.Pu{seen, next})))),
                ai)),
            Sa.PSet.member_of_to_list(sd,
              R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
                R.Pu{seen, next})), u,
              Reach.push_valid(G.Graph.succ(td, g, v), sd, seen,
                next, lt, Gr.Graph.succ_fits(td, sd, g, v, gf), vs),
              lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(sd,
                  R.Push.seen(R.Reach.push(sd,
                    G.Graph.succ(td, g, v), R.Pu{seen, next}))), u),
                Sa.Ords.all_in(rest, S.PSet.to_list(sd,
                  R.Push.seen(R.Reach.push(sd,
                    G.Graph.succ(td, g, v), R.Pu{seen, next})))),
                ai)))),
        Reach.settled_new(rest, td, sd, g, v, t, next, seen, gf, lt,
          vs, st,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(sd,
              R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
                R.Pu{seen, next}))), u),
            Sa.Ords.all_in(rest, S.PSet.to_list(sd,
              R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
                R.Pu{seen, next})))), ai)))

# ---------------------------------------------------------------------------
# The whole walk.
# ---------------------------------------------------------------------------

law Reach.go_valid:
  for +fuel: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +seen: S.PSet
  for +front: List<&2, U32>
  for +next: List<&2, U32>
  for +levels: R.Levels
  for +rounds: Nat
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool}
  for +ffit: {Sf.Ords.all_fit(front, 12n+sd) == True{} : Bool}
  for +nfit: {Sf.Ords.all_fit(next, 12n+sd) == True{} : Bool}
  {S.PSet.valid(sd, R.Reach.seen(sd,
    R.Reach.go(fuel, td, g, sd, seen, front, next, levels, rounds)),
    True{}) == True{} : Bool}

def Reach.go_valid(fuel, td, sd, g, seen, front, next, levels,
  rounds, gf, lt, vs, ffit, nfit):
  match fuel:
    case 0n:
      vs
    case 1n+f:
      match front:
        case Con{v, t}:
          Reach.go_valid(f, td, sd, g,
            R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
              R.Pu{seen, next})), t,
            R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
              R.Pu{seen, next})), levels, rounds, gf, lt,
            Reach.push_valid(G.Graph.succ(td, g, v), sd, seen, next,
              lt, Gr.Graph.succ_fits(td, sd, g, v, gf), vs),
            E.Bool.and_r(Dc.U32.hi_zero(v, 12n+sd),
              Sf.Ords.all_fit(t, 12n+sd), ffit),
            Reach.push_next_fit(G.Graph.succ(td, g, v), sd, seen,
              next, Gr.Graph.succ_fits(td, sd, g, v, gf), nfit))
        case Nil{}:
          match next:
            case Nil{}:
              vs
            case Con{n0, nt}:
              Reach.go_valid(f, td, sd, g, seen, Con{n0, nt}, Nil{},
                Con{Con{n0, nt}, levels}, 1n+rounds, gf, lt, vs,
                nfit, {==})

law Reach.go_grows:
  for +fuel: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +seen: S.PSet
  for +front: List<&2, U32>
  for +next: List<&2, U32>
  for +levels: R.Levels
  for +rounds: Nat
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool}
  for +ffit: {Sf.Ords.all_fit(front, 12n+sd) == True{} : Bool}
  for +nfit: {Sf.Ords.all_fit(next, 12n+sd) == True{} : Bool}
  {S.PSet.is_subset(sd, seen, R.Reach.seen(sd,
    R.Reach.go(fuel, td, g, sd, seen, front, next, levels, rounds)))
    == True{} : Bool}

def Reach.go_grows(fuel, td, sd, g, seen, front, next, levels,
  rounds, gf, lt, vs, ffit, nfit):
  match fuel:
    case 0n:
      Lp.PSet.subset_refl(sd, seen, vs, lt)
    case 1n+f:
      match front:
        case Con{v, t}:
          Sa.PSet.subset_trans(sd, seen,
            R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
              R.Pu{seen, next})),
            R.Reach.seen(sd, R.Reach.go(f, td, g, sd,
              R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
                R.Pu{seen, next})), t,
              R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
                R.Pu{seen, next})), levels, rounds)), vs,
            Reach.push_valid(G.Graph.succ(td, g, v), sd, seen, next,
              lt, Gr.Graph.succ_fits(td, sd, g, v, gf), vs),
            Reach.go_valid(f, td, sd, g,
              R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
                R.Pu{seen, next})), t,
              R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
                R.Pu{seen, next})), levels, rounds, gf, lt,
              Reach.push_valid(G.Graph.succ(td, g, v), sd, seen,
                next, lt, Gr.Graph.succ_fits(td, sd, g, v, gf), vs),
              E.Bool.and_r(Dc.U32.hi_zero(v, 12n+sd),
                Sf.Ords.all_fit(t, 12n+sd), ffit),
              Reach.push_next_fit(G.Graph.succ(td, g, v), sd, seen,
                next, Gr.Graph.succ_fits(td, sd, g, v, gf), nfit)),
            lt,
            Reach.push_grows(G.Graph.succ(td, g, v), sd, seen, next,
              lt, Gr.Graph.succ_fits(td, sd, g, v, gf), vs),
            Reach.go_grows(f, td, sd, g,
              R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
                R.Pu{seen, next})), t,
              R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
                R.Pu{seen, next})), levels, rounds, gf, lt,
              Reach.push_valid(G.Graph.succ(td, g, v), sd, seen,
                next, lt, Gr.Graph.succ_fits(td, sd, g, v, gf), vs),
              E.Bool.and_r(Dc.U32.hi_zero(v, 12n+sd),
                Sf.Ords.all_fit(t, 12n+sd), ffit),
              Reach.push_next_fit(G.Graph.succ(td, g, v), sd, seen,
                next, Gr.Graph.succ_fits(td, sd, g, v, gf), nfit)))
        case Nil{}:
          match next:
            case Nil{}:
              Lp.PSet.subset_refl(sd, seen, vs, lt)
            case Con{n0, nt}:
              Reach.go_grows(f, td, sd, g, seen, Con{n0, nt}, Nil{},
                Con{Con{n0, nt}, levels}, 1n+rounds, gf, lt, vs,
                nfit, {==})

law Reach.go_settled:
  for +fuel: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +seen: S.PSet
  for +front: List<&2, U32>
  for +next: List<&2, U32>
  for +levels: R.Levels
  for +rounds: Nat
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vs: {S.PSet.valid(sd, seen, True{}) == True{} : Bool}
  for +ffit: {Sf.Ords.all_fit(front, 12n+sd) == True{} : Bool}
  for +nfit: {Sf.Ords.all_fit(next, 12n+sd) == True{} : Bool}
  for +st: {Reach.settled(td, g, sd, seen, S.PSet.to_list(sd, seen),
    List.append(&2, U32, front, next)) == True{} : Bool}
  for +done: {R.Reach.done(sd, R.Reach.go(fuel, td, g, sd, seen,
    front, next, levels, rounds)) == True{} : Bool}
  {Sp.Spec.closed(td, g, sd, R.Reach.seen(sd, R.Reach.go(fuel, td,
    g, sd, seen, front, next, levels, rounds))) == True{} : Bool}

def Reach.go_settled(fuel, td, sd, g, seen, front, next, levels,
  rounds, gf, lt, vs, ffit, nfit, st, done):
  match fuel:
    case 0n:
      E.Bool.noconf({Sp.Spec.closed(td, g, sd, seen) == True{}
        : Bool}, done)
    case 1n+f:
      match front:
        case Con{v, t}:
          Reach.go_settled(f, td, sd, g,
            R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
              R.Pu{seen, next})), t,
            R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
              R.Pu{seen, next})), levels, rounds, gf, lt,
            Reach.push_valid(G.Graph.succ(td, g, v), sd, seen, next,
              lt, Gr.Graph.succ_fits(td, sd, g, v, gf), vs),
            E.Bool.and_r(Dc.U32.hi_zero(v, 12n+sd),
              Sf.Ords.all_fit(t, 12n+sd), ffit),
            Reach.push_next_fit(G.Graph.succ(td, g, v), sd, seen,
              next, Gr.Graph.succ_fits(td, sd, g, v, gf), nfit),
            Reach.settled_new(S.PSet.to_list(sd,
              R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
                R.Pu{seen, next}))), td, sd, g, v, t, next, seen, gf,
              lt, vs, st,
              Sa.Ords.all_in_self(S.PSet.to_list(sd,
                R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
                  R.Pu{seen, next}))))), done)
        case Nil{}:
          match next:
            case Nil{}:
              Reach.closed_of_settled(td, sd, g, seen, gf, lt, vs,
                st)
            case Con{n0, nt}:
              Reach.go_settled(f, td, sd, g, seen, Con{n0, nt},
                Nil{}, Con{Con{n0, nt}, levels}, 1n+rounds, gf, lt,
                vs, nfit, {==},
                %E.List.sym(U32,
                  List.append(&2, U32, Con{n0, nt}, Nil{}),
                  Con{n0, nt},
                  List.append_nil(Con{n0, nt}))
                  : {Reach.settled(td, g, sd, seen,
                    S.PSet.to_list(sd, seen), _) == True{} : Bool}
                st, done)

law Reach.settled_init:
  for +l: List<&2, U32>
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +roots: List<&2, U32>
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +rfit: {Sf.Ords.all_fit(roots, 12n+sd) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l,
    S.PSet.to_list(sd, S.PSet.from_list(sd, roots))) == True{}
    : Bool}
  {Reach.settled(td, g, sd, S.PSet.from_list(sd, roots), l,
    List.append(&2, U32, roots, Nil{})) == True{} : Bool}

def Reach.settled_init(l, td, sd, g, roots, lt, rfit, ai):
  match l:
    case Nil{}:
      {==}
    case Con{u, rest}:
      E.Bool.and_both(Bool.or(
        Sc.Ords.all_mem(G.Graph.succ(td, g, u), sd,
          S.PSet.from_list(sd, roots)),
        List.contains(~U32, ~U32.is_eq,
          List.append(&2, U32, roots, Nil{}), u)),
        Reach.settled(td, g, sd, S.PSet.from_list(sd, roots), rest,
          List.append(&2, U32, roots, Nil{})),
        Sa.Ords.or_right(Sc.Ords.all_mem(G.Graph.succ(td, g, u), sd,
          S.PSet.from_list(sd, roots)),
          List.contains(~U32, ~U32.is_eq,
            List.append(&2, U32, roots, Nil{}), u),
          %E.List.sym(U32, List.append(&2, U32, roots, Nil{}),
            roots, List.append_nil(roots))
            : {List.contains(~U32, ~U32.is_eq, _, u) == True{}
              : Bool}
          Ls.PSet.from_list_only_at(roots, sd, u, lt,
            Sa.PSet.in_range_of_to_list(sd,
              S.PSet.from_list(sd, roots), u,
              Iv.PSet.valid_from_list(roots, sd, lt, rfit), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(sd, S.PSet.from_list(sd, roots)), u),
                Sa.Ords.all_in(rest, S.PSet.to_list(sd,
                  S.PSet.from_list(sd, roots))), ai)), rfit,
            Sa.PSet.member_of_to_list(sd,
              S.PSet.from_list(sd, roots), u,
              Iv.PSet.valid_from_list(roots, sd, lt, rfit), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(sd, S.PSet.from_list(sd, roots)), u),
                Sa.Ords.all_in(rest, S.PSet.to_list(sd,
                  S.PSet.from_list(sd, roots))), ai)))),
        Reach.settled_init(rest, td, sd, g, roots, lt, rfit,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(sd, S.PSet.from_list(sd, roots)), u),
            Sa.Ords.all_in(rest, S.PSet.to_list(sd,
              S.PSet.from_list(sd, roots))), ai)))

law Ords.all_mem_roots:
  for +l: List<&2, U32>
  for +sd: Nat
  for +xx: S.PSet
  for +roots: List<&2, U32>
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +rfit: {Sf.Ords.all_fit(roots, 12n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, xx, True{}) == True{} : Bool}
  for +sub: {S.PSet.is_subset(sd, S.PSet.from_list(sd, roots), xx)
    == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l, roots) == True{} : Bool}
  {Sc.Ords.all_mem(l, sd, xx) == True{} : Bool}

def Ords.all_mem_roots(l, sd, xx, roots, lt, rfit, vx, sub, ai):
  match l:
    case Nil{}:
      {==}
    case Con{u, rest}:
      E.Bool.and_both(S.PSet.member(sd, xx, u),
        Sc.Ords.all_mem(rest, sd, xx),
        Sa.PSet.subset_member_at(sd, S.PSet.from_list(sd, roots), xx,
          u, Iv.PSet.valid_from_list(roots, sd, lt, rfit), vx, lt,
          Fx.Ords.fit_of_contains(roots, 12n+sd, u, rfit,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq, roots, u),
              Sa.Ords.all_in(rest, roots), ai)), sub,
          Ls.PSet.from_list_contains_at(roots, sd, u, lt,
            Fx.Ords.fit_of_contains(roots, 12n+sd, u, rfit,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq, roots, u),
                Sa.Ords.all_in(rest, roots), ai)),
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq, roots, u),
              Sa.Ords.all_in(rest, roots), ai))),
        Ords.all_mem_roots(rest, sd, xx, roots, lt, rfit, vx, sub,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq, roots, u),
            Sa.Ords.all_in(rest, roots), ai)))

law Reach.closure_same:
  for +n: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +roots: List<&2, U32>
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +rfit: {Sf.Ords.all_fit(roots, 12n+sd) == True{} : Bool}
  for +fuel: {C.Nat.upto(
    S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)), 1n+n) == True{}
    : Bool}
  for +done: {R.Reach.done(sd, R.Reach.closure(n, td, g, sd, roots))
    == True{} : Bool}
  {Ca.PSet.same(sd,
    R.Reach.seen(sd, R.Reach.closure(n, td, g, sd, roots)),
    Sp.Spec.closure(n, td, g, sd, S.PSet.from_list(sd, roots)))
    == True{} : Bool}

def Reach.closure_same(n, td, sd, g, roots, gf, lt, rfit, fuel,
  done):
  E.Bool.and_both(S.PSet.is_subset(sd,
    R.Reach.seen(sd, R.Reach.closure(n, td, g, sd, roots)),
    Sp.Spec.closure(n, td, g, sd, S.PSet.from_list(sd, roots))),
    S.PSet.is_subset(sd,
      Sp.Spec.closure(n, td, g, sd, S.PSet.from_list(sd, roots)),
      R.Reach.seen(sd, R.Reach.closure(n, td, g, sd, roots))),
    Reach.go_inside(2n+Nat.add(n, n), td, sd, g,
      Sp.Spec.closure(n, td, g, sd, S.PSet.from_list(sd, roots)),
      S.PSet.from_list(sd, roots), roots, Nil{},
      Con{roots, Nil{}}, 0n, gf, lt,
      Lp.Spec.closure_valid(n, td, sd, g,
        S.PSet.from_list(sd, roots), gf, lt,
        Iv.PSet.valid_from_list(roots, sd, lt, rfit)),
      Iv.PSet.valid_from_list(roots, sd, lt, rfit),
      St.Spec.closure_is_closed(n, td, sd, g,
        S.PSet.from_list(sd, roots), gf, lt,
        Iv.PSet.valid_from_list(roots, sd, lt, rfit), fuel),
      Lp.Spec.closure_contains_roots(n, td, sd, g,
        S.PSet.from_list(sd, roots), gf, lt,
        Iv.PSet.valid_from_list(roots, sd, lt, rfit)),
      Ords.all_mem_roots(roots, sd,
        Sp.Spec.closure(n, td, g, sd, S.PSet.from_list(sd, roots)),
        roots, lt, rfit,
        Lp.Spec.closure_valid(n, td, sd, g,
          S.PSet.from_list(sd, roots), gf, lt,
          Iv.PSet.valid_from_list(roots, sd, lt, rfit)),
        Lp.Spec.closure_contains_roots(n, td, sd, g,
          S.PSet.from_list(sd, roots), gf, lt,
          Iv.PSet.valid_from_list(roots, sd, lt, rfit)),
        Sa.Ords.all_in_self(roots)), {==}, rfit, {==}),
    Lp.Spec.closure_least(n, td, sd, g,
      S.PSet.from_list(sd, roots),
      R.Reach.seen(sd, R.Reach.closure(n, td, g, sd, roots)), gf, lt,
      Iv.PSet.valid_from_list(roots, sd, lt, rfit),
      Reach.go_valid(2n+Nat.add(n, n), td, sd, g,
        S.PSet.from_list(sd, roots), roots, Nil{},
        Con{roots, Nil{}}, 0n, gf, lt,
        Iv.PSet.valid_from_list(roots, sd, lt, rfit), rfit, {==}),
      Reach.go_settled(2n+Nat.add(n, n), td, sd, g,
        S.PSet.from_list(sd, roots), roots, Nil{},
        Con{roots, Nil{}}, 0n, gf, lt,
        Iv.PSet.valid_from_list(roots, sd, lt, rfit), rfit, {==},
        Reach.settled_init(
          S.PSet.to_list(sd, S.PSet.from_list(sd, roots)), td, sd, g,
          roots, lt, rfit,
          Sa.Ords.all_in_self(
            S.PSet.to_list(sd, S.PSet.from_list(sd, roots)))), done),
      Reach.go_grows(2n+Nat.add(n, n), td, sd, g,
        S.PSet.from_list(sd, roots), roots, Nil{},
        Con{roots, Nil{}}, 0n, gf, lt,
        Iv.PSet.valid_from_list(roots, sd, lt, rfit), rfit, {==})))

law Reach.closure_member:
  for +n: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +roots: List<&2, U32>
  for +x: U32
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +rfit: {Sf.Ords.all_fit(roots, 12n+sd) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+sd) == True{} : Bool}
  for +fuel: {C.Nat.upto(
    S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)), 1n+n) == True{}
    : Bool}
  for +done: {R.Reach.done(sd, R.Reach.closure(n, td, g, sd, roots))
    == True{} : Bool}
  {S.PSet.member(sd,
      R.Reach.seen(sd, R.Reach.closure(n, td, g, sd, roots)), x)
    == S.PSet.member(sd,
        Sp.Spec.closure(n, td, g, sd, S.PSet.from_list(sd, roots)),
        x) : Bool}

def Reach.closure_member(n, td, sd, g, roots, x, gf, lt, rfit, inv,
  fuel, done):
  Ca.PSet.member_same(sd,
    R.Reach.seen(sd, R.Reach.closure(n, td, g, sd, roots)),
    Sp.Spec.closure(n, td, g, sd, S.PSet.from_list(sd, roots)), x,
    Reach.go_valid(2n+Nat.add(n, n), td, sd, g,
      S.PSet.from_list(sd, roots), roots, Nil{}, Con{roots, Nil{}},
      0n, gf, lt, Iv.PSet.valid_from_list(roots, sd, lt, rfit), rfit,
      {==}),
    Lp.Spec.closure_valid(n, td, sd, g, S.PSet.from_list(sd, roots),
      gf, lt, Iv.PSet.valid_from_list(roots, sd, lt, rfit)), lt, inv,
    Reach.closure_same(n, td, sd, g, roots, gf, lt, rfit, fuel,
      done))

law Reach.closure_closed:
  for +n: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +roots: List<&2, U32>
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +rfit: {Sf.Ords.all_fit(roots, 12n+sd) == True{} : Bool}
  for +done: {R.Reach.done(sd, R.Reach.closure(n, td, g, sd, roots))
    == True{} : Bool}
  {Sp.Spec.closed(td, g, sd,
    R.Reach.seen(sd, R.Reach.closure(n, td, g, sd, roots)))
    == True{} : Bool}

def Reach.closure_closed(n, td, sd, g, roots, gf, lt, rfit, done):
  Reach.go_settled(2n+Nat.add(n, n), td, sd, g,
    S.PSet.from_list(sd, roots), roots, Nil{}, Con{roots, Nil{}}, 0n,
    gf, lt, Iv.PSet.valid_from_list(roots, sd, lt, rfit), rfit, {==},
    Reach.settled_init(
      S.PSet.to_list(sd, S.PSet.from_list(sd, roots)), td, sd, g,
      roots, lt, rfit,
      Sa.Ords.all_in_self(
        S.PSet.to_list(sd, S.PSet.from_list(sd, roots)))), done)
