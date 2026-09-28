# proofs/settle.bend -- the closure iteration reaches its fixed point.
#
# Each round either changes nothing -- and then it is edge-closed, and stays
# edge-closed however many more rounds are run -- or it adds an ordinal, and
# then the round is strictly bigger than the one before. A set at this depth
# is no bigger than the universe, so only as many strict rounds are possible
# as the universe has ordinals. That is the pigeonhole, and `Spec.closure`
# passes exactly that many rounds plus one.
#
# The measure is `PSet.count` of the universe minus the round, carried as
# "the universe is no bigger than the round plus what is left". The base case
# is not "the round is the universe" but a contradiction: a round that still
# grows would push the count past the universe's.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./count.bend as Ct
import ./childtest.bend as Ct2
import ./nodeenum.bend as Ne
import ./fusedlen.bend as Fl
import ./subsetalg.bend as Sa
import ./validshape.bend as Vs
import ./graphrange.bend as Gr
import ./postmono.bend as Pm
import ./lfp.bend as Lp
import ./closalg.bend as Ca
import ./setcard.bend as Sd
import ../core/count.bend as C
import ../core/set.bend as S
import ../closure/graph.bend as G
import ../spec/closure.bend as Sp

def Ords.len(l: List<&2, U32>) -> Nat:
  List.length(&2, U32, l)

# ---------------------------------------------------------------------------
# Edge-closed stays edge-closed.
# ---------------------------------------------------------------------------

law Spec.closed_stays:
  for +f: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +x: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool}
  for +cl: {Sp.Spec.closed(td, g, sd, x) == True{} : Bool}
  {Sp.Spec.closed(td, g, sd, Sp.Spec.iter(f, td, g, sd, x))
    == True{} : Bool}

def Spec.closed_stays(f, td, sd, g, x, gf, lt, vx, cl):
  Sa.PSet.subset_trans(sd,
    Sp.Spec.post(td, g, sd, Sp.Spec.iter(f, td, g, sd, x)), x,
    Sp.Spec.iter(f, td, g, sd, x),
    Pm.Spec.post_valid(td, sd, g,
      Sp.Spec.iter(f, td, g, sd, x), gf, lt), vx,
    Lp.Spec.iter_valid(f, td, sd, g, x, gf, lt, vx), lt,
    Sa.PSet.subset_trans(sd,
      Sp.Spec.post(td, g, sd, Sp.Spec.iter(f, td, g, sd, x)),
      Sp.Spec.post(td, g, sd, x), x,
      Pm.Spec.post_valid(td, sd, g,
        Sp.Spec.iter(f, td, g, sd, x), gf, lt),
      Pm.Spec.post_valid(td, sd, g, x, gf, lt), vx, lt,
      Pm.Spec.post_mono(td, sd, g, Sp.Spec.iter(f, td, g, sd, x), x,
        gf, lt, Lp.Spec.iter_valid(f, td, sd, g, x, gf, lt, vx), vx,
        Lp.Spec.iter_least(f, td, sd, g, x, x, gf, lt, vx, vx, cl,
          Lp.PSet.subset_refl(sd, x, vx, lt))), cl),
    Lp.Spec.iter_grows(f, td, sd, g, x, gf, lt, vx))

# ---------------------------------------------------------------------------
# A round that adds nothing is edge-closed.
# ---------------------------------------------------------------------------

def Spec.closed_of_step(+td: Nat, +sd: Nat, +g: G.Graph(),
  +x: S.PSet,
  +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool},
  +sx: {S.PSet.is_subset(sd, Sp.Spec.step(td, g, sd, x), x)
    == True{} : Bool})
  -> {Sp.Spec.closed(td, g, sd, x) == True{} : Bool}:
  Sa.PSet.subset_trans(sd, Sp.Spec.post(td, g, sd, x),
    Sp.Spec.step(td, g, sd, x), x,
    Pm.Spec.post_valid(td, sd, g, x, gf, lt),
    Lp.Spec.step_valid(td, sd, g, x, gf, lt, vx), vx, lt,
    Ca.Spec.post_sub_step(td, sd, g, x, gf, lt, vx), sx)

def Spec.settle.nil(+td: Nat, +sd: Nat, +g: G.Graph(), +x: S.PSet,
  +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool},
  +ecd: {False{} == Sp.Spec.closed(td, g, sd, x) : Bool},
  +el: {Nil{} == S.PSet.missing(sd, Sp.Spec.step(td, g, sd, x), x)
    : List<&2, U32>})
  -> {False{} == True{} : Bool}:
  %E.Bool.sym(False{}, Sp.Spec.closed(td, g, sd, x), ecd)
    : {_ == True{} : Bool}
  Spec.closed_of_step(td, sd, g, x, gf, lt, vx,
    %E.Nat.sym(
      S.PSet.missing_count(sd, Sp.Spec.step(td, g, sd, x), x), 0n,
      Equal.trans(Nat,
        S.PSet.missing_count(sd, Sp.Spec.step(td, g, sd, x), x),
        Ords.len(S.PSet.missing(sd, Sp.Spec.step(td, g, sd, x), x)),
        0n,
        Fl.PSet.missing_count_is_length(sd,
          Sp.Spec.step(td, g, sd, x), x, lt),
        E.Nat.sym(0n,
          Ords.len(S.PSet.missing(sd, Sp.Spec.step(td, g, sd, x),
            x)),
          Equal.cong(List<&2, U32>, Nat, Ords.len, Nil{},
            S.PSet.missing(sd, Sp.Spec.step(td, g, sd, x), x),
            el))))
      : {Nat.is_eq(_, 0n) == True{} : Bool}
    {==})

# ---------------------------------------------------------------------------
# A round that is not edge-closed is strictly bigger than the one before.
# ---------------------------------------------------------------------------

law Spec.round_grows:
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +x: S.PSet
  for +h: U32
  for +t: List<&2, U32>
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool}
  for +el: {Con{h, t}
    == S.PSet.missing(sd, Sp.Spec.step(td, g, sd, x), x)
    : List<&2, U32>}
  {C.Nat.upto(1n+S.PSet.count(sd, x, S.PSet.half(sd)),
    S.PSet.count(sd, Sp.Spec.step(td, g, sd, x), S.PSet.half(sd)))
    == True{} : Bool}

def Spec.round_grows(td, sd, g, x, h, t, gf, lt, vx, el):
  Sd.PSet.count_lt(sd, Sp.Spec.step(td, g, sd, x), x, h, t,
    Lp.Spec.step_valid(td, sd, g, x, gf, lt, vx), vx, lt, el,
    Ca.Spec.sub_step(td, sd, g, x, gf, lt, vx))

def Spec.settle.base(+td: Nat, +sd: Nat, +g: G.Graph(), +x: S.PSet,
  +h: U32, +t: List<&2, U32>,
  +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool},
  +el: {Con{h, t}
    == S.PSet.missing(sd, Sp.Spec.step(td, g, sd, x), x)
    : List<&2, U32>},
  +bnd: {C.Nat.upto(S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)),
    S.PSet.count(sd, x, S.PSet.half(sd))) == True{} : Bool})
  -> {Empty : Type}:
  Ct.Nat.upto_succ_absurd(S.PSet.count(sd, x, S.PSet.half(sd)),
    Ct2.Nat.le_trans(1n+S.PSet.count(sd, x, S.PSet.half(sd)),
      S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)),
      S.PSet.count(sd, x, S.PSet.half(sd)),
      Ct2.Nat.le_trans(1n+S.PSet.count(sd, x, S.PSet.half(sd)),
        S.PSet.count(sd, Sp.Spec.step(td, g, sd, x),
          S.PSet.half(sd)),
        S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)),
        Spec.round_grows(td, sd, g, x, h, t, gf, lt, vx, el),
        Sd.PSet.count_bound(sd, Sp.Spec.step(td, g, sd, x),
          Lp.Spec.step_valid(td, sd, g, x, gf, lt, vx), lt)), bnd))

def Spec.settle.bound(+q: Nat, +td: Nat, +sd: Nat, +g: G.Graph(),
  +x: S.PSet, +h: U32, +t: List<&2, U32>,
  +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool},
  +el: {Con{h, t}
    == S.PSet.missing(sd, Sp.Spec.step(td, g, sd, x), x)
    : List<&2, U32>},
  bnd: {C.Nat.upto(S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)),
    Nat.add(1n+q, S.PSet.count(sd, x, S.PSet.half(sd))))
    == True{} : Bool})
  -> {C.Nat.upto(S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)),
    Nat.add(q, S.PSet.count(sd, Sp.Spec.step(td, g, sd, x),
      S.PSet.half(sd)))) == True{} : Bool}:
  Ct2.Nat.le_trans(S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)),
    Nat.add(q, 1n+S.PSet.count(sd, x, S.PSet.half(sd))),
    Nat.add(q, S.PSet.count(sd, Sp.Spec.step(td, g, sd, x),
      S.PSet.half(sd))),
    %E.Nat.sym(Nat.add(q, 1n+S.PSet.count(sd, x, S.PSet.half(sd))),
      1n+Nat.add(q, S.PSet.count(sd, x, S.PSet.half(sd))),
      N.Nat.add_succ(q, S.PSet.count(sd, x, S.PSet.half(sd))))
      : {C.Nat.upto(S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)), _)
        == True{} : Bool}
    bnd,
    Ne.Nat.le_add_mono_l(q,
      1n+S.PSet.count(sd, x, S.PSet.half(sd)),
      S.PSet.count(sd, Sp.Spec.step(td, g, sd, x), S.PSet.half(sd)),
      Spec.round_grows(td, sd, g, x, h, t, gf, lt, vx, el)))

# ---------------------------------------------------------------------------
# The pigeonhole.
# ---------------------------------------------------------------------------

law Spec.settle:
  for +m: Nat
  for +f: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +x: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool}
  for bnd: {C.Nat.upto(S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)),
    Nat.add(m, S.PSet.count(sd, x, S.PSet.half(sd)))) == True{}
    : Bool}
  for mf: {C.Nat.upto(m, f) == True{} : Bool}
  {Sp.Spec.closed(td, g, sd, Sp.Spec.iter(f, td, g, sd, x))
    == True{} : Bool}

def Spec.settle.zero(+f: Nat, +td: Nat, +sd: Nat, +g: G.Graph(),
  +x: S.PSet,
  +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool},
  +cd: Bool, +ecd: {cd == Sp.Spec.closed(td, g, sd, x) : Bool},
  +l: List<&2, U32>,
  +el: {l == S.PSet.missing(sd, Sp.Spec.step(td, g, sd, x), x)
    : List<&2, U32>},
  bnd: {C.Nat.upto(S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)),
    S.PSet.count(sd, x, S.PSet.half(sd))) == True{} : Bool})
  -> {Sp.Spec.closed(td, g, sd, Sp.Spec.iter(f, td, g, sd, x))
    == True{} : Bool}:
  match cd:
    case True{}:
      Spec.closed_stays(f, td, sd, g, x, gf, lt, vx,
        E.Bool.sym(True{}, Sp.Spec.closed(td, g, sd, x), ecd))
    case False{}:
      match l:
        case Nil{}:
          E.Bool.noconf({Sp.Spec.closed(td, g, sd,
            Sp.Spec.iter(f, td, g, sd, x)) == True{} : Bool},
            Spec.settle.nil(td, sd, g, x, gf, lt, vx, ecd, el))
        case Con{h, t}:
          Empty.absurd({Sp.Spec.closed(td, g, sd,
            Sp.Spec.iter(f, td, g, sd, x)) == True{} : Bool},
            Spec.settle.base(td, sd, g, x, h, t, gf, lt, vx, el,
              bnd))

def Spec.settle.succ(+q: Nat, +e: Nat, +td: Nat, +sd: Nat,
  +g: G.Graph(), +x: S.PSet,
  +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool},
  +vx: {S.PSet.valid(sd, x, True{}) == True{} : Bool},
  +cd: Bool, +ecd: {cd == Sp.Spec.closed(td, g, sd, x) : Bool},
  +l: List<&2, U32>,
  +el: {l == S.PSet.missing(sd, Sp.Spec.step(td, g, sd, x), x)
    : List<&2, U32>},
  bnd: {C.Nat.upto(S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)),
    Nat.add(1n+q, S.PSet.count(sd, x, S.PSet.half(sd)))) == True{}
    : Bool},
  mf: {C.Nat.upto(q, e) == True{} : Bool},
  ih: {C.Nat.upto(S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)),
      Nat.add(q, S.PSet.count(sd, Sp.Spec.step(td, g, sd, x),
        S.PSet.half(sd)))) == True{} : Bool} ->
    {C.Nat.upto(q, e) == True{} : Bool} ->
    {Sp.Spec.closed(td, g, sd, Sp.Spec.iter(e, td, g, sd,
      Sp.Spec.step(td, g, sd, x))) == True{} : Bool})
  -> {Sp.Spec.closed(td, g, sd,
    Sp.Spec.iter(1n+e, td, g, sd, x)) == True{} : Bool}:
  match cd:
    case True{}:
      Spec.closed_stays(1n+e, td, sd, g, x, gf, lt, vx,
        E.Bool.sym(True{}, Sp.Spec.closed(td, g, sd, x), ecd))
    case False{}:
      match l:
        case Nil{}:
          E.Bool.noconf({Sp.Spec.closed(td, g, sd,
            Sp.Spec.iter(1n+e, td, g, sd, x)) == True{} : Bool},
            Spec.settle.nil(td, sd, g, x, gf, lt, vx, ecd, el))
        case Con{h, t}:
          ih(Spec.settle.bound(q, td, sd, g, x, h, t, gf, lt, vx, el,
            bnd), mf)

def Spec.settle(m, f, td, sd, g, x, gf, lt, vx, bnd, mf):
  match m:
    case 0n:
      Spec.settle.zero(f, td, sd, g, x, gf, lt, vx,
        Sp.Spec.closed(td, g, sd, x), {==},
        S.PSet.missing(sd, Sp.Spec.step(td, g, sd, x), x), {==}, bnd)
    case 1n+q:
      match f:
        case 0n:
          E.Bool.noconf({Sp.Spec.closed(td, g, sd,
            Sp.Spec.iter(0n, td, g, sd, x)) == True{} : Bool}, mf)
        case 1n+e:
          Spec.settle.succ(q, e, td, sd, g, x, gf, lt, vx,
            Sp.Spec.closed(td, g, sd, x), {==},
            S.PSet.missing(sd, Sp.Spec.step(td, g, sd, x), x), {==},
            bnd, mf,
            Spec.settle(q, e, td, sd, g, Sp.Spec.step(td, g, sd, x),
              gf, lt,
              Lp.Spec.step_valid(td, sd, g, x, gf, lt, vx)))

law Spec.closure_is_closed:
  for +n: Nat
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +r: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vr: {S.PSet.valid(sd, r, True{}) == True{} : Bool}
  for +fuel: {C.Nat.upto(
    S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)), 1n+n) == True{}
    : Bool}
  {Sp.Spec.closed(td, g, sd, Sp.Spec.closure(n, td, g, sd, r))
    == True{} : Bool}

def Spec.closure_is_closed(n, td, sd, g, r, gf, lt, vr, fuel):
  Spec.settle(S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)), 1n+n, td,
    sd, g, r, gf, lt, vr,
    Ct2.Nat.le_add_right(
      S.PSet.count(sd, S.PFull{}, S.PSet.half(sd)),
      S.PSet.count(sd, r, S.PSet.half(sd))), fuel)
