# proofs/postmono.bend -- the successor step is monotone.
#
# `Spec.post` is the round's whole content: gather every successor of every
# member of the frontier and fold the result into a set. The closure laws all
# need one fact about it -- a bigger frontier has a bigger image -- and this
# file proves it by going through the list in the middle rather than around
# it.
#
# An ordinal is a member of `post(x)` exactly when some member of `x` has it
# as a successor. Both halves of that are already available: the list-to-set
# bridge says `from_list` holds exactly what it was given (given that the
# ordinals fit, which is why the graph range invariant is a hypothesis), and
# `Graph.gather_contains` says the gathered list holds exactly the successors
# of the frontier. Between them, monotonicity is `Graph.any_succ_mono` with a
# frontier inclusion on either side.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./shift.bend as Sf
import ./treeenum.bend as Te
import ./validshape.bend as Vs
import ./subsetconv.bend as Sc
import ./subsetalg.bend as Sa
import ./listset.bend as Ls
import ./insertvalid.bend as Iv
import ./graphrange.bend as Gr
import ./listsub.bend as Lb
import ../core/count.bend as C
import ../core/set.bend as S
import ../closure/graph.bend as G
import ../spec/closure.bend as Sp

# ---------------------------------------------------------------------------
# A subset's enumeration is inside the bigger set's enumeration.
# ---------------------------------------------------------------------------

law Ords.all_in_subset:
  for +l: List<&2, U32>
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ab: {S.PSet.is_subset(d, a, b) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l, S.PSet.to_list(d, a)) == True{} : Bool}
  {Sa.Ords.all_in(l, S.PSet.to_list(d, b)) == True{} : Bool}

def Ords.in_of_member(+d: Nat, +b: S.PSet, +y: U32,
  +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +inv: {Dc.U32.hi_zero(y, 12n+d) == True{} : Bool},
  +m: {S.PSet.member(d, b, y) == True{} : Bool})
  -> {List.contains(~U32, ~U32.is_eq, S.PSet.to_list(d, b), y)
    == True{} : Bool}:
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      S.PSet.to_list(d, b), y), S.PSet.member(d, b, y),
    Vs.PSet.to_list_member_of_valid(d, b, y, vb, lt, inv))
    : {_ == True{} : Bool}
  m

def Ords.all_in_subset(l, d, a, b, va, vb, lt, ab, ai):
  match l:
    case Nil{}:
      {==}
    case Con{y, t}:
      E.Bool.and_both(List.contains(~U32, ~U32.is_eq,
        S.PSet.to_list(d, b), y),
        Sa.Ords.all_in(t, S.PSet.to_list(d, b)),
        Ords.in_of_member(d, b, y, vb, lt,
          Sa.PSet.in_range_of_to_list(d, a, y, va, lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(d, a), y),
              Sa.Ords.all_in(t, S.PSet.to_list(d, a)), ai)),
          Sa.PSet.subset_member_at(d, a, b, y, va, vb, lt,
            Sa.PSet.in_range_of_to_list(d, a, y, va, lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(d, a), y),
                Sa.Ords.all_in(t, S.PSet.to_list(d, a)), ai)),
            ab,
            Sa.PSet.member_of_to_list(d, a, y, va, lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(d, a), y),
                Sa.Ords.all_in(t, S.PSet.to_list(d, a)), ai)))),
        Ords.all_in_subset(t, d, a, b, va, vb, lt, ab,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(d, a), y),
            Sa.Ords.all_in(t, S.PSet.to_list(d, a)), ai)))

law PSet.subset_to_list:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ab: {S.PSet.is_subset(d, a, b) == True{} : Bool}
  {Sa.Ords.all_in(S.PSet.to_list(d, a), S.PSet.to_list(d, b))
    == True{} : Bool}

def PSet.subset_to_list(d, a, b, va, vb, lt, ab):
  Ords.all_in_subset(S.PSet.to_list(d, a), d, a, b, va, vb, lt, ab,
    Sa.Ords.all_in_self(S.PSet.to_list(d, a)))

# ---------------------------------------------------------------------------
# What the image is: exactly the successors of the frontier.
# ---------------------------------------------------------------------------

law Spec.post_valid:
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +a: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  {S.PSet.valid(sd, Sp.Spec.post(td, g, sd, a), True{}) == True{}
    : Bool}

def Spec.post_valid(td, sd, g, a, gf, lt):
  Iv.PSet.valid_from_list(
    G.Graph.gather(td, g, S.PSet.to_list(sd, a), Nil{}), sd, lt,
    Gr.Graph.gather_fit(S.PSet.to_list(sd, a), td, sd, g, Nil{}, gf,
      {==}))

law Spec.any_of_post:
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +a: S.PSet
  for +z: U32
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(z, 12n+sd) == True{} : Bool}
  for +m: {S.PSet.member(sd, Sp.Spec.post(td, g, sd, a), z)
    == True{} : Bool}
  {Gr.Graph.any_succ(td, g, S.PSet.to_list(sd, a), z) == True{}
    : Bool}

def Spec.any_of_post(td, sd, g, a, z, gf, lt, inv, m):
  %Te.Bool.or_false_r(Gr.Graph.any_succ(td, g,
    S.PSet.to_list(sd, a), z)) : {_ == True{} : Bool}
  %Gr.Graph.gather_contains(S.PSet.to_list(sd, a), td, g, Nil{}, z)
    : {_ == True{} : Bool}
  Ls.PSet.from_list_only_at(
    G.Graph.gather(td, g, S.PSet.to_list(sd, a), Nil{}), sd, z, lt,
    inv,
    Gr.Graph.gather_fit(S.PSet.to_list(sd, a), td, sd, g, Nil{}, gf,
      {==}), m)

law Spec.post_of_any:
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +b: S.PSet
  for +z: U32
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(z, 12n+sd) == True{} : Bool}
  for +any: {Gr.Graph.any_succ(td, g, S.PSet.to_list(sd, b), z)
    == True{} : Bool}
  {S.PSet.member(sd, Sp.Spec.post(td, g, sd, b), z) == True{} : Bool}

def Spec.contains_of_any(+td: Nat, +sd: Nat, +g: G.Graph(),
  +b: S.PSet, +z: U32,
  +any: {Gr.Graph.any_succ(td, g, S.PSet.to_list(sd, b), z)
    == True{} : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
    G.Graph.gather(td, g, S.PSet.to_list(sd, b), Nil{}), z)
    == True{} : Bool}:
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      G.Graph.gather(td, g, S.PSet.to_list(sd, b), Nil{}), z),
    Bool.or(Gr.Graph.any_succ(td, g, S.PSet.to_list(sd, b), z),
      False{}),
    Gr.Graph.gather_contains(S.PSet.to_list(sd, b), td, g, Nil{}, z))
    : {_ == True{} : Bool}
  %E.Bool.sym(Bool.or(Gr.Graph.any_succ(td, g,
      S.PSet.to_list(sd, b), z), False{}),
    Gr.Graph.any_succ(td, g, S.PSet.to_list(sd, b), z),
    Te.Bool.or_false_r(Gr.Graph.any_succ(td, g,
      S.PSet.to_list(sd, b), z))) : {_ == True{} : Bool}
  any

def Spec.post_of_any(td, sd, g, b, z, lt, inv, any):
  Ls.PSet.from_list_contains_at(
    G.Graph.gather(td, g, S.PSet.to_list(sd, b), Nil{}), sd, z, lt,
    inv, Spec.contains_of_any(td, sd, g, b, z, any))

# ---------------------------------------------------------------------------
# Monotonicity.
# ---------------------------------------------------------------------------

law Ords.all_mem_post:
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
  for +ab: {S.PSet.is_subset(sd, a, b) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l,
    S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, a))) == True{} : Bool}
  {Sc.Ords.all_mem(l, sd, Sp.Spec.post(td, g, sd, b)) == True{}
    : Bool}

def Ords.all_mem_post(l, td, sd, g, a, b, gf, lt, va, vb, ab, ai):
  match l:
    case Nil{}:
      {==}
    case Con{z, t}:
      E.Bool.and_both(
        S.PSet.member(sd, Sp.Spec.post(td, g, sd, b), z),
        Sc.Ords.all_mem(t, sd, Sp.Spec.post(td, g, sd, b)),
        Spec.post_of_any(td, sd, g, b, z, lt,
          Sa.PSet.in_range_of_to_list(sd,
            Sp.Spec.post(td, g, sd, a), z,
            Spec.post_valid(td, sd, g, a, gf, lt), lt,
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
              S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, a)), z),
              Sa.Ords.all_in(t,
                S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, a))),
              ai)),
          Gr.Graph.any_succ_mono(S.PSet.to_list(sd, a),
            S.PSet.to_list(sd, b), td, g, z,
            PSet.subset_to_list(sd, a, b, va, vb, lt, ab),
            Spec.any_of_post(td, sd, g, a, z, gf, lt,
              Sa.PSet.in_range_of_to_list(sd,
                Sp.Spec.post(td, g, sd, a), z,
                Spec.post_valid(td, sd, g, a, gf, lt), lt,
                E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                  S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, a)), z),
                  Sa.Ords.all_in(t,
                    S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, a))),
                  ai)),
              Sa.PSet.member_of_to_list(sd,
                Sp.Spec.post(td, g, sd, a), z,
                Spec.post_valid(td, sd, g, a, gf, lt), lt,
                E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                  S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, a)), z),
                  Sa.Ords.all_in(t,
                    S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, a))),
                  ai))))),
        Ords.all_mem_post(t, td, sd, g, a, b, gf, lt, va, vb, ab,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, a)), z),
            Sa.Ords.all_in(t,
              S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, a))), ai)))

law Spec.post_mono:
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +a: S.PSet
  for +b: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +va: {S.PSet.valid(sd, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(sd, b, True{}) == True{} : Bool}
  for +ab: {S.PSet.is_subset(sd, a, b) == True{} : Bool}
  {S.PSet.is_subset(sd, Sp.Spec.post(td, g, sd, a),
    Sp.Spec.post(td, g, sd, b)) == True{} : Bool}

def Spec.post_mono(td, sd, g, a, b, gf, lt, va, vb, ab):
  Sc.PSet.subset_of_members(sd, Sp.Spec.post(td, g, sd, a),
    Sp.Spec.post(td, g, sd, b),
    Spec.post_valid(td, sd, g, a, gf, lt),
    Spec.post_valid(td, sd, g, b, gf, lt), lt,
    Ords.all_mem_post(
      S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, a)), td, sd, g, a,
      b, gf, lt, va, vb, ab,
      Sa.Ords.all_in_self(
        S.PSet.to_list(sd, Sp.Spec.post(td, g, sd, a)))))

# ---------------------------------------------------------------------------
# The image stays inside a bounding set the graph respects.
# ---------------------------------------------------------------------------

law Spec.post_in:
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +uu: S.PSet
  for +a: S.PSet
  for +gf: {Gr.Graph.succs_fit(sd, g) == True{} : Bool}
  for +su: {Gr.Graph.succs_in(sd, uu, g) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +vu: {S.PSet.valid(sd, uu, True{}) == True{} : Bool}
  {S.PSet.is_subset(sd, Sp.Spec.post(td, g, sd, a), uu) == True{}
    : Bool}

def Spec.post_in(td, sd, g, uu, a, gf, su, lt, vu):
  Lb.PSet.subset_of_list_mem(
    G.Graph.gather(td, g, S.PSet.to_list(sd, a), Nil{}), sd, uu, lt,
    Gr.Graph.gather_fit(S.PSet.to_list(sd, a), td, sd, g, Nil{}, gf,
      {==}), vu,
    Gr.Graph.gather_in(S.PSet.to_list(sd, a), td, sd, uu, g, Nil{},
      su, {==}))
