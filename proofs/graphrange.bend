# proofs/graphrange.bend -- a graph whose successors are ordinals.
#
# The closure specification folds a frontier's successors into a set, and
# `PSet.from_list` only holds exactly what it was given when every ordinal it
# is given is one of the universe's. `Store.succ` checks that on load -- a
# successor pointing outside the universe is a corrupt index, not a set with
# an extra member -- so the condition is real, and this file makes it a
# predicate a proof can carry.
#
# It is stated over the graph rather than over a frontier, which is what lets
# it be established once and used at every vertex an induction reaches.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./shift.bend as Sf
import ./leafenum.bend as Le
import ./span.bend as Sn
import ./subsetconv.bend as Sc
import ./subsetalg.bend as Sa2
import ../core/count.bend as C
import ../core/trie.bend as T
import ../core/word.bend as W
import ../closure/graph.bend as G

# Every successor list in the trie is in range.
def Graph.succs_fit(+sd: Nat, t: T.Trie<List<&2, U32>>) -> Bool:
  match t:
    case T.TGap{}:
      True{}
    case T.TVal{v}:
      Sf.Ords.all_fit(v, 12n+sd)
    case T.TBr{lo, hi}:
      Bool.and(Graph.succs_fit(sd, lo), Graph.succs_fit(sd, hi))

law Graph.succs_fit_get:
  for +d: Nat
  for +sd: Nat
  for +t: T.Trie<List<&2, U32>>
  for +h: U32
  for +x: U32
  for +ok: {Graph.succs_fit(sd, t) == True{} : Bool}
  {Sf.Ords.all_fit(G.Graph.succ.un(T.Trie.get(List<&2, U32>, d, t, h,
    x)), 12n+sd) == True{} : Bool}

law Graph.succs_fit_pick:
  for +sd: Nat
  for +b: Bool
  for +lo: T.Trie<List<&2, U32>>
  for +hi: T.Trie<List<&2, U32>>
  for +ok: {Graph.succs_fit(sd, T.TBr{lo, hi}) == True{} : Bool}
  {Graph.succs_fit(sd, T.Trie.pick(List<&2, U32>, b, lo, hi))
    == True{} : Bool}

def Graph.succs_fit_pick(sd, b, lo, hi, ok):
  match b:
    case True{}:
      E.Bool.and_l(Graph.succs_fit(sd, lo), Graph.succs_fit(sd, hi),
        ok)
    case False{}:
      E.Bool.and_r(Graph.succs_fit(sd, lo), Graph.succs_fit(sd, hi),
        ok)

def Graph.succs_fit_get(d, sd, t, h, x, ok):
  match d:
    case 0n:
      match t:
        case T.TGap{}:
          {==}
        case T.TVal{v}:
          ok
        case T.TBr{lo, hi}:
          {==}
    case 1n+p:
      match t:
        case T.TGap{}:
          {==}
        case T.TVal{v}:
          {==}
        case T.TBr{lo, hi}:
          Graph.succs_fit_get(p, sd,
            T.Trie.pick(List<&2, U32>, U32.is_lt(x, h), lo, hi),
            U32.shr(h), T.Trie.rebase(U32.is_lt(x, h), h, x),
            Graph.succs_fit_pick(sd, U32.is_lt(x, h), lo, hi, ok))

law Graph.succ_fits:
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +v: U32
  for +ok: {Graph.succs_fit(sd, g) == True{} : Bool}
  {Sf.Ords.all_fit(G.Graph.succ(td, g, v), 12n+sd) == True{} : Bool}

def Graph.succ_fits(td, sd, g, v, ok):
  Graph.succs_fit_get(td, sd, g, T.Trie.half(td), v, ok)

# ---------------------------------------------------------------------------
# What the gather holds: an ordinal is on it exactly when some vertex of the
# frontier has it as a successor.
# ---------------------------------------------------------------------------

def Graph.any_succ(+td: Nat, +g: G.Graph(), +l: List<&2, U32>,
  +z: U32) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{v, t}:
      Bool.or(List.contains(~U32, ~U32.is_eq,
        G.Graph.succ(td, g, v), z), Graph.any_succ(td, g, t, z))

law Graph.gather_contains:
  for +l: List<&2, U32>
  for +td: Nat
  for +g: G.Graph()
  for +acc: List<&2, U32>
  for +z: U32
  {List.contains(~U32, ~U32.is_eq, G.Graph.gather(td, g, l, acc), z)
    == Bool.or(Graph.any_succ(td, g, l, z),
         List.contains(~U32, ~U32.is_eq, acc, z)) : Bool}

def Graph.gather_contains(l, td, g, acc, z):
  match l:
    case Nil{}:
      {==}
    case Con{v, t}:
      %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
          G.Graph.gather(td, g, t,
            List.append(&2, U32, G.Graph.succ(td, g, v), acc)), z),
        Bool.or(Graph.any_succ(td, g, t, z),
          List.contains(~U32, ~U32.is_eq,
            List.append(&2, U32, G.Graph.succ(td, g, v), acc), z)),
        Graph.gather_contains(t, td, g,
          List.append(&2, U32, G.Graph.succ(td, g, v), acc), z))
        : {_ == Bool.or(Bool.or(List.contains(~U32, ~U32.is_eq,
             G.Graph.succ(td, g, v), z),
             Graph.any_succ(td, g, t, z)),
             List.contains(~U32, ~U32.is_eq, acc, z)) : Bool}
      %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
          List.append(&2, U32, G.Graph.succ(td, g, v), acc), z),
        Bool.or(List.contains(~U32, ~U32.is_eq,
          G.Graph.succ(td, g, v), z),
          List.contains(~U32, ~U32.is_eq, acc, z)),
        Le.List.contains_append(G.Graph.succ(td, g, v), acc, z))
        : {Bool.or(Graph.any_succ(td, g, t, z), _)
          == Bool.or(Bool.or(List.contains(~U32, ~U32.is_eq,
               G.Graph.succ(td, g, v), z),
               Graph.any_succ(td, g, t, z)),
               List.contains(~U32, ~U32.is_eq, acc, z)) : Bool}
      Sn.Bool.or_rotate(Graph.any_succ(td, g, t, z),
        List.contains(~U32, ~U32.is_eq, G.Graph.succ(td, g, v), z),
        List.contains(~U32, ~U32.is_eq, acc, z))

law Ords.all_fit_append:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +k: Nat
  for +fa: {Sf.Ords.all_fit(a, k) == True{} : Bool}
  for +fb: {Sf.Ords.all_fit(b, k) == True{} : Bool}
  {Sf.Ords.all_fit(List.append(&2, U32, a, b), k) == True{} : Bool}

def Ords.all_fit_append(a, b, k, fa, fb):
  match a:
    case Nil{}:
      fb
    case Con{y, t}:
      E.Bool.and_both(Dc.U32.hi_zero(y, k),
        Sf.Ords.all_fit(List.append(&2, U32, t, b), k),
        E.Bool.and_l(Dc.U32.hi_zero(y, k), Sf.Ords.all_fit(t, k), fa),
        Ords.all_fit_append(t, b, k,
          E.Bool.and_r(Dc.U32.hi_zero(y, k), Sf.Ords.all_fit(t, k),
            fa), fb))

law Graph.gather_fit:
  for +l: List<&2, U32>
  for +td: Nat
  for +sd: Nat
  for +g: G.Graph()
  for +acc: List<&2, U32>
  for +ok: {Graph.succs_fit(sd, g) == True{} : Bool}
  for +facc: {Sf.Ords.all_fit(acc, 12n+sd) == True{} : Bool}
  {Sf.Ords.all_fit(G.Graph.gather(td, g, l, acc), 12n+sd) == True{}
    : Bool}

def Graph.gather_fit(l, td, sd, g, acc, ok, facc):
  match l:
    case Nil{}:
      facc
    case Con{v, t}:
      Graph.gather_fit(t, td, sd, g,
        List.append(&2, U32, G.Graph.succ(td, g, v), acc), ok,
        Ords.all_fit_append(G.Graph.succ(td, g, v), acc, 12n+sd,
          Graph.succ_fits(td, sd, g, v, ok), facc))

# ---------------------------------------------------------------------------
# A wider frontier has wider successors.
# ---------------------------------------------------------------------------

law Graph.any_succ_of_member:
  for +l: List<&2, U32>
  for +td: Nat
  for +g: G.Graph()
  for +v: U32
  for +z: U32
  for +e: Bool
  for +ee: {e == Sc.Ords.head_eq(l, v) : Bool}
  for +cv: {List.contains(~U32, ~U32.is_eq, l, v) == True{} : Bool}
  for +cs: {List.contains(~U32, ~U32.is_eq, G.Graph.succ(td, g, v), z)
    == True{} : Bool}
  {Graph.any_succ(td, g, l, z) == True{} : Bool}

def Graph.succ_cast(+td: Nat, +g: G.Graph(), +w: U32, +v: U32,
  +z: U32, +e: {w == v : U32},
  +cs: {List.contains(~U32, ~U32.is_eq, G.Graph.succ(td, g, v), z)
    == True{} : Bool})
  -> {List.contains(~U32, ~U32.is_eq, G.Graph.succ(td, g, w), z)
    == True{} : Bool}:
  %E.U32.sym(w, v, e)
    : {List.contains(~U32, ~U32.is_eq, G.Graph.succ(td, g, _), z)
      == True{} : Bool}
  cs

def Graph.any_succ_of_member(l, td, g, v, z, e, ee, cv, cs):
  match l:
    case Nil{}:
      E.Bool.noconf({Graph.any_succ(td, g, Nil{}, z) == True{}
        : Bool}, cv)
    case Con{w, t}:
      match e:
        case True{}:
          Sa2.Ords.or_left(List.contains(~U32, ~U32.is_eq,
            G.Graph.succ(td, g, w), z),
            Graph.any_succ(td, g, t, z),
            Graph.succ_cast(td, g, w, v, z,
              E.U32.eq_reflect(w, v,
                E.Bool.sym(True{}, U32.is_eq(w, v), ee)), cs))
        case False{}:
          Sa2.Ords.or_right(List.contains(~U32, ~U32.is_eq,
            G.Graph.succ(td, g, w), z),
            Graph.any_succ(td, g, t, z),
            Graph.any_succ_of_member(t, td, g, v, z,
              Sc.Ords.head_eq(t, v), {==},
              Sc.Ords.contains_tail(w, t, v, ee, cv), cs))

law Graph.any_succ_mono:
  for +l1: List<&2, U32>
  for +l2: List<&2, U32>
  for +td: Nat
  for +g: G.Graph()
  for +z: U32
  for +ai: {Sa2.Ords.all_in(l1, l2) == True{} : Bool}
  for any: {Graph.any_succ(td, g, l1, z) == True{} : Bool}
  {Graph.any_succ(td, g, l2, z) == True{} : Bool}

def Graph.any_succ_tail(+td: Nat, +g: G.Graph(), +v: U32,
  +t: List<&2, U32>, +z: U32,
  +ee: {False{} == List.contains(~U32, ~U32.is_eq,
    G.Graph.succ(td, g, v), z) : Bool},
  +any: {Graph.any_succ(td, g, Con{v, t}, z) == True{} : Bool})
  -> {Graph.any_succ(td, g, t, z) == True{} : Bool}:
  %E.Bool.sym(False{}, List.contains(~U32, ~U32.is_eq,
    G.Graph.succ(td, g, v), z), ee)
    : {Bool.or(_, Graph.any_succ(td, g, t, z)) == True{} : Bool}
  any

def Graph.any_succ_side(+l2: List<&2, U32>,
  +td: Nat, +g: G.Graph(), +z: U32, +v: U32, +t: List<&2, U32>,
  +e: Bool,
  +ee: {e == List.contains(~U32, ~U32.is_eq,
    G.Graph.succ(td, g, v), z) : Bool},
  +ai: {Sa2.Ords.all_in(Con{v, t}, l2) == True{} : Bool},
  +any: {Graph.any_succ(td, g, Con{v, t}, z) == True{} : Bool},
  ih: {Graph.any_succ(td, g, t, z) == True{} : Bool} ->
    {Graph.any_succ(td, g, l2, z) == True{} : Bool})
  -> {Graph.any_succ(td, g, l2, z) == True{} : Bool}:
  match e:
    case True{}:
      Graph.any_succ_of_member(l2, td, g, v, z,
        Sc.Ords.head_eq(l2, v), {==},
        E.Bool.and_l(List.contains(~U32, ~U32.is_eq, l2, v),
          Sa2.Ords.all_in(t, l2), ai),
        E.Bool.sym(True{}, List.contains(~U32, ~U32.is_eq,
          G.Graph.succ(td, g, v), z), ee))
    case False{}:
      ih(Graph.any_succ_tail(td, g, v, t, z, ee, any))

def Graph.any_succ_mono(l1, l2, td, g, z, ai, any):
  match l1:
    case Nil{}:
      E.Bool.noconf({Graph.any_succ(td, g, l2, z) == True{} : Bool},
        any)
    case Con{v, t}:
      Graph.any_succ_side(l2, td, g, z, v, t,
        List.contains(~U32, ~U32.is_eq, G.Graph.succ(td, g, v), z),
        {==}, ai, any,
        Graph.any_succ_mono(t, l2, td, g, z,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq, l2, v),
            Sa2.Ords.all_in(t, l2), ai)))
