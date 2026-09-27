# proofs/witness.bend -- what a dependency witness guarantees (law E-01).
#
# SPEC 4.4's explanation obligation has three parts: a returned path begins at
# a requested root, ends at the requested object, and takes a real policy edge
# at every step. `closure/explain.bend` both produces paths and checks them,
# and the check is what `pp git explain` runs on every witness it emits.
#
# Two of the three parts hold for a produced path with no hypothesis at all,
# and they are proved here:
#
#   * every step is a real edge, because `Explain.pred` only ever returns a
#     vertex it has just tested `Graph.edge` on;
#   * the path ends at the requested object, because the walk starts there and
#     only ever prepends.
#
# The third -- that it *starts* at a requested root -- is the one that depends
# on the levels being a genuine BFS layering from the roots, which is the
# traversal obligation C-02. A witness whose levels are not such a layering
# can stop early, and then its first vertex is not a root. That is exactly why
# `Explain.valid` checks all three rather than trusting the producer, and why
# tests.bend keeps a witness that starts off-root and must be rejected.

import Base
import ./eq.bend as E
import ../closure/graph.bend as G
import ../closure/reach.bend as R
import ../closure/explain.bend as X

# ---------------------------------------------------------------------------
# `Explain.pred` only returns a vertex with an edge to the target.
# ---------------------------------------------------------------------------

# What it means for a `Maybe` answer to be edge-justified.
def Explain.pred_ok(+td: Nat, +g: G.Graph(), m: Maybe<&2, U32>,
  +target: U32) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{u}:
      G.Graph.edge(td, g, u, target)

law Explain.opt_ok:
  for +td: Nat
  for +g: G.Graph()
  for +u: U32
  for +target: U32
  for +e: Bool
  for +ee: {e == G.Graph.edge(td, g, u, target) : Bool}
  {Explain.pred_ok(td, g, X.Explain.opt(u, e), target) == True{} : Bool}

def Explain.opt_ok(td, g, u, target, e, ee):
  match e:
    case False{}:
      {==}
    case True{}:
      E.Bool.sym(True{}, G.Graph.edge(td, g, u, target), ee)

law Explain.pred_edge:
  for +td: Nat
  for +g: G.Graph()
  for +cands: List<&2, U32>
  for +target: U32
  for +got: Maybe<&2, U32>
  for +ok: {Explain.pred_ok(td, g, got, target) == True{} : Bool}
  {Explain.pred_ok(td, g,
    X.Explain.pred(td, g, cands, target, got), target) == True{} : Bool}

def Explain.pred_edge(td, g, cands, target, got, ok):
  match cands:
    case Nil{}:
      ok
    case Con{u, t}:
      match got:
        case Some{x}:
          ok
        case None{}:
          Explain.pred_edge(td, g, t, target,
            X.Explain.opt(u, G.Graph.edge(td, g, u, target)),
            Explain.opt_ok(td, g, u, target,
              G.Graph.edge(td, g, u, target), {==}))

# ---------------------------------------------------------------------------
# The walk. It prepends a vertex only when `Explain.pred` has justified it, so
# the chain it builds is a chain of real edges -- and it never disturbs the
# end of the list, so the target it started from stays last.
# ---------------------------------------------------------------------------

law Explain.steps_cons:
  for +td: Nat
  for +g: G.Graph()
  for +u: U32
  for +cur: U32
  for +acc: List<&2, U32>
  for +edge: {G.Graph.edge(td, g, u, cur) == True{} : Bool}
  for +ok: {X.Explain.steps_ok(td, g, Con{cur, acc}, True{}) == True{} : Bool}
  {X.Explain.steps_ok(td, g, Con{u, Con{cur, acc}}, True{})
    == True{} : Bool}

def Explain.steps_cons(td, g, u, cur, acc, edge, ok):
  %E.Bool.sym(G.Graph.edge(td, g, u, cur), True{}, edge)
    : {X.Explain.steps_ok(td, g, Con{cur, acc}, _) == True{} : Bool}
  ok

law Explain.walk_steps:
  for +td: Nat
  for +g: G.Graph()
  for +rev: R.Levels
  for +cur: U32
  for +acc: List<&2, U32>
  for +p: Maybe<&2, U32>
  for +pok: {Explain.pred_ok(td, g, p, cur) == True{} : Bool}
  for +ok: {X.Explain.steps_ok(td, g, Con{cur, acc}, True{}) == True{} : Bool}
  {X.Explain.steps_ok(td, g, X.Explain.walk(td, g, rev, cur, acc, p),
    True{}) == True{} : Bool}

def Explain.walk_steps(td, g, rev, cur, acc, p, pok, ok):
  match rev:
    case Nil{}:
      ok
    case Con{lvl, t}:
      match p:
        case None{}:
          ok
        case Some{u}:
          Explain.walk_steps(td, g, t, u, Con{cur, acc},
            X.Explain.pred(td, g, X.Explain.head_lvl(t), u, None{}),
            Explain.pred_edge(td, g, X.Explain.head_lvl(t), u, None{},
              {==}),
            Explain.steps_cons(td, g, u, cur, acc, pok, ok))

law Explain.walk_last:
  for +td: Nat
  for +g: G.Graph()
  for +rev: R.Levels
  for +cur: U32
  for +acc: List<&2, U32>
  for +p: Maybe<&2, U32>
  {List.last(&2, U32, X.Explain.walk(td, g, rev, cur, acc, p))
    == List.last(&2, U32, Con{cur, acc}) : Maybe<&2, U32>}

def Explain.walk_last(td, g, rev, cur, acc, p):
  match rev:
    case Nil{}:
      {==}
    case Con{lvl, t}:
      match p:
        case None{}:
          {==}
        case Some{u}:
          Explain.walk_last(td, g, t, u, Con{cur, acc},
            X.Explain.pred(td, g, X.Explain.head_lvl(t), u, None{}))

# ---------------------------------------------------------------------------
# The produced witness.
# ---------------------------------------------------------------------------

law Explain.path_steps:
  for +td: Nat
  for +g: G.Graph()
  for +rev: R.Levels
  for +target: U32
  {X.Explain.steps_ok(td, g, X.Explain.path.go(td, g, rev, target), True{})
    == True{} : Bool}

def Explain.path_steps(td, g, rev, target):
  match rev:
    case Nil{}:
      {==}
    case Con{lvl, t}:
      Explain.walk_steps(td, g, t, target, Nil{},
        X.Explain.pred(td, g, X.Explain.head_lvl(t), target, None{}),
        Explain.pred_edge(td, g, X.Explain.head_lvl(t), target, None{},
          {==}),
        {==})

# The witness ends at the object it was asked about. Stated over the walk,
# because `Explain.path.go` answers the empty list when the target is in no
# level -- which is how "not reachable" is reported, and an empty witness is
# rejected by `Explain.valid` rather than accepted.
law Explain.walk_ends_at_target:
  for +td: Nat
  for +g: G.Graph()
  for +rev: R.Levels
  for +target: U32
  for +p: Maybe<&2, U32>
  {X.Explain.last_is(
    X.Explain.walk(td, g, rev, target, Nil{}, p), target) == True{} : Bool}

def Explain.walk_ends_at_target(td, g, rev, target, p):
  %Equal.sym(Maybe<&2, U32>,
    List.last(&2, U32, X.Explain.walk(td, g, rev, target, Nil{}, p)),
    List.last(&2, U32, Con{target, Nil{}}),
    Explain.walk_last(td, g, rev, target, Nil{}, p))
    : {X.Explain.last_is.un(_, target) == True{} : Bool}
  E.U32.is_eq_refl(target)
