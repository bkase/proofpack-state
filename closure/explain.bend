# closure/explain.bend -- dependency witnesses (law E-01).
#
# A returned explanation must begin at a requested root, end at the requested
# object, and take a real policy edge at every step. This module produces such
# a path and, separately, checks one -- the check does not trust the producer,
# so a cached or heuristically-produced witness is accepted on the same terms
# as a freshly walked one (SPEC 4.4's stance, applied to explanations).
#
# The path is read off the traversal's BFS levels: the target sits in some
# level k, so some member of level k-1 has an edge to it, and so on back to
# level 0, which is the roots. That yields a shortest witness, and needs no
# parent pointers carried through the traversal.

import Base
import ../core/set.bend as S
import ./graph.bend as G
import ./reach.bend as R

def Explain.opt(+u: U32, e: Bool) -> Maybe<&2, U32>:
  match e:
    case True{}:
      Some{u}
    case False{}:
      None{}

# The first member of `cands` with an edge to `target`.
def Explain.pred(+td: Nat, +g: G.Graph(td), cands: List<&2, U32>,
  +target: U32, got: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match cands:
    case Nil{}:
      got
    case Con{u, t}:
      match got:
        case Some{x}:
          Some{x}
        case None{}:
          +uu = u
          Explain.pred(td, g, t, target,
            Explain.opt(uu, G.Graph.edge(td, g, uu, target)))

def Explain.head_lvl(rev: R.Levels) -> List<&2, U32>:
  match rev:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      l

def Explain.upto.fin(acc: R.Levels, found: Bool) -> R.Levels:
  match found:
    case True{}:
      acc
    case False{}:
      Nil{}

# The levels up to and including the first one that holds `target`, reversed.
# Empty when no level holds it, which is how "not reachable" is reported.
def Explain.upto(levels: R.Levels, +target: U32, acc: R.Levels,
  found: Bool) -> R.Levels:
  match levels:
    case Nil{}:
      Explain.upto.fin(acc, found)
    case Con{l, t}:
      match found:
        case True{}:
          acc
        case False{}:
          +ll = l
          Explain.upto(t, target, Con{ll, acc},
            List.contains(~U32, ~U32.is_eq, ll, target))

# Walk back down the levels, prepending each vertex.
def Explain.walk(+td: Nat, +g: G.Graph(td), +rev: R.Levels, +cur: U32,
  acc: List<&2, U32>, p: Maybe<&2, U32>) -> List<&2, U32>:
  match rev:
    case Nil{}:
      Con{cur, acc}
    case Con{lvl, t}:
      match p:
        case None{}:
          Con{cur, acc}
        case Some{u}:
          +uu = u
          Explain.walk(td, g, t, uu, Con{cur, acc},
            Explain.pred(td, g, Explain.head_lvl(t), uu, None{}))

def Explain.path.go(+td: Nat, +g: G.Graph(td), +rev: R.Levels,
  +target: U32) -> List<&2, U32>:
  match rev:
    case Nil{}:
      Nil{}
    case Con{lvl, t}:
      Explain.walk(td, g, t, target, Nil{},
        Explain.pred(td, g, Explain.head_lvl(t), target, None{}))

# A root-to-object path, or the empty list when the object is not reachable.
def Explain.path(+td: Nat, +g: G.Graph(td), levels: R.Levels,
  +target: U32) -> List<&2, U32>:
  Explain.path.go(td, g, Explain.upto(levels, target, Nil{}, False{}), target)

# ---------------------------------------------------------------------------
# Checking a witness. This is what law E-01 is stated over: the check, not the
# producer.
# ---------------------------------------------------------------------------

def Explain.steps_ok(+td: Nat, +g: G.Graph(td), path: List<&2, U32>,
  ok: Bool) -> Bool:
  match path:
    case Nil{}:
      ok
    case Con{u, t}:
      match t:
        case Nil{}:
          ok
        case Con{v, rest}:
          match ok:
            case False{}:
              False{}
            case True{}:
              +vv = v
              Explain.steps_ok(td, g, Con{vv, rest},
                G.Graph.edge(td, g, u, vv))

def Explain.last_is.un(m: Maybe<&2, U32>, +target: U32) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      U32.is_eq(x, target)

def Explain.last_is(path: List<&2, U32>, +target: U32) -> Bool:
  Explain.last_is.un(List.last(&2, U32, path), target)

def Explain.first_in.un(m: Maybe<&2, U32>, roots: List<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      List.contains(~U32, ~U32.is_eq, roots, x)

def Explain.first_in(path: List<&2, U32>, roots: List<&2, U32>) -> Bool:
  Explain.first_in.un(List.head(&2, U32, path), roots)

# Law E-01, as a runnable check: the path starts at a requested root, ends at
# the requested object, and every step is a real policy edge.
def Explain.valid(+td: Nat, +g: G.Graph(td), roots: List<&2, U32>,
  +path: List<&2, U32>, +target: U32) -> Bool:
  Bool.and(Explain.first_in(path, roots),
    Bool.and(Explain.last_is(path, target),
      Explain.steps_ok(td, g, path, True{})))
