# closure/graph.bend -- finite directed graphs over a universe's ordinals.
#
# An edge `x -> y` means: having the requirement rooted at x requires y, under
# the selected policy (SPEC 3.2). The orientation is deliberately the same for
# commits-to-parents and actions-to-inputs, so the same core serves a future
# build-CAS adapter without reinterpretation.
#
# Adjacency is complete by construction: `Graph.succ` of a vertex the table
# does not describe is not "a vertex with zero successors" -- the importer
# fails with `IncompleteGraph` before a graph reaches here, and
# `Graph.domain_ok` is the check that says so (SPEC 3.2).
#
# The generic core handles cycles. Termination comes from finiteness and a
# visited set, never from an assumption that artifact graphs are acyclic.

import Base
import ../core/count.bend as C
import ../core/set.bend as S
import ../core/trie.bend as T

def Succ() -> Data:
  List<&2, U32>

def Graph(td: Nat) -> Data:
  T.Trie<Succ>

def Graph.succ.un(m: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match m:
    case None{}:
      Nil{}
    case Some{s}:
      s

def Graph.has.un(m: Maybe<&2, List<&2, U32>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      True{}

def Graph.has(+td: Nat, +g: Graph(td), +v: U32) -> Bool:
  Graph.has.un(T.Trie.at(Succ, td, g, v))

# Is every ordinal in `vs` described by the table? An undescribed required
# object is `IncompleteGraph`, not an empty adjacency.
def Graph.domain_ok(+td: Nat, +g: Graph(td), vs: List<&2, U32>, ok: Bool) ->
  Bool:
  match vs:
    case Nil{}:
      ok
    case Con{v, t}:
      match ok:
        case False{}:
          False{}
        case True{}:
          Graph.domain_ok(td, g, t, Graph.has(td, g, v))

# The successors recorded for `v`. An ordinal with no entry answers the empty
# list; `Graph.domain_ok` is what establishes that no *required* ordinal is in
# that state.
def Graph.succ(+td: Nat, +g: Graph(td), +v: U32) -> List<&2, U32>:
  Graph.succ.un(T.Trie.at(Succ, td, g, v))

# post(G, X): every successor of every member of `X`, as a list with
# duplicates. Callers fold it into a set, which removes them.
def Graph.gather(+td: Nat, +g: Graph(td), vs: List<&2, U32>,
  acc: List<&2, U32>) -> List<&2, U32>:
  match vs:
    case Nil{}:
      acc
    case Con{v, t}:
      Graph.gather(td, g, t,
        List.append(&2, U32, Graph.succ(td, g, v), acc))

def Graph.post(+td: Nat, +g: Graph(td), +sd: Nat, xs: List<&2, U32>) ->
  S.PSet:
  S.PSet.from_list(sd, Graph.gather(td, g, xs, Nil{}))

# Does `v` have an edge to `w`?
def Graph.edge(+td: Nat, +g: Graph(td), +v: U32, +w: U32) -> Bool:
  List.contains(~U32, ~U32.is_eq, Graph.succ(td, g, v), w)
