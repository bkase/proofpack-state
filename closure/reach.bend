# closure/reach.bend -- the production reachability traversal.
#
# Set-at-a-time breadth-first search. Each round gathers the successors of the
# current frontier, subtracts what is already seen, and takes the remainder as
# the next frontier. The subtraction and the union are the proved tree
# operations of core/set.bend, so no per-vertex membership test happens at
# all: the cost of a round is one pass over the frontier's adjacency plus two
# tree walks, not |frontier| * depth lookups.
#
# Each vertex is expanded at most once, because a vertex only enters a
# frontier when it was absent from `seen`, and `seen` only grows.
#
# Termination is by an explicit decreasing `Nat` budget derived from the
# finite universe, not by `@unsafe` (SPEC 6.1). Running out returns
# `done = False`, which the caller must report as `ResourceLimit`: an
# unfinished traversal is never dressed up as a successful result (SPEC 3.3).
#
# The traversal records its frontiers. They are the BFS levels, which are the
# ranks a closure certificate needs (SPEC 4.4) and the layers an `explain`
# witness walks back through (law E-01).

import Base
import ../core/count.bend as C
import ../core/set.bend as S
import ../core/trie.bend as T
import ./graph.bend as G

def Levels() -> Data:
  List<&2, List<&2, U32>>

type Reach.Out<-sd: Nat> is Data:
  Out{seen: S.PSet(sd), levels: Levels, done: Bool, rounds: Nat}

def Reach.go(+fuel: Nat, +td: Nat, +g: G.Graph(td), +sd: Nat,
  +seen: S.PSet(sd), front: List<&2, U32>, levels: Levels, rounds: Nat) ->
  Reach.Out<sd>:
  match fuel:
    case 0n:
      Out{seen, levels, False{}, rounds}
    case 1n+f:
      match front:
        case Nil{}:
          Out{seen, levels, True{}, rounds}
        case Con{v, t}:
          +f0 = {Con{v, t} : List<&2, U32>}
          +cand = S.PSet.from_list(sd, G.Graph.gather(td, g, f0, Nil{}))
          Reach.go(f, td, g, sd, S.PSet.union(sd, seen, cand),
            S.PSet.to_list(sd, S.PSet.diff(sd, cand, seen)),
            Con{f0, levels}, 1n+rounds)

# `n` is the universe size. A round that does not finish the traversal adds at
# least one vertex, so n+2 rounds always suffice and exhausting them means the
# graph was larger than the universe it was declared over.
def Reach.closure(+n: Nat, +td: Nat, +g: G.Graph(td), +sd: Nat,
  +roots: List<&2, U32>) -> Reach.Out<sd>:
  Reach.go(2n+n, td, g, sd, S.PSet.from_list(sd, roots), roots, Nil{}, 0n)

def Reach.seen(+sd: Nat, o: Reach.Out<sd>) -> S.PSet(sd):
  match o:
    case Out{seen, levels, done, rounds}:
      seen

def Reach.done(+sd: Nat, o: Reach.Out<sd>) -> Bool:
  match o:
    case Out{seen, levels, done, rounds}:
      done

def Reach.levels(+sd: Nat, o: Reach.Out<sd>) -> Levels:
  match o:
    case Out{seen, levels, done, rounds}:
      List.reverse(&2, List<&2, U32>, levels)

def Reach.rounds(+sd: Nat, o: Reach.Out<sd>) -> Nat:
  match o:
    case Out{seen, levels, done, rounds}:
      rounds
