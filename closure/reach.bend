# closure/reach.bend -- the production reachability traversal.
#
# Breadth-first search, one vertex at a time.
#
# This was set-at-a-time at first: each round gathered the whole frontier's
# successors and subtracted `seen` with a tree difference, so no per-vertex
# membership test happened at all. That is the better shape when a round's
# frontier is large -- and the wrong shape for Git history, where it is not.
# A repository with a long commit chain takes one round per commit, and a
# round that re-walks the whole `seen` tree to add one vertex makes the
# traversal quadratic: on a 16k-object repository it ran for minutes at full
# CPU.
#
# Per-vertex is the right trade here. A membership test is about twenty trie
# steps plus a leaf lookup, and an insert copies one path, so a round costs
# what its frontier costs and nothing more. `PSet.member` and `PSet.insert`
# are the same proved operations either way.
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

type Reach.Out is Data:
  Out{seen: S.PSet, levels: Levels, done: Bool, rounds: Nat}

# The state of one successor fold: what has been seen, and what the next
# frontier has collected so far.
type Push is Data:
  Pu{seen: S.PSet, next: List<&2, U32>}

def Reach.push.add(+sd: Nat, +w: U32, +seen: S.PSet,
  next: List<&2, U32>, have: Bool) -> Push:
  match have:
    case True{}:
      Pu{seen, next}
    case False{}:
      Pu{S.PSet.insert(sd, seen, w), Con{w, next}}

def Reach.push.one(+sd: Nat, +w: U32, st: Push) -> Push:
  match st:
    case Pu{seen, next}:
      +s = seen
      Reach.push.add(sd, w, s, next, S.PSet.member(sd, s, w))

# A vertex enters a frontier only when it was absent from `seen`, and `seen`
# only grows, so each vertex is expanded at most once.
def Reach.push(+sd: Nat, ws: List<&2, U32>, st: Push) -> Push:
  match ws:
    case Nil{}:
      st
    case Con{w, t}:
      Reach.push(sd, t, Reach.push.one(sd, w, st))

def Push.seen(p: Push) -> S.PSet:
  match p:
    case Pu{seen, next}:
      seen

def Push.next(p: Push) -> List<&2, U32>:
  match p:
    case Pu{seen, next}:
      next

# Termination is an explicit decreasing `Nat` budget derived from the finite
# universe, not `@unsafe` (SPEC 6.1). Running out returns `done = False`,
# which the caller must report as `ResourceLimit`: an unfinished traversal is
# never dressed up as a successful result (SPEC 3.3).
def Reach.go(+fuel: Nat, +td: Nat, +g: G.Graph(), +sd: Nat, seen: S.PSet,
  front: List<&2, U32>, next: List<&2, U32>, levels: Levels,
  rounds: Nat) -> Reach.Out:
  match fuel:
    case 0n:
      Out{seen, levels, False{}, rounds}
    case 1n+f:
      match front:
        case Con{v, t}:
          +st = Reach.push(sd, G.Graph.succ(td, g, v), Pu{seen, next})
          Reach.go(f, td, g, sd, Push.seen(st), t, Push.next(st), levels,
            rounds)
        case Nil{}:
          match next:
            case Nil{}:
              Out{seen, levels, True{}, rounds}
            case Con{n0, nt}:
              +nn = {Con{n0, nt} : List<&2, U32>}
              Reach.go(f, td, g, sd, seen, nn, Nil{}, Con{nn, levels},
                1n+rounds)

# Each vertex is expanded once and each level rotation consumes at least one
# vertex, so 2n+2 steps always suffice; exhausting them means the graph was
# larger than the universe it was declared over.
def Reach.closure(+n: Nat, +td: Nat, +g: G.Graph(), +sd: Nat,
  +roots: List<&2, U32>) -> Reach.Out:
  Reach.go(2n+Nat.add(n, n), td, g, sd, S.PSet.from_list(sd, roots), roots,
    Nil{}, [roots], 0n)

def Reach.seen(+sd: Nat, o: Reach.Out) -> S.PSet:
  match o:
    case Out{seen, levels, done, rounds}:
      seen

def Reach.done(+sd: Nat, o: Reach.Out) -> Bool:
  match o:
    case Out{seen, levels, done, rounds}:
      done

def Reach.levels(+sd: Nat, o: Reach.Out) -> Levels:
  match o:
    case Out{seen, levels, done, rounds}:
      List.reverse(&2, List<&2, U32>, levels)

def Reach.rounds(+sd: Nat, o: Reach.Out) -> Nat:
  match o:
    case Out{seen, levels, done, rounds}:
      rounds
