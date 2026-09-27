# proofs/traverse.bend -- C-02, in part: the traversal never loses a vertex.
#
# The production traversal is a frontier walk with a `seen` set: a vertex
# enters the next frontier only when it was absent from `seen`, and `seen`
# only grows. "Only grows" is the invariant the whole refinement argument
# rests on -- it is why each vertex is expanded at most once, which is why
# the budget suffices, and it is what makes the answer at least the closure.
#
# It is also the half of C-02 that can be proved without relating the
# traversal to the specification iteration. That relation needs the induction
# to carry "this round is inside the specification's round" as a reusable
# hypothesis, which runs into the same wall as C-01's leastness. What is here
# instead is unconditional: whatever the traversal has seen it keeps, so the
# roots it started from are in the answer it returns -- an answer that
# dropped a requested root would be wrong in the direction that matters, and
# this rules it out.

import Base
import ./eq.bend as E
import ./shape.bend as Sh
import ./preserve.bend as Pr
import ./insert.bend as Ins
import ./only.bend as On
import ../core/set.bend as S
import ../closure/graph.bend as G
import ../closure/reach.bend as R

law Reach.push_keeps:
  for +ws: List<&2, U32>
  for +st: R.Push
  for +x: U32
  for +v: {Sh.PSet.wf(20n, R.Push.seen(st), True{}) == True{} : Bool}
  for +ok: {S.PSet.member(20n, R.Push.seen(st), x) == True{} : Bool}
  {S.PSet.member(20n, R.Push.seen(R.Reach.push(20n, ws, st)), x)
    == True{} : Bool}

# One vertex: either it was already there, or it is inserted -- and insertion
# neither loses a member nor spoils the shape.
law Reach.push_one_keeps:
  for +st: R.Push
  for +w: U32
  for +have: Bool
  for +eh: {have == S.PSet.member(20n, R.Push.seen(st), w) : Bool}
  for +x: U32
  for +v: {Sh.PSet.wf(20n, R.Push.seen(st), True{}) == True{} : Bool}
  for +ok: {S.PSet.member(20n, R.Push.seen(st), x) == True{} : Bool}
  {S.PSet.member(20n, R.Push.seen(R.Reach.push.one(20n, w, st)), x)
    == True{} : Bool}

def Reach.push_one_keeps(st, w, have, eh, x, v, ok):
  match st:
    case R.Pu{seen, next}:
      match have:
        case True{}:
          %eh : {S.PSet.member(20n, R.Push.seen(
              R.Reach.push.add(20n, w, seen, next, _)), x)
            == True{} : Bool}
          ok
        case False{}:
          %eh : {S.PSet.member(20n, R.Push.seen(
              R.Reach.push.add(20n, w, seen, next, _)), x)
            == True{} : Bool}
          Ins.PSet.insert_keeps(seen, w, x, v, ok)

law Reach.push_one_wf:
  for +st: R.Push
  for +w: U32
  for +have: Bool
  for +eh: {have == S.PSet.member(20n, R.Push.seen(st), w) : Bool}
  for +v: {Sh.PSet.wf(20n, R.Push.seen(st), True{}) == True{} : Bool}
  {Sh.PSet.wf(20n, R.Push.seen(R.Reach.push.one(20n, w, st)), True{})
    == True{} : Bool}

def Reach.push_one_wf(st, w, have, eh, v):
  match st:
    case R.Pu{seen, next}:
      match have:
        case True{}:
          %eh : {Sh.PSet.wf(20n, R.Push.seen(
              R.Reach.push.add(20n, w, seen, next, _)), True{})
            == True{} : Bool}
          v
        case False{}:
          %eh : {Sh.PSet.wf(20n, R.Push.seen(
              R.Reach.push.add(20n, w, seen, next, _)), True{})
            == True{} : Bool}
          Pr.PSet.wf_insert(20n, seen, w, v)

def Reach.push_keeps(ws, st, x, v, ok):
  match ws:
    case Nil{}:
      ok
    case Con{w, t}:
      Reach.push_keeps(t, R.Reach.push.one(20n, w, st), x,
        Reach.push_one_wf(st, w, S.PSet.member(20n, R.Push.seen(st), w),
          {==}, v),
        Reach.push_one_keeps(st, w, S.PSet.member(20n, R.Push.seen(st), w),
          {==}, x, v, ok))

law Reach.push_wf:
  for +ws: List<&2, U32>
  for +st: R.Push
  for +v: {Sh.PSet.wf(20n, R.Push.seen(st), True{}) == True{} : Bool}
  {Sh.PSet.wf(20n, R.Push.seen(R.Reach.push(20n, ws, st)), True{})
    == True{} : Bool}

def Reach.push_wf(ws, st, v):
  match ws:
    case Nil{}:
      v
    case Con{w, t}:
      Reach.push_wf(t, R.Reach.push.one(20n, w, st),
        Reach.push_one_wf(st, w, S.PSet.member(20n, R.Push.seen(st), w),
          {==}, v))

# ---------------------------------------------------------------------------
# The walk. Every round either expands a vertex -- which pushes, and pushing
# keeps -- or rotates a level, which touches nothing.
# ---------------------------------------------------------------------------

law Reach.go_keeps:
  for +fuel: Nat
  for +td: Nat
  for +g: G.Graph()
  for +seen: S.PSet
  for +front: List<&2, U32>
  for +next: List<&2, U32>
  for +levels: R.Levels()
  for +rounds: Nat
  for +x: U32
  for +v: {Sh.PSet.wf(20n, seen, True{}) == True{} : Bool}
  for +ok: {S.PSet.member(20n, seen, x) == True{} : Bool}
  {S.PSet.member(20n, R.Reach.seen(20n,
      R.Reach.go(fuel, td, g, 20n, seen, front, next, levels, rounds)), x)
    == True{} : Bool}

def Reach.go_keeps(fuel, td, g, seen, front, next, levels, rounds, x, v,
  ok):
  match fuel:
    case 0n:
      ok
    case 1n+f:
      match front:
        case Con{w, t}:
          Reach.go_keeps(f, td, g,
            R.Push.seen(R.Reach.push(20n, G.Graph.succ(td, g, w),
              R.Pu{seen, next})), t,
            R.Push.next(R.Reach.push(20n, G.Graph.succ(td, g, w),
              R.Pu{seen, next})), levels, rounds, x,
            Reach.push_wf(G.Graph.succ(td, g, w), R.Pu{seen, next}, v),
            Reach.push_keeps(G.Graph.succ(td, g, w), R.Pu{seen, next}, x,
              v, ok))
        case Nil{}:
          match next:
            case Nil{}:
              ok
            case Con{n0, nt}:
              Reach.go_keeps(f, td, g, seen, Con{n0, nt}, Nil{},
                Con{Con{n0, nt}, levels}, 1n+rounds, x, v, ok)

law Reach.closure_keeps_its_roots:
  for +n: Nat
  for +td: Nat
  for +g: G.Graph()
  for +roots: List<&2, U32>
  for +r: U32
  for +ok: {List.contains(~U32, ~U32.is_eq, roots, r) == True{} : Bool}
  {S.PSet.member(20n, R.Reach.seen(20n,
      R.Reach.closure(n, td, g, 20n, roots)), r) == True{} : Bool}

def Reach.closure_keeps_its_roots(n, td, g, roots, r, ok):
  Reach.go_keeps(2n+Nat.add(n, n), td, g,
    S.PSet.from_list(20n, roots), roots, Nil{}, [roots], 0n, r,
    Pr.PSet.wf_from_list(20n, roots),
    Ins.PSet.from_list_contains(roots, r, ok))
