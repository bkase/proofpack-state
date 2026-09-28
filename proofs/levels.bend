# proofs/levels.bend -- the traversal's levels really are a layering.
#
# proofs/layering.bend proves that a witness walked back through a layering
# starts at a requested root. This module proves the traversal produces one:
# level 0 is the roots, and every vertex of every later level has an edge from
# the level before it.
#
# The invariant is carried through `Reach.go` as decidable data, three
# conjuncts: the levels so far are a ladder, every vertex still on the current
# frontier belongs to the head level, and every vertex collected for the next
# level has a predecessor in the head level. The frontier fold is what
# re-establishes the third -- a vertex only enters `next` as a successor of the
# vertex being expanded, and that vertex is in the head level.

import Base
import ./eq.bend as E
import ./layering.bend as Ly
import ../core/set.bend as S
import ../closure/graph.bend as G
import ../closure/reach.bend as R
import ../closure/explain.bend as Xp

def Lv.out_levels(o: R.Reach.Out) -> R.Levels:
  match o:
    case R.Out{seen, levels, done, rounds}:
      levels

def Lv.levels_eq(+sd: Nat, +o: R.Reach.Out)
  -> {R.Reach.levels(sd, o)
    == List.reverse(&2, List<&2, U32>, Lv.out_levels(o)) : R.Levels}:
  match o:
    case R.Out{seen, levels, done, rounds}:
      {==}

# ---------------------------------------------------------------------------
# The frontier fold keeps every collected vertex one edge below the head
# level.
# ---------------------------------------------------------------------------

law Lv.push_pred:
  for +sd: Nat
  for +td: Nat
  for +g: G.Graph()
  for +ws: List<&2, U32>
  for +seen: S.PSet
  for +next: List<&2, U32>
  for +head: List<&2, U32>
  for +aw: {Ly.Ex.all_pred(td, g, ws, head) == True{} : Bool}
  for +an: {Ly.Ex.all_pred(td, g, next, head) == True{} : Bool}
  {Ly.Ex.all_pred(td, g,
    R.Push.next(R.Reach.push(sd, ws, R.Pu{seen, next})), head)
    == True{} : Bool}

def Lv.push_pred.pick(+sd: Nat, +td: Nat, +g: G.Graph(), +w: U32,
  +t: List<&2, U32>, +seen: S.PSet, +next: List<&2, U32>,
  +head: List<&2, U32>, +have: Bool,
  ihT: {Ly.Ex.all_pred(td, g,
    R.Push.next(R.Reach.push(sd, t, R.Pu{seen, next})), head)
    == True{} : Bool},
  ihF: {Ly.Ex.all_pred(td, g,
    R.Push.next(R.Reach.push(sd, t,
      R.Pu{S.PSet.insert(sd, seen, w), Con{w, next}})), head)
    == True{} : Bool})
  -> {Ly.Ex.all_pred(td, g,
    R.Push.next(R.Reach.push(sd, t,
      R.Reach.push.add(sd, w, seen, next, have))), head)
    == True{} : Bool}:
  match have:
    case True{}:
      ihT
    case False{}:
      ihF

def Lv.push_pred(sd, td, g, ws, seen, next, head, aw, an):
  match ws:
    case Nil{}:
      an
    case Con{w, t}:
      Lv.push_pred.pick(sd, td, g, w, t, seen, next, head,
        S.PSet.member(sd, seen, w),
        Lv.push_pred(sd, td, g, t, seen, next, head,
          E.Bool.and_r(Ly.Ex.has_pred(td, g, head, w),
            Ly.Ex.all_pred(td, g, t, head), aw), an),
        Lv.push_pred(sd, td, g, t, S.PSet.insert(sd, seen, w),
          Con{w, next}, head,
          E.Bool.and_r(Ly.Ex.has_pred(td, g, head, w),
            Ly.Ex.all_pred(td, g, t, head), aw),
          E.Bool.and_both(Ly.Ex.has_pred(td, g, head, w),
            Ly.Ex.all_pred(td, g, next, head),
            E.Bool.and_l(Ly.Ex.has_pred(td, g, head, w),
              Ly.Ex.all_pred(td, g, t, head), aw), an)))

# ---------------------------------------------------------------------------
# The level rotation extends the ladder by one rung.
# ---------------------------------------------------------------------------

def Lv.rotate(+td: Nat, +g: G.Graph(), +n0: U32, +nt: List<&2, U32>,
  +levels: R.Levels, +roots: List<&2, U32>,
  +ld: {Ly.Ex.ladder(td, g, levels, roots) == True{} : Bool},
  +ap: {Ly.Ex.all_pred(td, g, Con{n0, nt},
    Xp.Explain.head_lvl(levels)) == True{} : Bool})
  -> {Ly.Ex.ladder(td, g, Con{Con{n0, nt}, levels}, roots)
    == True{} : Bool}:
  match levels:
    case Nil{}:
      E.Bool.noconf({Ly.Ex.all_in(Con{n0, nt}, roots) == True{} : Bool},
        E.Bool.and_l(Ly.Ex.has_pred(td, g, Nil{}, n0),
          Ly.Ex.all_pred(td, g, nt, Nil{}), ap))
    case Con{h, r}:
      E.Bool.and_both(Ly.Ex.all_pred(td, g, Con{n0, nt}, h),
        Ly.Ex.ladder(td, g, Con{h, r}, roots), ap, ld)

# ---------------------------------------------------------------------------
# The invariant, and that the traversal keeps it.
#
# Three conjuncts, carried separately because each is decidable data and so
# may be used as often as the step needs:
#
#   ld  the levels recorded so far are a ladder
#   fr  every vertex still on the frontier belongs to the head level
#   nx  every vertex collected for the next level has a predecessor in the
#       head level
# ---------------------------------------------------------------------------

law Lv.go_ladder:
  for +fuel: Nat
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +seen: S.PSet
  for +front: List<&2, U32>
  for +next: List<&2, U32>
  for +levels: R.Levels
  for +rounds: Nat
  for +roots: List<&2, U32>
  for +ld: {Ly.Ex.ladder(td, g, levels, roots) == True{} : Bool}
  for +fr: {Ly.Ex.all_in(front, Xp.Explain.head_lvl(levels))
    == True{} : Bool}
  for +nx: {Ly.Ex.all_pred(td, g, next, Xp.Explain.head_lvl(levels))
    == True{} : Bool}
  {Ly.Ex.ladder(td, g, Lv.out_levels(R.Reach.go(fuel, td, g, sd, seen,
    front, next, levels, rounds)), roots) == True{} : Bool}

def Lv.go_ladder(fuel, td, g, sd, seen, front, next, levels, rounds,
  roots, ld, fr, nx):
  match fuel:
    case 0n:
      ld
    case 1n+f:
      match front:
        case Con{v, t}:
          Lv.go_ladder(f, td, g, sd,
            R.Push.seen(R.Reach.push(sd, G.Graph.succ(td, g, v),
              R.Pu{seen, next})), t,
            R.Push.next(R.Reach.push(sd, G.Graph.succ(td, g, v),
              R.Pu{seen, next})), levels, rounds, roots, ld,
            E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
              Xp.Explain.head_lvl(levels), v),
              Ly.Ex.all_in(t, Xp.Explain.head_lvl(levels)), fr),
            Lv.push_pred(sd, td, g, G.Graph.succ(td, g, v), seen, next,
              Xp.Explain.head_lvl(levels),
              Ly.Ex.all_pred_succ(td, g, v,
                Xp.Explain.head_lvl(levels),
                E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                  Xp.Explain.head_lvl(levels), v),
                  Ly.Ex.all_in(t, Xp.Explain.head_lvl(levels)), fr)),
              nx))
        case Nil{}:
          match next:
            case Nil{}:
              ld
            case Con{n0, nt}:
              Lv.go_ladder(f, td, g, sd, seen, Con{n0, nt}, Nil{},
                Con{Con{n0, nt}, levels}, 1n+rounds, roots,
                Lv.rotate(td, g, n0, nt, levels, roots, ld, nx),
                Ly.Ex.all_in_self(Con{n0, nt}), {==})

# ---------------------------------------------------------------------------
# What `Reach.closure` returns.
#
# It starts with the roots as level 0 and the roots as the frontier, so the
# invariant holds at the start for the same reason both times: every member of
# a list is in that list.
# ---------------------------------------------------------------------------

law Lv.closure_chain:
  for +n: Nat
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +roots: List<&2, U32>
  {Ly.Ex.chain(td, g,
    R.Reach.levels(sd, R.Reach.closure(n, td, g, sd, roots)), roots)
    == True{} : Bool}

def Lv.closure_chain(n, td, g, sd, roots):
  %Equal.sym(R.Levels,
    R.Reach.levels(sd, R.Reach.closure(n, td, g, sd, roots)),
    List.reverse(&2, List<&2, U32>,
      Lv.out_levels(R.Reach.closure(n, td, g, sd, roots))),
    Lv.levels_eq(sd, R.Reach.closure(n, td, g, sd, roots)))
    : {Ly.Ex.chain(td, g, _, roots) == True{} : Bool}
  Ly.Ex.chain_of_ladder(td, g,
    Lv.out_levels(R.Reach.closure(n, td, g, sd, roots)), roots,
    Lv.go_ladder(2n+Nat.add(n, n), td, g, sd,
      S.PSet.from_list(sd, roots), roots, Nil{}, Con{roots, Nil{}}, 0n,
      roots, Ly.Ex.all_in_self(roots), Ly.Ex.all_in_self(roots), {==}))

# ---------------------------------------------------------------------------
# E-01, part three.
#
# The hypothesis is that the target appears in some level of the traversal --
# which is exactly "the object is reachable", and exactly the case in which
# `Explain.path` produces a witness at all. Without it the law is false rather
# than unproved: an unreachable object gets the empty path, and the empty path
# starts nowhere.
# ---------------------------------------------------------------------------

law Lv.witness_root:
  for +n: Nat
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +roots: List<&2, U32>
  for +target: U32
  for +sw: {Ly.Ex.somewhere(R.Reach.levels(sd,
    R.Reach.closure(n, td, g, sd, roots)), target) == True{} : Bool}
  {Xp.Explain.first_in(Xp.Explain.path(td, g,
    R.Reach.levels(sd, R.Reach.closure(n, td, g, sd, roots)), target),
    roots) == True{} : Bool}

def Lv.witness_root(n, td, g, sd, roots, target, sw):
  Ly.Ex.path_root(td, g,
    R.Reach.levels(sd, R.Reach.closure(n, td, g, sd, roots)), target,
    roots, Lv.closure_chain(n, td, g, sd, roots), sw)
