# proofs/layering.bend -- why a witness starts at a root (law E-01, part 3).
#
# `Explain.walk` climbs back down the traversal's levels: from the level that
# holds the target, it picks a predecessor in the level below, then a
# predecessor of that one, and so on. It stops early -- with whatever vertex
# it reached -- if some level has no predecessor for the vertex it is on. So
# "the witness starts at a requested root" is not a fact about the walk. It is
# a fact about the levels: level 0 is inside the roots, and every later level
# has, for each of its vertices, an edge from the level before.
#
# `Ex.ladder` is that property, as decidable data over the reversed level list
# the walk consumes. It has to be data rather than a quantified hypothesis
# because the induction uses it at every level, and an affine hypothesis
# cannot be used twice.
#
# This module proves the walk half: given the ladder, the walk reaches level 0
# and stops on a root. proofs/levels.bend proves the other half -- that the
# traversal's own levels are a ladder.

import Base
import ./eq.bend as E
import ../core/count.bend as C
import ../closure/graph.bend as G
import ../closure/reach.bend as R
import ../closure/explain.bend as Xp

# ---------------------------------------------------------------------------
# The ladder.
# ---------------------------------------------------------------------------

# Does `u` have a predecessor in `prev`?
def Ex.has_pred(+td: Nat, +g: G.Graph(), +prev: List<&2, U32>,
  +u: U32) -> Bool:
  Maybe.is_some(&2, U32, Xp.Explain.pred(td, g, prev, u, None{}))

# Does every vertex of `l`?
def Ex.all_pred(+td: Nat, +g: G.Graph(), +l: List<&2, U32>,
  +prev: List<&2, U32>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case Con{u, t}:
      Bool.and(Ex.has_pred(td, g, prev, u), Ex.all_pred(td, g, t, prev))

def Ex.all_in(+l: List<&2, U32>, +roots: List<&2, U32>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case Con{u, t}:
      Bool.and(List.contains(~U32, ~U32.is_eq, roots, u),
        Ex.all_in(t, roots))

# `ls` is the levels the walk still has below it, newest first. The last one
# is level 0, which has to be inside the roots; every other one has to be one
# edge above the one after it.
def Ex.ladder(+td: Nat, +g: G.Graph(), +ls: R.Levels,
  +roots: List<&2, U32>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l, t}:
      match t:
        case Nil{}:
          Ex.all_in(l, roots)
        case Con{l2, r}:
          Bool.and(Ex.all_pred(td, g, l, l2),
            Ex.ladder(td, g, Con{l2, r}, roots))

# ---------------------------------------------------------------------------
# Reading the two list predicates back at a member.
# ---------------------------------------------------------------------------

def Bool.or_on_r(+p: Bool, +q: Bool,
  +ep: {p == False{} : Bool},
  +on: {Bool.or(p, q) == True{} : Bool}) -> {q == True{} : Bool}:
  %ep : {Bool.or(_, q) == True{} : Bool}
  on

law Ex.all_pred_at:
  for +td: Nat
  for +g: G.Graph()
  for +l: List<&2, U32>
  for +prev: List<&2, U32>
  for +u: U32
  for +ap: {Ex.all_pred(td, g, l, prev) == True{} : Bool}
  for mem: {List.contains(~U32, ~U32.is_eq, l, u) == True{} : Bool}
  {Ex.has_pred(td, g, prev, u) == True{} : Bool}

def Ex.all_pred_at.pick(+td: Nat, +g: G.Graph(), +h: U32,
  +t: List<&2, U32>, +prev: List<&2, U32>, +u: U32, +e: Bool,
  +ee: {e == U32.is_eq(h, u) : Bool},
  +hd: {Ex.has_pred(td, g, prev, h) == True{} : Bool},
  ih: {List.contains(~U32, ~U32.is_eq, t, u) == True{} : Bool} ->
    {Ex.has_pred(td, g, prev, u) == True{} : Bool},
  mem: {Bool.or(U32.is_eq(h, u),
    List.contains(~U32, ~U32.is_eq, t, u)) == True{} : Bool})
  -> {Ex.has_pred(td, g, prev, u) == True{} : Bool}:
  match e:
    case True{}:
      %E.U32.eq_reflect(h, u, E.Bool.sym(True{}, U32.is_eq(h, u), ee))
        : {Ex.has_pred(td, g, prev, _) == True{} : Bool}
      hd
    case False{}:
      ih(Bool.or_on_r(U32.is_eq(h, u),
        List.contains(~U32, ~U32.is_eq, t, u),
        E.Bool.sym(False{}, U32.is_eq(h, u), ee), mem))

def Ex.all_pred_at(td, g, l, prev, u, ap, mem):
  match l:
    case Nil{}:
      E.Bool.noconf({Ex.has_pred(td, g, prev, u) == True{} : Bool}, mem)
    case Con{h, t}:
      Ex.all_pred_at.pick(td, g, h, t, prev, u, U32.is_eq(h, u), {==},
        E.Bool.and_l(Ex.has_pred(td, g, prev, h),
          Ex.all_pred(td, g, t, prev), ap),
        Ex.all_pred_at(td, g, t, prev, u,
          E.Bool.and_r(Ex.has_pred(td, g, prev, h),
            Ex.all_pred(td, g, t, prev), ap)), mem)

law Ex.all_in_at:
  for +l: List<&2, U32>
  for +roots: List<&2, U32>
  for +u: U32
  for +ai: {Ex.all_in(l, roots) == True{} : Bool}
  for mem: {List.contains(~U32, ~U32.is_eq, l, u) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, roots, u) == True{} : Bool}

def Ex.all_in_at.pick(+h: U32, +t: List<&2, U32>,
  +roots: List<&2, U32>, +u: U32, +e: Bool,
  +ee: {e == U32.is_eq(h, u) : Bool},
  +hd: {List.contains(~U32, ~U32.is_eq, roots, h) == True{} : Bool},
  ih: {List.contains(~U32, ~U32.is_eq, t, u) == True{} : Bool} ->
    {List.contains(~U32, ~U32.is_eq, roots, u) == True{} : Bool},
  mem: {Bool.or(U32.is_eq(h, u),
    List.contains(~U32, ~U32.is_eq, t, u)) == True{} : Bool})
  -> {List.contains(~U32, ~U32.is_eq, roots, u) == True{} : Bool}:
  match e:
    case True{}:
      %E.U32.eq_reflect(h, u, E.Bool.sym(True{}, U32.is_eq(h, u), ee))
        : {List.contains(~U32, ~U32.is_eq, roots, _) == True{} : Bool}
      hd
    case False{}:
      ih(Bool.or_on_r(U32.is_eq(h, u),
        List.contains(~U32, ~U32.is_eq, t, u),
        E.Bool.sym(False{}, U32.is_eq(h, u), ee), mem))

def Ex.all_in_at(l, roots, u, ai, mem):
  match l:
    case Nil{}:
      E.Bool.noconf({List.contains(~U32, ~U32.is_eq, roots, u)
        == True{} : Bool}, mem)
    case Con{h, t}:
      Ex.all_in_at.pick(h, t, roots, u, U32.is_eq(h, u), {==},
        E.Bool.and_l(List.contains(~U32, ~U32.is_eq, roots, h),
          Ex.all_in(t, roots), ai),
        Ex.all_in_at(t, roots, u,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq, roots, h),
            Ex.all_in(t, roots), ai)), mem)

# ---------------------------------------------------------------------------
# The predecessor search answers a member of the list it searched.
# ---------------------------------------------------------------------------

def Bool.or_grow(+p: Bool, +q: Bool, +ok: {q == True{} : Bool})
  -> {Bool.or(p, q) == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      ok

def Bool.or_left(+p: Bool, +q: Bool, +ok: {p == True{} : Bool})
  -> {Bool.or(p, q) == True{} : Bool}:
  %E.Bool.sym(p, True{}, ok) : {Bool.or(_, q) == True{} : Bool}
  {==}

def Bool.or_swap(+p: Bool, +q: Bool,
  +ok: {Bool.or(p, q) == True{} : Bool})
  -> {Bool.or(q, p) == True{} : Bool}:
  match p:
    case True{}:
      match q:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match q:
        case True{}:
          {==}
        case False{}:
          ok

def Bool.or_drop(+p: Bool, +ok: {Bool.or(p, False{}) == True{} : Bool})
  -> {p == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      ok

def Bool.or_pad(+p: Bool, +ok: {p == True{} : Bool})
  -> {Bool.or(p, False{}) == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      ok

def Maybe.und(+d: U32, m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def Ex.some_inj(+a: U32, +b: U32,
  e: {Some{a} == Some{b} : Maybe<&2, U32>}) -> {a == b : U32}:
  Equal.cong(Maybe<&2, U32>, U32, Maybe.und(a), Some{a}, Some{b}, e)

def Ex.eq_true(+x: U32, +u: U32, +e: {x == u : U32})
  -> {U32.is_eq(x, u) == True{} : Bool}:
  %E.U32.sym(x, u, e) : {U32.is_eq(_, u) == True{} : Bool}
  E.U32.is_eq_refl(u)

def Ex.is_u(m: Maybe<&2, U32>, +u: U32) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      U32.is_eq(x, u)

law Ex.pred_acc:
  for +td: Nat
  for +g: G.Graph()
  for +cands: List<&2, U32>
  for +target: U32
  for +u: U32
  for +got: Maybe<&2, U32>
  for pm: {Xp.Explain.pred(td, g, cands, target, got) == Some{u}
    : Maybe<&2, U32>}
  {Bool.or(List.contains(~U32, ~U32.is_eq, cands, u), Ex.is_u(got, u))
    == True{} : Bool}

def Ex.pred_acc.step(+td: Nat, +g: G.Graph(), +h: U32,
  +t: List<&2, U32>, +u: U32, +e: Bool,
  ih: {Bool.or(List.contains(~U32, ~U32.is_eq, t, u),
    Ex.is_u(Xp.Explain.opt(h, e), u)) == True{} : Bool})
  -> {Bool.or(Bool.or(U32.is_eq(h, u),
    List.contains(~U32, ~U32.is_eq, t, u)), False{}) == True{} : Bool}:
  match e:
    case True{}:
      Bool.or_pad(Bool.or(U32.is_eq(h, u),
        List.contains(~U32, ~U32.is_eq, t, u)),
        Bool.or_swap(List.contains(~U32, ~U32.is_eq, t, u),
          U32.is_eq(h, u), ih))
    case False{}:
      Bool.or_pad(Bool.or(U32.is_eq(h, u),
        List.contains(~U32, ~U32.is_eq, t, u)),
        Bool.or_grow(U32.is_eq(h, u),
          List.contains(~U32, ~U32.is_eq, t, u),
          Bool.or_drop(List.contains(~U32, ~U32.is_eq, t, u), ih)))

def Ex.pred_acc(td, g, cands, target, u, got, pm):
  match cands:
    case Nil{}:
      %E.Maybe.sym(U32, got, Some{u}, pm)
        : {Bool.or(False{}, Ex.is_u(_, u)) == True{} : Bool}
      E.U32.is_eq_refl(u)
    case Con{h, t}:
      match got:
        case Some{x}:
          Bool.or_grow(List.contains(~U32, ~U32.is_eq, Con{h, t}, u),
            U32.is_eq(x, u),
            Ex.eq_true(x, u, Ex.some_inj(x, u, pm)))
        case None{}:
          Ex.pred_acc.step(td, g, h, t, u,
            G.Graph.edge(td, g, h, target),
            Ex.pred_acc(td, g, t, target, u,
              Xp.Explain.opt(h, G.Graph.edge(td, g, h, target)), pm))

# ---------------------------------------------------------------------------
# The walk.
#
# `Explain.walk` is at some vertex with the levels below it still to go. What
# it needs at each point is one step's worth of the ladder: a predecessor in
# the next level down, or -- when there is no next level -- membership of the
# roots. That is `Ex.step_ok`, and the ladder is what re-establishes it after
# the step.
# ---------------------------------------------------------------------------

def Ex.step_ok(+td: Nat, +g: G.Graph(), +rev: R.Levels, +cur: U32,
  +roots: List<&2, U32>) -> Bool:
  match rev:
    case Nil{}:
      List.contains(~U32, ~U32.is_eq, roots, cur)
    case Con{l, t}:
      Ex.has_pred(td, g, l, cur)

def Ex.ladder_tail(+td: Nat, +g: G.Graph(), +lvl: List<&2, U32>,
  +t: R.Levels, +roots: List<&2, U32>,
  +ld: {Ex.ladder(td, g, Con{lvl, t}, roots) == True{} : Bool})
  -> {Ex.ladder(td, g, t, roots) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{l2, r}:
      E.Bool.and_r(Ex.all_pred(td, g, lvl, l2),
        Ex.ladder(td, g, Con{l2, r}, roots), ld)

def Ex.step_ok_next(+td: Nat, +g: G.Graph(), +lvl: List<&2, U32>,
  +t: R.Levels, +roots: List<&2, U32>, +u: U32,
  +ld: {Ex.ladder(td, g, Con{lvl, t}, roots) == True{} : Bool},
  mem: {List.contains(~U32, ~U32.is_eq, lvl, u) == True{} : Bool})
  -> {Ex.step_ok(td, g, t, u, roots) == True{} : Bool}:
  match t:
    case Nil{}:
      Ex.all_in_at(lvl, roots, u, ld, mem)
    case Con{l2, r}:
      Ex.all_pred_at(td, g, lvl, l2, u,
        E.Bool.and_l(Ex.all_pred(td, g, lvl, l2),
          Ex.ladder(td, g, Con{l2, r}, roots), ld), mem)

law Ex.walk_root:
  for +td: Nat
  for +g: G.Graph()
  for +rev: R.Levels
  for +cur: U32
  for acc: List<&2, U32>
  for +roots: List<&2, U32>
  for +p: Maybe<&2, U32>
  for +ep: {p == Xp.Explain.pred(td, g, Xp.Explain.head_lvl(rev), cur,
    None{}) : Maybe<&2, U32>}
  for +ld: {Ex.ladder(td, g, rev, roots) == True{} : Bool}
  for +sp: {Ex.step_ok(td, g, rev, cur, roots) == True{} : Bool}
  {Xp.Explain.first_in(Xp.Explain.walk(td, g, rev, cur, acc, p), roots)
    == True{} : Bool}

def Ex.walk_root(td, g, rev, cur, acc, roots, p, ep, ld, sp):
  match rev:
    case Nil{}:
      sp
    case Con{lvl, t}:
      match p:
        case None{}:
          E.Bool.noconf({Xp.Explain.first_in(Con{cur, acc}, roots)
            == True{} : Bool},
            Equal.trans(Bool, False{}, Ex.has_pred(td, g, lvl, cur),
              True{},
              Equal.cong(Maybe<&2, U32>, Bool, Maybe.is_some(&2, U32),
                None{}, Xp.Explain.pred(td, g, lvl, cur, None{}), ep),
              sp))
        case Some{u}:
          Ex.walk_root(td, g, t, u, Con{cur, acc}, roots,
            Xp.Explain.pred(td, g, Xp.Explain.head_lvl(t), u, None{}),
            {==}, Ex.ladder_tail(td, g, lvl, t, roots, ld),
            Ex.step_ok_next(td, g, lvl, t, roots, u, ld,
              Bool.or_drop(List.contains(~U32, ~U32.is_eq, lvl, u),
                Ex.pred_acc(td, g, lvl, cur, u, None{},
                  E.Maybe.sym(U32, Some{u},
                    Xp.Explain.pred(td, g, lvl, cur, None{}), ep)))))

# ---------------------------------------------------------------------------
# From the level list the traversal returns.
#
# `Reach.levels` answers the levels oldest first, and `Explain.upto` reverses
# a prefix of them -- up to and including the first level that holds the
# target -- which is the order the walk consumes. `Ex.chain` is the ladder
# property stated in the oldest-first order, and the two lemmas below carry it
# and the target through that reversal.
# ---------------------------------------------------------------------------

def Ex.chain.go(+td: Nat, +g: G.Graph(), +ls: R.Levels,
  +prev: List<&2, U32>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l, t}:
      Bool.and(Ex.all_pred(td, g, l, prev), Ex.chain.go(td, g, t, l))

def Ex.chain(+td: Nat, +g: G.Graph(), +ls: R.Levels,
  +roots: List<&2, U32>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l0, t}:
      Bool.and(Ex.all_in(l0, roots), Ex.chain.go(td, g, t, l0))

# What the still-unread levels have to say about the ones already reversed.
def Ex.rest(+td: Nat, +g: G.Graph(), +ls: R.Levels, +acc: R.Levels,
  +roots: List<&2, U32>) -> Bool:
  match acc:
    case Nil{}:
      Ex.chain(td, g, ls, roots)
    case Con{a, r}:
      Ex.chain.go(td, g, ls, a)

def Ex.head_has(+rev: R.Levels, +target: U32) -> Bool:
  match rev:
    case Nil{}:
      False{}
    case Con{l, t}:
      List.contains(~U32, ~U32.is_eq, l, target)

def Ex.somewhere(+ls: R.Levels, +target: U32) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{l, t}:
      Bool.or(List.contains(~U32, ~U32.is_eq, l, target),
        Ex.somewhere(t, target))

def Ex.found_ok(+acc: R.Levels, +target: U32, +found: Bool) -> Bool:
  match found:
    case False{}:
      True{}
    case True{}:
      Ex.head_has(acc, target)

law Ex.upto_ladder:
  for +td: Nat
  for +g: G.Graph()
  for +ls: R.Levels
  for +target: U32
  for +acc: R.Levels
  for +found: Bool
  for +roots: List<&2, U32>
  for +ld: {Ex.ladder(td, g, acc, roots) == True{} : Bool}
  for +rs: {Ex.rest(td, g, ls, acc, roots) == True{} : Bool}
  {Ex.ladder(td, g, Xp.Explain.upto(ls, target, acc, found), roots)
    == True{} : Bool}

def Ex.upto_ladder.push(+td: Nat, +g: G.Graph(), +l: List<&2, U32>,
  +t: R.Levels, +acc: R.Levels, +roots: List<&2, U32>,
  +ld: {Ex.ladder(td, g, acc, roots) == True{} : Bool},
  +rs: {Ex.rest(td, g, Con{l, t}, acc, roots) == True{} : Bool})
  -> {Ex.ladder(td, g, Con{l, acc}, roots) == True{} : Bool}:
  match acc:
    case Nil{}:
      E.Bool.and_l(Ex.all_in(l, roots), Ex.chain.go(td, g, t, l), rs)
    case Con{a, r}:
      E.Bool.and_both(Ex.all_pred(td, g, l, a),
        Ex.ladder(td, g, Con{a, r}, roots),
        E.Bool.and_l(Ex.all_pred(td, g, l, a),
          Ex.chain.go(td, g, t, l), rs), ld)

def Ex.upto_ladder.rest(+td: Nat, +g: G.Graph(), +l: List<&2, U32>,
  +t: R.Levels, +acc: R.Levels, +roots: List<&2, U32>,
  +rs: {Ex.rest(td, g, Con{l, t}, acc, roots) == True{} : Bool})
  -> {Ex.rest(td, g, t, Con{l, acc}, roots) == True{} : Bool}:
  match acc:
    case Nil{}:
      E.Bool.and_r(Ex.all_in(l, roots), Ex.chain.go(td, g, t, l), rs)
    case Con{a, r}:
      E.Bool.and_r(Ex.all_pred(td, g, l, a),
        Ex.chain.go(td, g, t, l), rs)

def Ex.upto_ladder(td, g, ls, target, acc, found, roots, ld, rs):
  match ls:
    case Nil{}:
      match found:
        case True{}:
          ld
        case False{}:
          {==}
    case Con{l, t}:
      match found:
        case True{}:
          ld
        case False{}:
          Ex.upto_ladder(td, g, t, target, Con{l, acc},
            List.contains(~U32, ~U32.is_eq, l, target), roots,
            Ex.upto_ladder.push(td, g, l, t, acc, roots, ld, rs),
            Ex.upto_ladder.rest(td, g, l, t, acc, roots, rs))

def Ex.found_here(+l: List<&2, U32>, +acc: R.Levels, +target: U32,
  +b: Bool,
  +eb: {b == List.contains(~U32, ~U32.is_eq, l, target) : Bool})
  -> {Ex.found_ok(Con{l, acc}, target, b) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      E.Bool.sym(True{}, List.contains(~U32, ~U32.is_eq, l, target), eb)

law Ex.upto_head:
  for +ls: R.Levels
  for +target: U32
  for +acc: R.Levels
  for +found: Bool
  for +fo: {Ex.found_ok(acc, target, found) == True{} : Bool}
  for +sw: {Bool.or(found, Ex.somewhere(ls, target)) == True{} : Bool}
  {Ex.head_has(Xp.Explain.upto(ls, target, acc, found), target)
    == True{} : Bool}

def Ex.upto_head(ls, target, acc, found, fo, sw):
  match ls:
    case Nil{}:
      match found:
        case True{}:
          fo
        case False{}:
          sw
    case Con{l, t}:
      match found:
        case True{}:
          fo
        case False{}:
          Ex.upto_head(t, target, Con{l, acc},
            List.contains(~U32, ~U32.is_eq, l, target),
            Ex.found_here(l, acc, target,
              List.contains(~U32, ~U32.is_eq, l, target), {==}), sw)

# ---------------------------------------------------------------------------
# The witness starts at a requested root.
# ---------------------------------------------------------------------------

law Ex.path_go_root:
  for +td: Nat
  for +g: G.Graph()
  for +rev: R.Levels
  for +target: U32
  for +roots: List<&2, U32>
  for +ld: {Ex.ladder(td, g, rev, roots) == True{} : Bool}
  for hh: {Ex.head_has(rev, target) == True{} : Bool}
  {Xp.Explain.first_in(Xp.Explain.path.go(td, g, rev, target), roots)
    == True{} : Bool}

def Ex.path_go_root(td, g, rev, target, roots, ld, hh):
  match rev:
    case Nil{}:
      E.Bool.noconf({Xp.Explain.first_in(Nil{}, roots) == True{} : Bool},
        hh)
    case Con{lvl, t}:
      Ex.walk_root(td, g, t, target, Nil{}, roots,
        Xp.Explain.pred(td, g, Xp.Explain.head_lvl(t), target, None{}),
        {==}, Ex.ladder_tail(td, g, lvl, t, roots, ld),
        Ex.step_ok_next(td, g, lvl, t, roots, target, ld, hh))

law Ex.path_root:
  for +td: Nat
  for +g: G.Graph()
  for +ls: R.Levels
  for +target: U32
  for +roots: List<&2, U32>
  for +ch: {Ex.chain(td, g, ls, roots) == True{} : Bool}
  for +sw: {Ex.somewhere(ls, target) == True{} : Bool}
  {Xp.Explain.first_in(Xp.Explain.path(td, g, ls, target), roots)
    == True{} : Bool}

def Ex.path_root(td, g, ls, target, roots, ch, sw):
  Ex.path_go_root(td, g,
    Xp.Explain.upto(ls, target, Nil{}, False{}), target, roots,
    Ex.upto_ladder(td, g, ls, target, Nil{}, False{}, roots, {==}, ch),
    Ex.upto_head(ls, target, Nil{}, False{}, {==}, sw))

# ---------------------------------------------------------------------------
# The two orders are the same property.
#
# `Ex.ladder` reads a newest-first level list -- the order the traversal
# accumulates them and the order the walk consumes them. `Ex.chain` reads an
# oldest-first one -- the order `Reach.levels` returns. They say the same
# thing, and this is the reversal that carries one to the other, with the
# accumulator generalised so the induction goes through.
# ---------------------------------------------------------------------------

def Ex.linked(+td: Nat, +g: G.Graph(), +acc: R.Levels, +ls: R.Levels,
  +roots: List<&2, U32>) -> Bool:
  match ls:
    case Nil{}:
      Ex.chain(td, g, acc, roots)
    case Con{l, t}:
      Ex.chain.go(td, g, acc, l)

def Ex.linked_nil(+td: Nat, +g: G.Graph(), +ls: R.Levels,
  +roots: List<&2, U32>)
  -> {Ex.linked(td, g, Nil{}, ls, roots) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, t}:
      {==}

def Ex.rev_chain.join(+td: Nat, +g: G.Graph(), +l: List<&2, U32>,
  +t: R.Levels, +acc: R.Levels, +roots: List<&2, U32>,
  +ld: {Ex.ladder(td, g, Con{l, t}, roots) == True{} : Bool},
  +jn: {Ex.linked(td, g, acc, Con{l, t}, roots) == True{} : Bool})
  -> {Ex.linked(td, g, Con{l, acc}, t, roots) == True{} : Bool}:
  match t:
    case Nil{}:
      E.Bool.and_both(Ex.all_in(l, roots), Ex.chain.go(td, g, acc, l),
        ld, jn)
    case Con{l2, r}:
      E.Bool.and_both(Ex.all_pred(td, g, l, l2),
        Ex.chain.go(td, g, acc, l),
        E.Bool.and_l(Ex.all_pred(td, g, l, l2),
          Ex.ladder(td, g, Con{l2, r}, roots), ld), jn)

law Ex.rev_chain:
  for +td: Nat
  for +g: G.Graph()
  for +ls: R.Levels
  for +acc: R.Levels
  for +roots: List<&2, U32>
  for +ld: {Ex.ladder(td, g, ls, roots) == True{} : Bool}
  for +jn: {Ex.linked(td, g, acc, ls, roots) == True{} : Bool}
  {Ex.chain(td, g,
    List.reverse.go(&2, List<&2, U32>, ls, acc), roots) == True{} : Bool}

def Ex.rev_chain(td, g, ls, acc, roots, ld, jn):
  match ls:
    case Nil{}:
      jn
    case Con{l, t}:
      Ex.rev_chain(td, g, t, Con{l, acc}, roots,
        Ex.ladder_tail(td, g, l, t, roots, ld),
        Ex.rev_chain.join(td, g, l, t, acc, roots, ld, jn))

law Ex.chain_of_ladder:
  for +td: Nat
  for +g: G.Graph()
  for +ls: R.Levels
  for +roots: List<&2, U32>
  for +ld: {Ex.ladder(td, g, ls, roots) == True{} : Bool}
  {Ex.chain(td, g, List.reverse(&2, List<&2, U32>, ls), roots)
    == True{} : Bool}

def Ex.chain_of_ladder(td, g, ls, roots, ld):
  Ex.rev_chain(td, g, ls, Nil{}, roots, ld,
    Ex.linked_nil(td, g, ls, roots))

# ---------------------------------------------------------------------------
# Every member of a list is in that list, and a longer list still holds it.
# ---------------------------------------------------------------------------

law Ex.contains_grow:
  for +h: U32
  for +l: List<&2, U32>
  for +u: U32
  for +mem: {List.contains(~U32, ~U32.is_eq, l, u) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, Con{h, l}, u) == True{} : Bool}

def Ex.contains_grow(h, l, u, mem):
  Bool.or_grow(U32.is_eq(h, u),
    List.contains(~U32, ~U32.is_eq, l, u), mem)

law Ex.all_in_grow:
  for +xs: List<&2, U32>
  for +h: U32
  for +l: List<&2, U32>
  for +ai: {Ex.all_in(xs, l) == True{} : Bool}
  {Ex.all_in(xs, Con{h, l}) == True{} : Bool}

def Ex.all_in_grow(xs, h, l, ai):
  match xs:
    case Nil{}:
      {==}
    case Con{u, t}:
      E.Bool.and_both(List.contains(~U32, ~U32.is_eq, Con{h, l}, u),
        Ex.all_in(t, Con{h, l}),
        Ex.contains_grow(h, l, u,
          E.Bool.and_l(List.contains(~U32, ~U32.is_eq, l, u),
            Ex.all_in(t, l), ai)),
        Ex.all_in_grow(t, h, l,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq, l, u),
            Ex.all_in(t, l), ai)))

law Ex.all_in_self:
  for +l: List<&2, U32>
  {Ex.all_in(l, l) == True{} : Bool}

def Ex.all_in_self(l):
  match l:
    case Nil{}:
      {==}
    case Con{h, t}:
      E.Bool.and_both(List.contains(~U32, ~U32.is_eq, Con{h, t}, h),
        Ex.all_in(t, Con{h, t}),
        Bool.or_left(U32.is_eq(h, h),
          List.contains(~U32, ~U32.is_eq, t, h),
          E.U32.is_eq_refl(h)),
        Ex.all_in_grow(t, h, t, Ex.all_in_self(t)))

# ---------------------------------------------------------------------------
# A vertex with an edge from somewhere in the candidate list has a
# predecessor there.
# ---------------------------------------------------------------------------

law Ex.pred_sticky:
  for +td: Nat
  for +g: G.Graph()
  for +cands: List<&2, U32>
  for +w: U32
  for +x: U32
  {Maybe.is_some(&2, U32,
    Xp.Explain.pred(td, g, cands, w, Some{x})) == True{} : Bool}

def Ex.pred_sticky(td, g, cands, w, x):
  match cands:
    case Nil{}:
      {==}
    case Con{u, t}:
      {==}

def Ex.edge_cast(+td: Nat, +g: G.Graph(), +u: U32, +v: U32, +w: U32,
  +euv: {u == v : U32},
  +ed: {G.Graph.edge(td, g, v, w) == True{} : Bool})
  -> {G.Graph.edge(td, g, u, w) == True{} : Bool}:
  %E.U32.sym(u, v, euv) : {G.Graph.edge(td, g, _, w) == True{} : Bool}
  ed

law Ex.pred_found:
  for +td: Nat
  for +g: G.Graph()
  for +cands: List<&2, U32>
  for +w: U32
  for +v: U32
  for +ed: {G.Graph.edge(td, g, v, w) == True{} : Bool}
  for mem: {List.contains(~U32, ~U32.is_eq, cands, v) == True{} : Bool}
  {Ex.has_pred(td, g, cands, w) == True{} : Bool}

def Ex.pred_found.pick(+td: Nat, +g: G.Graph(), +u: U32,
  +t: List<&2, U32>, +w: U32, +v: U32, +e: Bool,
  +ee: {e == G.Graph.edge(td, g, u, w) : Bool}, +q: Bool,
  +eq: {q == U32.is_eq(u, v) : Bool},
  +ed: {G.Graph.edge(td, g, v, w) == True{} : Bool},
  ih: {List.contains(~U32, ~U32.is_eq, t, v) == True{} : Bool} ->
    {Ex.has_pred(td, g, t, w) == True{} : Bool},
  mem: {Bool.or(U32.is_eq(u, v),
    List.contains(~U32, ~U32.is_eq, t, v)) == True{} : Bool})
  -> {Maybe.is_some(&2, U32,
    Xp.Explain.pred(td, g, t, w, Xp.Explain.opt(u, e)))
    == True{} : Bool}:
  match e:
    case True{}:
      Ex.pred_sticky(td, g, t, w, u)
    case False{}:
      match q:
        case True{}:
          E.Bool.noconf({Ex.has_pred(td, g, t, w) == True{} : Bool},
            Equal.trans(Bool, False{}, G.Graph.edge(td, g, u, w),
              True{}, ee,
              Ex.edge_cast(td, g, u, v, w,
                E.U32.eq_reflect(u, v,
                  E.Bool.sym(True{}, U32.is_eq(u, v), eq)), ed)))
        case False{}:
          ih(Bool.or_on_r(U32.is_eq(u, v),
            List.contains(~U32, ~U32.is_eq, t, v),
            E.Bool.sym(False{}, U32.is_eq(u, v), eq), mem))

def Ex.pred_found(td, g, cands, w, v, ed, mem):
  match cands:
    case Nil{}:
      E.Bool.noconf({Ex.has_pred(td, g, Nil{}, w) == True{} : Bool}, mem)
    case Con{u, t}:
      Ex.pred_found.pick(td, g, u, t, w, v,
        G.Graph.edge(td, g, u, w), {==}, U32.is_eq(u, v), {==}, ed,
        Ex.pred_found(td, g, t, w, v, ed), mem)

law Ex.all_pred_of_edges:
  for +td: Nat
  for +g: G.Graph()
  for +v: U32
  for +ws: List<&2, U32>
  for +head: List<&2, U32>
  for +hv: {List.contains(~U32, ~U32.is_eq, head, v) == True{} : Bool}
  for +aw: {Ex.all_in(ws, G.Graph.succ(td, g, v)) == True{} : Bool}
  {Ex.all_pred(td, g, ws, head) == True{} : Bool}

def Ex.all_pred_of_edges(td, g, v, ws, head, hv, aw):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      E.Bool.and_both(Ex.has_pred(td, g, head, w),
        Ex.all_pred(td, g, t, head),
        Ex.pred_found(td, g, head, w, v,
          E.Bool.and_l(
            List.contains(~U32, ~U32.is_eq, G.Graph.succ(td, g, v), w),
            Ex.all_in(t, G.Graph.succ(td, g, v)), aw), hv),
        Ex.all_pred_of_edges(td, g, v, t, head, hv,
          E.Bool.and_r(
            List.contains(~U32, ~U32.is_eq, G.Graph.succ(td, g, v), w),
            Ex.all_in(t, G.Graph.succ(td, g, v)), aw)))

law Ex.all_pred_succ:
  for +td: Nat
  for +g: G.Graph()
  for +v: U32
  for +head: List<&2, U32>
  for +hv: {List.contains(~U32, ~U32.is_eq, head, v) == True{} : Bool}
  {Ex.all_pred(td, g, G.Graph.succ(td, g, v), head) == True{} : Bool}

def Ex.all_pred_succ(td, g, v, head, hv):
  Ex.all_pred_of_edges(td, g, v, G.Graph.succ(td, g, v), head, hv,
    Ex.all_in_self(G.Graph.succ(td, g, v)))
