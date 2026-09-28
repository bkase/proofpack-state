# proofs/listset.bend -- building a set from a list, at any depth.
#
# `PSet.from_list` is how every set that enters a query from outside the
# algebra is built: the universe, a filter's result, the successors of a
# frontier. That it holds exactly the ordinals on the list is proved in
# proofs/insert.bend and proofs/only.bend, at the production depth of 20.
#
# The closure specification folds successors into a set at whatever depth the
# source has, so this file repeats those two statements with the depth left
# open. The proofs are the same walks; the depth-20 versions instantiate
# lemmas that were always general.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./shape.bend as Sh
import ./preserve.bend as Pr
import ./insert.bend as In
import ./only.bend as On
import ./shift.bend as Sf2
import ./missing.bend as Ms
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/set.bend as S

law PSet.insert_keeps_at:
  for +d: Nat
  for +s: S.PSet
  for +y: U32
  for +x: U32
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +v: {Sh.PSet.wf(d, s, True{}) == True{} : Bool}
  for +ok: {S.PSet.member(d, s, x) == True{} : Bool}
  {S.PSet.member(d, S.PSet.insert(d, s, y), x) == True{} : Bool}

def PSet.insert_keeps_at(d, s, y, x, lt, inv, v, ok):
  In.PSet.add_keeps(d, s, U32.is_lt(y, S.PSet.half(d)),
    U32.is_lt(x, S.PSet.half(d)), S.PSet.half(d), y, x, {==}, lt, inv,
    {==}, v, ok)

law PSet.mem_insert_at:
  for +d: Nat
  for +s: S.PSet
  for +x: U32
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +v: {Sh.PSet.wf(d, s, True{}) == True{} : Bool}
  {S.PSet.member(d, S.PSet.insert(d, s, x), x) == True{} : Bool}

def PSet.mem_insert_at(d, s, x, lt, inv, v):
  In.PSet.wf_mem_add_go(d, s, S.PSet.half(d), x,
    U32.is_lt(x, S.PSet.half(d)), {==}, {==}, lt, v, inv)

law PSet.insert_hit_at:
  for +d: Nat
  for +s: S.PSet
  for +a: U32
  for +x: U32
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +v: {Sh.PSet.wf(d, s, True{}) == True{} : Bool}
  for +eq: {U32.is_eq(a, x) == True{} : Bool}
  {S.PSet.member(d, S.PSet.insert(d, s, a), x) == True{} : Bool}

def PSet.range_cast(+a: U32, +x: U32, +k: Nat,
  +e: {a == x : U32},
  +inv: {Dc.U32.hi_zero(x, k) == True{} : Bool})
  -> {Dc.U32.hi_zero(a, k) == True{} : Bool}:
  %E.U32.sym(a, x, e) : {Dc.U32.hi_zero(_, k) == True{} : Bool}
  inv

def PSet.insert_hit_at(d, s, a, x, lt, inv, v, eq):
  %E.U32.eq_reflect(a, x, eq)
    : {S.PSet.member(d, S.PSet.insert(d, s, a), _) == True{} : Bool}
  PSet.mem_insert_at(d, s, a, lt,
    PSet.range_cast(a, x, 12n+d, E.U32.eq_reflect(a, x, eq), inv), v)

law PSet.of_list_keeps_at:
  for +xs: List<&2, U32>
  for +d: Nat
  for +s: S.PSet
  for +x: U32
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +v: {Sh.PSet.wf(d, s, True{}) == True{} : Bool}
  for +ok: {S.PSet.member(d, s, x) == True{} : Bool}
  {S.PSet.member(d, S.PSet.of_list(d, xs, s), x) == True{} : Bool}

def PSet.of_list_keeps_at(xs, d, s, x, lt, inv, v, ok):
  match xs:
    case Nil{}:
      ok
    case Con{a, t}:
      PSet.of_list_keeps_at(t, d, S.PSet.insert(d, s, a), x, lt, inv,
        Pr.PSet.wf_insert(d, s, a, v),
        PSet.insert_keeps_at(d, s, a, x, lt, inv, v, ok))

law PSet.of_list_contains_at:
  for +xs: List<&2, U32>
  for +d: Nat
  for +hit: Bool
  for +s: S.PSet
  for +x: U32
  for +eh: {hit == In.U32.head_eq(xs, x) : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +v: {Sh.PSet.wf(d, s, True{}) == True{} : Bool}
  for +ok: {List.contains(~U32, ~U32.is_eq, xs, x) == True{} : Bool}
  {S.PSet.member(d, S.PSet.of_list(d, xs, s), x) == True{} : Bool}

def PSet.of_list_contains_at(xs, d, hit, s, x, eh, lt, inv, v, ok):
  match xs:
    case Nil{}:
      E.Bool.noconf({S.PSet.member(d, S.PSet.of_list(d, Nil{}, s), x)
        == True{} : Bool}, ok)
    case Con{a, t}:
      match hit:
        case True{}:
          PSet.of_list_keeps_at(t, d, S.PSet.insert(d, s, a), x, lt,
            inv, Pr.PSet.wf_insert(d, s, a, v),
            PSet.insert_hit_at(d, s, a, x, lt, inv, v,
              E.Bool.sym(True{}, U32.is_eq(a, x), eh)))
        case False{}:
          PSet.of_list_contains_at(t, d, In.U32.head_eq(t, x),
            S.PSet.insert(d, s, a), x, {==}, lt, inv,
            Pr.PSet.wf_insert(d, s, a, v),
            In.PSet.contains_tail(t, a, x, eh, ok))

law PSet.from_list_contains_at:
  for +xs: List<&2, U32>
  for +d: Nat
  for +x: U32
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +ok: {List.contains(~U32, ~U32.is_eq, xs, x) == True{} : Bool}
  {S.PSet.member(d, S.PSet.from_list(d, xs), x) == True{} : Bool}

def PSet.from_list_contains_at(xs, d, x, lt, inv, ok):
  PSet.of_list_contains_at(xs, d, In.U32.head_eq(xs, x), S.PZero{}, x,
    {==}, lt, inv, Sh.PSet.wf_zero(d), ok)

# ---------------------------------------------------------------------------
# And the other direction: nothing but the list's ordinals.
# ---------------------------------------------------------------------------

law PSet.insert_only_at:
  for +d: Nat
  for +s: S.PSet
  for +y: U32
  for +x: U32
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +invy: {Dc.U32.hi_zero(y, 12n+d) == True{} : Bool}
  for +v: {Sh.PSet.wf(d, s, True{}) == True{} : Bool}
  for +ok: {S.PSet.member(d, S.PSet.insert(d, s, y), x) == True{}
    : Bool}
  {Bool.or(U32.is_eq(y, x), S.PSet.member(d, s, x)) == True{} : Bool}

def PSet.insert_only_at(d, s, y, x, lt, inv, invy, v, ok):
  On.PSet.add_only(d, s, U32.is_lt(y, S.PSet.half(d)),
    U32.is_lt(x, S.PSet.half(d)), S.PSet.half(d), y, x, {==}, {==},
    lt, inv, invy, {==}, v, ok)

law PSet.imp_insert_only_at:
  for +d: Nat
  for +q: Bool
  for +s: S.PSet
  for +y: U32
  for +x: U32
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +invy: {Dc.U32.hi_zero(y, 12n+d) == True{} : Bool}
  for +eq: {q == S.PSet.member(d, S.PSet.insert(d, s, y), x) : Bool}
  for +v: {Sh.PSet.wf(d, s, True{}) == True{} : Bool}
  {Ms.Bool.imp(q, Bool.or(U32.is_eq(y, x),
    S.PSet.member(d, s, x))) == True{} : Bool}

def PSet.imp_insert_only_at(d, q, s, y, x, lt, inv, invy, eq, v):
  match q:
    case False{}:
      {==}
    case True{}:
      PSet.insert_only_at(d, s, y, x, lt, inv, invy, v,
        E.Bool.sym(True{},
          S.PSet.member(d, S.PSet.insert(d, s, y), x), eq))

law PSet.of_list_only_at:
  for +xs: List<&2, U32>
  for +d: Nat
  for +s: S.PSet
  for +x: U32
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +invs: {Sf2.Ords.all_fit(xs, 12n+d) == True{} : Bool}
  for +v: {Sh.PSet.wf(d, s, True{}) == True{} : Bool}
  for +ok: {S.PSet.member(d, S.PSet.of_list(d, xs, s), x) == True{}
    : Bool}
  {Bool.or(List.contains(~U32, ~U32.is_eq, xs, x),
    S.PSet.member(d, s, x)) == True{} : Bool}

def PSet.of_list_only_at(xs, d, s, x, lt, inv, invs, v, ok):
  match xs:
    case Nil{}:
      ok
    case Con{a, t}:
      On.Bool.or3(List.contains(~U32, ~U32.is_eq, t, x),
        U32.is_eq(a, x), S.PSet.member(d, s, x),
        On.Bool.or_lift_r(List.contains(~U32, ~U32.is_eq, t, x),
          S.PSet.member(d, S.PSet.insert(d, s, a), x),
          Bool.or(U32.is_eq(a, x), S.PSet.member(d, s, x)),
          PSet.of_list_only_at(t, d, S.PSet.insert(d, s, a), x, lt,
            inv,
            E.Bool.and_r(Dc.U32.hi_zero(a, 12n+d),
              Sf2.Ords.all_fit(t, 12n+d), invs),
            Pr.PSet.wf_insert(d, s, a, v), ok),
          PSet.imp_insert_only_at(d,
            S.PSet.member(d, S.PSet.insert(d, s, a), x), s, a, x, lt,
            inv,
            E.Bool.and_l(Dc.U32.hi_zero(a, 12n+d),
              Sf2.Ords.all_fit(t, 12n+d), invs), {==}, v)))

law PSet.from_list_only_at:
  for +xs: List<&2, U32>
  for +d: Nat
  for +x: U32
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +invs: {Sf2.Ords.all_fit(xs, 12n+d) == True{} : Bool}
  for +ok: {S.PSet.member(d, S.PSet.from_list(d, xs), x) == True{}
    : Bool}
  {List.contains(~U32, ~U32.is_eq, xs, x) == True{} : Bool}

law PSet.mem_zero:
  for +d: Nat
  for +h: U32
  for +x: U32
  {S.PSet.mem(d, S.PZero{}, h, x) == False{} : Bool}

def PSet.mem_zero(d, h, x):
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

def PSet.drop_zero(+c: Bool, +d: Nat, +x: U32,
  +ok: {Bool.or(c, S.PSet.member(d, S.PZero{}, x)) == True{} : Bool})
  -> {Bool.or(c, False{}) == True{} : Bool}:
  %PSet.mem_zero(d, S.PSet.half(d), x)
    : {Bool.or(c, _) == True{} : Bool}
  ok

def PSet.from_list_only_at(xs, d, x, lt, inv, invs, ok):
  On.Bool.or_false_true(List.contains(~U32, ~U32.is_eq, xs, x),
    PSet.drop_zero(List.contains(~U32, ~U32.is_eq, xs, x), d, x,
      PSet.of_list_only_at(xs, d, S.PZero{}, x, lt, inv, invs,
        Sh.PSet.wf_zero(d), ok)))
