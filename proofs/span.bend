# proofs/span.bend -- what counting down from an ordinal covers.
#
# `PSet.range(k, ord, tail)` is how a full interval is enumerated: `k` steps
# down from `ord`, each one prepended. This file says which ordinals that
# covers, in two steps.
#
# The first is a mirror: `Ords.in_down` is the same walk asking a question
# instead of building a list, and `contains` of the built list is `in_down`
# or `contains` of the tail. That step needs no arithmetic at all.
#
# The second is the arithmetic, and it is the only place the enumeration
# needs any: the walk covers exactly the ordinals from `ord - k + 1` up to
# `ord`, which is one application of the decrement lemma per step.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./decr.bend as De
import ./order.bend as Or
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/set.bend as S

def Ords.in_down(+k: Nat, ord: U32, +x: U32) -> Bool:
  match k:
    case 0n:
      False{}
    case 1n+j:
      +o = ord
      Bool.or(U32.is_eq(o, x), Ords.in_down(j, U32.sub(o, 1), x))

law Bool.or_rotate:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(b, a), c) : Bool}

def Bool.or_rotate(a, b, c):
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

law Ords.contains_range:
  for +k: Nat
  for +ord: U32
  for +tail: List<&2, U32>
  for +x: U32
  {List.contains(~U32, ~U32.is_eq, S.PSet.range(k, ord, tail), x)
    == Bool.or(Ords.in_down(k, ord, x),
         List.contains(~U32, ~U32.is_eq, tail, x)) : Bool}

def Ords.contains_range(k, ord, tail, x):
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(Bool,
        List.contains(~U32, ~U32.is_eq,
          S.PSet.range(j, U32.sub(ord, 1), Con{ord, tail}), x),
        Bool.or(Ords.in_down(j, U32.sub(ord, 1), x),
          Bool.or(U32.is_eq(ord, x),
            List.contains(~U32, ~U32.is_eq, tail, x))),
        Bool.or(Bool.or(U32.is_eq(ord, x),
          Ords.in_down(j, U32.sub(ord, 1), x)),
          List.contains(~U32, ~U32.is_eq, tail, x)),
        Ords.contains_range(j, U32.sub(ord, 1), Con{ord, tail}, x),
        Bool.or_rotate(Ords.in_down(j, U32.sub(ord, 1), x),
          U32.is_eq(ord, x),
          List.contains(~U32, ~U32.is_eq, tail, x)))

# ---------------------------------------------------------------------------
# Small order facts, proved where they are used rather than assumed.
# ---------------------------------------------------------------------------

law Nat.upto_gt_absurd:
  for +a: Nat
  for +b: Nat
  for +le: {C.Nat.upto(a, b) == True{} : Bool}
  for +g: {C.Nat.gt(a, b) == True{} : Bool}
  {False{} == True{} : Bool}

def Nat.upto_gt_absurd(a, b, le, g):
  match a:
    case 0n:
      g
    case 1n+p:
      match b:
        case 0n:
          le
        case 1n+q:
          Nat.upto_gt_absurd(p, q, le, g)

law Nat.pos_of_ne:
  for +o: Nat
  for +x: Nat
  for +le: {C.Nat.upto(x, o) == True{} : Bool}
  for +ne: {Nat.is_eq(o, x) == False{} : Bool}
  {C.Nat.gt(o, 0n) == True{} : Bool}

def Nat.pos_of_ne(o, x, le, ne):
  match o:
    case 1n+q:
      {==}
    case 0n:
      match x:
        case 0n:
          E.Bool.noconf.r({C.Nat.gt(0n, 0n) == True{} : Bool}, ne)
        case 1n+p:
          le

law Nat.le_pred:
  for +q: Nat
  for +x: Nat
  for +le: {C.Nat.upto(x, 1n+q) == True{} : Bool}
  for +ne: {Nat.is_eq(1n+q, x) == False{} : Bool}
  {C.Nat.upto(x, q) == True{} : Bool}

def Nat.le_pred(q, x, le, ne):
  match q:
    case 0n:
      match x:
        case 0n:
          {==}
        case 1n+i:
          match i:
            case 0n:
              E.Bool.noconf.r({C.Nat.upto(1n+0n, 0n) == True{} : Bool}, ne)
            case 1n+r:
              le
    case 1n+j:
      match x:
        case 0n:
          {==}
        case 1n+i:
          Nat.le_pred(j, i, le, ne)

law Nat.le_ne_pred:
  for +o: Nat
  for +x: Nat
  for +le: {C.Nat.upto(x, o) == True{} : Bool}
  for +ne: {Nat.is_eq(o, x) == False{} : Bool}
  {C.Nat.upto(x, Nat.sub(o, 1n)) == True{} : Bool}

def Nat.le_ne_pred(o, x, le, ne):
  match o:
    case 0n:
      match x:
        case 0n:
          {==}
        case 1n+p:
          le
    case 1n+q:
      %E.Nat.sym(Nat.sub(q, 0n), q, De.Nat.sub_zero(q))
        : {C.Nat.upto(x, _) == True{} : Bool}
      Nat.le_pred(q, x, le, ne)

# ---------------------------------------------------------------------------
# The walk covers the span.
# ---------------------------------------------------------------------------

law Nat.gt_pred:
  for +o: Nat
  for +a: Nat
  for +pos: {C.Nat.gt(o, 0n) == True{} : Bool}
  for +g: {C.Nat.gt(1n+a, o) == True{} : Bool}
  {C.Nat.gt(a, Nat.sub(o, 1n)) == True{} : Bool}

def Nat.gt_pred(o, a, pos, g):
  match o:
    case 0n:
      E.Bool.noconf({C.Nat.gt(a, Nat.sub(0n, 1n)) == True{} : Bool}, pos)
    case 1n+q:
      %E.Nat.sym(Nat.sub(q, 0n), q, De.Nat.sub_zero(q))
        : {C.Nat.gt(a, _) == True{} : Bool}
      g

law U32.ne_of_is_eq_false:
  for +o: U32
  for +x: U32
  for +ne: {U32.is_eq(o, x) == False{} : Bool}
  {Nat.is_eq(U32.to_nat(o), U32.to_nat(x)) == False{} : Bool}

def U32.ne_of_is_eq_false(o, x, ne):
  %Or.U32.cmp_spec(o, x) : {Cmp.is_eq(_) == False{} : Bool}
  ne

law U32.to_nat_dec:
  for +ord: U32
  for +x: U32
  for +le: {C.Nat.upto(U32.to_nat(x), U32.to_nat(ord)) == True{} : Bool}
  for +ne: {U32.is_eq(ord, x) == False{} : Bool}
  {U32.to_nat(U32.sub(ord, 1)) == Nat.sub(U32.to_nat(ord), 1n) : Nat}

def U32.to_nat_dec(ord, x, le, ne):
  De.U32.dec_spec(ord,
    Nat.pos_of_ne(U32.to_nat(ord), U32.to_nat(x), le,
      U32.ne_of_is_eq_false(ord, x, ne)))

law Ords.in_down_of_span:
  for +k: Nat
  for +eq: Bool
  for +ord: U32
  for +x: U32
  for +eeq: {eq == U32.is_eq(ord, x) : Bool}
  for +le: {C.Nat.upto(U32.to_nat(x), U32.to_nat(ord)) == True{} : Bool}
  for +g: {C.Nat.gt(Nat.add(U32.to_nat(x), k), U32.to_nat(ord))
    == True{} : Bool}
  {Ords.in_down(k, ord, x) == True{} : Bool}

law Span.gt_add_zero:
  for +a: Nat
  for +o: Nat
  for +g: {C.Nat.gt(Nat.add(a, 0n), o) == True{} : Bool}
  {C.Nat.gt(a, o) == True{} : Bool}

def Span.gt_add_zero(a, o, g):
  %N.Nat.add_zero(a) : {C.Nat.gt(_, o) == True{} : Bool}
  g

law Span.gt_succ:
  for +a: Nat
  for +j: Nat
  for +o: Nat
  for +g: {C.Nat.gt(Nat.add(a, 1n+j), o) == True{} : Bool}
  {C.Nat.gt(1n+Nat.add(a, j), o) == True{} : Bool}

def Span.gt_succ(a, j, o, g):
  %N.Nat.add_succ(a, j) : {C.Nat.gt(_, o) == True{} : Bool}
  g

law Span.or_right:
  for +p: Bool
  for +q: Bool
  for +ok: {q == True{} : Bool}
  {Bool.or(p, q) == True{} : Bool}

def Span.or_right(p, q, ok):
  match p:
    case True{}:
      {==}
    case False{}:
      ok

law Span.le_move:
  for +a: Nat
  for +u: Nat
  for +v: Nat
  for +e: {u == v : Nat}
  for +ok: {C.Nat.upto(a, v) == True{} : Bool}
  {C.Nat.upto(a, u) == True{} : Bool}

def Span.le_move(a, u, v, e, ok):
  %E.Nat.sym(u, v, e) : {C.Nat.upto(a, _) == True{} : Bool}
  ok

law Span.gt_move:
  for +a: Nat
  for +u: Nat
  for +v: Nat
  for +e: {u == v : Nat}
  for +ok: {C.Nat.gt(a, v) == True{} : Bool}
  {C.Nat.gt(a, u) == True{} : Bool}

def Span.gt_move(a, u, v, e, ok):
  %E.Nat.sym(u, v, e) : {C.Nat.gt(a, _) == True{} : Bool}
  ok

def Ords.in_down_of_span(k, eq, ord, x, eeq, le, g):
  match k:
    case 0n:
      E.Bool.noconf({Ords.in_down(0n, ord, x) == True{} : Bool},
        Nat.upto_gt_absurd(U32.to_nat(x), U32.to_nat(ord), le,
          Span.gt_add_zero(U32.to_nat(x), U32.to_nat(ord), g)))
    case 1n+j:
      match eq:
        case True{}:
          %E.Bool.sym(U32.is_eq(ord, x), True{},
            E.Bool.sym(eq, U32.is_eq(ord, x), eeq))
            : {Bool.or(_, Ords.in_down(j, U32.sub(ord, 1), x))
              == True{} : Bool}
          {==}
        case False{}:
          Span.or_right(U32.is_eq(ord, x),
            Ords.in_down(j, U32.sub(ord, 1), x),
            Ords.in_down_of_span(j,
              U32.is_eq(U32.sub(ord, 1), x), U32.sub(ord, 1), x, {==},
              Span.le_move(U32.to_nat(x), U32.to_nat(U32.sub(ord, 1)),
                Nat.sub(U32.to_nat(ord), 1n),
                U32.to_nat_dec(ord, x, le,
                  E.Bool.sym(False{}, U32.is_eq(ord, x), eeq)),
                Nat.le_ne_pred(U32.to_nat(ord), U32.to_nat(x), le,
                  U32.ne_of_is_eq_false(ord, x,
                    E.Bool.sym(False{}, U32.is_eq(ord, x), eeq)))),
              Span.gt_move(Nat.add(U32.to_nat(x), j),
                U32.to_nat(U32.sub(ord, 1)),
                Nat.sub(U32.to_nat(ord), 1n),
                U32.to_nat_dec(ord, x, le,
                  E.Bool.sym(False{}, U32.is_eq(ord, x), eeq)),
                Nat.gt_pred(U32.to_nat(ord), Nat.add(U32.to_nat(x), j),
                  Nat.pos_of_ne(U32.to_nat(ord), U32.to_nat(x), le,
                    U32.ne_of_is_eq_false(ord, x,
                      E.Bool.sym(False{}, U32.is_eq(ord, x), eeq))),
                  Span.gt_succ(U32.to_nat(x), j, U32.to_nat(ord), g)))))

# ---------------------------------------------------------------------------
# And covers nothing else -- as long as the count does not run past zero and
# wrap, which is why the hypothesis is there. `PSet.range` is only ever
# called with a count that stops at the bottom of the interval it is
# enumerating.
# ---------------------------------------------------------------------------

law Nat.upto_self:
  for +m: Nat
  {C.Nat.upto(m, m) == True{} : Bool}

def Nat.upto_self(m):
  match m:
    case 0n:
      {==}
    case 1n+p:
      Nat.upto_self(p)

law Nat.gt_succ_add:
  for +m: Nat
  for +j: Nat
  {C.Nat.gt(1n+Nat.add(m, j), m) == True{} : Bool}

def Nat.gt_succ_add(m, j):
  match m:
    case 0n:
      {==}
    case 1n+p:
      Nat.gt_succ_add(p, j)

law Nat.pos_of_upto_succ:
  for +o: Nat
  for +i: Nat
  for +le: {C.Nat.upto(1n+i, o) == True{} : Bool}
  {C.Nat.gt(o, 0n) == True{} : Bool}

def Nat.pos_of_upto_succ(o, i, le):
  match o:
    case 0n:
      E.Bool.noconf({C.Nat.gt(0n, 0n) == True{} : Bool}, le)
    case 1n+q:
      {==}

law Ords.span_of_in_down:
  for +k: Nat
  for +eq: Bool
  for +ord: U32
  for +x: U32
  for +eeq: {eq == U32.is_eq(ord, x) : Bool}
  for +nowrap: {C.Nat.upto(k, 1n+U32.to_nat(ord)) == True{} : Bool}
  for +ok: {Ords.in_down(k, ord, x) == True{} : Bool}
  {Bool.and(C.Nat.upto(U32.to_nat(x), U32.to_nat(ord)),
    C.Nat.gt(Nat.add(U32.to_nat(x), k), U32.to_nat(ord)))
    == True{} : Bool}

law Span.span_here:
  for +ord: U32
  for +x: U32
  for +j: Nat
  for +e: {ord == x : U32}
  {Bool.and(C.Nat.upto(U32.to_nat(x), U32.to_nat(ord)),
    C.Nat.gt(Nat.add(U32.to_nat(x), 1n+j), U32.to_nat(ord)))
    == True{} : Bool}

law Span.in_down_zero:
  for +ord: U32
  for +x: U32
  for +ok: {Ords.in_down(0n, ord, x) == True{} : Bool}
  {False{} == True{} : Bool}

law Span.or_false_left:
  for +p: Bool
  for +q: Bool
  for +ep: {False{} == p : Bool}
  for +ok: {Bool.or(p, q) == True{} : Bool}
  {q == True{} : Bool}

law Span.upto_peel:
  for +a: Nat
  for +b: Nat
  for +ok: {C.Nat.upto(1n+a, 1n+b) == True{} : Bool}
  {C.Nat.upto(a, b) == True{} : Bool}

law Span.succ_cong:
  for +u: Nat
  for +v: Nat
  for +e: {u == v : Nat}
  {1n+u == 1n+v : Nat}

law Span.move_le:
  for +a: Nat
  for +u: Nat
  for +v: Nat
  for +e: {u == v : Nat}
  for +ok: {C.Nat.upto(a, v) == True{} : Bool}
  {C.Nat.upto(a, u) == True{} : Bool}

law Span.nowrap_pred:
  for +o: Nat
  for +i: Nat
  for +ok: {C.Nat.upto(2n+i, 1n+o) == True{} : Bool}
  {C.Nat.upto(1n+i, 1n+Nat.sub(o, 1n)) == True{} : Bool}

law Span.move_span:
  for +a: Nat
  for +u: Nat
  for +v: Nat
  for +k: Nat
  for +e: {u == v : Nat}
  for +ok: {Bool.and(C.Nat.upto(a, u), C.Nat.gt(Nat.add(a, k), u))
    == True{} : Bool}
  {Bool.and(C.Nat.upto(a, v), C.Nat.gt(Nat.add(a, k), v)) == True{} : Bool}

law Span.lift:
  for +a: Nat
  for +o: Nat
  for +i: Nat
  for +pos: {C.Nat.gt(o, 0n) == True{} : Bool}
  for +ok: {Bool.and(C.Nat.upto(a, Nat.sub(o, 1n)),
    C.Nat.gt(Nat.add(a, 1n+i), Nat.sub(o, 1n))) == True{} : Bool}
  {Bool.and(C.Nat.upto(a, o), C.Nat.gt(Nat.add(a, 2n+i), o))
    == True{} : Bool}

law Span.lift.step:
  for +a: Nat
  for +q: Nat
  for +i: Nat
  for +ok: {Bool.and(C.Nat.upto(a, q), C.Nat.gt(Nat.add(a, 1n+i), q))
    == True{} : Bool}
  {Bool.and(C.Nat.upto(a, 1n+q), C.Nat.gt(Nat.add(a, 2n+i), 1n+q))
    == True{} : Bool}

law Span.lift.arm:
  for +a: Nat
  for +q: Nat
  for +i: Nat
  for +le: {C.Nat.upto(a, q) == True{} : Bool}
  for +g: {C.Nat.gt(1n+Nat.add(a, i), q) == True{} : Bool}
  {Bool.and(C.Nat.upto(a, 1n+q), C.Nat.gt(1n+Nat.add(a, i), q))
    == True{} : Bool}

law Span.upto_up:
  for +a: Nat
  for +q: Nat
  for +le: {C.Nat.upto(a, q) == True{} : Bool}
  {C.Nat.upto(a, 1n+q) == True{} : Bool}

def Span.span_here(ord, x, j, e):
  %E.U32.sym(ord, x, e) : {Bool.and(C.Nat.upto(U32.to_nat(x), U32.to_nat(_)),
      C.Nat.gt(Nat.add(U32.to_nat(x), 1n+j), U32.to_nat(_)))
    == True{} : Bool}
  %E.Bool.sym(C.Nat.upto(U32.to_nat(x), U32.to_nat(x)), True{},
    Nat.upto_self(U32.to_nat(x)))
    : {Bool.and(_, C.Nat.gt(Nat.add(U32.to_nat(x), 1n+j),
        U32.to_nat(x))) == True{} : Bool}
  %E.Nat.sym(Nat.add(U32.to_nat(x), 1n+j), 1n+Nat.add(U32.to_nat(x), j),
    N.Nat.add_succ(U32.to_nat(x), j))
    : {Bool.and(True{}, C.Nat.gt(_, U32.to_nat(x))) == True{} : Bool}
  Nat.gt_succ_add(U32.to_nat(x), j)

def Span.in_down_zero(ord, x, ok):
  ok

def Span.or_false_left(p, q, ep, ok):
  %E.Bool.sym(False{}, p, ep) : {Bool.or(_, q) == True{} : Bool}
  ok

def Span.upto_peel(a, b, ok):
  ok

def Span.succ_cong(u, v, e):
  %E.Nat.sym(u, v, e) : {1n+_ == 1n+v : Nat}
  {==}

def Span.move_le(a, u, v, e, ok):
  %E.Nat.sym(u, v, e) : {C.Nat.upto(a, _) == True{} : Bool}
  ok

def Span.nowrap_pred(o, i, ok):
  match o:
    case 0n:
      E.Bool.noconf({C.Nat.upto(1n+i, 1n+Nat.sub(0n, 1n))
        == True{} : Bool}, ok)
    case 1n+q:
      %E.Nat.sym(Nat.sub(q, 0n), q, De.Nat.sub_zero(q))
        : {C.Nat.upto(1n+i, 1n+_) == True{} : Bool}
      ok

def Span.move_span(a, u, v, k, e, ok):
  %e
    : {Bool.and(C.Nat.upto(a, _), C.Nat.gt(Nat.add(a, k), _))
      == True{} : Bool}
  ok

def Span.upto_up(a, q, le):
  match a:
    case 0n:
      {==}
    case 1n+p:
      match q:
        case 0n:
          E.Bool.noconf({C.Nat.upto(p, 0n) == True{} : Bool}, le)
        case 1n+r:
          Span.upto_up(p, r, le)

def Span.lift.arm(a, q, i, le, g):
  %E.Bool.sym(C.Nat.upto(a, 1n+q), True{},
    Span.upto_up(a, q, le))
    : {Bool.and(_, C.Nat.gt(1n+Nat.add(a, i), q)) == True{} : Bool}
  g

def Span.lift.step(a, q, i, ok):
  %E.Nat.sym(Nat.add(a, 2n+i), 1n+Nat.add(a, 1n+i),
    N.Nat.add_succ(a, 1n+i))
    : {Bool.and(C.Nat.upto(a, 1n+q), C.Nat.gt(_, 1n+q)) == True{} : Bool}
  %E.Nat.sym(Nat.add(a, 1n+i), 1n+Nat.add(a, i), N.Nat.add_succ(a, i))
    : {Bool.and(C.Nat.upto(a, 1n+q), C.Nat.gt(1n+_, 1n+q))
      == True{} : Bool}
  Span.lift.arm(a, q, i,
    E.Bool.and_l(C.Nat.upto(a, q), C.Nat.gt(Nat.add(a, 1n+i), q), ok),
    Span.gt_succ(a, i, q,
      E.Bool.and_r(C.Nat.upto(a, q), C.Nat.gt(Nat.add(a, 1n+i), q), ok)))

def Span.lift(a, o, i, pos, ok):
  match o:
    case 0n:
      E.Bool.noconf({Bool.and(C.Nat.upto(a, 0n),
        C.Nat.gt(Nat.add(a, 2n+i), 0n)) == True{} : Bool}, pos)
    case 1n+q:
      Span.lift.step(a, q, i,
        Span.move_span(a, Nat.sub(q, 0n), q, 1n+i,
          De.Nat.sub_zero(q), ok))

def Ords.span_of_in_down(k, eq, ord, x, eeq, nowrap, ok):
  match k:
    case 0n:
      E.Bool.noconf({Bool.and(
        C.Nat.upto(U32.to_nat(x), U32.to_nat(ord)),
        C.Nat.gt(Nat.add(U32.to_nat(x), 0n), U32.to_nat(ord)))
        == True{} : Bool}, ok)
    case 1n+j:
      match j:
        case 0n:
          match eq:
            case True{}:
              Span.span_here(ord, x, 0n,
                E.U32.eq_reflect(ord, x,
                  E.Bool.sym(True{}, U32.is_eq(ord, x), eeq)))
            case False{}:
              E.Bool.noconf({Bool.and(
                C.Nat.upto(U32.to_nat(x), U32.to_nat(ord)),
                C.Nat.gt(Nat.add(U32.to_nat(x), 1n+0n), U32.to_nat(ord)))
                == True{} : Bool},
                Span.in_down_zero(U32.sub(ord, 1), x,
                  Span.or_false_left(U32.is_eq(ord, x),
                    Ords.in_down(0n, U32.sub(ord, 1), x), eeq, ok)))
        case 1n+i:
          match eq:
            case True{}:
              Span.span_here(ord, x, 1n+i,
                E.U32.eq_reflect(ord, x,
                  E.Bool.sym(True{}, U32.is_eq(ord, x), eeq)))
            case False{}:
              Span.lift(U32.to_nat(x), U32.to_nat(ord), i,
                Nat.pos_of_upto_succ(U32.to_nat(ord), i,
                  Span.upto_peel(1n+i, U32.to_nat(ord), nowrap)),
                Span.move_span(U32.to_nat(x),
                  U32.to_nat(U32.sub(ord, 1)),
                  Nat.sub(U32.to_nat(ord), 1n), 1n+i,
                  De.U32.dec_spec(ord,
                    Nat.pos_of_upto_succ(U32.to_nat(ord), i,
                      Span.upto_peel(1n+i, U32.to_nat(ord), nowrap))),
                  Ords.span_of_in_down(1n+i,
                    U32.is_eq(U32.sub(ord, 1), x), U32.sub(ord, 1), x,
                    {==},
                    Span.move_le(1n+i,
                      1n+U32.to_nat(U32.sub(ord, 1)),
                      1n+Nat.sub(U32.to_nat(ord), 1n),
                      Span.succ_cong(U32.to_nat(U32.sub(ord, 1)),
                        Nat.sub(U32.to_nat(ord), 1n),
                        De.U32.dec_spec(ord,
                          Nat.pos_of_upto_succ(U32.to_nat(ord), i,
                            Span.upto_peel(1n+i, U32.to_nat(ord),
                              nowrap)))),
                      Span.nowrap_pred(U32.to_nat(ord), i, nowrap)),
                    Span.or_false_left(U32.is_eq(ord, x),
                      Ords.in_down(1n+i, U32.sub(ord, 1), x), eeq, ok))))
