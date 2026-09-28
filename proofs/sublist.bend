# proofs/sublist.bend -- an ascending list inside another is no longer.
#
# The closure's fixed point is a pigeonhole, and a pigeonhole needs a count
# that strictly grows. What makes the count grow is this: if every ordinal of
# `a` is on `b`, and both ascend, then `a` is no longer than `b` -- and if `b`
# also holds an ordinal `a` does not, then `a` is strictly shorter.
#
# Ascending is what supplies distinctness. Without it the statement is false
# -- a list may repeat -- and with it the proof is one walk down both lists,
# comparing heads, which is the same shape as the merge the set difference
# already uses.

import Base
import ./eq.bend as E
import ./orderlist.bend as Ol
import ./subsetconv.bend as Sc
import ./subsetalg.bend as Sa
import ./count.bend as Ct
import ../core/count.bend as C
import ../core/word.bend as W

# ---------------------------------------------------------------------------
# Dropping a head that nothing in the list can equal.
# ---------------------------------------------------------------------------

law Ords.lt_of_lt_all:
  for +t: List<&2, U32>
  for +h: U32
  for +y: U32
  for +la: {Ol.Ords.lt_all(h, t) == True{} : Bool}
  for c: {List.contains(~U32, ~U32.is_eq, t, y) == True{} : Bool}
  {U32.is_lt(h, y) == True{} : Bool}

def Ords.lt_of_lt_all.pick(+u: List<&2, U32>, +h: U32, +y: U32,
  +z: U32, +e: Bool, +ee: {e == U32.is_eq(z, y) : Bool},
  +lz: {U32.is_lt(h, z) == True{} : Bool},
  ih: {List.contains(~U32, ~U32.is_eq, u, y) == True{} : Bool} ->
    {U32.is_lt(h, y) == True{} : Bool},
  +c: {List.contains(~U32, ~U32.is_eq, Con{z, u}, y) == True{}
    : Bool})
  -> {U32.is_lt(h, y) == True{} : Bool}:
  match e:
    case True{}:
      %E.U32.eq_reflect(z, y, E.Bool.sym(True{}, U32.is_eq(z, y), ee))
        : {U32.is_lt(h, _) == True{} : Bool}
      lz
    case False{}:
      ih(Sc.Ords.contains_tail(z, u, y, ee, c))

def Ords.lt_of_lt_all(t, h, y, la, c):
  match t:
    case Nil{}:
      E.Bool.noconf({U32.is_lt(h, y) == True{} : Bool}, c)
    case Con{z, u}:
      Ords.lt_of_lt_all.pick(u, h, y, z, U32.is_eq(z, y), {==},
        E.Bool.and_l(U32.is_lt(h, z), Ol.Ords.lt_all(h, u), la),
        Ords.lt_of_lt_all(u, h, y,
          E.Bool.and_r(U32.is_lt(h, z), Ol.Ords.lt_all(h, u), la)),
        c)

law Ords.all_in_tail:
  for +a: List<&2, U32>
  for +h: U32
  for +t: List<&2, U32>
  for +la: {Ol.Ords.lt_all(h, a) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(a, Con{h, t}) == True{} : Bool}
  {Sa.Ords.all_in(a, t) == True{} : Bool}

def Ords.all_in_tail(a, h, t, la, ai):
  match a:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(List.contains(~U32, ~U32.is_eq, t, y),
        Sa.Ords.all_in(u, t),
        Sc.Ords.contains_tail(h, t, y,
          E.Bool.sym(U32.is_eq(h, y), False{},
            Ol.U32.ne_of_gt(h, y,
              E.Bool.and_l(U32.is_lt(h, y), Ol.Ords.lt_all(h, u),
                la))),
          E.Bool.and_l(List.contains(~U32, ~U32.is_eq, Con{h, t}, y),
            Sa.Ords.all_in(u, Con{h, t}), ai)),
        Ords.all_in_tail(u, h, t,
          E.Bool.and_r(U32.is_lt(h, y), Ol.Ords.lt_all(h, u), la),
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq, Con{h, t}, y),
            Sa.Ords.all_in(u, Con{h, t}), ai)))

# ---------------------------------------------------------------------------
# No longer.
# ---------------------------------------------------------------------------

def Bool.or_off_l(+p: Bool, +q: Bool,
  +z: {Bool.or(p, q) == False{} : Bool}) -> {p == False{} : Bool}:
  match p:
    case False{}:
      {==}
    case True{}:
      E.Bool.noconf.r({True{} == False{} : Bool}, z)

def Bool.or_off_r(+p: Bool, +q: Bool,
  +z: {Bool.or(p, q) == False{} : Bool}) -> {q == False{} : Bool}:
  match p:
    case False{}:
      z
    case True{}:
      E.Bool.noconf.r({q == False{} : Bool}, z)

def Ords.length_le.pick(+t: List<&2, U32>, +ta: List<&2, U32>,
  +h: U32, +ha: U32, +e: Bool,
  +ee: {e == U32.is_eq(h, ha) : Bool},
  +aa: {Ol.Ords.asc(Con{ha, ta}) == True{} : Bool},
  +ab: {Ol.Ords.asc(Con{h, t}) == True{} : Bool},
  +ai: {Sa.Ords.all_in(Con{ha, ta}, Con{h, t}) == True{} : Bool},
  ih1: {Sa.Ords.all_in(ta, t) == True{} : Bool} ->
    {C.Nat.upto(List.length(&2, U32, ta), List.length(&2, U32, t))
      == True{} : Bool},
  ih2: {Sa.Ords.all_in(Con{ha, ta}, t) == True{} : Bool} ->
    {C.Nat.upto(List.length(&2, U32, Con{ha, ta}),
      List.length(&2, U32, t)) == True{} : Bool})
  -> {C.Nat.upto(List.length(&2, U32, Con{ha, ta}),
    List.length(&2, U32, Con{h, t})) == True{} : Bool}:
  match e:
    case True{}:
      ih1(Ords.all_in_tail(ta, h, t,
        %E.U32.sym(h, ha, E.U32.eq_reflect(h, ha,
          E.Bool.sym(True{}, U32.is_eq(h, ha), ee)))
          : {Ol.Ords.lt_all(_, ta) == True{} : Bool}
        Ol.Ords.lt_all_of_asc(ta, ha, aa),
        E.Bool.and_r(List.contains(~U32, ~U32.is_eq, Con{h, t}, ha),
          Sa.Ords.all_in(ta, Con{h, t}), ai)))
    case False{}:
      Ct.Nat.upto_succ_r(List.length(&2, U32, Con{ha, ta}),
        List.length(&2, U32, t),
        ih2(Ords.all_in_tail(Con{ha, ta}, h, t,
          E.Bool.and_both(U32.is_lt(h, ha), Ol.Ords.lt_all(h, ta),
            Ords.lt_of_lt_all(t, h, ha,
              Ol.Ords.lt_all_of_asc(t, h, ab),
              Sc.Ords.contains_tail(h, t, ha, ee,
                E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                  Con{h, t}, ha), Sa.Ords.all_in(ta, Con{h, t}),
                  ai))),
            Ol.Ords.lt_all_trans(ta, h, ha,
              Ords.lt_of_lt_all(t, h, ha,
                Ol.Ords.lt_all_of_asc(t, h, ab),
                Sc.Ords.contains_tail(h, t, ha, ee,
                  E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                    Con{h, t}, ha), Sa.Ords.all_in(ta, Con{h, t}),
                    ai))),
              Ol.Ords.lt_all_of_asc(ta, ha, aa))),
          ai)))

law Ords.length_le:
  for +b: List<&2, U32>
  for +a: List<&2, U32>
  for +aa: {Ol.Ords.asc(a) == True{} : Bool}
  for +ab: {Ol.Ords.asc(b) == True{} : Bool}
  for ai: {Sa.Ords.all_in(a, b) == True{} : Bool}
  {C.Nat.upto(List.length(&2, U32, a), List.length(&2, U32, b))
    == True{} : Bool}

def Ords.length_le(b, a, aa, ab, ai):
  match b:
    case Nil{}:
      match a:
        case Nil{}:
          {==}
        case Con{y, u}:
          E.Bool.noconf({C.Nat.upto(List.length(&2, U32, Con{y, u}),
            0n) == True{} : Bool},
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq, Nil{}, y),
              Sa.Ords.all_in(u, Nil{}), ai))
    case Con{h, t}:
      match a:
        case Nil{}:
          {==}
        case Con{ha, ta}:
          Ords.length_le.pick(t, ta, h, ha, U32.is_eq(h, ha), {==},
            aa, ab, ai,
            Ords.length_le(t, ta,
              E.Bool.and_r(Ol.Ords.above(ha, ta), Ol.Ords.asc(ta),
                aa),
              E.Bool.and_r(Ol.Ords.above(h, t), Ol.Ords.asc(t), ab)),
            Ords.length_le(t, Con{ha, ta}, aa,
              E.Bool.and_r(Ol.Ords.above(h, t), Ol.Ords.asc(t), ab)))

# ---------------------------------------------------------------------------
# Strictly shorter, when the longer list holds something the shorter does not.
# ---------------------------------------------------------------------------

def Ords.length_lt.pick(+t: List<&2, U32>, +ta: List<&2, U32>,
  +h: U32, +ha: U32, +z: U32, +e: Bool,
  +ee: {e == U32.is_eq(h, ha) : Bool},
  +aa: {Ol.Ords.asc(Con{ha, ta}) == True{} : Bool},
  +ab: {Ol.Ords.asc(Con{h, t}) == True{} : Bool},
  +ai: {Sa.Ords.all_in(Con{ha, ta}, Con{h, t}) == True{} : Bool},
  +cb: {List.contains(~U32, ~U32.is_eq, Con{h, t}, z) == True{}
    : Bool},
  +ca: {List.contains(~U32, ~U32.is_eq, Con{ha, ta}, z) == False{}
    : Bool},
  ih: {Sa.Ords.all_in(ta, t) == True{} : Bool} ->
    {List.contains(~U32, ~U32.is_eq, t, z) == True{} : Bool} ->
    {List.contains(~U32, ~U32.is_eq, ta, z) == False{} : Bool} ->
    {C.Nat.upto(1n+List.length(&2, U32, ta),
      List.length(&2, U32, t)) == True{} : Bool})
  -> {C.Nat.upto(1n+List.length(&2, U32, Con{ha, ta}),
    List.length(&2, U32, Con{h, t})) == True{} : Bool}:
  match e:
    case True{}:
      ih(Ords.all_in_tail(ta, h, t,
          %E.U32.sym(h, ha, E.U32.eq_reflect(h, ha,
            E.Bool.sym(True{}, U32.is_eq(h, ha), ee)))
            : {Ol.Ords.lt_all(_, ta) == True{} : Bool}
          Ol.Ords.lt_all_of_asc(ta, ha, aa),
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq, Con{h, t}, ha),
            Sa.Ords.all_in(ta, Con{h, t}), ai)),
        Sc.Ords.contains_tail(h, t, z,
          E.Bool.sym(U32.is_eq(h, z), False{},
            %E.U32.sym(h, ha, E.U32.eq_reflect(h, ha,
              E.Bool.sym(True{}, U32.is_eq(h, ha), ee)))
              : {U32.is_eq(_, z) == False{} : Bool}
            Bool.or_off_l(U32.is_eq(ha, z),
              List.contains(~U32, ~U32.is_eq, ta, z), ca)), cb),
        Bool.or_off_r(U32.is_eq(ha, z),
          List.contains(~U32, ~U32.is_eq, ta, z), ca))
    case False{}:
      Ords.length_le(t, Con{ha, ta}, aa,
        E.Bool.and_r(Ol.Ords.above(h, t), Ol.Ords.asc(t), ab),
        Ords.all_in_tail(Con{ha, ta}, h, t,
          E.Bool.and_both(U32.is_lt(h, ha), Ol.Ords.lt_all(h, ta),
            Ords.lt_of_lt_all(t, h, ha,
              Ol.Ords.lt_all_of_asc(t, h, ab),
              Sc.Ords.contains_tail(h, t, ha, ee,
                E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                  Con{h, t}, ha), Sa.Ords.all_in(ta, Con{h, t}),
                  ai))),
            Ol.Ords.lt_all_trans(ta, h, ha,
              Ords.lt_of_lt_all(t, h, ha,
                Ol.Ords.lt_all_of_asc(t, h, ab),
                Sc.Ords.contains_tail(h, t, ha, ee,
                  E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                    Con{h, t}, ha), Sa.Ords.all_in(ta, Con{h, t}),
                    ai))),
              Ol.Ords.lt_all_of_asc(ta, ha, aa))),
          ai))

law Ords.length_lt:
  for +b: List<&2, U32>
  for +a: List<&2, U32>
  for +z: U32
  for +aa: {Ol.Ords.asc(a) == True{} : Bool}
  for +ab: {Ol.Ords.asc(b) == True{} : Bool}
  for ai: {Sa.Ords.all_in(a, b) == True{} : Bool}
  for cb: {List.contains(~U32, ~U32.is_eq, b, z) == True{} : Bool}
  for ca: {List.contains(~U32, ~U32.is_eq, a, z) == False{} : Bool}
  {C.Nat.upto(1n+List.length(&2, U32, a), List.length(&2, U32, b))
    == True{} : Bool}

def Ords.length_lt(b, a, z, aa, ab, ai, cb, ca):
  match b:
    case Nil{}:
      E.Bool.noconf({C.Nat.upto(1n+List.length(&2, U32, a),
        0n) == True{} : Bool}, cb)
    case Con{h, t}:
      match a:
        case Nil{}:
          {==}
        case Con{ha, ta}:
          Ords.length_lt.pick(t, ta, h, ha, z, U32.is_eq(h, ha),
            {==}, aa, ab, ai, cb, ca,
            Ords.length_lt(t, ta, z,
              E.Bool.and_r(Ol.Ords.above(ha, ta), Ol.Ords.asc(ta),
                aa),
              E.Bool.and_r(Ol.Ords.above(h, t), Ol.Ords.asc(t), ab)))
