# proofs/ascext.bend -- an ascending list is a function of its members.
#
# Two strictly ascending lists that hold the same ordinals are the same list.
# That is what makes an enumeration usable as an equality: `PSet.to_list` and
# `PSet.missing` both ascend, so a fold over either depends only on the set,
# not on the tree that produced it.
#
# "Hold the same ordinals" is mutual containment, which is decidable data, so
# the induction may use it on both sides without running into the affine
# discipline. The heads must agree because each is in the other's list, and if
# they differed each would have to be strictly below the other.

import Base
import ./eq.bend as E
import ./orderlist.bend as Ol
import ./sublist.bend as Sl
import ./subsetalg.bend as Sa
import ../core/count.bend as C

def Bool.or_on_r(+p: Bool, +q: Bool,
  +ep: {p == False{} : Bool},
  +on: {Bool.or(p, q) == True{} : Bool}) -> {q == True{} : Bool}:
  %ep : {Bool.or(_, q) == True{} : Bool}
  on

def Nat.gt_asym(-A: Type, +a: Nat, +b: Nat,
  +g1: {C.Nat.gt(a, b) == True{} : Bool},
  +g2: {C.Nat.gt(b, a) == True{} : Bool}) -> A:
  match a:
    case 0n:
      E.Bool.noconf(A, g1)
    case 1n+p:
      match b:
        case 0n:
          E.Bool.noconf(A, g2)
        case 1n+q:
          Nat.gt_asym(A, p, q, g1, g2)

def U32.lt_asym(-A: Type, +x: U32, +y: U32,
  +l1: {U32.is_lt(x, y) == True{} : Bool},
  +l2: {U32.is_lt(y, x) == True{} : Bool}) -> A:
  Nat.gt_asym(A, U32.to_nat(y), U32.to_nat(x),
    Ol.Ords.lt_value(x, y, l1), Ol.Ords.lt_value(y, x, l2))

def Ords.lt_all_cast(+a: U32, +b: U32, +l: List<&2, U32>,
  +e: {a == b : U32},
  +la: {Ol.Ords.lt_all(a, l) == True{} : Bool})
  -> {Ol.Ords.lt_all(b, l) == True{} : Bool}:
  %e : {Ol.Ords.lt_all(_, l) == True{} : Bool}
  la

def Ords.cons(+h: U32, t: List<&2, U32>) -> List<&2, U32>:
  Con{h, t}

# Everything on `l` is in `Con{hy, ty}`, and `hy` is strictly below everything
# on `l`, so nothing on `l` was the head.
law Ords.all_in_drop_head:
  for +l: List<&2, U32>
  for +hy: U32
  for +ty: List<&2, U32>
  for +la: {Ol.Ords.lt_all(hy, l) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l, Con{hy, ty}) == True{} : Bool}
  {Sa.Ords.all_in(l, ty) == True{} : Bool}

def Ords.all_in_drop_head(l, hy, ty, la, ai):
  match l:
    case Nil{}:
      {==}
    case Con{z, u}:
      E.Bool.and_both(List.contains(~U32, ~U32.is_eq, ty, z),
        Sa.Ords.all_in(u, ty),
        Bool.or_on_r(U32.is_eq(hy, z),
          List.contains(~U32, ~U32.is_eq, ty, z),
          Ol.U32.ne_of_gt(hy, z,
            E.Bool.and_l(U32.is_lt(hy, z),
              Ol.Ords.lt_all(hy, u), la)),
          E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
            Con{hy, ty}, z), Sa.Ords.all_in(u, Con{hy, ty}), ai)),
        Ords.all_in_drop_head(u, hy, ty,
          E.Bool.and_r(U32.is_lt(hy, z), Ol.Ords.lt_all(hy, u), la),
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            Con{hy, ty}, z), Sa.Ords.all_in(u, Con{hy, ty}), ai)))

def Ords.same_lists(+x: List<&2, U32>, +y: List<&2, U32>) -> Bool:
  Bool.and(Sa.Ords.all_in(x, y), Sa.Ords.all_in(y, x))

def Ords.asc_ext.head(+hx: U32, +tx: List<&2, U32>, +hy: U32,
  +ty: List<&2, U32>,
  +ax: {Ol.Ords.asc(Con{hx, tx}) == True{} : Bool},
  +ay: {Ol.Ords.asc(Con{hy, ty}) == True{} : Bool},
  +e1: Bool, +ee1: {e1 == U32.is_eq(hy, hx) : Bool},
  +e2: Bool, +ee2: {e2 == U32.is_eq(hx, hy) : Bool},
  +mxy: {Bool.or(U32.is_eq(hy, hx),
    List.contains(~U32, ~U32.is_eq, ty, hx)) == True{} : Bool},
  +myx: {Bool.or(U32.is_eq(hx, hy),
    List.contains(~U32, ~U32.is_eq, tx, hy)) == True{} : Bool})
  -> {hx == hy : U32}:
  match e1:
    case True{}:
      E.U32.sym(hy, hx,
        E.U32.eq_reflect(hy, hx,
          E.Bool.sym(True{}, U32.is_eq(hy, hx), ee1)))
    case False{}:
      match e2:
        case True{}:
          E.U32.eq_reflect(hx, hy,
            E.Bool.sym(True{}, U32.is_eq(hx, hy), ee2))
        case False{}:
          U32.lt_asym({hx == hy : U32}, hy, hx,
            Sl.Ords.lt_of_lt_all(ty, hy, hx,
              Ol.Ords.lt_all_of_asc(ty, hy, ay),
              Bool.or_on_r(U32.is_eq(hy, hx),
                List.contains(~U32, ~U32.is_eq, ty, hx),
                E.Bool.sym(False{}, U32.is_eq(hy, hx), ee1), mxy)),
            Sl.Ords.lt_of_lt_all(tx, hx, hy,
              Ol.Ords.lt_all_of_asc(tx, hx, ax),
              Bool.or_on_r(U32.is_eq(hx, hy),
                List.contains(~U32, ~U32.is_eq, tx, hy),
                E.Bool.sym(False{}, U32.is_eq(hx, hy), ee2), myx)))

law Ords.asc_ext:
  for +x: List<&2, U32>
  for +y: List<&2, U32>
  for +ax: {Ol.Ords.asc(x) == True{} : Bool}
  for +ay: {Ol.Ords.asc(y) == True{} : Bool}
  for +sm: {Ords.same_lists(x, y) == True{} : Bool}
  {x == y : List<&2, U32>}

def Ords.asc_ext.step(+hx: U32, +tx: List<&2, U32>, +hy: U32,
  +ty: List<&2, U32>, +heq: {hx == hy : U32},
  +teq: {tx == ty : List<&2, U32>})
  -> {Con{hx, tx} == Con{hy, ty} : List<&2, U32>}:
  %E.U32.sym(hx, hy, heq) : {Con{_, tx} == Con{hy, ty}
    : List<&2, U32>}
  Equal.cong(List<&2, U32>, List<&2, U32>, Ords.cons(hy), tx, ty,
    teq)

def Ords.asc_ext(x, y, ax, ay, sm):
  match x:
    case Nil{}:
      match y:
        case Nil{}:
          {==}
        case Con{hy, ty}:
          E.Bool.noconf({Nil{} == Con{hy, ty} : List<&2, U32>},
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq, Nil{}, hy),
              Sa.Ords.all_in(ty, Nil{}),
              E.Bool.and_r(Sa.Ords.all_in(Nil{}, Con{hy, ty}),
                Sa.Ords.all_in(Con{hy, ty}, Nil{}), sm)))
    case Con{hx, tx}:
      match y:
        case Nil{}:
          E.Bool.noconf({Con{hx, tx} == Nil{} : List<&2, U32>},
            E.Bool.and_l(List.contains(~U32, ~U32.is_eq, Nil{}, hx),
              Sa.Ords.all_in(tx, Nil{}),
              E.Bool.and_l(Sa.Ords.all_in(Con{hx, tx}, Nil{}),
                Sa.Ords.all_in(Nil{}, Con{hx, tx}), sm)))
        case Con{hy, ty}:
          Ords.asc_ext.step(hx, tx, hy, ty,
            Ords.asc_ext.head(hx, tx, hy, ty, ax, ay,
              U32.is_eq(hy, hx), {==}, U32.is_eq(hx, hy), {==},
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                Con{hy, ty}, hx), Sa.Ords.all_in(tx, Con{hy, ty}),
                E.Bool.and_l(Sa.Ords.all_in(Con{hx, tx},
                  Con{hy, ty}),
                  Sa.Ords.all_in(Con{hy, ty}, Con{hx, tx}), sm)),
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                Con{hx, tx}, hy), Sa.Ords.all_in(ty, Con{hx, tx}),
                E.Bool.and_r(Sa.Ords.all_in(Con{hx, tx},
                  Con{hy, ty}),
                  Sa.Ords.all_in(Con{hy, ty}, Con{hx, tx}), sm))),
            Ords.asc_ext(tx, ty,
              E.Bool.and_r(Ol.Ords.above(hx, tx), Ol.Ords.asc(tx),
                ax),
              E.Bool.and_r(Ol.Ords.above(hy, ty), Ol.Ords.asc(ty),
                ay),
              E.Bool.and_both(Sa.Ords.all_in(tx, ty),
                Sa.Ords.all_in(ty, tx),
                Ords.all_in_drop_head(tx, hy, ty,
                  Ords.lt_all_cast(hx, hy, tx,
                    Ords.asc_ext.head(hx, tx, hy, ty, ax, ay,
                      U32.is_eq(hy, hx), {==}, U32.is_eq(hx, hy),
                      {==},
                      E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                        Con{hy, ty}, hx),
                        Sa.Ords.all_in(tx, Con{hy, ty}),
                        E.Bool.and_l(Sa.Ords.all_in(Con{hx, tx},
                          Con{hy, ty}),
                          Sa.Ords.all_in(Con{hy, ty}, Con{hx, tx}),
                          sm)),
                      E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                        Con{hx, tx}, hy),
                        Sa.Ords.all_in(ty, Con{hx, tx}),
                        E.Bool.and_r(Sa.Ords.all_in(Con{hx, tx},
                          Con{hy, ty}),
                          Sa.Ords.all_in(Con{hy, ty}, Con{hx, tx}),
                          sm))),
                    Ol.Ords.lt_all_of_asc(tx, hx, ax)),
                  E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
                    Con{hy, ty}, hx), Sa.Ords.all_in(tx,
                    Con{hy, ty}),
                    E.Bool.and_l(Sa.Ords.all_in(Con{hx, tx},
                      Con{hy, ty}),
                      Sa.Ords.all_in(Con{hy, ty}, Con{hx, tx}),
                      sm))),
                Ords.all_in_drop_head(ty, hx, tx,
                  Ords.lt_all_cast(hy, hx, ty,
                    E.U32.sym(hx, hy,
                      Ords.asc_ext.head(hx, tx, hy, ty, ax, ay,
                        U32.is_eq(hy, hx), {==}, U32.is_eq(hx, hy),
                        {==},
                        E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                          Con{hy, ty}, hx),
                          Sa.Ords.all_in(tx, Con{hy, ty}),
                          E.Bool.and_l(Sa.Ords.all_in(Con{hx, tx},
                            Con{hy, ty}),
                            Sa.Ords.all_in(Con{hy, ty},
                              Con{hx, tx}), sm)),
                        E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                          Con{hx, tx}, hy),
                          Sa.Ords.all_in(ty, Con{hx, tx}),
                          E.Bool.and_r(Sa.Ords.all_in(Con{hx, tx},
                            Con{hy, ty}),
                            Sa.Ords.all_in(Con{hy, ty},
                              Con{hx, tx}), sm)))),
                    Ol.Ords.lt_all_of_asc(ty, hy, ay)),
                  E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
                    Con{hx, tx}, hy), Sa.Ords.all_in(ty,
                    Con{hx, tx}),
                    E.Bool.and_r(Sa.Ords.all_in(Con{hx, tx},
                      Con{hy, ty}),
                      Sa.Ords.all_in(Con{hy, ty}, Con{hx, tx}),
                      sm))))))
