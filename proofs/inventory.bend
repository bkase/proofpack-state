# proofs/inventory.bend -- G-03, the inventory projection.
#
# A receiver reports the object ids it holds. `Inv.project` turns that report
# into a set of source ordinals by looking each id up in the source
# universe's identity table: an id the source never named has no ordinal,
# which is what out-of-scope means, and an id it did name contributes its
# ordinal.
#
# The obligation is that the projection contains exactly the recorded ids the
# source universe names, without assuming the receiver's store is graph-closed
# -- that is the whole point of the least-missing theorem, which holds for an
# arbitrary inventory. This file proves the direction that decides whether an
# answer can be trusted: every id on the report that the universe names has
# its ordinal in the projection. Under-reporting an inventory is what makes
# `pp` claim an object is missing when the receiver has it, and this is what
# rules that out.
#
# Two things do it. Interning is reflexive on equal ids -- `Oid.eq` decides
# equality of the complete digest, so an id that matches the one asked about
# *is* that id, and no hash-collision assumption appears anywhere (SPEC 8.4).
# And insertion never loses a member (proofs/insert.bend), so an ordinal put
# in by one step survives every later step.

import Base
import ./eq.bend as E
import ./shape.bend as Sh
import ./preserve.bend as Pr
import ./insert.bend as Ins
import ./only.bend as Only
import ../core/set.bend as S
import ../core/trie.bend as T
import ../adapters/git/oid.bend as O
import ../adapters/git/intern.bend as I
import ../adapters/git/inventory.bend as Iv

# ---------------------------------------------------------------------------
# Deciding equality of two object ids decides equality of the digests.
# ---------------------------------------------------------------------------

law Oid.eq_reflect:
  for +a: O.Oid
  for +b: O.Oid
  for +ok: {O.Oid.eq(a, b) == True{} : Bool}
  {a == b : O.Oid}

def Oid.eq_reflect(a, b, ok):
  match a:
    case O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}:
      match b:
        case O.Oid{b0, b1, b2, b3, b4, b5, b6, b7}:
          %E.U32.eq_reflect(a0, b0,
            E.Bool.and_l(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok))
            : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
              == O.Oid{_, b1, b2, b3, b4, b5, b6, b7} : O.Oid}
          %E.U32.eq_reflect(a1, b1,
            E.Bool.and_l(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))))),
              E.Bool.and_r(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok)))
            : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
              == O.Oid{a0, _, b2, b3, b4, b5, b6, b7} : O.Oid}
          %E.U32.eq_reflect(a2, b2,
            E.Bool.and_l(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))),
              E.Bool.and_r(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))))),
                E.Bool.and_r(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok))))
            : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
              == O.Oid{a0, a1, _, b3, b4, b5, b6, b7} : O.Oid}
          %E.U32.eq_reflect(a3, b3,
            E.Bool.and_l(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))),
              E.Bool.and_r(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))),
                E.Bool.and_r(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))))),
                  E.Bool.and_r(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok)))))
            : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
              == O.Oid{a0, a1, a2, _, b4, b5, b6, b7} : O.Oid}
          %E.U32.eq_reflect(a4, b4,
            E.Bool.and_l(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))),
              E.Bool.and_r(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))),
                E.Bool.and_r(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))),
                  E.Bool.and_r(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))))),
                    E.Bool.and_r(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok))))))
            : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
              == O.Oid{a0, a1, a2, a3, _, b5, b6, b7} : O.Oid}
          %E.U32.eq_reflect(a5, b5,
            E.Bool.and_l(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)),
              E.Bool.and_r(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))),
                E.Bool.and_r(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))),
                  E.Bool.and_r(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))),
                    E.Bool.and_r(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))))),
                      E.Bool.and_r(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok)))))))
            : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
              == O.Oid{a0, a1, a2, a3, a4, _, b6, b7} : O.Oid}
          %E.U32.eq_reflect(a6, b6,
            E.Bool.and_l(U32.is_eq(a6, b6), U32.is_eq(a7, b7),
              E.Bool.and_r(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)),
                E.Bool.and_r(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))),
                  E.Bool.and_r(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))),
                    E.Bool.and_r(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))),
                      E.Bool.and_r(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))))),
                        E.Bool.and_r(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok))))))))
            : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
              == O.Oid{a0, a1, a2, a3, a4, a5, _, b7} : O.Oid}
          %E.U32.eq_reflect(a7, b7,
            E.Bool.and_r(U32.is_eq(a6, b6), U32.is_eq(a7, b7),
              E.Bool.and_r(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)),
                E.Bool.and_r(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))),
                  E.Bool.and_r(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))),
                    E.Bool.and_r(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))),
                      E.Bool.and_r(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))))),
                        E.Bool.and_r(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok))))))))
            : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
              == O.Oid{a0, a1, a2, a3, a4, a5, a6, _} : O.Oid}
          {==}

# ---------------------------------------------------------------------------
# One step of the fold. The lookup is carried as a parameter with an equation
# naming it, because what the step does to the set depends on it.
# ---------------------------------------------------------------------------

law Inv.step_wf:
  for +acc: Iv.Inventory
  for +m: Maybe<&2, U32>
  for +tbl: T.Trie<I.Bucket()>
  for +o: O.Oid
  for +em: {m == I.Uni.find(tbl, o) : Maybe<&2, U32>}
  for +v: {Sh.PSet.wf(20n, Iv.Inventory.present(acc), True{})
    == True{} : Bool}
  {Sh.PSet.wf(20n, Iv.Inventory.present(Iv.Inv.step(tbl, acc, o)), True{})
    == True{} : Bool}

def Inv.step_wf(acc, m, tbl, o, em, v):
  match acc:
    case Iv.Inv{present, in_scope, out_of_scope, total}:
      match m:
        case None{}:
          %em : {Sh.PSet.wf(20n, Iv.Inventory.present(
              Iv.Inv.add.hit(present, in_scope, out_of_scope, _)), True{})
            == True{} : Bool}
          v
        case Some{k}:
          %em : {Sh.PSet.wf(20n, Iv.Inventory.present(
              Iv.Inv.add.hit(present, in_scope, out_of_scope, _)), True{})
            == True{} : Bool}
          Pr.PSet.wf_insert(20n, present, k, v)

law Inv.step_keeps:
  for +acc: Iv.Inventory
  for +m: Maybe<&2, U32>
  for +tbl: T.Trie<I.Bucket()>
  for +o: O.Oid
  for +x: U32
  for +em: {m == I.Uni.find(tbl, o) : Maybe<&2, U32>}
  for +v: {Sh.PSet.wf(20n, Iv.Inventory.present(acc), True{})
    == True{} : Bool}
  for +ok: {S.PSet.member(20n, Iv.Inventory.present(acc), x)
    == True{} : Bool}
  {S.PSet.member(20n,
    Iv.Inventory.present(Iv.Inv.step(tbl, acc, o)), x) == True{} : Bool}

def Inv.step_keeps(acc, m, tbl, o, x, em, v, ok):
  match acc:
    case Iv.Inv{present, in_scope, out_of_scope, total}:
      match m:
        case None{}:
          %em : {S.PSet.member(20n, Iv.Inventory.present(
              Iv.Inv.add.hit(present, in_scope, out_of_scope, _)), x)
            == True{} : Bool}
          ok
        case Some{k}:
          %em : {S.PSet.member(20n, Iv.Inventory.present(
              Iv.Inv.add.hit(present, in_scope, out_of_scope, _)), x)
            == True{} : Bool}
          Ins.PSet.insert_keeps(present, k, x, v, ok)

law Inv.fold_keeps:
  for +oids: List<&2, O.Oid>
  for +tbl: T.Trie<I.Bucket()>
  for +acc: Iv.Inventory
  for +x: U32
  for +v: {Sh.PSet.wf(20n, Iv.Inventory.present(acc), True{})
    == True{} : Bool}
  for +ok: {S.PSet.member(20n, Iv.Inventory.present(acc), x)
    == True{} : Bool}
  {S.PSet.member(20n,
    Iv.Inventory.present(Iv.Inv.fold(tbl, oids, acc)), x) == True{} : Bool}

def Inv.fold_keeps(oids, tbl, acc, x, v, ok):
  match oids:
    case Nil{}:
      ok
    case Con{o, t}:
      Inv.fold_keeps(t, tbl, Iv.Inv.step(tbl, acc, o), x,
        Inv.step_wf(acc, I.Uni.find(tbl, o), tbl, o, {==}, v),
        Inv.step_keeps(acc, I.Uni.find(tbl, o), tbl, o, x, {==}, v, ok))

# ---------------------------------------------------------------------------
# And the step that finds the id asked about.
# ---------------------------------------------------------------------------

def Oid.head_eq(oids: List<&2, O.Oid>, +o: O.Oid) -> Bool:
  match oids:
    case Nil{}:
      False{}
    case Con{a, t}:
      O.Oid.eq(a, o)

law Inv.contains_tail:
  for +t: List<&2, O.Oid>
  for +a: O.Oid
  for +o: O.Oid
  for +eh: {False{} == O.Oid.eq(a, o) : Bool}
  for +ok: {List.contains(~O.Oid, ~O.Oid.eq, Con{a, t}, o)
    == True{} : Bool}
  {List.contains(~O.Oid, ~O.Oid.eq, t, o) == True{} : Bool}

def Inv.contains_tail(t, a, o, eh, ok):
  %E.Bool.sym(False{}, O.Oid.eq(a, o), eh)
    : {Bool.or(_, List.contains(~O.Oid, ~O.Oid.eq, t, o))
      == True{} : Bool}
  ok

law Inv.step_finds:
  for +acc: Iv.Inventory
  for +tbl: T.Trie<I.Bucket()>
  for +a: O.Oid
  for +o: O.Oid
  for +x: U32
  for +eq: {O.Oid.eq(a, o) == True{} : Bool}
  for +f: {I.Uni.find(tbl, o) == Some{x} : Maybe<&2, U32>}
  for +v: {Sh.PSet.wf(20n, Iv.Inventory.present(acc), True{})
    == True{} : Bool}
  {S.PSet.member(20n,
    Iv.Inventory.present(Iv.Inv.step(tbl, acc, a)), x) == True{} : Bool}

def Inv.step_finds(acc, tbl, a, o, x, eq, f, v):
  match acc:
    case Iv.Inv{present, in_scope, out_of_scope, total}:
      %Equal.sym(O.Oid, a, o, Oid.eq_reflect(a, o, eq))
        : {S.PSet.member(20n, Iv.Inventory.present(
            Iv.Inv.add.hit(present, in_scope, out_of_scope,
              I.Uni.find(tbl, _))), x) == True{} : Bool}
      %E.Maybe.sym(U32, I.Uni.find(tbl, o), Some{x}, f)
        : {S.PSet.member(20n, Iv.Inventory.present(
            Iv.Inv.add.hit(present, in_scope, out_of_scope, _)), x)
          == True{} : Bool}
      Ins.PSet.wf_mem_insert(present, x, v)

law Inv.fold_finds:
  for +oids: List<&2, O.Oid>
  for +hit: Bool
  for +tbl: T.Trie<I.Bucket()>
  for +acc: Iv.Inventory
  for +o: O.Oid
  for +x: U32
  for +eh: {hit == Oid.head_eq(oids, o) : Bool}
  for +f: {I.Uni.find(tbl, o) == Some{x} : Maybe<&2, U32>}
  for +v: {Sh.PSet.wf(20n, Iv.Inventory.present(acc), True{})
    == True{} : Bool}
  for +ok: {List.contains(~O.Oid, ~O.Oid.eq, oids, o) == True{} : Bool}
  {S.PSet.member(20n,
    Iv.Inventory.present(Iv.Inv.fold(tbl, oids, acc)), x) == True{} : Bool}

def Inv.fold_finds(oids, hit, tbl, acc, o, x, eh, f, v, ok):
  match oids:
    case Nil{}:
      E.Bool.noconf({S.PSet.member(20n,
        Iv.Inventory.present(Iv.Inv.fold(tbl, Nil{}, acc)), x)
        == True{} : Bool}, ok)
    case Con{a, t}:
      match hit:
        case True{}:
          Inv.fold_keeps(t, tbl, Iv.Inv.step(tbl, acc, a), x,
            Inv.step_wf(acc, I.Uni.find(tbl, a), tbl, a, {==}, v),
            Inv.step_finds(acc, tbl, a, o, x,
              E.Bool.sym(True{}, O.Oid.eq(a, o), eh), f, v))
        case False{}:
          Inv.fold_finds(t, Oid.head_eq(t, o), tbl,
            Iv.Inv.step(tbl, acc, a), o, x, {==}, f,
            Inv.step_wf(acc, I.Uni.find(tbl, a), tbl, a, {==}, v),
            Inv.contains_tail(t, a, o, eh, ok))

law Inv.present_finish:
  for +v: Iv.Inventory
  {Iv.Inventory.present(Iv.Inv.finish(v))
    == Iv.Inventory.present(v) : S.PSet}

def Inv.present_finish(v):
  match v:
    case Iv.Inv{present, in_scope, out_of_scope, total}:
      {==}

law Inv.project_finds:
  for +u: I.Universe
  for +oids: List<&2, O.Oid>
  for +o: O.Oid
  for +x: U32
  for +f: {I.Uni.find(I.Uni.table(u), o) == Some{x} : Maybe<&2, U32>}
  for +ok: {List.contains(~O.Oid, ~O.Oid.eq, oids, o) == True{} : Bool}
  {S.PSet.member(20n,
    Iv.Inventory.present(Iv.Inv.project(u, oids)), x) == True{} : Bool}

def Inv.project_finds(u, oids, o, x, f, ok):
  %Equal.sym(S.PSet,
    Iv.Inventory.present(Iv.Inv.finish(Iv.Inv.fold(I.Uni.table(u), oids,
      Iv.Inv{S.PSet.empty(), 0n, 0n, 0n}))),
    Iv.Inventory.present(Iv.Inv.fold(I.Uni.table(u), oids,
      Iv.Inv{S.PSet.empty(), 0n, 0n, 0n})),
    Inv.present_finish(Iv.Inv.fold(I.Uni.table(u), oids,
      Iv.Inv{S.PSet.empty(), 0n, 0n, 0n})))
    : {S.PSet.member(20n, _, x) == True{} : Bool}
  Inv.fold_finds(oids, Oid.head_eq(oids, o), I.Uni.table(u),
    Iv.Inv{S.PSet.empty(), 0n, 0n, 0n}, o, x, {==}, f,
    Sh.PSet.wf_zero(20n), ok)

# ---------------------------------------------------------------------------
# And nothing else. The fold is the set built from the ordinals the table
# named, so "the projection has nothing the report did not mention" is that
# list, plus the fact that a set built from a list has only what is on it
# (proofs/only.bend).
#
# `Inv.ords` is proof-only: the product folds directly into the set and never
# materialises this list. It is the specification of what the fold put in.
# ---------------------------------------------------------------------------

def Inv.ords.pick(m: Maybe<&2, U32>, rest: List<&2, U32>) ->
  List<&2, U32>:
  match m:
    case None{}:
      rest
    case Some{k}:
      Con{k, rest}

def Inv.ords(+tbl: T.Trie<I.Bucket()>, oids: List<&2, O.Oid>) ->
  List<&2, U32>:
  match oids:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      Inv.ords.pick(I.Uni.find(tbl, o), Inv.ords(tbl, t))

def Inv.head_find(+tbl: T.Trie<I.Bucket()>, oids: List<&2, O.Oid>) ->
  Maybe<&2, U32>:
  match oids:
    case Nil{}:
      None{}
    case Con{o, t}:
      I.Uni.find(tbl, o)

law Inv.fold_of_list:
  for +oids: List<&2, O.Oid>
  for +m: Maybe<&2, U32>
  for +tbl: T.Trie<I.Bucket()>
  for +acc: Iv.Inventory
  for +em: {m == Inv.head_find(tbl, oids) : Maybe<&2, U32>}
  {Iv.Inventory.present(Iv.Inv.fold(tbl, oids, acc))
    == S.PSet.of_list(20n, Inv.ords(tbl, oids),
         Iv.Inventory.present(acc)) : S.PSet}

def Inv.fold_of_list(oids, m, tbl, acc, em):
  match oids:
    case Nil{}:
      {==}
    case Con{o, t}:
      match m:
        case None{}:
          match acc:
            case Iv.Inv{present, in_scope, out_of_scope, total}:
              %em : {Iv.Inventory.present(Iv.Inv.fold(tbl, t,
                  Iv.Inv.add.hit(present, in_scope, out_of_scope, _)))
                == S.PSet.of_list(20n,
                     Inv.ords.pick(_, Inv.ords(tbl, t)), present) : S.PSet}
              Inv.fold_of_list(t, Inv.head_find(tbl, t), tbl,
                Iv.Inv{present, in_scope, 1n+out_of_scope, 0n}, {==})
        case Some{k}:
          match acc:
            case Iv.Inv{present, in_scope, out_of_scope, total}:
              %em : {Iv.Inventory.present(Iv.Inv.fold(tbl, t,
                  Iv.Inv.add.hit(present, in_scope, out_of_scope, _)))
                == S.PSet.of_list(20n,
                     Inv.ords.pick(_, Inv.ords(tbl, t)), present) : S.PSet}
              Inv.fold_of_list(t, Inv.head_find(tbl, t), tbl,
                Iv.Inv{S.PSet.insert(20n, present, k), 1n+in_scope,
                  out_of_scope, 0n}, {==})

law Inv.project_only:
  for +u: I.Universe
  for +oids: List<&2, O.Oid>
  for +x: U32
  for +ok: {S.PSet.member(20n,
    Iv.Inventory.present(Iv.Inv.project(u, oids)), x) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, Inv.ords(I.Uni.table(u), oids), x)
    == True{} : Bool}

def Inv.member_at(+x: U32, s: S.PSet) -> Bool:
  S.PSet.member(20n, s, x)

def Inv.project_only(u, oids, x, ok):
  Only.PSet.from_list_only(Inv.ords(I.Uni.table(u), oids), x,
    Equal.trans(Bool,
      S.PSet.member(20n,
        S.PSet.from_list(20n, Inv.ords(I.Uni.table(u), oids)), x),
      S.PSet.member(20n,
        Iv.Inventory.present(Iv.Inv.project(u, oids)), x), True{},
      Equal.cong(S.PSet, Bool, Inv.member_at(x),
        S.PSet.from_list(20n, Inv.ords(I.Uni.table(u), oids)),
        Iv.Inventory.present(Iv.Inv.project(u, oids)),
        Equal.trans(S.PSet,
          S.PSet.from_list(20n, Inv.ords(I.Uni.table(u), oids)),
          Iv.Inventory.present(Iv.Inv.fold(I.Uni.table(u), oids,
            Iv.Inv{S.PSet.empty(), 0n, 0n, 0n})),
          Iv.Inventory.present(Iv.Inv.project(u, oids)),
          Equal.sym(S.PSet,
            Iv.Inventory.present(Iv.Inv.fold(I.Uni.table(u), oids,
              Iv.Inv{S.PSet.empty(), 0n, 0n, 0n})),
            S.PSet.from_list(20n, Inv.ords(I.Uni.table(u), oids)),
            Inv.fold_of_list(oids,
              Inv.head_find(I.Uni.table(u), oids), I.Uni.table(u),
              Iv.Inv{S.PSet.empty(), 0n, 0n, 0n}, {==})),
          Equal.sym(S.PSet,
            Iv.Inventory.present(Iv.Inv.project(u, oids)),
            Iv.Inventory.present(Iv.Inv.fold(I.Uni.table(u), oids,
              Iv.Inv{S.PSet.empty(), 0n, 0n, 0n})),
            Inv.present_finish(Iv.Inv.fold(I.Uni.table(u), oids,
              Iv.Inv{S.PSet.empty(), 0n, 0n, 0n}))))),
      ok))
