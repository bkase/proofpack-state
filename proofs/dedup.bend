# proofs/dedup.bend -- a reused answer is the answer that cell would have
# computed (law Q-04).
#
# `pp git matrix` answers one cell per *distinct* inventory. Two inventories
# count as the same when `PSet.is_subset` holds both ways, which is a count in
# both directions and says nothing on its face about what the cells compute.
# This module closes that gap: two inventories that compare equal are equally
# ready, and leave the same objects missing, so the reused answer is the one
# the duplicate cell would have produced.
#
# Readiness is the easy half -- it *is* a subset test, so transitivity carries
# it across. The missing statistics are the other half: they fold over
# `PSet.missing`, a list, and two lists with the same members give the same
# fold only because both ascend strictly, which makes the list a function of
# its members.

import Base
import ./eq.bend as E
import ./closalg.bend as Ca
import ./subsetalg.bend as Sa2
import ./subsetconv.bend as Sc
import ./split_add.bend as Sa
import ./ascext.bend as Ae
import ./ascdiffwalk.bend as Aw
import ./orderlist.bend as Ol
import ../core/word.bend as W
import ../core/count.bend as C
import ../core/set.bend as S
import ../query/eval.bend as Qe
import ../query/ast.bend as A
import ../index/source.bend as Idx
import ../cli/main.bend as Cm
import ../cli/json.bend as J

# ---------------------------------------------------------------------------
# Readiness.
# ---------------------------------------------------------------------------

law Ev.ready_same:
  for +k: S.PSet
  for +h1: S.PSet
  for +h2: S.PSet
  for +vk: {S.PSet.valid(20n, k, True{}) == True{} : Bool}
  for +v1: {S.PSet.valid(20n, h1, True{}) == True{} : Bool}
  for +v2: {S.PSet.valid(20n, h2, True{}) == True{} : Bool}
  for +sm: {Ca.PSet.same(20n, h1, h2) == True{} : Bool}
  {Qe.Ev.ready(k, h1) == Qe.Ev.ready(k, h2) : Bool}

def Ev.ready_same.pick(+k: S.PSet, +h1: S.PSet, +h2: S.PSet,
  +vk: {S.PSet.valid(20n, k, True{}) == True{} : Bool},
  +v1: {S.PSet.valid(20n, h1, True{}) == True{} : Bool},
  +v2: {S.PSet.valid(20n, h2, True{}) == True{} : Bool},
  +sm: {Ca.PSet.same(20n, h1, h2) == True{} : Bool},
  +b1: Bool, +e1: {b1 == S.PSet.is_subset(20n, k, h1) : Bool},
  +b2: Bool, +e2: {b2 == S.PSet.is_subset(20n, k, h2) : Bool})
  -> {S.PSet.is_subset(20n, k, h1) == S.PSet.is_subset(20n, k, h2)
    : Bool}:
  match b1:
    case True{}:
      match b2:
        case True{}:
          %e1 : {_ == S.PSet.is_subset(20n, k, h2) : Bool}
          %e2 : {True{} == _ : Bool}
          {==}
        case False{}:
          %e1 : {_ == S.PSet.is_subset(20n, k, h2) : Bool}
          %e2 : {True{} == _ : Bool}
          E.Bool.noconf.r({True{} == False{} : Bool},
            Equal.trans(Bool, True{}, S.PSet.is_subset(20n, k, h2),
              False{},
              E.Bool.sym(S.PSet.is_subset(20n, k, h2), True{},
                Sa2.PSet.subset_trans(20n, k, h1, h2, vk, v1, v2, {==},
                  E.Bool.sym(True{}, S.PSet.is_subset(20n, k, h1), e1),
                  E.Bool.and_l(S.PSet.is_subset(20n, h1, h2),
                    S.PSet.is_subset(20n, h2, h1), sm))),
              E.Bool.sym(False{}, S.PSet.is_subset(20n, k, h2), e2)))
    case False{}:
      match b2:
        case True{}:
          %e1 : {_ == S.PSet.is_subset(20n, k, h2) : Bool}
          %e2 : {False{} == _ : Bool}
          E.Bool.noconf({False{} == True{} : Bool},
            Equal.trans(Bool, False{}, S.PSet.is_subset(20n, k, h1),
              True{}, e1,
              Sa2.PSet.subset_trans(20n, k, h2, h1, vk, v2, v1, {==},
                E.Bool.sym(True{}, S.PSet.is_subset(20n, k, h2), e2),
                E.Bool.and_r(S.PSet.is_subset(20n, h1, h2),
                  S.PSet.is_subset(20n, h2, h1), sm))))
        case False{}:
          %e1 : {_ == S.PSet.is_subset(20n, k, h2) : Bool}
          %e2 : {False{} == _ : Bool}
          {==}

def Ev.ready_same(k, h1, h2, vk, v1, v2, sm):
  Ev.ready_same.pick(k, h1, h2, vk, v1, v2, sm,
    S.PSet.is_subset(20n, k, h1), {==},
    S.PSet.is_subset(20n, k, h2), {==})

# ---------------------------------------------------------------------------
# The objects left missing.
#
# `Ev.missing_stats` folds over `PSet.missing`, a *list*, so equal members are
# not enough on their own -- a fold sees order and repetition. What makes it
# enough here is that `PSet.missing` ascends strictly (proofs/ascdiffwalk.bend),
# which makes the list a function of its members (proofs/ascext.bend). So the
# two lists are not merely equivalent: they are the same list.
# ---------------------------------------------------------------------------

def Ords.miss_shape(+r: Bool, +mk: Bool, m: Bool) -> Bool:
  Bool.and(r, Bool.and(mk, Bool.not(m)))

law Ords.missing_same_at:
  for +d: Nat
  for +k: S.PSet
  for +h1: S.PSet
  for +h2: S.PSet
  for +x: U32
  for +vk: {S.PSet.valid(d, k, True{}) == True{} : Bool}
  for +v1: {S.PSet.valid(d, h1, True{}) == True{} : Bool}
  for +v2: {S.PSet.valid(d, h2, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +sm: {Ca.PSet.same(d, h1, h2) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, S.PSet.missing(d, k, h1), x)
    == List.contains(~U32, ~U32.is_eq, S.PSet.missing(d, k, h2), x)
    : Bool}

def Ords.missing_same_at(d, k, h1, h2, x, vk, v1, v2, lt, sm):
  Equal.trans(Bool,
    List.contains(~U32, ~U32.is_eq, S.PSet.missing(d, k, h1), x),
    Ords.miss_shape(U32.is_eq(0, W.U32.diff(x, W.U32.mask(12n+d))),
      S.PSet.mem(d, k, S.PSet.half(d),
        U32.and(x, W.U32.mask(12n+d))),
      S.PSet.mem(d, h1, S.PSet.half(d),
        U32.and(x, W.U32.mask(12n+d)))),
    List.contains(~U32, ~U32.is_eq, S.PSet.missing(d, k, h2), x),
    Sc.PSet.missing_contains(d, k, h1, x, vk, v1, lt),
    Equal.trans(Bool,
      Ords.miss_shape(U32.is_eq(0, W.U32.diff(x, W.U32.mask(12n+d))),
        S.PSet.mem(d, k, S.PSet.half(d),
          U32.and(x, W.U32.mask(12n+d))),
        S.PSet.mem(d, h1, S.PSet.half(d),
          U32.and(x, W.U32.mask(12n+d)))),
      Ords.miss_shape(U32.is_eq(0, W.U32.diff(x, W.U32.mask(12n+d))),
        S.PSet.mem(d, k, S.PSet.half(d),
          U32.and(x, W.U32.mask(12n+d))),
        S.PSet.mem(d, h2, S.PSet.half(d),
          U32.and(x, W.U32.mask(12n+d)))),
      List.contains(~U32, ~U32.is_eq, S.PSet.missing(d, k, h2), x),
      Equal.cong(Bool, Bool,
        Ords.miss_shape(
          U32.is_eq(0, W.U32.diff(x, W.U32.mask(12n+d))),
          S.PSet.mem(d, k, S.PSet.half(d),
            U32.and(x, W.U32.mask(12n+d)))),
        S.PSet.mem(d, h1, S.PSet.half(d),
          U32.and(x, W.U32.mask(12n+d))),
        S.PSet.mem(d, h2, S.PSet.half(d),
          U32.and(x, W.U32.mask(12n+d))),
        Ca.PSet.member_same(d, h1, h2,
          U32.and(x, W.U32.mask(12n+d)), v1, v2, lt,
          Sa.U32.hi_zero_low(x, 12n+d), sm)),
      E.Bool.sym(
        List.contains(~U32, ~U32.is_eq, S.PSet.missing(d, k, h2), x),
        Ords.miss_shape(
          U32.is_eq(0, W.U32.diff(x, W.U32.mask(12n+d))),
          S.PSet.mem(d, k, S.PSet.half(d),
            U32.and(x, W.U32.mask(12n+d))),
          S.PSet.mem(d, h2, S.PSet.half(d),
            U32.and(x, W.U32.mask(12n+d)))),
        Sc.PSet.missing_contains(d, k, h2, x, vk, v2, lt))))

law Ords.all_in_missing:
  for +d: Nat
  for +k: S.PSet
  for +h1: S.PSet
  for +h2: S.PSet
  for +l: List<&2, U32>
  for +vk: {S.PSet.valid(d, k, True{}) == True{} : Bool}
  for +v1: {S.PSet.valid(d, h1, True{}) == True{} : Bool}
  for +v2: {S.PSet.valid(d, h2, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +sm: {Ca.PSet.same(d, h1, h2) == True{} : Bool}
  for +ai: {Sa2.Ords.all_in(l, S.PSet.missing(d, k, h1)) == True{}
    : Bool}
  {Sa2.Ords.all_in(l, S.PSet.missing(d, k, h2)) == True{} : Bool}

def Ords.all_in_missing(d, k, h1, h2, l, vk, v1, v2, lt, sm, ai):
  match l:
    case Nil{}:
      {==}
    case Con{z, u}:
      E.Bool.and_both(List.contains(~U32, ~U32.is_eq,
        S.PSet.missing(d, k, h2), z),
        Sa2.Ords.all_in(u, S.PSet.missing(d, k, h2)),
        Equal.trans(Bool, List.contains(~U32, ~U32.is_eq,
          S.PSet.missing(d, k, h2), z),
          List.contains(~U32, ~U32.is_eq,
            S.PSet.missing(d, k, h1), z), True{},
          E.Bool.sym(List.contains(~U32, ~U32.is_eq,
            S.PSet.missing(d, k, h1), z),
            List.contains(~U32, ~U32.is_eq,
              S.PSet.missing(d, k, h2), z),
            Ords.missing_same_at(d, k, h1, h2, z, vk, v1, v2, lt,
              sm)),
          E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
            S.PSet.missing(d, k, h1), z),
            Sa2.Ords.all_in(u, S.PSet.missing(d, k, h1)), ai)),
        Ords.all_in_missing(d, k, h1, h2, u, vk, v1, v2, lt, sm,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.missing(d, k, h1), z),
            Sa2.Ords.all_in(u, S.PSet.missing(d, k, h1)), ai)))

law Ords.missing_eq:
  for +d: Nat
  for +k: S.PSet
  for +h1: S.PSet
  for +h2: S.PSet
  for +vk: {S.PSet.valid(d, k, True{}) == True{} : Bool}
  for +v1: {S.PSet.valid(d, h1, True{}) == True{} : Bool}
  for +v2: {S.PSet.valid(d, h2, True{}) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +sm: {Ca.PSet.same(d, h1, h2) == True{} : Bool}
  {S.PSet.missing(d, k, h1) == S.PSet.missing(d, k, h2)
    : List<&2, U32>}

def Ords.missing_eq(d, k, h1, h2, vk, v1, v2, lt, sm):
  Ae.Ords.asc_ext(S.PSet.missing(d, k, h1), S.PSet.missing(d, k, h2),
    Aw.Ords.asc_missing(d, k, h1, vk, v1, lt),
    Aw.Ords.asc_missing(d, k, h2, vk, v2, lt),
    E.Bool.and_both(
      Sa2.Ords.all_in(S.PSet.missing(d, k, h1),
        S.PSet.missing(d, k, h2)),
      Sa2.Ords.all_in(S.PSet.missing(d, k, h2),
        S.PSet.missing(d, k, h1)),
      Ords.all_in_missing(d, k, h1, h2, S.PSet.missing(d, k, h1),
        vk, v1, v2, lt, sm,
        Sa2.Ords.all_in_self(S.PSet.missing(d, k, h1))),
      Ords.all_in_missing(d, k, h2, h1, S.PSet.missing(d, k, h2),
        vk, v2, v1, lt, Ca.PSet.same_sym(d, h1, h2, sm),
        Sa2.Ords.all_in_self(S.PSet.missing(d, k, h2)))))

# ---------------------------------------------------------------------------
# The cell's answer.
# ---------------------------------------------------------------------------

def Ev.miss_fold(src: Idx.Source, l: List<&2, U32>) -> A.Stats:
  Qe.Ev.stats.of(src, l, A.Stats.zero())

law Ev.missing_stats_same:
  for +src: Idx.Source
  for +k: S.PSet
  for +h1: S.PSet
  for +h2: S.PSet
  for +vk: {S.PSet.valid(20n, k, True{}) == True{} : Bool}
  for +v1: {S.PSet.valid(20n, h1, True{}) == True{} : Bool}
  for +v2: {S.PSet.valid(20n, h2, True{}) == True{} : Bool}
  for +sm: {Ca.PSet.same(20n, h1, h2) == True{} : Bool}
  {Qe.Ev.missing_stats(src, k, h1) == Qe.Ev.missing_stats(src, k, h2)
    : A.Stats}

def Ev.missing_stats_same(src, k, h1, h2, vk, v1, v2, sm):
  Equal.cong(List<&2, U32>, A.Stats, Ev.miss_fold(src),
    S.PSet.missing(20n, k, h1), S.PSet.missing(20n, k, h2),
    Ords.missing_eq(20n, k, h1, h2, vk, v1, v2, {==}, sm))

def Ev.answer_shape(+r: Bool, st: A.Stats) -> String:
  J.Json.obj([
    J.Json.field("ready_at_observation", J.Json.bool(r)),
    J.Json.field("missing", Cm.Cli.stats_json(st))])

def Ev.answer_at(st: A.Stats, r: Bool) -> String:
  Ev.answer_shape(r, st)

law Cmd.matrix.answer_same:
  for +src: Idx.Source
  for +k: S.PSet
  for +h1: S.PSet
  for +h2: S.PSet
  for +vk: {S.PSet.valid(20n, k, True{}) == True{} : Bool}
  for +v1: {S.PSet.valid(20n, h1, True{}) == True{} : Bool}
  for +v2: {S.PSet.valid(20n, h2, True{}) == True{} : Bool}
  for +sm: {Cm.Cmd.matrix.same(h1, h2) == True{} : Bool}
  {Cm.Cmd.matrix.answer(src, k, h1)
    == Cm.Cmd.matrix.answer(src, k, h2) : String}

def Cmd.matrix.answer_same(src, k, h1, h2, vk, v1, v2, sm):
  Equal.trans(String,
    Ev.answer_shape(Qe.Ev.ready(k, h1),
      Qe.Ev.missing_stats(src, k, h1)),
    Ev.answer_shape(Qe.Ev.ready(k, h2),
      Qe.Ev.missing_stats(src, k, h1)),
    Ev.answer_shape(Qe.Ev.ready(k, h2),
      Qe.Ev.missing_stats(src, k, h2)),
    Equal.cong(Bool, String,
      Ev.answer_at(Qe.Ev.missing_stats(src, k, h1)),
      Qe.Ev.ready(k, h1), Qe.Ev.ready(k, h2),
      Ev.ready_same(k, h1, h2, vk, v1, v2, sm)),
    Equal.cong(A.Stats, String,
      Ev.answer_shape(Qe.Ev.ready(k, h2)),
      Qe.Ev.missing_stats(src, k, h1),
      Qe.Ev.missing_stats(src, k, h2),
      Ev.missing_stats_same(src, k, h1, h2, vk, v1, v2, sm)))
