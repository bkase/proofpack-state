# proofs/listsub.bend -- a set built from a list is inside anything the list
# is inside.
#
# The bridge the closure proofs use when they have to bound `PSet.from_list`:
# every ordinal on the list is a member of the bounding set, so every member
# of the set the list builds is too. It is stated as a subset rather than
# pointwise because that is what an induction can carry.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./shift.bend as Sf
import ./subsetconv.bend as Sc
import ./subsetalg.bend as Sa
import ./listset.bend as Ls
import ./insertvalid.bend as Iv
import ../core/count.bend as C
import ../core/set.bend as S

law Ords.all_mem_of_from_list:
  for +l2: List<&2, U32>
  for +l: List<&2, U32>
  for +sd: Nat
  for +xx: S.PSet
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +lfit: {Sf.Ords.all_fit(l, 12n+sd) == True{} : Bool}
  for +am: {Sc.Ords.all_mem(l, sd, xx) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l2,
    S.PSet.to_list(sd, S.PSet.from_list(sd, l))) == True{} : Bool}
  {Sc.Ords.all_mem(l2, sd, xx) == True{} : Bool}

def Ords.all_mem_of_from_list(l2, l, sd, xx, lt, lfit, am, ai):
  match l2:
    case Nil{}:
      {==}
    case Con{u, rest}:
      E.Bool.and_both(S.PSet.member(sd, xx, u),
        Sc.Ords.all_mem(rest, sd, xx),
        Sc.Ords.all_mem_at(l, sd, xx, u, Sc.Ords.head_eq(l, u),
          {==}, am,
          Ls.PSet.from_list_only_at(l, sd, u, lt,
            Sa.PSet.in_range_of_to_list(sd, S.PSet.from_list(sd, l),
              u, Iv.PSet.valid_from_list(l, sd, lt, lfit), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(sd, S.PSet.from_list(sd, l)), u),
                Sa.Ords.all_in(rest, S.PSet.to_list(sd,
                  S.PSet.from_list(sd, l))), ai)), lfit,
            Sa.PSet.member_of_to_list(sd, S.PSet.from_list(sd, l), u,
              Iv.PSet.valid_from_list(l, sd, lt, lfit), lt,
              E.Bool.and_l(List.contains(~U32, ~U32.is_eq,
                S.PSet.to_list(sd, S.PSet.from_list(sd, l)), u),
                Sa.Ords.all_in(rest, S.PSet.to_list(sd,
                  S.PSet.from_list(sd, l))), ai)))),
        Ords.all_mem_of_from_list(rest, l, sd, xx, lt, lfit, am,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq,
            S.PSet.to_list(sd, S.PSet.from_list(sd, l)), u),
            Sa.Ords.all_in(rest, S.PSet.to_list(sd,
              S.PSet.from_list(sd, l))), ai)))

law PSet.subset_of_list_mem:
  for +l: List<&2, U32>
  for +sd: Nat
  for +xx: S.PSet
  for +lt: {C.Nat.gt(32n, 11n+sd) == True{} : Bool}
  for +lfit: {Sf.Ords.all_fit(l, 12n+sd) == True{} : Bool}
  for +vx: {S.PSet.valid(sd, xx, True{}) == True{} : Bool}
  for +am: {Sc.Ords.all_mem(l, sd, xx) == True{} : Bool}
  {S.PSet.is_subset(sd, S.PSet.from_list(sd, l), xx) == True{}
    : Bool}

def PSet.subset_of_list_mem(l, sd, xx, lt, lfit, vx, am):
  Sc.PSet.subset_of_members(sd, S.PSet.from_list(sd, l), xx,
    Iv.PSet.valid_from_list(l, sd, lt, lfit), vx, lt,
    Ords.all_mem_of_from_list(
      S.PSet.to_list(sd, S.PSet.from_list(sd, l)), l, sd, xx, lt,
      lfit, am,
      Sa.Ords.all_in_self(
        S.PSet.to_list(sd, S.PSet.from_list(sd, l)))))
