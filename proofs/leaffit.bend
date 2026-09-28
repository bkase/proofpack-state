# proofs/leaffit.bend -- everything the fused leaf emits fits in a leaf.
#
# The enumeration shifts a leaf's list by the node's base, and the shift law
# needs every ordinal on the list to fit in the twelve bits a leaf covers.
# For the fused difference that is an arm per pair of shapes, each reducing
# to one of three facts: a count-down of 4096 fits, a tile's walk fits, and a
# merge keeps whatever fit on its first operand.
#
# Each arm is its own definition on purpose. The kernel checks a definition
# with a fixed budget, and a full leaf's 4096 ordinals are most of one.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./shift.bend as Sf
import ./tilefit.bend as Tf
import ./tileorder.bend as To
import ./interval.bend as It
import ./split.bend as Sp2
import ./leafenum.bend as Le
import ../core/count.bend as C
import ../core/ords.bend as O
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# Everything the fused leaf emits fits in a leaf.
# ---------------------------------------------------------------------------

law Ords.all_fit_diff_go:
  for +fuel: Nat
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +c: Cmp
  for +fa: {Sf.Ords.all_fit(a, 12n) == True{} : Bool}
  {Sf.Ords.all_fit(O.Ords.diff.go(fuel, a, b, c), 12n) == True{}
    : Bool}

def Ords.all_fit_diff_go(fuel, a, b, c, fa):
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      match a:
        case Nil{}:
          {==}
        case Con{ah, at}:
          match b:
            case Nil{}:
              fa
            case Con{bh, bt}:
              match c:
                case LT{}:
                  E.Bool.and_both(Dc.U32.hi_zero(ah, 12n),
                    Sf.Ords.all_fit(O.Ords.diff.go(f, at,
                      Con{bh, bt}, O.Ords.head_cmp(at,
                        Con{bh, bt})), 12n),
                    E.Bool.and_l(Dc.U32.hi_zero(ah, 12n),
                      Sf.Ords.all_fit(at, 12n), fa),
                    Ords.all_fit_diff_go(f, at, Con{bh, bt},
                      O.Ords.head_cmp(at, Con{bh, bt}),
                      E.Bool.and_r(Dc.U32.hi_zero(ah, 12n),
                        Sf.Ords.all_fit(at, 12n), fa)))
                case GT{}:
                  Ords.all_fit_diff_go(f, Con{ah, at}, bt,
                    O.Ords.head_cmp(Con{ah, at}, bt), fa)
                case EQ{}:
                  Ords.all_fit_diff_go(f, at, bt,
                    O.Ords.head_cmp(at, bt),
                    E.Bool.and_r(Dc.U32.hi_zero(ah, 12n),
                      Sf.Ords.all_fit(at, 12n), fa))

law Ords.all_fit_diff:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +fa: {Sf.Ords.all_fit(a, 12n) == True{} : Bool}
  {Sf.Ords.all_fit(O.Ords.diff(a, b), 12n) == True{} : Bool}

def Ords.all_fit_diff(a, b, fa):
  Ords.all_fit_diff_go(O.Ords.merge_fuel(a, b), a, b,
    O.Ords.head_cmp(a, b), fa)

law Ords.all_fit_leaf_diff:
  for +a: S.PSet
  for +b: S.PSet
  for +va: {Le.PSet.ok.leaf(a) == True{} : Bool}
  {Sf.Ords.all_fit(S.PSet.leaf_diff_members(a, b), 12n) == True{}
    : Bool}

def Ords.all_fit_sp_arm(+ao: List<&2, U32>, +b: S.PSet,
  +va: {Sf.Ords.all_fit(ao, 12n) == True{} : Bool})
  -> {Sf.Ords.all_fit(S.PSet.leaf_diff_members.sp(ao, b), 12n)
     == True{} : Bool}:
  match b:
    case S.PZero{}:
      va
    case S.PBranch{l, h}:
      va
    case S.PFull{}:
      {==}
    case S.PSparse{bo}:
      Ords.all_fit_diff(ao, bo, va)
    case S.PDense{bw}:
      Ords.all_fit_diff(ao, Wo.Words.members(bw, 0), va)

def Ords.all_fit_full_sparse(+bo: List<&2, U32>)
  -> {Sf.Ords.all_fit(O.Ords.diff(S.PSet.range(4096n, 4095, Nil{}),
       bo), 12n) == True{} : Bool}:
  Ords.all_fit_diff(S.PSet.range(4096n, 4095, Nil{}), bo,
    Tf.Ords.all_fit_full_leaf())

# The fused tile walk's own fit, proved directly rather than through the
# difference tile: the kernel would otherwise have to walk 128 words of a
# concrete tile to compare the two shapes.
law Words.diff_members_go_fit:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +ord: U32
  for +acc: List<&2, U32>
  for +facc: {Sf.Ords.all_fit(acc, 12n) == True{} : Bool}
  for +bnd: {C.Nat.upto(Nat.add(U32.to_nat(ord),
    Sp2.Nat.dbl(5n, List.length(&2, U32, a))), 4096n)
    == True{} : Bool}
  {Sf.Ords.all_fit(Wo.Words.diff_members.go(a, b, ord, acc), 12n)
    == True{} : Bool}

def Words.diff_members_go_fit(a, b, ord, acc, facc, bnd):
  match a:
    case Nil{}:
      facc
    case Con{ah, at}:
      match b:
        case Nil{}:
          Tf.Words.members_go_fit(Con{ah, at}, ord, acc, facc, bnd)
        case Con{bh, bt}:
          Words.diff_members_go_fit(at, bt, (ord + 32 : U32),
            Wo.Words.bits_rev(32n, W.U32.diff(ah, bh), ord, acc),
            Tf.Words.bits_rev_fit(32n, W.U32.diff(ah, bh), ord, acc,
              facc,
              Tf.Nat.word_room(U32.to_nat(ord),
                List.length(&2, U32, at), bnd)),
            It.Nat.upto_cast(
              Nat.add(U32.to_nat(ord),
                Sp2.Nat.dbl(5n, 1n+List.length(&2, U32, at))),
              Nat.add(U32.to_nat((ord + 32 : U32)),
                Sp2.Nat.dbl(5n, List.length(&2, U32, at))), 4096n,
              4096n,
              Tf.Nat.word_step(U32.to_nat(ord),
                List.length(&2, U32, at),
                U32.to_nat((ord + 32 : U32)),
                Tf.U32.add_small(ord, 32, 12n,
                  Tf.U32.fits_of_le(ord, 31n,
                    Tf.Nat.word_room(U32.to_nat(ord),
                      List.length(&2, U32, at), bnd)), {==}, {==})),
              {==}, bnd))

law Words.diff_members_fit:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +la: {Nat.is_eq(List.length(&2, U32, a), 128n) == True{}
    : Bool}
  {Sf.Ords.all_fit(Wo.Words.diff_members(a, b, 0), 12n) == True{}
    : Bool}

def Words.diff_members_fit(a, b, la):
  Tf.Ords.all_fit_reverse_go(Wo.Words.diff_members.go(a, b, 0, Nil{}),
    Nil{},
    Words.diff_members_go_fit(a, b, 0, Nil{}, {==},
      Tf.Words.tile_room(a, la)), {==})

def Ords.all_fit_dn_arm(+aw: List<&2, U32>, +b: S.PSet,
  +la: {Nat.is_eq(List.length(&2, U32, aw), 128n) == True{} : Bool})
  -> {Sf.Ords.all_fit(S.PSet.leaf_diff_members.dn(aw, b), 12n)
     == True{} : Bool}:
  match b:
    case S.PZero{}:
      Tf.Words.members_fit(aw, la)
    case S.PBranch{l, h}:
      Tf.Words.members_fit(aw, la)
    case S.PFull{}:
      {==}
    case S.PSparse{bo}:
      Ords.all_fit_diff(Wo.Words.members(aw, 0), bo,
        Tf.Words.members_fit(aw, la))
    case S.PDense{bw}:
      Words.diff_members_fit(aw, bw, la)

def Ords.all_fit_full_dense(+bw: List<&2, U32>)
  -> {Sf.Ords.all_fit(Wo.Words.diff_members(Wo.Words.ones(128n), bw,
       0), 12n) == True{} : Bool}:
  Words.diff_members_fit(Wo.Words.ones(128n), bw, {==})

# Stating the fit over an abstract list, with the concrete one supplied as
# an equation, is what keeps the kernel's work to a single pass over a full
# leaf's 4096 ordinals: the equation costs one comparison of the lists, and
# nothing downstream ever has to normalise them again.
law Ords.all_fit_at:
  for +l: List<&2, U32>
  for +m: List<&2, U32>
  for +el: {l == m : List<&2, U32>}
  for +fm: {Sf.Ords.all_fit(m, 12n) == True{} : Bool}
  {Sf.Ords.all_fit(l, 12n) == True{} : Bool}

def Ords.all_fit_at(l, m, el, fm):
  %E.List.sym(U32, l, m, el)
    : {Sf.Ords.all_fit(_, 12n) == True{} : Bool}
  fm

law Ords.full_zero_list:
  {S.PSet.leaf_diff_members.full(S.PZero{})
    == S.PSet.range(4096n, 4095, Nil{}) : List<&2, U32>}

def Ords.full_zero_list():
  {==}

def Ords.all_fit_full_zero()
  -> {Sf.Ords.all_fit(S.PSet.leaf_diff_members.full(S.PZero{}), 12n)
     == True{} : Bool}:
  Ords.all_fit_at(S.PSet.leaf_diff_members.full(S.PZero{}),
    S.PSet.range(4096n, 4095, Nil{}), Ords.full_zero_list(),
    Tf.Ords.all_fit_full_leaf())

law Ords.full_branch_list:
  for +l: S.PSet
  for +h: S.PSet
  {S.PSet.leaf_diff_members.full(S.PBranch{l, h})
    == S.PSet.range(4096n, 4095, Nil{}) : List<&2, U32>}

def Ords.full_branch_list(l, h):
  {==}

def Ords.all_fit_full_branch(+l: S.PSet, +h: S.PSet)
  -> {Sf.Ords.all_fit(S.PSet.leaf_diff_members.full(
       S.PBranch{l, h}), 12n) == True{} : Bool}:
  Ords.all_fit_at(S.PSet.leaf_diff_members.full(S.PBranch{l, h}),
    S.PSet.range(4096n, 4095, Nil{}), Ords.full_branch_list(l, h),
    Tf.Ords.all_fit_full_leaf())

def Ords.all_fit_full_arm(+b: S.PSet)
  -> {Sf.Ords.all_fit(S.PSet.leaf_diff_members.full(b), 12n)
     == True{} : Bool}:
  match b:
    case S.PZero{}:
      Ords.all_fit_full_zero()
    case S.PBranch{l, h}:
      Ords.all_fit_full_branch(l, h)
    case S.PFull{}:
      {==}
    case S.PSparse{bo}:
      Ords.all_fit_full_sparse(bo)
    case S.PDense{bw}:
      Ords.all_fit_full_dense(bw)

def Ords.all_fit_leaf_diff(a, b, va):
  match a:
    case S.PZero{}:
      {==}
    case S.PBranch{l, h}:
      {==}
    case S.PFull{}:
      Ords.all_fit_full_arm(b)
    case S.PSparse{ao}:
      Ords.all_fit_sp_arm(ao, b, va)
    case S.PDense{aw}:
      Ords.all_fit_dn_arm(aw, b, va)
