# proofs/leafdiff.bend -- what the fused leaf difference emits.
#
# SPEC 7.2's fused leaf computes the members of `a \ b` without building
# `a \ b`, picking the cheapest walk for the pair of shapes it got: a sparse
# operand is merged as a list, two dense operands go through the word kernel,
# and a `PFull` or `PZero` operand short-circuits. This says every arm is
# right -- an ordinal is on the list exactly when the leaf `a` holds it and
# the leaf `b` does not.
#
# The merge arms need both lists ascending. For a sparse leaf that is what
# `PSet.valid` checks; for a tile it is proofs/tileorder.bend; for a full
# leaf's count-down it is the same file.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./order.bend as Or
import ./descend.bend as Dc
import ./orderlist.bend as Ol
import ./tileorder.bend as To
import ./merge.bend as Mg
import ./leafenum.bend as Le
import ./treeenum.bend as Te
import ./validshape.bend as Vs
import ./words.bend as Wd
import ./faithful.bend as Fa
import ./split_add.bend as Sa
import ../core/count.bend as C
import ../core/ords.bend as O
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# A valid sparse leaf's offsets ascend.
# ---------------------------------------------------------------------------

law Nat.cmp_is_gt:
  for +m: Nat
  for +n: Nat
  {Cmp.is_gt(Nat.cmp(m, n)) == C.Nat.gt(m, n) : Bool}

def Nat.cmp_is_gt(m, n):
  match m:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      match n:
        case 0n:
          {==}
        case 1n+q:
          Nat.cmp_is_gt(p, q)

law U32.lt_of_is_gt:
  for +z: U32
  for +o: U32
  for +g: {U32.is_gt(z, o) == True{} : Bool}
  {U32.is_lt(o, z) == True{} : Bool}

def U32.gt_value(+z: U32, +o: U32,
  +g: {U32.is_gt(z, o) == True{} : Bool})
  -> {C.Nat.gt(U32.to_nat(z), U32.to_nat(o)) == True{} : Bool}:
  %Nat.cmp_is_gt(U32.to_nat(z), U32.to_nat(o))
    : {_ == True{} : Bool}
  %Or.U32.cmp_spec(z, o)
    : {Cmp.is_gt(_) == True{} : Bool}
  g

def U32.lt_of_is_gt(z, o, g):
  Ol.U32.lt_of_nat(o, z, U32.gt_value(z, o, g))

law Ords.asc_of_valid_offs:
  for +offs: List<&2, U32>
  for +last: U32
  for +first: Bool
  for +ok: Bool
  for +v: {S.PSet.valid.offs(offs, last, first, ok) == True{} : Bool}
  {Ol.Ords.asc(offs) == True{} : Bool}

# The walk's accumulator is the previous element's check, and a walk that
# ends in `True{}` never passed through `False{}`.
law Ords.valid_cast:
  for +l: List<&2, U32>
  for +last: U32
  for +first: Bool
  for +acc: Bool
  for +ea: {acc == True{} : Bool}
  for +v: {S.PSet.valid.offs(l, last, first, acc) == True{} : Bool}
  {S.PSet.valid.offs(l, last, first, True{}) == True{} : Bool}

def Ords.valid_cast(l, last, first, acc, ea, v):
  %ea : {S.PSet.valid.offs(l, last, first, _) == True{} : Bool}
  v

def Ords.acc_true(+u: List<&2, U32>, +z: U32, +o: U32,
  +v: {S.PSet.valid.offs(Con{z, u}, o, False{}, True{}) == True{}
    : Bool})
  -> {Bool.and(U32.is_lt(z, 4096),
       Bool.or(False{}, U32.is_gt(z, o))) == True{} : Bool}:
  Vs.PSet.valid_offs_acc(u, z, False{},
    Bool.and(U32.is_lt(z, 4096),
      Bool.or(False{}, U32.is_gt(z, o))), v)

def Ords.asc_of_valid_offs(offs, last, first, ok, v):
  match offs:
    case Nil{}:
      {==}
    case Con{o, t}:
      match t:
        case Nil{}:
          {==}
        case Con{z, u}:
          match ok:
            case False{}:
              E.Bool.noconf({Ol.Ords.asc(Con{o, Con{z, u}})
                == True{} : Bool}, v)
            case True{}:
              E.Bool.and_both(U32.is_lt(o, z),
                Ol.Ords.asc(Con{z, u}),
                U32.lt_of_is_gt(z, o,
                  E.Bool.and_r(U32.is_lt(z, 4096),
                    Bool.or(False{}, U32.is_gt(z, o)),
                    Ords.acc_true(u, z, o,
                      Ords.valid_cast(Con{z, u}, o, False{},
                        Bool.and(U32.is_lt(o, 4096),
                          Bool.or(first, U32.is_gt(o, last))),
                        Vs.PSet.valid_offs_acc(Con{z, u}, o, False{},
                          Bool.and(U32.is_lt(o, 4096),
                            Bool.or(first, U32.is_gt(o, last))), v),
                        v)))),
                Ords.asc_of_valid_offs(Con{z, u}, o, False{},
                  Bool.and(U32.is_lt(o, 4096),
                    Bool.or(first, U32.is_gt(o, last))), v))

# ---------------------------------------------------------------------------
# The tile the fused walk never builds still has 128 words.
# ---------------------------------------------------------------------------

law Words.length_diff:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {List.length(&2, U32, Wo.Words.diff(a, b))
    == List.length(&2, U32, a) : Nat}

def Words.length_diff(a, b):
  match a:
    case Nil{}:
      {==}
    case Con{ah, at}:
      match b:
        case Nil{}:
          {==}
        case Con{bh, bt}:
          %E.Nat.sym(List.length(&2, U32, Wo.Words.diff(at, bt)),
            List.length(&2, U32, at), Words.length_diff(at, bt))
            : {1n+_ == 1n+List.length(&2, U32, at) : Nat}
          {==}

law Words.diff_len_ok:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +la: {Nat.is_eq(List.length(&2, U32, a), 128n) == True{}
    : Bool}
  {Nat.is_eq(List.length(&2, U32, Wo.Words.diff(a, b)), 128n)
    == True{} : Bool}

def Words.diff_len_ok(a, b, la):
  %E.Nat.sym(List.length(&2, U32, Wo.Words.diff(a, b)),
    List.length(&2, U32, a), Words.length_diff(a, b))
    : {Nat.is_eq(_, 128n) == True{} : Bool}
  la

# The fused tile walk, read as membership.
law Words.diff_members_bit:
  for +aw: List<&2, U32>
  for +bw: List<&2, U32>
  for +y: U32
  for +la: {Nat.is_eq(List.length(&2, U32, aw), 128n) == True{}
    : Bool}
  for +inr: {Dc.U32.hi_zero(y, 12n) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, Wo.Words.diff_members(aw, bw, 0),
    y)
    == Bool.and(Wo.Words.bit(aw, y),
         Bool.not(Wo.Words.bit(bw, y))) : Bool}

law Words.diff_bit:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +y: U32
  {Wo.Words.bit(Wo.Words.diff(a, b), y)
    == Bool.and(Wo.Words.bit(a, y), Bool.not(Wo.Words.bit(b, y)))
    : Bool}

def Words.diff_bit(a, b, y):
  Wd.Words.at_diff(a, b, U32.to_nat(U32.shrn(y, 5n)),
    U32.to_nat(U32.and(y, 31)))

def Words.diff_members_bit(aw, bw, y, la, inr):
  %E.List.sym(U32, Wo.Words.diff_members(aw, bw, 0),
    Wo.Words.members(Wo.Words.diff(aw, bw), 0),
    To.Words.diff_members_is_members(aw, bw, 0))
    : {List.contains(~U32, ~U32.is_eq, _, y)
      == Bool.and(Wo.Words.bit(aw, y),
           Bool.not(Wo.Words.bit(bw, y))) : Bool}
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      Wo.Words.members(Wo.Words.diff(aw, bw), 0), y),
    Wo.Words.bit(Wo.Words.diff(aw, bw), y),
    Le.PSet.leaf_members_mem(S.PDense{Wo.Words.diff(aw, bw)}, y, inr,
      Words.diff_len_ok(aw, bw, la)))
    : {_ == Bool.and(Wo.Words.bit(aw, y),
         Bool.not(Wo.Words.bit(bw, y))) : Bool}
  Words.diff_bit(aw, bw, y)

# ---------------------------------------------------------------------------
# A full leaf against each shape.
# ---------------------------------------------------------------------------

def PSet.leaf_diff_full(+b: S.PSet, +y: U32,
  +vb: {S.PSet.valid.leaf(b) == True{} : Bool},
  +inr: {Dc.U32.hi_zero(y, 12n) == True{} : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
       S.PSet.leaf_diff_members.full(b), y)
     == Bool.and(True{}, Bool.not(S.PSet.mem.leaf(b, y))) : Bool}:
  match b:
    case S.PZero{}:
      Le.PSet.full_leaf_enumerates(y, inr)
    case S.PFull{}:
      {==}
    case S.PBranch{l, h}:
      Le.PSet.full_leaf_enumerates(y, inr)
    case S.PSparse{bo}:
      %E.Bool.sym(O.Ords.elem(bo, y),
        List.contains(~U32, ~U32.is_eq, bo, y),
        Le.Ords.elem_contains(bo, y))
        : {List.contains(~U32, ~U32.is_eq,
            O.Ords.diff(S.PSet.range(4096n, 4095, Nil{}), bo), y)
          == Bool.not(_) : Bool}
      %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
          O.Ords.diff(S.PSet.range(4096n, 4095, Nil{}), bo), y),
        Bool.and(List.contains(~U32, ~U32.is_eq,
          S.PSet.range(4096n, 4095, Nil{}), y),
          Bool.not(List.contains(~U32, ~U32.is_eq, bo, y))),
        Mg.Ords.diff_contains(S.PSet.range(4096n, 4095, Nil{}), bo, y,
          To.Ords.asc_full_leaf(),
          Ords.asc_of_valid_offs(bo, 0, True{}, True{}, vb)))
        : {_ == Bool.not(List.contains(~U32, ~U32.is_eq, bo, y))
          : Bool}
      %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
          S.PSet.range(4096n, 4095, Nil{}), y), True{},
        Le.PSet.full_leaf_enumerates(y, inr))
        : {Bool.and(_,
            Bool.not(List.contains(~U32, ~U32.is_eq, bo, y)))
          == Bool.not(List.contains(~U32, ~U32.is_eq, bo, y))
          : Bool}
      {==}
    case S.PDense{bw}:
      %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
          Wo.Words.diff_members(Wo.Words.ones(128n), bw, 0), y),
        Bool.and(Wo.Words.bit(Wo.Words.ones(128n), y),
          Bool.not(Wo.Words.bit(bw, y))),
        Words.diff_members_bit(Wo.Words.ones(128n), bw, y, {==}, inr))
        : {_ == Bool.and(True{},
             Bool.not(Wo.Words.bit(bw, y))) : Bool}
      %E.Bool.sym(Wo.Words.bit(Wo.Words.ones(128n), y), True{},
        Fa.PSet.bit_ones_in_range(y, inr))
        : {Bool.and(_, Bool.not(Wo.Words.bit(bw, y)))
          == Bool.and(True{}, Bool.not(Wo.Words.bit(bw, y)))
          : Bool}
      {==}

# ---------------------------------------------------------------------------
# A sparse leaf against each shape.
# ---------------------------------------------------------------------------

def PSet.leaf_diff_sp(+ao: List<&2, U32>, +b: S.PSet, +y: U32,
  +aa: {Ol.Ords.asc(ao) == True{} : Bool},
  +vb: {S.PSet.valid.leaf(b) == True{} : Bool},
  +inr: {Dc.U32.hi_zero(y, 12n) == True{} : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
       S.PSet.leaf_diff_members.sp(ao, b), y)
     == Bool.and(O.Ords.elem(ao, y),
          Bool.not(S.PSet.mem.leaf(b, y))) : Bool}:
  match b:
    case S.PZero{}:
      %E.Bool.sym(Bool.and(O.Ords.elem(ao, y), True{}),
        O.Ords.elem(ao, y),
        Te.Bool.and_true_r(O.Ords.elem(ao, y)))
        : {List.contains(~U32, ~U32.is_eq, ao, y) == _ : Bool}
      E.Bool.sym(O.Ords.elem(ao, y),
        List.contains(~U32, ~U32.is_eq, ao, y),
        Le.Ords.elem_contains(ao, y))
    case S.PBranch{l, h}:
      %E.Bool.sym(Bool.and(O.Ords.elem(ao, y), True{}),
        O.Ords.elem(ao, y),
        Te.Bool.and_true_r(O.Ords.elem(ao, y)))
        : {List.contains(~U32, ~U32.is_eq, ao, y) == _ : Bool}
      E.Bool.sym(O.Ords.elem(ao, y),
        List.contains(~U32, ~U32.is_eq, ao, y),
        Le.Ords.elem_contains(ao, y))
    case S.PFull{}:
      E.Bool.sym(Bool.and(O.Ords.elem(ao, y), False{}), False{},
        Sa.Word.and_false_r(O.Ords.elem(ao, y)))
    case S.PSparse{bo}:
      %E.Bool.sym(O.Ords.elem(ao, y),
        List.contains(~U32, ~U32.is_eq, ao, y),
        Le.Ords.elem_contains(ao, y))
        : {List.contains(~U32, ~U32.is_eq, O.Ords.diff(ao, bo), y)
          == Bool.and(_, Bool.not(O.Ords.elem(bo, y))) : Bool}
      %E.Bool.sym(O.Ords.elem(bo, y),
        List.contains(~U32, ~U32.is_eq, bo, y),
        Le.Ords.elem_contains(bo, y))
        : {List.contains(~U32, ~U32.is_eq, O.Ords.diff(ao, bo), y)
          == Bool.and(List.contains(~U32, ~U32.is_eq, ao, y),
               Bool.not(_)) : Bool}
      Mg.Ords.diff_contains(ao, bo, y, aa,
        Ords.asc_of_valid_offs(bo, 0, True{}, True{}, vb))
    case S.PDense{bw}:
      %E.Bool.sym(O.Ords.elem(ao, y),
        List.contains(~U32, ~U32.is_eq, ao, y),
        Le.Ords.elem_contains(ao, y))
        : {List.contains(~U32, ~U32.is_eq,
            O.Ords.diff(ao, Wo.Words.members(bw, 0)), y)
          == Bool.and(_, Bool.not(Wo.Words.bit(bw, y))) : Bool}
      %Le.PSet.leaf_members_mem(S.PDense{bw}, y, inr, vb)
        : {List.contains(~U32, ~U32.is_eq,
            O.Ords.diff(ao, Wo.Words.members(bw, 0)), y)
          == Bool.and(List.contains(~U32, ~U32.is_eq, ao, y),
               Bool.not(_)) : Bool}
      Mg.Ords.diff_contains(ao, Wo.Words.members(bw, 0), y, aa,
        To.Ords.asc_members(bw, vb))

# ---------------------------------------------------------------------------
# A dense leaf against each shape.
# ---------------------------------------------------------------------------

def PSet.leaf_diff_dn(+aw: List<&2, U32>, +b: S.PSet, +y: U32,
  +la: {Nat.is_eq(List.length(&2, U32, aw), 128n) == True{} : Bool},
  +vb: {S.PSet.valid.leaf(b) == True{} : Bool},
  +inr: {Dc.U32.hi_zero(y, 12n) == True{} : Bool})
  -> {List.contains(~U32, ~U32.is_eq,
       S.PSet.leaf_diff_members.dn(aw, b), y)
     == Bool.and(Wo.Words.bit(aw, y),
          Bool.not(S.PSet.mem.leaf(b, y))) : Bool}:
  match b:
    case S.PZero{}:
      %E.Bool.sym(Bool.and(Wo.Words.bit(aw, y), True{}),
        Wo.Words.bit(aw, y),
        Te.Bool.and_true_r(Wo.Words.bit(aw, y)))
        : {List.contains(~U32, ~U32.is_eq,
            Wo.Words.members(aw, 0), y) == _ : Bool}
      Le.PSet.leaf_members_mem(S.PDense{aw}, y, inr, la)
    case S.PBranch{l, h}:
      %E.Bool.sym(Bool.and(Wo.Words.bit(aw, y), True{}),
        Wo.Words.bit(aw, y),
        Te.Bool.and_true_r(Wo.Words.bit(aw, y)))
        : {List.contains(~U32, ~U32.is_eq,
            Wo.Words.members(aw, 0), y) == _ : Bool}
      Le.PSet.leaf_members_mem(S.PDense{aw}, y, inr, la)
    case S.PFull{}:
      E.Bool.sym(Bool.and(Wo.Words.bit(aw, y), False{}), False{},
        Sa.Word.and_false_r(Wo.Words.bit(aw, y)))
    case S.PSparse{bo}:
      %E.Bool.sym(Wo.Words.bit(aw, y),
        List.contains(~U32, ~U32.is_eq, Wo.Words.members(aw, 0), y),
        E.Bool.sym(List.contains(~U32, ~U32.is_eq,
            Wo.Words.members(aw, 0), y), Wo.Words.bit(aw, y),
          Le.PSet.leaf_members_mem(S.PDense{aw}, y, inr, la)))
        : {List.contains(~U32, ~U32.is_eq,
            O.Ords.diff(Wo.Words.members(aw, 0), bo), y)
          == Bool.and(_, Bool.not(O.Ords.elem(bo, y))) : Bool}
      %E.Bool.sym(O.Ords.elem(bo, y),
        List.contains(~U32, ~U32.is_eq, bo, y),
        Le.Ords.elem_contains(bo, y))
        : {List.contains(~U32, ~U32.is_eq,
            O.Ords.diff(Wo.Words.members(aw, 0), bo), y)
          == Bool.and(List.contains(~U32, ~U32.is_eq,
               Wo.Words.members(aw, 0), y), Bool.not(_)) : Bool}
      Mg.Ords.diff_contains(Wo.Words.members(aw, 0), bo, y,
        To.Ords.asc_members(aw, la),
        Ords.asc_of_valid_offs(bo, 0, True{}, True{}, vb))
    case S.PDense{bw}:
      Words.diff_members_bit(aw, bw, y, la, inr)

# ---------------------------------------------------------------------------
# And the leaf, whichever pair of shapes it got.
# ---------------------------------------------------------------------------

law PSet.leaf_diff_members_mem:
  for +a: S.PSet
  for +b: S.PSet
  for +y: U32
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(y, 12n) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, S.PSet.leaf_diff_members(a, b), y)
    == Bool.and(S.PSet.mem.leaf(a, y),
         Bool.not(S.PSet.mem.leaf(b, y))) : Bool}

def PSet.leaf_diff_members_mem(a, b, y, va, vb, inr):
  match a:
    case S.PZero{}:
      {==}
    case S.PBranch{l, h}:
      {==}
    case S.PFull{}:
      PSet.leaf_diff_full(b, y, vb, inr)
    case S.PSparse{ao}:
      PSet.leaf_diff_sp(ao, b, y,
        Ords.asc_of_valid_offs(ao, 0, True{}, True{}, va), vb, inr)
    case S.PDense{aw}:
      PSet.leaf_diff_dn(aw, b, y, va, vb, inr)
