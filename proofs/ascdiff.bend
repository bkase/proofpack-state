# proofs/ascdiff.bend -- the sorted difference ascends.
#
# `Ords.diff` walks two ascending lists in step and emits the ordinals of the
# first that the second does not hold. proofs/merge.bend proves it emits
# exactly those. This is the other half a caller needs: what it emits still
# ascends, so it is still a list a merge can consume and still a list whose
# length is a cardinality.
#
# The induction needs one thing beyond `asc`: that the output is a *sublist*
# of the first operand. Without that, the step that keeps a head cannot show
# the head is below everything the recursive call produced. So the statement
# carries both, and both come out of the same walk.

import Base
import ./eq.bend as E
import ./orderlist.bend as Ol
import ./sublist.bend as Sl
import ./subsetalg.bend as Sa
import ./tileorder.bend as To
import ./leafdiff.bend as Ld
import ../core/set.bend as S
import ./tilefit.bend as Tf
import ./interval.bend as It
import ./childtest.bend as Ct
import ./split.bend as Sp
import ../core/count.bend as C
import ../core/ords.bend as O
import ../core/word.bend as W
import ../core/words.bend as Wo

law Ords.lt_all_of_all_in:
  for +l: List<&2, U32>
  for +w: List<&2, U32>
  for +h: U32
  for +la: {Ol.Ords.lt_all(h, w) == True{} : Bool}
  for +ai: {Sa.Ords.all_in(l, w) == True{} : Bool}
  {Ol.Ords.lt_all(h, l) == True{} : Bool}

def Ords.lt_all_of_all_in(l, w, h, la, ai):
  match l:
    case Nil{}:
      {==}
    case Con{y, u}:
      E.Bool.and_both(U32.is_lt(h, y), Ol.Ords.lt_all(h, u),
        Sl.Ords.lt_of_lt_all(w, h, y, la,
          E.Bool.and_l(List.contains(~U32, ~U32.is_eq, w, y),
            Sa.Ords.all_in(u, w), ai)),
        Ords.lt_all_of_all_in(u, w, h, la,
          E.Bool.and_r(List.contains(~U32, ~U32.is_eq, w, y),
            Sa.Ords.all_in(u, w), ai)))

law Ords.asc_diff_go:
  for +fuel: Nat
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +c: Cmp
  for +aa: {Ol.Ords.asc(a) == True{} : Bool}
  {Bool.and(Ol.Ords.asc(O.Ords.diff.go(fuel, a, b, c)),
    Sa.Ords.all_in(O.Ords.diff.go(fuel, a, b, c), a))
    == True{} : Bool}

def Ords.asc_diff_go.keep(+ah: U32, +at: List<&2, U32>,
  +rest: List<&2, U32>,
  +aa: {Ol.Ords.asc(Con{ah, at}) == True{} : Bool},
  +ih: {Bool.and(Ol.Ords.asc(rest), Sa.Ords.all_in(rest, at))
    == True{} : Bool})
  -> {Bool.and(Ol.Ords.asc(Con{ah, rest}),
    Sa.Ords.all_in(Con{ah, rest}, Con{ah, at})) == True{} : Bool}:
  E.Bool.and_both(Ol.Ords.asc(Con{ah, rest}),
    Sa.Ords.all_in(Con{ah, rest}, Con{ah, at}),
    E.Bool.and_both(Ol.Ords.above(ah, rest), Ol.Ords.asc(rest),
      Ol.Ords.above_of_lt_all(rest, ah,
        Ords.lt_all_of_all_in(rest, at, ah,
          Ol.Ords.lt_all_of_asc(at, ah, aa),
          E.Bool.and_r(Ol.Ords.asc(rest), Sa.Ords.all_in(rest, at),
            ih))),
      E.Bool.and_l(Ol.Ords.asc(rest), Sa.Ords.all_in(rest, at), ih)),
    E.Bool.and_both(List.contains(~U32, ~U32.is_eq, Con{ah, at}, ah),
      Sa.Ords.all_in(rest, Con{ah, at}),
      Sa.Ords.or_left(U32.is_eq(ah, ah),
        List.contains(~U32, ~U32.is_eq, at, ah),
        E.U32.is_eq_refl(ah)),
      Sa.Ords.all_in_cons(rest, at, ah,
        E.Bool.and_r(Ol.Ords.asc(rest), Sa.Ords.all_in(rest, at),
          ih))))

def Ords.asc_diff_go.pick(+f: Nat, +ah: U32, +at: List<&2, U32>,
  +bh: U32, +bt: List<&2, U32>, +c: Cmp,
  +aa: {Ol.Ords.asc(Con{ah, at}) == True{} : Bool},
  ihLT: {Bool.and(Ol.Ords.asc(O.Ords.diff.go(f, at, Con{bh, bt},
      O.Ords.head_cmp(at, Con{bh, bt}))),
    Sa.Ords.all_in(O.Ords.diff.go(f, at, Con{bh, bt},
      O.Ords.head_cmp(at, Con{bh, bt})), at)) == True{} : Bool},
  ihGT: {Bool.and(Ol.Ords.asc(O.Ords.diff.go(f, Con{ah, at}, bt,
      O.Ords.head_cmp(Con{ah, at}, bt))),
    Sa.Ords.all_in(O.Ords.diff.go(f, Con{ah, at}, bt,
      O.Ords.head_cmp(Con{ah, at}, bt)), Con{ah, at}))
    == True{} : Bool},
  +ihEQ: {Bool.and(Ol.Ords.asc(O.Ords.diff.go(f, at, bt,
      O.Ords.head_cmp(at, bt))),
    Sa.Ords.all_in(O.Ords.diff.go(f, at, bt,
      O.Ords.head_cmp(at, bt)), at)) == True{} : Bool})
  -> {Bool.and(Ol.Ords.asc(O.Ords.diff.go(1n+f, Con{ah, at},
      Con{bh, bt}, c)),
    Sa.Ords.all_in(O.Ords.diff.go(1n+f, Con{ah, at}, Con{bh, bt}, c),
      Con{ah, at})) == True{} : Bool}:
  match c:
    case LT{}:
      Ords.asc_diff_go.keep(ah, at,
        O.Ords.diff.go(f, at, Con{bh, bt},
          O.Ords.head_cmp(at, Con{bh, bt})), aa, ihLT)
    case GT{}:
      ihGT
    case EQ{}:
      E.Bool.and_both(Ol.Ords.asc(O.Ords.diff.go(f, at, bt,
        O.Ords.head_cmp(at, bt))),
        Sa.Ords.all_in(O.Ords.diff.go(f, at, bt,
          O.Ords.head_cmp(at, bt)), Con{ah, at}),
        E.Bool.and_l(Ol.Ords.asc(O.Ords.diff.go(f, at, bt,
          O.Ords.head_cmp(at, bt))),
          Sa.Ords.all_in(O.Ords.diff.go(f, at, bt,
            O.Ords.head_cmp(at, bt)), at), ihEQ),
        Sa.Ords.all_in_cons(O.Ords.diff.go(f, at, bt,
          O.Ords.head_cmp(at, bt)), at, ah,
          E.Bool.and_r(Ol.Ords.asc(O.Ords.diff.go(f, at, bt,
            O.Ords.head_cmp(at, bt))),
            Sa.Ords.all_in(O.Ords.diff.go(f, at, bt,
              O.Ords.head_cmp(at, bt)), at), ihEQ)))

def Ords.asc_diff_go(fuel, a, b, c, aa):
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
              E.Bool.and_both(Ol.Ords.asc(Con{ah, at}),
                Sa.Ords.all_in(Con{ah, at}, Con{ah, at}), aa,
                Sa.Ords.all_in_self(Con{ah, at}))
            case Con{bh, bt}:
              Ords.asc_diff_go.pick(f, ah, at, bh, bt, c, aa,
                Ords.asc_diff_go(f, at, Con{bh, bt},
                  O.Ords.head_cmp(at, Con{bh, bt}),
                  E.Bool.and_r(Ol.Ords.above(ah, at),
                    Ol.Ords.asc(at), aa)),
                Ords.asc_diff_go(f, Con{ah, at}, bt,
                  O.Ords.head_cmp(Con{ah, at}, bt), aa),
                Ords.asc_diff_go(f, at, bt,
                  O.Ords.head_cmp(at, bt),
                  E.Bool.and_r(Ol.Ords.above(ah, at),
                    Ol.Ords.asc(at), aa)))

law Ords.asc_diff:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +aa: {Ol.Ords.asc(a) == True{} : Bool}
  {Ol.Ords.asc(O.Ords.diff(a, b)) == True{} : Bool}

def Ords.asc_diff(a, b, aa):
  E.Bool.and_l(Ol.Ords.asc(O.Ords.diff(a, b)),
    Sa.Ords.all_in(O.Ords.diff(a, b), a),
    Ords.asc_diff_go(O.Ords.merge_fuel(a, b), a, b,
      O.Ords.head_cmp(a, b), aa))

# ---------------------------------------------------------------------------
# The fused word walk ascends too.
#
# `Words.diff_members.go` is `Words.members.go` with the word it emits taken
# from `U32.diff` instead of straight out of the tile, and with a fall-through
# to the plain walk when the second operand runs out. It builds its answer
# newest-first and reverses once, so what the induction actually maintains is
# that the accumulator descends -- the same shape proofs/tileorder.bend uses,
# and the same step, since which word is being read never mattered to the
# order.
# ---------------------------------------------------------------------------

law Ords.desc_diff_members_go:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +ord: U32
  for +acc: List<&2, U32>
  for +dacc: {Ol.Ords.desc(acc) == True{} : Bool}
  for +gacc: {Ol.Ords.gt_all(ord, acc) == True{} : Bool}
  for +bnd: {C.Nat.upto(Nat.add(U32.to_nat(ord),
    Sp.Nat.dbl(5n, List.length(&2, U32, a))), 4096n)
    == True{} : Bool}
  {Ol.Ords.desc(Wo.Words.diff_members.go(a, b, ord, acc))
    == True{} : Bool}

def Ords.desc_diff_members_go(a, b, ord, acc, dacc, gacc, bnd):
  match a:
    case Nil{}:
      dacc
    case Con{ah, at}:
      match b:
        case Nil{}:
          To.Ords.desc_members_go(Con{ah, at}, ord, acc, dacc, gacc,
            bnd)
        case Con{bh, bt}:
          Ords.desc_diff_members_go(at, bt, (ord + 32 : U32),
            Wo.Words.bits_rev(32n, W.U32.diff(ah, bh), ord, acc),
            To.Ords.desc_bits_rev(32n, W.U32.diff(ah, bh), ord, acc,
              dacc, gacc,
              Tf.Nat.word_room(U32.to_nat(ord),
                List.length(&2, U32, at), bnd)),
            To.Ords.gt_all_bits_rev(32n, (ord + 32 : U32),
              W.U32.diff(ah, bh), ord, acc,
              To.Ords.gt_all_mono(ord, (ord + 32 : U32), acc,
                It.Nat.upto_cast(U32.to_nat(ord), U32.to_nat(ord),
                  Nat.add(U32.to_nat(ord), 32n),
                  U32.to_nat((ord + 32 : U32)), {==},
                  E.Nat.sym(U32.to_nat((ord + 32 : U32)),
                    Nat.add(U32.to_nat(ord), 32n),
                    Tf.U32.add_small(ord, 32, 12n,
                      Tf.U32.fits_of_le(ord, 31n,
                        Tf.Nat.word_room(U32.to_nat(ord),
                          List.length(&2, U32, at), bnd)), {==},
                      {==})),
                  Ct.Nat.le_add_right(U32.to_nat(ord), 32n)),
                gacc),
              It.Nat.upto_cast(Nat.add(U32.to_nat(ord), 32n),
                Nat.add(U32.to_nat(ord), 32n),
                Nat.add(U32.to_nat(ord), 32n),
                U32.to_nat((ord + 32 : U32)), {==},
                E.Nat.sym(U32.to_nat((ord + 32 : U32)),
                  Nat.add(U32.to_nat(ord), 32n),
                  Tf.U32.add_small(ord, 32, 12n,
                    Tf.U32.fits_of_le(ord, 31n,
                      Tf.Nat.word_room(U32.to_nat(ord),
                        List.length(&2, U32, at), bnd)), {==}, {==})),
                It.Nat.upto_refl(Nat.add(U32.to_nat(ord), 32n))),
              Tf.Nat.word_room(U32.to_nat(ord),
                List.length(&2, U32, at), bnd)),
            It.Nat.upto_cast(
              Nat.add(U32.to_nat(ord),
                Sp.Nat.dbl(5n, 1n+List.length(&2, U32, at))),
              Nat.add(U32.to_nat((ord + 32 : U32)),
                Sp.Nat.dbl(5n, List.length(&2, U32, at))), 4096n,
              4096n,
              Tf.Nat.word_step(U32.to_nat(ord),
                List.length(&2, U32, at),
                U32.to_nat((ord + 32 : U32)),
                Tf.U32.add_small(ord, 32, 12n,
                  Tf.U32.fits_of_le(ord, 31n,
                    Tf.Nat.word_room(U32.to_nat(ord),
                      List.length(&2, U32, at), bnd)), {==}, {==})),
              {==}, bnd))

law Ords.asc_diff_members:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +len: {Nat.is_eq(List.length(&2, U32, a), 128n) == True{}
    : Bool}
  {Ol.Ords.asc(Wo.Words.diff_members(a, b, 0)) == True{} : Bool}

def Ords.asc_diff_members(a, b, len):
  Ol.Ords.asc_reverse(Wo.Words.diff_members.go(a, b, 0, Nil{}),
    Ords.desc_diff_members_go(a, b, 0, Nil{}, {==}, {==},
      Tf.Words.tile_room(a, len)))

# ---------------------------------------------------------------------------
# The fused leaf difference ascends.
#
# Twenty-five shape pairs, but only four kinds of answer: nothing, a full
# leaf's count-down, one of the two operands' own enumeration, or a merge.
# Each of those is already known to ascend, and the merge arms are the lemma
# above, so this is a case analysis rather than an argument.
# ---------------------------------------------------------------------------

# The four equations below are what the `PFull` arms of the fused leaf reduce
# to, stated as laws so the arms can rewrite with them rather than leave the
# checker to convert. That is not style: `bend 2.0.32`'s `--verdict` reports a
# TypeScript/kernel mismatch on any implicit conversion whose normal form runs
# past about 850 list cells, and a full leaf is 4096 of them. The rewrite makes
# both sides syntactically equal, so no conversion happens.
# docs/bendtt-verdict-mismatch.md has the reduction and the bug report.

law PSet.lfd_zero_eq:
  {S.PSet.leaf_diff_members.full(S.PZero{})
    == S.PSet.range(4096n, 4095, Nil{}) : List<&2, U32>}

def PSet.lfd_zero_eq():
  {==}

law PSet.lfd_branch_eq:
  for +l: S.PSet
  for +h: S.PSet
  {S.PSet.leaf_diff_members.full(S.PBranch{l, h})
    == S.PSet.range(4096n, 4095, Nil{}) : List<&2, U32>}

def PSet.lfd_branch_eq(l, h):
  {==}

law PSet.lfd_sparse_eq:
  for +bo: List<&2, U32>
  {S.PSet.leaf_diff_members.full(S.PSparse{bo})
    == O.Ords.diff(S.PSet.range(4096n, 4095, Nil{}), bo)
    : List<&2, U32>}

def PSet.lfd_sparse_eq(bo):
  {==}

law PSet.lfd_dense_eq:
  for +bw: List<&2, U32>
  {S.PSet.leaf_diff_members.full(S.PDense{bw})
    == Wo.Words.diff_members(Wo.Words.ones(128n), bw, 0)
    : List<&2, U32>}

def PSet.lfd_dense_eq(bw):
  {==}

def Ords.asc_leaf_diff.full(+b: S.PSet,
  +vb: {S.PSet.valid.leaf(b) == True{} : Bool})
  -> {Ol.Ords.asc(S.PSet.leaf_diff_members.full(b)) == True{} : Bool}:
  match b:
    case S.PZero{}:
      %Equal.sym(List<&2, U32>,
        S.PSet.leaf_diff_members.full(S.PZero{}),
        S.PSet.range(4096n, 4095, Nil{}), PSet.lfd_zero_eq())
        : {Ol.Ords.asc(_) == True{} : Bool}
      To.Ords.asc_full_leaf()
    case S.PFull{}:
      {==}
    case S.PBranch{l, h}:
      %Equal.sym(List<&2, U32>,
        S.PSet.leaf_diff_members.full(S.PBranch{l, h}),
        S.PSet.range(4096n, 4095, Nil{}), PSet.lfd_branch_eq(l, h))
        : {Ol.Ords.asc(_) == True{} : Bool}
      To.Ords.asc_full_leaf()
    case S.PSparse{bo}:
      %Equal.sym(List<&2, U32>,
        S.PSet.leaf_diff_members.full(S.PSparse{bo}),
        O.Ords.diff(S.PSet.range(4096n, 4095, Nil{}), bo),
        PSet.lfd_sparse_eq(bo))
        : {Ol.Ords.asc(_) == True{} : Bool}
      Ords.asc_diff(S.PSet.range(4096n, 4095, Nil{}), bo,
        To.Ords.asc_full_leaf())
    case S.PDense{bw}:
      %Equal.sym(List<&2, U32>,
        S.PSet.leaf_diff_members.full(S.PDense{bw}),
        Wo.Words.diff_members(Wo.Words.ones(128n), bw, 0),
        PSet.lfd_dense_eq(bw))
        : {Ol.Ords.asc(_) == True{} : Bool}
      Ords.asc_diff_members(Wo.Words.ones(128n), bw, {==})

def Ords.asc_leaf_diff.sp(+ao: List<&2, U32>, +b: S.PSet,
  +va: {Ol.Ords.asc(ao) == True{} : Bool},
  +vb: {S.PSet.valid.leaf(b) == True{} : Bool})
  -> {Ol.Ords.asc(S.PSet.leaf_diff_members.sp(ao, b)) == True{}
    : Bool}:
  match b:
    case S.PZero{}:
      va
    case S.PFull{}:
      {==}
    case S.PBranch{l, h}:
      va
    case S.PSparse{bo}:
      Ords.asc_diff(ao, bo, va)
    case S.PDense{bw}:
      Ords.asc_diff(ao, Wo.Words.members(bw, 0), va)

def Ords.asc_leaf_diff.dn(+aw: List<&2, U32>, +b: S.PSet,
  +va: {Nat.is_eq(List.length(&2, U32, aw), 128n) == True{} : Bool},
  +vb: {S.PSet.valid.leaf(b) == True{} : Bool})
  -> {Ol.Ords.asc(S.PSet.leaf_diff_members.dn(aw, b)) == True{}
    : Bool}:
  match b:
    case S.PZero{}:
      To.Ords.asc_members(aw, va)
    case S.PFull{}:
      {==}
    case S.PBranch{l, h}:
      To.Ords.asc_members(aw, va)
    case S.PSparse{bo}:
      Ords.asc_diff(Wo.Words.members(aw, 0), bo,
        To.Ords.asc_members(aw, va))
    case S.PDense{bw}:
      Ords.asc_diff_members(aw, bw, va)

law Ords.asc_leaf_diff_members:
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  {Ol.Ords.asc(S.PSet.leaf_diff_members(a, b)) == True{} : Bool}

def Ords.asc_leaf_diff_members(a, b, va, vb):
  match a:
    case S.PZero{}:
      {==}
    case S.PBranch{l, h}:
      {==}
    case S.PFull{}:
      Ords.asc_leaf_diff.full(b, vb)
    case S.PSparse{ao}:
      Ords.asc_leaf_diff.sp(ao, b,
        Ld.Ords.asc_of_valid_offs(ao, 0, True{}, True{}, va), vb)
    case S.PDense{aw}:
      Ords.asc_leaf_diff.dn(aw, b, va, vb)
