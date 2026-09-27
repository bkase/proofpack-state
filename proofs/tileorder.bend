# proofs/tileorder.bend -- the tile walk emits ordinals in order.
#
# `Words.members` walks a tile low bit to high, prepending an ordinal for
# each bit set, and reverses at the end. So what the walk builds directly is
# descending -- each ordinal it prepends is above everything already there --
# and the reverse of that is the ascending list the merge-based set
# operations need.
#
# The bound that keeps the ordinals in range is the same one proofs/tilefit
# uses: a tile is 128 words of thirty-two ordinals, so nothing the walk emits
# reaches 4096, and each step's `ord + 1` and `ord + 32` do not carry.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./split.bend as Sp
import ./interval.bend as It
import ./nodeenum.bend as Ne
import ./childtest.bend as Ct
import ./tilefit.bend as Tf
import ./orderlist.bend as Ol
import ./leaf.bend as Lf
import ./adder.bend as Ad
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo

# ---------------------------------------------------------------------------
# Raising the bound on a list.
# ---------------------------------------------------------------------------

law Ords.gt_all_mono:
  for +e: U32
  for +e2: U32
  for +xs: List<&2, U32>
  for +le: {C.Nat.upto(U32.to_nat(e), U32.to_nat(e2)) == True{}
    : Bool}
  for +gt: {Ol.Ords.gt_all(e, xs) == True{} : Bool}
  {Ol.Ords.gt_all(e2, xs) == True{} : Bool}

law Ords.lt_to_nat:
  for +x: U32
  for +y: U32
  for +lt: {U32.is_lt(x, y) == True{} : Bool}
  {C.Nat.gt(U32.to_nat(y), U32.to_nat(x)) == True{} : Bool}

def Ords.lt_to_nat(x, y, lt):
  %Ol.U32.is_lt_nat(x, y)
    : {_ == True{} : Bool}
  lt

# ---------------------------------------------------------------------------
# One ordinal, prepended or not.
# ---------------------------------------------------------------------------

def Ords.gt_all_mono(e, e2, xs, le, gt):
  match xs:
    case Nil{}:
      {==}
    case Con{y, t}:
      E.Bool.and_both(U32.is_lt(y, e2), Ol.Ords.gt_all(e2, t),
        Ol.U32.lt_of_nat(y, e2,
          Ct.Nat.gt_up(U32.to_nat(e), U32.to_nat(e2), U32.to_nat(y),
            le,
            Ords.lt_to_nat(y, e,
              E.Bool.and_l(U32.is_lt(y, e), Ol.Ords.gt_all(e, t),
                gt)))),
        Ords.gt_all_mono(e, e2, t, le,
          E.Bool.and_r(U32.is_lt(y, e), Ol.Ords.gt_all(e, t), gt)))

law Ords.desc_cons_if:
  for +b: Bool
  for +ord: U32
  for +acc: List<&2, U32>
  for +dacc: {Ol.Ords.desc(acc) == True{} : Bool}
  for +gacc: {Ol.Ords.gt_all(ord, acc) == True{} : Bool}
  {Ol.Ords.desc(Wo.Words.cons_if(b, ord, acc)) == True{} : Bool}

def Ords.desc_cons_if(b, ord, acc, dacc, gacc):
  match b:
    case False{}:
      dacc
    case True{}:
      E.Bool.and_both(Ol.Ords.gt_all(ord, acc), Ol.Ords.desc(acc),
        gacc, dacc)

law Ords.gt_all_cons_if:
  for +e: U32
  for +b: Bool
  for +ord: U32
  for +acc: List<&2, U32>
  for +lt: {U32.is_lt(ord, e) == True{} : Bool}
  for +gacc: {Ol.Ords.gt_all(e, acc) == True{} : Bool}
  {Ol.Ords.gt_all(e, Wo.Words.cons_if(b, ord, acc)) == True{} : Bool}

def Ords.gt_all_cons_if(e, b, ord, acc, lt, gacc):
  match b:
    case False{}:
      gacc
    case True{}:
      E.Bool.and_both(U32.is_lt(ord, e), Ol.Ords.gt_all(e, acc), lt,
        gacc)

# ---------------------------------------------------------------------------
# One word: thirty-two ordinals, each above the last.
# ---------------------------------------------------------------------------

law Ords.gt_all_bits_rev:
  for +k: Nat
  for +e: U32
  for +w: U32
  for +ord: U32
  for +acc: List<&2, U32>
  for +gacc: {Ol.Ords.gt_all(e, acc) == True{} : Bool}
  for +room: {C.Nat.upto(Nat.add(U32.to_nat(ord), k), U32.to_nat(e))
    == True{} : Bool}
  for +bnd: {C.Nat.upto(Nat.add(U32.to_nat(ord), k), 4096n)
    == True{} : Bool}
  {Ol.Ords.gt_all(e, Wo.Words.bits_rev(k, w, ord, acc)) == True{}
    : Bool}

def Ords.gt_all_bits_rev(k, e, w, ord, acc, gacc, room, bnd):
  match k:
    case 0n:
      gacc
    case 1n+j:
      Ords.gt_all_bits_rev(j, e, U32.shr(w), (ord + 1 : U32),
        Wo.Words.cons_if(Wo.Nat.is_one(W.U32.low(w)), ord, acc),
        Ords.gt_all_cons_if(e, Wo.Nat.is_one(W.U32.low(w)), ord, acc,
          Ol.U32.lt_of_nat(ord, e,
            Ct.Nat.gt_up(1n+U32.to_nat(ord), U32.to_nat(e),
              U32.to_nat(ord),
              Ct.Nat.le_trans(1n+U32.to_nat(ord),
                1n+Nat.add(U32.to_nat(ord), j), U32.to_nat(e),
                Ct.Nat.le_add_right(U32.to_nat(ord), j),
                It.Nat.upto_cast(Nat.add(U32.to_nat(ord), 1n+j),
                  1n+Nat.add(U32.to_nat(ord), j), U32.to_nat(e),
                  U32.to_nat(e), N.Nat.add_succ(U32.to_nat(ord), j),
                  {==}, room)),
              Ne.Nat.gt_succ_of_le(U32.to_nat(ord),
                U32.to_nat(ord), It.Nat.upto_refl(U32.to_nat(ord))))),
          gacc),
        It.Nat.upto_cast(Nat.add(U32.to_nat(ord), 1n+j),
          Nat.add(U32.to_nat((ord + 1 : U32)), j), U32.to_nat(e),
          U32.to_nat(e),
          Tf.Nat.step_bound(U32.to_nat(ord), j,
            U32.to_nat((ord + 1 : U32)),
            Tf.U32.add_small(ord, 1, 12n,
              Tf.U32.fits_of_le(ord, j, bnd), {==}, {==})),
          {==}, room),
        It.Nat.upto_cast(Nat.add(U32.to_nat(ord), 1n+j),
          Nat.add(U32.to_nat((ord + 1 : U32)), j), 4096n, 4096n,
          Tf.Nat.step_bound(U32.to_nat(ord), j,
            U32.to_nat((ord + 1 : U32)),
            Tf.U32.add_small(ord, 1, 12n,
              Tf.U32.fits_of_le(ord, j, bnd), {==}, {==})),
          {==}, bnd))

law Ords.desc_bits_rev:
  for +k: Nat
  for +w: U32
  for +ord: U32
  for +acc: List<&2, U32>
  for +dacc: {Ol.Ords.desc(acc) == True{} : Bool}
  for +gacc: {Ol.Ords.gt_all(ord, acc) == True{} : Bool}
  for +bnd: {C.Nat.upto(Nat.add(U32.to_nat(ord), k), 4096n)
    == True{} : Bool}
  {Ol.Ords.desc(Wo.Words.bits_rev(k, w, ord, acc)) == True{} : Bool}

law Ords.lt_succ:
  for +ord: U32
  for +j: Nat
  for +bnd: {C.Nat.upto(Nat.add(U32.to_nat(ord), 1n+j), 4096n)
    == True{} : Bool}
  {U32.is_lt(ord, (ord + 1 : U32)) == True{} : Bool}

def Ords.lt_succ(ord, j, bnd):
  Ol.U32.lt_of_nat(ord, (ord + 1 : U32),
    It.Nat.gt_cast(Nat.add(U32.to_nat(ord), 1n),
      U32.to_nat((ord + 1 : U32)), U32.to_nat(ord), U32.to_nat(ord),
      E.Nat.sym(U32.to_nat((ord + 1 : U32)),
        Nat.add(U32.to_nat(ord), 1n),
        Tf.U32.add_small(ord, 1, 12n, Tf.U32.fits_of_le(ord, j, bnd),
          {==}, {==})), {==},
      It.Nat.gt_cast(1n+U32.to_nat(ord),
        Nat.add(U32.to_nat(ord), 1n), U32.to_nat(ord),
        U32.to_nat(ord),
        E.Nat.sym(Nat.add(U32.to_nat(ord), 1n), 1n+U32.to_nat(ord),
          Ad.Nat.add_one(U32.to_nat(ord))), {==},
        Ne.Nat.gt_succ_of_le(U32.to_nat(ord), U32.to_nat(ord),
          It.Nat.upto_refl(U32.to_nat(ord))))))

def Ords.desc_bits_rev(k, w, ord, acc, dacc, gacc, bnd):
  match k:
    case 0n:
      dacc
    case 1n+j:
      Ords.desc_bits_rev(j, U32.shr(w), (ord + 1 : U32),
        Wo.Words.cons_if(Wo.Nat.is_one(W.U32.low(w)), ord, acc),
        Ords.desc_cons_if(Wo.Nat.is_one(W.U32.low(w)), ord, acc, dacc,
          gacc),
        Ords.gt_all_cons_if((ord + 1 : U32),
          Wo.Nat.is_one(W.U32.low(w)), ord, acc,
          Ords.lt_succ(ord, j, bnd),
          Ords.gt_all_mono(ord, (ord + 1 : U32), acc,
            It.Nat.upto_cast(U32.to_nat(ord), U32.to_nat(ord),
              Nat.add(U32.to_nat(ord), 1n),
              U32.to_nat((ord + 1 : U32)), {==},
              E.Nat.sym(U32.to_nat((ord + 1 : U32)),
                Nat.add(U32.to_nat(ord), 1n),
                Tf.U32.add_small(ord, 1, 12n,
                  Tf.U32.fits_of_le(ord, j, bnd), {==}, {==})),
              Ct.Nat.le_add_right(U32.to_nat(ord), 1n)),
            gacc)),
        It.Nat.upto_cast(Nat.add(U32.to_nat(ord), 1n+j),
          Nat.add(U32.to_nat((ord + 1 : U32)), j), 4096n, 4096n,
          Tf.Nat.step_bound(U32.to_nat(ord), j,
            U32.to_nat((ord + 1 : U32)),
            Tf.U32.add_small(ord, 1, 12n,
              Tf.U32.fits_of_le(ord, j, bnd), {==}, {==})),
          {==}, bnd))

# ---------------------------------------------------------------------------
# The whole tile, and then turned around.
# ---------------------------------------------------------------------------

law Nat.word_span_le:
  for +x: Nat
  for +m: Nat
  {C.Nat.upto(Nat.add(x, 32n), Nat.add(x, Sp.Nat.dbl(5n, 1n+m)))
    == True{} : Bool}

def Nat.word_span_le(x, m):
  %E.Nat.sym(Nat.add(x, Sp.Nat.dbl(5n, 1n+m)),
    Nat.add(Nat.add(x, 32n), Sp.Nat.dbl(5n, m)),
    Tf.Nat.word_step(x, m, Nat.add(x, 32n), {==}))
    : {C.Nat.upto(Nat.add(x, 32n), _) == True{} : Bool}
  Ct.Nat.le_add_right(Nat.add(x, 32n), Sp.Nat.dbl(5n, m))

law Ords.gt_all_members_go:
  for +ws: List<&2, U32>
  for +e: U32
  for +ord: U32
  for +acc: List<&2, U32>
  for +gacc: {Ol.Ords.gt_all(e, acc) == True{} : Bool}
  for +room: {C.Nat.upto(Nat.add(U32.to_nat(ord),
    Sp.Nat.dbl(5n, List.length(&2, U32, ws))), U32.to_nat(e))
    == True{} : Bool}
  for +bnd: {C.Nat.upto(Nat.add(U32.to_nat(ord),
    Sp.Nat.dbl(5n, List.length(&2, U32, ws))), 4096n)
    == True{} : Bool}
  {Ol.Ords.gt_all(e, Wo.Words.members.go(ws, ord, acc)) == True{}
    : Bool}

def Ords.gt_all_members_go(ws, e, ord, acc, gacc, room, bnd):
  match ws:
    case Nil{}:
      gacc
    case Con{w, t}:
      Ords.gt_all_members_go(t, e, (ord + 32 : U32),
        Wo.Words.bits_rev(32n, w, ord, acc),
        Ords.gt_all_bits_rev(32n, e, w, ord, acc, gacc,
          Ct.Nat.le_trans(Nat.add(U32.to_nat(ord), 32n),
            Nat.add(U32.to_nat(ord),
              Sp.Nat.dbl(5n, 1n+List.length(&2, U32, t))),
            U32.to_nat(e),
            Nat.word_span_le(U32.to_nat(ord),
              List.length(&2, U32, t)), room),
          Tf.Nat.word_room(U32.to_nat(ord),
            List.length(&2, U32, t), bnd)),
        It.Nat.upto_cast(
          Nat.add(U32.to_nat(ord),
            Sp.Nat.dbl(5n, 1n+List.length(&2, U32, t))),
          Nat.add(U32.to_nat((ord + 32 : U32)),
            Sp.Nat.dbl(5n, List.length(&2, U32, t))), U32.to_nat(e),
          U32.to_nat(e),
          Tf.Nat.word_step(U32.to_nat(ord), List.length(&2, U32, t),
            U32.to_nat((ord + 32 : U32)),
            Tf.U32.add_small(ord, 32, 12n,
              Tf.U32.fits_of_le(ord, 31n,
                Tf.Nat.word_room(U32.to_nat(ord),
                  List.length(&2, U32, t), bnd)), {==}, {==})),
          {==}, room),
        It.Nat.upto_cast(
          Nat.add(U32.to_nat(ord),
            Sp.Nat.dbl(5n, 1n+List.length(&2, U32, t))),
          Nat.add(U32.to_nat((ord + 32 : U32)),
            Sp.Nat.dbl(5n, List.length(&2, U32, t))), 4096n, 4096n,
          Tf.Nat.word_step(U32.to_nat(ord), List.length(&2, U32, t),
            U32.to_nat((ord + 32 : U32)),
            Tf.U32.add_small(ord, 32, 12n,
              Tf.U32.fits_of_le(ord, 31n,
                Tf.Nat.word_room(U32.to_nat(ord),
                  List.length(&2, U32, t), bnd)), {==}, {==})),
          {==}, bnd))

law Ords.desc_members_go:
  for +ws: List<&2, U32>
  for +ord: U32
  for +acc: List<&2, U32>
  for +dacc: {Ol.Ords.desc(acc) == True{} : Bool}
  for +gacc: {Ol.Ords.gt_all(ord, acc) == True{} : Bool}
  for +bnd: {C.Nat.upto(Nat.add(U32.to_nat(ord),
    Sp.Nat.dbl(5n, List.length(&2, U32, ws))), 4096n)
    == True{} : Bool}
  {Ol.Ords.desc(Wo.Words.members.go(ws, ord, acc)) == True{} : Bool}

def Ords.desc_members_go(ws, ord, acc, dacc, gacc, bnd):
  match ws:
    case Nil{}:
      dacc
    case Con{w, t}:
      Ords.desc_members_go(t, (ord + 32 : U32),
        Wo.Words.bits_rev(32n, w, ord, acc),
        Ords.desc_bits_rev(32n, w, ord, acc, dacc, gacc,
          Tf.Nat.word_room(U32.to_nat(ord),
            List.length(&2, U32, t), bnd)),
        Ords.gt_all_bits_rev(32n, (ord + 32 : U32), w, ord, acc,
          Ords.gt_all_mono(ord, (ord + 32 : U32), acc,
            It.Nat.upto_cast(U32.to_nat(ord), U32.to_nat(ord),
              Nat.add(U32.to_nat(ord), 32n),
              U32.to_nat((ord + 32 : U32)), {==},
              E.Nat.sym(U32.to_nat((ord + 32 : U32)),
                Nat.add(U32.to_nat(ord), 32n),
                Tf.U32.add_small(ord, 32, 12n,
                  Tf.U32.fits_of_le(ord, 31n,
                    Tf.Nat.word_room(U32.to_nat(ord),
                      List.length(&2, U32, t), bnd)), {==}, {==})),
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
                    List.length(&2, U32, t), bnd)), {==}, {==})),
            It.Nat.upto_refl(Nat.add(U32.to_nat(ord), 32n))),
          Tf.Nat.word_room(U32.to_nat(ord),
            List.length(&2, U32, t), bnd)),
        It.Nat.upto_cast(
          Nat.add(U32.to_nat(ord),
            Sp.Nat.dbl(5n, 1n+List.length(&2, U32, t))),
          Nat.add(U32.to_nat((ord + 32 : U32)),
            Sp.Nat.dbl(5n, List.length(&2, U32, t))), 4096n, 4096n,
          Tf.Nat.word_step(U32.to_nat(ord), List.length(&2, U32, t),
            U32.to_nat((ord + 32 : U32)),
            Tf.U32.add_small(ord, 32, 12n,
              Tf.U32.fits_of_le(ord, 31n,
                Tf.Nat.word_room(U32.to_nat(ord),
                  List.length(&2, U32, t), bnd)), {==}, {==})),
          {==}, bnd))

law Ords.asc_members:
  for +ws: List<&2, U32>
  for +len: {Nat.is_eq(List.length(&2, U32, ws), 128n) == True{}
    : Bool}
  {Ol.Ords.asc(Wo.Words.members(ws, 0)) == True{} : Bool}

def Ords.asc_members(ws, len):
  Ol.Ords.asc_reverse(Wo.Words.members.go(ws, 0, Nil{}),
    Ords.desc_members_go(ws, 0, Nil{}, {==}, {==},
      Tf.Words.tile_room(ws, len)))
