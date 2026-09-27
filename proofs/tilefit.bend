# proofs/tilefit.bend -- the tile walk stays inside the leaf.
#
# A dense leaf holds 128 words and reads them as 4096 ordinals: thirty-two
# per word, counting up from the tile's base. The enumeration needs that none
# of those ordinals leaves the twelve bits a leaf covers, which is a bound on
# the walk rather than on any one word -- so it is proved as an invariant:
# whatever is already accumulated fits, and there is room left for the words
# not yet walked.
#
# The walk adds with `U32` addition, so each step needs to know the addition
# did not carry out of the word. That comes from the bound too: both operands
# are far below the top, so no carry can reach it.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./adder.bend as Ad
import ./split.bend as Sp
import ./split_add.bend as Sa
import ./sum.bend as Sm
import ./shift.bend as Sf
import ./interval.bend as It
import ./nodeenum.bend as Ne
import ./childtest.bend as Ct
import ./halves.bend as Hv
import ./leaf.bend as Lf
import ./decr.bend as De
import ../core/set.bend as S
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo

# ---------------------------------------------------------------------------
# Small operands do not carry out.
# ---------------------------------------------------------------------------

law Word.no_carry_zeros.step:
  for +p: Nat
  for +ab: Bool
  for +bb: Bool
  for +c: Bool
  for +at: Word(p)
  for +bt: Word(p)
  for +ha: {Dc.Word.hi_zero(1n+p, WCon{ab, at}, 0n) == True{} : Bool}
  for +hb: {Dc.Word.hi_zero(1n+p, WCon{bb, bt}, 0n) == True{} : Bool}
  for +ih: {Ad.Word.carry(p, at, bt, False{}, False{}) == False{}
    : Bool}
  {Ad.Word.carry(1n+p, WCon{ab, at}, WCon{bb, bt}, False{}, c)
    == False{} : Bool}

def Word.no_carry_zeros.step(p, ab, bb, c, at, bt, ha, hb, ih):
  match ab bb c:
    case False{} False{} False{}:
      ih
    case False{} False{} True{}:
      ih
    case False{} True{} False{}:
      E.Bool.noconf({Ad.Word.carry(1n+p, WCon{False{}, at},
        WCon{True{}, bt}, False{}, False{}) == False{} : Bool}, hb)
    case False{} True{} True{}:
      E.Bool.noconf({Ad.Word.carry(1n+p, WCon{False{}, at},
        WCon{True{}, bt}, False{}, True{}) == False{} : Bool}, hb)
    case True{} False{} False{}:
      E.Bool.noconf({Ad.Word.carry(1n+p, WCon{True{}, at},
        WCon{False{}, bt}, False{}, False{}) == False{} : Bool}, ha)
    case True{} False{} True{}:
      E.Bool.noconf({Ad.Word.carry(1n+p, WCon{True{}, at},
        WCon{False{}, bt}, False{}, True{}) == False{} : Bool}, ha)
    case True{} True{} False{}:
      E.Bool.noconf({Ad.Word.carry(1n+p, WCon{True{}, at},
        WCon{True{}, bt}, False{}, False{}) == False{} : Bool}, ha)
    case True{} True{} True{}:
      E.Bool.noconf({Ad.Word.carry(1n+p, WCon{True{}, at},
        WCon{True{}, bt}, False{}, True{}) == False{} : Bool}, ha)

law Word.zero_carry_false:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +ha: {Dc.Word.hi_zero(n, a, 0n) == True{} : Bool}
  for +hb: {Dc.Word.hi_zero(n, b, 0n) == True{} : Bool}
  {Ad.Word.carry(n, a, b, False{}, False{}) == False{} : Bool}

def Word.zero_carry_false(n, a, b, ha, hb):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          Word.no_carry_zeros.step(p, ab, bb, False{}, at, bt, ha, hb,
            Word.zero_carry_false(p, at, bt,
              E.Bool.and_r(Bool.not(ab), Dc.Word.hi_zero(p, at, 0n),
                ha),
              E.Bool.and_r(Bool.not(bb), Dc.Word.hi_zero(p, bt, 0n),
                hb)))

law Word.no_carry_zeros:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  for +ha: {Dc.Word.hi_zero(n, a, 0n) == True{} : Bool}
  for +hb: {Dc.Word.hi_zero(n, b, 0n) == True{} : Bool}
  for +pos: {C.Nat.gt(n, 0n) == True{} : Bool}
  {Ad.Word.carry(n, a, b, False{}, c) == False{} : Bool}

def Word.no_carry_zeros(n, a, b, c, ha, hb, pos):
  match n:
    case 0n:
      E.Bool.noconf({Ad.Word.carry(0n, a, b, False{}, c) == False{}
        : Bool}, pos)
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          Word.no_carry_zeros.step(p, ab, bb, c, at, bt, ha, hb,
            Word.zero_carry_false(p, at, bt,
              E.Bool.and_r(Bool.not(ab), Dc.Word.hi_zero(p, at, 0n),
                ha),
              E.Bool.and_r(Bool.not(bb), Dc.Word.hi_zero(p, bt, 0n),
                hb)))

law Word.no_carry_small:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +k: Nat
  for +c: Bool
  for +ha: {Dc.Word.hi_zero(n, a, k) == True{} : Bool}
  for +hb: {Dc.Word.hi_zero(n, b, k) == True{} : Bool}
  for +lt: {C.Nat.gt(n, k) == True{} : Bool}
  {Ad.Word.carry(n, a, b, False{}, c) == False{} : Bool}

def Word.no_carry_small(n, a, b, k, c, ha, hb, lt):
  match n:
    case 0n:
      E.Bool.noconf({Ad.Word.carry(0n, a, b, False{}, c) == False{}
        : Bool}, lt)
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          match k:
            case 0n:
              Word.no_carry_zeros(1n+p, WCon{ab, at}, WCon{bb, bt}, c,
                ha, hb, {==})
            case 1n+j:
              Word.no_carry_small(p, at, bt, j,
                Ad.Bool.snd2(Bool.full_add(ab, bb, c)), ha, hb, lt)

law U32.add_small:
  for +a: U32
  for +b: U32
  for +k: Nat
  for +ha: {Dc.U32.hi_zero(a, k) == True{} : Bool}
  for +hb: {Dc.U32.hi_zero(b, k) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, k) == True{} : Bool}
  {U32.to_nat((a + b : U32))
    == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}

def U32.add_small(a, b, k, ha, hb, lt):
  Sm.U32.add_of_no_carry(a, b,
    Word.no_carry_small(32n, W.U32.word(a), W.U32.word(b), k, False{},
      ha, hb, lt))

# ---------------------------------------------------------------------------
# Fitting, from a numeric bound and back.
# ---------------------------------------------------------------------------

law U32.fits_of_le:
  for +x: U32
  for +m: Nat
  for +le: {C.Nat.upto(Nat.add(U32.to_nat(x), 1n+m), 4096n)
    == True{} : Bool}
  {Dc.U32.hi_zero(x, 12n) == True{} : Bool}

def U32.fits_of_le(x, m, le):
  match x:
    case U32{xw}:
      Dc.Word.to_nat_fits(32n, 12n, xw,
        Ct.Nat.gt_up(1n+Nat.add(Word.to_nat(32n, xw), m), 4096n,
          Word.to_nat(32n, xw),
          It.Nat.upto_cast(Nat.add(Word.to_nat(32n, xw), 1n+m),
            1n+Nat.add(Word.to_nat(32n, xw), m), 4096n, 4096n,
            N.Nat.add_succ(Word.to_nat(32n, xw), m), {==}, le),
          Ct.Nat.gt_up(1n+Word.to_nat(32n, xw),
            1n+Nat.add(Word.to_nat(32n, xw), m),
            Word.to_nat(32n, xw),
            Ct.Nat.le_add_right(Word.to_nat(32n, xw), m),
            Ne.Nat.gt_succ_of_le(Word.to_nat(32n, xw),
              Word.to_nat(32n, xw),
              It.Nat.upto_refl(Word.to_nat(32n, xw))))))

# ---------------------------------------------------------------------------
# One word: thirty-two ordinals counting up.
# ---------------------------------------------------------------------------

law Words.cons_if_fit:
  for +b: Bool
  for +ord: U32
  for +acc: List<&2, U32>
  for +h: {Dc.U32.hi_zero(ord, 12n) == True{} : Bool}
  for +facc: {Sf.Ords.all_fit(acc, 12n) == True{} : Bool}
  {Sf.Ords.all_fit(Wo.Words.cons_if(b, ord, acc), 12n) == True{}
    : Bool}

def Words.cons_if_fit(b, ord, acc, h, facc):
  match b:
    case False{}:
      facc
    case True{}:
      E.Bool.and_both(Dc.U32.hi_zero(ord, 12n),
        Sf.Ords.all_fit(acc, 12n), h, facc)

law Nat.step_bound:
  for +a: Nat
  for +j: Nat
  for +b: Nat
  for +eb: {b == Nat.add(a, 1n) : Nat}
  {Nat.add(a, 1n+j) == Nat.add(b, j) : Nat}

def Nat.step_bound(a, j, b, eb):
  %E.Nat.sym(b, Nat.add(a, 1n), eb)
    : {Nat.add(a, 1n+j) == Nat.add(_, j) : Nat}
  %E.Nat.sym(Nat.add(a, 1n), 1n+a, Ad.Nat.add_one(a))
    : {Nat.add(a, 1n+j) == Nat.add(_, j) : Nat}
  N.Nat.add_succ(a, j)

law Words.bits_rev_fit:
  for +k: Nat
  for +w: U32
  for +ord: U32
  for +acc: List<&2, U32>
  for +facc: {Sf.Ords.all_fit(acc, 12n) == True{} : Bool}
  for +bnd: {C.Nat.upto(Nat.add(U32.to_nat(ord), k), 4096n)
    == True{} : Bool}
  {Sf.Ords.all_fit(Wo.Words.bits_rev(k, w, ord, acc), 12n) == True{}
    : Bool}

def Words.bits_rev_fit(k, w, ord, acc, facc, bnd):
  match k:
    case 0n:
      facc
    case 1n+j:
      Words.bits_rev_fit(j, U32.shr(w), (ord + 1 : U32),
        Wo.Words.cons_if(Wo.Nat.is_one(W.U32.low(w)), ord, acc),
        Words.cons_if_fit(Wo.Nat.is_one(W.U32.low(w)), ord, acc,
          U32.fits_of_le(ord, j, bnd), facc),
        It.Nat.upto_cast(Nat.add(U32.to_nat(ord), 1n+j),
          Nat.add(U32.to_nat((ord + 1 : U32)), j), 4096n, 4096n,
          Nat.step_bound(U32.to_nat(ord), j,
            U32.to_nat((ord + 1 : U32)),
            U32.add_small(ord, 1, 12n, U32.fits_of_le(ord, j, bnd),
              {==}, {==})),
          {==}, bnd))

# ---------------------------------------------------------------------------
# The whole tile: one word at a time, thirty-two ordinals each.
# ---------------------------------------------------------------------------

law Nat.word_step:
  for +a: Nat
  for +m: Nat
  for +b: Nat
  for +eb: {b == Nat.add(a, 32n) : Nat}
  {Nat.add(a, Sp.Nat.dbl(5n, 1n+m)) == Nat.add(b, Sp.Nat.dbl(5n, m))
    : Nat}

def Nat.word_step(a, m, b, eb):
  %E.Nat.sym(b, Nat.add(a, 32n), eb)
    : {Nat.add(a, Sp.Nat.dbl(5n, 1n+m))
      == Nat.add(_, Sp.Nat.dbl(5n, m)) : Nat}
  %It.Nat.dbl_succ(5n, m)
    : {Nat.add(a, _) == Nat.add(Nat.add(a, 32n), Sp.Nat.dbl(5n, m))
      : Nat}
  E.Nat.sym(Nat.add(Nat.add(a, 32n), Sp.Nat.dbl(5n, m)),
    Nat.add(a, Nat.add(32n, Sp.Nat.dbl(5n, m))),
    N.Nat.add_assoc(a, 32n, Sp.Nat.dbl(5n, m)))

law Nat.word_room:
  for +a: Nat
  for +m: Nat
  for +bnd: {C.Nat.upto(Nat.add(a, Sp.Nat.dbl(5n, 1n+m)), 4096n)
    == True{} : Bool}
  {C.Nat.upto(Nat.add(a, 32n), 4096n) == True{} : Bool}

def Nat.word_room(a, m, bnd):
  Ct.Nat.le_trans(Nat.add(a, 32n),
    Nat.add(a, Sp.Nat.dbl(5n, 1n+m)), 4096n,
    It.Nat.upto_cast(Nat.add(a, 32n), Nat.add(a, 32n),
      Nat.add(Nat.add(a, 32n), Sp.Nat.dbl(5n, m)),
      Nat.add(a, Sp.Nat.dbl(5n, 1n+m)), {==},
      E.Nat.sym(Nat.add(a, Sp.Nat.dbl(5n, 1n+m)),
        Nat.add(Nat.add(a, 32n), Sp.Nat.dbl(5n, m)),
        Nat.word_step(a, m, Nat.add(a, 32n), {==})),
      Ct.Nat.le_add_right(Nat.add(a, 32n), Sp.Nat.dbl(5n, m))),
    bnd)

law Words.members_go_fit:
  for +ws: List<&2, U32>
  for +ord: U32
  for +acc: List<&2, U32>
  for +facc: {Sf.Ords.all_fit(acc, 12n) == True{} : Bool}
  for +bnd: {C.Nat.upto(Nat.add(U32.to_nat(ord),
    Sp.Nat.dbl(5n, List.length(&2, U32, ws))), 4096n)
    == True{} : Bool}
  {Sf.Ords.all_fit(Wo.Words.members.go(ws, ord, acc), 12n) == True{}
    : Bool}

def Words.members_go_fit(ws, ord, acc, facc, bnd):
  match ws:
    case Nil{}:
      facc
    case Con{w, t}:
      Words.members_go_fit(t, (ord + 32 : U32),
        Wo.Words.bits_rev(32n, w, ord, acc),
        Words.bits_rev_fit(32n, w, ord, acc, facc,
          Nat.word_room(U32.to_nat(ord),
            List.length(&2, U32, t), bnd)),
        It.Nat.upto_cast(
          Nat.add(U32.to_nat(ord),
            Sp.Nat.dbl(5n, 1n+List.length(&2, U32, t))),
          Nat.add(U32.to_nat((ord + 32 : U32)),
            Sp.Nat.dbl(5n, List.length(&2, U32, t))), 4096n, 4096n,
          Nat.word_step(U32.to_nat(ord), List.length(&2, U32, t),
            U32.to_nat((ord + 32 : U32)),
            U32.add_small(ord, 32, 12n,
              U32.fits_of_le(ord, 31n,
                Nat.word_room(U32.to_nat(ord),
                  List.length(&2, U32, t), bnd)),
              {==}, {==})),
          {==}, bnd))

law Ords.all_fit_reverse_go:
  for +l: List<&2, U32>
  for +acc: List<&2, U32>
  for +fl: {Sf.Ords.all_fit(l, 12n) == True{} : Bool}
  for +facc: {Sf.Ords.all_fit(acc, 12n) == True{} : Bool}
  {Sf.Ords.all_fit(List.reverse.go(&2, U32, l, acc), 12n) == True{}
    : Bool}

def Ords.all_fit_reverse_go(l, acc, fl, facc):
  match l:
    case Nil{}:
      facc
    case Con{h, t}:
      Ords.all_fit_reverse_go(t, Con{h, acc},
        E.Bool.and_r(Dc.U32.hi_zero(h, 12n),
          Sf.Ords.all_fit(t, 12n), fl),
        E.Bool.and_both(Dc.U32.hi_zero(h, 12n),
          Sf.Ords.all_fit(acc, 12n),
          E.Bool.and_l(Dc.U32.hi_zero(h, 12n),
            Sf.Ords.all_fit(t, 12n), fl), facc))

law Words.members_fit:
  for +ws: List<&2, U32>
  for +len: {Nat.is_eq(List.length(&2, U32, ws), 128n) == True{}
    : Bool}
  {Sf.Ords.all_fit(Wo.Words.members(ws, 0), 12n) == True{} : Bool}

def Words.tile_room(+ws: List<&2, U32>,
  +len: {Nat.is_eq(List.length(&2, U32, ws), 128n) == True{} : Bool})
  -> {C.Nat.upto(Nat.add(U32.to_nat(0),
       Sp.Nat.dbl(5n, List.length(&2, U32, ws))), 4096n)
     == True{} : Bool}:
  %E.Nat.sym(List.length(&2, U32, ws), 128n,
    Lf.Nat.is_eq_reflect(List.length(&2, U32, ws), 128n, len))
    : {C.Nat.upto(Nat.add(U32.to_nat(0), Sp.Nat.dbl(5n, _)), 4096n)
      == True{} : Bool}
  {==}

def Words.members_fit(ws, len):
  Ords.all_fit_reverse_go(Wo.Words.members.go(ws, 0, Nil{}), Nil{},
    Words.members_go_fit(ws, 0, Nil{}, {==},
      Words.tile_room(ws, len)), {==})

# ---------------------------------------------------------------------------
# A full leaf: the count-down from 4095 stays inside twelve bits.
#
# Stated for any count-down that does not wrap, and proved structurally --
# the closed computation at 4096 ordinals typechecks but exhausts the
# kernel's fuel under `--safe`.
# ---------------------------------------------------------------------------

law Nat.pos_of_le_succ:
  for +i: Nat
  for +a: Nat
  for +le: {C.Nat.upto(1n+i, a) == True{} : Bool}
  {C.Nat.gt(a, 0n) == True{} : Bool}

def Nat.pos_of_le_succ(i, a, le):
  match a:
    case 0n:
      E.Bool.noconf({C.Nat.gt(0n, 0n) == True{} : Bool}, le)
    case 1n+q:
      {==}

law Nat.le_dec:
  for +a: Nat
  {C.Nat.upto(Nat.sub(a, 1n), a) == True{} : Bool}

def Nat.le_dec(a):
  match a:
    case 0n:
      {==}
    case 1n+q:
      %E.Nat.sym(Nat.sub(q, 0n), q, De.Nat.sub_zero(q))
        : {C.Nat.upto(_, 1n+q) == True{} : Bool}
      It.Nat.le_up(q, q, It.Nat.upto_refl(q))

law Nat.le_pred_of_le_succ:
  for +i: Nat
  for +a: Nat
  for +le: {C.Nat.upto(1n+i, a) == True{} : Bool}
  {C.Nat.upto(i, Nat.sub(a, 1n)) == True{} : Bool}

def Nat.le_pred_of_le_succ(i, a, le):
  match a:
    case 0n:
      E.Bool.noconf({C.Nat.upto(i, Nat.sub(0n, 1n)) == True{} : Bool},
        le)
    case 1n+q:
      %E.Nat.sym(Nat.sub(q, 0n), q, De.Nat.sub_zero(q))
        : {C.Nat.upto(i, _) == True{} : Bool}
      le

law U32.fits_dec:
  for +ord: U32
  for +i: Nat
  for +hz: {Dc.U32.hi_zero(ord, 12n) == True{} : Bool}
  for +room: {C.Nat.upto(1n+i, U32.to_nat(ord)) == True{} : Bool}
  {Dc.U32.hi_zero(U32.sub(ord, 1), 12n) == True{} : Bool}

def U32.fits_dec(ord, i, hz, room):
  match ord:
    case U32{ow}:
      Dc.Word.to_nat_fits(32n, 12n, W.U32.word(U32.sub(U32{ow}, 1)),
        It.Nat.gt_cast(4096n, 4096n,
          Nat.sub(Word.to_nat(32n, ow), 1n),
          U32.to_nat(U32.sub(U32{ow}, 1)), {==},
          E.Nat.sym(U32.to_nat(U32.sub(U32{ow}, 1)),
            Nat.sub(Word.to_nat(32n, ow), 1n),
            De.U32.dec_spec(U32{ow},
              Nat.pos_of_le_succ(i, Word.to_nat(32n, ow), room))),
          It.Nat.gt_of_le(4096n, Nat.sub(Word.to_nat(32n, ow), 1n),
            Word.to_nat(32n, ow), Nat.le_dec(Word.to_nat(32n, ow)),
            Dc.Word.to_nat_bound(32n, 12n, ow, hz))))

law Ords.all_fit_range:
  for +k: Nat
  for +ord: U32
  for +tail: List<&2, U32>
  for +ftail: {Sf.Ords.all_fit(tail, 12n) == True{} : Bool}
  for +hz: {Dc.U32.hi_zero(ord, 12n) == True{} : Bool}
  for +room: {C.Nat.upto(k, 1n+U32.to_nat(ord)) == True{} : Bool}
  {Sf.Ords.all_fit(S.PSet.range(k, ord, tail), 12n) == True{} : Bool}

def Ords.all_fit_range(k, ord, tail, ftail, hz, room):
  match k:
    case 0n:
      ftail
    case 1n+j:
      match j:
        case 0n:
          E.Bool.and_both(Dc.U32.hi_zero(ord, 12n),
            Sf.Ords.all_fit(tail, 12n), hz, ftail)
        case 1n+i:
          Ords.all_fit_range(1n+i, U32.sub(ord, 1),
            Con{ord, tail},
            E.Bool.and_both(Dc.U32.hi_zero(ord, 12n),
              Sf.Ords.all_fit(tail, 12n), hz, ftail),
            U32.fits_dec(ord, i, hz, room),
            It.Nat.upto_cast(i, i, Nat.sub(U32.to_nat(ord), 1n),
              U32.to_nat(U32.sub(ord, 1)), {==},
              E.Nat.sym(U32.to_nat(U32.sub(ord, 1)),
                Nat.sub(U32.to_nat(ord), 1n),
                De.U32.dec_spec(ord,
                  Nat.pos_of_le_succ(i, U32.to_nat(ord), room))),
              Nat.le_pred_of_le_succ(i, U32.to_nat(ord), room)))

law Ords.all_fit_full_leaf:
  {Sf.Ords.all_fit(S.PSet.range(4096n, 4095, Nil{}), 12n) == True{}
    : Bool}

def Ords.all_fit_full_leaf():
  Ords.all_fit_range(4096n, 4095, Nil{}, {==}, {==}, {==})
