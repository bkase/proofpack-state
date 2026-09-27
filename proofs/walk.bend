# proofs/walk.bend -- the walk and the tile address name the same positions.
#
# This is the last thing law S-03 needs, and through S-03 the last thing
# S-02's leaf needs. `Words.holds` walks the words of a tile, building
# ordinals with `ord + 1` inside a word and `ord + 32` between words;
# `Words.bit` addresses word `x >> 5`, bit `x & 31`. They agree.
#
# Everything it rests on is already proved: `U32` addition adds
# (proofs/adder.bend), a word is determined by the number it reads as
# (proofs/inject.bend), an ordinal is its word index scaled plus its bit index
# (proofs/split.bend), and a number below 2^k fits in k bits
# (proofs/descend.bend). What is here is the case analysis joining them: an
# ordinal below a word's base is not found in it, one at or above the next
# word's base is not found in it either, and the one in between is found at
# exactly its bit.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./inject.bend as Ij
import ./split.bend as Sp
import ./adder.bend as Ad
import ./addr.bend as Adr
import ./count.bend as Ct
import ./descend.bend as Dc
import ./enum.bend as En
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo

# ---------------------------------------------------------------------------
# Ordering, and turning a numeric difference into a `U32` disequality.
# ---------------------------------------------------------------------------

law Nat.gt_irrefl:
  for +n: Nat
  {C.Nat.gt(n, n) == False{} : Bool}

def Nat.gt_irrefl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Nat.gt_irrefl(p)

law Nat.gt_of_upto:
  for +n: Nat
  for +a: Nat
  for +b: Nat
  for +le: {C.Nat.upto(a, b) == True{} : Bool}
  for +ok: {C.Nat.gt(n, b) == True{} : Bool}
  {C.Nat.gt(n, a) == True{} : Bool}

def Nat.gt_of_upto(n, a, b, le, ok):
  match n:
    case 0n:
      E.Bool.noconf({C.Nat.gt(0n, a) == True{} : Bool}, ok)
    case 1n+m:
      match a:
        case 0n:
          {==}
        case 1n+p:
          match b:
            case 0n:
              E.Bool.noconf({C.Nat.gt(1n+m, 1n+p) == True{} : Bool}, le)
            case 1n+q:
              Nat.gt_of_upto(m, p, q, le, ok)

law U32.neq_of_gt:
  for +a: U32
  for +b: U32
  for +ok: {C.Nat.gt(U32.to_nat(b), U32.to_nat(a)) == True{} : Bool}
  {U32.is_eq(a, b) == False{} : Bool}

law U32.neq_of_gt.on:
  for +a: U32
  for +b: U32
  for +ok: {C.Nat.gt(U32.to_nat(b), U32.to_nat(a)) == True{} : Bool}
  for +e: Bool
  for +ee: {e == U32.is_eq(a, b) : Bool}
  {U32.is_eq(a, b) == False{} : Bool}

law U32.neq_of_gt.absurd:
  for +a: U32
  for +b: U32
  for +ee: {True{} == U32.is_eq(a, b) : Bool}
  {C.Nat.gt(U32.to_nat(b), U32.to_nat(a)) == False{} : Bool}

def U32.neq_of_gt.absurd(a, b, ee):
  %E.Nat.sym(U32.to_nat(a), U32.to_nat(b),
    Equal.cong(U32, Nat, U32.to_nat, a, b,
      E.U32.eq_reflect(a, b, E.Bool.sym(True{}, U32.is_eq(a, b), ee))))
    : {C.Nat.gt(U32.to_nat(b), _) == False{} : Bool}
  Nat.gt_irrefl(U32.to_nat(b))

def U32.neq_of_gt.on(a, b, ok, e, ee):
  match e:
    case False{}:
      E.Bool.sym(e, U32.is_eq(a, b), ee)
    case True{}:
      E.Bool.noconf({U32.is_eq(a, b) == False{} : Bool},
        Equal.trans(Bool, False{}, C.Nat.gt(U32.to_nat(b),
          U32.to_nat(a)), True{},
          E.Bool.sym(C.Nat.gt(U32.to_nat(b), U32.to_nat(a)), False{},
            U32.neq_of_gt.absurd(a, b, ee)),
          ok))

def U32.neq_of_gt(a, b, ok):
  U32.neq_of_gt.on(a, b, ok, U32.is_eq(a, b), {==})

# ---------------------------------------------------------------------------
# Stepping the ordinal. Both increments are small, so `U32` addition adds.
# ---------------------------------------------------------------------------

law U32.to_nat_step:
  for +ord: U32
  for +d: U32
  for +zo: {Dc.U32.hi_zero(ord, 13n) == True{} : Bool}
  for +zd: {Dc.U32.hi_zero(d, 13n) == True{} : Bool}
  {U32.to_nat((ord + d : U32))
    == Nat.add(U32.to_nat(ord), U32.to_nat(d)) : Nat}

def U32.to_nat_step(ord, d, zo, zd):
  Ad.U32.to_nat_add(ord, d, 13n, zo, zd, {==})

law U32.fits13:
  for +v: U32
  for +ok: {C.Nat.gt(8192n, U32.to_nat(v)) == True{} : Bool}
  {Dc.U32.hi_zero(v, 13n) == True{} : Bool}

def U32.fits13(v, ok):
  match v:
    case U32{w}:
      Dc.Word.to_nat_fits(32n, 13n, w, ok)

law U32.bound13:
  for +v: U32
  for +ok: {Dc.U32.hi_zero(v, 13n) == True{} : Bool}
  {C.Nat.gt(8192n, U32.to_nat(v)) == True{} : Bool}

def U32.bound13(v, ok):
  match v:
    case U32{w}:
      Dc.Word.to_nat_bound(32n, 13n, w, ok)

# ---------------------------------------------------------------------------
# The scan's bound. `bnd` says the whole remaining scan stays inside 13 bits,
# and it is exactly what the next step needs: one fewer step from one higher
# base is the same bound.
# ---------------------------------------------------------------------------

law Nat.upto_add:
  for +a: Nat
  for +k: Nat
  {C.Nat.upto(a, Nat.add(a, k)) == True{} : Bool}

def Nat.upto_add(a, k):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.upto_add(p, k)

law U32.scan_fits:
  for +ord: U32
  for +k: Nat
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord), k))
    == True{} : Bool}
  {Dc.U32.hi_zero(ord, 13n) == True{} : Bool}

def U32.scan_fits(ord, k, bnd):
  U32.fits13(ord,
    Nat.gt_of_upto(8192n, U32.to_nat(ord),
      Nat.add(U32.to_nat(ord), k), Nat.upto_add(U32.to_nat(ord), k), bnd))

law U32.scan_step:
  for +ord: U32
  for +j: Nat
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord), 1n+j))
    == True{} : Bool}
  {C.Nat.gt(8192n, Nat.add(U32.to_nat((ord + 1 : U32)), j))
    == True{} : Bool}

law Words.bit_at_below:
  for +k: Nat
  for +w: U32
  for +ord: U32
  for +x: U32
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord), k))
    == True{} : Bool}
  for +lt: {C.Nat.gt(U32.to_nat(ord), U32.to_nat(x)) == True{} : Bool}
  {En.Words.bit_at(k, w, ord, x) == False{} : Bool}

law Words.above_step:
  for +ord: U32
  for +j: Nat
  for +x: U32
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord), 1n+j))
    == True{} : Bool}
  for +lt: {C.Nat.gt(U32.to_nat(ord), U32.to_nat(x)) == True{} : Bool}
  {C.Nat.gt(U32.to_nat((ord + 1 : U32)), U32.to_nat(x)) == True{} : Bool}

law Nat.gt_succ_l:
  for +a: Nat
  for +b: Nat
  for +ok: {C.Nat.gt(a, b) == True{} : Bool}
  {C.Nat.gt(Nat.add(a, 1n), b) == True{} : Bool}

def Nat.gt_succ_l(a, b, ok):
  match a:
    case 0n:
      E.Bool.noconf({C.Nat.gt(Nat.add(0n, 1n), b) == True{} : Bool}, ok)
    case 1n+p:
      match b:
        case 0n:
          {==}
        case 1n+q:
          Nat.gt_succ_l(p, q, ok)

def Words.above_step(ord, j, x, bnd, lt):
  %E.Nat.sym(U32.to_nat((ord + 1 : U32)),
    Nat.add(U32.to_nat(ord), U32.to_nat(1)),
    U32.to_nat_step(ord, 1, U32.scan_fits(ord, 1n+j, bnd), {==}))
    : {C.Nat.gt(_, U32.to_nat(x)) == True{} : Bool}
  Nat.gt_succ_l(U32.to_nat(ord), U32.to_nat(x), lt)

law Nat.shift_one:
  for +a: Nat
  for +j: Nat
  {Nat.add(Nat.add(a, 1n), j) == Nat.add(a, 1n+j) : Nat}

def Nat.shift_one(a, j):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %E.Nat.sym(Nat.add(Nat.add(p, 1n), j), Nat.add(p, 1n+j),
        Nat.shift_one(p, j))
        : {1n+_ == 1n+Nat.add(p, 1n+j) : Nat}
      {==}

def U32.scan_step(ord, j, bnd):
  %E.Nat.sym(U32.to_nat((ord + 1 : U32)),
    Nat.add(U32.to_nat(ord), U32.to_nat(1)),
    U32.to_nat_step(ord, 1, U32.scan_fits(ord, 1n+j, bnd), {==}))
    : {C.Nat.gt(8192n, Nat.add(_, j)) == True{} : Bool}
  %E.Nat.sym(Nat.add(Nat.add(U32.to_nat(ord), 1n), j),
    Nat.add(U32.to_nat(ord), 1n+j),
    Nat.shift_one(U32.to_nat(ord), j))
    : {C.Nat.gt(8192n, _) == True{} : Bool}
  bnd

# ---------------------------------------------------------------------------
# An ordinal below a word's base is not found in that word: every ordinal the
# scan tests is at or above the base.
# ---------------------------------------------------------------------------

law U32.neq_of_lt:
  for +a: U32
  for +b: U32
  for +ok: {C.Nat.gt(U32.to_nat(a), U32.to_nat(b)) == True{} : Bool}
  {U32.is_eq(a, b) == False{} : Bool}

law U32.neq_of_lt.on:
  for +a: U32
  for +b: U32
  for +ok: {C.Nat.gt(U32.to_nat(a), U32.to_nat(b)) == True{} : Bool}
  for +e: Bool
  for +ee: {e == U32.is_eq(a, b) : Bool}
  {U32.is_eq(a, b) == False{} : Bool}

law U32.neq_of_lt.absurd:
  for +a: U32
  for +b: U32
  for +ee: {True{} == U32.is_eq(a, b) : Bool}
  {C.Nat.gt(U32.to_nat(a), U32.to_nat(b)) == False{} : Bool}

def U32.neq_of_lt.absurd(a, b, ee):
  %Equal.cong(U32, Nat, U32.to_nat, a, b,
    E.U32.eq_reflect(a, b, E.Bool.sym(True{}, U32.is_eq(a, b), ee)))
    : {C.Nat.gt(U32.to_nat(a), _) == False{} : Bool}
  Nat.gt_irrefl(U32.to_nat(a))

def U32.neq_of_lt.on(a, b, ok, e, ee):
  match e:
    case False{}:
      E.Bool.sym(e, U32.is_eq(a, b), ee)
    case True{}:
      E.Bool.noconf({U32.is_eq(a, b) == False{} : Bool},
        Equal.trans(Bool, False{},
          C.Nat.gt(U32.to_nat(a), U32.to_nat(b)), True{},
          E.Bool.sym(C.Nat.gt(U32.to_nat(a), U32.to_nat(b)), False{},
            U32.neq_of_lt.absurd(a, b, ee)),
          ok))

def U32.neq_of_lt(a, b, ok):
  U32.neq_of_lt.on(a, b, ok, U32.is_eq(a, b), {==})

law Bool.and_false2:
  for +b: Bool
  {Bool.and(b, False{}) == False{} : Bool}

def Bool.and_false2(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Words.bit_at_below(k, w, ord, x, bnd, lt):
  match k:
    case 0n:
      {==}
    case 1n+j:
      %E.Bool.sym(U32.is_eq(ord, x), False{},
        U32.neq_of_lt(ord, x, lt))
        : {Bool.or(Bool.and(Wo.Nat.is_one(W.U32.low(w)), _),
            En.Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x))
          == False{} : Bool}
      %E.Bool.sym(Bool.and(Wo.Nat.is_one(W.U32.low(w)), False{}),
        False{}, Bool.and_false2(Wo.Nat.is_one(W.U32.low(w))))
        : {Bool.or(_, En.Words.bit_at(j, U32.shr(w),
            (ord + 1 : U32), x)) == False{} : Bool}
      Words.bit_at_below(j, U32.shr(w), (ord + 1 : U32), x,
        U32.scan_step(ord, j, bnd),
        Words.above_step(ord, j, x, bnd, lt))

# ---------------------------------------------------------------------------
# An ordinal at or beyond a word's end is not found in it either.
# ---------------------------------------------------------------------------

law Nat.gt_of_upto_succ:
  for +a: Nat
  for +j: Nat
  for +x: Nat
  for +le: {C.Nat.upto(Nat.add(a, 1n+j), x) == True{} : Bool}
  {C.Nat.gt(x, a) == True{} : Bool}

def Nat.gt_of_upto_succ(a, j, x, le):
  match a:
    case 0n:
      match x:
        case 0n:
          E.Bool.noconf({C.Nat.gt(0n, 0n) == True{} : Bool}, le)
        case 1n+y:
          {==}
    case 1n+p:
      match x:
        case 0n:
          E.Bool.noconf({C.Nat.gt(0n, 1n+p) == True{} : Bool}, le)
        case 1n+y:
          Nat.gt_of_upto_succ(p, j, y, le)

law Words.bit_at_beyond:
  for +k: Nat
  for +w: U32
  for +ord: U32
  for +x: U32
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord), k))
    == True{} : Bool}
  for +ge: {C.Nat.upto(Nat.add(U32.to_nat(ord), k), U32.to_nat(x))
    == True{} : Bool}
  {En.Words.bit_at(k, w, ord, x) == False{} : Bool}

law Words.beyond_step:
  for +ord: U32
  for +j: Nat
  for +x: U32
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord), 1n+j))
    == True{} : Bool}
  for +ge: {C.Nat.upto(Nat.add(U32.to_nat(ord), 1n+j), U32.to_nat(x))
    == True{} : Bool}
  {C.Nat.upto(Nat.add(U32.to_nat((ord + 1 : U32)), j), U32.to_nat(x))
    == True{} : Bool}

def Words.beyond_step(ord, j, x, bnd, ge):
  %E.Nat.sym(U32.to_nat((ord + 1 : U32)),
    Nat.add(U32.to_nat(ord), U32.to_nat(1)),
    U32.to_nat_step(ord, 1, U32.scan_fits(ord, 1n+j, bnd), {==}))
    : {C.Nat.upto(Nat.add(_, j), U32.to_nat(x)) == True{} : Bool}
  %E.Nat.sym(Nat.add(Nat.add(U32.to_nat(ord), 1n), j),
    Nat.add(U32.to_nat(ord), 1n+j),
    Nat.shift_one(U32.to_nat(ord), j))
    : {C.Nat.upto(_, U32.to_nat(x)) == True{} : Bool}
  ge

def Words.bit_at_beyond(k, w, ord, x, bnd, ge):
  match k:
    case 0n:
      {==}
    case 1n+j:
      %E.Bool.sym(U32.is_eq(ord, x), False{},
        U32.neq_of_gt(ord, x,
          Nat.gt_of_upto_succ(U32.to_nat(ord), j, U32.to_nat(x), ge)))
        : {Bool.or(Bool.and(Wo.Nat.is_one(W.U32.low(w)), _),
            En.Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x))
          == False{} : Bool}
      %E.Bool.sym(Bool.and(Wo.Nat.is_one(W.U32.low(w)), False{}),
        False{}, Bool.and_false2(Wo.Nat.is_one(W.U32.low(w))))
        : {Bool.or(_, En.Words.bit_at(j, U32.shr(w),
            (ord + 1 : U32), x)) == False{} : Bool}
      Words.bit_at_beyond(j, U32.shr(w), (ord + 1 : U32), x,
        U32.scan_step(ord, j, bnd),
        Words.beyond_step(ord, j, x, bnd, ge))

# ---------------------------------------------------------------------------
# And the ordinal in between is found at exactly its bit.
# ---------------------------------------------------------------------------

law U32.test_shr:
  for +w: U32
  for +d: Nat
  {Wo.U32.test(U32.shr(w), d) == Wo.U32.test(w, 1n+d) : Bool}

law U32.shrn_shr:
  for +w: U32
  for +d: Nat
  {U32.shrn(U32.shr(w), d) == U32.shrn(w, 1n+d) : U32}

def U32.shrn_shr(w, d):
  match d:
    case 0n:
      {==}
    case 1n+i:
      %E.U32.sym(U32.shrn(U32.shr(w), i), U32.shrn(w, 1n+i),
        U32.shrn_shr(w, i))
        : {U32.shr(_) == U32.shrn(w, 2n+i) : U32}
      {==}

def U32.test_shr(w, d):
  %E.U32.sym(U32.shrn(U32.shr(w), d), U32.shrn(w, 1n+d),
    U32.shrn_shr(w, d))
    : {Wo.Nat.is_one(W.U32.low(_)) == Wo.U32.test(w, 1n+d) : Bool}
  {==}

law Words.bit_at_hit:
  for +k: Nat
  for +w: U32
  for +ord: U32
  for +x: U32
  for +d: Nat
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord), k))
    == True{} : Bool}
  for +ex: {U32.to_nat(x) == Nat.add(U32.to_nat(ord), d) : Nat}
  for +ok: {C.Nat.gt(k, d) == True{} : Bool}
  {En.Words.bit_at(k, w, ord, x) == Wo.U32.test(w, d) : Bool}

law Bool.and_true_or:
  for +b: Bool
  {Bool.or(Bool.and(b, True{}), False{}) == b : Bool}

def Bool.and_true_or(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law Words.hit_eq:
  for +ord: U32
  for +x: U32
  for +ex: {U32.to_nat(x) == Nat.add(U32.to_nat(ord), 0n) : Nat}
  {U32.is_eq(ord, x) == True{} : Bool}

def Words.hit_eq(ord, x, ex):
  %E.U32.sym(x, ord,
    Ij.U32.to_nat_inj(x, ord,
      Equal.trans(Nat, U32.to_nat(x), Nat.add(U32.to_nat(ord), 0n),
        U32.to_nat(ord), ex, N.Nat.add_zero(U32.to_nat(ord)))))
    : {U32.is_eq(ord, _) == True{} : Bool}
  E.U32.is_eq_refl(ord)

law Words.hit_above:
  for +ord: U32
  for +j: Nat
  for +x: U32
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord), 1n+j))
    == True{} : Bool}
  for +ex: {U32.to_nat(x) == Nat.add(U32.to_nat(ord), 0n) : Nat}
  {C.Nat.gt(U32.to_nat((ord + 1 : U32)), U32.to_nat(x)) == True{} : Bool}

law Nat.gt_succ_self:
  for +a: Nat
  {C.Nat.gt(Nat.add(a, 1n), Nat.add(a, 0n)) == True{} : Bool}

def Nat.gt_succ_self(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.gt_succ_self(p)

def Words.hit_above(ord, j, x, bnd, ex):
  %E.Nat.sym(U32.to_nat((ord + 1 : U32)),
    Nat.add(U32.to_nat(ord), U32.to_nat(1)),
    U32.to_nat_step(ord, 1, U32.scan_fits(ord, 1n+j, bnd), {==}))
    : {C.Nat.gt(_, U32.to_nat(x)) == True{} : Bool}
  %E.Nat.sym(U32.to_nat(x), Nat.add(U32.to_nat(ord), 0n), ex)
    : {C.Nat.gt(Nat.add(U32.to_nat(ord), 1n), _) == True{} : Bool}
  Nat.gt_succ_self(U32.to_nat(ord))

law Words.hit_gt:
  for +ord: U32
  for +x: U32
  for +e: Nat
  for +ex: {U32.to_nat(x) == Nat.add(U32.to_nat(ord), 1n+e) : Nat}
  {C.Nat.gt(U32.to_nat(x), U32.to_nat(ord)) == True{} : Bool}

law Nat.gt_add_succ:
  for +a: Nat
  for +e: Nat
  {C.Nat.gt(Nat.add(a, 1n+e), a) == True{} : Bool}

def Nat.gt_add_succ(a, e):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.gt_add_succ(p, e)

def Words.hit_gt(ord, x, e, ex):
  %E.Nat.sym(U32.to_nat(x), Nat.add(U32.to_nat(ord), 1n+e), ex)
    : {C.Nat.gt(_, U32.to_nat(ord)) == True{} : Bool}
  Nat.gt_add_succ(U32.to_nat(ord), e)

law Words.hit_shift:
  for +ord: U32
  for +j: Nat
  for +x: U32
  for +e: Nat
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord), 1n+j))
    == True{} : Bool}
  for +ex: {U32.to_nat(x) == Nat.add(U32.to_nat(ord), 1n+e) : Nat}
  {U32.to_nat(x) == Nat.add(U32.to_nat((ord + 1 : U32)), e) : Nat}

def Words.hit_shift(ord, j, x, e, bnd, ex):
  %E.Nat.sym(U32.to_nat((ord + 1 : U32)),
    Nat.add(U32.to_nat(ord), U32.to_nat(1)),
    U32.to_nat_step(ord, 1, U32.scan_fits(ord, 1n+j, bnd), {==}))
    : {U32.to_nat(x) == Nat.add(_, e) : Nat}
  %E.Nat.sym(Nat.add(Nat.add(U32.to_nat(ord), 1n), e),
    Nat.add(U32.to_nat(ord), 1n+e),
    Nat.shift_one(U32.to_nat(ord), e))
    : {U32.to_nat(x) == _ : Nat}
  ex

def Words.bit_at_hit(k, w, ord, x, d, bnd, ex, ok):
  match k:
    case 0n:
      E.Bool.noconf({En.Words.bit_at(0n, w, ord, x)
        == Wo.U32.test(w, d) : Bool}, ok)
    case 1n+j:
      match d:
        case 0n:
          # The ordinal is this one: the test succeeds here and the rest of
          # the scan is looking above it.
          %E.Bool.sym(U32.is_eq(ord, x), True{},
            Words.hit_eq(ord, x, ex))
            : {Bool.or(Bool.and(Wo.Nat.is_one(W.U32.low(w)), _),
                En.Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x))
              == Wo.U32.test(w, 0n) : Bool}
          %E.Bool.sym(En.Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x),
            False{},
            Words.bit_at_below(j, U32.shr(w), (ord + 1 : U32), x,
              U32.scan_step(ord, j, bnd),
              Words.hit_above(ord, j, x, bnd, ex)))
            : {Bool.or(Bool.and(Wo.Nat.is_one(W.U32.low(w)), True{}), _)
              == Wo.U32.test(w, 0n) : Bool}
          Bool.and_true_or(Wo.Nat.is_one(W.U32.low(w)))
        case 1n+e:
          # Not this one: skip it and look one higher.
          %E.Bool.sym(U32.is_eq(ord, x), False{},
            U32.neq_of_gt(ord, x, Words.hit_gt(ord, x, e, ex)))
            : {Bool.or(Bool.and(Wo.Nat.is_one(W.U32.low(w)), _),
                En.Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x))
              == Wo.U32.test(w, 1n+e) : Bool}
          %E.Bool.sym(Bool.and(Wo.Nat.is_one(W.U32.low(w)), False{}),
            False{}, Bool.and_false2(Wo.Nat.is_one(W.U32.low(w))))
            : {Bool.or(_, En.Words.bit_at(j, U32.shr(w),
                (ord + 1 : U32), x)) == Wo.U32.test(w, 1n+e) : Bool}
          %U32.test_shr(w, e)
            : {En.Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x)
              == _ : Bool}
          Words.bit_at_hit(j, U32.shr(w), (ord + 1 : U32), x, e,
            U32.scan_step(ord, j, bnd),
            Words.hit_shift(ord, j, x, e, bnd, ex), ok)

# The three small facts the hit case needs about the ordinal.

# ---------------------------------------------------------------------------
# The bound, moved one word along.
# ---------------------------------------------------------------------------

law Nat.word_bound_step:
  for +a: Nat
  for +m: Nat
  {Nat.add(a, Sp.Nat.dbl(5n, 1n+m))
    == Nat.add(Nat.add(a, 32n), Sp.Nat.dbl(5n, m)) : Nat}

def Nat.at_add3(+l: Nat, r: Nat) -> Nat:
  Nat.add(l, r)

def Nat.word_bound_step(a, m):
  Equal.trans(Nat, Nat.add(a, Sp.Nat.dbl(5n, 1n+m)),
    Nat.add(a, Nat.add(32n, Sp.Nat.dbl(5n, m))),
    Nat.add(Nat.add(a, 32n), Sp.Nat.dbl(5n, m)),
    Equal.cong(Nat, Nat, Nat.at_add3(a), Sp.Nat.dbl(5n, 1n+m),
      Nat.add(32n, Sp.Nat.dbl(5n, m)),
      Ct.Nat.dbl_add(5n, 1n, m)),
    E.Nat.sym(Nat.add(Nat.add(a, 32n), Sp.Nat.dbl(5n, m)),
      Nat.add(a, Nat.add(32n, Sp.Nat.dbl(5n, m))),
      N.Nat.add_assoc(a, 32n, Sp.Nat.dbl(5n, m))))

law U32.to_nat_plus32:
  for +ord: U32
  for +bnd: {Dc.U32.hi_zero(ord, 13n) == True{} : Bool}
  {U32.to_nat((ord + 32 : U32)) == Nat.add(U32.to_nat(ord), 32n) : Nat}

def U32.to_nat_plus32(ord, bnd):
  U32.to_nat_step(ord, 32, bnd, {==})

law U32.word_fits:
  for +ord: U32
  for +m: Nat
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord),
    Sp.Nat.dbl(5n, m))) == True{} : Bool}
  {Dc.U32.hi_zero(ord, 13n) == True{} : Bool}

def U32.word_fits(ord, m, bnd):
  U32.scan_fits(ord, Sp.Nat.dbl(5n, m), bnd)

# The first word's scan is inside the tile's bound.
law U32.first_word_bound:
  for +ord: U32
  for +m: Nat
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord),
    Sp.Nat.dbl(5n, 1n+m))) == True{} : Bool}
  {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord), 32n)) == True{} : Bool}

law Nat.word_bound_step.apply:
  for +a: Nat
  for +m: Nat
  for +bnd: {C.Nat.gt(8192n, Nat.add(a, Sp.Nat.dbl(5n, 1n+m)))
    == True{} : Bool}
  {C.Nat.gt(8192n, Nat.add(Nat.add(a, 32n), Sp.Nat.dbl(5n, m)))
    == True{} : Bool}

def Nat.word_bound_step.apply(a, m, bnd):
  %Nat.word_bound_step(a, m)
    : {C.Nat.gt(8192n, _) == True{} : Bool}
  bnd

def U32.first_word_bound(ord, m, bnd):
  Nat.gt_of_upto(8192n, Nat.add(U32.to_nat(ord), 32n),
    Nat.add(Nat.add(U32.to_nat(ord), 32n), Sp.Nat.dbl(5n, m)),
    Nat.upto_add(Nat.add(U32.to_nat(ord), 32n), Sp.Nat.dbl(5n, m)),
    Nat.word_bound_step.apply(U32.to_nat(ord), m, bnd))

law U32.next_word_bound:
  for +ord: U32
  for +m: Nat
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord),
    Sp.Nat.dbl(5n, 1n+m))) == True{} : Bool}
  {C.Nat.gt(8192n, Nat.add(U32.to_nat((ord + 32 : U32)),
    Sp.Nat.dbl(5n, m))) == True{} : Bool}

def U32.next_word_bound(ord, m, bnd):
  %E.Nat.sym(U32.to_nat((ord + 32 : U32)),
    Nat.add(U32.to_nat(ord), U32.to_nat(32)),
    U32.to_nat_plus32(ord, U32.word_fits(ord, 1n+m, bnd)))
    : {C.Nat.gt(8192n, Nat.add(_, Sp.Nat.dbl(5n, m))) == True{} : Bool}
  Nat.word_bound_step.apply(U32.to_nat(ord), m, bnd)

# ---------------------------------------------------------------------------
# An ordinal below the tile's base is in none of its words.
# ---------------------------------------------------------------------------

law Words.holds_below:
  for +ws: List<&2, U32>
  for +ord: U32
  for +x: U32
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord),
    Sp.Nat.dbl(5n, List.length(&2, U32, ws)))) == True{} : Bool}
  for +lt: {C.Nat.gt(U32.to_nat(ord), U32.to_nat(x)) == True{} : Bool}
  {En.Words.holds(ws, ord, x) == False{} : Bool}

law Words.holds_below.lt:
  for +ord: U32
  for +m: Nat
  for +x: U32
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord),
    Sp.Nat.dbl(5n, 1n+m))) == True{} : Bool}
  for +lt: {C.Nat.gt(U32.to_nat(ord), U32.to_nat(x)) == True{} : Bool}
  {C.Nat.gt(U32.to_nat((ord + 32 : U32)), U32.to_nat(x))
    == True{} : Bool}

law Nat.gt_add_l:
  for +a: Nat
  for +c: Nat
  for +b: Nat
  for +ok: {C.Nat.gt(a, b) == True{} : Bool}
  {C.Nat.gt(Nat.add(a, c), b) == True{} : Bool}

def Nat.gt_add_l(a, c, b, ok):
  match a:
    case 0n:
      E.Bool.noconf({C.Nat.gt(Nat.add(0n, c), b) == True{} : Bool}, ok)
    case 1n+p:
      match b:
        case 0n:
          {==}
        case 1n+q:
          Nat.gt_add_l(p, c, q, ok)

def Words.holds_below.lt(ord, m, x, bnd, lt):
  %E.Nat.sym(U32.to_nat((ord + 32 : U32)),
    Nat.add(U32.to_nat(ord), U32.to_nat(32)),
    U32.to_nat_plus32(ord, U32.word_fits(ord, 1n+m, bnd)))
    : {C.Nat.gt(_, U32.to_nat(x)) == True{} : Bool}
  Nat.gt_add_l(U32.to_nat(ord), 32n, U32.to_nat(x), lt)

def Words.holds_below(ws, ord, x, bnd, lt):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      %E.Bool.sym(En.Words.bit_at(32n, w, ord, x), False{},
        Words.bit_at_below(32n, w, ord, x,
          U32.first_word_bound(ord, List.length(&2, U32, t), bnd), lt))
        : {Bool.or(_, En.Words.holds(t, (ord + 32 : U32), x))
          == False{} : Bool}
      Words.holds_below(t, (ord + 32 : U32), x,
        U32.next_word_bound(ord, List.length(&2, U32, t), bnd),
        Words.holds_below.lt(ord, List.length(&2, U32, t), x, bnd, lt))

# ---------------------------------------------------------------------------
# The walk and the address agree.
# ---------------------------------------------------------------------------

law Words.holds_at:
  for +ws: List<&2, U32>
  for +ord: U32
  for +x: U32
  for +i: Nat
  for +b: Nat
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord),
    Sp.Nat.dbl(5n, List.length(&2, U32, ws)))) == True{} : Bool}
  for +eb: {C.Nat.gt(32n, b) == True{} : Bool}
  for +ex: {U32.to_nat(x)
    == Nat.add(U32.to_nat(ord), Nat.add(Sp.Nat.dbl(5n, i), b))
    : Nat}
  {En.Words.holds(ws, ord, x) == Wo.Words.at(ws, i, b) : Bool}

law Bool.or_false3:
  for +v: Bool
  {Bool.or(v, False{}) == v : Bool}

def Bool.or_false3(v):
  match v:
    case False{}:
      {==}
    case True{}:
      {==}

# The four facts the induction needs about where the ordinal sits.

law Words.here_eq:
  for +ord: U32
  for +x: U32
  for +b: Nat
  for +ex: {U32.to_nat(x)
    == Nat.add(U32.to_nat(ord), Nat.add(Sp.Nat.dbl(5n, 0n), b)) : Nat}
  {U32.to_nat(x) == Nat.add(U32.to_nat(ord), b) : Nat}

def Words.here_eq(ord, x, b, ex):
  ex

law Words.here_below:
  for +ord: U32
  for +m: Nat
  for +x: U32
  for +b: Nat
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord),
    Sp.Nat.dbl(5n, 1n+m))) == True{} : Bool}
  for +eb: {C.Nat.gt(32n, b) == True{} : Bool}
  for +ex: {U32.to_nat(x)
    == Nat.add(U32.to_nat(ord), Nat.add(Sp.Nat.dbl(5n, 0n), b)) : Nat}
  {C.Nat.gt(U32.to_nat((ord + 32 : U32)), U32.to_nat(x))
    == True{} : Bool}

law Nat.gt_add_r:
  for +a: Nat
  for +b: Nat
  for +ok: {C.Nat.gt(32n, b) == True{} : Bool}
  {C.Nat.gt(Nat.add(a, 32n), Nat.add(a, b)) == True{} : Bool}

def Nat.gt_add_r(a, b, ok):
  match a:
    case 0n:
      ok
    case 1n+p:
      Nat.gt_add_r(p, b, ok)

def Words.here_below(ord, m, x, b, bnd, eb, ex):
  %E.Nat.sym(U32.to_nat((ord + 32 : U32)),
    Nat.add(U32.to_nat(ord), U32.to_nat(32)),
    U32.to_nat_plus32(ord, U32.word_fits(ord, 1n+m, bnd)))
    : {C.Nat.gt(_, U32.to_nat(x)) == True{} : Bool}
  %E.Nat.sym(U32.to_nat(x),
    Nat.add(U32.to_nat(ord), Nat.add(Sp.Nat.dbl(5n, 0n), b)), ex)
    : {C.Nat.gt(Nat.add(U32.to_nat(ord), 32n), _) == True{} : Bool}
  Nat.gt_add_r(U32.to_nat(ord), b, eb)

law Words.later_beyond:
  for +ord: U32
  for +x: U32
  for +i2: Nat
  for +b: Nat
  for +ex: {U32.to_nat(x)
    == Nat.add(U32.to_nat(ord), Nat.add(Sp.Nat.dbl(5n, 1n+i2), b))
    : Nat}
  {C.Nat.upto(Nat.add(U32.to_nat(ord), 32n), U32.to_nat(x))
    == True{} : Bool}

law Nat.upto_add_r2:
  for +a: Nat
  for +y: Nat
  for +b: Nat
  {C.Nat.upto(Nat.add(a, 32n),
    Nat.add(a, 32n+Nat.add(y, b))) == True{} : Bool}


def Nat.upto_add_r2(a, y, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.upto_add_r2(p, y, b)

def Words.later_beyond(ord, x, i2, b, ex):
  %E.Nat.sym(U32.to_nat(x),
    Nat.add(U32.to_nat(ord), Nat.add(Sp.Nat.dbl(5n, 1n+i2), b)), ex)
    : {C.Nat.upto(Nat.add(U32.to_nat(ord), 32n), _) == True{} : Bool}
  Nat.upto_add_r2(U32.to_nat(ord), Sp.Nat.dbl(5n, i2), b)

law Words.later_shift:
  for +ord: U32
  for +m: Nat
  for +x: U32
  for +i2: Nat
  for +b: Nat
  for +bnd: {C.Nat.gt(8192n, Nat.add(U32.to_nat(ord),
    Sp.Nat.dbl(5n, 1n+m))) == True{} : Bool}
  for +ex: {U32.to_nat(x)
    == Nat.add(U32.to_nat(ord), Nat.add(Sp.Nat.dbl(5n, 1n+i2), b))
    : Nat}
  {U32.to_nat(x)
    == Nat.add(U32.to_nat((ord + 32 : U32)),
         Nat.add(Sp.Nat.dbl(5n, i2), b)) : Nat}

law Nat.regroup32:
  for +a: Nat
  for +y: Nat
  for +b: Nat
  {Nat.add(a, 32n+Nat.add(y, b))
    == Nat.add(Nat.add(a, 32n), Nat.add(y, b)) : Nat}

def Nat.regroup32(a, y, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %E.Nat.sym(Nat.add(p, 32n+Nat.add(y, b)),
        Nat.add(Nat.add(p, 32n), Nat.add(y, b)), Nat.regroup32(p, y, b))
        : {1n+_ == 1n+Nat.add(Nat.add(p, 32n), Nat.add(y, b)) : Nat}
      {==}

def Words.later_shift(ord, m, x, i2, b, bnd, ex):
  %E.Nat.sym(U32.to_nat((ord + 32 : U32)),
    Nat.add(U32.to_nat(ord), U32.to_nat(32)),
    U32.to_nat_plus32(ord, U32.word_fits(ord, 1n+m, bnd)))
    : {U32.to_nat(x) == Nat.add(_, Nat.add(Sp.Nat.dbl(5n, i2), b))
      : Nat}
  %Nat.regroup32(U32.to_nat(ord), Sp.Nat.dbl(5n, i2), b)
    : {U32.to_nat(x) == _ : Nat}
  ex

def Words.holds_at(ws, ord, x, i, b, bnd, eb, ex):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      match i:
        case 0n:
          # The ordinal is in this word. The rest of the tile starts above
          # it, so the walk finds it here or nowhere.
          %E.Bool.sym(En.Words.holds(t, (ord + 32 : U32), x), False{},
            Words.holds_below(t, (ord + 32 : U32), x,
              U32.next_word_bound(ord, List.length(&2, U32, t), bnd),
              Words.here_below(ord, List.length(&2, U32, t), x, b,
                bnd, eb, ex)))
            : {Bool.or(En.Words.bit_at(32n, w, ord, x), _)
              == Wo.U32.test(w, b) : Bool}
          %E.Bool.sym(En.Words.bit_at(32n, w, ord, x),
            Wo.U32.test(w, b),
            Words.bit_at_hit(32n, w, ord, x, b,
              U32.first_word_bound(ord, List.length(&2, U32, t), bnd),
              Words.here_eq(ord, x, b, ex), eb))
            : {Bool.or(_, False{}) == Wo.U32.test(w, b) : Bool}
          Bool.or_false3(Wo.U32.test(w, b))
        case 1n+i2:
          # The ordinal is further along, so this word does not hold it.
          %E.Bool.sym(En.Words.bit_at(32n, w, ord, x), False{},
            Words.bit_at_beyond(32n, w, ord, x,
              U32.first_word_bound(ord, List.length(&2, U32, t), bnd),
              Words.later_beyond(ord, x, i2, b, ex)))
            : {Bool.or(_, En.Words.holds(t, (ord + 32 : U32), x))
              == Wo.Words.at(t, i2, b) : Bool}
          Words.holds_at(t, (ord + 32 : U32), x, i2, b,
            U32.next_word_bound(ord, List.length(&2, U32, t), bnd),
            eb,
            Words.later_shift(ord, List.length(&2, U32, t), x, i2, b,
              bnd, ex))

# ---------------------------------------------------------------------------
# At the top: a 128-word tile, an ordinal it covers.
# ---------------------------------------------------------------------------

law Words.holds_bit:
  for +ws: List<&2, U32>
  for +x: U32
  for +wide: {List.length(&2, U32, ws) == 128n : Nat}
  {En.Words.holds(ws, 0, x) == Wo.Words.bit(ws, x) : Bool}

law Words.holds_bit.bnd:
  for +ws: List<&2, U32>
  for +wide: {List.length(&2, U32, ws) == 128n : Nat}
  {C.Nat.gt(8192n, Nat.add(U32.to_nat(0),
    Sp.Nat.dbl(5n, List.length(&2, U32, ws)))) == True{} : Bool}

def Words.holds_bit.bnd(ws, wide):
  %E.Nat.sym(List.length(&2, U32, ws), 128n, wide)
    : {C.Nat.gt(8192n, Nat.add(U32.to_nat(0), Sp.Nat.dbl(5n, _)))
      == True{} : Bool}
  {==}

def Words.holds_bit(ws, x, wide):
  Words.holds_at(ws, 0, x, U32.to_nat(U32.shrn(x, 5n)),
    U32.to_nat(U32.and(x, 31)),
    Words.holds_bit.bnd(ws, wide),
    Adr.U32.low_five_bound(x),
    Sp.U32.to_nat_split(x))
