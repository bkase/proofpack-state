# proofs/halves.bend -- a node's two halves, as bases.
#
# A branch at depth 1n+p covers 2^(13+p) ordinals from `base`; its halves
# cover 2^(12+p) each, the first from `base` and the second from `base + h`
# where `h` is 2^(12+p). This file says what `base + h` is: no carry leaves
# the half's own bit, so the sum is an `or`, its low bits are still zero, and
# it reads as the number one half above the base.
#
# Those three facts are what let the enumeration hand a child the same shape
# of hypothesis it was given itself.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./split_add.bend as Sa
import ./lastord.bend as Ld
import ../core/count.bend as C
import ../core/word.bend as W

law Word.lo_zero_down:
  for +n: Nat
  for +w: Word(n)
  for +k: Nat
  for +lz: {Sa.Word.lo_zero(n, w, 1n+k) == True{} : Bool}
  {Sa.Word.lo_zero(n, w, k) == True{} : Bool}

def Word.lo_zero_down(n, w, k, lz):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              E.Bool.and_both(Bool.not(b), Sa.Word.lo_zero(p, t, j),
                E.Bool.and_l(Bool.not(b), Sa.Word.lo_zero(p, t, 1n+j),
                  lz),
                Word.lo_zero_down(p, t, j,
                  E.Bool.and_r(Bool.not(b),
                    Sa.Word.lo_zero(p, t, 1n+j), lz)))

law Word.lo_zero_or:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +k: Nat
  for +la: {Sa.Word.lo_zero(n, a, k) == True{} : Bool}
  for +lbb: {Sa.Word.lo_zero(n, b, k) == True{} : Bool}
  {Sa.Word.lo_zero(n, Word.or(n, a, b), k) == True{} : Bool}

law Word.lo_zero_or.head:
  for +ab: Bool
  for +bb: Bool
  for +na: {Bool.not(ab) == True{} : Bool}
  for +nb: {Bool.not(bb) == True{} : Bool}
  {Bool.not(Bool.or(ab, bb)) == True{} : Bool}

def Word.lo_zero_or.head(ab, bb, na, nb):
  match ab:
    case False{}:
      match bb:
        case False{}:
          {==}
        case True{}:
          nb
    case True{}:
      na

def Word.lo_zero_or(n, a, b, k, la, lbb):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              E.Bool.and_both(Bool.not(Bool.or(ab, bb)),
                Sa.Word.lo_zero(p, Word.or(p, at, bt), j),
                Word.lo_zero_or.head(ab, bb,
                  E.Bool.and_l(Bool.not(ab),
                    Sa.Word.lo_zero(p, at, j), la),
                  E.Bool.and_l(Bool.not(bb),
                    Sa.Word.lo_zero(p, bt, j), lbb)),
                Word.lo_zero_or(p, at, bt, j,
                  E.Bool.and_r(Bool.not(ab),
                    Sa.Word.lo_zero(p, at, j), la),
                  E.Bool.and_r(Bool.not(bb),
                    Sa.Word.lo_zero(p, bt, j), lbb)))

law Word.lo_zero_pow2:
  for +n: Nat
  for +k: Nat
  {Sa.Word.lo_zero(n, Dc.Word.pow2(n, k), k) == True{} : Bool}

def Word.lo_zero_pow2(n, k):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match k:
        case 0n:
          {==}
        case 1n+j:
          Word.lo_zero_pow2(p, j)

law Word.hi_zero_zeros:
  for +n: Nat
  for +k: Nat
  {Dc.Word.hi_zero(n, Dc.Word.zeros(n), k) == True{} : Bool}

def Word.hi_zero_zeros(n, k):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match k:
        case 0n:
          Word.hi_zero_zeros(p, 0n)
        case 1n+j:
          Word.hi_zero_zeros(p, j)

law Word.hi_zero_pow2:
  for +n: Nat
  for +k: Nat
  {Dc.Word.hi_zero(n, Dc.Word.pow2(n, k), 1n+k) == True{} : Bool}

def Word.hi_zero_pow2(n, k):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match k:
        case 0n:
          Word.hi_zero_zeros(p, 0n)
        case 1n+j:
          Word.hi_zero_pow2(p, j)

# ---------------------------------------------------------------------------
# At `U32`: the second half's base.
# ---------------------------------------------------------------------------

law U32.half_base:
  for +base: U32
  for +k: Nat
  for +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool}
  {(base + U32.shln(1, k) : U32) == U32.or(base, U32.shln(1, k)) : U32}

def U32.half_base(base, k, lz):
  match base:
    case U32{bw}:
      %E.U32.sym(U32.shln(1, k), U32{Dc.Word.pow2(32n, k)},
        Dc.U32.shln_one_pow2(k))
        : {(U32{bw} + _ : U32) == U32.or(U32{bw}, _) : U32}
      %Word.add_comm(32n, Dc.Word.pow2(32n, k), bw)
        : {U32{_} == U32{Word.or(32n, bw, Dc.Word.pow2(32n, k))} : U32}
      %Ld.Word.or_comm(32n, Dc.Word.pow2(32n, k), bw)
        : {U32{Word.adc(32n, Dc.Word.pow2(32n, k), bw, False{},
            False{})} == U32{_} : U32}
      Equal.cong(Word(32n), U32, E.U32.pak,
        Word.adc(32n, Dc.Word.pow2(32n, k), bw, False{}, False{}),
        Word.or(32n, Dc.Word.pow2(32n, k), bw),
        Sa.Word.adc_disjoint(32n, 1n+k, Dc.Word.pow2(32n, k), bw,
          Word.hi_zero_pow2(32n, k), lz))

law U32.lo_zero_half_base:
  for +base: U32
  for +k: Nat
  for +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool}
  {Sa.U32.lo_zero((base + U32.shln(1, k) : U32), k) == True{} : Bool}

def U32.lo_zero_half_base(base, k, lz):
  match base:
    case U32{bw}:
      %E.U32.sym((U32{bw} + U32.shln(1, k) : U32),
        U32.or(U32{bw}, U32.shln(1, k)),
        U32.half_base(U32{bw}, k, lz))
        : {Sa.U32.lo_zero(_, k) == True{} : Bool}
      %E.U32.sym(U32.shln(1, k), U32{Dc.Word.pow2(32n, k)},
        Dc.U32.shln_one_pow2(k))
        : {Sa.U32.lo_zero(U32.or(U32{bw}, _), k) == True{} : Bool}
      Word.lo_zero_or(32n, bw, Dc.Word.pow2(32n, k), k,
        Word.lo_zero_down(32n, bw, k, lz),
        Word.lo_zero_pow2(32n, k))

law U32.to_nat_half_base:
  for +base: U32
  for +k: Nat
  for +lz: {Sa.U32.lo_zero(base, 1n+k) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, k) == True{} : Bool}
  {U32.to_nat((base + U32.shln(1, k) : U32))
    == Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)) : Nat}

law U32.hi_zero_shln:
  for +k: Nat
  {Dc.U32.hi_zero(U32.shln(1, k), 1n+k) == True{} : Bool}

def U32.hi_zero_shln(k):
  %E.U32.sym(U32.shln(1, k), U32{Dc.Word.pow2(32n, k)},
    Dc.U32.shln_one_pow2(k))
    : {Dc.U32.hi_zero(_, 1n+k) == True{} : Bool}
  Word.hi_zero_pow2(32n, k)

def U32.to_nat_half_base(base, k, lz, lt):
  %E.U32.sym((base + U32.shln(1, k) : U32),
    U32.or(base, U32.shln(1, k)), U32.half_base(base, k, lz))
    : {U32.to_nat(_) == Nat.add(U32.to_nat(base), Dc.Nat.pow2(k))
      : Nat}
  %Ld.U32.or_comm(U32.shln(1, k), base)
    : {U32.to_nat(_) == Nat.add(U32.to_nat(base), Dc.Nat.pow2(k))
      : Nat}
  %E.Nat.sym(U32.to_nat(U32.or(U32.shln(1, k), base)),
    Nat.add(U32.to_nat(U32.shln(1, k)), U32.to_nat(base)),
    Sa.U32.to_nat_or(U32.shln(1, k), base, 1n+k,
      U32.hi_zero_shln(k), lz))
    : {_ == Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)) : Nat}
  %E.Nat.sym(U32.to_nat(U32.shln(1, k)), Dc.Nat.pow2(k),
    Ld.U32.to_nat_shln(k, lt))
    : {Nat.add(_, U32.to_nat(base))
      == Nat.add(U32.to_nat(base), Dc.Nat.pow2(k)) : Nat}
  N.Nat.add_comm(Dc.Nat.pow2(k), U32.to_nat(base))

law Nat.le_down:
  for +a: Nat
  for +b: Nat
  for +le: {C.Nat.upto(1n+a, b) == True{} : Bool}
  {C.Nat.upto(a, b) == True{} : Bool}

def Nat.le_down(a, b, le):
  match a:
    case 0n:
      {==}
    case 1n+p:
      match b:
        case 0n:
          le
        case 1n+q:
          Nat.le_down(p, q, le)
