# proofs/cardsplit.bend -- counting a set and its complement inside another.
#
# The fixed point of the closure iteration is a pigeonhole argument, and what
# a pigeonhole needs is a measure that strictly grows. The measure is the
# size of the round, and what makes it grow is this identity:
#
#     |b| = |a| + |b \ a|      whenever a is inside b
#
# stated over the fused counts the production code actually runs, so that no
# intermediate difference is ever allocated in the statement either. "a is
# inside b" is itself a fused count being zero, which is decidable data and
# so reusable -- the whole reason the closure proofs can carry it.
#
# This file is the bit and tile level. The tree level is proofs/setcard.bend.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./inject.bend as Ij
import ./word.bend as Wd
import ./popcount.bend as PP
import ./count.bend as Ct
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo

# ---------------------------------------------------------------------------
# Nat rearrangement.
# ---------------------------------------------------------------------------

law Nat.add_swap:
  for +y: Nat
  for +z: Nat
  for +w: Nat
  {Nat.add(y, Nat.add(z, w)) == Nat.add(z, Nat.add(y, w)) : Nat}

def Nat.add_swap(y, z, w):
  %N.Nat.add_assoc(y, z, w)
    : {_ == Nat.add(z, Nat.add(y, w)) : Nat}
  %N.Nat.add_assoc(z, y, w)
    : {Nat.add(Nat.add(y, z), w) == _ : Nat}
  %N.Nat.add_comm(y, z)
    : {Nat.add(Nat.add(y, z), w) == Nat.add(_, w) : Nat}
  {==}

law Nat.add_exchange:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for +w: Nat
  {Nat.add(Nat.add(x, y), Nat.add(z, w))
    == Nat.add(Nat.add(x, z), Nat.add(y, w)) : Nat}

def Nat.add_exchange(x, y, z, w):
  %E.Nat.sym(Nat.add(Nat.add(x, y), Nat.add(z, w)),
    Nat.add(x, Nat.add(y, Nat.add(z, w))),
    N.Nat.add_assoc(x, y, Nat.add(z, w)))
    : {_ == Nat.add(Nat.add(x, z), Nat.add(y, w)) : Nat}
  %E.Nat.sym(Nat.add(Nat.add(x, z), Nat.add(y, w)),
    Nat.add(x, Nat.add(z, Nat.add(y, w))),
    N.Nat.add_assoc(x, z, Nat.add(y, w)))
    : {Nat.add(x, Nat.add(y, Nat.add(z, w))) == _ : Nat}
  %Nat.add_swap(y, z, w)
    : {Nat.add(x, Nat.add(y, Nat.add(z, w))) == Nat.add(x, _)
      : Nat}
  {==}

# ---------------------------------------------------------------------------
# One bit position.
# ---------------------------------------------------------------------------

law U32.card_split.bits:
  for +ba: Bool
  for +bb: Bool
  for +bd: Bool
  for +ca: Nat
  for +cb: Nat
  for +cd: Nat
  for +ebd: {bd == Bool.and(bb, Bool.not(ba)) : Bool}
  for +nz: {Bool.and(ba, Bool.not(bb)) == False{} : Bool}
  for +ih: {cb == Nat.add(ca, cd) : Nat}
  {W.U32.bump(bb, cb)
    == Nat.add(W.U32.bump(ba, ca), W.U32.bump(bd, cd)) : Nat}

def U32.card_split.bits(ba, bb, bd, ca, cb, cd, ebd, nz, ih):
  match ba:
    case False{}:
      match bb:
        case False{}:
          %E.Bool.sym(bd, Bool.and(False{}, Bool.not(False{})), ebd)
            : {cb == Nat.add(ca, W.U32.bump(_, cd)) : Nat}
          ih
        case True{}:
          %E.Bool.sym(bd, Bool.and(True{}, Bool.not(False{})), ebd)
            : {1n+cb == Nat.add(ca, W.U32.bump(_, cd)) : Nat}
          %E.Nat.sym(Nat.add(ca, 1n+cd), 1n+Nat.add(ca, cd),
            N.Nat.add_succ(ca, cd)) : {1n+cb == _ : Nat}
          %ih : {1n+cb == 1n+_ : Nat}
          {==}
    case True{}:
      match bb:
        case False{}:
          E.Bool.noconf.r({W.U32.bump(False{}, cb)
            == Nat.add(W.U32.bump(True{}, ca), W.U32.bump(bd, cd))
            : Nat}, nz)
        case True{}:
          %E.Bool.sym(bd, Bool.and(True{}, Bool.not(True{})), ebd)
            : {1n+cb == Nat.add(1n+ca, W.U32.bump(_, cd)) : Nat}
          %ih : {1n+cb == 1n+_ : Nat}
          {==}

law U32.card_zero_bit:
  for +p: Nat
  for +x: U32
  for +bx: Bool
  for +ebx: {bx == W.U32.bit(x, p) : Bool}
  for +z: {W.U32.card(1n+p, x) == 0n : Nat}
  {W.U32.bit(x, p) == False{} : Bool}

def U32.card_zero_bit(p, x, bx, ebx, z):
  match bx:
    case False{}:
      E.Bool.sym(False{}, W.U32.bit(x, p), ebx)
    case True{}:
      E.Nat.noconf2({W.U32.bit(x, p) == False{} : Bool},
        W.U32.card(p, x),
        %E.Bool.sym(True{}, W.U32.bit(x, p), ebx)
          : {W.U32.bump(_, W.U32.card(p, x)) == 0n : Nat}
        z)

law U32.card_zero_rest:
  for +p: Nat
  for +x: U32
  for +bx: Bool
  for +ebx: {bx == W.U32.bit(x, p) : Bool}
  for +z: {W.U32.card(1n+p, x) == 0n : Nat}
  {W.U32.card(p, x) == 0n : Nat}

def U32.card_zero_rest(p, x, bx, ebx, z):
  match bx:
    case False{}:
      %E.Bool.sym(False{}, W.U32.bit(x, p), ebx)
        : {W.U32.bump(_, W.U32.card(p, x)) == 0n : Nat}
      z
    case True{}:
      E.Nat.noconf2({W.U32.card(p, x) == 0n : Nat},
        W.U32.card(p, x),
        %E.Bool.sym(True{}, W.U32.bit(x, p), ebx)
          : {W.U32.bump(_, W.U32.card(p, x)) == 0n : Nat}
        z)

law U32.card_split:
  for +k: Nat
  for +a: U32
  for +b: U32
  for +sub: {W.U32.card(k, W.U32.diff(a, b)) == 0n : Nat}
  {W.U32.card(k, b)
    == Nat.add(W.U32.card(k, a), W.U32.card(k, W.U32.diff(b, a)))
    : Nat}

def U32.card_split(k, a, b, sub):
  match k:
    case 0n:
      {==}
    case 1n+p:
      U32.card_split.bits(W.U32.bit(a, p), W.U32.bit(b, p),
        W.U32.bit(W.U32.diff(b, a), p), W.U32.card(p, a),
        W.U32.card(p, b), W.U32.card(p, W.U32.diff(b, a)),
        Wd.U32.bit_diff(b, a, p),
        Equal.trans(Bool,
          Bool.and(W.U32.bit(a, p), Bool.not(W.U32.bit(b, p))),
          W.U32.bit(W.U32.diff(a, b), p), False{},
          E.Bool.sym(W.U32.bit(W.U32.diff(a, b), p),
            Bool.and(W.U32.bit(a, p), Bool.not(W.U32.bit(b, p))),
            Wd.U32.bit_diff(a, b, p)),
          U32.card_zero_bit(p, W.U32.diff(a, b),
            W.U32.bit(W.U32.diff(a, b), p), {==}, sub)),
        U32.card_split(p, a, b,
          U32.card_zero_rest(p, W.U32.diff(a, b),
            W.U32.bit(W.U32.diff(a, b), p), {==}, sub)))

# ---------------------------------------------------------------------------
# One word.
# ---------------------------------------------------------------------------

law U32.popcount_split:
  for +a: U32
  for +b: U32
  for +sub: {W.U32.popcount(W.U32.diff(a, b)) == 0n : Nat}
  {W.U32.popcount(b)
    == Nat.add(W.U32.popcount(a),
         W.U32.popcount(W.U32.diff(b, a))) : Nat}

def U32.popcount_split(a, b, sub):
  %E.Nat.sym(W.U32.popcount(b), W.U32.card(32n, b),
    PP.U32.popcount_spec(b))
    : {_ == Nat.add(W.U32.popcount(a),
        W.U32.popcount(W.U32.diff(b, a))) : Nat}
  %E.Nat.sym(W.U32.popcount(a), W.U32.card(32n, a),
    PP.U32.popcount_spec(a))
    : {W.U32.card(32n, b) == Nat.add(_,
        W.U32.popcount(W.U32.diff(b, a))) : Nat}
  %E.Nat.sym(W.U32.popcount(W.U32.diff(b, a)),
    W.U32.card(32n, W.U32.diff(b, a)),
    PP.U32.popcount_spec(W.U32.diff(b, a)))
    : {W.U32.card(32n, b) == Nat.add(W.U32.card(32n, a), _) : Nat}
  U32.card_split(32n, a, b,
    Equal.trans(Nat, W.U32.card(32n, W.U32.diff(a, b)),
      W.U32.popcount(W.U32.diff(a, b)), 0n,
      E.Nat.sym(W.U32.popcount(W.U32.diff(a, b)),
        W.U32.card(32n, W.U32.diff(a, b)),
        PP.U32.popcount_spec(W.U32.diff(a, b))), sub))

# ---------------------------------------------------------------------------
# A tile.
# ---------------------------------------------------------------------------

law Words.diff_nil:
  for +b: List<&2, U32>
  {Wo.Words.diff(b, Nil{}) == b : List<&2, U32>}

def Words.diff_nil(b):
  match b:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

law Words.count_split:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +sub: {Wo.Words.count(Wo.Words.diff(a, b)) == 0n : Nat}
  {Wo.Words.count(b)
    == Nat.add(Wo.Words.count(a),
         Wo.Words.count(Wo.Words.diff(b, a))) : Nat}

def Words.count_split(a, b, sub):
  match a:
    case Nil{}:
      %E.List.sym(U32, Wo.Words.diff(b, Nil{}), b, Words.diff_nil(b))
        : {Wo.Words.count(b) == Wo.Words.count(_) : Nat}
      {==}
    case Con{ah, at}:
      match b:
        case Nil{}:
          %E.Nat.sym(Wo.Words.count(Con{ah, at}), 0n, sub)
            : {0n == Nat.add(_, 0n) : Nat}
          {==}
        case Con{bh, bt}:
          %E.Nat.sym(Wo.Words.count(Con{bh, bt}),
            Nat.add(Wo.Words.count(bt), W.U32.popcount(bh)),
            Ct.Words.count_cons(bh, bt))
            : {_ == Nat.add(Wo.Words.count(Con{ah, at}),
                Wo.Words.count(Con{W.U32.diff(bh, ah),
                  Wo.Words.diff(bt, at)})) : Nat}
          %E.Nat.sym(Wo.Words.count(Con{ah, at}),
            Nat.add(Wo.Words.count(at), W.U32.popcount(ah)),
            Ct.Words.count_cons(ah, at))
            : {Nat.add(Wo.Words.count(bt), W.U32.popcount(bh))
              == Nat.add(_, Wo.Words.count(Con{W.U32.diff(bh, ah),
                Wo.Words.diff(bt, at)})) : Nat}
          %E.Nat.sym(Wo.Words.count(Con{W.U32.diff(bh, ah),
              Wo.Words.diff(bt, at)}),
            Nat.add(Wo.Words.count(Wo.Words.diff(bt, at)),
              W.U32.popcount(W.U32.diff(bh, ah))),
            Ct.Words.count_cons(W.U32.diff(bh, ah),
              Wo.Words.diff(bt, at)))
            : {Nat.add(Wo.Words.count(bt), W.U32.popcount(bh))
              == Nat.add(Nat.add(Wo.Words.count(at),
                W.U32.popcount(ah)), _) : Nat}
          %E.Nat.sym(
            Nat.add(Nat.add(Wo.Words.count(at), W.U32.popcount(ah)),
              Nat.add(Wo.Words.count(Wo.Words.diff(bt, at)),
                W.U32.popcount(W.U32.diff(bh, ah)))),
            Nat.add(Nat.add(Wo.Words.count(at),
              Wo.Words.count(Wo.Words.diff(bt, at))),
              Nat.add(W.U32.popcount(ah),
                W.U32.popcount(W.U32.diff(bh, ah)))),
            Nat.add_exchange(Wo.Words.count(at), W.U32.popcount(ah),
              Wo.Words.count(Wo.Words.diff(bt, at)),
              W.U32.popcount(W.U32.diff(bh, ah))))
            : {Nat.add(Wo.Words.count(bt), W.U32.popcount(bh)) == _
              : Nat}
          %E.Nat.sym(Wo.Words.count(bt),
            Nat.add(Wo.Words.count(at),
              Wo.Words.count(Wo.Words.diff(bt, at))),
            Words.count_split(at, bt,
              Ct.Nat.add_zero_left(
                Wo.Words.count(Wo.Words.diff(at, bt)),
                W.U32.popcount(W.U32.diff(ah, bh)),
                Ct.Words.count_zero.sum(W.U32.diff(ah, bh),
                  Wo.Words.diff(at, bt), sub))))
            : {Nat.add(_, W.U32.popcount(bh))
              == Nat.add(Nat.add(Wo.Words.count(at),
                Wo.Words.count(Wo.Words.diff(bt, at))),
                Nat.add(W.U32.popcount(ah),
                  W.U32.popcount(W.U32.diff(bh, ah)))) : Nat}
          %E.Nat.sym(W.U32.popcount(bh),
            Nat.add(W.U32.popcount(ah),
              W.U32.popcount(W.U32.diff(bh, ah))),
            U32.popcount_split(ah, bh,
              Ct.Nat.add_zero_right(
                Wo.Words.count(Wo.Words.diff(at, bt)),
                W.U32.popcount(W.U32.diff(ah, bh)),
                Ct.Words.count_zero.sum(W.U32.diff(ah, bh),
                  Wo.Words.diff(at, bt), sub))))
            : {Nat.add(Nat.add(Wo.Words.count(at),
                Wo.Words.count(Wo.Words.diff(bt, at))), _)
              == Nat.add(Nat.add(Wo.Words.count(at),
                Wo.Words.count(Wo.Words.diff(bt, at))),
                Nat.add(W.U32.popcount(ah),
                  W.U32.popcount(W.U32.diff(bh, ah)))) : Nat}
          {==}
