# proofs/count.bend -- what a bit count says about the bits (law S-03).
#
# `PSet.compress` decides a leaf's representation from one number: the count
# of set bits. Zero means `PZero{}`, 4096 means `PFull{}`, few enough means a
# sparse offset list, and the rest stays dense. For that decision to preserve
# membership -- which is what S-03 says, and what makes the sparse/dense
# crossover a benchmark parameter rather than a semantic constant -- two
# counting facts have to hold:
#
#   * a count of zero means no bit is set;
#   * a count of 4096 across 128 words means every bit is set.
#
# The second is a pigeonhole: 128 words hold at most 32 bits each, so 4096 is
# only reachable when every word is full, and a word is full only when every
# bit of it is set. Both halves are inductions, and the arithmetic they need
# is one cancellation lemma: if `a + B == c + D` with `a <= c` and `B <= D`,
# then `a == c`.
#
# The counts are stated over `U32.card`, the specification-side count, because
# `popcount_counts_the_bits_that_are_set` already connects it to the
# production loop.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./inject.bend as Ij
import ./leaf.bend as Lf
import ./bits.bend as PB
import ./popcount.bend as PP
import ./split.bend as Sp
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo

# ---------------------------------------------------------------------------
# Ordering.
# ---------------------------------------------------------------------------
law Nat.gt_split:
  for +p: Nat
  for +j: Nat
  for +ok: {C.Nat.gt(1n+p, j) == True{} : Bool}
  {Bool.or(Nat.is_eq(j, p), C.Nat.gt(p, j)) == True{} : Bool}

def Nat.gt_split(p, j, ok):
  match p:
    case 0n:
      match j:
        case 0n:
          {==}
        case 1n+i:
          E.Bool.noconf({Bool.or(Nat.is_eq(1n+i, 0n), C.Nat.gt(0n, 1n+i))
            == True{} : Bool}, ok)
    case 1n+q:
      match j:
        case 0n:
          {==}
        case 1n+i:
          Nat.gt_split(q, i, ok)

law Nat.upto_succ_absurd:
  for +p: Nat
  for +ok: {C.Nat.upto(1n+p, p) == True{} : Bool}
  {Empty : Type}

def Nat.upto_succ_absurd(p, ok):
  match p:
    case 0n:
      E.Bool.empty(ok)
    case 1n+q:
      Nat.upto_succ_absurd(q, ok)

law Nat.bump_le:
  for +b: Bool
  for +a: Nat
  for +k: Nat
  for +ok: {C.Nat.upto(a, k) == True{} : Bool}
  {C.Nat.upto(W.U32.bump(b, a), 1n+k) == True{} : Bool}

law Nat.upto_succ_r:
  for +u: Nat
  for +v: Nat
  for +ok: {C.Nat.upto(u, v) == True{} : Bool}
  {C.Nat.upto(u, 1n+v) == True{} : Bool}

def Nat.upto_succ_r(u, v, ok):
  match u:
    case 0n:
      {==}
    case 1n+p:
      match v:
        case 0n:
          E.Bool.noconf({C.Nat.upto(1n+p, 1n) == True{} : Bool}, ok)
        case 1n+q:
          Nat.upto_succ_r(p, q, ok)

# ---------------------------------------------------------------------------
# A bit count never exceeds the number of bits counted.
# ---------------------------------------------------------------------------

def Nat.bump_le(b, a, k, ok):
  match b:
    case False{}:
      Nat.upto_succ_r(a, k, ok)
    case True{}:
      ok

law U32.card_le:
  for +k: Nat
  for +x: U32
  {C.Nat.upto(W.U32.card(k, x), k) == True{} : Bool}

def U32.card_le(k, x):
  match k:
    case 0n:
      {==}
    case 1n+p:
      Nat.bump_le(W.U32.bit(x, p), W.U32.card(p, x), p,
        U32.card_le(p, x))

# ---------------------------------------------------------------------------
# A full count means every bit is set; a zero count means none is.
# ---------------------------------------------------------------------------

# The top bit of a range, and whether an index is that bit, as functions of
# the range so they can be carried as parameters through the induction --
# Bend matches parameters, not computed values, and has no mutual recursion.
def U32.top_bit(k: Nat, +x: U32) -> Bool:
  match k:
    case 0n:
      False{}
    case 1n+p:
      W.U32.bit(x, p)

def U32.top_eq(k: Nat, +j: Nat) -> Bool:
  match k:
    case 0n:
      False{}
    case 1n+p:
      Nat.is_eq(j, p)

law U32.card_full:
  for +k: Nat
  for +x: U32
  for +full: {W.U32.card(k, x) == k : Nat}
  for +j: Nat
  for +ok: {C.Nat.gt(k, j) == True{} : Bool}
  for +tb: Bool
  for +etb: {tb == U32.top_bit(k, x) : Bool}
  for +q: Bool
  for +eq: {q == U32.top_eq(k, j) : Bool}
  {W.U32.bit(x, j) == True{} : Bool}

def Nat.upto_at(+k: Nat, a: Nat) -> Bool:
  C.Nat.upto(a, k)

# With the top bit clear the count of the range is the count of the rest.
law U32.card_full.top:
  for +p: Nat
  for +x: U32
  for +full: {W.U32.card(1n+p, x) == 1n+p : Nat}
  for +etb: {False{} == W.U32.bit(x, p) : Bool}
  {W.U32.card(p, x) == 1n+p : Nat}

# With it set, the rest counted exactly `p`.
law U32.card_full.rest:
  for +p: Nat
  for +x: U32
  for +full: {W.U32.card(1n+p, x) == 1n+p : Nat}
  for +etb: {True{} == W.U32.bit(x, p) : Bool}
  {W.U32.card(p, x) == p : Nat}

def U32.bump_at(+a: Nat, b: Bool) -> Nat:
  W.U32.bump(b, a)

def U32.card_full.top(p, x, full, etb):
  Equal.trans(Nat, W.U32.card(p, x),
    W.U32.bump(W.U32.bit(x, p), W.U32.card(p, x)), 1n+p,
    Equal.cong(Bool, Nat, U32.bump_at(W.U32.card(p, x)), False{},
      W.U32.bit(x, p), etb),
    full)

def U32.card_full.rest(p, x, full, etb):
  Ij.Nat.succ_inj(W.U32.card(p, x), p,
    Equal.trans(Nat, 1n+W.U32.card(p, x),
      W.U32.card(1n+p, x), 1n+p,
      Equal.cong(Bool, Nat, U32.bump_at(W.U32.card(p, x)), True{},
        W.U32.bit(x, p), etb),
      full))

# Not the top bit, so strictly below it.
law U32.card_full.below:
  for +p: Nat
  for +j: Nat
  for +ok: {C.Nat.gt(1n+p, j) == True{} : Bool}
  for +eq: {False{} == Nat.is_eq(j, p) : Bool}
  {C.Nat.gt(p, j) == True{} : Bool}

def U32.card_full.below(p, j, ok, eq):
  %E.Bool.sym(False{}, Nat.is_eq(j, p), eq)
    : {Bool.or(_, C.Nat.gt(p, j)) == True{} : Bool}
  Nat.gt_split(p, j, ok)

def U32.card_full(k, x, full, j, ok, tb, etb, q, eq):
  match k:
    case 0n:
      E.Bool.noconf({W.U32.bit(x, j) == True{} : Bool}, ok)
    case 1n+p:
      match tb:
        case False{}:
          # The top bit is clear, so the rest would have to count `1n+p` on
          # its own, which is one more than it has room for.
          Empty.absurd({W.U32.bit(x, j) == True{} : Bool},
            Nat.upto_succ_absurd(p,
              Equal.trans(Bool, C.Nat.upto(1n+p, p),
                C.Nat.upto(W.U32.card(p, x), p), True{},
                Equal.cong(Nat, Bool, Nat.upto_at(p), 1n+p,
                  W.U32.card(p, x),
                  E.Nat.sym(W.U32.card(p, x), 1n+p,
                    U32.card_full.top(p, x, full, etb))),
                U32.card_le(p, x))))
        case True{}:
          match q:
            case True{}:
              %E.Nat.sym(j, p, Lf.Nat.is_eq_reflect(j, p,
                E.Bool.sym(True{}, Nat.is_eq(j, p), eq)))
                : {W.U32.bit(x, _) == True{} : Bool}
              E.Bool.sym(True{}, W.U32.bit(x, p), etb)
            case False{}:
              U32.card_full(p, x,
                U32.card_full.rest(p, x, full, etb), j,
                U32.card_full.below(p, j, ok, eq),
                U32.top_bit(p, x), {==}, U32.top_eq(p, j), {==})

# ---------------------------------------------------------------------------
# A zero count means no bit is set. Easier than the full case: a set bit would
# make the count at least one.
# ---------------------------------------------------------------------------

law U32.bump_zero_bit:
  for +b: Bool
  for +a: Nat
  for +z: {W.U32.bump(b, a) == 0n : Nat}
  {b == False{} : Bool}

def U32.bump_zero_bit(b, a, z):
  match b:
    case False{}:
      {==}
    case True{}:
      Ij.Nat.noconf({True{} == False{} : Bool}, a,
        E.Nat.sym(1n+a, 0n, z))

law U32.bump_zero_rest:
  for +b: Bool
  for +a: Nat
  for +z: {W.U32.bump(b, a) == 0n : Nat}
  {a == 0n : Nat}

def U32.bump_zero_rest(b, a, z):
  match b:
    case False{}:
      z
    case True{}:
      Ij.Nat.noconf({a == 0n : Nat}, a, E.Nat.sym(1n+a, 0n, z))

law U32.card_zero:
  for +k: Nat
  for +x: U32
  for +z: {W.U32.card(k, x) == 0n : Nat}
  for +j: Nat
  for +ok: {C.Nat.gt(k, j) == True{} : Bool}
  for +q: Bool
  for +eq: {q == U32.top_eq(k, j) : Bool}
  {W.U32.bit(x, j) == False{} : Bool}

def U32.card_zero(k, x, z, j, ok, q, eq):
  match k:
    case 0n:
      E.Bool.noconf({W.U32.bit(x, j) == False{} : Bool}, ok)
    case 1n+p:
      match q:
        case True{}:
          %E.Nat.sym(j, p, Lf.Nat.is_eq_reflect(j, p,
            E.Bool.sym(True{}, Nat.is_eq(j, p), eq)))
            : {W.U32.bit(x, _) == False{} : Bool}
          U32.bump_zero_bit(W.U32.bit(x, p), W.U32.card(p, x), z)
        case False{}:
          U32.card_zero(p, x,
            U32.bump_zero_rest(W.U32.bit(x, p), W.U32.card(p, x), z), j,
            U32.card_full.below(p, j, ok, eq),
            U32.top_eq(p, j), {==})

# ---------------------------------------------------------------------------
# The tile. `Words.count` accumulates, so the first step is to say what the
# accumulator holds; after that the sum decomposes word by word.
# ---------------------------------------------------------------------------

law Words.count_go:
  for +ws: List<&2, U32>
  for +acc: Nat
  {Wo.Words.count.go(ws, acc)
    == Nat.add(Wo.Words.count(ws), acc) : Nat}

# The accumulator, moved out of the loop. `pc` stays abstract: unfolding a
# popcount here would print a page of shifts and prove nothing.
law Words.count_go.step:
  for +t: List<&2, U32>
  for +acc: Nat
  for +pc: Nat
  for +ih1: {Wo.Words.count.go(t, Nat.add(pc, acc))
    == Nat.add(Wo.Words.count(t), Nat.add(pc, acc)) : Nat}
  for +ih2: {Wo.Words.count.go(t, Nat.add(pc, 0n))
    == Nat.add(Wo.Words.count(t), Nat.add(pc, 0n)) : Nat}
  {Wo.Words.count.go(t, Nat.add(pc, acc))
    == Nat.add(Wo.Words.count.go(t, Nat.add(pc, 0n)), acc) : Nat}

def Nat.at_add(+c: Nat, a: Nat) -> Nat:
  Nat.add(c, a)

def Nat.add_at(+acc: Nat, a: Nat) -> Nat:
  Nat.add(a, acc)

def Words.count_go.step(t, acc, pc, ih1, ih2):
  Equal.trans(Nat, Wo.Words.count.go(t, Nat.add(pc, acc)),
    Nat.add(Nat.add(Wo.Words.count(t), pc), acc),
    Nat.add(Wo.Words.count.go(t, Nat.add(pc, 0n)), acc),
    Equal.trans(Nat, Wo.Words.count.go(t, Nat.add(pc, acc)),
      Nat.add(Wo.Words.count(t), Nat.add(pc, acc)),
      Nat.add(Nat.add(Wo.Words.count(t), pc), acc),
      ih1,
      E.Nat.sym(Nat.add(Nat.add(Wo.Words.count(t), pc), acc),
        Nat.add(Wo.Words.count(t), Nat.add(pc, acc)),
        N.Nat.add_assoc(Wo.Words.count(t), pc, acc))),
    Equal.cong(Nat, Nat, Nat.add_at(acc),
      Nat.add(Wo.Words.count(t), pc),
      Wo.Words.count.go(t, Nat.add(pc, 0n)),
      E.Nat.sym(Wo.Words.count.go(t, Nat.add(pc, 0n)),
        Nat.add(Wo.Words.count(t), pc),
        Equal.trans(Nat, Wo.Words.count.go(t, Nat.add(pc, 0n)),
          Nat.add(Wo.Words.count(t), Nat.add(pc, 0n)),
          Nat.add(Wo.Words.count(t), pc),
          ih2,
          Equal.cong(Nat, Nat, Nat.at_add(Wo.Words.count(t)),
            Nat.add(pc, 0n), pc, N.Nat.add_zero(pc))))))

def Words.count_go(ws, acc):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      Words.count_go.step(t, acc, W.U32.popcount(w),
        Words.count_go(t, Nat.add(W.U32.popcount(w), acc)),
        Words.count_go(t, Nat.add(W.U32.popcount(w), 0n)))

law Words.count_cons:
  for +w: U32
  for +t: List<&2, U32>
  {Wo.Words.count(Con{w, t})
    == Nat.add(Wo.Words.count(t), W.U32.popcount(w)) : Nat}

def Words.count_cons(w, t):
  Equal.trans(Nat, Wo.Words.count(Con{w, t}),
    Nat.add(Wo.Words.count(t), Nat.add(W.U32.popcount(w), 0n)),
    Nat.add(Wo.Words.count(t), W.U32.popcount(w)),
    Words.count_go(t, Nat.add(W.U32.popcount(w), 0n)),
    Equal.cong(Nat, Nat, Nat.at_add(Wo.Words.count(t)),
      Nat.add(W.U32.popcount(w), 0n), W.U32.popcount(w),
      N.Nat.add_zero(W.U32.popcount(w))))

# ---------------------------------------------------------------------------
# Arithmetic: adding preserves order, and a sum that matches a larger sum
# term by term must match in each term.
# ---------------------------------------------------------------------------

law Nat.upto_add_r:
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for +ok: {C.Nat.upto(b, d) == True{} : Bool}
  {C.Nat.upto(b, Nat.add(c, d)) == True{} : Bool}

def Nat.upto_add_r(b, c, d, ok):
  match c:
    case 0n:
      ok
    case 1n+q:
      Nat.upto_succ_r(b, Nat.add(q, d), Nat.upto_add_r(b, q, d, ok))

law Nat.add_mono:
  for +a: Nat
  for +c: Nat
  for +b: Nat
  for +d: Nat
  for +ac: {C.Nat.upto(a, c) == True{} : Bool}
  for +bd: {C.Nat.upto(b, d) == True{} : Bool}
  {C.Nat.upto(Nat.add(a, b), Nat.add(c, d)) == True{} : Bool}

def Nat.add_mono(a, c, b, d, ac, bd):
  match a:
    case 0n:
      Nat.upto_add_r(b, c, d, bd)
    case 1n+p:
      match c:
        case 0n:
          E.Bool.noconf({C.Nat.upto(Nat.add(1n+p, b), Nat.add(0n, d))
            == True{} : Bool}, ac)
        case 1n+q:
          Nat.add_mono(p, q, b, d, ac, bd)

law Nat.upto_add_absurd:
  for +q: Nat
  for +d: Nat
  for +ok: {C.Nat.upto(1n+Nat.add(q, d), d) == True{} : Bool}
  {Empty : Type}

law Nat.upto_add_absurd.shift:
  for +q: Nat
  for +e: Nat
  for +ok: {C.Nat.upto(1n+Nat.add(q, 1n+e), 1n+e) == True{} : Bool}
  {C.Nat.upto(1n+Nat.add(q, e), e) == True{} : Bool}

def Nat.upto_add_absurd.shift(q, e, ok):
  %N.Nat.add_succ(q, e)
    : {C.Nat.upto(_, e) == True{} : Bool}
  ok

def Nat.upto_add_absurd(q, d, ok):
  match d:
    case 0n:
      E.Bool.empty(ok)
    case 1n+e:
      Nat.upto_add_absurd(q, e,
        Nat.upto_add_absurd.shift(q, e, ok))

law Nat.add_cancel:
  for +a: Nat
  for +c: Nat
  for +b: Nat
  for +d: Nat
  for +e: {Nat.add(a, b) == Nat.add(c, d) : Nat}
  for +ac: {C.Nat.upto(a, c) == True{} : Bool}
  for +bd: {C.Nat.upto(b, d) == True{} : Bool}
  {a == c : Nat}

law Nat.add_cancel.bound:
  for +q: Nat
  for +b: Nat
  for +d: Nat
  for +e: {b == Nat.add(1n+q, d) : Nat}
  for +bd: {C.Nat.upto(b, d) == True{} : Bool}
  {C.Nat.upto(1n+Nat.add(q, d), d) == True{} : Bool}

def Nat.add_cancel.bound(q, b, d, e, bd):
  %e : {C.Nat.upto(_, d) == True{} : Bool}
  bd

def Nat.add_cancel(a, c, b, d, e, ac, bd):
  match a:
    case 0n:
      match c:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({0n == 1n+q : Nat},
            Nat.upto_add_absurd(q, d,
              Nat.add_cancel.bound(q, b, d, e, bd)))
    case 1n+p:
      match c:
        case 0n:
          E.Bool.noconf({1n+p == 0n : Nat}, ac)
        case 1n+q:
          %Nat.add_cancel(p, q, b, d,
            Ij.Nat.succ_inj(Nat.add(p, b), Nat.add(q, d), e), ac, bd)
            : {1n+p == 1n+_ : Nat}
          {==}

# ---------------------------------------------------------------------------
# A tile of n words holds at most 32n bits.
# ---------------------------------------------------------------------------

law Nat.dbl_add:
  for +k: Nat
  for +a: Nat
  for +b: Nat
  {Sp.Nat.dbl(k, Nat.add(a, b))
    == Nat.add(Sp.Nat.dbl(k, a), Sp.Nat.dbl(k, b)) : Nat}

def Nat.dbl_add(k, a, b):
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(Nat, Nat.double(Sp.Nat.dbl(j, Nat.add(a, b))),
        Nat.double(Nat.add(Sp.Nat.dbl(j, a), Sp.Nat.dbl(j, b))),
        Nat.add(Nat.double(Sp.Nat.dbl(j, a)), Nat.double(Sp.Nat.dbl(j, b))),
        Equal.cong(Nat, Nat, Nat.double, Sp.Nat.dbl(j, Nat.add(a, b)),
          Nat.add(Sp.Nat.dbl(j, a), Sp.Nat.dbl(j, b)), Nat.dbl_add(j, a, b)),
        Sp.Nat.double_add(Sp.Nat.dbl(j, a), Sp.Nat.dbl(j, b)))

law U32.popcount_le:
  for +w: U32
  {C.Nat.upto(W.U32.popcount(w), 32n) == True{} : Bool}

def U32.popcount_le(w):
  %E.Nat.sym(W.U32.popcount(w), W.U32.card(32n, w),
    PP.U32.popcount_spec(w))
    : {C.Nat.upto(_, 32n) == True{} : Bool}
  U32.card_le(32n, w)

law Words.count_le:
  for +ws: List<&2, U32>
  {C.Nat.upto(Wo.Words.count(ws),
    Sp.Nat.dbl(5n, List.length(&2, U32, ws))) == True{} : Bool}

def Words.count_le(ws):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      %E.Nat.sym(Wo.Words.count(Con{w, t}),
        Nat.add(Wo.Words.count(t), W.U32.popcount(w)),
        Words.count_cons(w, t))
        : {C.Nat.upto(_, Sp.Nat.dbl(5n, 1n+List.length(&2, U32, t)))
          == True{} : Bool}
      %E.Nat.sym(Sp.Nat.dbl(5n, Nat.add(1n, List.length(&2, U32, t))),
        Nat.add(Sp.Nat.dbl(5n, 1n),
          Sp.Nat.dbl(5n, List.length(&2, U32, t))),
        Nat.dbl_add(5n, 1n, List.length(&2, U32, t)))
        : {C.Nat.upto(Nat.add(Wo.Words.count(t), W.U32.popcount(w)), _)
          == True{} : Bool}
      %N.Nat.add_comm(Sp.Nat.dbl(5n, List.length(&2, U32, t)), 32n)
        : {C.Nat.upto(Nat.add(Wo.Words.count(t), W.U32.popcount(w)), _)
          == True{} : Bool}
      Nat.add_mono(Wo.Words.count(t),
        Sp.Nat.dbl(5n, List.length(&2, U32, t)),
        W.U32.popcount(w), 32n, Words.count_le(t), U32.popcount_le(w))

# ---------------------------------------------------------------------------
# So a tile whose count reaches its capacity has every bit set, and one whose
# count is zero has none.
# ---------------------------------------------------------------------------

law Words.count_full:
  for +ws: List<&2, U32>
  for +full: {Wo.Words.count(ws)
    == Sp.Nat.dbl(5n, List.length(&2, U32, ws)) : Nat}
  for +i: Nat
  for +iok: {C.Nat.gt(List.length(&2, U32, ws), i) == True{} : Bool}
  for +b: Nat
  for +bok: {C.Nat.gt(32n, b) == True{} : Bool}
  {Wo.Words.at(ws, i, b) == True{} : Bool}

# The head word is full: the whole tile reached its capacity, the tail can at
# most reach its own, and a sum cannot exceed its parts.
law Words.count_full.head:
  for +w: U32
  for +t: List<&2, U32>
  for +full: {Wo.Words.count(Con{w, t})
    == Sp.Nat.dbl(5n, 1n+List.length(&2, U32, t)) : Nat}
  {W.U32.card(32n, w) == 32n : Nat}

law Words.count_full.sum:
  for +w: U32
  for +t: List<&2, U32>
  for +full: {Wo.Words.count(Con{w, t})
    == Sp.Nat.dbl(5n, 1n+List.length(&2, U32, t)) : Nat}
  {Nat.add(W.U32.popcount(w), Wo.Words.count(t))
    == Nat.add(32n, Sp.Nat.dbl(5n, List.length(&2, U32, t))) : Nat}

def Words.count_full.sum(w, t, full):
  Equal.trans(Nat, Nat.add(W.U32.popcount(w), Wo.Words.count(t)),
    Wo.Words.count(Con{w, t}),
    Nat.add(32n, Sp.Nat.dbl(5n, List.length(&2, U32, t))),
    Equal.trans(Nat, Nat.add(W.U32.popcount(w), Wo.Words.count(t)),
      Nat.add(Wo.Words.count(t), W.U32.popcount(w)),
      Wo.Words.count(Con{w, t}),
      N.Nat.add_comm(W.U32.popcount(w), Wo.Words.count(t)),
      E.Nat.sym(Wo.Words.count(Con{w, t}),
        Nat.add(Wo.Words.count(t), W.U32.popcount(w)),
        Words.count_cons(w, t))),
    full)

def Words.count_full.head(w, t, full):
  %PP.U32.popcount_spec(w)
    : {_ == 32n : Nat}
  Nat.add_cancel(W.U32.popcount(w), 32n, Wo.Words.count(t),
    Sp.Nat.dbl(5n, List.length(&2, U32, t)),
    Words.count_full.sum(w, t, full), U32.popcount_le(w),
    Words.count_le(t))

law Words.count_full.tail:
  for +w: U32
  for +t: List<&2, U32>
  for +full: {Wo.Words.count(Con{w, t})
    == Sp.Nat.dbl(5n, 1n+List.length(&2, U32, t)) : Nat}
  {Wo.Words.count(t)
    == Sp.Nat.dbl(5n, List.length(&2, U32, t)) : Nat}

def Words.count_full.tail(w, t, full):
  Nat.add_cancel(Wo.Words.count(t),
    Sp.Nat.dbl(5n, List.length(&2, U32, t)), W.U32.popcount(w), 32n,
    Equal.trans(Nat, Nat.add(Wo.Words.count(t), W.U32.popcount(w)),
      Wo.Words.count(Con{w, t}),
      Nat.add(Sp.Nat.dbl(5n, List.length(&2, U32, t)), 32n),
      E.Nat.sym(Wo.Words.count(Con{w, t}),
        Nat.add(Wo.Words.count(t), W.U32.popcount(w)),
        Words.count_cons(w, t)),
      Equal.trans(Nat, Wo.Words.count(Con{w, t}),
        Nat.add(32n, Sp.Nat.dbl(5n, List.length(&2, U32, t))),
        Nat.add(Sp.Nat.dbl(5n, List.length(&2, U32, t)), 32n),
        full,
        N.Nat.add_comm(32n, Sp.Nat.dbl(5n, List.length(&2, U32, t))))),
    Words.count_le(t), U32.popcount_le(w))

def Words.count_full(ws, full, i, iok, b, bok):
  match ws:
    case Nil{}:
      E.Bool.noconf({Wo.Words.at(Nil{}, i, b) == True{} : Bool}, iok)
    case Con{w, t}:
      match i:
        case 0n:
          Equal.trans(Bool, Wo.U32.test(w, b), W.U32.bit(w, b), True{},
            PB.U32.test_spec(w, b),
            U32.card_full(32n, w,
              Words.count_full.head(w, t, full), b, bok,
              U32.top_bit(32n, w), {==}, U32.top_eq(32n, b), {==}))
        case 1n+j:
          Words.count_full(t, Words.count_full.tail(w, t, full), j, iok,
            b, bok)

law Words.count_zero:
  for +ws: List<&2, U32>
  for +z: {Wo.Words.count(ws) == 0n : Nat}
  for +i: Nat
  for +b: Nat
  for +bok: {C.Nat.gt(32n, b) == True{} : Bool}
  {Wo.Words.at(ws, i, b) == False{} : Bool}

law Nat.add_zero_left:
  for +a: Nat
  for +b: Nat
  for +z: {Nat.add(a, b) == 0n : Nat}
  {a == 0n : Nat}

def Nat.add_zero_left(a, b, z):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Ij.Nat.noconf({1n+p == 0n : Nat}, Nat.add(p, b),
        E.Nat.sym(1n+Nat.add(p, b), 0n, z))

law Nat.add_zero_right:
  for +a: Nat
  for +b: Nat
  for +z: {Nat.add(a, b) == 0n : Nat}
  {b == 0n : Nat}

def Nat.add_zero_right(a, b, z):
  match a:
    case 0n:
      z
    case 1n+p:
      Ij.Nat.noconf({b == 0n : Nat}, Nat.add(p, b),
        E.Nat.sym(1n+Nat.add(p, b), 0n, z))

law Words.count_zero.head:
  for +w: U32
  for +t: List<&2, U32>
  for +z: {Wo.Words.count(Con{w, t}) == 0n : Nat}
  {W.U32.card(32n, w) == 0n : Nat}

law Words.count_zero.sum:
  for +w: U32
  for +t: List<&2, U32>
  for +z: {Wo.Words.count(Con{w, t}) == 0n : Nat}
  {Nat.add(Wo.Words.count(t), W.U32.popcount(w)) == 0n : Nat}

def Words.count_zero.sum(w, t, z):
  Equal.trans(Nat, Nat.add(Wo.Words.count(t), W.U32.popcount(w)),
    Wo.Words.count(Con{w, t}), 0n,
    E.Nat.sym(Wo.Words.count(Con{w, t}),
      Nat.add(Wo.Words.count(t), W.U32.popcount(w)),
      Words.count_cons(w, t)),
    z)

def Words.count_zero.head(w, t, z):
  %PP.U32.popcount_spec(w)
    : {_ == 0n : Nat}
  Nat.add_zero_right(Wo.Words.count(t), W.U32.popcount(w),
    Words.count_zero.sum(w, t, z))

law Words.count_zero.tail:
  for +w: U32
  for +t: List<&2, U32>
  for +z: {Wo.Words.count(Con{w, t}) == 0n : Nat}
  {Wo.Words.count(t) == 0n : Nat}

def Words.count_zero.tail(w, t, z):
  Nat.add_zero_left(Wo.Words.count(t), W.U32.popcount(w),
    Words.count_zero.sum(w, t, z))

def Words.count_zero(ws, z, i, b, bok):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      match i:
        case 0n:
          Equal.trans(Bool, Wo.U32.test(w, b), W.U32.bit(w, b), False{},
            PB.U32.test_spec(w, b),
            U32.card_zero(32n, w, Words.count_zero.head(w, t, z), b, bok,
              U32.top_eq(32n, b), {==}))
        case 1n+j:
          Words.count_zero(t, Words.count_zero.tail(w, t, z), j, b, bok)
