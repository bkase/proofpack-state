# proofs/descend.bend -- carrying an ordinal down one level of the tree.
#
# This is addressing fact A2 from LAWS.pending.bend, and it is what every
# obligation that descends the set tree was waiting on. `PSet.mem`, `PSet.add`
# and the node operations all split an interval by comparing the ordinal with
# the half-width `h` and, in the upper half, rebasing by `x - h`. For the
# descent to preserve "the ordinal is inside this interval", `x - h` has to be
# subtraction, and the result has to land inside the child.
#
# The half-width is never an arbitrary number: `PSet.half(d)` is
# `U32.shln(1, 11n+d)`, a single set bit. That is what makes this tractable.
# For a power of two the whole question is bitwise, with no arithmetic on
# `Nat` anywhere:
#
#   * `x < 2^k` is exactly "every bit of `x` from `k` up is zero";
#   * `x - 2^k`, when bit `k` of `x` is set, is `x` with bit `k` cleared.
#
# Both are inductions down the bit vector. The second is the one that looks
# hard and is not: `Word.sub` is `Word.adc` with the borrow flag set, and for
# a subtrahend that is a single bit the carry is `True{}` at every position,
# so each output bit is the input bit except at `k`.

import Base
import ./eq.bend as E
import ../core/count.bend as C
import ../core/word.bend as W

# ---------------------------------------------------------------------------
# The two shapes this file is about: a word with one bit set, and a word with
# that bit cleared.
# ---------------------------------------------------------------------------

def Word.zeros(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{False{}, Word.zeros(p)}

def Word.pow2(n: Nat, k: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match k:
        case 0n:
          WCon{True{}, Word.zeros(p)}
        case 1n+j:
          WCon{False{}, Word.pow2(p, j)}

def Word.clear(n: Nat, w: Word(n), k: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match k:
            case 0n:
              WCon{False{}, t}
            case 1n+j:
              WCon{b, Word.clear(p, t, j)}

# ---------------------------------------------------------------------------
# Subtracting zero with the borrow flag set is the identity: `adc` with
# `f = True{}` computes `a + ~b + c`, and with `b` zero that is
# `a + (2^n - 1) + 1`, which is `a` again in `n` bits. Each step is
# `full_add(ab, True{}, True{}) = (ab, True{})`, so the carry never changes
# and no bit does either.
# ---------------------------------------------------------------------------

law Word.adc_sub_zero:
  for +n: Nat
  for +a: Word(n)
  {Word.adc(n, a, Word.zeros(n), True{}, True{}) == a : Word(n)}

# One step of that, with the head bit taken as a parameter so it can be
# matched: whatever the bit is, a borrow-in of `True{}` against a zero bit
# reproduces it and passes the borrow on.
law Word.adc_con_keep:
  for +p: Nat
  for +at: Word(p)
  for +ab: Bool
  {Word.adc.con(p, at, Word.zeros(p), True{},
      Bool.full_add(ab, Bool.not(False{}), True{}))
    == WCon{ab, Word.adc(p, at, Word.zeros(p), True{}, True{})}
    : Word(1n+p)}

def Word.adc_con_keep(p, at, ab):
  match ab:
    case False{}:
      {==}
    case True{}:
      {==}

def Word.adc_sub_zero(n, a):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{ab, at}:
          %Word.adc_sub_zero(p, at)
            : {Word.adc.con(p, at, Word.zeros(p), True{},
                Bool.full_add(ab, Bool.not(False{}), True{}))
              == WCon{ab, _} : Word(1n+p)}
          Word.adc_con_keep(p, at, ab)

# ---------------------------------------------------------------------------
# Subtracting a single set bit clears it.
#
# At every position below `k` the subtrahend's bit is zero, so
# `full_add(ab, True{}, True{})` reproduces the bit and keeps the borrow. At
# `k` the subtrahend's bit is one, so `full_add(ab, False{}, True{})` gives
# `(not ab, ab)` -- and because bit `k` of `x` is set, that is `(False{},
# True{})`: the bit clears and the borrow still goes on. Above `k` it is the
# first case again.
# ---------------------------------------------------------------------------

law Word.adc_head_sub:
  for +p: Nat
  for +at: Word(p)
  for +bt: Word(p)
  for +ab: Bool
  {Word.adc.con(p, at, bt, True{},
      Bool.full_add(ab, Bool.not(False{}), True{}))
    == WCon{ab, Word.adc(p, at, bt, True{}, True{})} : Word(1n+p)}

def Word.adc_head_sub(p, at, bt, ab):
  match ab:
    case False{}:
      {==}
    case True{}:
      {==}

law Word.sub_pow2:
  for +n: Nat
  for +k: Nat
  for +x: Word(n)
  for +bitk: {W.Word.get(n, x, k) == True{} : Bool}
  {Word.adc(n, x, Word.pow2(n, k), True{}, True{})
    == Word.clear(n, x, k) : Word(n)}

def Word.sub_pow2(n, k, x, bitk):
  match n:
    case 0n:
      match x:
        case WNil{}:
          {==}
    case 1n+p:
      match k:
        case 0n:
          match x:
            case WCon{ab, at}:
              # The bit being cleared is this one, and `bitk` says it is set.
              %E.Bool.sym(ab, True{}, bitk)
                : {Word.adc.con(p, at, Word.zeros(p), True{},
                    Bool.full_add(_, Bool.not(True{}), True{}))
                  == WCon{False{}, at} : Word(1n+p)}
              %Equal.sym(Word(p),
                Word.adc(p, at, Word.zeros(p), True{}, True{}), at,
                Word.adc_sub_zero(p, at))
                : {WCon{False{}, _} == WCon{False{}, at} : Word(1n+p)}
              {==}
        case 1n+j:
          match x:
            case WCon{ab, at}:
              %Word.sub_pow2(p, j, at, bitk)
                : {Word.adc.con(p, at, Word.pow2(p, j), True{},
                    Bool.full_add(ab, Bool.not(False{}), True{}))
                  == WCon{ab, _} : Word(1n+p)}
              Word.adc_head_sub(p, at, Word.pow2(p, j), ab)

# ---------------------------------------------------------------------------
# `x < 2^k` is exactly "every bit from `k` up is zero".
#
# `Word.cmp` compares the high bits first with the low bit as the tiebreak, so
# this is an induction down the vector against the shape of `Word.pow2`.
# It needs `k < n`: with `n` bits there is no `2^n` to compare against, and
# `Word.pow2(n, k)` for `k` at or past `n` is zero, which is a different
# question.
# ---------------------------------------------------------------------------

def Word.hi_zero(n: Nat, w: Word(n), k: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match k:
            case 0n:
              Bool.and(Bool.not(b), Word.hi_zero(p, t, 0n))
            case 1n+j:
              Word.hi_zero(p, t, j)

law Cmp.is_lt_fin_false:
  for +c: Cmp
  for +ab: Bool
  {Cmp.is_lt(Word.cmp.fin(ab, False{}, c)) == Cmp.is_lt(c) : Bool}

def Cmp.is_lt_fin_false(c, ab):
  match c:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      match ab:
        case False{}:
          {==}
        case True{}:
          {==}

law Cmp.is_eq_fin_false:
  for +c: Cmp
  for +ab: Bool
  {Cmp.is_eq(Word.cmp.fin(ab, False{}, c))
    == Bool.and(Bool.not(ab), Cmp.is_eq(c)) : Bool}

def Cmp.is_eq_fin_false(c, ab):
  match c:
    case LT{}:
      match ab:
        case False{}:
          {==}
        case True{}:
          {==}
    case GT{}:
      match ab:
        case False{}:
          {==}
        case True{}:
          {==}
    case EQ{}:
      match ab:
        case False{}:
          {==}
        case True{}:
          {==}

law Cmp.is_lt_fin_true:
  for +c: Cmp
  for +ab: Bool
  {Cmp.is_lt(Word.cmp.fin(ab, True{}, c))
    == Bool.or(Cmp.is_lt(c), Bool.and(Bool.not(ab), Cmp.is_eq(c)))
    : Bool}

def Cmp.is_lt_fin_true(c, ab):
  match c:
    case LT{}:
      match ab:
        case False{}:
          {==}
        case True{}:
          {==}
    case GT{}:
      match ab:
        case False{}:
          {==}
        case True{}:
          {==}
    case EQ{}:
      match ab:
        case False{}:
          {==}
        case True{}:
          {==}

law Word.is_lt_zeros:
  for +n: Nat
  for +a: Word(n)
  {Cmp.is_lt(Word.cmp(n, a, Word.zeros(n))) == False{} : Bool}

def Word.is_lt_zeros(n, a):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{ab, at}:
          %Word.is_lt_zeros(p, at)
            : {Cmp.is_lt(Word.cmp.fin(ab, False{}, Word.cmp(p, at,
                Word.zeros(p)))) == _ : Bool}
          Cmp.is_lt_fin_false(Word.cmp(p, at, Word.zeros(p)), ab)

law Word.is_eq_zeros:
  for +n: Nat
  for +a: Word(n)
  {Cmp.is_eq(Word.cmp(n, a, Word.zeros(n)))
    == Word.hi_zero(n, a, 0n) : Bool}

def Word.is_eq_zeros(n, a):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{ab, at}:
          %Word.is_eq_zeros(p, at)
            : {Cmp.is_eq(Word.cmp.fin(ab, False{}, Word.cmp(p, at,
                Word.zeros(p)))) == Bool.and(Bool.not(ab), _) : Bool}
          Cmp.is_eq_fin_false(Word.cmp(p, at, Word.zeros(p)), ab)

law Word.is_lt_pow2:
  for +n: Nat
  for +k: Nat
  for +x: Word(n)
  for +ok: {C.Nat.gt(n, k) == True{} : Bool}
  {Cmp.is_lt(Word.cmp(n, x, Word.pow2(n, k)))
    == Word.hi_zero(n, x, k) : Bool}

law Word.is_lt_pow2.one:
  for +ab: Bool
  for +z: Bool
  {Bool.or(False{}, Bool.and(Bool.not(ab), z))
    == Bool.and(Bool.not(ab), z) : Bool}

def Word.is_lt_pow2.one(ab, z):
  match ab:
    case False{}:
      {==}
    case True{}:
      {==}

def Word.is_lt_pow2(n, k, x, ok):
  match n:
    case 0n:
      E.Bool.noconf({Cmp.is_lt(Word.cmp(0n, x, Word.pow2(0n, k)))
        == Word.hi_zero(0n, x, k) : Bool}, ok)
    case 1n+p:
      match k:
        case 0n:
          match x:
            case WCon{ab, at}:
              # Comparing against 1: smaller exactly when every bit is
              # zero. The tail can never be less than zero, and it is equal
              # to zero exactly when it has no bits, so the whole comparison
              # comes down to the low bit and that.
              %E.Bool.sym(
                Cmp.is_lt(Word.cmp.fin(ab, True{},
                  Word.cmp(p, at, Word.zeros(p)))),
                Bool.or(Cmp.is_lt(Word.cmp(p, at, Word.zeros(p))),
                  Bool.and(Bool.not(ab),
                    Cmp.is_eq(Word.cmp(p, at, Word.zeros(p))))),
                Cmp.is_lt_fin_true(Word.cmp(p, at, Word.zeros(p)), ab))
                : {_ == Bool.and(Bool.not(ab), Word.hi_zero(p, at, 0n))
                  : Bool}
              %E.Bool.sym(Cmp.is_lt(Word.cmp(p, at, Word.zeros(p))),
                False{}, Word.is_lt_zeros(p, at))
                : {Bool.or(_, Bool.and(Bool.not(ab),
                    Cmp.is_eq(Word.cmp(p, at, Word.zeros(p)))))
                  == Bool.and(Bool.not(ab), Word.hi_zero(p, at, 0n))
                  : Bool}
              %E.Bool.sym(Cmp.is_eq(Word.cmp(p, at, Word.zeros(p))),
                Word.hi_zero(p, at, 0n), Word.is_eq_zeros(p, at))
                : {Bool.or(False{}, Bool.and(Bool.not(ab), _))
                  == Bool.and(Bool.not(ab), Word.hi_zero(p, at, 0n))
                  : Bool}
              Word.is_lt_pow2.one(ab, Word.hi_zero(p, at, 0n))
        case 1n+j:
          match x:
            case WCon{ab, at}:
              %Word.is_lt_pow2(p, j, at, ok)
                : {Cmp.is_lt(Word.cmp.fin(ab, False{},
                    Word.cmp(p, at, Word.pow2(p, j)))) == _ : Bool}
              Cmp.is_lt_fin_false(Word.cmp(p, at, Word.pow2(p, j)), ab)

# ---------------------------------------------------------------------------
# The bridge: `PSet.half(d)` is `U32.shln(1, 11n+d)`, and that is the word
# with one bit set. Shifting left moves the bit up, which is the whole
# argument.
# ---------------------------------------------------------------------------

def Word.sym(-n: Nat, -a: Word(n), -b: Word(n), e: {a == b : Word(n)})
  -> {b == a : Word(n)}:
  Equal.sym(Word(n), a, b, e)

law Word.shl_put_zeros:
  for +n: Nat
  {Word.shl.put(n, False{}, Word.zeros(n)) == Word.zeros(n) : Word(n)}

def Word.shl_put_zeros(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Word.sym(p, Word.shl.put(p, False{}, Word.zeros(p)),
        Word.zeros(p), Word.shl_put_zeros(p))
        : {WCon{False{}, _} == WCon{False{}, Word.zeros(p)} : Word(1n+p)}
      {==}

law Word.shl_put_one:
  for +n: Nat
  {Word.shl.put(n, True{}, Word.zeros(n)) == Word.pow2(n, 0n) : Word(n)}

def Word.shl_put_one(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Word.sym(p, Word.shl.put(p, False{}, Word.zeros(p)),
        Word.zeros(p), Word.shl_put_zeros(p))
        : {WCon{True{}, _} == WCon{True{}, Word.zeros(p)} : Word(1n+p)}
      {==}

law Word.shl_put_pow2:
  for +n: Nat
  for +j: Nat
  {Word.shl.put(n, False{}, Word.pow2(n, j)) == Word.pow2(n, 1n+j)
    : Word(n)}

def Word.shl_put_pow2(n, j):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match j:
        case 0n:
          %Word.sym(p, Word.shl.put(p, True{}, Word.zeros(p)),
            Word.pow2(p, 0n), Word.shl_put_one(p))
            : {WCon{False{}, _} == WCon{False{}, Word.pow2(p, 0n)}
              : Word(1n+p)}
          {==}
        case 1n+i:
          %Word.sym(p, Word.shl.put(p, False{}, Word.pow2(p, i)),
            Word.pow2(p, 1n+i), Word.shl_put_pow2(p, i))
            : {WCon{False{}, _} == WCon{False{}, Word.pow2(p, 1n+i)}
              : Word(1n+p)}
          {==}

law Word.shl_pow2:
  for +n: Nat
  for +i: Nat
  {Word.shl(n, Word.pow2(n, i)) == Word.pow2(n, 1n+i) : Word(n)}

def Word.shl_pow2(n, i):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match i:
        case 0n:
          %Word.sym(p, Word.shl.put(p, True{}, Word.zeros(p)),
            Word.pow2(p, 0n), Word.shl_put_one(p))
            : {WCon{False{}, _} == WCon{False{}, Word.pow2(p, 0n)}
              : Word(1n+p)}
          {==}
        case 1n+j:
          %Word.sym(p, Word.shl.put(p, False{}, Word.pow2(p, j)),
            Word.pow2(p, 1n+j), Word.shl_put_pow2(p, j))
            : {WCon{False{}, _} == WCon{False{}, Word.pow2(p, 1n+j)}
              : Word(1n+p)}
          {==}

law U32.shln_one_pow2:
  for +k: Nat
  {U32.shln(1, k) == U32{Word.pow2(32n, k)} : U32}

def U32.shln_one_pow2(k):
  match k:
    case 0n:
      {==}
    case 1n+i:
      %E.U32.sym(U32.shln(1, i), U32{Word.pow2(32n, i)},
        U32.shln_one_pow2(i))
        : {U32.shl(_) == U32{Word.pow2(32n, 1n+i)} : U32}
      %Word.sym(32n, Word.shl(32n, Word.pow2(32n, i)),
        Word.pow2(32n, 1n+i), Word.shl_pow2(32n, i))
        : {U32{_} == U32{Word.pow2(32n, 1n+i)} : U32}
      {==}

# ---------------------------------------------------------------------------
# Halving. A node hands its child `U32.shr(h)`, and for a single set bit that
# is the bit one position down.
# ---------------------------------------------------------------------------

law Word.shr_pad_zeros:
  for +n: Nat
  {Word.shr.pad(n, Word.zeros(n)) == Word.zeros(1n+n) : Word(1n+n)}

def Word.shr_pad_zeros(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Word.sym(1n+p, Word.shr.pad(p, Word.zeros(p)), Word.zeros(1n+p),
        Word.shr_pad_zeros(p))
        : {WCon{False{}, _} == Word.zeros(2n+p) : Word(2n+p)}
      {==}

law Word.shr_pad_pow2:
  for +n: Nat
  for +k: Nat
  for +ok: {C.Nat.gt(n, k) == True{} : Bool}
  {Word.shr.pad(n, Word.pow2(n, k)) == Word.pow2(1n+n, k) : Word(1n+n)}

def Word.shr_pad_pow2(n, k, ok):
  match n:
    case 0n:
      E.Bool.noconf({Word.shr.pad(0n, Word.pow2(0n, k))
        == Word.pow2(1n, k) : Word(1n)}, ok)
    case 1n+q:
      match k:
        case 0n:
          %Word.sym(1n+q, Word.shr.pad(q, Word.zeros(q)),
            Word.zeros(1n+q), Word.shr_pad_zeros(q))
            : {WCon{True{}, _} == Word.pow2(2n+q, 0n) : Word(2n+q)}
          {==}
        case 1n+j:
          %Word.sym(1n+q, Word.shr.pad(q, Word.pow2(q, j)),
            Word.pow2(1n+q, j), Word.shr_pad_pow2(q, j, ok))
            : {WCon{False{}, _} == Word.pow2(2n+q, 1n+j) : Word(2n+q)}
          {==}

law Word.shr_pow2:
  for +n: Nat
  for +k: Nat
  for +ok: {C.Nat.gt(n, 1n+k) == True{} : Bool}
  {Word.shr(n, Word.pow2(n, 1n+k)) == Word.pow2(n, k) : Word(n)}

def Word.shr_pow2(n, k, ok):
  match n:
    case 0n:
      E.Bool.noconf({Word.shr(0n, Word.pow2(0n, 1n+k))
        == Word.pow2(0n, k) : Word(0n)}, ok)
    case 1n+p:
      Word.shr_pad_pow2(p, k, ok)

law U32.shr_shln_one:
  for +k: Nat
  for +ok: {C.Nat.gt(32n, 1n+k) == True{} : Bool}
  {U32.shr(U32.shln(1, 1n+k)) == U32.shln(1, k) : U32}

def U32.shr_shln_one(k, ok):
  %E.U32.sym(U32.shln(1, 1n+k), U32{Word.pow2(32n, 1n+k)},
    U32.shln_one_pow2(1n+k))
    : {U32.shr(_) == U32.shln(1, k) : U32}
  %E.U32.sym(U32.shln(1, k), U32{Word.pow2(32n, k)},
    U32.shln_one_pow2(k))
    : {U32{Word.shr(32n, Word.pow2(32n, 1n+k))} == _ : U32}
  %Word.sym(32n, Word.shr(32n, Word.pow2(32n, 1n+k)),
    Word.pow2(32n, k), Word.shr_pow2(32n, k, ok))
    : {U32{_} == U32{Word.pow2(32n, k)} : U32}
  {==}

# ---------------------------------------------------------------------------
# The descent, at last.
#
# `U32.hi_zero(x, k)` is "x fits in k bits", which is the invariant a node
# hands its child: at depth d a node covers 2^(12+d) ordinals, so an ordinal
# inside it fits in 12+d bits. Going down a level, the low half keeps the
# ordinal and the high half rebases it by the half-width, and either way the
# result fits in one bit fewer.
# ---------------------------------------------------------------------------

def U32.hi_zero(x: U32, k: Nat) -> Bool:
  Word.hi_zero(32n, W.U32.word(x), k)

law U32.is_lt_shln:
  for +x: U32
  for +k: Nat
  for +ok: {C.Nat.gt(32n, k) == True{} : Bool}
  {U32.is_lt(x, U32.shln(1, k)) == U32.hi_zero(x, k) : Bool}

def U32.is_lt_shln(x, k, ok):
  match x:
    case U32{w}:
      %E.U32.sym(U32.shln(1, k), U32{Word.pow2(32n, k)},
        U32.shln_one_pow2(k))
        : {Cmp.is_lt(U32.cmp(U32{w}, _)) == U32.hi_zero(U32{w}, k) : Bool}
      Word.is_lt_pow2(32n, k, w, ok)

# A word that fits in k+1 bits but not in k has bit k set: it is the only bit
# left for it to have.
law Word.bit_of_not_hi_zero:
  for +n: Nat
  for +k: Nat
  for +w: Word(n)
  for +hi: {Word.hi_zero(n, w, 1n+k) == True{} : Bool}
  for +no: {Word.hi_zero(n, w, k) == False{} : Bool}
  {W.Word.get(n, w, k) == True{} : Bool}

# The head case: `hi` says the whole word fits in one bit, and `no` says it
# does not fit in none, so the one bit it has is the head.
law Word.bit_head:
  for +p: Nat
  for +b: Bool
  for +t: Word(p)
  for +hi: {Word.hi_zero(1n+p, WCon{b, t}, 1n) == True{} : Bool}
  for +no: {Word.hi_zero(1n+p, WCon{b, t}, 0n) == False{} : Bool}
  {W.Word.get(1n+p, WCon{b, t}, 0n) == True{} : Bool}

def Word.bit_head(p, b, t, hi, no):
  match b:
    case True{}:
      {==}
    case False{}:
      # With the head clear, "fits in one bit" and "fits in none" are the
      # same statement, so `hi` and `no` contradict each other.
      E.Bool.noconf({False{} == True{} : Bool},
        Equal.trans(Bool, False{}, Word.hi_zero(p, t, 0n), True{},
          E.Bool.sym(Word.hi_zero(p, t, 0n), False{}, no), hi))

def Word.bit_of_not_hi_zero(n, k, w, hi, no):
  match n:
    case 0n:
      E.Bool.noconf({W.Word.get(0n, w, k) == True{} : Bool},
        E.Bool.sym(Word.hi_zero(0n, w, k), False{}, no))
    case 1n+p:
      match k:
        case 0n:
          match w:
            case WCon{b, t}:
              Word.bit_head(p, b, t, hi, no)
        case 1n+j:
          match w:
            case WCon{b, t}:
              Word.bit_of_not_hi_zero(p, j, t, hi, no)

# Clearing bit k of a word that fits in k+1 bits leaves one that fits in k.
law Word.hi_zero_clear:
  for +n: Nat
  for +k: Nat
  for +w: Word(n)
  for +hi: {Word.hi_zero(n, w, 1n+k) == True{} : Bool}
  {Word.hi_zero(n, Word.clear(n, w, k), k) == True{} : Bool}

def Word.hi_zero_clear(n, k, w, hi):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match k:
        case 0n:
          match w:
            case WCon{b, t}:
              hi
        case 1n+j:
          match w:
            case WCon{b, t}:
              Word.hi_zero_clear(p, j, t, hi)

law U32.sub_shln:
  for +x: U32
  for +k: Nat
  for +bitk: {W.U32.bit(x, k) == True{} : Bool}
  {U32.sub(x, U32.shln(1, k))
    == U32{Word.clear(32n, W.U32.word(x), k)} : U32}

def U32.sub_shln(x, k, bitk):
  match x:
    case U32{w}:
      %E.U32.sym(U32.shln(1, k), U32{Word.pow2(32n, k)},
        U32.shln_one_pow2(k))
        : {U32.sub(U32{w}, _) == U32{Word.clear(32n, w, k)} : U32}
      %Word.sym(32n, Word.adc(32n, w, Word.pow2(32n, k), True{}, True{}),
        Word.clear(32n, w, k), Word.sub_pow2(32n, k, w, bitk))
        : {U32{_} == U32{Word.clear(32n, w, k)} : U32}
      {==}

# The upper half: an ordinal that fits in k+1 bits but not in k, rebased by
# 2^k, fits in k. This and `U32.is_lt_shln` together are addressing fact A2.
law U32.hi_zero_sub:
  for +x: U32
  for +k: Nat
  for +hi: {U32.hi_zero(x, 1n+k) == True{} : Bool}
  for +no: {U32.hi_zero(x, k) == False{} : Bool}
  {U32.hi_zero(U32.sub(x, U32.shln(1, k)), k) == True{} : Bool}

def U32.hi_zero_sub(x, k, hi, no):
  match x:
    case U32{w}:
      %E.U32.sym(U32.sub(U32{w}, U32.shln(1, k)),
        U32{Word.clear(32n, w, k)},
        U32.sub_shln(U32{w}, k,
          Word.bit_of_not_hi_zero(32n, k, w, hi, no)))
        : {Word.hi_zero(32n, W.U32.word(_), k) == True{} : Bool}
      Word.hi_zero_clear(32n, k, w, hi)
