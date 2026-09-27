# proofs/split_add.bend -- adding into free bits is just setting them.
#
# The enumeration of a set walks intervals: a branch enumerates its low half
# at `base` and its high half at `base + h`, and a leaf shifts its offsets by
# `base`. Every one of those additions has the same shape -- a value that
# fits in the low `k` bits, added to a base whose low `k` bits are zero -- and
# for that shape addition carries nowhere, so it is the same as `or`.
#
# That is what makes the enumeration reachable without general `U32`
# arithmetic. The two facts this file proves are both structural inductions
# over the bit vector, with the two conditions carried as decidable
# predicates rather than as claims quantified over bit positions: `hi_zero`
# says the value fits, and `lo_zero` says the base has room.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ../core/count.bend as C
import ../core/word.bend as W

# The low `k` bits of a word are all zero.
def Word.lo_zero(n: Nat, w: Word(n), k: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match k:
            case 0n:
              True{}
            case 1n+j:
              Bool.and(Bool.not(b), Word.lo_zero(p, t, j))

def U32.lo_zero(x: U32, k: Nat) -> Bool:
  Word.lo_zero(32n, W.U32.word(x), k)

# ---------------------------------------------------------------------------
# No carry ever leaves a free bit.
# ---------------------------------------------------------------------------

law Word.adc_disjoint:
  for +n: Nat
  for +k: Nat
  for +y: Word(n)
  for +b: Word(n)
  for +hy: {Dc.Word.hi_zero(n, y, k) == True{} : Bool}
  for +lb: {Word.lo_zero(n, b, k) == True{} : Bool}
  {Word.adc(n, y, b, False{}, False{}) == Word.or(n, y, b) : Word(n)}

# A zero head on the base side: the sum keeps the value's head and the carry
# stays clear.
law Word.adc_cons:
  for +p: Nat
  for +yb: Bool
  for +yt: Word(p)
  for +bt: Word(p)
  for +ih: {Word.adc(p, yt, bt, False{}, False{})
    == Word.or(p, yt, bt) : Word(p)}
  {Word.adc(1n+p, WCon{yb, yt}, WCon{False{}, bt}, False{}, False{})
    == Word.or(1n+p, WCon{yb, yt}, WCon{False{}, bt}) : Word(1n+p)}

def Word.adc_cons(p, yb, yt, bt, ih):
  match yb:
    case False{}:
      %Dc.Word.sym(p, Word.adc(p, yt, bt, False{}, False{}),
        Word.or(p, yt, bt), ih)
        : {WCon{False{}, _} == WCon{False{}, Word.or(p, yt, bt)}
          : Word(1n+p)}
      {==}
    case True{}:
      %Dc.Word.sym(p, Word.adc(p, yt, bt, False{}, False{}),
        Word.or(p, yt, bt), ih)
        : {WCon{True{}, _} == WCon{True{}, Word.or(p, yt, bt)}
          : Word(1n+p)}
      {==}

# The value has no bits at all: the sum is the base.
law Word.adc_all_zero:
  for +n: Nat
  for +y: Word(n)
  for +b: Word(n)
  for +hy: {Dc.Word.hi_zero(n, y, 0n) == True{} : Bool}
  {Word.adc(n, y, b, False{}, False{}) == Word.or(n, y, b) : Word(n)}

law Word.adc_zero_head:
  for +q: Nat
  for +at: Word(q)
  for +c: Bool
  for +ct: Word(q)
  for +ih: {Word.adc(q, at, ct, False{}, False{})
    == Word.or(q, at, ct) : Word(q)}
  {Word.adc(1n+q, WCon{False{}, at}, WCon{c, ct}, False{}, False{})
    == Word.or(1n+q, WCon{False{}, at}, WCon{c, ct}) : Word(1n+q)}

def Word.adc_zero_head(q, at, c, ct, ih):
  match c:
    case False{}:
      %Dc.Word.sym(q, Word.adc(q, at, ct, False{}, False{}),
        Word.or(q, at, ct), ih)
        : {WCon{False{}, _} == WCon{False{}, Word.or(q, at, ct)}
          : Word(1n+q)}
      {==}
    case True{}:
      %Dc.Word.sym(q, Word.adc(q, at, ct, False{}, False{}),
        Word.or(q, at, ct), ih)
        : {WCon{True{}, _} == WCon{True{}, Word.or(q, at, ct)}
          : Word(1n+q)}
      {==}

def Word.adc_all_zero(n, y, b, hy):
  match n:
    case 0n:
      match y b:
        case WNil{} WNil{}:
          {==}
    case 1n+q:
      match y b:
        case WCon{a, at} WCon{c, ct}:
          %E.Bool.not_true(a,
            E.Bool.and_l(Bool.not(a), Dc.Word.hi_zero(q, at, 0n), hy))
            : {Word.adc(1n+q, WCon{_, at}, WCon{c, ct}, False{}, False{})
              == Word.or(1n+q, WCon{_, at}, WCon{c, ct}) : Word(1n+q)}
          Word.adc_zero_head(q, at, c, ct,
            Word.adc_all_zero(q, at, ct,
              E.Bool.and_r(Bool.not(a), Dc.Word.hi_zero(q, at, 0n), hy)))

def Word.adc_disjoint(n, k, y, b, hy, lb):
  match n:
    case 0n:
      match y b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match k:
        case 0n:
          match y b:
            case WCon{yb, yt} WCon{bb, bt}:
              Word.adc_all_zero(1n+p, WCon{yb, yt}, WCon{bb, bt}, hy)
        case 1n+j:
          match y b:
            case WCon{yb, yt} WCon{bb, bt}:
              %E.Bool.not_true(bb,
                E.Bool.and_l(Bool.not(bb),
                  Word.lo_zero(p, bt, j), lb))
                : {Word.adc(1n+p, WCon{yb, yt}, WCon{_, bt}, False{},
                    False{})
                  == Word.or(1n+p, WCon{yb, yt}, WCon{_, bt})
                  : Word(1n+p)}
              Word.adc_cons(p, yb, yt, bt,
                Word.adc_disjoint(p, j, yt, bt, hy,
                  E.Bool.and_r(Bool.not(bb), Word.lo_zero(p, bt, j), lb)))

# ---------------------------------------------------------------------------
# And the two halves come back out.
#
# With the value in the free bits and the base above them, masking recovers
# each: the low `k` bits are the value, and clearing them leaves the base.
# Those two, with the fact that a word is its low bits or its high bits, are
# what turn "x is `y` shifted to `base`" into two independent tests a walk
# can perform.
# ---------------------------------------------------------------------------

law Word.and_or_low:
  for +n: Nat
  for +y: Word(n)
  for +b: Word(n)
  for +k: Nat
  for +hy: {Dc.Word.hi_zero(n, y, k) == True{} : Bool}
  for +lb: {Word.lo_zero(n, b, k) == True{} : Bool}
  {Word.and(n, Word.or(n, y, b), W.Word.low_mask(n, k)) == y : Word(n)}

law Word.or_false_cons:
  for +p: Nat
  for +yb: Bool
  for +yt: Word(p)
  {WCon{Bool.and(Bool.or(yb, False{}), True{}), yt} == WCon{yb, yt}
    : Word(1n+p)}

def Word.or_false_cons(p, yb, yt):
  match yb:
    case True{}:
      {==}
    case False{}:
      {==}

law Word.and_false_r:
  for +p: Bool
  {Bool.and(p, False{}) == False{} : Bool}

def Word.and_false_r(p):
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

law Word.lo_zero_zero:
  for +n: Nat
  for +w: Word(n)
  {Word.lo_zero(n, w, 0n) == True{} : Bool}

def Word.lo_zero_zero(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          {==}

def Word.and_or_low(n, y, b, k, hy, lb):
  match n:
    case 0n:
      match y:
        case WNil{}:
          {==}
    case 1n+p:
      match y b:
        case WCon{yb, yt} WCon{bb, bt}:
          match k:
            case 0n:
              %E.Bool.sym(Bool.and(Bool.or(yb, bb), False{}), False{},
                Word.and_false_r(Bool.or(yb, bb)))
                : {WCon{_,
                    Word.and(p, Word.or(p, yt, bt), W.Word.low_mask(p, 0n))}
                  == WCon{yb, yt} : Word(1n+p)}
              %E.Bool.not_true(yb,
                E.Bool.and_l(Bool.not(yb), Dc.Word.hi_zero(p, yt, 0n), hy))
                : {WCon{False{},
                    Word.and(p, Word.or(p, yt, bt), W.Word.low_mask(p, 0n))}
                  == WCon{_, yt} : Word(1n+p)}
              %Dc.Word.sym(p,
                Word.and(p, Word.or(p, yt, bt), W.Word.low_mask(p, 0n)), yt,
                Word.and_or_low(p, yt, bt, 0n,
                  E.Bool.and_r(Bool.not(yb), Dc.Word.hi_zero(p, yt, 0n),
                    hy), Word.lo_zero_zero(p, bt)))
                : {WCon{False{}, _} == WCon{False{}, yt} : Word(1n+p)}
              {==}
            case 1n+j:
              %E.Bool.not_true(bb,
                E.Bool.and_l(Bool.not(bb), Word.lo_zero(p, bt, j), lb))
                : {WCon{Bool.and(Bool.or(yb, _), True{}),
                    Word.and(p, Word.or(p, yt, bt),
                      W.Word.low_mask(p, j))}
                  == WCon{yb, yt} : Word(1n+p)}
              %Dc.Word.sym(p,
                Word.and(p, Word.or(p, yt, bt), W.Word.low_mask(p, j)), yt,
                Word.and_or_low(p, yt, bt, j, hy,
                  E.Bool.and_r(Bool.not(bb), Word.lo_zero(p, bt, j), lb)))
                : {WCon{Bool.and(Bool.or(yb, False{}), True{}), _}
                  == WCon{yb, yt} : Word(1n+p)}
              Word.or_false_cons(p, yb, yt)

law Word.and_not_or_high:
  for +n: Nat
  for +y: Word(n)
  for +b: Word(n)
  for +k: Nat
  for +hy: {Dc.Word.hi_zero(n, y, k) == True{} : Bool}
  for +lb: {Word.lo_zero(n, b, k) == True{} : Bool}
  {Word.and(n, Word.or(n, y, b), Word.not(n, W.Word.low_mask(n, k))) == b
    : Word(n)}

law Word.or_false_left:
  for +p: Nat
  for +bb: Bool
  for +bt: Word(p)
  {WCon{Bool.and(Bool.or(False{}, bb), True{}), bt} == WCon{bb, bt}
    : Word(1n+p)}

def Word.or_false_left(p, bb, bt):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

law Word.and_false_cons:
  for +p: Nat
  for +c: Bool
  for +bt: Word(p)
  {WCon{Bool.and(c, False{}), bt} == WCon{False{}, bt} : Word(1n+p)}

def Word.and_false_cons(p, c, bt):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def Word.and_not_or_high(n, y, b, k, hy, lb):
  match n:
    case 0n:
      match b:
        case WNil{}:
          {==}
    case 1n+p:
      match y b:
        case WCon{yb, yt} WCon{bb, bt}:
          match k:
            case 0n:
              %E.Bool.not_true(yb,
                E.Bool.and_l(Bool.not(yb), Dc.Word.hi_zero(p, yt, 0n), hy))
                : {WCon{Bool.and(Bool.or(_, bb), True{}),
                    Word.and(p, Word.or(p, yt, bt),
                      Word.not(p, W.Word.low_mask(p, 0n)))}
                  == WCon{bb, bt} : Word(1n+p)}
              %Dc.Word.sym(p,
                Word.and(p, Word.or(p, yt, bt),
                  Word.not(p, W.Word.low_mask(p, 0n))), bt,
                Word.and_not_or_high(p, yt, bt, 0n,
                  E.Bool.and_r(Bool.not(yb), Dc.Word.hi_zero(p, yt, 0n),
                    hy), Word.lo_zero_zero(p, bt)))
                : {WCon{Bool.and(Bool.or(False{}, bb), True{}), _}
                  == WCon{bb, bt} : Word(1n+p)}
              Word.or_false_left(p, bb, bt)
            case 1n+j:
              %E.Bool.not_true(bb,
                E.Bool.and_l(Bool.not(bb), Word.lo_zero(p, bt, j), lb))
                : {WCon{Bool.and(Bool.or(yb, _), False{}),
                    Word.and(p, Word.or(p, yt, bt),
                      Word.not(p, W.Word.low_mask(p, j)))}
                  == WCon{_, bt} : Word(1n+p)}
              %Dc.Word.sym(p,
                Word.and(p, Word.or(p, yt, bt),
                  Word.not(p, W.Word.low_mask(p, j))), bt,
                Word.and_not_or_high(p, yt, bt, j, hy,
                  E.Bool.and_r(Bool.not(bb), Word.lo_zero(p, bt, j), lb)))
                : {WCon{Bool.and(Bool.or(yb, False{}), False{}), _}
                  == WCon{False{}, bt} : Word(1n+p)}
              Word.and_false_cons(p, Bool.or(yb, False{}), bt)

# A word is its low bits or its high bits.
law Word.or_split:
  for +n: Nat
  for +x: Word(n)
  for +k: Nat
  {Word.or(n, Word.and(n, x, W.Word.low_mask(n, k)),
    Word.and(n, x, Word.not(n, W.Word.low_mask(n, k)))) == x : Word(n)}

law Word.split_head:
  for +p: Nat
  for +xb: Bool
  for +xt: Word(p)
  for +m: Bool
  {WCon{Bool.or(Bool.and(xb, m), Bool.and(xb, Bool.not(m))), xt}
    == WCon{xb, xt} : Word(1n+p)}

def Word.split_head(p, xb, xt, m):
  match xb:
    case True{}:
      match m:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match m:
        case True{}:
          {==}
        case False{}:
          {==}

def Word.or_split(n, x, k):
  match n:
    case 0n:
      match x:
        case WNil{}:
          {==}
    case 1n+p:
      match x:
        case WCon{xb, xt}:
          match k:
            case 0n:
              %Dc.Word.sym(p,
                Word.or(p, Word.and(p, xt, W.Word.low_mask(p, 0n)),
                  Word.and(p, xt, Word.not(p, W.Word.low_mask(p, 0n)))),
                xt, Word.or_split(p, xt, 0n))
                : {WCon{Bool.or(Bool.and(xb, False{}),
                    Bool.and(xb, True{})), _} == WCon{xb, xt}
                  : Word(1n+p)}
              Word.split_head(p, xb, xt, False{})
            case 1n+j:
              %Dc.Word.sym(p,
                Word.or(p, Word.and(p, xt, W.Word.low_mask(p, j)),
                  Word.and(p, xt, Word.not(p, W.Word.low_mask(p, j)))),
                xt, Word.or_split(p, xt, j))
                : {WCon{Bool.or(Bool.and(xb, True{}),
                    Bool.and(xb, False{})), _} == WCon{xb, xt}
                  : Word(1n+p)}
              Word.split_head(p, xb, xt, True{})

# The two halves of a word satisfy the two conditions, so a word can always
# be taken apart and put back together this way.
law Word.hi_zero_low:
  for +n: Nat
  for +x: Word(n)
  for +k: Nat
  {Dc.Word.hi_zero(n, Word.and(n, x, W.Word.low_mask(n, k)), k)
    == True{} : Bool}

def Word.hi_zero_low(n, x, k):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match x:
        case WCon{xb, xt}:
          match k:
            case 0n:
              %E.Bool.sym(Bool.and(xb, False{}), False{},
                Word.and_false_r(xb))
                : {Bool.and(Bool.not(_),
                    Dc.Word.hi_zero(p, Word.and(p, xt,
                      W.Word.low_mask(p, 0n)), 0n)) == True{} : Bool}
              Word.hi_zero_low(p, xt, 0n)
            case 1n+j:
              Word.hi_zero_low(p, xt, j)

law Word.lo_zero_high:
  for +n: Nat
  for +x: Word(n)
  for +k: Nat
  {Word.lo_zero(n, Word.and(n, x, Word.not(n, W.Word.low_mask(n, k))), k)
    == True{} : Bool}

def Word.lo_zero_high(n, x, k):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match x:
        case WCon{xb, xt}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              %E.Bool.sym(Bool.and(xb, False{}), False{},
                Word.and_false_r(xb))
                : {Bool.and(Bool.not(_),
                    Word.lo_zero(p, Word.and(p, xt,
                      Word.not(p, W.Word.low_mask(p, j))), j))
                  == True{} : Bool}
              Word.lo_zero_high(p, xt, j)

# ---------------------------------------------------------------------------
# At `U32`.
# ---------------------------------------------------------------------------

law U32.add_disjoint:
  for +y: U32
  for +b: U32
  for +k: Nat
  for +hy: {Dc.U32.hi_zero(y, k) == True{} : Bool}
  for +lb: {U32.lo_zero(b, k) == True{} : Bool}
  {(y + b : U32) == U32.or(y, b) : U32}

def U32.add_disjoint(y, b, k, hy, lb):
  match y b:
    case U32{yw} U32{bw}:
      Equal.cong(Word(32n), U32, E.U32.pak,
        Word.adc(32n, yw, bw, False{}, False{}), Word.or(32n, yw, bw),
        Word.adc_disjoint(32n, k, yw, bw, hy, lb))

law U32.and_or_low:
  for +y: U32
  for +b: U32
  for +k: Nat
  for +hy: {Dc.U32.hi_zero(y, k) == True{} : Bool}
  for +lb: {U32.lo_zero(b, k) == True{} : Bool}
  {U32.and(U32.or(y, b), W.U32.mask(k)) == y : U32}

def U32.and_or_low(y, b, k, hy, lb):
  match y b:
    case U32{yw} U32{bw}:
      Equal.cong(Word(32n), U32, E.U32.pak,
        Word.and(32n, Word.or(32n, yw, bw), W.Word.low_mask(32n, k)), yw,
        Word.and_or_low(32n, yw, bw, k, hy, lb))

law U32.diff_or_high:
  for +y: U32
  for +b: U32
  for +k: Nat
  for +hy: {Dc.U32.hi_zero(y, k) == True{} : Bool}
  for +lb: {U32.lo_zero(b, k) == True{} : Bool}
  {W.U32.diff(U32.or(y, b), W.U32.mask(k)) == b : U32}

def U32.diff_or_high(y, b, k, hy, lb):
  match y b:
    case U32{yw} U32{bw}:
      Equal.cong(Word(32n), U32, E.U32.pak,
        Word.and(32n, Word.or(32n, yw, bw),
          Word.not(32n, W.Word.low_mask(32n, k))), bw,
        Word.and_not_or_high(32n, yw, bw, k, hy, lb))

law U32.or_split:
  for +x: U32
  for +k: Nat
  {U32.or(U32.and(x, W.U32.mask(k)), W.U32.diff(x, W.U32.mask(k))) == x
    : U32}

def U32.or_split(x, k):
  match x:
    case U32{xw}:
      Equal.cong(Word(32n), U32, E.U32.pak,
        Word.or(32n, Word.and(32n, xw, W.Word.low_mask(32n, k)),
          Word.and(32n, xw, Word.not(32n, W.Word.low_mask(32n, k)))), xw,
        Word.or_split(32n, xw, k))

law U32.hi_zero_low:
  for +x: U32
  for +k: Nat
  {Dc.U32.hi_zero(U32.and(x, W.U32.mask(k)), k) == True{} : Bool}

def U32.hi_zero_low(x, k):
  match x:
    case U32{xw}:
      Word.hi_zero_low(32n, xw, k)

law U32.lo_zero_high:
  for +x: U32
  for +k: Nat
  {U32.lo_zero(W.U32.diff(x, W.U32.mask(k)), k) == True{} : Bool}

def U32.lo_zero_high(x, k):
  match x:
    case U32{xw}:
      Word.lo_zero_high(32n, xw, k)
