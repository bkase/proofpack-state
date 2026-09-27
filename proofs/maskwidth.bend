# proofs/maskwidth.bend -- the same ordinal, masked at two adjacent widths.
#
# A branch hands its child an ordinal rebased into the child's half: the low
# half keeps it, the high half subtracts the half-width. The enumeration hands
# its child the same ordinal masked one bit narrower. These are the lemmas
# that say those are the same thing -- masking at k+1 and then clearing bit k
# is masking at k, and if bit k was already clear the two masks agree.
#
# Everything here is structural on the bit vector. No arithmetic.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./split_add.bend as Sa
import ../core/count.bend as C
import ../core/word.bend as W

# Clearing the top bit of the low k+1 bits leaves the low k bits.
law Word.clear_mask:
  for +n: Nat
  for +w: Word(n)
  for +k: Nat
  {Dc.Word.clear(n, Word.and(n, w, W.Word.low_mask(n, 1n+k)), k)
    == Word.and(n, w, W.Word.low_mask(n, k)) : Word(n)}

def Word.clear_mask(n, w, k):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match k:
            case 0n:
              %E.Bool.sym(Bool.and(b, False{}), False{},
                Sa.Word.and_false_r(b))
                : {WCon{False{}, Word.and(p, t,
                    W.Word.low_mask(p, 0n))}
                  == WCon{_, Word.and(p, t,
                    W.Word.low_mask(p, 0n))} : Word(1n+p)}
              {==}
            case 1n+j:
              %E.Word.sym(p, Dc.Word.clear(p, Word.and(p, t,
                  W.Word.low_mask(p, 1n+j)), j),
                Word.and(p, t, W.Word.low_mask(p, j)),
                Word.clear_mask(p, t, j))
                : {WCon{Bool.and(b, True{}), _}
                  == WCon{Bool.and(b, True{}),
                    Word.and(p, t, W.Word.low_mask(p, j))} : Word(1n+p)}
              {==}

# If that bit was clear, the two masks agree.
law Word.mask_step:
  for +n: Nat
  for +w: Word(n)
  for +k: Nat
  for +hz: {Dc.Word.hi_zero(n, Word.and(n, w,
    W.Word.low_mask(n, 1n+k)), k) == True{} : Bool}
  {Word.and(n, w, W.Word.low_mask(n, 1n+k))
    == Word.and(n, w, W.Word.low_mask(n, k)) : Word(n)}

def Word.mask_step(n, w, k, hz):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case False{}:
              match k:
                case 0n:
                  {==}
                case 1n+j:
                  %E.Word.sym(p, Word.and(p, t,
                      W.Word.low_mask(p, 1n+j)),
                    Word.and(p, t, W.Word.low_mask(p, j)),
                    Word.mask_step(p, t, j, hz))
                    : {WCon{False{}, _}
                      == WCon{False{}, Word.and(p, t,
                        W.Word.low_mask(p, j))} : Word(1n+p)}
                  {==}
            case True{}:
              match k:
                case 0n:
                  E.Bool.noconf({Word.and(1n+p, WCon{True{}, t},
                    W.Word.low_mask(1n+p, 1n))
                    == Word.and(1n+p, WCon{True{}, t},
                      W.Word.low_mask(1n+p, 0n)) : Word(1n+p)}, hz)
                case 1n+j:
                  %E.Word.sym(p, Word.and(p, t,
                      W.Word.low_mask(p, 1n+j)),
                    Word.and(p, t, W.Word.low_mask(p, j)),
                    Word.mask_step(p, t, j, hz))
                    : {WCon{True{}, _}
                      == WCon{True{}, Word.and(p, t,
                        W.Word.low_mask(p, j))} : Word(1n+p)}
                  {==}

# ---------------------------------------------------------------------------
# At `U32`.
# ---------------------------------------------------------------------------

law U32.clear_mask:
  for +x: U32
  for +k: Nat
  {U32{Dc.Word.clear(32n, W.U32.word(U32.and(x, W.U32.mask(1n+k))), k)}
    == U32.and(x, W.U32.mask(k)) : U32}

def U32.clear_mask(x, k):
  match x:
    case U32{xw}:
      Equal.cong(Word(32n), U32, E.U32.pak,
        Dc.Word.clear(32n, Word.and(32n, xw,
          W.Word.low_mask(32n, 1n+k)), k),
        Word.and(32n, xw, W.Word.low_mask(32n, k)),
        Word.clear_mask(32n, xw, k))

law U32.mask_step:
  for +x: U32
  for +k: Nat
  for +hz: {Dc.U32.hi_zero(U32.and(x, W.U32.mask(1n+k)), k)
    == True{} : Bool}
  {U32.and(x, W.U32.mask(1n+k)) == U32.and(x, W.U32.mask(k)) : U32}

def U32.mask_step(x, k, hz):
  match x:
    case U32{xw}:
      Equal.cong(Word(32n), U32, E.U32.pak,
        Word.and(32n, xw, W.Word.low_mask(32n, 1n+k)),
        Word.and(32n, xw, W.Word.low_mask(32n, k)),
        Word.mask_step(32n, xw, k, hz))
