# proofs/split.bend -- the division identity, and addressing fact A3.
#
# `Words.bit(ws, x)` addresses a tile by two numbers: `x >> 5` picks the word
# and `x & 31` picks the bit. For a sparse leaf and the tile it spreads into
# to hold the same ordinals, that address has to be injective -- two different
# ordinals must not land on the same bit of the same word.
#
# The way in is the identity every such split rests on:
#
#     x  ==  2^k * (x >> k)  +  (x & (2^k - 1))
#
# With it, two ordinals with the same address have the same `U32.to_nat`, and
# `the_number_a_word_reads_as_determines_the_word` finishes. No reasoning
# about bit positions under a quantifier is needed, which is what made the
# direct route stall.
#
# The identity itself is an induction down the vector: the head bit is the
# parity, the mask keeps it, the shift drops it, and what is left is the same
# statement one bit shorter.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./inject.bend as Ij
import ../core/word.bend as W

# ---------------------------------------------------------------------------
# Shifting a word, and doubling a number, k times.
# ---------------------------------------------------------------------------

def Word.shrn(+n: Nat, w: Word(n), k: Nat) -> Word(n):
  match k:
    case 0n:
      w
    case 1n+j:
      Word.shr(n, Word.shrn(n, w, j))

def Nat.dbl(k: Nat, m: Nat) -> Nat:
  match k:
    case 0n:
      m
    case 1n+j:
      Nat.double(Nat.dbl(j, m))

# The head bit and the halved value, as `Word.to_nat` combines them.
def Nat.cons(b: Bool, m: Nat) -> Nat:
  match b:
    case False{}:
      Nat.double(m)
    case True{}:
      1n+Nat.double(m)

# ---------------------------------------------------------------------------
# `Nat` lemmas.
# ---------------------------------------------------------------------------

law Nat.double_add:
  for +a: Nat
  for +b: Nat
  {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b))
    : Nat}

def Nat.double_add(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %E.Nat.sym(Nat.double(Nat.add(p, b)),
        Nat.add(Nat.double(p), Nat.double(b)), Nat.double_add(p, b))
        : {2n+_ == 2n+Nat.add(Nat.double(p), Nat.double(b)) : Nat}
      {==}

# Pulling a head bit out of a sum: the bit belongs with the low part.
law Nat.cons_add:
  for +b: Bool
  for +a: Nat
  for +m: Nat
  {Nat.cons(b, Nat.add(a, m))
    == Nat.add(Nat.double(a), Nat.cons(b, m)) : Nat}

def Nat.cons_add(b, a, m):
  match b:
    case False{}:
      Nat.double_add(a, m)
    case True{}:
      %E.Nat.sym(Nat.double(Nat.add(a, m)),
        Nat.add(Nat.double(a), Nat.double(m)), Nat.double_add(a, m))
        : {1n+_ == Nat.add(Nat.double(a), 1n+Nat.double(m)) : Nat}
      E.Nat.sym(Nat.add(Nat.double(a), 1n+Nat.double(m)),
        1n+Nat.add(Nat.double(a), Nat.double(m)),
        N.Nat.add_succ(Nat.double(a), Nat.double(m)))

# ---------------------------------------------------------------------------
# Padding a zero on top changes neither the value nor what a shift does to it.
# ---------------------------------------------------------------------------

law Word.to_nat_pad:
  for +n: Nat
  for +w: Word(n)
  {Word.to_nat(1n+n, Word.shr.pad(n, w)) == Word.to_nat(n, w) : Nat}

def Nat.succ_double(m: Nat) -> Nat:
  1n+Nat.double(m)

# The head bit, with the bit as a parameter so it can be matched.
law Word.to_nat_pad.step:
  for +q: Nat
  for +c: Bool
  for +u: Word(q)
  for +ih: {Word.to_nat(1n+q, Word.shr.pad(q, u))
    == Word.to_nat(q, u) : Nat}
  {Word.to_nat(2n+q, WCon{c, Word.shr.pad(q, u)})
    == Word.to_nat(1n+q, WCon{c, u}) : Nat}

def Word.to_nat_pad.step(q, c, u, ih):
  match c:
    case False{}:
      Equal.cong(Nat, Nat, Nat.double,
        Word.to_nat(1n+q, Word.shr.pad(q, u)), Word.to_nat(q, u), ih)
    case True{}:
      Equal.cong(Nat, Nat, Nat.succ_double,
        Word.to_nat(1n+q, Word.shr.pad(q, u)), Word.to_nat(q, u), ih)

# `Word.to_nat` on a cons is `Nat.cons`; stated because the proofs below work
# through `Nat.cons` and Bend will not reduce a match on an unknown bit.
law Word.to_nat_cons:
  for +n: Nat
  for +b: Bool
  for +t: Word(n)
  {Word.to_nat(1n+n, WCon{b, t}) == Nat.cons(b, Word.to_nat(n, t)) : Nat}

def Word.to_nat_cons(n, b, t):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Word.to_nat_pad(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+q:
      match w:
        case WCon{c, u}:
          Word.to_nat_pad.step(q, c, u, Word.to_nat_pad(q, u))

law Word.shr_pad:
  for +n: Nat
  for +w: Word(n)
  {Word.shr(1n+n, Word.shr.pad(n, w))
    == Word.shr.pad(n, Word.shr(n, w)) : Word(1n+n)}

def Word.shr_pad(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+q:
      match w:
        case WCon{c, u}:
          {==}

law Word.shrn_pad:
  for +n: Nat
  for +w: Word(n)
  for +k: Nat
  {Word.shrn(1n+n, Word.shr.pad(n, w), k)
    == Word.shr.pad(n, Word.shrn(n, w, k)) : Word(1n+n)}

def Word.shrn_pad(n, w, k):
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(Word(1n+n),
        Word.shrn(1n+n, Word.shr.pad(n, w), j),
        Word.shr.pad(n, Word.shrn(n, w, j)), Word.shrn_pad(n, w, j))
        : {Word.shr(1n+n, _)
          == Word.shr.pad(n, Word.shr(n, Word.shrn(n, w, j)))
          : Word(1n+n)}
      Word.shr_pad(n, Word.shrn(n, w, j))

# ---------------------------------------------------------------------------
# The identity: a word is its high part shifted up, plus its low part.
# ---------------------------------------------------------------------------

law Word.and_low_mask_zero:
  for +n: Nat
  for +w: Word(n)
  {Word.to_nat(n, Word.and(n, w, W.Word.low_mask(n, 0n))) == 0n : Nat}

law Word.and_low_mask_zero.step:
  for +p: Nat
  for +b: Bool
  for +t: Word(p)
  for +ih: {Word.to_nat(p, Word.and(p, t, W.Word.low_mask(p, 0n)))
    == 0n : Nat}
  {Word.to_nat(1n+p, Word.and(1n+p, WCon{b, t},
      W.Word.low_mask(1n+p, 0n))) == 0n : Nat}

def Word.and_low_mask_zero.step(p, b, t, ih):
  match b:
    case False{}:
      Equal.cong(Nat, Nat, Nat.double,
        Word.to_nat(p, Word.and(p, t, W.Word.low_mask(p, 0n))), 0n, ih)
    case True{}:
      Equal.cong(Nat, Nat, Nat.double,
        Word.to_nat(p, Word.and(p, t, W.Word.low_mask(p, 0n))), 0n, ih)

def Word.and_low_mask_zero(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Word.and_low_mask_zero.step(p, b, t,
            Word.and_low_mask_zero(p, t))

law Nat.dbl_zero:
  for +k: Nat
  {Nat.dbl(k, 0n) == 0n : Nat}

def Nat.dbl_zero(k):
  match k:
    case 0n:
      {==}
    case 1n+j:
      %E.Nat.sym(Nat.dbl(j, 0n), 0n, Nat.dbl_zero(j))
        : {Nat.double(_) == 0n : Nat}
      {==}

law Word.to_nat_split:
  for +n: Nat
  for +w: Word(n)
  for +k: Nat
  {Word.to_nat(n, w)
    == Nat.add(Nat.dbl(k, Word.to_nat(n, Word.shrn(n, w, k))),
         Word.to_nat(n, Word.and(n, w, W.Word.low_mask(n, k)))) : Nat}

law Word.shrn_shr:
  for +n: Nat
  for +w: Word(n)
  for +j: Nat
  {Word.shrn(n, w, 1n+j) == Word.shrn(n, Word.shr(n, w), j) : Word(n)}

def Word.shrn_shr(n, w, j):
  match j:
    case 0n:
      {==}
    case 1n+i:
      %Equal.sym(Word(n), Word.shrn(n, w, 1n+i),
        Word.shrn(n, Word.shr(n, w), i), Word.shrn_shr(n, w, i))
        : {Word.shr(n, _) == Word.shrn(n, Word.shr(n, w), 1n+i)
          : Word(n)}
      {==}

# The high part of a word, read past its head: shifting a cons right by one
# more than `j` is shifting its tail right by `j`, once the padding is
# discounted.
law Word.shrn_head:
  for +p: Nat
  for +b: Bool
  for +t: Word(p)
  for +j: Nat
  {Word.to_nat(1n+p, Word.shrn(1n+p, WCon{b, t}, 1n+j))
    == Word.to_nat(p, Word.shrn(p, t, j)) : Nat}

def Word.shrn_head(p, b, t, j):
  %Equal.sym(Word(1n+p), Word.shrn(1n+p, WCon{b, t}, 1n+j),
    Word.shrn(1n+p, Word.shr(1n+p, WCon{b, t}), j),
    Word.shrn_shr(1n+p, WCon{b, t}, j))
    : {Word.to_nat(1n+p, _) == Word.to_nat(p, Word.shrn(p, t, j)) : Nat}
  %Equal.sym(Word(1n+p), Word.shrn(1n+p, Word.shr.pad(p, t), j),
    Word.shr.pad(p, Word.shrn(p, t, j)), Word.shrn_pad(p, t, j))
    : {Word.to_nat(1n+p, _) == Word.to_nat(p, Word.shrn(p, t, j)) : Nat}
  Word.to_nat_pad(p, Word.shrn(p, t, j))

law Word.to_nat_split.step:
  for +p: Nat
  for +b: Bool
  for +t: Word(p)
  for +j: Nat
  for +ih: {Word.to_nat(p, t)
    == Nat.add(Nat.dbl(j, Word.to_nat(p, Word.shrn(p, t, j))),
         Word.to_nat(p, Word.and(p, t, W.Word.low_mask(p, j)))) : Nat}
  {Word.to_nat(1n+p, WCon{b, t})
    == Nat.add(Nat.dbl(1n+j,
         Word.to_nat(1n+p, Word.shrn(1n+p, WCon{b, t}, 1n+j))),
         Word.to_nat(1n+p, Word.and(1n+p, WCon{b, t},
           W.Word.low_mask(1n+p, 1n+j)))) : Nat}

law Word.to_nat_split.arm:
  for +p: Nat
  for +b: Bool
  for +t: Word(p)
  for +j: Nat
  for +ih: {Word.to_nat(p, t)
    == Nat.add(Nat.dbl(j, Word.to_nat(p, Word.shrn(p, t, j))),
         Word.to_nat(p, Word.and(p, t, W.Word.low_mask(p, j)))) : Nat}
  {Word.to_nat(1n+p, WCon{b, t})
    == Nat.add(Nat.double(Nat.dbl(j,
         Word.to_nat(p, Word.shrn(p, t, j)))),
         Word.to_nat(1n+p, Word.and(1n+p, WCon{b, t},
           W.Word.low_mask(1n+p, 1n+j)))) : Nat}

def Word.to_nat_split.arm(p, b, t, j, ih):
  match b:
    case False{}:
      %E.Nat.sym(Word.to_nat(p, t),
        Nat.add(Nat.dbl(j, Word.to_nat(p, Word.shrn(p, t, j))),
          Word.to_nat(p, Word.and(p, t, W.Word.low_mask(p, j)))), ih)
        : {Nat.double(_)
        == Nat.add(Nat.double(Nat.dbl(j,
             Word.to_nat(p, Word.shrn(p, t, j)))),
             Nat.double(Word.to_nat(p,
               Word.and(p, t, W.Word.low_mask(p, j))))) : Nat}
      Nat.cons_add(False{}, Nat.dbl(j, Word.to_nat(p, Word.shrn(p, t, j))),
        Word.to_nat(p, Word.and(p, t, W.Word.low_mask(p, j))))
    case True{}:
      %E.Nat.sym(Word.to_nat(p, t),
        Nat.add(Nat.dbl(j, Word.to_nat(p, Word.shrn(p, t, j))),
          Word.to_nat(p, Word.and(p, t, W.Word.low_mask(p, j)))), ih)
        : {1n+Nat.double(_)
        == Nat.add(Nat.double(Nat.dbl(j,
             Word.to_nat(p, Word.shrn(p, t, j)))),
             1n+Nat.double(Word.to_nat(p,
               Word.and(p, t, W.Word.low_mask(p, j))))) : Nat}
      Nat.cons_add(True{}, Nat.dbl(j, Word.to_nat(p, Word.shrn(p, t, j))),
        Word.to_nat(p, Word.and(p, t, W.Word.low_mask(p, j))))

def Word.to_nat_split.step(p, b, t, j, ih):
  %E.Nat.sym(Word.to_nat(1n+p, Word.shrn(1n+p, WCon{b, t}, 1n+j)),
    Word.to_nat(p, Word.shrn(p, t, j)), Word.shrn_head(p, b, t, j))
    : {Word.to_nat(1n+p, WCon{b, t})
      == Nat.add(Nat.double(Nat.dbl(j, _)),
           Word.to_nat(1n+p, Word.and(1n+p, WCon{b, t},
             W.Word.low_mask(1n+p, 1n+j)))) : Nat}
  Word.to_nat_split.arm(p, b, t, j, ih)

def Word.to_nat_split(n, w, k):
  match n:
    case 0n:
      match w:
        case WNil{}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              %E.Nat.sym(Nat.dbl(j, 0n), 0n, Nat.dbl_zero(j))
                : {0n == Nat.add(Nat.double(_), 0n) : Nat}
              {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match k:
            case 0n:
              %E.Nat.sym(Word.to_nat(1n+p, Word.and(1n+p, WCon{b, t},
                W.Word.low_mask(1n+p, 0n))), 0n,
                Word.and_low_mask_zero(1n+p, WCon{b, t}))
                : {Word.to_nat(1n+p, WCon{b, t})
                  == Nat.add(Word.to_nat(1n+p, WCon{b, t}), _) : Nat}
              E.Nat.sym(Nat.add(Word.to_nat(1n+p, WCon{b, t}), 0n),
                Word.to_nat(1n+p, WCon{b, t}),
                N.Nat.add_zero(Word.to_nat(1n+p, WCon{b, t})))
            case 1n+j:
              Word.to_nat_split.step(p, b, t, j,
                Word.to_nat_split(p, t, j))

# ---------------------------------------------------------------------------
# At `U32`, and then addressing fact A3.
# ---------------------------------------------------------------------------

law U32.shrn_word:
  for +x: U32
  for +k: Nat
  {U32.shrn(x, k) == U32{Word.shrn(32n, W.U32.word(x), k)} : U32}

def U32.shrn_word(x, k):
  match x:
    case U32{w}:
      match k:
        case 0n:
          {==}
        case 1n+j:
          %E.U32.sym(U32.shrn(U32{w}, j),
            U32{Word.shrn(32n, w, j)}, U32.shrn_word(U32{w}, j))
            : {U32.shr(_)
              == U32{Word.shrn(32n, w, 1n+j)} : U32}
          {==}

law U32.to_nat_split:
  for +x: U32
  {U32.to_nat(x)
    == Nat.add(Nat.dbl(5n, U32.to_nat(U32.shrn(x, 5n))),
         U32.to_nat(U32.and(x, 31))) : Nat}

def U32.to_nat_split(x):
  match x:
    case U32{w}:
      %U32.shrn_word(U32{w}, 5n)
        : {Word.to_nat(32n, w)
          == Nat.add(Nat.dbl(5n, U32.to_nat(_)),
               Word.to_nat(32n, Word.and(32n, w,
                 W.Word.low_mask(32n, 5n)))) : Nat}
      Word.to_nat_split(32n, w, 5n)

def Nat.hi_at(+m: Nat, y: Nat) -> Nat:
  Nat.add(Nat.dbl(5n, y), m)

def Nat.lo_at(+a: Nat, m: Nat) -> Nat:
  Nat.add(a, m)

law U32.address_inj:
  for +o: U32
  for +x: U32
  for +ei: {U32.to_nat(U32.shrn(o, 5n))
    == U32.to_nat(U32.shrn(x, 5n)) : Nat}
  for +eb: {U32.to_nat(U32.and(o, 31))
    == U32.to_nat(U32.and(x, 31)) : Nat}
  {o == x : U32}

def U32.address_inj(o, x, ei, eb):
  Ij.U32.to_nat_inj(o, x,
    Equal.trans(Nat, U32.to_nat(o),
      Nat.add(Nat.dbl(5n, U32.to_nat(U32.shrn(o, 5n))),
        U32.to_nat(U32.and(o, 31))), U32.to_nat(x),
      U32.to_nat_split(o),
      Equal.trans(Nat,
        Nat.add(Nat.dbl(5n, U32.to_nat(U32.shrn(o, 5n))),
          U32.to_nat(U32.and(o, 31))),
        Nat.add(Nat.dbl(5n, U32.to_nat(U32.shrn(x, 5n))),
          U32.to_nat(U32.and(x, 31))), U32.to_nat(x),
        Equal.trans(Nat,
          Nat.add(Nat.dbl(5n, U32.to_nat(U32.shrn(o, 5n))),
            U32.to_nat(U32.and(o, 31))),
          Nat.add(Nat.dbl(5n, U32.to_nat(U32.shrn(x, 5n))),
            U32.to_nat(U32.and(o, 31))),
          Nat.add(Nat.dbl(5n, U32.to_nat(U32.shrn(x, 5n))),
            U32.to_nat(U32.and(x, 31))),
          Equal.cong(Nat, Nat, Nat.hi_at(U32.to_nat(U32.and(o, 31))),
            U32.to_nat(U32.shrn(o, 5n)), U32.to_nat(U32.shrn(x, 5n)), ei),
          Equal.cong(Nat, Nat,
            Nat.lo_at(Nat.dbl(5n, U32.to_nat(U32.shrn(x, 5n)))),
            U32.to_nat(U32.and(o, 31)), U32.to_nat(U32.and(x, 31)), eb)),
        E.Nat.sym(U32.to_nat(x),
          Nat.add(Nat.dbl(5n, U32.to_nat(U32.shrn(x, 5n))),
            U32.to_nat(U32.and(x, 31))), U32.to_nat_split(x)))))
