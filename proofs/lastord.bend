# proofs/lastord.bend -- the last ordinal of a node's interval.
#
# `PSet.members` starts a full node's count-down at `base + h + h - 1`, the
# last ordinal the node covers. Reading that as a number is the one place the
# walk's own arithmetic has to be accounted for, and it is the one place a
# node at the very top of the address space would overflow: the widest
# possible node has `base + h + h` equal to 2^32, which is not a `U32`.
#
# So the accounting is done without numbers. Doubling the half and taking one
# away is, bit for bit, filling the node's own low bits: the result is
# `base | mask`, which wraps exactly the way the walk does and needs no
# bound at all. Only then is it read as a number, through the `or`, where
# nothing carries and the reading splits.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./inject.bend as Ij
import ./split.bend as Sp
import ./descend.bend as Dc
import ./split_add.bend as Sa
import ./decr.bend as De
import ./interval.bend as It
import ../core/count.bend as C
import ../core/word.bend as W

# ---------------------------------------------------------------------------
# Four small identities about the adder at zero.
# ---------------------------------------------------------------------------

law Word.add_zeros:
  for +n: Nat
  for +t: Word(n)
  {Word.adc(n, t, Dc.Word.zeros(n), False{}, False{}) == t : Word(n)}

def Word.add_zeros(n, t):
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{b, u}:
          match b:
            case False{}:
              %E.Word.sym(p, Word.adc(p, u, Dc.Word.zeros(p),
                  False{}, False{}), u, Word.add_zeros(p, u))
                : {WCon{False{}, _} == WCon{False{}, u} : Word(1n+p)}
              {==}
            case True{}:
              %E.Word.sym(p, Word.adc(p, u, Dc.Word.zeros(p),
                  False{}, False{}), u, Word.add_zeros(p, u))
                : {WCon{True{}, _} == WCon{True{}, u} : Word(1n+p)}
              {==}

law Word.add_one:
  for +n: Nat
  for +t: Word(n)
  {Word.adc(n, t, Dc.Word.zeros(n), False{}, True{})
    == Word.inc(n, t) : Word(n)}

def Word.add_one(n, t):
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{b, u}:
          match b:
            case False{}:
              %E.Word.sym(p, Word.adc(p, u, Dc.Word.zeros(p),
                  False{}, False{}), u, Word.add_zeros(p, u))
                : {WCon{True{}, _} == WCon{True{}, u} : Word(1n+p)}
              {==}
            case True{}:
              %E.Word.sym(p, Word.adc(p, u, Dc.Word.zeros(p),
                  False{}, True{}), Word.inc(p, u), Word.add_one(p, u))
                : {WCon{False{}, _}
                  == WCon{False{}, Word.inc(p, u)} : Word(1n+p)}
              {==}

law Word.dec_inc:
  for +n: Nat
  for +t: Word(n)
  {De.Word.dec(n, Word.inc(n, t)) == t : Word(n)}

def Word.dec_inc(n, t):
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{b, u}:
          match b:
            case False{}:
              %E.Word.sym(p, Word.adc(p, u, Dc.Word.zeros(p),
                  True{}, True{}), u, Dc.Word.adc_sub_zero(p, u))
                : {WCon{False{}, _} == WCon{False{}, u} : Word(1n+p)}
              {==}
            case True{}:
              %E.Word.sym(p, De.Word.dec(p, Word.inc(p, u)), u,
                  Word.dec_inc(p, u))
                : {WCon{True{}, _} == WCon{True{}, u} : Word(1n+p)}
              {==}

law Word.or_mask_zero:
  for +n: Nat
  for +t: Word(n)
  {Word.or(n, t, W.Word.low_mask(n, 0n)) == t : Word(n)}

def Word.or_mask_zero(n, t):
  match n:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+p:
      match t:
        case WCon{b, u}:
          match b:
            case False{}:
              %E.Word.sym(p, Word.or(p, u, W.Word.low_mask(p, 0n)), u,
                  Word.or_mask_zero(p, u))
                : {WCon{False{}, _} == WCon{False{}, u} : Word(1n+p)}
              {==}
            case True{}:
              %E.Word.sym(p, Word.or(p, u, W.Word.low_mask(p, 0n)), u,
                  Word.or_mask_zero(p, u))
                : {WCon{True{}, _} == WCon{True{}, u} : Word(1n+p)}
              {==}

# ---------------------------------------------------------------------------
# Doubling the half and taking one away fills the node's low bits.
# ---------------------------------------------------------------------------

law Word.double_step:
  for +n: Nat
  for +w: Word(n)
  for +j: Nat
  for +lz: {Sa.Word.lo_zero(n, w, 1n+j) == True{} : Bool}
  {De.Word.dec(n, Word.adc(n,
    Word.adc(n, w, Dc.Word.pow2(n, j), False{}, False{}),
    Dc.Word.pow2(n, j), False{}, False{}))
    == Word.or(n, w, W.Word.low_mask(n, 1n+j)) : Word(n)}

def Word.double_step(n, w, j, lz):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case False{}:
              match j:
                case 0n:
                  %E.Word.sym(p, Word.adc(p, t, Dc.Word.zeros(p),
                      False{}, False{}), t, Word.add_zeros(p, t))
                    : {WCon{True{}, De.Word.dec(p, Word.adc(p, _,
                        Dc.Word.zeros(p), False{}, True{}))}
                      == Word.or(1n+p, WCon{False{}, t},
                        W.Word.low_mask(1n+p, 1n)) : Word(1n+p)}
                  %E.Word.sym(p, Word.adc(p, t, Dc.Word.zeros(p),
                      False{}, True{}), Word.inc(p, t),
                    Word.add_one(p, t))
                    : {WCon{True{}, De.Word.dec(p, _)}
                      == Word.or(1n+p, WCon{False{}, t},
                        W.Word.low_mask(1n+p, 1n)) : Word(1n+p)}
                  %E.Word.sym(p, De.Word.dec(p, Word.inc(p, t)), t,
                    Word.dec_inc(p, t))
                    : {WCon{True{}, _}
                      == Word.or(1n+p, WCon{False{}, t},
                        W.Word.low_mask(1n+p, 1n)) : Word(1n+p)}
                  %E.Word.sym(p, Word.or(p, t,
                      W.Word.low_mask(p, 0n)), t, Word.or_mask_zero(p, t))
                    : {WCon{True{}, t} == WCon{True{}, _} : Word(1n+p)}
                  {==}
                case 1n+i:
                  %E.Word.sym(p, De.Word.dec(p, Word.adc(p,
                      Word.adc(p, t, Dc.Word.pow2(p, i), False{},
                        False{}), Dc.Word.pow2(p, i), False{}, False{})),
                    Word.or(p, t, W.Word.low_mask(p, 1n+i)),
                    Word.double_step(p, t, i, lz))
                    : {WCon{True{}, _}
                      == Word.or(1n+p, WCon{False{}, t},
                        W.Word.low_mask(1n+p, 2n+i)) : Word(1n+p)}
                  {==}
            case True{}:
              E.Bool.noconf({De.Word.dec(1n+p, Word.adc(1n+p,
                Word.adc(1n+p, WCon{True{}, t},
                  Dc.Word.pow2(1n+p, j), False{}, False{}),
                Dc.Word.pow2(1n+p, j), False{}, False{}))
                == Word.or(1n+p, WCon{True{}, t},
                  W.Word.low_mask(1n+p, 1n+j)) : Word(1n+p)}, lz)

# ---------------------------------------------------------------------------
# Reading the pieces as numbers.
# ---------------------------------------------------------------------------

law Word.to_nat_zeros:
  for +n: Nat
  {Word.to_nat(n, Dc.Word.zeros(n)) == 0n : Nat}

def Word.to_nat_zeros(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %E.Nat.sym(Word.to_nat(p, Dc.Word.zeros(p)), 0n,
        Word.to_nat_zeros(p))
        : {Nat.double(_) == 0n : Nat}
      {==}

law Word.to_nat_mask_zero:
  for +n: Nat
  {Word.to_nat(n, W.Word.low_mask(n, 0n)) == 0n : Nat}

def Word.to_nat_mask_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %E.Nat.sym(Word.to_nat(p, W.Word.low_mask(p, 0n)), 0n,
        Word.to_nat_mask_zero(p))
        : {Nat.double(_) == 0n : Nat}
      {==}

law Word.to_nat_pow2:
  for +n: Nat
  for +k: Nat
  for +lt: {C.Nat.gt(n, k) == True{} : Bool}
  {Word.to_nat(n, Dc.Word.pow2(n, k)) == Dc.Nat.pow2(k) : Nat}

def Word.to_nat_pow2(n, k, lt):
  match n:
    case 0n:
      E.Bool.noconf({Word.to_nat(0n, Dc.Word.pow2(0n, k))
        == Dc.Nat.pow2(k) : Nat}, lt)
    case 1n+p:
      match k:
        case 0n:
          %E.Nat.sym(Word.to_nat(p, Dc.Word.zeros(p)), 0n,
            Word.to_nat_zeros(p))
            : {1n+Nat.double(_) == 1n : Nat}
          {==}
        case 1n+j:
          %E.Nat.sym(Word.to_nat(p, Dc.Word.pow2(p, j)),
            Dc.Nat.pow2(j), Word.to_nat_pow2(p, j, lt))
            : {Nat.double(_) == Nat.double(Dc.Nat.pow2(j)) : Nat}
          {==}

law Word.to_nat_low_mask:
  for +n: Nat
  for +k: Nat
  for +le: {C.Nat.upto(k, n) == True{} : Bool}
  {Word.to_nat(n, W.Word.low_mask(n, k))
    == Nat.sub(Dc.Nat.pow2(k), 1n) : Nat}

def Word.to_nat_low_mask(n, k, le):
  match n:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+j:
          E.Bool.noconf({Word.to_nat(0n, W.Word.low_mask(0n, 1n+j))
            == Nat.sub(Dc.Nat.pow2(1n+j), 1n) : Nat}, le)
    case 1n+p:
      match k:
        case 0n:
          Word.to_nat_mask_zero(1n+p)
        case 1n+j:
          %E.Nat.sym(Word.to_nat(p, W.Word.low_mask(p, j)),
            Nat.sub(Dc.Nat.pow2(j), 1n),
            Word.to_nat_low_mask(p, j, le))
            : {1n+Nat.double(_)
              == Nat.sub(Nat.double(Dc.Nat.pow2(j)), 1n) : Nat}
          De.Nat.dec_double(Dc.Nat.pow2(j), Dc.Nat.pow2_pos(j))

law Word.hi_zero_mask:
  for +n: Nat
  for +k: Nat
  {Dc.Word.hi_zero(n, W.Word.low_mask(n, k), k) == True{} : Bool}

def Word.hi_zero_mask(n, k):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match k:
        case 0n:
          Word.hi_zero_mask(p, 0n)
        case 1n+j:
          Word.hi_zero_mask(p, j)

law Word.or_comm:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.or(n, a, b) == Word.or(n, b, a) : Word(n)}

law Word.or_comm.bit:
  for +a: Bool
  for +b: Bool
  {Bool.or(a, b) == Bool.or(b, a) : Bool}

def Word.or_comm.bit(a, b):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Word.or_comm(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          %E.Word.sym(p, Word.or(p, at, bt), Word.or(p, bt, at),
            Word.or_comm(p, at, bt))
            : {WCon{Bool.or(ab, bb), _}
              == WCon{Bool.or(bb, ab), Word.or(p, bt, at)} : Word(1n+p)}
          %E.Bool.sym(Bool.or(ab, bb), Bool.or(bb, ab),
            Word.or_comm.bit(ab, bb))
            : {WCon{_, Word.or(p, bt, at)}
              == WCon{Bool.or(bb, ab), Word.or(p, bt, at)} : Word(1n+p)}
          {==}

law Nat.sub_add_swap:
  for +a: Nat
  for +b: Nat
  for +pos: {C.Nat.gt(b, 0n) == True{} : Bool}
  {Nat.add(Nat.sub(b, 1n), a) == Nat.sub(Nat.add(a, b), 1n) : Nat}

def Nat.sub_add_swap(a, b, pos):
  match b:
    case 0n:
      E.Bool.noconf({Nat.add(Nat.sub(0n, 1n), a)
        == Nat.sub(Nat.add(a, 0n), 1n) : Nat}, pos)
    case 1n+q:
      %E.Nat.sym(Nat.add(a, 1n+q), 1n+Nat.add(a, q),
        N.Nat.add_succ(a, q))
        : {Nat.add(Nat.sub(1n+q, 1n), a) == Nat.sub(_, 1n) : Nat}
      %E.Nat.sym(Nat.sub(q, 0n), q, De.Nat.sub_zero(q))
        : {Nat.add(_, a) == Nat.sub(1n+Nat.add(a, q), 1n) : Nat}
      %E.Nat.sym(Nat.sub(Nat.add(a, q), 0n), Nat.add(a, q),
        De.Nat.sub_zero(Nat.add(a, q)))
        : {Nat.add(q, a) == _ : Nat}
      N.Nat.add_comm(q, a)

# ---------------------------------------------------------------------------
# At `U32`: the walk's own expression, and what it reads as.
# ---------------------------------------------------------------------------

law U32.last_ordinal:
  for +base: U32
  for +j: Nat
  for +lz: {Sa.U32.lo_zero(base, 1n+j) == True{} : Bool}
  {(base + U32.shln(1, j) + U32.shln(1, j) - 1 : U32)
    == U32.or(base, W.U32.mask(1n+j)) : U32}

def U32.last_ordinal(base, j, lz):
  match base:
    case U32{bw}:
      %E.U32.sym(U32.shln(1, j), U32{Dc.Word.pow2(32n, j)},
        Dc.U32.shln_one_pow2(j))
        : {(U32{bw} + _ + _ - 1 : U32)
          == U32.or(U32{bw}, W.U32.mask(1n+j)) : U32}
      %E.U32.sym(U32.sub((U32{bw} + U32{Dc.Word.pow2(32n, j)}
          + U32{Dc.Word.pow2(32n, j)} : U32), 1),
        U32{De.Word.dec(32n, W.U32.word((U32{bw}
          + U32{Dc.Word.pow2(32n, j)}
          + U32{Dc.Word.pow2(32n, j)} : U32)))},
        De.U32.sub_one_is_dec((U32{bw} + U32{Dc.Word.pow2(32n, j)}
          + U32{Dc.Word.pow2(32n, j)} : U32)))
        : {_ == U32.or(U32{bw}, W.U32.mask(1n+j)) : U32}
      Equal.cong(Word(32n), U32, E.U32.pak,
        De.Word.dec(32n, Word.adc(32n,
          Word.adc(32n, bw, Dc.Word.pow2(32n, j), False{}, False{}),
          Dc.Word.pow2(32n, j), False{}, False{})),
        Word.or(32n, bw, W.Word.low_mask(32n, 1n+j)),
        Word.double_step(32n, bw, j, lz))

law U32.last_ordinal_value:
  for +base: U32
  for +j: Nat
  for +lz: {Sa.U32.lo_zero(base, 1n+j) == True{} : Bool}
  for +le: {C.Nat.upto(1n+j, 32n) == True{} : Bool}
  {U32.to_nat((base + U32.shln(1, j) + U32.shln(1, j) - 1 : U32))
    == Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(1n+j)), 1n) : Nat}

law U32.or_comm:
  for +a: U32
  for +b: U32
  {U32.or(a, b) == U32.or(b, a) : U32}

def U32.or_comm(a, b):
  match a b:
    case U32{aw} U32{bw}:
      Equal.cong(Word(32n), U32, E.U32.pak,
        Word.or(32n, aw, bw), Word.or(32n, bw, aw),
        Word.or_comm(32n, aw, bw))

law U32.hi_zero_mask:
  for +k: Nat
  {Dc.U32.hi_zero(W.U32.mask(k), k) == True{} : Bool}

def U32.hi_zero_mask(k):
  Word.hi_zero_mask(32n, k)

law U32.to_nat_mask:
  for +k: Nat
  for +le: {C.Nat.upto(k, 32n) == True{} : Bool}
  {U32.to_nat(W.U32.mask(k)) == Nat.sub(Dc.Nat.pow2(k), 1n) : Nat}

def U32.to_nat_mask(k, le):
  Word.to_nat_low_mask(32n, k, le)

def U32.last_ordinal_value(base, j, lz, le):
  %E.U32.sym((base + U32.shln(1, j) + U32.shln(1, j) - 1 : U32),
    U32.or(base, W.U32.mask(1n+j)), U32.last_ordinal(base, j, lz))
    : {U32.to_nat(_)
      == Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(1n+j)), 1n)
      : Nat}
  %U32.or_comm(W.U32.mask(1n+j), base)
    : {U32.to_nat(_)
      == Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(1n+j)), 1n)
      : Nat}
  %E.Nat.sym(U32.to_nat(U32.or(W.U32.mask(1n+j), base)),
    Nat.add(U32.to_nat(W.U32.mask(1n+j)), U32.to_nat(base)),
    Sa.U32.to_nat_or(W.U32.mask(1n+j), base, 1n+j,
      U32.hi_zero_mask(1n+j), lz))
    : {_ == Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(1n+j)), 1n)
      : Nat}
  %E.Nat.sym(U32.to_nat(W.U32.mask(1n+j)),
    Nat.sub(Dc.Nat.pow2(1n+j), 1n), U32.to_nat_mask(1n+j, le))
    : {Nat.add(_, U32.to_nat(base))
      == Nat.sub(Nat.add(U32.to_nat(base), Dc.Nat.pow2(1n+j)), 1n)
      : Nat}
  Nat.sub_add_swap(U32.to_nat(base), Dc.Nat.pow2(1n+j),
    Dc.Nat.pow2_pos(1n+j))

law Nat.double_is_add:
  for +a: Nat
  {Nat.add(a, a) == Nat.double(a) : Nat}

def Nat.double_is_add(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %E.Nat.sym(Nat.add(p, 1n+p), 1n+Nat.add(p, p),
        N.Nat.add_succ(p, p))
        : {1n+_ == Nat.double(1n+p) : Nat}
      %E.Nat.sym(Nat.add(p, p), Nat.double(p), Nat.double_is_add(p))
        : {2n+_ == Nat.double(1n+p) : Nat}
      {==}

law U32.full_node_count:
  for +j: Nat
  for +lt: {C.Nat.gt(32n, j) == True{} : Bool}
  {Nat.add(U32.to_nat(U32.shln(1, j)), U32.to_nat(U32.shln(1, j)))
    == Dc.Nat.pow2(1n+j) : Nat}

law U32.to_nat_shln:
  for +j: Nat
  for +lt: {C.Nat.gt(32n, j) == True{} : Bool}
  {U32.to_nat(U32.shln(1, j)) == Dc.Nat.pow2(j) : Nat}

def U32.to_nat_shln(j, lt):
  %E.U32.sym(U32.shln(1, j), U32{Dc.Word.pow2(32n, j)},
    Dc.U32.shln_one_pow2(j))
    : {U32.to_nat(_) == Dc.Nat.pow2(j) : Nat}
  Word.to_nat_pow2(32n, j, lt)

def U32.full_node_count(j, lt):
  %E.Nat.sym(U32.to_nat(U32.shln(1, j)), Dc.Nat.pow2(j),
    U32.to_nat_shln(j, lt))
    : {Nat.add(_, _) == Dc.Nat.pow2(1n+j) : Nat}
  Nat.double_is_add(Dc.Nat.pow2(j))
