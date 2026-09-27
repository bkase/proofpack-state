# proofs/leafops.bend -- the leaf operations are pointwise (law S-02, at the
# leaf).
#
# A leaf operation converts both operands to words, works there, and
# compresses the result back. Each of those three steps is now proved:
# conversion is faithful (proofs/faithful.bend), the tile kernel is pointwise
# (proofs/words.bend, law S-01), and compression changes no member
# (proofs/compress.bend, law S-03). This file puts them together.
#
# The hypotheses are the same three throughout: both operands are
# structurally valid leaves, and the ordinal is one the leaf covers.

import Base
import ./eq.bend as E
import ./words.bend as PWo
import ./faithful.bend as Fa
import ./compress.bend as Cp
import ./leaf.bend as Lf
import ./descend.bend as Dc
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# The kernels keep a tile 128 words wide.
# ---------------------------------------------------------------------------

law Words.len_diff:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {List.length(&2, U32, Wo.Words.diff(a, b))
    == List.length(&2, U32, a) : Nat}

def Words.len_diff(a, b):
  match a:
    case Nil{}:
      {==}
    case Con{ah, at}:
      match b:
        case Nil{}:
          {==}
        case Con{bh, bt}:
          %E.Nat.sym(List.length(&2, U32, Wo.Words.diff(at, bt)),
            List.length(&2, U32, at), Words.len_diff(at, bt))
            : {1n+_ == 1n+List.length(&2, U32, at) : Nat}
          {==}

law Words.len_and:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +e: {List.length(&2, U32, a) == List.length(&2, U32, b) : Nat}
  {List.length(&2, U32, Wo.Words.and(a, b))
    == List.length(&2, U32, a) : Nat}

def Words.len_and(a, b, e):
  match a:
    case Nil{}:
      {==}
    case Con{ah, at}:
      match b:
        case Nil{}:
          E.Nat.noconf2({List.length(&2, U32, Wo.Words.and(Con{ah, at},
            Nil{})) == List.length(&2, U32, Con{ah, at}) : Nat},
            List.length(&2, U32, at), e)
        case Con{bh, bt}:
          %E.Nat.sym(List.length(&2, U32, Wo.Words.and(at, bt)),
            List.length(&2, U32, at),
            Words.len_and(at, bt,
              Lf.Nat.succ_inj2(List.length(&2, U32, at),
                List.length(&2, U32, bt), e)))
            : {1n+_ == 1n+List.length(&2, U32, at) : Nat}
          {==}

law Words.len_or:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +e: {List.length(&2, U32, a) == List.length(&2, U32, b) : Nat}
  {List.length(&2, U32, Wo.Words.or(a, b))
    == List.length(&2, U32, a) : Nat}

def Words.len_or(a, b, e):
  match a:
    case Nil{}:
      E.Nat.sym(List.length(&2, U32, Nil{}),
        List.length(&2, U32, b), e)
    case Con{ah, at}:
      match b:
        case Nil{}:
          {==}
        case Con{bh, bt}:
          %E.Nat.sym(List.length(&2, U32, Wo.Words.or(at, bt)),
            List.length(&2, U32, at),
            Words.len_or(at, bt,
              Lf.Nat.succ_inj2(List.length(&2, U32, at),
                List.length(&2, U32, bt), e)))
            : {1n+_ == 1n+List.length(&2, U32, at) : Nat}
          {==}

# ---------------------------------------------------------------------------
# The three operations. Each non-shortcut arm is the same three steps:
# convert, work in words, compress back.
# ---------------------------------------------------------------------------

law PSet.diff_leaf_pointwise:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.diff.leaf(a, b), x)
    == Bool.and(S.PSet.mem.leaf(a, x),
         Bool.not(S.PSet.mem.leaf(b, x))) : Bool}

# The shared shape: `compress(diff(words of a, words of b))`.
law PSet.op_leaf:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.compress(Wo.Words.diff(
      S.PSet.leaf_words(a), S.PSet.leaf_words(b))), x)
    == Bool.and(S.PSet.mem.leaf(a, x),
         Bool.not(S.PSet.mem.leaf(b, x))) : Bool}

law PSet.diff_width:
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  {List.length(&2, U32, Wo.Words.diff(S.PSet.leaf_words(a),
    S.PSet.leaf_words(b))) == 128n : Nat}

def PSet.diff_width(a, b, va):
  Equal.trans(Nat,
    List.length(&2, U32, Wo.Words.diff(S.PSet.leaf_words(a),
      S.PSet.leaf_words(b))),
    List.length(&2, U32, S.PSet.leaf_words(a)), 128n,
    Words.len_diff(S.PSet.leaf_words(a), S.PSet.leaf_words(b)),
    Lf.PSet.leaf_words_width(a, va))

def PSet.op_leaf(a, b, x, va, vb, inr):
  %E.Bool.sym(S.PSet.mem.leaf(S.PSet.compress(Wo.Words.diff(
      S.PSet.leaf_words(a), S.PSet.leaf_words(b))), x),
    Wo.Words.bit(Wo.Words.diff(S.PSet.leaf_words(a),
      S.PSet.leaf_words(b)), x),
    Cp.PSet.compress_keeps(Wo.Words.diff(S.PSet.leaf_words(a),
      S.PSet.leaf_words(b)), x, PSet.diff_width(a, b, va), inr))
    : {_ == Bool.and(S.PSet.mem.leaf(a, x),
         Bool.not(S.PSet.mem.leaf(b, x))) : Bool}
  %E.Bool.sym(Wo.Words.at(Wo.Words.diff(S.PSet.leaf_words(a),
      S.PSet.leaf_words(b)), U32.to_nat(U32.shrn(x, 5n)),
      U32.to_nat(U32.and(x, 31))),
    Bool.and(Wo.Words.bit(S.PSet.leaf_words(a), x),
      Bool.not(Wo.Words.bit(S.PSet.leaf_words(b), x))),
    PWo.Words.at_diff(S.PSet.leaf_words(a), S.PSet.leaf_words(b),
      U32.to_nat(U32.shrn(x, 5n)), U32.to_nat(U32.and(x, 31))))
    : {_ == Bool.and(S.PSet.mem.leaf(a, x),
         Bool.not(S.PSet.mem.leaf(b, x))) : Bool}
  %Fa.PSet.leaf_faithful(a, x, va, inr)
    : {Bool.and(_, Bool.not(Wo.Words.bit(S.PSet.leaf_words(b), x)))
      == Bool.and(S.PSet.mem.leaf(a, x),
           Bool.not(S.PSet.mem.leaf(b, x))) : Bool}
  %Fa.PSet.leaf_faithful(b, x, vb, inr)
    : {Bool.and(S.PSet.mem.leaf(a, x), Bool.not(_))
      == Bool.and(S.PSet.mem.leaf(a, x),
           Bool.not(S.PSet.mem.leaf(b, x))) : Bool}
  {==}

def PSet.diff_leaf_pointwise(a, b, x, va, vb, inr):
  match a:
    case S.PZero{}:
      {==}
    case S.PBranch{l, h}:
      E.Bool.noconf({S.PSet.mem.leaf(S.PSet.diff.leaf(S.PBranch{l, h}, b),
        x) == Bool.and(S.PSet.mem.leaf(S.PBranch{l, h}, x),
          Bool.not(S.PSet.mem.leaf(b, x))) : Bool}, va)
    case S.PFull{}:
      PSet.op_leaf(S.PFull{}, b, x, va, vb, inr)
    case S.PSparse{o}:
      PSet.op_leaf(S.PSparse{o}, b, x, va, vb, inr)
    case S.PDense{w}:
      PSet.op_leaf(S.PDense{w}, b, x, va, vb, inr)

law PSet.union_leaf_pointwise:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.union.leaf(a, b), x)
    == Bool.or(S.PSet.mem.leaf(a, x), S.PSet.mem.leaf(b, x)) : Bool}

law PSet.or_leaf:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.compress(Wo.Words.or(
      S.PSet.leaf_words(a), S.PSet.leaf_words(b))), x)
    == Bool.or(S.PSet.mem.leaf(a, x), S.PSet.mem.leaf(b, x)) : Bool}

law PSet.pair_width_or:
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  {List.length(&2, U32, Wo.Words.or(S.PSet.leaf_words(a),
    S.PSet.leaf_words(b))) == 128n : Nat}

law PSet.same_width:
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  {List.length(&2, U32, S.PSet.leaf_words(a))
    == List.length(&2, U32, S.PSet.leaf_words(b)) : Nat}

def PSet.same_width(a, b, va, vb):
  Equal.trans(Nat, List.length(&2, U32, S.PSet.leaf_words(a)), 128n,
    List.length(&2, U32, S.PSet.leaf_words(b)),
    Lf.PSet.leaf_words_width(a, va),
    E.Nat.sym(List.length(&2, U32, S.PSet.leaf_words(b)), 128n,
      Lf.PSet.leaf_words_width(b, vb)))

def PSet.pair_width_or(a, b, va, vb):
  Equal.trans(Nat,
    List.length(&2, U32, Wo.Words.or(S.PSet.leaf_words(a),
      S.PSet.leaf_words(b))),
    List.length(&2, U32, S.PSet.leaf_words(a)), 128n,
    Words.len_or(S.PSet.leaf_words(a), S.PSet.leaf_words(b),
      PSet.same_width(a, b, va, vb)),
    Lf.PSet.leaf_words_width(a, va))

def PSet.or_leaf(a, b, x, va, vb, inr):
  %E.Bool.sym(S.PSet.mem.leaf(S.PSet.compress(Wo.Words.or(
      S.PSet.leaf_words(a), S.PSet.leaf_words(b))), x),
    Wo.Words.bit(Wo.Words.or(S.PSet.leaf_words(a),
      S.PSet.leaf_words(b)), x),
    Cp.PSet.compress_keeps(Wo.Words.or(S.PSet.leaf_words(a),
      S.PSet.leaf_words(b)), x, PSet.pair_width_or(a, b, va, vb), inr))
    : {_ == Bool.or(S.PSet.mem.leaf(a, x),
         S.PSet.mem.leaf(b, x)) : Bool}
  %E.Bool.sym(Wo.Words.at(Wo.Words.or(S.PSet.leaf_words(a),
      S.PSet.leaf_words(b)), U32.to_nat(U32.shrn(x, 5n)),
      U32.to_nat(U32.and(x, 31))),
    Bool.or(Wo.Words.bit(S.PSet.leaf_words(a), x),
      Wo.Words.bit(S.PSet.leaf_words(b), x)),
    PWo.Words.at_or(S.PSet.leaf_words(a), S.PSet.leaf_words(b),
      U32.to_nat(U32.shrn(x, 5n)), U32.to_nat(U32.and(x, 31))))
    : {_ == Bool.or(S.PSet.mem.leaf(a, x),
         S.PSet.mem.leaf(b, x)) : Bool}
  %Fa.PSet.leaf_faithful(a, x, va, inr)
    : {Bool.or(_, Wo.Words.bit(S.PSet.leaf_words(b), x))
      == Bool.or(S.PSet.mem.leaf(a, x), S.PSet.mem.leaf(b, x)) : Bool}
  %Fa.PSet.leaf_faithful(b, x, vb, inr)
    : {Bool.or(S.PSet.mem.leaf(a, x), _)
      == Bool.or(S.PSet.mem.leaf(a, x), S.PSet.mem.leaf(b, x)) : Bool}
  {==}

def PSet.union_leaf_pointwise(a, b, x, va, vb, inr):
  match a:
    case S.PZero{}:
      {==}
    case S.PFull{}:
      {==}
    case S.PBranch{l, h}:
      E.Bool.noconf({S.PSet.mem.leaf(S.PSet.union.leaf(S.PBranch{l, h},
        b), x) == Bool.or(S.PSet.mem.leaf(S.PBranch{l, h}, x),
          S.PSet.mem.leaf(b, x)) : Bool}, va)
    case S.PSparse{o}:
      PSet.or_leaf(S.PSparse{o}, b, x, va, vb, inr)
    case S.PDense{w}:
      PSet.or_leaf(S.PDense{w}, b, x, va, vb, inr)

law PSet.inter_leaf_pointwise:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.inter.leaf(a, b), x)
    == Bool.and(S.PSet.mem.leaf(a, x), S.PSet.mem.leaf(b, x)) : Bool}

law PSet.and_leaf:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.compress(Wo.Words.and(
      S.PSet.leaf_words(a), S.PSet.leaf_words(b))), x)
    == Bool.and(S.PSet.mem.leaf(a, x), S.PSet.mem.leaf(b, x)) : Bool}

law PSet.pair_width_and:
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  {List.length(&2, U32, Wo.Words.and(S.PSet.leaf_words(a),
    S.PSet.leaf_words(b))) == 128n : Nat}

def PSet.pair_width_and(a, b, va, vb):
  Equal.trans(Nat,
    List.length(&2, U32, Wo.Words.and(S.PSet.leaf_words(a),
      S.PSet.leaf_words(b))),
    List.length(&2, U32, S.PSet.leaf_words(a)), 128n,
    Words.len_and(S.PSet.leaf_words(a), S.PSet.leaf_words(b),
      PSet.same_width(a, b, va, vb)),
    Lf.PSet.leaf_words_width(a, va))

def PSet.and_leaf(a, b, x, va, vb, inr):
  %E.Bool.sym(S.PSet.mem.leaf(S.PSet.compress(Wo.Words.and(
      S.PSet.leaf_words(a), S.PSet.leaf_words(b))), x),
    Wo.Words.bit(Wo.Words.and(S.PSet.leaf_words(a),
      S.PSet.leaf_words(b)), x),
    Cp.PSet.compress_keeps(Wo.Words.and(S.PSet.leaf_words(a),
      S.PSet.leaf_words(b)), x, PSet.pair_width_and(a, b, va, vb), inr))
    : {_ == Bool.and(S.PSet.mem.leaf(a, x),
         S.PSet.mem.leaf(b, x)) : Bool}
  %E.Bool.sym(Wo.Words.at(Wo.Words.and(S.PSet.leaf_words(a),
      S.PSet.leaf_words(b)), U32.to_nat(U32.shrn(x, 5n)),
      U32.to_nat(U32.and(x, 31))),
    Bool.and(Wo.Words.bit(S.PSet.leaf_words(a), x),
      Wo.Words.bit(S.PSet.leaf_words(b), x)),
    PWo.Words.at_and(S.PSet.leaf_words(a), S.PSet.leaf_words(b),
      U32.to_nat(U32.shrn(x, 5n)), U32.to_nat(U32.and(x, 31))))
    : {_ == Bool.and(S.PSet.mem.leaf(a, x),
         S.PSet.mem.leaf(b, x)) : Bool}
  %Fa.PSet.leaf_faithful(a, x, va, inr)
    : {Bool.and(_, Wo.Words.bit(S.PSet.leaf_words(b), x))
      == Bool.and(S.PSet.mem.leaf(a, x), S.PSet.mem.leaf(b, x)) : Bool}
  %Fa.PSet.leaf_faithful(b, x, vb, inr)
    : {Bool.and(S.PSet.mem.leaf(a, x), _)
      == Bool.and(S.PSet.mem.leaf(a, x), S.PSet.mem.leaf(b, x)) : Bool}
  {==}

def PSet.inter_leaf_pointwise(a, b, x, va, vb, inr):
  match a:
    case S.PZero{}:
      {==}
    case S.PFull{}:
      {==}
    case S.PBranch{l, h}:
      E.Bool.noconf({S.PSet.mem.leaf(S.PSet.inter.leaf(S.PBranch{l, h},
        b), x) == Bool.and(S.PSet.mem.leaf(S.PBranch{l, h}, x),
          S.PSet.mem.leaf(b, x)) : Bool}, va)
    case S.PSparse{o}:
      PSet.and_leaf(S.PSparse{o}, b, x, va, vb, inr)
    case S.PDense{w}:
      PSet.and_leaf(S.PDense{w}, b, x, va, vb, inr)
