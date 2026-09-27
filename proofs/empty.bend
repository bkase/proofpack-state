# proofs/empty.bend -- an empty set has no members (law S-04).
#
# `PSet.empty_p` is the early-exit emptiness test SPEC 4.3 asks for: it must
# not pay to count a whole set to discover it is non-empty, so it stops at the
# first word with a bit in it. The rewrites of `query/rewrite.bend` are
# admitted on the strength of its answer -- `A u Empty` becomes `A`, `A n
# Empty` becomes `Empty` -- so what those rewrites rest on is that the test
# only answers `True{}` for a set with no members. That is this file.
#
# With it and the pointwise laws (S-02), each admitted Boolean rewrite
# preserves membership.

import Base
import ./eq.bend as E
import ./addr.bend as Ad
import ./bits.bend as PB
import ./word.bend as PW
import ./count.bend as Ct
import ./descend.bend as Dc
import ./leaf.bend as Lf
import ./setops.bend as So
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/ords.bend as O
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# A tile with no word set has no bit set.
# ---------------------------------------------------------------------------

law U32.is_zero_bit:
  for +w: U32
  for +z: {U32.is_zero(w) == True{} : Bool}
  for +b: Nat
  {Wo.U32.test(w, b) == False{} : Bool}

def U32.is_zero_bit(w, z, b):
  %E.U32.sym(w, 0, E.U32.eq_reflect(w, 0, z))
    : {Wo.U32.test(_, b) == False{} : Bool}
  Equal.trans(Bool, Wo.U32.test(0, b), W.U32.bit(0, b), False{},
    PB.U32.test_spec(0, b), PW.U32.bit_zero(b))

law Words.any_go_false:
  for +ws: List<&2, U32>
  for +found: Bool
  for +z: {Wo.Words.any.go(ws, found) == False{} : Bool}
  for +i: Nat
  for +b: Nat
  {Wo.Words.at(ws, i, b) == False{} : Bool}

# The scan reached the tail, so the head word was zero.
law Words.not_found:
  for +c: Bool
  for +t: List<&2, U32>
  for +z: {Wo.Words.any.go(t, Bool.not(c)) == False{} : Bool}
  {c == True{} : Bool}

law Words.any_go_true:
  for +t: List<&2, U32>
  for +z: {Wo.Words.any.go(t, True{}) == False{} : Bool}
  {False{} == True{} : Bool}

def Words.any_go_true(t, z):
  match t:
    case Nil{}:
      E.Bool.sym(True{}, False{}, z)
    case Con{w, r}:
      E.Bool.sym(True{}, False{}, z)

def Words.not_found(c, t, z):
  match c:
    case True{}:
      {==}
    case False{}:
      E.Bool.noconf({False{} == True{} : Bool},
        Words.any_go_true(t, z))

def Words.any_go_false(ws, found, z, i, b):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      match found:
        case True{}:
          E.Bool.noconf.r({Wo.Words.at(Con{w, t}, i, b)
            == False{} : Bool}, z)
        case False{}:
          match i:
            case 0n:
              U32.is_zero_bit(w,
                Words.not_found(U32.is_zero(w), t, z), b)
            case 1n+j:
              Words.any_go_false(t, Bool.not(U32.is_zero(w)), z, j, b)

law Words.any_false:
  for +ws: List<&2, U32>
  for +z: {Wo.Words.any(ws) == False{} : Bool}
  for +i: Nat
  for +b: Nat
  {Wo.Words.at(ws, i, b) == False{} : Bool}

def Words.any_false(ws, z, i, b):
  Words.any_go_false(ws, False{}, z, i, b)

# ---------------------------------------------------------------------------
# The set. `PSet.is_empty` threads an accumulator that never recovers once it
# is `False{}`, so a `True{}` answer splits the same way structural validity
# does.
# ---------------------------------------------------------------------------

law PSet.is_empty_false:
  for +d: Nat
  for +s: S.PSet
  {S.PSet.is_empty(d, s, False{}) == False{} : Bool}

def PSet.is_empty_false(d, s):
  match d:
    case 0n:
      {==}
    case 1n+p:
      match s:
        case S.PZero{}:
          {==}
        case S.PFull{}:
          {==}
        case S.PSparse{o}:
          {==}
        case S.PDense{w}:
          {==}
        case S.PBranch{lo, hi}:
          {==}

law PSet.empty_lo:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +z: {S.PSet.is_empty(1n+p, S.PBranch{lo, hi}, True{})
    == True{} : Bool}
  {S.PSet.is_empty(p, lo, True{}) == True{} : Bool}

def PSet.empty_at(+p: Nat, +hi: S.PSet, a: Bool) -> Bool:
  S.PSet.is_empty(p, hi, a)

law PSet.empty_lo.on:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +a: Bool
  for +ea: {a == S.PSet.is_empty(p, lo, True{}) : Bool}
  for +z: {S.PSet.is_empty(1n+p, S.PBranch{lo, hi}, True{})
    == True{} : Bool}
  {S.PSet.is_empty(p, lo, True{}) == True{} : Bool}

def PSet.empty_lo.on(p, lo, hi, a, ea, z):
  match a:
    case True{}:
      E.Bool.sym(a, S.PSet.is_empty(p, lo, True{}), ea)
    case False{}:
      E.Bool.noconf({S.PSet.is_empty(p, lo, True{}) == True{} : Bool},
        Equal.trans(Bool, False{}, S.PSet.is_empty(p, hi, False{}),
          True{},
          E.Bool.sym(S.PSet.is_empty(p, hi, False{}), False{},
            PSet.is_empty_false(p, hi)),
          Equal.trans(Bool, S.PSet.is_empty(p, hi, False{}),
            S.PSet.is_empty(p, hi, S.PSet.is_empty(p, lo, True{})),
            True{},
            Equal.cong(Bool, Bool, PSet.empty_at(p, hi), False{},
              S.PSet.is_empty(p, lo, True{}), ea),
            z)))

def PSet.empty_lo(p, lo, hi, z):
  PSet.empty_lo.on(p, lo, hi, S.PSet.is_empty(p, lo, True{}), {==}, z)

law PSet.empty_hi:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +z: {S.PSet.is_empty(1n+p, S.PBranch{lo, hi}, True{})
    == True{} : Bool}
  {S.PSet.is_empty(p, hi, True{}) == True{} : Bool}

def PSet.empty_hi(p, lo, hi, z):
  %PSet.empty_lo(p, lo, hi, z)
    : {S.PSet.is_empty(p, hi, _) == True{} : Bool}
  z

law PSet.empty_no_member:
  for +d: Nat
  for +s: S.PSet
  for +h: U32
  for +x: U32
  for +z: {S.PSet.empty_p(d, s) == True{} : Bool}
  for +bt: Bool
  for +ebt: {bt == U32.is_lt(x, h) : Bool}
  {S.PSet.mem(d, s, h, x) == False{} : Bool}

law PSet.empty_sparse:
  for +offs: List<&2, U32>
  for +x: U32
  for +z: {List.length(&2, U32, offs) == 0n : Nat}
  {O.Ords.elem(offs, x) == False{} : Bool}

def PSet.empty_sparse(offs, x, z):
  match offs:
    case Nil{}:
      {==}
    case Con{o, t}:
      E.Nat.noconf2({O.Ords.elem(Con{o, t}, x) == False{} : Bool},
        List.length(&2, U32, t), z)

law PSet.nil_of_is_empty:
  for +offs: List<&2, U32>
  for +z: {List.is_empty(&2, U32, offs) == True{} : Bool}
  {List.length(&2, U32, offs) == 0n : Nat}

def PSet.nil_of_is_empty(offs, z):
  match offs:
    case Nil{}:
      {==}
    case Con{o, t}:
      E.Bool.noconf({List.length(&2, U32, Con{o, t}) == 0n : Nat}, z)

law PSet.not_any:
  for +ws: List<&2, U32>
  for +z: {Bool.not(Wo.Words.any(ws)) == True{} : Bool}
  {Wo.Words.any(ws) == False{} : Bool}

def PSet.not_any(ws, z):
  E.Bool.sym(False{}, Wo.Words.any(ws),
    E.Bool.not_true(Wo.Words.any(ws), z))

def PSet.empty_no_member(d, s, h, x, z, bt, ebt):
  match d:
    case 0n:
      match s:
        case S.PZero{}:
          {==}
        case S.PBranch{l, r}:
          {==}
        case S.PFull{}:
          E.Bool.noconf({S.PSet.mem.leaf(S.PFull{}, x)
            == False{} : Bool}, z)
        case S.PSparse{offs}:
          PSet.empty_sparse(offs, x,
            Lf.Nat.is_eq_reflect(List.length(&2, U32, offs), 0n, z))
        case S.PDense{ws}:
          Ct.Words.count_zero(ws,
            Lf.Nat.is_eq_reflect(Wo.Words.count(ws), 0n, z),
            U32.to_nat(U32.shrn(x, 5n)), U32.to_nat(U32.and(x, 31)),
            Ad.U32.low_five_bound(x))
    case 1n+p:
      match s:
        case S.PZero{}:
          {==}
        case S.PFull{}:
          E.Bool.noconf({S.PSet.mem(1n+p, S.PFull{}, h, x)
            == False{} : Bool}, z)
        case S.PSparse{offs}:
          PSet.empty_sparse(offs, x, PSet.nil_of_is_empty(offs, z))
        case S.PDense{ws}:
          Words.any_false(ws, PSet.not_any(ws, z),
            U32.to_nat(U32.shrn(x, 5n)), U32.to_nat(U32.and(x, 31)))
        case S.PBranch{lo, hi}:
          match bt:
            case True{}:
              %ebt : {S.PSet.mem(p, S.PSet.pick(_, lo, hi), U32.shr(h),
                S.PSet.rebase(_, h, x)) == False{} : Bool}
              PSet.empty_no_member(p, lo, U32.shr(h), x,
                PSet.empty_lo(p, lo, hi, z),
                U32.is_lt(x, U32.shr(h)), {==})
            case False{}:
              %ebt : {S.PSet.mem(p, S.PSet.pick(_, lo, hi), U32.shr(h),
                S.PSet.rebase(_, h, x)) == False{} : Bool}
              PSet.empty_no_member(p, hi, U32.shr(h), U32.sub(x, h),
                PSet.empty_hi(p, lo, hi, z),
                U32.is_lt(U32.sub(x, h), U32.shr(h)), {==})

# ---------------------------------------------------------------------------
# The rewrites `query/rewrite.bend` admits, at the set level (law S-04).
#
# Each is an instance of a pointwise law (S-02) with an empty operand, and
# what makes the operand empty is the test above.
# ---------------------------------------------------------------------------

law PSet.union_empty_left:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid(20n, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(20n, b, True{}) == True{} : Bool}
  for +z: {S.PSet.empty_p(20n, a) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.union(20n, a, b), x)
    == S.PSet.member(20n, b, x) : Bool}

def PSet.union_empty_left(a, b, x, va, vb, z):
  %E.Bool.sym(S.PSet.member(20n, S.PSet.union(20n, a, b), x),
    Bool.or(S.PSet.member(20n, a, x), S.PSet.member(20n, b, x)),
    So.PSet.union_member(a, b, x, va, vb))
    : {_ == S.PSet.member(20n, b, x) : Bool}
  %E.Bool.sym(S.PSet.mem(20n, a, S.PSet.half(20n), x), False{},
    PSet.empty_no_member(20n, a, S.PSet.half(20n), x, z,
      U32.is_lt(x, S.PSet.half(20n)), {==}))
    : {Bool.or(_, S.PSet.member(20n, b, x))
      == S.PSet.member(20n, b, x) : Bool}
  {==}

law PSet.inter_empty_left:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid(20n, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(20n, b, True{}) == True{} : Bool}
  for +z: {S.PSet.empty_p(20n, a) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.inter(20n, a, b), x) == False{} : Bool}

def PSet.inter_empty_left(a, b, x, va, vb, z):
  %E.Bool.sym(S.PSet.member(20n, S.PSet.inter(20n, a, b), x),
    Bool.and(S.PSet.member(20n, a, x), S.PSet.member(20n, b, x)),
    So.PSet.inter_member(a, b, x, va, vb))
    : {_ == False{} : Bool}
  %E.Bool.sym(S.PSet.mem(20n, a, S.PSet.half(20n), x), False{},
    PSet.empty_no_member(20n, a, S.PSet.half(20n), x, z,
      U32.is_lt(x, S.PSet.half(20n)), {==}))
    : {Bool.and(_, S.PSet.member(20n, b, x)) == False{} : Bool}
  {==}

law PSet.diff_empty_right:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {S.PSet.valid(20n, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(20n, b, True{}) == True{} : Bool}
  for +z: {S.PSet.empty_p(20n, b) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.diff(20n, a, b), x)
    == S.PSet.member(20n, a, x) : Bool}

law Bool.and_true_r3:
  for +b: Bool
  {Bool.and(b, True{}) == b : Bool}

def Bool.and_true_r3(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def PSet.diff_empty_right(a, b, x, va, vb, z):
  %E.Bool.sym(S.PSet.member(20n, S.PSet.diff(20n, a, b), x),
    Bool.and(S.PSet.member(20n, a, x),
      Bool.not(S.PSet.member(20n, b, x))),
    So.PSet.diff_member(a, b, x, va, vb))
    : {_ == S.PSet.member(20n, a, x) : Bool}
  %E.Bool.sym(S.PSet.mem(20n, b, S.PSet.half(20n), x), False{},
    PSet.empty_no_member(20n, b, S.PSet.half(20n), x, z,
      U32.is_lt(x, S.PSet.half(20n)), {==}))
    : {Bool.and(S.PSet.member(20n, a, x), Bool.not(_))
      == S.PSet.member(20n, a, x) : Bool}
  Bool.and_true_r3(S.PSet.member(20n, a, x))
