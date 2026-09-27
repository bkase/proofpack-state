# proofs/nonempty.bend -- a set whose count is not zero has a member.
#
# `a_set_with_a_zero_count_has_no_members` is the easy direction: a zero
# count means nothing is in the set. This is the other one, and it is what
# turns a count back into an ordinal a proof can hold: if the count is not
# zero then the list the set enumerates is not empty, and its first ordinal
# is a member.
#
# The ordinal's range comes out of the enumeration law rather than being
# assumed: the list contains it, so the law's own interval test accepted it,
# and an ordinal whose high bits are zero is inside the universe.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./split_add.bend as Sa
import ./treeenum.bend as Te
import ./countlen.bend as Cl
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/set.bend as S

def Ords.head(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      h

law List.contains_head:
  for +h: U32
  for +t: List<&2, U32>
  {List.contains(~U32, ~U32.is_eq, Con{h, t}, h) == True{} : Bool}

def List.contains_head(h, t):
  %E.Bool.sym(U32.is_eq(h, h), True{}, E.U32.is_eq_refl(h))
    : {Bool.or(_, List.contains(~U32, ~U32.is_eq, t, h))
      == True{} : Bool}
  {==}

# The converse of the bound in proofs/treeenum.bend: a word whose high bits
# are cleared by the mask had none set.
law Word.hi_zero_of_diff_zero:
  for +n: Nat
  for +w: Word(n)
  for +k: Nat
  for +z: {Word.and(n, w, Word.not(n, W.Word.low_mask(n, k)))
    == Dc.Word.zeros(n) : Word(n)}
  {Dc.Word.hi_zero(n, w, k) == True{} : Bool}

law Word.tail_of_zeros:
  for +p: Nat
  for +hd: Bool
  for +u: Word(p)
  for +z: {WCon{hd, u} == Dc.Word.zeros(1n+p) : Word(1n+p)}
  {u == Dc.Word.zeros(p) : Word(p)}

law Word.head_of_zeros:
  for +p: Nat
  for +u: Word(p)
  for +z: {WCon{True{}, u} == Dc.Word.zeros(1n+p) : Word(1n+p)}
  {False{} == True{} : Bool}

law Word.head_eq:
  for +p: Nat
  for +a: Bool
  for +b: Bool
  for +at: Word(p)
  for +bt: Word(p)
  for +e: {WCon{a, at} == WCon{b, bt} : Word(1n+p)}
  {a == b : Bool}

def Word.head_of(-p: Nat, w: Word(1n+p)) -> Bool:
  match w:
    case WCon{b, t}:
      b

def Word.head_eq(p, a, b, at, bt, e):
  Equal.cong(Word(1n+p), Bool, Word.head_of(p),
    WCon{a, at}, WCon{b, bt}, e)

def Word.head_of_zeros(p, u, z):
  E.Bool.sym(True{}, False{},
    Word.head_eq(p, True{}, False{}, u, Dc.Word.zeros(p), z))

law Word.tail_eq:
  for +p: Nat
  for +a: Bool
  for +b: Bool
  for +at: Word(p)
  for +bt: Word(p)
  for +e: {WCon{a, at} == WCon{b, bt} : Word(1n+p)}
  {at == bt : Word(p)}

def Word.tail_of(-p: Nat, w: Word(1n+p)) -> Word(p):
  match w:
    case WCon{b, t}:
      t

def Word.tail_eq(p, a, b, at, bt, e):
  Equal.cong(Word(1n+p), Word(p), Word.tail_of(p),
    WCon{a, at}, WCon{b, bt}, e)

def Word.tail_of_zeros(p, hd, u, z):
  Word.tail_eq(p, hd, False{}, u, Dc.Word.zeros(p), z)

def Word.hi_zero_of_diff_zero(n, w, k, z):
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
                  Word.hi_zero_of_diff_zero(p, t, 0n,
                    Word.tail_of_zeros(p,
                      Bool.and(False{}, Bool.not(False{})),
                      Word.and(p, t,
                        Word.not(p, W.Word.low_mask(p, 0n))), z))
                case 1n+j:
                  Word.hi_zero_of_diff_zero(p, t, j,
                    Word.tail_of_zeros(p,
                      Bool.and(False{}, Bool.not(True{})),
                      Word.and(p, t,
                        Word.not(p, W.Word.low_mask(p, j))), z))
            case True{}:
              match k:
                case 0n:
                  E.Bool.noconf({Dc.Word.hi_zero(1n+p,
                    WCon{True{}, t}, 0n) == True{} : Bool},
                    Word.head_of_zeros(p,
                      Word.and(p, t,
                        Word.not(p, W.Word.low_mask(p, 0n))), z))
                case 1n+j:
                  Word.hi_zero_of_diff_zero(p, t, j,
                    Word.tail_of_zeros(p,
                      Bool.and(True{}, Bool.not(True{})),
                      Word.and(p, t,
                        Word.not(p, W.Word.low_mask(p, j))), z))

law U32.hi_zero_of_test:
  for +x: U32
  for +k: Nat
  for +e: {U32.is_eq(0, W.U32.diff(x, W.U32.mask(k))) == True{}
    : Bool}
  {Dc.U32.hi_zero(x, k) == True{} : Bool}

law Word.of_u32:
  for +a: U32
  for +b: U32
  for +e: {a == b : U32}
  {W.U32.word(a) == W.U32.word(b) : Word(32n)}

def Word.of_u32(a, b, e):
  Equal.cong(U32, Word(32n), W.U32.word, a, b, e)

def U32.hi_zero_of_test(x, k, e):
  match x:
    case U32{xw}:
      Word.hi_zero_of_diff_zero(32n, xw, k,
        Word.of_u32(W.U32.diff(U32{xw}, W.U32.mask(k)), 0,
          E.U32.sym(0, W.U32.diff(U32{xw}, W.U32.mask(k)),
            E.U32.eq_reflect(0, W.U32.diff(U32{xw}, W.U32.mask(k)),
              e))))

# ---------------------------------------------------------------------------
# The witness.
# ---------------------------------------------------------------------------

def PSet.witness.contains(+d: Nat, +s: S.PSet, +h: U32,
  +t: List<&2, U32>,
  +el: {Con{h, t} == S.PSet.to_list(d, s) : List<&2, U32>})
  -> {List.contains(~U32, ~U32.is_eq, S.PSet.to_list(d, s), h)
    == True{} : Bool}:
  %el
    : {List.contains(~U32, ~U32.is_eq, _, h) == True{} : Bool}
  List.contains_head(h, t)

def PSet.witness.both(+d: Nat, +s: S.PSet, +h: U32,
  +t: List<&2, U32>,
  +ok: {Te.PSet.ok(d, s) == True{} : Bool},
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +el: {Con{h, t} == S.PSet.to_list(d, s) : List<&2, U32>})
  -> {Bool.and(U32.is_eq(0, W.U32.diff(h, W.U32.mask(12n+d))),
       S.PSet.mem(d, s, S.PSet.half(d),
         U32.and(h, W.U32.mask(12n+d)))) == True{} : Bool}:
  %Te.Bool.or_false_r(
    Bool.and(U32.is_eq(0, W.U32.diff(h, W.U32.mask(12n+d))),
      S.PSet.mem(d, s, S.PSet.half(d),
        U32.and(h, W.U32.mask(12n+d)))))
    : {_ == True{} : Bool}
  %Te.PSet.members_contains(d, s, 0, h, Nil{}, ok,
    Te.U32.lo_zero_zero(12n+d), lt)
    : {_ == True{} : Bool}
  PSet.witness.contains(d, s, h, t, el)

law PSet.witness:
  for +d: Nat
  for +s: S.PSet
  for +l: List<&2, U32>
  for +ok: {Te.PSet.ok(d, s) == True{} : Bool}
  for +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +el: {l == S.PSet.to_list(d, s) : List<&2, U32>}
  for +pos: {C.Nat.gt(S.PSet.count(d, s, S.PSet.half(d)), 0n)
    == True{} : Bool}
  {S.PSet.member(d, s, Ords.head(l)) == True{} : Bool}

def PSet.witness.zero(+d: Nat, +s: S.PSet,
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +el: {Nil{} == S.PSet.to_list(d, s) : List<&2, U32>})
  -> {S.PSet.count(d, s, S.PSet.half(d)) == 0n : Nat}:
  %Cl.PSet.count_is_to_list_length(d, s, lt)
    : {_ == 0n : Nat}
  %el
    : {List.length(&2, U32, _) == 0n : Nat}
  {==}

def PSet.witness.empty(+d: Nat, +s: S.PSet,
  +lt: {C.Nat.gt(32n, 11n+d) == True{} : Bool},
  +el: {Nil{} == S.PSet.to_list(d, s) : List<&2, U32>},
  +pos: {C.Nat.gt(S.PSet.count(d, s, S.PSet.half(d)), 0n)
    == True{} : Bool})
  -> {False{} == True{} : Bool}:
  %PSet.witness.zero(d, s, lt, el)
    : {C.Nat.gt(_, 0n) == True{} : Bool}
  pos

def PSet.witness(d, s, l, ok, lt, el, pos):
  match l:
    case Nil{}:
      E.Bool.noconf({S.PSet.member(d, s, Ords.head(Nil{}))
        == True{} : Bool},
        PSet.witness.empty(d, s, lt, el, pos))
    case Con{h, t}:
      %Te.U32.and_mask_of_hi_zero(h, 12n+d,
        U32.hi_zero_of_test(h, 12n+d,
          E.Bool.and_l(U32.is_eq(0, W.U32.diff(h, W.U32.mask(12n+d))),
            S.PSet.mem(d, s, S.PSet.half(d),
              U32.and(h, W.U32.mask(12n+d))),
            PSet.witness.both(d, s, h, t, ok, lt, el))))
        : {S.PSet.mem(d, s, S.PSet.half(d), _) == True{} : Bool}
      E.Bool.and_r(U32.is_eq(0, W.U32.diff(h, W.U32.mask(12n+d))),
        S.PSet.mem(d, s, S.PSet.half(d),
          U32.and(h, W.U32.mask(12n+d))),
        PSet.witness.both(d, s, h, t, ok, lt, el))
