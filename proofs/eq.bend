# proofs/eq.bend -- equality reflection for machine words, and the
# contradiction helper the conditional laws need.
#
# Two small tools that several of the harder obligations turn out to need.
#
# The first is a way to use a false hypothesis. A law with a premise -- "if
# the certificate accepts", "if this successor list is filtered" -- has cases
# the premise rules out, and discharging them means turning an impossible
# equation into anything at all. `Bool.code` sends `False{}` to `Empty` and
# `True{}` to `Unit`, so rewriting along `{False{} == True{} : Bool}` turns a
# goal of `Empty` into a goal of `Unit`, which is inhabited. That is the whole
# trick, and it is the standard one.
#
# The second is reflection: `U32.is_eq` answers `True{}` only for equal
# words. Nothing in the algebra needs that, because every set law is stated
# pointwise over `Bool`. The Git adapter does need it: `List.contains` decides
# membership with `U32.is_eq`, so a law about a *filtered* successor list --
# G-02, the tree-data policy -- has to know that when `is_eq(w, v)` holds, `w`
# and `v` have the same object metadata. That only follows from `w == v`.
#
# `U32.cmp` is `Word.cmp` on the 32-bit vector, comparing tails first with the
# head bit as the tiebreak, so reflection is an induction on the vector.

import Base

# ---------------------------------------------------------------------------
# Using a false hypothesis.
# ---------------------------------------------------------------------------

def Bool.code(b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

def Bool.sym(-a: Bool, -b: Bool, e: {a == b : Bool}) -> {b == a : Bool}:
  Equal.sym(Bool, a, b, e)

def Bool.empty(e: {False{} == True{} : Bool}) -> Empty:
  %Bool.sym(False{}, True{}, e) : Bool.code(_)
  Unit{}

# `False{} == True{}` proves anything.
def Bool.noconf(-A: Type, e: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, Bool.empty(e))

# And so does `True{} == False{}`.
def Bool.noconf.r(-A: Type, e: {True{} == False{} : Bool}) -> A:
  Bool.noconf(A, Bool.sym(True{}, False{}, e))

# ---------------------------------------------------------------------------
# Reflection for `Word.cmp`.
# ---------------------------------------------------------------------------
def Word.wcon(-p: Nat, b: Bool, t: Word(p)) -> Word(1n+p):
  WCon{b, t}

# `Word.cmp.fin` combines the tail comparison with the head bit: the tail
# decides unless it is `EQ{}`, in which case the head does. So an `EQ{}`
# overall result splits into two facts, and each split is a non-recursive case
# analysis. They are separate lemmas rather than arms of the induction below
# because Bend has no mutual recursion, and the induction needs both.

law Word.cmp_fin_tail:
  for +c: Cmp
  for +ab: Bool
  for +bb: Bool
  for +ok: {Cmp.is_eq(Word.cmp.fin(ab, bb, c)) == True{} : Bool}
  {Cmp.is_eq(c) == True{} : Bool}

def Word.cmp_fin_tail(c, ab, bb, ok):
  match c:
    case LT{}:
      ok
    case GT{}:
      ok
    case EQ{}:
      {==}

law Word.cmp_fin_head:
  for +c: Cmp
  for +ab: Bool
  for +bb: Bool
  for +ok: {Cmp.is_eq(Word.cmp.fin(ab, bb, c)) == True{} : Bool}
  {ab == bb : Bool}

def Word.cmp_fin_head(c, ab, bb, ok):
  match c:
    case LT{}:
      Bool.noconf({ab == bb : Bool}, ok)
    case GT{}:
      Bool.noconf({ab == bb : Bool}, ok)
    case EQ{}:
      match ab bb:
        case False{} False{}:
          {==}
        case True{} True{}:
          {==}
        case False{} True{}:
          Bool.noconf({False{} == True{} : Bool}, ok)
        case True{} False{}:
          Bool.noconf({True{} == False{} : Bool}, ok)

law Word.eq_reflect:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +ok: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}
  {a == b : Word(n)}

def Word.eq_reflect(n, a, b, ok):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          %Word.cmp_fin_head(Word.cmp(p, at, bt), ab, bb, ok)
            : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
          %Word.eq_reflect(p, at, bt,
            Word.cmp_fin_tail(Word.cmp(p, at, bt), ab, bb, ok))
            : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
          {==}

# ---------------------------------------------------------------------------
# Reflection at `U32`.
# ---------------------------------------------------------------------------

def U32.pak(w: Word(32n)) -> U32:
  U32{w}

law U32.eq_reflect:
  for +a: U32
  for +b: U32
  for +ok: {U32.is_eq(a, b) == True{} : Bool}
  {a == b : U32}

def U32.eq_reflect(a, b, ok):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, U32.pak, x, y,
        Word.eq_reflect(32n, x, y, ok))

