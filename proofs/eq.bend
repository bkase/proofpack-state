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

def Cmp.sym(-a: Cmp, -b: Cmp, e: {a == b : Cmp}) -> {b == a : Cmp}:
  Equal.sym(Cmp, a, b, e)

def U32.sym(-a: U32, -b: U32, e: {a == b : U32}) -> {b == a : U32}:
  Equal.sym(U32, a, b, e)

def Nat.sym(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

def Word.sym(-n: Nat, -a: Word(n), -b: Word(n), e: {a == b : Word(n)})
  -> {b == a : Word(n)}:
  Equal.sym(Word(n), a, b, e)

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


# ---------------------------------------------------------------------------
# Reflexivity. `U32.cmp` answers `EQ{}` on a word and itself -- needed
# wherever a proof inserts an ordinal and then looks it up.
# ---------------------------------------------------------------------------

law Word.cmp_refl:
  for +n: Nat
  for +w: Word(n)
  {Word.cmp(n, w, w) == EQ{} : Cmp}

def Word.cmp_refl(n, w):
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
              %Cmp.sym(Word.cmp(p, t, t), EQ{}, Word.cmp_refl(p, t))
                : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
              {==}
            case True{}:
              %Cmp.sym(Word.cmp(p, t, t), EQ{}, Word.cmp_refl(p, t))
                : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
              {==}

law U32.is_eq_refl:
  for +a: U32
  {U32.is_eq(a, a) == True{} : Bool}

def U32.is_eq_refl(a):
  match a:
    case U32{w}:
      %Cmp.sym(Word.cmp(32n, w, w), EQ{}, Word.cmp_refl(32n, w))
        : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# A `Nat` successor is never zero; used to discharge impossible list-length
# cases.
def Nat.code2(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def Nat.trim2(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      1n+0n

def Nat.empty2(e: {0n == 1n+0n : Nat}) -> Empty:
  %e : Nat.code2(_)
  Unit{}

def Nat.noconf2(-A: Type, -k: Nat, e: {1n+k == 0n : Nat}) -> A:
  Empty.absurd(A, Nat.empty2(Equal.cong(Nat, Nat, Nat.trim2, 0n, 1n+k,
    Equal.sym(Nat, 1n+k, 0n, e))))

law Bool.not_true:
  for +b: Bool
  for +ok: {Bool.not(b) == True{} : Bool}
  {False{} == b : Bool}

def Bool.not_true(b, ok):
  match b:
    case False{}:
      {==}
    case True{}:
      Bool.noconf({False{} == True{} : Bool}, ok)
