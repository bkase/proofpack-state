# proofs/ords.bend -- the sparse leaf's list (part of law P-01).
#
# A sparse leaf is an ascending list of offsets, and an insert into one has to
# leave the inserted ordinal present. That is the half of P-01 this file
# proves, and it is the half that needs no hypothesis at all: it holds for any
# list, ascending or not, of any length.
#
# The other half -- a *dense* leaf keeps the bit it just set -- does need one,
# because `Words.set` on a tile too short to contain the position silently
# changes nothing. See proofs/bitset.bend and the counterexample recorded in
# tests.bend.
#
# `Ords.insert` walks the list carrying the comparison of the head with the
# new ordinal, because Bend matches parameters rather than computed values.
# The proof carries the same comparison the same way.

import Base
import ./eq.bend as E
import ../core/ords.bend as O

# Once the scan has found the ordinal it stays found, whatever is left.
law Ords.elem_go_found:
  for +xs: List<&2, U32>
  for +x: U32
  {O.Ords.elem.go(xs, x, True{}) == True{} : Bool}

def Ords.elem_go_found(xs, x):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# The scan from a `False{}` start is just `Ords.elem`, which is how the
# recursive case below lines up with the induction hypothesis.
law Ords.elem_go_start:
  for +xs: List<&2, U32>
  for +x: U32
  {O.Ords.elem.go(xs, x, False{}) == O.Ords.elem(xs, x) : Bool}

def Ords.elem_go_start(xs, x):
  {==}

# ---------------------------------------------------------------------------
# The insert. `c` is the comparison of the list's head with `x`, taken as a
# parameter with the equation that names it -- the same shape `Ords.insert`
# itself uses.
# ---------------------------------------------------------------------------

law Ords.elem_insert_go:
  for +xs: List<&2, U32>
  for +x: U32
  for +c: Cmp
  for +ec: {c == O.Ords.head_one(xs, x) : Cmp}
  {O.Ords.elem(O.Ords.insert.go(xs, x, c), x) == True{} : Bool}

def Ords.elem_insert_go(xs, x, c, ec):
  match xs:
    case Nil{}:
      # The list was empty, so the result is `[x]` and the scan compares `x`
      # with itself.
      E.U32.is_eq_refl(x)
    case Con{h, t}:
      match c:
        case EQ{}:
          # `x` is already the head. `ec` says the head comparison is `EQ{}`,
          # so the scan's first test succeeds.
          %ec : {O.Ords.elem.go(t, x, Cmp.is_eq(_)) == True{} : Bool}
          Ords.elem_go_found(t, x)
        case GT{}:
          # `x` goes in front, and the scan's first test compares it with
          # itself.
          %E.Bool.sym(U32.is_eq(x, x), True{}, E.U32.is_eq_refl(x))
            : {O.Ords.elem.go(Con{h, t}, x, _) == True{} : Bool}
          Ords.elem_go_found(Con{h, t}, x)
        case LT{}:
          # `x` belongs further along. The head fails the test -- `ec` says
          # the comparison is `LT{}` -- so the scan restarts on the tail,
          # which is the induction hypothesis.
          %ec : {O.Ords.elem.go(O.Ords.insert.go(t, x,
              O.Ords.head_one(t, x)), x, Cmp.is_eq(_)) == True{} : Bool}
          Ords.elem_insert_go(t, x, O.Ords.head_one(t, x), {==})

law Ords.elem_insert:
  for +xs: List<&2, U32>
  for +x: U32
  {O.Ords.elem(O.Ords.insert(xs, x), x) == True{} : Bool}

def Ords.elem_insert(xs, x):
  Ords.elem_insert_go(xs, x, O.Ords.head_one(xs, x), {==})
