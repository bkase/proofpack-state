# core/ords.bend -- strictly ascending U32 ordinal lists.
#
# The sparse side of the set representation, and the shape every enumeration
# comes back in.
#
# Two Bend rules shape this file. Mutual recursion is not allowed, so a merge
# cannot be split into a `go` that computes a comparison and an `arm` that
# recurses: the comparison of the two heads is instead carried as a parameter
# and recomputed by `Ords.head_cmp`, which is an ordinary def declared above.
# And a merge consumes whichever side is smaller, which is not a shape the
# termination check accepts on its own, so each merge carries an explicit fuel
# that always decreases. `Ords.merge_fuel` computes a fuel that is always
# enough, rather than guessing one: a merge can never silently truncate.

import Base
import ./count.bend as C

def Ords() -> Data:
  List<&2, U32>

# ---------------------------------------------------------------------------
# Membership. The `True` arm drops the rest of the list, so a hit stops the
# walk.
# ---------------------------------------------------------------------------

def Ords.elem.go(xs: List<&2, U32>, +x: U32, found: Bool) -> Bool:
  match xs:
    case Nil{}:
      found
    case Con{h, t}:
      match found:
        case True{}:
          True{}
        case False{}:
          Ords.elem.go(t, x, U32.is_eq(h, x))

def Ords.elem(xs: List<&2, U32>, +x: U32) -> Bool:
  Ords.elem.go(xs, x, False{})

def Ords.count(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

def Ords.head_cmp(a: List<&2, U32>, b: List<&2, U32>) -> Cmp:
  match a:
    case Nil{}:
      EQ{}
    case Con{ah, at}:
      match b:
        case Nil{}:
          EQ{}
        case Con{bh, bt}:
          U32.cmp(ah, bh)

def Ords.merge_fuel(a: List<&2, U32>, b: List<&2, U32>) -> Nat:
  1n+Nat.add(List.length(&2, U32, a), List.length(&2, U32, b))

# ---------------------------------------------------------------------------
# Sorted merges.
# ---------------------------------------------------------------------------

def Ords.union.go(+fuel: Nat, +a: List<&2, U32>, +b: List<&2, U32>, c: Cmp) ->
  List<&2, U32>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match a:
        case Nil{}:
          b
        case Con{ah, at}:
          match b:
            case Nil{}:
              Con{ah, at}
            case Con{bh, bt}:
              match c:
                case LT{}:
                  +y = {Con{bh, bt} : List<&2, U32>}
                  ah <> Ords.union.go(f, at, y, Ords.head_cmp(at, y))
                case GT{}:
                  +x = {Con{ah, at} : List<&2, U32>}
                  bh <> Ords.union.go(f, x, bt, Ords.head_cmp(x, bt))
                case EQ{}:
                  ah <> Ords.union.go(f, at, bt, Ords.head_cmp(at, bt))

def Ords.union(+a: List<&2, U32>, +b: List<&2, U32>) -> List<&2, U32>:
  Ords.union.go(Ords.merge_fuel(a, b), a, b, Ords.head_cmp(a, b))

def Ords.inter.go(+fuel: Nat, +a: List<&2, U32>, +b: List<&2, U32>, c: Cmp) ->
  List<&2, U32>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match a:
        case Nil{}:
          Nil{}
        case Con{ah, at}:
          match b:
            case Nil{}:
              Nil{}
            case Con{bh, bt}:
              match c:
                case LT{}:
                  +y = {Con{bh, bt} : List<&2, U32>}
                  Ords.inter.go(f, at, y, Ords.head_cmp(at, y))
                case GT{}:
                  +x = {Con{ah, at} : List<&2, U32>}
                  Ords.inter.go(f, x, bt, Ords.head_cmp(x, bt))
                case EQ{}:
                  ah <> Ords.inter.go(f, at, bt, Ords.head_cmp(at, bt))

def Ords.inter(+a: List<&2, U32>, +b: List<&2, U32>) -> List<&2, U32>:
  Ords.inter.go(Ords.merge_fuel(a, b), a, b, Ords.head_cmp(a, b))

def Ords.diff.go(+fuel: Nat, +a: List<&2, U32>, +b: List<&2, U32>, c: Cmp) ->
  List<&2, U32>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match a:
        case Nil{}:
          Nil{}
        case Con{ah, at}:
          match b:
            case Nil{}:
              Con{ah, at}
            case Con{bh, bt}:
              match c:
                case LT{}:
                  +y = {Con{bh, bt} : List<&2, U32>}
                  ah <> Ords.diff.go(f, at, y, Ords.head_cmp(at, y))
                case GT{}:
                  +x = {Con{ah, at} : List<&2, U32>}
                  Ords.diff.go(f, x, bt, Ords.head_cmp(x, bt))
                case EQ{}:
                  Ords.diff.go(f, at, bt, Ords.head_cmp(at, bt))

def Ords.diff(+a: List<&2, U32>, +b: List<&2, U32>) -> List<&2, U32>:
  Ords.diff.go(Ords.merge_fuel(a, b), a, b, Ords.head_cmp(a, b))

# ---------------------------------------------------------------------------
# Insert, keeping the list strictly ascending.
# ---------------------------------------------------------------------------

def Ords.head_one(xs: List<&2, U32>, +x: U32) -> Cmp:
  match xs:
    case Nil{}:
      EQ{}
    case Con{h, t}:
      U32.cmp(h, x)

def Ords.insert.go(+xs: List<&2, U32>, +x: U32, c: Cmp) -> List<&2, U32>:
  match xs:
    case Nil{}:
      [x]
    case Con{h, t}:
      match c:
        case EQ{}:
          h <> t
        case GT{}:
          x <> Con{h, t}
        case LT{}:
          h <> Ords.insert.go(t, x, Ords.head_one(t, x))

def Ords.insert(xs: List<&2, U32>, +x: U32) -> List<&2, U32>:
  +ys = xs
  Ords.insert.go(ys, x, Ords.head_one(ys, x))
