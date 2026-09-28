# Accepted by --verdict, and useful for locating the bug: proving an equation
# whose sides reduce to the same 4096-cell list is fine. It is converting two
# *types* over a term that size that is not. Needs Bend's Base only for U32.

import Base

def ones(+k: Nat) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      Con{1, ones(j)}

def idl(xs: List<&2, U32>) -> List<&2, U32>:
  xs

law ones_eq:
  {idl(ones(4096n)) == ones(4096n) : List<&2, U32>}

def ones_eq():
  {==}
