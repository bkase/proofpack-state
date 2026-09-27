# proofs/nat.bend -- the Nat lemmas the counting proofs need.
#
# `Nat` is this runtime's checked accumulator: it compiles to a native
# unsigned integer capped at 2^48-1, and `nat_chk` posts a runtime error
# rather than wrapping when a sum passes that cap (see core/count.bend and
# TRUST.md). Its equations, though, are the ordinary Peano ones, which is what
# makes every count and byte-sum law below provable by plain induction.

import Base

# add(a, 1n+b) == 1n+add(a, b). Base does not ship this one.
law Nat.add_succ:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def Nat.add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Nat.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

law Nat.add_zero:
  for a: Nat
  {Nat.add(a, 0n) == a : Nat}

def Nat.add_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Nat.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

law Nat.add_comm:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

def Nat.add_comm(a, b):
  match b:
    case 0n:
      Nat.add_zero(a)
    case 1n+q:
      %Nat.add_comm(a, q) : {Nat.add(a, 1n+q) == 1n+_ : Nat}
      Nat.add_succ(a, q)

law Nat.add_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def Nat.add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Nat.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# A short name for symmetry at Nat: `%e : P` rewrites b into a, so applying an
# induction hypothesis to the left-hand side needs the equation flipped.
def Nat.flip(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

def Bool.flip(-a: Bool, -b: Bool, e: {a == b : Bool}) -> {b == a : Bool}:
  Equal.sym(Bool, a, b, e)
