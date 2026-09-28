import Base

def and_both(+p: Bool, +q: Bool,
  +a: {p == True{} : Bool}, +b: {q == True{} : Bool})
  -> {Bool.and(p, q) == True{} : Bool}:
  match p:
    case True{}:
      b
    case False{}:
      a

def ones(+k: Nat) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      Con{1, ones(j)}

def allone(+xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(U32.is_eq(h, 1), allone(t))

law ones_ok:
  for +k: Nat
  {allone(ones(k)) == True{} : Bool}

def ones_ok(k):
  match k:
    case 0n:
      {==}
    case 1n+j:
      and_both(U32.is_eq(1, 1), allone(ones(j)), {==}, ones_ok(j))

def p() -> {allone(ones(851n)) == True{} : Bool}:
  ones_ok(851n)
