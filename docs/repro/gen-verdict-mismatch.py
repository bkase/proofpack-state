#!/usr/bin/env python3
"""Generate the --verdict mismatch repro at any size.

    python3 gen-verdict-mismatch.py 851 > t.bend && bend t.bend --verdict

`--cells 2` builds two list cells per recursive step, which is how the report
shows the threshold tracks the size of the normalized term rather than the
depth of the recursion. `--no-wrapper` drops the `idl` indirection, which
removes the conversion and makes every size pass.
"""
import argparse

P = argparse.ArgumentParser()
P.add_argument("k", type=int)
P.add_argument("--cells", type=int, default=1, choices=(1, 2))
P.add_argument("--no-wrapper", action="store_true")
a = P.parse_args()

step = ("      Con{1, ones(j)}" if a.cells == 1
        else "      Con{1, Con{1, ones(j)}}")
proof = ("      and_both(U32.is_eq(1, 1), allone(ones(j)), {==}, ones_ok(j))"
         if a.cells == 1 else
         "      and_both(U32.is_eq(1, 1), allone(Con{1, ones(j)}), {==},\n"
         "        and_both(U32.is_eq(1, 1), allone(ones(j)), {==},\n"
         "          ones_ok(j)))")
wrapper = "" if a.no_wrapper else """
def idl(xs: List<&2, U32>) -> List<&2, U32>:
  xs
"""
subject = ("ones(%dn)" % a.k) if a.no_wrapper else ("idl(ones(%dn))" % a.k)

print("""import Base

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
%s

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
%s
%s
def p() -> {allone(%s) == True{} : Bool}:
  ones_ok(%dn)""" % (step, proof, wrapper, subject, a.k))
