# proofs/stats.bend -- statistics form a monoid (law R-02).
#
# SPEC 4.3: with w(x) a nonnegative logical payload size,
#
#     Stats(A) = (|A|, sum of w over A, counts by type)
#
# and for **disjoint** A and B, Stats(A + B) = Stats(A) (+) Stats(B), with
# (+) componentwise addition. That is what licenses a parallel reduction over
# disjoint ordinal ranges and a deterministic balanced fold.
#
# The laws here are that monoid: `Stats.add` is associative, commutative, and
# has `Stats.zero` as its identity. Commutativity is what makes a *balanced*
# reduction give the same answer as a left fold, so the order tiles come back
# in cannot change a byte total.
#
# The disjointness hypothesis is not decoration. For overlapping sets, adding
# counts double-counts the shared objects, and SPEC 4.3 forbids caching
# `Stats(Union(a, b))` as `Stats(a) + Stats(b)` without proving disjointness.
# Nothing in query/eval.bend does: statistics come from one enumeration of
# one set, and the fused difference enumerates `a \ b` itself rather than
# combining two independently measured pieces.

import Base
import ./nat.bend as N
import ../core/count.bend as C
import ../query/ast.bend as A

# Six componentwise equalities make one `Stats` equality. Every law below is
# six applications of a `Nat` lemma through this.
law Stats.eq6:
  for -a1: Nat
  for -a2: Nat
  for -a3: Nat
  for -a4: Nat
  for -a5: Nat
  for -a6: Nat
  for -b1: Nat
  for -b2: Nat
  for -b3: Nat
  for -b4: Nat
  for -b5: Nat
  for -b6: Nat
  for e1: {a1 == b1 : Nat}
  for e2: {a2 == b2 : Nat}
  for e3: {a3 == b3 : Nat}
  for e4: {a4 == b4 : Nat}
  for e5: {a5 == b5 : Nat}
  for e6: {a6 == b6 : Nat}
  {A.St{a1, a2, a3, a4, a5, a6}
    == A.St{b1, b2, b3, b4, b5, b6} : A.Stats}

def Stats.eq6(a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6,
  e1, e2, e3, e4, e5, e6):
  %e1 : {A.St{a1, a2, a3, a4, a5, a6}
    == A.St{_, b2, b3, b4, b5, b6} : A.Stats}
  %e2 : {A.St{a1, a2, a3, a4, a5, a6}
    == A.St{a1, _, b3, b4, b5, b6} : A.Stats}
  %e3 : {A.St{a1, a2, a3, a4, a5, a6}
    == A.St{a1, a2, _, b4, b5, b6} : A.Stats}
  %e4 : {A.St{a1, a2, a3, a4, a5, a6}
    == A.St{a1, a2, a3, _, b5, b6} : A.Stats}
  %e5 : {A.St{a1, a2, a3, a4, a5, a6}
    == A.St{a1, a2, a3, a4, _, b6} : A.Stats}
  %e6 : {A.St{a1, a2, a3, a4, a5, a6}
    == A.St{a1, a2, a3, a4, a5, _} : A.Stats}
  {==}

law Stats.add_zero_left:
  for s: A.Stats
  {A.Stats.add(A.Stats.zero(), s) == s : A.Stats}

def Stats.add_zero_left(s):
  match s:
    case A.St{c, b, k, t, l, g}:
      {==}

law Stats.add_zero_right:
  for +s: A.Stats
  {A.Stats.add(s, A.Stats.zero()) == s : A.Stats}

def Stats.add_zero_right(s):
  match s:
    case A.St{c, b, k, t, l, g}:
      Stats.eq6(Nat.add(c, 0n), Nat.add(b, 0n), Nat.add(k, 0n),
        Nat.add(t, 0n), Nat.add(l, 0n), Nat.add(g, 0n), c, b, k, t, l, g,
        N.Nat.add_zero(c), N.Nat.add_zero(b), N.Nat.add_zero(k),
        N.Nat.add_zero(t), N.Nat.add_zero(l), N.Nat.add_zero(g))

law Stats.add_comm:
  for +x: A.Stats
  for +y: A.Stats
  {A.Stats.add(x, y) == A.Stats.add(y, x) : A.Stats}

def Stats.add_comm(x, y):
  match x:
    case A.St{c1, b1, k1, t1, l1, g1}:
      match y:
        case A.St{c2, b2, k2, t2, l2, g2}:
          Stats.eq6(Nat.add(c1, c2), Nat.add(b1, b2), Nat.add(k1, k2),
            Nat.add(t1, t2), Nat.add(l1, l2), Nat.add(g1, g2),
            Nat.add(c2, c1), Nat.add(b2, b1), Nat.add(k2, k1),
            Nat.add(t2, t1), Nat.add(l2, l1), Nat.add(g2, g1),
            N.Nat.add_comm(c1, c2), N.Nat.add_comm(b1, b2),
            N.Nat.add_comm(k1, k2), N.Nat.add_comm(t1, t2),
            N.Nat.add_comm(l1, l2), N.Nat.add_comm(g1, g2))

law Stats.add_assoc:
  for +x: A.Stats
  for +y: A.Stats
  for +z: A.Stats
  {A.Stats.add(A.Stats.add(x, y), z)
    == A.Stats.add(x, A.Stats.add(y, z)) : A.Stats}

def Stats.add_assoc(x, y, z):
  match x:
    case A.St{c1, b1, k1, t1, l1, g1}:
      match y:
        case A.St{c2, b2, k2, t2, l2, g2}:
          match z:
            case A.St{c3, b3, k3, t3, l3, g3}:
              Stats.eq6(Nat.add(Nat.add(c1, c2), c3),
                Nat.add(Nat.add(b1, b2), b3), Nat.add(Nat.add(k1, k2), k3),
                Nat.add(Nat.add(t1, t2), t3), Nat.add(Nat.add(l1, l2), l3),
                Nat.add(Nat.add(g1, g2), g3),
                Nat.add(c1, Nat.add(c2, c3)), Nat.add(b1, Nat.add(b2, b3)),
                Nat.add(k1, Nat.add(k2, k3)), Nat.add(t1, Nat.add(t2, t3)),
                Nat.add(l1, Nat.add(l2, l3)), Nat.add(g1, Nat.add(g2, g3)),
                N.Nat.add_assoc(c1, c2, c3), N.Nat.add_assoc(b1, b2, b3),
                N.Nat.add_assoc(k1, k2, k3), N.Nat.add_assoc(t1, t2, t3),
                N.Nat.add_assoc(l1, l2, l3), N.Nat.add_assoc(g1, g2, g3))

# One object contributes exactly one to the count, whatever its type. This is
# why the type breakdown can never disagree with the total.
law Stats.one_object.go:
  for +size: Nat
  for k: Nat
  {A.Stats.count(A.Stats.of_kind.pick(size, k)) == 1n : Nat}

def Stats.one_object.go(size, k):
  match k:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  {==}

law Stats.one_object:
  for +size: Nat
  for +kind: U32
  {A.Stats.count(A.Stats.of_kind(size, kind)) == 1n : Nat}

def Stats.one_object(size, kind):
  Stats.one_object.go(size, U32.to_nat(kind))
