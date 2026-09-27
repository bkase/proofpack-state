# query/ast.bend -- the typed query language (SPEC 3.5).
#
# Deliberately small:
#
#   SetExpr = Empty | Full | Literal | Roots
#           | Union | Intersect | Difference
#           | Reach(policy, e) | Filter(type, e)
#
#   Query   = Objects | Stats | IsEmpty | IsSubset | ExplainReach | Batch
#
# `Filter` supports exact object-type filtering only. Predicates are
# declarative, versioned operations -- never a caller-supplied executable
# function (SPEC 3.5).
#
# A literal carries its set value rather than a name: names are resolved
# against the store, and universe compatibility checked, *before* an
# expression is built. That ordering is not cosmetic. SPEC 3.5 requires that
# only validated, total queries enter the optimizer, so that simplifying
# `Difference(q, q)` cannot hide an unresolved input by skipping validation.
# Here it is structural: an unresolved input cannot be represented.

import Base
import ../core/count.bend as C
import ../core/set.bend as S
import ../index/source.bend as Idx

type SetExpr is Data:
  EEmpty{}
  EFull{}
  ELit{set: S.PSet}
  EUnion{a: SetExpr, b: SetExpr}
  EInter{a: SetExpr, b: SetExpr}
  EDiff{a: SetExpr, b: SetExpr}
  EReach{policy: Idx.Policy, a: SetExpr}
  EFilter{kind: U32, a: SetExpr}

type Order is Data:
  ByOid{}
  ByOrdinal{}

type Query is Data:
  QObjects{expr: SetExpr, order: Order}
  QStats{expr: SetExpr}
  QIsEmpty{expr: SetExpr}
  QIsSubset{a: SetExpr, b: SetExpr}

# ---------------------------------------------------------------------------
# Statistics (SPEC 4.3). Exact count, logical payload-byte sum, and counts by
# type. A commutative monoid under componentwise addition -- which is what
# makes a parallel reduction over disjoint ordinal ranges legal, and what
# makes adding the parts of an *overlapping* union wrong.
# ---------------------------------------------------------------------------

type Stats is Data:
  St{count: Nat, bytes: Nat, commits: Nat, trees: Nat, blobs: Nat,
    tags: Nat}

def Stats.zero() -> Stats:
  St{0n, 0n, 0n, 0n, 0n, 0n}

def Stats.add(x: Stats, y: Stats) -> Stats:
  match x:
    case St{c1, b1, k1, t1, l1, g1}:
      match y:
        case St{c2, b2, k2, t2, l2, g2}:
          St{Nat.add(c1, c2), Nat.add(b1, b2), Nat.add(k1, k2),
            Nat.add(t1, t2), Nat.add(l1, l2), Nat.add(g1, g2)}

def Stats.count(s: Stats) -> Nat:
  match s:
    case St{count, bytes, commits, trees, blobs, tags}:
      count

def Stats.bytes(s: Stats) -> Nat:
  match s:
    case St{count, bytes, commits, trees, blobs, tags}:
      bytes

def Stats.commits(s: Stats) -> Nat:
  match s:
    case St{count, bytes, commits, trees, blobs, tags}:
      commits

def Stats.trees(s: Stats) -> Nat:
  match s:
    case St{count, bytes, commits, trees, blobs, tags}:
      trees

def Stats.blobs(s: Stats) -> Nat:
  match s:
    case St{count, bytes, commits, trees, blobs, tags}:
      blobs

def Stats.tags(s: Stats) -> Nat:
  match s:
    case St{count, bytes, commits, trees, blobs, tags}:
      tags

# One object's contribution, by its recorded type code.

def Stats.of_kind.pick(+size: Nat, k: Nat) -> Stats:
  match k:
    case 0n:
      St{1n, size, 1n, 0n, 0n, 0n}
    case 1n+a:
      match a:
        case 0n:
          St{1n, size, 0n, 1n, 0n, 0n}
        case 1n+b:
          match b:
            case 0n:
              St{1n, size, 0n, 0n, 1n, 0n}
            case 1n+c:
              match c:
                case 0n:
                  St{1n, size, 0n, 0n, 0n, 1n}
                case 1n+d:
                  St{1n, size, 0n, 0n, 0n, 0n}

def Stats.of_kind(+size: Nat, +kind: U32) -> Stats:
  Stats.of_kind.pick(size, U32.to_nat(kind))
