# execute/plan.bend -- leaf jobs, and the backends that run them.
#
# A plan is a fork tree whose leaves each hold *their own* pair of word tiles.
# That ownership is the finding of docs/evidence/T01.md, not a style choice:
# handing one host-built operand list to every leaf costs an atomic per
# operand per fork level and measured ~12x slower than leaf-owned tiles. The
# planner therefore splits data down the tree rather than broadcasting it, and
# `bench/spike_t01.bend` is the regression that catches a change which starts
# broadcasting again.
#
# The obligations of SPEC 7.3 -- coverage, disjointness, bounded input reads,
# exact leaf semantics, correctly associated outputs -- are met structurally.
# The tree mirrors the set tree, so the intervals are the set's own and are
# disjoint by construction; each job returns one number; and the numbers are
# combined by a balanced fold, which gives the same answer in any order
# because `Nat` addition is a commutative monoid (law B-02, proved).
#
# Reachability is resolved before any of this runs. SPEC 7.2 is explicit that
# graph paths leave an ordinal tile and come back, so a leaf job must never
# see a truncated traversal -- only established set values.

import Base
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/set.bend as S

type Job is Data:
  JZero{}
  JLeaf{req: List<&2, U32>, have: List<&2, U32>}
  JFork{lo: Job, hi: Job}

# ---------------------------------------------------------------------------
# Planning. Whole intervals are pruned before any tile is built: a `PZero`
# required side has nothing missing, and a `PFull` inventory side has nothing
# missing either. Only where two real leaves meet does a tile get
# materialized.
# ---------------------------------------------------------------------------

def Plan.leaf(a: S.PSet, b: S.PSet) -> Job:
  match a:
    case S.PZero{}:
      JZero{}
    case S.PFull{}:
      JLeaf{Wo.Words.ones(128n), S.PSet.leaf_words(b)}
    case S.PSparse{o}:
      JLeaf{S.PSet.leaf_words(S.PSparse{o}), S.PSet.leaf_words(b)}
    case S.PDense{w}:
      JLeaf{w, S.PSet.leaf_words(b)}
    case S.PBranch{l, h}:
      JZero{}

def Plan.of(+d: Nat, a: S.PSet, b: S.PSet) -> Job:
  match d:
    case 0n:
      Plan.leaf(a, b)
    case 1n+p:
      match a:
        case S.PZero{}:
          JZero{}
        case S.PSparse{o}:
          JZero{}
        case S.PDense{w}:
          JZero{}
        case S.PFull{}:
          match b:
            case S.PFull{}:
              JZero{}
            case S.PZero{}:
              JFork{Plan.of(p, S.PFull{}, S.PZero{}),
                Plan.of(p, S.PFull{}, S.PZero{})}
            case S.PSparse{o}:
              JFork{Plan.of(p, S.PFull{}, S.PZero{}),
                Plan.of(p, S.PFull{}, S.PZero{})}
            case S.PDense{w}:
              JFork{Plan.of(p, S.PFull{}, S.PZero{}),
                Plan.of(p, S.PFull{}, S.PZero{})}
            case S.PBranch{bl, bh}:
              JFork{Plan.of(p, S.PFull{}, bl), Plan.of(p, S.PFull{}, bh)}
        case S.PBranch{al, ah}:
          match b:
            case S.PFull{}:
              JZero{}
            case S.PZero{}:
              JFork{Plan.of(p, al, S.PZero{}), Plan.of(p, ah, S.PZero{})}
            case S.PSparse{o}:
              JFork{Plan.of(p, al, S.PZero{}), Plan.of(p, ah, S.PZero{})}
            case S.PDense{w}:
              JFork{Plan.of(p, al, S.PZero{}), Plan.of(p, ah, S.PZero{})}
            case S.PBranch{bl, bh}:
              JFork{Plan.of(p, al, bl), Plan.of(p, ah, bh)}

# ---------------------------------------------------------------------------
# What the plan will actually read. SPEC 7.7 requires reporting bytes
# processed rather than implying a GPU makes any matrix cheap; SPEC 11.3 asks
# for dense words actually scanned and structural branches pruned.
# ---------------------------------------------------------------------------

def Plan.leaves(j: Job, acc: Nat) -> Nat:
  match j:
    case JZero{}:
      acc
    case JLeaf{r, h}:
      1n+acc
    case JFork{lo, hi}:
      Plan.leaves(hi, Plan.leaves(lo, acc))

def Plan.pruned(j: Job, acc: Nat) -> Nat:
  match j:
    case JZero{}:
      1n+acc
    case JLeaf{r, h}:
      acc
    case JFork{lo, hi}:
      Plan.pruned(hi, Plan.pruned(lo, acc))

def Plan.words(j: Job, acc: Nat) -> Nat:
  match j:
    case JZero{}:
      acc
    case JLeaf{r, h}:
      Nat.add(acc, Nat.add(List.length(&2, U32, r),
        List.length(&2, U32, h)))
    case JFork{lo, hi}:
      Plan.words(hi, Plan.words(lo, acc))

# ---------------------------------------------------------------------------
# Execution. `Exec.count` forks on the CPU pool; `Exec.count_gpu` is the same
# leaf code behind a `!`, which hands the whole fork tree to Metal. They must
# agree, and the CLI checks that they do on every forced-backend run rather
# than assuming it (SPEC 11.1's second independent comparison).
# ---------------------------------------------------------------------------

def Exec.leaf(j: Job) -> Nat:
  match j:
    case JZero{}:
      0n
    case JLeaf{r, h}:
      Wo.Words.diff_count(r, h)
    case JFork{lo, hi}:
      0n

def Exec.count(+d: Nat, j: Job) -> Nat:
  match d:
    case 0n:
      Exec.leaf(j)
    case 1n+p:
      match j:
        case JZero{}:
          0n
        case JLeaf{r, h}:
          Wo.Words.diff_count(r, h)
        case JFork{lo, hi}:
          x y = Exec.count(p, lo) Exec.count(p, hi)
          Nat.add(x, y)

def Exec.count_gpu(+d: Nat, j: Job) -> Nat:
  Exec.count!(d, j)
