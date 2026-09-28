# proofs/validkeep.bend -- the algebra keeps a set in the shape the store
# checks.
#
# `PSet.wf` -- validity minus the ascending-offsets condition -- is what the
# pointwise laws need, and proofs/preserve.bend already shows the operations
# keep it. The subset laws need more: their fused walks merge sparse operands
# as lists, and a merge is only right on ascending ones. So this file proves
# the condition `PSet.wf` drops.
#
# Every sparse leaf the algebra builds comes out of compression, and
# compression's sparse arm is the tile walk's own output -- which ascends,
# and whose ordinals fit in a leaf. That is the whole argument; the rest is
# carrying it through the branch collapses.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./descend.bend as Dc
import ./shift.bend as Sf
import ./orderlist.bend as Ol
import ./order.bend as Or2
import ./tileorder.bend as To
import ./tilefit.bend as Tf
import ./leafdiff.bend as Lf
import ./validshape.bend as Vs2
import ./shape.bend as Sh
import ./preserve.bend as Pr
import ./leaf.bend as Lf2
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/set.bend as S

# Is the head above what came before -- or is there no before?
def Ords.head_above(+l: List<&2, U32>, +last: U32, +first: Bool)
  -> Bool:
  match l:
    case Nil{}:
      True{}
    case Con{o, t}:
      Bool.or(first, U32.is_gt(o, last))

law U32.gt_of_lt:
  for +o: U32
  for +z: U32
  for +lt: {U32.is_lt(o, z) == True{} : Bool}
  {U32.is_gt(z, o) == True{} : Bool}

def U32.gt_of_lt(o, z, lt):
  %E.Cmp.sym(U32.cmp(z, o), Nat.cmp(U32.to_nat(z), U32.to_nat(o)),
    Or2.U32.cmp_spec(z, o))
    : {Cmp.is_gt(_) == True{} : Bool}
  %E.Cmp.sym(Nat.cmp(U32.to_nat(z), U32.to_nat(o)), GT{},
    Ol.Nat.cmp_of_gt(U32.to_nat(z), U32.to_nat(o),
      Ol.Ords.lt_value(o, z, lt)))
    : {Cmp.is_gt(_) == True{} : Bool}
  {==}

law U32.lt_4096:
  for +o: U32
  for +hz: {Dc.U32.hi_zero(o, 12n) == True{} : Bool}
  {U32.is_lt(o, 4096) == True{} : Bool}

def U32.lt_4096(o, hz):
  %E.Bool.sym(U32.is_lt(o, U32.shln(1, 12n)),
    Dc.U32.hi_zero(o, 12n), Dc.U32.is_lt_shln(o, 12n, {==}))
    : {_ == True{} : Bool}
  hz

law PSet.valid_offs_of_asc:
  for +l: List<&2, U32>
  for +last: U32
  for +first: Bool
  for +al: {Ol.Ords.asc(l) == True{} : Bool}
  for +fl: {Sf.Ords.all_fit(l, 12n) == True{} : Bool}
  for +hd: {Ords.head_above(l, last, first) == True{} : Bool}
  {S.PSet.valid.offs(l, last, first, True{}) == True{} : Bool}

law PSet.head_above_of_asc:
  for +t: List<&2, U32>
  for +o: U32
  for +ab: {Ol.Ords.above(o, t) == True{} : Bool}
  {Ords.head_above(t, o, False{}) == True{} : Bool}

def PSet.head_above_of_asc(t, o, ab):
  match t:
    case Nil{}:
      {==}
    case Con{z, u}:
      U32.gt_of_lt(o, z, ab)

def PSet.valid_offs_of_asc(l, last, first, al, fl, hd):
  match l:
    case Nil{}:
      {==}
    case Con{o, t}:
      %E.Bool.sym(U32.is_lt(o, 4096), True{},
        U32.lt_4096(o,
          E.Bool.and_l(Dc.U32.hi_zero(o, 12n),
            Sf.Ords.all_fit(t, 12n), fl)))
        : {S.PSet.valid.offs(t, o, False{},
            Bool.and(_, Bool.or(first, U32.is_gt(o, last))))
          == True{} : Bool}
      %E.Bool.sym(Bool.or(first, U32.is_gt(o, last)), True{}, hd)
        : {S.PSet.valid.offs(t, o, False{}, Bool.and(True{}, _))
          == True{} : Bool}
      PSet.valid_offs_of_asc(t, o, False{},
        E.Bool.and_r(Ol.Ords.above(o, t), Ol.Ords.asc(t), al),
        E.Bool.and_r(Dc.U32.hi_zero(o, 12n),
          Sf.Ords.all_fit(t, 12n), fl),
        PSet.head_above_of_asc(t, o,
          E.Bool.and_l(Ol.Ords.above(o, t), Ol.Ords.asc(t), al)))

# ---------------------------------------------------------------------------
# A compressed tile is a valid leaf.
# ---------------------------------------------------------------------------

law Ords.head_above_first:
  for +l: List<&2, U32>
  for +last: U32
  {Ords.head_above(l, last, True{}) == True{} : Bool}

def Ords.head_above_first(l, last):
  match l:
    case Nil{}:
      {==}
    case Con{o, t}:
      {==}

law PSet.valid_compress_sparse:
  for +ws: List<&2, U32>
  for +sparse: Bool
  for +len: {Nat.is_eq(List.length(&2, U32, ws), 128n) == True{}
    : Bool}
  {S.PSet.valid.leaf(S.PSet.compress.sparse(ws, sparse)) == True{}
    : Bool}

def PSet.valid_compress_sparse(ws, sparse, len):
  match sparse:
    case True{}:
      PSet.valid_offs_of_asc(Wo.Words.members(ws, 0), 0, True{},
        To.Ords.asc_members(ws, len), Tf.Words.members_fit(ws, len),
        Ords.head_above_first(Wo.Words.members(ws, 0), 0))
    case False{}:
      len

law PSet.valid_compress_full:
  for +ws: List<&2, U32>
  for +k: Nat
  for +full: Bool
  for +len: {Nat.is_eq(List.length(&2, U32, ws), 128n) == True{}
    : Bool}
  {S.PSet.valid.leaf(S.PSet.compress.full(ws, k, full)) == True{}
    : Bool}

def PSet.valid_compress_full(ws, k, full, len):
  match full:
    case True{}:
      {==}
    case False{}:
      PSet.valid_compress_sparse(ws,
        C.Nat.upto(k, S.PSet.sparse_max()), len)

law PSet.valid_compress:
  for +ws: List<&2, U32>
  for +len: {Nat.is_eq(List.length(&2, U32, ws), 128n) == True{}
    : Bool}
  {S.PSet.valid.leaf(S.PSet.compress(ws)) == True{} : Bool}

law PSet.valid_compress_pick:
  for +ws: List<&2, U32>
  for +k: Nat
  for +len: {Nat.is_eq(List.length(&2, U32, ws), 128n) == True{}
    : Bool}
  {S.PSet.valid.leaf(S.PSet.compress.pick(ws, k)) == True{} : Bool}

def PSet.valid_compress_pick(ws, k, len):
  match k:
    case 0n:
      {==}
    case 1n+p:
      PSet.valid_compress_full(ws, 1n+p, Nat.is_eq(1n+p, 4096n), len)

def PSet.valid_compress(ws, len):
  PSet.valid_compress_pick(ws, Wo.Words.count(ws), len)

# ---------------------------------------------------------------------------
# The three shapes a node can be, and the branch collapses.
# ---------------------------------------------------------------------------

law PSet.valid_zero:
  for +d: Nat
  {S.PSet.valid(d, S.PZero{}, True{}) == True{} : Bool}

def PSet.valid_zero(d):
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

law PSet.valid_branch:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +vl: {S.PSet.valid(p, lo, True{}) == True{} : Bool}
  for +vh: {S.PSet.valid(p, hi, True{}) == True{} : Bool}
  {S.PSet.valid(1n+p, S.PBranch{lo, hi}, True{}) == True{} : Bool}

def PSet.valid_branch(p, lo, hi, vl, vh):
  %E.Bool.sym(S.PSet.valid(p, lo, True{}), True{}, vl)
    : {S.PSet.valid(p, hi, _) == True{} : Bool}
  vh

law PSet.valid_mk_z:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +vl: {S.PSet.valid(p, lo, True{}) == True{} : Bool}
  for +vh: {S.PSet.valid(p, hi, True{}) == True{} : Bool}
  {S.PSet.valid(1n+p, S.PSet.mk.z(lo, hi), True{}) == True{} : Bool}

def PSet.valid_mk_z(p, lo, hi, vl, vh):
  match hi:
    case S.PZero{}:
      PSet.valid_zero(1n+p)
    case S.PFull{}:
      PSet.valid_branch(p, lo, S.PFull{}, vl, vh)
    case S.PSparse{o}:
      PSet.valid_branch(p, lo, S.PSparse{o}, vl, vh)
    case S.PDense{w}:
      PSet.valid_branch(p, lo, S.PDense{w}, vl, vh)
    case S.PBranch{x, y}:
      PSet.valid_branch(p, lo, S.PBranch{x, y}, vl, vh)

law PSet.valid_mk_f:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +vl: {S.PSet.valid(p, lo, True{}) == True{} : Bool}
  for +vh: {S.PSet.valid(p, hi, True{}) == True{} : Bool}
  {S.PSet.valid(1n+p, S.PSet.mk.f(lo, hi), True{}) == True{} : Bool}

def PSet.valid_mk_f(p, lo, hi, vl, vh):
  match hi:
    case S.PFull{}:
      Vs2.PSet.valid_full(1n+p)
    case S.PZero{}:
      PSet.valid_branch(p, lo, S.PZero{}, vl, vh)
    case S.PSparse{o}:
      PSet.valid_branch(p, lo, S.PSparse{o}, vl, vh)
    case S.PDense{w}:
      PSet.valid_branch(p, lo, S.PDense{w}, vl, vh)
    case S.PBranch{x, y}:
      PSet.valid_branch(p, lo, S.PBranch{x, y}, vl, vh)

law PSet.valid_mk_hi:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +lz: Bool
  for +lf: Bool
  for +vl: {S.PSet.valid(p, lo, True{}) == True{} : Bool}
  for +vh: {S.PSet.valid(p, hi, True{}) == True{} : Bool}
  {S.PSet.valid(1n+p, S.PSet.mk.hi(lo, hi, lz, lf), True{})
    == True{} : Bool}

def PSet.valid_mk_hi(p, lo, hi, lz, lf, vl, vh):
  match lz:
    case True{}:
      PSet.valid_mk_z(p, lo, hi, vl, vh)
    case False{}:
      match lf:
        case True{}:
          PSet.valid_mk_f(p, lo, hi, vl, vh)
        case False{}:
          PSet.valid_branch(p, lo, hi, vl, vh)

law PSet.valid_mk:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +vl: {S.PSet.valid(p, lo, True{}) == True{} : Bool}
  for +vh: {S.PSet.valid(p, hi, True{}) == True{} : Bool}
  {S.PSet.valid(1n+p, S.PSet.mk(lo, hi), True{}) == True{} : Bool}

def PSet.valid_mk(p, lo, hi, vl, vh):
  PSet.valid_mk_hi(p, lo, hi, S.PSet.is_zero(lo), S.PSet.is_full(lo),
    vl, vh)

# ---------------------------------------------------------------------------
# A leaf operation.
# ---------------------------------------------------------------------------

law PSet.valid_union_leaf:
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  {S.PSet.valid.leaf(S.PSet.union.leaf(a, b)) == True{} : Bool}

law PSet.width_eq:
  for +ws: List<&2, U32>
  for +w: {List.length(&2, U32, ws) == 128n : Nat}
  {Nat.is_eq(List.length(&2, U32, ws), 128n) == True{} : Bool}

law PSet.valid_inter_leaf:
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  {S.PSet.valid.leaf(S.PSet.inter.leaf(a, b)) == True{} : Bool}

law PSet.valid_diff_leaf:
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid.leaf(a) == True{} : Bool}
  for +vb: {S.PSet.valid.leaf(b) == True{} : Bool}
  {S.PSet.valid.leaf(S.PSet.diff.leaf(a, b)) == True{} : Bool}

def PSet.spread2(+ao: List<&2, U32>) -> List<&2, U32>:
  S.PSet.spread(ao, Wo.Words.zeros(128n))

law Nat.is_eq_self:
  for +n: Nat
  {Nat.is_eq(n, n) == True{} : Bool}

def Nat.is_eq_self(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Nat.is_eq_self(p)

def PSet.width_eq(ws, w):
  %E.Nat.sym(List.length(&2, U32, ws), 128n, w)
    : {Nat.is_eq(_, 128n) == True{} : Bool}
  Nat.is_eq_self(128n)

def PSet.valid_union_leaf(a, b, va, vb):
  match a:
    case S.PZero{}:
      vb
    case S.PFull{}:
      {==}
    case S.PBranch{l, h}:
      vb
    case S.PSparse{ao}:
      PSet.valid_compress(
        Wo.Words.or(S.PSet.leaf_words(S.PSparse{ao}),
          S.PSet.leaf_words(b)),
        PSet.width_eq(
          Wo.Words.or(S.PSet.leaf_words(S.PSparse{ao}),
            S.PSet.leaf_words(b)),
          Pr.PSet.or_width(S.PSparse{ao}, b,
            Sh.PSet.valid_leaf_wf(S.PSparse{ao}, va),
            Sh.PSet.valid_leaf_wf(b, vb))))
    case S.PDense{aw}:
      PSet.valid_compress(
        Wo.Words.or(S.PSet.leaf_words(S.PDense{aw}),
          S.PSet.leaf_words(b)),
        PSet.width_eq(
          Wo.Words.or(S.PSet.leaf_words(S.PDense{aw}),
            S.PSet.leaf_words(b)),
          Pr.PSet.or_width(S.PDense{aw}, b,
            Sh.PSet.valid_leaf_wf(S.PDense{aw}, va),
            Sh.PSet.valid_leaf_wf(b, vb))))

def PSet.valid_inter_leaf(a, b, va, vb):
  match a:
    case S.PZero{}:
      {==}
    case S.PFull{}:
      vb
    case S.PBranch{l, h}:
      {==}
    case S.PSparse{ao}:
      PSet.valid_compress(
        Wo.Words.and(S.PSet.leaf_words(S.PSparse{ao}),
          S.PSet.leaf_words(b)),
        PSet.width_eq(
          Wo.Words.and(S.PSet.leaf_words(S.PSparse{ao}),
            S.PSet.leaf_words(b)),
          Pr.PSet.and_width(S.PSparse{ao}, b,
            Sh.PSet.valid_leaf_wf(S.PSparse{ao}, va),
            Sh.PSet.valid_leaf_wf(b, vb))))
    case S.PDense{aw}:
      PSet.valid_compress(
        Wo.Words.and(S.PSet.leaf_words(S.PDense{aw}),
          S.PSet.leaf_words(b)),
        PSet.width_eq(
          Wo.Words.and(S.PSet.leaf_words(S.PDense{aw}),
            S.PSet.leaf_words(b)),
          Pr.PSet.and_width(S.PDense{aw}, b,
            Sh.PSet.valid_leaf_wf(S.PDense{aw}, va),
            Sh.PSet.valid_leaf_wf(b, vb))))

def PSet.valid_diff_leaf(a, b, va, vb):
  match a:
    case S.PZero{}:
      {==}
    case S.PBranch{l, h}:
      {==}
    case S.PFull{}:
      PSet.valid_compress(
        Wo.Words.diff(Wo.Words.ones(128n), S.PSet.leaf_words(b)),
        PSet.width_eq(
          Wo.Words.diff(Wo.Words.ones(128n), S.PSet.leaf_words(b)),
          Pr.PSet.sub_width(S.PFull{}, b,
            Sh.PSet.valid_leaf_wf(S.PFull{}, va))))
    case S.PSparse{ao}:
      PSet.valid_compress(
        Wo.Words.diff(PSet.spread2(ao), S.PSet.leaf_words(b)),
        PSet.width_eq(
          Wo.Words.diff(PSet.spread2(ao), S.PSet.leaf_words(b)),
          Pr.PSet.sub_width(S.PSparse{ao}, b,
            Sh.PSet.valid_leaf_wf(S.PSparse{ao}, va))))
    case S.PDense{aw}:
      PSet.valid_compress(
        Wo.Words.diff(aw, S.PSet.leaf_words(b)),
        PSet.width_eq(
          Wo.Words.diff(aw, S.PSet.leaf_words(b)),
          Pr.PSet.sub_width(S.PDense{aw}, b,
            Sh.PSet.valid_leaf_wf(S.PDense{aw}, va))))

# ---------------------------------------------------------------------------
# The three operations, at any depth. Same arms as the `PSet.wf` version in
# proofs/preserve.bend: an operand handed back keeps what it came with, a
# `PZero` or `PFull` is valid at any depth, and a rebuilt branch is the
# collapse lemma above.
# ---------------------------------------------------------------------------

law PSet.valid_union:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  {S.PSet.valid(d, S.PSet.union(d, a, b), True{}) == True{} : Bool}

def PSet.valid_union(d, a, b, va, vb):
  match d:
    case 0n:
      PSet.valid_union_leaf(a, b, va, vb)
    case 1n+p:
      match a:
        case S.PZero{}:
          vb
        case S.PFull{}:
          Vs2.PSet.valid_full(1n+p)
        case S.PSparse{o}:
          vb
        case S.PDense{w}:
          vb
        case S.PBranch{al, ah}:
          match b:
            case S.PZero{}:
              va
            case S.PFull{}:
              Vs2.PSet.valid_full(1n+p)
            case S.PSparse{o}:
              va
            case S.PDense{w}:
              va
            case S.PBranch{bl, bh}:
              PSet.valid_mk(p, S.PSet.union(p, al, bl),
                S.PSet.union(p, ah, bh),
                PSet.valid_union(p, al, bl,
                  E.Bool.and_l(S.PSet.valid(p, al, True{}),
                    S.PSet.valid(p, ah, True{}),
                    Vs2.PSet.both_of_branch(p, al, ah, va)),
                  E.Bool.and_l(S.PSet.valid(p, bl, True{}),
                    S.PSet.valid(p, bh, True{}),
                    Vs2.PSet.both_of_branch(p, bl, bh, vb))),
                PSet.valid_union(p, ah, bh,
                  E.Bool.and_r(S.PSet.valid(p, al, True{}),
                    S.PSet.valid(p, ah, True{}),
                    Vs2.PSet.both_of_branch(p, al, ah, va)),
                  E.Bool.and_r(S.PSet.valid(p, bl, True{}),
                    S.PSet.valid(p, bh, True{}),
                    Vs2.PSet.both_of_branch(p, bl, bh, vb))))

law PSet.valid_inter:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  {S.PSet.valid(d, S.PSet.inter(d, a, b), True{}) == True{} : Bool}

def PSet.valid_inter(d, a, b, va, vb):
  match d:
    case 0n:
      PSet.valid_inter_leaf(a, b, va, vb)
    case 1n+p:
      match a:
        case S.PZero{}:
          PSet.valid_zero(1n+p)
        case S.PSparse{o}:
          PSet.valid_zero(1n+p)
        case S.PDense{w}:
          PSet.valid_zero(1n+p)
        case S.PFull{}:
          vb
        case S.PBranch{al, ah}:
          match b:
            case S.PZero{}:
              PSet.valid_zero(1n+p)
            case S.PSparse{o}:
              PSet.valid_zero(1n+p)
            case S.PDense{w}:
              PSet.valid_zero(1n+p)
            case S.PFull{}:
              va
            case S.PBranch{bl, bh}:
              PSet.valid_mk(p, S.PSet.inter(p, al, bl),
                S.PSet.inter(p, ah, bh),
                PSet.valid_inter(p, al, bl,
                  E.Bool.and_l(S.PSet.valid(p, al, True{}),
                    S.PSet.valid(p, ah, True{}),
                    Vs2.PSet.both_of_branch(p, al, ah, va)),
                  E.Bool.and_l(S.PSet.valid(p, bl, True{}),
                    S.PSet.valid(p, bh, True{}),
                    Vs2.PSet.both_of_branch(p, bl, bh, vb))),
                PSet.valid_inter(p, ah, bh,
                  E.Bool.and_r(S.PSet.valid(p, al, True{}),
                    S.PSet.valid(p, ah, True{}),
                    Vs2.PSet.both_of_branch(p, al, ah, va)),
                  E.Bool.and_r(S.PSet.valid(p, bl, True{}),
                    S.PSet.valid(p, bh, True{}),
                    Vs2.PSet.both_of_branch(p, bl, bh, vb))))

law PSet.valid_diff:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {S.PSet.valid(d, a, True{}) == True{} : Bool}
  for +vb: {S.PSet.valid(d, b, True{}) == True{} : Bool}
  {S.PSet.valid(d, S.PSet.diff(d, a, b), True{}) == True{} : Bool}

def PSet.valid_diff(d, a, b, va, vb):
  match d:
    case 0n:
      PSet.valid_diff_leaf(a, b, va, vb)
    case 1n+p:
      match a:
        case S.PZero{}:
          PSet.valid_zero(1n+p)
        case S.PSparse{o}:
          PSet.valid_zero(1n+p)
        case S.PDense{w}:
          PSet.valid_zero(1n+p)
        case S.PFull{}:
          match b:
            case S.PZero{}:
              Vs2.PSet.valid_full(1n+p)
            case S.PFull{}:
              PSet.valid_zero(1n+p)
            case S.PSparse{o}:
              Vs2.PSet.valid_full(1n+p)
            case S.PDense{w}:
              Vs2.PSet.valid_full(1n+p)
            case S.PBranch{bl, bh}:
              PSet.valid_mk(p, S.PSet.diff(p, S.PFull{}, bl),
                S.PSet.diff(p, S.PFull{}, bh),
                PSet.valid_diff(p, S.PFull{}, bl,
                  Vs2.PSet.valid_full(p),
                  E.Bool.and_l(S.PSet.valid(p, bl, True{}),
                    S.PSet.valid(p, bh, True{}),
                    Vs2.PSet.both_of_branch(p, bl, bh, vb))),
                PSet.valid_diff(p, S.PFull{}, bh,
                  Vs2.PSet.valid_full(p),
                  E.Bool.and_r(S.PSet.valid(p, bl, True{}),
                    S.PSet.valid(p, bh, True{}),
                    Vs2.PSet.both_of_branch(p, bl, bh, vb))))
        case S.PBranch{al, ah}:
          match b:
            case S.PZero{}:
              va
            case S.PFull{}:
              PSet.valid_zero(1n+p)
            case S.PSparse{o}:
              va
            case S.PDense{w}:
              va
            case S.PBranch{bl, bh}:
              PSet.valid_mk(p, S.PSet.diff(p, al, bl),
                S.PSet.diff(p, ah, bh),
                PSet.valid_diff(p, al, bl,
                  E.Bool.and_l(S.PSet.valid(p, al, True{}),
                    S.PSet.valid(p, ah, True{}),
                    Vs2.PSet.both_of_branch(p, al, ah, va)),
                  E.Bool.and_l(S.PSet.valid(p, bl, True{}),
                    S.PSet.valid(p, bh, True{}),
                    Vs2.PSet.both_of_branch(p, bl, bh, vb))),
                PSet.valid_diff(p, ah, bh,
                  E.Bool.and_r(S.PSet.valid(p, al, True{}),
                    S.PSet.valid(p, ah, True{}),
                    Vs2.PSet.both_of_branch(p, al, ah, va)),
                  E.Bool.and_r(S.PSet.valid(p, bl, True{}),
                    S.PSet.valid(p, bh, True{}),
                    Vs2.PSet.both_of_branch(p, bl, bh, vb))))
