# proofs/preserve.bend -- the set operations keep a set well shaped.
#
# `PSet.wf` (proofs/shape.bend) is what the pointwise laws need of their
# operands: no payload above a leaf, and a dense leaf exactly 128 words. This
# file proves that union, intersection and difference produce it again.
#
# That is the step an induction over a query's syntax could not take before.
# A query is a tree of set operations over index sets; to use the pointwise
# law at a node, the proof has to know the operands are well shaped, and the
# operands are themselves results of operations. Without preservation the
# induction stops at depth one.
#
# Two places do the work. At a leaf every real operation is
# `compress(op(tile, tile))`, and compression produces one of four shapes --
# `PZero`, `PFull`, a sparse leaf, or the tile itself -- so the only thing to
# check is that the tile is still 128 words wide. Above a leaf every arm
# either returns an operand, returns `PZero`/`PFull`, or rebuilds with
# `PSet.mk`, and `PSet.mk` of two well-shaped halves is well shaped whichever
# collapse it takes.

import Base
import ./eq.bend as E
import ../core/count.bend as C
import ./shape.bend as Sh
import ./leaf.bend as Lf
import ./leafops.bend as Lo
import ../core/words.bend as Wo
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# Compression.
#
# `compress.pick` and its two helpers are proved for *every* decision they
# could be handed, not only the one the counter produces: the shape is well
# formed whichever branch is taken, so there is nothing to tie the decision
# back to the tile with.
# ---------------------------------------------------------------------------

law Nat.is_eq_128:
  for +n: Nat
  for +e: {n == 128n : Nat}
  {Nat.is_eq(n, 128n) == True{} : Bool}

def Nat.is_eq_128(n, e):
  %E.Nat.sym(n, 128n, e) : {Nat.is_eq(_, 128n) == True{} : Bool}
  {==}

law PSet.wf_compress_sparse:
  for +ws: List<&2, U32>
  for +lw: {List.length(&2, U32, ws) == 128n : Nat}
  for +sp: Bool
  {Sh.PSet.wf.leaf(S.PSet.compress.sparse(ws, sp)) == True{} : Bool}

def PSet.wf_compress_sparse(ws, lw, sp):
  match sp:
    case True{}:
      {==}
    case False{}:
      Nat.is_eq_128(List.length(&2, U32, ws), lw)

law PSet.wf_compress_full:
  for +ws: List<&2, U32>
  for +lw: {List.length(&2, U32, ws) == 128n : Nat}
  for +k: Nat
  for +fu: Bool
  {Sh.PSet.wf.leaf(S.PSet.compress.full(ws, k, fu)) == True{} : Bool}

def PSet.wf_compress_full(ws, lw, k, fu):
  match fu:
    case True{}:
      {==}
    case False{}:
      PSet.wf_compress_sparse(ws, lw, C.Nat.upto(k, S.PSet.sparse_max()))

law PSet.wf_compress_pick:
  for +ws: List<&2, U32>
  for +lw: {List.length(&2, U32, ws) == 128n : Nat}
  for +k: Nat
  {Sh.PSet.wf.leaf(S.PSet.compress.pick(ws, k)) == True{} : Bool}

def PSet.wf_compress_pick(ws, lw, k):
  match k:
    case 0n:
      {==}
    case 1n+p:
      PSet.wf_compress_full(ws, lw, 1n+p, Nat.is_eq(1n+p, 4096n))

law PSet.wf_compress:
  for +ws: List<&2, U32>
  for +lw: {List.length(&2, U32, ws) == 128n : Nat}
  {Sh.PSet.wf.leaf(S.PSet.compress(ws)) == True{} : Bool}

def PSet.wf_compress(ws, lw):
  PSet.wf_compress_pick(ws, lw, Wo.Words.count(ws))

# ---------------------------------------------------------------------------
# The three tiles, still 128 words wide.
# ---------------------------------------------------------------------------

law PSet.or_width:
  for +a: S.PSet
  for +b: S.PSet
  for +va: {Sh.PSet.wf.leaf(a) == True{} : Bool}
  for +vb: {Sh.PSet.wf.leaf(b) == True{} : Bool}
  {List.length(&2, U32, Wo.Words.or(S.PSet.leaf_words(a),
    S.PSet.leaf_words(b))) == 128n : Nat}

def PSet.or_width(a, b, va, vb):
  Equal.trans(Nat,
    List.length(&2, U32, Wo.Words.or(S.PSet.leaf_words(a),
      S.PSet.leaf_words(b))),
    List.length(&2, U32, S.PSet.leaf_words(a)), 128n,
    Lo.Words.len_or(S.PSet.leaf_words(a), S.PSet.leaf_words(b),
      Equal.trans(Nat, List.length(&2, U32, S.PSet.leaf_words(a)), 128n,
        List.length(&2, U32, S.PSet.leaf_words(b)),
        Sh.PSet.wf_leaf_words_width(a, va),
        E.Nat.sym(List.length(&2, U32, S.PSet.leaf_words(b)), 128n,
          Sh.PSet.wf_leaf_words_width(b, vb)))),
    Sh.PSet.wf_leaf_words_width(a, va))

law PSet.and_width:
  for +a: S.PSet
  for +b: S.PSet
  for +va: {Sh.PSet.wf.leaf(a) == True{} : Bool}
  for +vb: {Sh.PSet.wf.leaf(b) == True{} : Bool}
  {List.length(&2, U32, Wo.Words.and(S.PSet.leaf_words(a),
    S.PSet.leaf_words(b))) == 128n : Nat}

def PSet.and_width(a, b, va, vb):
  Equal.trans(Nat,
    List.length(&2, U32, Wo.Words.and(S.PSet.leaf_words(a),
      S.PSet.leaf_words(b))),
    List.length(&2, U32, S.PSet.leaf_words(a)), 128n,
    Lo.Words.len_and(S.PSet.leaf_words(a), S.PSet.leaf_words(b),
      Equal.trans(Nat, List.length(&2, U32, S.PSet.leaf_words(a)), 128n,
        List.length(&2, U32, S.PSet.leaf_words(b)),
        Sh.PSet.wf_leaf_words_width(a, va),
        E.Nat.sym(List.length(&2, U32, S.PSet.leaf_words(b)), 128n,
          Sh.PSet.wf_leaf_words_width(b, vb)))),
    Sh.PSet.wf_leaf_words_width(a, va))

# ---------------------------------------------------------------------------
# A leaf operation.
# ---------------------------------------------------------------------------

law PSet.wf_union_leaf:
  for +a: S.PSet
  for +b: S.PSet
  for +va: {Sh.PSet.wf.leaf(a) == True{} : Bool}
  for +vb: {Sh.PSet.wf.leaf(b) == True{} : Bool}
  {Sh.PSet.wf.leaf(S.PSet.union.leaf(a, b)) == True{} : Bool}

def PSet.wf_union_leaf(a, b, va, vb):
  match a:
    case S.PZero{}:
      vb
    case S.PFull{}:
      {==}
    case S.PBranch{l, h}:
      vb
    case S.PSparse{ao}:
      PSet.wf_compress(Wo.Words.or(S.PSet.leaf_words(S.PSparse{ao}),
        S.PSet.leaf_words(b)),
        PSet.or_width(S.PSparse{ao}, b, va, vb))
    case S.PDense{aw}:
      PSet.wf_compress(Wo.Words.or(S.PSet.leaf_words(S.PDense{aw}),
        S.PSet.leaf_words(b)),
        PSet.or_width(S.PDense{aw}, b, va, vb))

law PSet.wf_inter_leaf:
  for +a: S.PSet
  for +b: S.PSet
  for +va: {Sh.PSet.wf.leaf(a) == True{} : Bool}
  for +vb: {Sh.PSet.wf.leaf(b) == True{} : Bool}
  {Sh.PSet.wf.leaf(S.PSet.inter.leaf(a, b)) == True{} : Bool}

def PSet.wf_inter_leaf(a, b, va, vb):
  match a:
    case S.PZero{}:
      {==}
    case S.PFull{}:
      vb
    case S.PBranch{l, h}:
      {==}
    case S.PSparse{ao}:
      PSet.wf_compress(Wo.Words.and(S.PSet.leaf_words(S.PSparse{ao}),
        S.PSet.leaf_words(b)),
        PSet.and_width(S.PSparse{ao}, b, va, vb))
    case S.PDense{aw}:
      PSet.wf_compress(Wo.Words.and(S.PSet.leaf_words(S.PDense{aw}),
        S.PSet.leaf_words(b)),
        PSet.and_width(S.PDense{aw}, b, va, vb))

law PSet.sub_width:
  for +a: S.PSet
  for +b: S.PSet
  for +va: {Sh.PSet.wf.leaf(a) == True{} : Bool}
  {List.length(&2, U32, Wo.Words.diff(S.PSet.leaf_words(a),
    S.PSet.leaf_words(b))) == 128n : Nat}

def PSet.sub_width(a, b, va):
  Equal.trans(Nat,
    List.length(&2, U32, Wo.Words.diff(S.PSet.leaf_words(a),
      S.PSet.leaf_words(b))),
    List.length(&2, U32, S.PSet.leaf_words(a)), 128n,
    Lo.Words.len_diff(S.PSet.leaf_words(a), S.PSet.leaf_words(b)),
    Sh.PSet.wf_leaf_words_width(a, va))

law PSet.wf_diff_leaf:
  for +a: S.PSet
  for +b: S.PSet
  for +va: {Sh.PSet.wf.leaf(a) == True{} : Bool}
  for +vb: {Sh.PSet.wf.leaf(b) == True{} : Bool}
  {Sh.PSet.wf.leaf(S.PSet.diff.leaf(a, b)) == True{} : Bool}

def PSet.wf_diff_leaf(a, b, va, vb):
  match a:
    case S.PZero{}:
      {==}
    case S.PBranch{l, h}:
      {==}
    case S.PFull{}:
      PSet.wf_compress(Wo.Words.diff(S.PSet.leaf_words(S.PFull{}),
        S.PSet.leaf_words(b)),
        PSet.sub_width(S.PFull{}, b, va))
    case S.PSparse{ao}:
      PSet.wf_compress(Wo.Words.diff(S.PSet.leaf_words(S.PSparse{ao}),
        S.PSet.leaf_words(b)),
        PSet.sub_width(S.PSparse{ao}, b, va))
    case S.PDense{aw}:
      PSet.wf_compress(Wo.Words.diff(S.PSet.leaf_words(S.PDense{aw}),
        S.PSet.leaf_words(b)),
        PSet.sub_width(S.PDense{aw}, b, va))

# ---------------------------------------------------------------------------
# Branch construction. Proved for every collapse decision, again because the
# result is well shaped whichever one is taken.
# ---------------------------------------------------------------------------

law PSet.wf_mk_z:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +vl: {Sh.PSet.wf(p, lo, True{}) == True{} : Bool}
  for +vh: {Sh.PSet.wf(p, hi, True{}) == True{} : Bool}
  {Sh.PSet.wf(1n+p, S.PSet.mk.z(lo, hi), True{}) == True{} : Bool}

def PSet.wf_mk_z(p, lo, hi, vl, vh):
  match hi:
    case S.PZero{}:
      Sh.PSet.wf_zero(1n+p)
    case S.PFull{}:
      Sh.PSet.wf_branch(p, lo, S.PFull{}, vl, vh)
    case S.PSparse{o}:
      Sh.PSet.wf_branch(p, lo, S.PSparse{o}, vl, vh)
    case S.PDense{w}:
      Sh.PSet.wf_branch(p, lo, S.PDense{w}, vl, vh)
    case S.PBranch{x, y}:
      Sh.PSet.wf_branch(p, lo, S.PBranch{x, y}, vl, vh)

law PSet.wf_mk_f:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +vl: {Sh.PSet.wf(p, lo, True{}) == True{} : Bool}
  for +vh: {Sh.PSet.wf(p, hi, True{}) == True{} : Bool}
  {Sh.PSet.wf(1n+p, S.PSet.mk.f(lo, hi), True{}) == True{} : Bool}

def PSet.wf_mk_f(p, lo, hi, vl, vh):
  match hi:
    case S.PFull{}:
      Sh.PSet.wf_full(1n+p)
    case S.PZero{}:
      Sh.PSet.wf_branch(p, lo, S.PZero{}, vl, vh)
    case S.PSparse{o}:
      Sh.PSet.wf_branch(p, lo, S.PSparse{o}, vl, vh)
    case S.PDense{w}:
      Sh.PSet.wf_branch(p, lo, S.PDense{w}, vl, vh)
    case S.PBranch{x, y}:
      Sh.PSet.wf_branch(p, lo, S.PBranch{x, y}, vl, vh)

law PSet.wf_mk_hi:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +lz: Bool
  for +lf: Bool
  for +vl: {Sh.PSet.wf(p, lo, True{}) == True{} : Bool}
  for +vh: {Sh.PSet.wf(p, hi, True{}) == True{} : Bool}
  {Sh.PSet.wf(1n+p, S.PSet.mk.hi(lo, hi, lz, lf), True{}) == True{} : Bool}

def PSet.wf_mk_hi(p, lo, hi, lz, lf, vl, vh):
  match lz:
    case True{}:
      PSet.wf_mk_z(p, lo, hi, vl, vh)
    case False{}:
      match lf:
        case True{}:
          PSet.wf_mk_f(p, lo, hi, vl, vh)
        case False{}:
          Sh.PSet.wf_branch(p, lo, hi, vl, vh)

law PSet.wf_mk:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +vl: {Sh.PSet.wf(p, lo, True{}) == True{} : Bool}
  for +vh: {Sh.PSet.wf(p, hi, True{}) == True{} : Bool}
  {Sh.PSet.wf(1n+p, S.PSet.mk(lo, hi), True{}) == True{} : Bool}

def PSet.wf_mk(p, lo, hi, vl, vh):
  PSet.wf_mk_hi(p, lo, hi, S.PSet.is_zero(lo), S.PSet.is_full(lo), vl, vh)

# ---------------------------------------------------------------------------
# The three operations, at any depth.
#
# Every arm is one of four things: an operand handed back, a `PZero` or
# `PFull`, or a rebuilt branch. The first keeps the hypothesis it came with,
# the second two are well shaped at any depth, and the third is the lemma
# above.
# ---------------------------------------------------------------------------

law PSet.wf_union:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {Sh.PSet.wf(d, a, True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(d, b, True{}) == True{} : Bool}
  {Sh.PSet.wf(d, S.PSet.union(d, a, b), True{}) == True{} : Bool}

def PSet.wf_union(d, a, b, va, vb):
  match d:
    case 0n:
      PSet.wf_union_leaf(a, b, va, vb)
    case 1n+p:
      match a:
        case S.PZero{}:
          vb
        case S.PFull{}:
          Sh.PSet.wf_full(1n+p)
        case S.PSparse{o}:
          vb
        case S.PDense{w}:
          vb
        case S.PBranch{al, ah}:
          match b:
            case S.PZero{}:
              va
            case S.PFull{}:
              Sh.PSet.wf_full(1n+p)
            case S.PSparse{o}:
              va
            case S.PDense{w}:
              va
            case S.PBranch{bl, bh}:
              PSet.wf_mk(p, S.PSet.union(p, al, bl),
                S.PSet.union(p, ah, bh),
                PSet.wf_union(p, al, bl, Sh.PSet.wf_lo(p, al, ah, va),
                  Sh.PSet.wf_lo(p, bl, bh, vb)),
                PSet.wf_union(p, ah, bh, Sh.PSet.wf_hi(p, al, ah, va),
                  Sh.PSet.wf_hi(p, bl, bh, vb)))

law PSet.wf_inter:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {Sh.PSet.wf(d, a, True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(d, b, True{}) == True{} : Bool}
  {Sh.PSet.wf(d, S.PSet.inter(d, a, b), True{}) == True{} : Bool}

def PSet.wf_inter(d, a, b, va, vb):
  match d:
    case 0n:
      PSet.wf_inter_leaf(a, b, va, vb)
    case 1n+p:
      match a:
        case S.PZero{}:
          Sh.PSet.wf_zero(1n+p)
        case S.PSparse{o}:
          Sh.PSet.wf_zero(1n+p)
        case S.PDense{w}:
          Sh.PSet.wf_zero(1n+p)
        case S.PFull{}:
          vb
        case S.PBranch{al, ah}:
          match b:
            case S.PZero{}:
              Sh.PSet.wf_zero(1n+p)
            case S.PSparse{o}:
              Sh.PSet.wf_zero(1n+p)
            case S.PDense{w}:
              Sh.PSet.wf_zero(1n+p)
            case S.PFull{}:
              va
            case S.PBranch{bl, bh}:
              PSet.wf_mk(p, S.PSet.inter(p, al, bl),
                S.PSet.inter(p, ah, bh),
                PSet.wf_inter(p, al, bl, Sh.PSet.wf_lo(p, al, ah, va),
                  Sh.PSet.wf_lo(p, bl, bh, vb)),
                PSet.wf_inter(p, ah, bh, Sh.PSet.wf_hi(p, al, ah, va),
                  Sh.PSet.wf_hi(p, bl, bh, vb)))

law PSet.wf_diff:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +va: {Sh.PSet.wf(d, a, True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(d, b, True{}) == True{} : Bool}
  {Sh.PSet.wf(d, S.PSet.diff(d, a, b), True{}) == True{} : Bool}

def PSet.wf_diff(d, a, b, va, vb):
  match d:
    case 0n:
      PSet.wf_diff_leaf(a, b, va, vb)
    case 1n+p:
      match a:
        case S.PZero{}:
          Sh.PSet.wf_zero(1n+p)
        case S.PSparse{o}:
          Sh.PSet.wf_zero(1n+p)
        case S.PDense{w}:
          Sh.PSet.wf_zero(1n+p)
        case S.PFull{}:
          match b:
            case S.PZero{}:
              Sh.PSet.wf_full(1n+p)
            case S.PFull{}:
              Sh.PSet.wf_zero(1n+p)
            case S.PSparse{o}:
              Sh.PSet.wf_full(1n+p)
            case S.PDense{w}:
              Sh.PSet.wf_full(1n+p)
            case S.PBranch{bl, bh}:
              PSet.wf_mk(p, S.PSet.diff(p, S.PFull{}, bl),
                S.PSet.diff(p, S.PFull{}, bh),
                PSet.wf_diff(p, S.PFull{}, bl, Sh.PSet.wf_full(p),
                  Sh.PSet.wf_lo(p, bl, bh, vb)),
                PSet.wf_diff(p, S.PFull{}, bh, Sh.PSet.wf_full(p),
                  Sh.PSet.wf_hi(p, bl, bh, vb)))
        case S.PBranch{al, ah}:
          match b:
            case S.PZero{}:
              va
            case S.PFull{}:
              Sh.PSet.wf_zero(1n+p)
            case S.PSparse{o}:
              va
            case S.PDense{w}:
              va
            case S.PBranch{bl, bh}:
              PSet.wf_mk(p, S.PSet.diff(p, al, bl), S.PSet.diff(p, ah, bh),
                PSet.wf_diff(p, al, bl, Sh.PSet.wf_lo(p, al, ah, va),
                  Sh.PSet.wf_lo(p, bl, bh, vb)),
                PSet.wf_diff(p, ah, bh, Sh.PSet.wf_hi(p, al, ah, va),
                  Sh.PSet.wf_hi(p, bl, bh, vb)))
