# proofs/insert.bend -- inserting never loses a member.
#
# `inserting_adds_exactly_that_ordinal` (P-01) says the ordinal just inserted
# is present. It does not say the ones already there still are, and nothing
# built out of repeated insertion can be reasoned about until it does: a set
# assembled from a list -- the universe of `Full`, a type filter's result, a
# receiver's inventory projected into the source universe -- is a fold of
# `PSet.insert` over that list, and every step has to keep what the steps
# before it put in.
#
# The shape hypothesis is doing real work here, as it does for the pointwise
# laws. Above a leaf `PSet.add` treats a sparse or dense payload as an empty
# subtree and replaces it with a fresh branch, while `PSet.mem` reads it as a
# set of members; so for that one shape inserting *does* lose members, and it
# is exactly the shape `PSet.wf` rules out.

import Base
import ./eq.bend as E
import ./shape.bend as Sh
import ./preserve.bend as Pr
import ./leaf.bend as Lf
import ./ords.bend as PO
import ./bitset.bend as Bs
import ./bridge.bend as Br
import ./faithful.bend as Fa
import ./descend.bend as Dc
import ../core/count.bend as C
import ../core/ords.bend as O
import ../core/words.bend as Wo
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# The offset list.
# ---------------------------------------------------------------------------

law Ords.elem_go_mono:
  for +l: List<&2, U32>
  for +x: U32
  for +acc: Bool
  for +ok: {O.Ords.elem.go(l, x, False{}) == True{} : Bool}
  {O.Ords.elem.go(l, x, acc) == True{} : Bool}

def Ords.elem_go_mono(l, x, acc, ok):
  match acc:
    case False{}:
      ok
    case True{}:
      PO.Ords.elem_go_found(l, x)

law Ords.insert_go_keeps:
  for +xs: List<&2, U32>
  for +acc: Bool
  for +y: U32
  for +c: Cmp
  for +x: U32
  for +ok: {O.Ords.elem.go(xs, x, acc) == True{} : Bool}
  {O.Ords.elem.go(O.Ords.insert.go(xs, y, c), x, acc) == True{} : Bool}

def Ords.insert_go_keeps(xs, acc, y, c, x, ok):
  match xs:
    case Nil{}:
      match acc:
        case True{}:
          {==}
        case False{}:
          E.Bool.noconf({O.Ords.elem.go(O.Ords.insert.go(Nil{}, y, c), x,
            False{}) == True{} : Bool}, ok)
    case Con{h, t}:
      match acc:
        case True{}:
          PO.Ords.elem_go_found(O.Ords.insert.go(Con{h, t}, y, c), x)
        case False{}:
          match c:
            case EQ{}:
              ok
            case GT{}:
              Ords.elem_go_mono(Con{h, t}, x, U32.is_eq(y, x), ok)
            case LT{}:
              Ords.insert_go_keeps(t, U32.is_eq(h, x), y,
                O.Ords.head_one(t, y), x, ok)

law Ords.elem_insert_keeps:
  for +xs: List<&2, U32>
  for +y: U32
  for +x: U32
  for +ok: {O.Ords.elem(xs, x) == True{} : Bool}
  {O.Ords.elem(O.Ords.insert(xs, y), x) == True{} : Bool}

def Ords.elem_insert_keeps(xs, y, x, ok):
  Ords.insert_go_keeps(xs, False{}, y, O.Ords.head_one(xs, y), x, ok)

# ---------------------------------------------------------------------------
# The leaf.
# ---------------------------------------------------------------------------

law PSet.add_leaf_pick_keeps:
  for +offs: List<&2, U32>
  for +x: U32
  for +small: Bool
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  for +ok: {O.Ords.elem(offs, x) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.add.leaf.pick(offs, small), x) == True{} : Bool}

def PSet.add_leaf_pick_keeps(offs, x, small, inr, ok):
  match small:
    case True{}:
      ok
    case False{}:
      %E.Bool.sym(
        Wo.Words.bit(S.PSet.spread(offs, Wo.Words.zeros(128n)), x),
        O.Ords.elem(offs, x),
        Br.PSet.sparse_matches_its_tile(offs, x,
          Fa.PSet.zeros_fits(x, inr)))
        : {_ == True{} : Bool}
      ok

law PSet.add_leaf_keeps:
  for +s: S.PSet
  for +y: U32
  for +x: U32
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  for +ok: {S.PSet.mem.leaf(s, x) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.add.leaf(s, y), x) == True{} : Bool}

def PSet.add_leaf_keeps(s, y, x, inr, ok):
  match s:
    case S.PZero{}:
      E.Bool.noconf({S.PSet.mem.leaf(S.PSet.add.leaf(S.PZero{}, y), x)
        == True{} : Bool}, ok)
    case S.PBranch{l, h}:
      E.Bool.noconf({S.PSet.mem.leaf(
        S.PSet.add.leaf(S.PBranch{l, h}, y), x) == True{} : Bool}, ok)
    case S.PFull{}:
      {==}
    case S.PDense{ws}:
      Bs.Words.bit_set_mono(ws, x, y, ok)
    case S.PSparse{offs}:
      PSet.add_leaf_pick_keeps(O.Ords.insert(offs, y), x,
        C.Nat.upto(List.length(&2, U32, O.Ords.insert(offs, y)),
          S.PSet.sparse_max()), inr,
        Ords.elem_insert_keeps(offs, y, x, ok))

# ---------------------------------------------------------------------------
# The tree.
#
# `bx` is the branch the ordinal being asked about lives in, carried as a
# parameter with an equation naming it; `b` is the branch the insert descends
# into, which `PSet.add` already takes as a parameter for the same reason.
# The four combinations are the whole argument: when they agree, the half the
# ordinal is in is the half that changed, and that is the induction step; when
# they differ, the half the ordinal is in is untouched.
# ---------------------------------------------------------------------------

law PSet.add_keeps:
  for +d: Nat
  for +s: S.PSet
  for +b: Bool
  for +bx: Bool
  for +h: U32
  for +y: U32
  for +x: U32
  for +eh: {h == U32.shln(1, 11n+d) : U32}
  for +dok: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +ebx: {bx == U32.is_lt(x, h) : Bool}
  for +v: {Sh.PSet.wf(d, s, True{}) == True{} : Bool}
  for +ok: {S.PSet.mem(d, s, h, x) == True{} : Bool}
  {S.PSet.mem(d, S.PSet.add(d, s, h, y, b), h, x) == True{} : Bool}

# The hypothesis, carried onto the branch the ordinal is in.
law PSet.mem_lo:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +h: U32
  for +x: U32
  for +ebx: {True{} == U32.is_lt(x, h) : Bool}
  for +ok: {S.PSet.mem(1n+p, S.PBranch{lo, hi}, h, x) == True{} : Bool}
  {S.PSet.mem(p, lo, U32.shr(h), x) == True{} : Bool}

def PSet.mem_lo(p, lo, hi, h, x, ebx, ok):
  %E.Bool.sym(True{}, U32.is_lt(x, h), ebx)
    : {S.PSet.mem(p, S.PSet.pick(_, lo, hi), U32.shr(h),
        S.PSet.rebase(_, h, x)) == True{} : Bool}
  ok

law PSet.mem_hi:
  for +p: Nat
  for +lo: S.PSet
  for +hi: S.PSet
  for +h: U32
  for +x: U32
  for +ebx: {False{} == U32.is_lt(x, h) : Bool}
  for +ok: {S.PSet.mem(1n+p, S.PBranch{lo, hi}, h, x) == True{} : Bool}
  {S.PSet.mem(p, hi, U32.shr(h), U32.sub(x, h)) == True{} : Bool}

def PSet.mem_hi(p, lo, hi, h, x, ebx, ok):
  %E.Bool.sym(False{}, U32.is_lt(x, h), ebx)
    : {S.PSet.mem(p, S.PSet.pick(_, lo, hi), U32.shr(h),
        S.PSet.rebase(_, h, x)) == True{} : Bool}
  ok

def PSet.add_keeps(d, s, b, bx, h, y, x, eh, dok, inv, ebx, v, ok):
  match d:
    case 0n:
      PSet.add_leaf_keeps(s, y, x, inv, ok)
    case 1n+p:
      match s:
        case S.PFull{}:
          {==}
        case S.PZero{}:
          E.Bool.noconf({S.PSet.mem(1n+p,
            S.PSet.add(1n+p, S.PZero{}, h, y, b), h, x)
            == True{} : Bool}, ok)
        case S.PSparse{o}:
          E.Bool.noconf({S.PSet.mem(1n+p,
            S.PSet.add(1n+p, S.PSparse{o}, h, y, b), h, x)
            == True{} : Bool}, v)
        case S.PDense{w}:
          E.Bool.noconf({S.PSet.mem(1n+p,
            S.PSet.add(1n+p, S.PDense{w}, h, y, b), h, x)
            == True{} : Bool}, v)
        case S.PBranch{lo, hi}:
          match b:
            case True{}:
              match bx:
                case True{}:
                  %ebx : {S.PSet.mem(p, S.PSet.pick(_,
                      S.PSet.add(p, lo, U32.shr(h), y,
                        U32.is_lt(y, U32.shr(h))), hi), U32.shr(h),
                      S.PSet.rebase(_, h, x)) == True{} : Bool}
                  PSet.add_keeps(p, lo, U32.is_lt(y, U32.shr(h)),
                    U32.is_lt(x, U32.shr(h)), U32.shr(h), y, x,
                    Lf.PSet.half_shr(p, h, eh, dok),
                    Dc.Nat.gt_down(32n, 11n+p, dok),
                    Lf.PSet.range_lo(p, h, x, eh, dok, ebx),
                    {==}, Sh.PSet.wf_lo(p, lo, hi, v),
                    PSet.mem_lo(p, lo, hi, h, x, ebx, ok))
                case False{}:
                  %ebx : {S.PSet.mem(p, S.PSet.pick(_,
                      S.PSet.add(p, lo, U32.shr(h), y,
                        U32.is_lt(y, U32.shr(h))), hi), U32.shr(h),
                      S.PSet.rebase(_, h, x)) == True{} : Bool}
                  PSet.mem_hi(p, lo, hi, h, x, ebx, ok)
            case False{}:
              match bx:
                case True{}:
                  %ebx : {S.PSet.mem(p, S.PSet.pick(_, lo,
                      S.PSet.add(p, hi, U32.shr(h), U32.sub(y, h),
                        U32.is_lt(U32.sub(y, h), U32.shr(h)))), U32.shr(h),
                      S.PSet.rebase(_, h, x)) == True{} : Bool}
                  PSet.mem_lo(p, lo, hi, h, x, ebx, ok)
                case False{}:
                  %ebx : {S.PSet.mem(p, S.PSet.pick(_, lo,
                      S.PSet.add(p, hi, U32.shr(h), U32.sub(y, h),
                        U32.is_lt(U32.sub(y, h), U32.shr(h)))), U32.shr(h),
                      S.PSet.rebase(_, h, x)) == True{} : Bool}
                  PSet.add_keeps(p, hi,
                    U32.is_lt(U32.sub(y, h), U32.shr(h)),
                    U32.is_lt(U32.sub(x, h), U32.shr(h)), U32.shr(h),
                    U32.sub(y, h), U32.sub(x, h),
                    Lf.PSet.half_shr(p, h, eh, dok),
                    Dc.Nat.gt_down(32n, 11n+p, dok),
                    Lf.PSet.range_hi(p, h, x, eh, dok, ebx, inv),
                    {==}, Sh.PSet.wf_hi(p, lo, hi, v),
                    PSet.mem_hi(p, lo, hi, h, x, ebx, ok))

# ---------------------------------------------------------------------------
# P-01 again, from the weaker hypothesis.
#
# `PSet.mem_insert` in proofs/leaf.bend is P-01 with `PSet.valid`. A fold of
# insertions cannot carry `PSet.valid` -- nothing in this release proves the
# ascending-offsets condition is preserved -- but it can carry `PSet.wf`,
# which is all the argument uses. This is the same induction with that
# hypothesis; the published law still reads `PSet.valid`, and `PROOF.bend`
# weakens it on the way in.
# ---------------------------------------------------------------------------

law PSet.wf_word_index_bound:
  for +s: S.PSet
  for +x: U32
  for +v: {Sh.PSet.wf.leaf(s) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {C.Nat.gt(List.length(&2, U32, S.PSet.leaf_words(s)),
    U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}

def PSet.wf_word_index_bound(s, x, v, inr):
  %E.Nat.sym(List.length(&2, U32, S.PSet.leaf_words(s)), 128n,
    Sh.PSet.wf_leaf_words_width(s, v))
    : {C.Nat.gt(_, U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}
  Lf.PSet.shift_bound(x, inr)

law PSet.wf_fits_of_range:
  for +s: S.PSet
  for +x: U32
  for +v: {Sh.PSet.wf.leaf(s) == True{} : Bool}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {Wo.Words.has_word(S.PSet.leaf_words(s),
    U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}

def PSet.wf_fits_of_range(s, x, v, inr):
  Lf.Words.has_word_of_length(S.PSet.leaf_words(s),
    U32.to_nat(U32.shrn(x, 5n)),
    PSet.wf_word_index_bound(s, x, v, inr))

law PSet.wf_mem_add_go:
  for +d: Nat
  for +s: S.PSet
  for +h: U32
  for +x: U32
  for +b: Bool
  for +eh: {h == U32.shln(1, 11n+d) : U32}
  for +eb: {b == U32.is_lt(x, h) : Bool}
  for +dok: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +v: {Sh.PSet.wf(d, s, True{}) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  {S.PSet.mem(d, S.PSet.add(d, s, h, x, b), h, x) == True{} : Bool}

def PSet.wf_mem_add_go(d, s, h, x, b, eh, eb, dok, v, inv):
  match d:
    case 0n:
      Lf.PSet.mem_add_leaf(s, x, PSet.wf_fits_of_range(s, x, v, inv))
    case 1n+p:
      match s:
        case S.PFull{}:
          {==}
        case S.PSparse{o}:
          E.Bool.noconf({S.PSet.mem(1n+p,
            S.PSet.add(1n+p, S.PSparse{o}, h, x, b), h, x)
            == True{} : Bool}, v)
        case S.PDense{w}:
          E.Bool.noconf({S.PSet.mem(1n+p,
            S.PSet.add(1n+p, S.PDense{w}, h, x, b), h, x)
            == True{} : Bool}, v)
        case S.PZero{}:
          match b:
            case True{}:
              %eb
                : {S.PSet.mem(p, S.PSet.pick(_,
                    S.PSet.add(p, S.PZero{}, U32.shr(h), x,
                      U32.is_lt(x, U32.shr(h))), S.PZero{}),
                    U32.shr(h), S.PSet.rebase(_, h, x)) == True{} : Bool}
              PSet.wf_mem_add_go(p, S.PZero{}, U32.shr(h), x,
                U32.is_lt(x, U32.shr(h)),
                Lf.PSet.half_shr(p, h, eh, dok), {==},
                Dc.Nat.gt_down(32n, 11n+p, dok),
                Sh.PSet.wf_zero(p),
                Lf.PSet.range_lo(p, h, x, eh, dok, eb))
            case False{}:
              %eb
                : {S.PSet.mem(p, S.PSet.pick(_, S.PZero{},
                    S.PSet.add(p, S.PZero{}, U32.shr(h), U32.sub(x, h),
                      U32.is_lt(U32.sub(x, h), U32.shr(h)))),
                    U32.shr(h), S.PSet.rebase(_, h, x)) == True{} : Bool}
              PSet.wf_mem_add_go(p, S.PZero{}, U32.shr(h), U32.sub(x, h),
                U32.is_lt(U32.sub(x, h), U32.shr(h)),
                Lf.PSet.half_shr(p, h, eh, dok), {==},
                Dc.Nat.gt_down(32n, 11n+p, dok),
                Sh.PSet.wf_zero(p),
                Lf.PSet.range_hi(p, h, x, eh, dok, eb, inv))
        case S.PBranch{lo, hi}:
          match b:
            case True{}:
              %eb
                : {S.PSet.mem(p, S.PSet.pick(_,
                    S.PSet.add(p, lo, U32.shr(h), x,
                      U32.is_lt(x, U32.shr(h))), hi),
                    U32.shr(h), S.PSet.rebase(_, h, x)) == True{} : Bool}
              PSet.wf_mem_add_go(p, lo, U32.shr(h), x,
                U32.is_lt(x, U32.shr(h)),
                Lf.PSet.half_shr(p, h, eh, dok), {==},
                Dc.Nat.gt_down(32n, 11n+p, dok),
                Sh.PSet.wf_lo(p, lo, hi, v),
                Lf.PSet.range_lo(p, h, x, eh, dok, eb))
            case False{}:
              %eb
                : {S.PSet.mem(p, S.PSet.pick(_, lo,
                    S.PSet.add(p, hi, U32.shr(h), U32.sub(x, h),
                      U32.is_lt(U32.sub(x, h), U32.shr(h)))),
                    U32.shr(h), S.PSet.rebase(_, h, x)) == True{} : Bool}
              PSet.wf_mem_add_go(p, hi, U32.shr(h), U32.sub(x, h),
                U32.is_lt(U32.sub(x, h), U32.shr(h)),
                Lf.PSet.half_shr(p, h, eh, dok), {==},
                Dc.Nat.gt_down(32n, 11n+p, dok),
                Sh.PSet.wf_hi(p, lo, hi, v),
                Lf.PSet.range_hi(p, h, x, eh, dok, eb, inv))

law PSet.wf_mem_insert:
  for +s: S.PSet
  for +x: U32
  for +v: {Sh.PSet.wf(20n, s, True{}) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.insert(20n, s, x), x) == True{} : Bool}

def PSet.wf_mem_insert(s, x, v):
  PSet.wf_mem_add_go(20n, s, S.PSet.half(20n), x,
    U32.is_lt(x, S.PSet.half(20n)), {==}, {==}, {==}, v,
    Dc.U32.hi_zero_full(x))

law PSet.insert_keeps:
  for +s: S.PSet
  for +y: U32
  for +x: U32
  for +v: {Sh.PSet.wf(20n, s, True{}) == True{} : Bool}
  for +ok: {S.PSet.member(20n, s, x) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.insert(20n, s, y), x) == True{} : Bool}

def PSet.insert_keeps(s, y, x, v, ok):
  PSet.add_keeps(20n, s, U32.is_lt(y, S.PSet.half(20n)),
    U32.is_lt(x, S.PSet.half(20n)), S.PSet.half(20n), y, x,
    {==}, {==}, Dc.U32.hi_zero_full(x), {==}, v, ok)

# ---------------------------------------------------------------------------
# A set built from a list has every ordinal on the list.
#
# The two halves together: the ordinal each step inserts is present after that
# step (P-01), and every step after it keeps what is already there. This is
# the fact every set that enters the algebra from outside rests on -- the
# universe of `Full`, a type filter's result, and G-03's projection of a
# receiver's inventory into the source universe, which is a fold of insertion
# over the ordinals the identity table named.
# ---------------------------------------------------------------------------

def U32.head_eq(xs: List<&2, U32>, +x: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{a, t}:
      U32.is_eq(a, x)

law PSet.of_list_contains:
  for +xs: List<&2, U32>
  for +hit: Bool
  for +s: S.PSet
  for +x: U32
  for +eh: {hit == U32.head_eq(xs, x) : Bool}
  for +v: {Sh.PSet.wf(20n, s, True{}) == True{} : Bool}
  for +ok: {List.contains(~U32, ~U32.is_eq, xs, x) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.of_list(20n, xs, s), x) == True{} : Bool}

# The head matched, so the ordinal just inserted is the one asked about.
law PSet.insert_hit:
  for +s: S.PSet
  for +a: U32
  for +x: U32
  for +v: {Sh.PSet.wf(20n, s, True{}) == True{} : Bool}
  for +eq: {U32.is_eq(a, x) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.insert(20n, s, a), x) == True{} : Bool}

def PSet.insert_hit(s, a, x, v, eq):
  %E.U32.eq_reflect(a, x, eq)
    : {S.PSet.member(20n, S.PSet.insert(20n, s, a), _) == True{} : Bool}
  PSet.wf_mem_insert(s, a, v)

# The head did not match, so the tail holds it.
law PSet.contains_tail:
  for +t: List<&2, U32>
  for +a: U32
  for +x: U32
  for +eh: {False{} == U32.is_eq(a, x) : Bool}
  for +ok: {List.contains(~U32, ~U32.is_eq, Con{a, t}, x) == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, t, x) == True{} : Bool}

def PSet.contains_tail(t, a, x, eh, ok):
  %E.Bool.sym(False{}, U32.is_eq(a, x), eh)
    : {Bool.or(_, List.contains(~U32, ~U32.is_eq, t, x)) == True{} : Bool}
  ok

law PSet.of_list_keeps:
  for +xs: List<&2, U32>
  for +s: S.PSet
  for +x: U32
  for +v: {Sh.PSet.wf(20n, s, True{}) == True{} : Bool}
  for +ok: {S.PSet.member(20n, s, x) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.of_list(20n, xs, s), x) == True{} : Bool}

def PSet.of_list_keeps(xs, s, x, v, ok):
  match xs:
    case Nil{}:
      ok
    case Con{a, t}:
      PSet.of_list_keeps(t, S.PSet.insert(20n, s, a), x,
        Pr.PSet.wf_insert(20n, s, a, v),
        PSet.insert_keeps(s, a, x, v, ok))

def PSet.of_list_contains(xs, hit, s, x, eh, v, ok):
  match xs:
    case Nil{}:
      E.Bool.noconf({S.PSet.member(20n, S.PSet.of_list(20n, Nil{}, s), x)
        == True{} : Bool}, ok)
    case Con{a, t}:
      match hit:
        case True{}:
          PSet.of_list_keeps(t, S.PSet.insert(20n, s, a), x,
            Pr.PSet.wf_insert(20n, s, a, v),
            PSet.insert_hit(s, a, x, v,
              E.Bool.sym(True{}, U32.is_eq(a, x), eh)))
        case False{}:
          PSet.of_list_contains(t, U32.head_eq(t, x),
            S.PSet.insert(20n, s, a), x, {==},
            Pr.PSet.wf_insert(20n, s, a, v),
            PSet.contains_tail(t, a, x, eh, ok))

law PSet.from_list_contains:
  for +xs: List<&2, U32>
  for +x: U32
  for +ok: {List.contains(~U32, ~U32.is_eq, xs, x) == True{} : Bool}
  {S.PSet.member(20n, S.PSet.from_list(20n, xs), x) == True{} : Bool}

def PSet.from_list_contains(xs, x, ok):
  PSet.of_list_contains(xs, U32.head_eq(xs, x), S.PZero{}, x, {==},
    Sh.PSet.wf_zero(20n), ok)
