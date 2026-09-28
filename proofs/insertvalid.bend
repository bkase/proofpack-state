# proofs/insertvalid.bend -- insertion keeps the shape the store checks.
#
# proofs/validkeep.bend covers union, intersection and difference, which all
# build their leaves by compressing a tile. Insertion is the one operation
# that does not: a sparse leaf takes the new ordinal through `Ords.insert`,
# which is a sorted insert into the offsets themselves. So the ascending
# condition has to be carried through that insert, and the fitting condition
# with it.
#
# Every set that enters a query from outside the algebra is built by
# insertion -- the universe, a filter's result, a frontier's successors --
# so this is what lets the subset laws apply to any of them.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ./shape.bend as Sh
import ./shift.bend as Sf
import ./orderlist.bend as Ol
import ./validkeep.bend as Vk
import ./preserve.bend as Pr
import ./leaf.bend as Lf2
import ./leafdiff.bend as Lf3
import ./validshape.bend as Vs3
import ../core/count.bend as C
import ../core/ords.bend as O
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/set.bend as S

# ---------------------------------------------------------------------------
# A sorted insert keeps the list sorted.
# ---------------------------------------------------------------------------

law Ords.above_insert:
  for +t: List<&2, U32>
  for +h: U32
  for +x: U32
  for +c: Cmp
  for +ec: {c == O.Ords.head_one(t, x) : Cmp}
  for +ab: {Ol.Ords.above(h, t) == True{} : Bool}
  for +hx: {U32.is_lt(h, x) == True{} : Bool}
  {Ol.Ords.above(h, O.Ords.insert.go(t, x, c)) == True{} : Bool}

def Ords.above_insert(t, h, x, c, ec, ab, hx):
  match t:
    case Nil{}:
      hx
    case Con{y, u}:
      match c:
        case EQ{}:
          ab
        case GT{}:
          hx
        case LT{}:
          ab

law Ords.asc_insert:
  for +xs: List<&2, U32>
  for +x: U32
  for +c: Cmp
  for +ec: {c == O.Ords.head_one(xs, x) : Cmp}
  for +ax: {Ol.Ords.asc(xs) == True{} : Bool}
  {Ol.Ords.asc(O.Ords.insert.go(xs, x, c)) == True{} : Bool}

def Ords.asc_insert(xs, x, c, ec, ax):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      match c:
        case EQ{}:
          ax
        case GT{}:
          E.Bool.and_both(U32.is_lt(x, h),
            Ol.Ords.asc(Con{h, t}),
            Ol.U32.lt_of_cmp_gt(h, x,
              E.Cmp.sym(GT{}, O.Ords.head_one(Con{h, t}, x), ec)),
            ax)
        case LT{}:
          E.Bool.and_both(
            Ol.Ords.above(h, O.Ords.insert.go(t, x,
              O.Ords.head_one(t, x))),
            Ol.Ords.asc(O.Ords.insert.go(t, x,
              O.Ords.head_one(t, x))),
            Ords.above_insert(t, h, x, O.Ords.head_one(t, x), {==},
              E.Bool.and_l(Ol.Ords.above(h, t), Ol.Ords.asc(t), ax),
              Ol.U32.lt_of_cmp_lt(h, x,
                E.Cmp.sym(LT{}, O.Ords.head_one(Con{h, t}, x), ec))),
            Ords.asc_insert(t, x, O.Ords.head_one(t, x), {==},
              E.Bool.and_r(Ol.Ords.above(h, t), Ol.Ords.asc(t), ax)))

law Ords.all_fit_insert:
  for +xs: List<&2, U32>
  for +x: U32
  for +c: Cmp
  for +fx: {Sf.Ords.all_fit(xs, 12n) == True{} : Bool}
  for +hx: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {Sf.Ords.all_fit(O.Ords.insert.go(xs, x, c), 12n) == True{}
    : Bool}

def Ords.all_fit_insert(xs, x, c, fx, hx):
  match xs:
    case Nil{}:
      E.Bool.and_both(Dc.U32.hi_zero(x, 12n), True{}, hx, {==})
    case Con{h, t}:
      match c:
        case EQ{}:
          fx
        case GT{}:
          E.Bool.and_both(Dc.U32.hi_zero(x, 12n),
            Sf.Ords.all_fit(Con{h, t}, 12n), hx, fx)
        case LT{}:
          E.Bool.and_both(Dc.U32.hi_zero(h, 12n),
            Sf.Ords.all_fit(O.Ords.insert.go(t, x,
              O.Ords.head_one(t, x)), 12n),
            E.Bool.and_l(Dc.U32.hi_zero(h, 12n),
              Sf.Ords.all_fit(t, 12n), fx),
            Ords.all_fit_insert(t, x, O.Ords.head_one(t, x),
              E.Bool.and_r(Dc.U32.hi_zero(h, 12n),
                Sf.Ords.all_fit(t, 12n), fx), hx))

# ---------------------------------------------------------------------------
# A leaf takes the ordinal.
# ---------------------------------------------------------------------------

law PSet.valid_add_leaf_pick:
  for +offs: List<&2, U32>
  for +small: Bool
  for +ao: {Ol.Ords.asc(offs) == True{} : Bool}
  for +fo: {Sf.Ords.all_fit(offs, 12n) == True{} : Bool}
  {S.PSet.valid.leaf(S.PSet.add.leaf.pick(offs, small)) == True{}
    : Bool}

def PSet.valid_add_leaf_pick(offs, small, ao, fo):
  match small:
    case True{}:
      Vk.PSet.valid_offs_of_asc(offs, 0, True{}, ao, fo,
        Vk.Ords.head_above_first(offs, 0))
    case False{}:
      Vk.PSet.width_eq(S.PSet.spread(offs, Wo.Words.zeros(128n)),
        Equal.trans(Nat,
          List.length(&2, U32,
            S.PSet.spread(offs, Wo.Words.zeros(128n))),
          List.length(&2, U32, Wo.Words.zeros(128n)), 128n,
          Lf2.Words.length_spread(offs, Wo.Words.zeros(128n)),
          Lf2.Words.length_zeros(128n)))

law PSet.valid_add_leaf:
  for +s: S.PSet
  for +x: U32
  for +v: {S.PSet.valid.leaf(s) == True{} : Bool}
  for +hx: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {S.PSet.valid.leaf(S.PSet.add.leaf(s, x)) == True{} : Bool}

law PSet.valid_single:
  for +x: U32
  for +hx: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {S.PSet.valid.leaf(S.PSparse{Con{x, Nil{}}}) == True{} : Bool}

def PSet.valid_single(x, hx):
  Vk.PSet.valid_offs_of_asc(Con{x, Nil{}}, 0, True{}, {==},
    E.Bool.and_both(Dc.U32.hi_zero(x, 12n), True{}, hx, {==}),
    Vk.Ords.head_above_first(Con{x, Nil{}}, 0))

def PSet.valid_add_leaf(s, x, v, hx):
  match s:
    case S.PZero{}:
      PSet.valid_single(x, hx)
    case S.PBranch{l, h}:
      PSet.valid_single(x, hx)
    case S.PFull{}:
      {==}
    case S.PDense{ws}:
      Vk.PSet.width_eq(Wo.Words.set(ws, x),
        Equal.trans(Nat, List.length(&2, U32, Wo.Words.set(ws, x)),
          List.length(&2, U32, ws), 128n, Pr.Words.len_set(ws, x),
          Lf2.Nat.is_eq_reflect(List.length(&2, U32, ws), 128n, v)))
    case S.PSparse{offs}:
      PSet.valid_add_leaf_pick(O.Ords.insert(offs, x),
        C.Nat.upto(List.length(&2, U32, O.Ords.insert(offs, x)),
          S.PSet.sparse_max()),
        Ords.asc_insert(offs, x, O.Ords.head_one(offs, x), {==},
          Lf3.Ords.asc_of_valid_offs(offs, 0, True{}, True{}, v)),
        Ords.all_fit_insert(offs, x, O.Ords.head_one(offs, x),
          Vs3.Ords.all_fit_of_valid_offs(offs, 0, True{}, True{}, v),
          hx))

# ---------------------------------------------------------------------------
# And the tree, at any depth. Same arms as the `PSet.wf` version, with the
# range of the inserted ordinal carried down: the low half keeps it, the
# high half rebases it, and either way it still fits one bit lower.
# ---------------------------------------------------------------------------

law PSet.valid_add:
  for +d: Nat
  for +s: S.PSet
  for +h: U32
  for +x: U32
  for +b: Bool
  for +eh: {h == U32.shln(1, 11n+d) : U32}
  for +eb: {b == U32.is_lt(x, h) : Bool}
  for +dok: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +v: {S.PSet.valid(d, s, True{}) == True{} : Bool}
  {S.PSet.valid(d, S.PSet.add(d, s, h, x, b), True{}) == True{}
    : Bool}

def PSet.shr_half(+p: Nat, +h: U32,
  +eh: {h == U32.shln(1, 12n+p) : U32},
  +dok: {C.Nat.gt(32n, 12n+p) == True{} : Bool})
  -> {U32.shr(h) == U32.shln(1, 11n+p) : U32}:
  %E.U32.sym(h, U32.shln(1, 12n+p), eh)
    : {U32.shr(_) == U32.shln(1, 11n+p) : U32}
  Dc.U32.shr_shln_one(11n+p, dok)

def PSet.lt_cast(+p: Nat, +h: U32, +x: U32,
  +eh: {h == U32.shln(1, 12n+p) : U32},
  +eb: {True{} == U32.is_lt(x, h) : Bool})
  -> {U32.is_lt(x, U32.shln(1, 12n+p)) == True{} : Bool}:
  %eh
    : {U32.is_lt(x, _) == True{} : Bool}
  E.Bool.sym(True{}, U32.is_lt(x, h), eb)

def PSet.low_fits(+p: Nat, +h: U32, +x: U32,
  +eh: {h == U32.shln(1, 12n+p) : U32},
  +dok: {C.Nat.gt(32n, 12n+p) == True{} : Bool},
  +eb: {True{} == U32.is_lt(x, h) : Bool})
  -> {Dc.U32.hi_zero(x, 12n+p) == True{} : Bool}:
  %Dc.U32.is_lt_shln(x, 12n+p, dok)
    : {_ == True{} : Bool}
  PSet.lt_cast(p, h, x, eh, eb)

def PSet.lt_cast_false(+p: Nat, +h: U32, +x: U32,
  +eh: {h == U32.shln(1, 12n+p) : U32},
  +eb: {False{} == U32.is_lt(x, h) : Bool})
  -> {U32.is_lt(x, U32.shln(1, 12n+p)) == False{} : Bool}:
  %eh
    : {U32.is_lt(x, _) == False{} : Bool}
  E.Bool.sym(False{}, U32.is_lt(x, h), eb)

def PSet.not_fits(+p: Nat, +h: U32, +x: U32,
  +eh: {h == U32.shln(1, 12n+p) : U32},
  +dok: {C.Nat.gt(32n, 12n+p) == True{} : Bool},
  +eb: {False{} == U32.is_lt(x, h) : Bool})
  -> {Dc.U32.hi_zero(x, 12n+p) == False{} : Bool}:
  %Dc.U32.is_lt_shln(x, 12n+p, dok)
    : {_ == False{} : Bool}
  PSet.lt_cast_false(p, h, x, eh, eb)

def PSet.high_fits(+p: Nat, +h: U32, +x: U32,
  +eh: {h == U32.shln(1, 12n+p) : U32},
  +dok: {C.Nat.gt(32n, 12n+p) == True{} : Bool},
  +eb: {False{} == U32.is_lt(x, h) : Bool},
  +inv: {Dc.U32.hi_zero(x, 13n+p) == True{} : Bool})
  -> {Dc.U32.hi_zero(U32.sub(x, h), 12n+p) == True{} : Bool}:
  %E.U32.sym(h, U32.shln(1, 12n+p), eh)
    : {Dc.U32.hi_zero(U32.sub(x, _), 12n+p) == True{} : Bool}
  Dc.U32.hi_zero_sub(x, 12n+p, inv,
    PSet.not_fits(p, h, x, eh, dok, eb))

def PSet.valid_add(d, s, h, x, b, eh, eb, dok, inv, v):
  match d:
    case 0n:
      PSet.valid_add_leaf(s, x, v, inv)
    case 1n+p:
      match s:
        case S.PFull{}:
          Vs3.PSet.valid_full(1n+p)
        case S.PSparse{o}:
          E.Bool.noconf({S.PSet.valid(1n+p,
            S.PSet.add(1n+p, S.PSparse{o}, h, x, b), True{})
            == True{} : Bool}, v)
        case S.PDense{w}:
          E.Bool.noconf({S.PSet.valid(1n+p,
            S.PSet.add(1n+p, S.PDense{w}, h, x, b), True{})
            == True{} : Bool}, v)
        case S.PZero{}:
          match b:
            case True{}:
              Vk.PSet.valid_branch(p,
                S.PSet.add(p, S.PZero{}, U32.shr(h), x,
                  U32.is_lt(x, U32.shr(h))), S.PZero{},
                PSet.valid_add(p, S.PZero{}, U32.shr(h), x,
                  U32.is_lt(x, U32.shr(h)),
                  PSet.shr_half(p, h, eh, dok), {==},
                  Dc.Nat.gt_down(32n, 11n+p, dok),
                  PSet.low_fits(p, h, x, eh, dok, eb), Vk.PSet.valid_zero(p)), Vk.PSet.valid_zero(p))
            case False{}:
              Vk.PSet.valid_branch(p, S.PZero{},
                S.PSet.add(p, S.PZero{}, U32.shr(h), U32.sub(x, h),
                  U32.is_lt(U32.sub(x, h), U32.shr(h))), Vk.PSet.valid_zero(p),
                PSet.valid_add(p, S.PZero{}, U32.shr(h), U32.sub(x, h),
                  U32.is_lt(U32.sub(x, h), U32.shr(h)),
                  PSet.shr_half(p, h, eh, dok), {==},
                  Dc.Nat.gt_down(32n, 11n+p, dok),
                  PSet.high_fits(p, h, x, eh, dok, eb, inv), Vk.PSet.valid_zero(p)))
        case S.PBranch{lo, hi}:
          match b:
            case True{}:
              Vk.PSet.valid_branch(p,
                S.PSet.add(p, lo, U32.shr(h), x,
                  U32.is_lt(x, U32.shr(h))), hi,
                PSet.valid_add(p, lo, U32.shr(h), x,
                  U32.is_lt(x, U32.shr(h)),
                  PSet.shr_half(p, h, eh, dok), {==},
                  Dc.Nat.gt_down(32n, 11n+p, dok),
                  PSet.low_fits(p, h, x, eh, dok, eb), E.Bool.and_l(S.PSet.valid(p, lo, True{}),
                    S.PSet.valid(p, hi, True{}),
                    Vs3.PSet.both_of_branch(p, lo, hi, v))), E.Bool.and_r(S.PSet.valid(p, lo, True{}),
                    S.PSet.valid(p, hi, True{}),
                    Vs3.PSet.both_of_branch(p, lo, hi, v)))
            case False{}:
              Vk.PSet.valid_branch(p, lo,
                S.PSet.add(p, hi, U32.shr(h), U32.sub(x, h),
                  U32.is_lt(U32.sub(x, h), U32.shr(h))), E.Bool.and_l(S.PSet.valid(p, lo, True{}),
                    S.PSet.valid(p, hi, True{}),
                    Vs3.PSet.both_of_branch(p, lo, hi, v)),
                PSet.valid_add(p, hi, U32.shr(h), U32.sub(x, h),
                  U32.is_lt(U32.sub(x, h), U32.shr(h)),
                  PSet.shr_half(p, h, eh, dok), {==},
                  Dc.Nat.gt_down(32n, 11n+p, dok),
                  PSet.high_fits(p, h, x, eh, dok, eb, inv), E.Bool.and_r(S.PSet.valid(p, lo, True{}),
                    S.PSet.valid(p, hi, True{}),
                    Vs3.PSet.both_of_branch(p, lo, hi, v))))

law PSet.valid_insert:
  for +d: Nat
  for +s: S.PSet
  for +x: U32
  for +dok: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +v: {S.PSet.valid(d, s, True{}) == True{} : Bool}
  {S.PSet.valid(d, S.PSet.insert(d, s, x), True{}) == True{} : Bool}

def PSet.valid_insert(d, s, x, dok, inv, v):
  PSet.valid_add(d, s, S.PSet.half(d), x,
    U32.is_lt(x, S.PSet.half(d)), {==}, {==}, dok, inv, v)

law PSet.valid_of_list:
  for +xs: List<&2, U32>
  for +d: Nat
  for +s: S.PSet
  for +dok: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +fits: {Sf.Ords.all_fit(xs, 12n+d) == True{} : Bool}
  for +v: {S.PSet.valid(d, s, True{}) == True{} : Bool}
  {S.PSet.valid(d, S.PSet.of_list(d, xs, s), True{}) == True{}
    : Bool}

def PSet.valid_of_list(xs, d, s, dok, fits, v):
  match xs:
    case Nil{}:
      v
    case Con{y, t}:
      PSet.valid_of_list(t, d, S.PSet.insert(d, s, y), dok,
        E.Bool.and_r(Dc.U32.hi_zero(y, 12n+d),
          Sf.Ords.all_fit(t, 12n+d), fits),
        PSet.valid_insert(d, s, y, dok,
          E.Bool.and_l(Dc.U32.hi_zero(y, 12n+d),
            Sf.Ords.all_fit(t, 12n+d), fits), v))

law PSet.valid_from_list:
  for +xs: List<&2, U32>
  for +d: Nat
  for +dok: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +fits: {Sf.Ords.all_fit(xs, 12n+d) == True{} : Bool}
  {S.PSet.valid(d, S.PSet.from_list(d, xs), True{}) == True{}
    : Bool}

def PSet.valid_from_list(xs, d, dok, fits):
  PSet.valid_of_list(xs, d, S.PZero{}, dok, fits,
    Vk.PSet.valid_zero(d))
