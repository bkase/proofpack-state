# proofs/subset.bend -- what a zero difference count says about membership.
#
# `PSet.is_subset` is the readiness test and the equality test the matrix
# deduplication uses, and it is a *count*: it asks whether the fused
# difference has no members, never whether a particular ordinal is in both
# sets. Three obligations wait on turning that count back into a statement
# about an ordinal -- C-01's leastness, C-03's subset-form properties, and
# Q-04's reuse of an answer between cells whose inventories compare equal.
#
# This file is the first step of that bridge: the sorted-list difference.
# `Ords.diff` walks two offset lists together, keeping a head of the left
# list when it is smaller than the head of the right and dropping both when
# they match. If the walk comes back empty, then every element of the left
# list was matched against something in the right -- and, notably, that
# argument needs no sortedness hypothesis at all. It needs only that the walk
# had enough fuel to finish, which `Ords.merge_fuel` guarantees by
# construction.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./ords.bend as PO
import ./only.bend as On
import ./bitset.bend as Bs
import ./shape.bend as Sh
import ./collapse.bend as Co
import ./enum.bend as En
import ./count.bend as Ct
import ./words.bend as PWo
import ./addr.bend as Ad
import ./inject.bend as Ij
import ./word.bend as PW
import ../core/word.bend as W
import ./walk.bend as Wk
import ./leaf.bend as Lf
import ./faithful.bend as Fa
import ./descend.bend as Dc
import ../core/set.bend as S
import ../core/words.bend as Wo
import ./insert.bend as Ins
import ../core/count.bend as C
import ../core/ords.bend as O

law List.cons_not_nil:
  for -A: Type
  for +x: U32
  for +t: List<&2, U32>
  for +e: {Con{x, t} == Nil{} : List<&2, U32>}
  A

def List.len_at(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

def List.cons_not_nil(A, x, t, e):
  E.Nat.noconf2(A, List.length(&2, U32, t),
    Equal.cong(List<&2, U32>, Nat, List.len_at, Con{x, t}, Nil{}, e))

law Nat.gt_peel:
  for +f: Nat
  for +m: Nat
  for +n: Nat
  for +ok: {C.Nat.gt(1n+f, Nat.add(1n+m, n)) == True{} : Bool}
  {C.Nat.gt(f, Nat.add(m, n)) == True{} : Bool}

def Nat.gt_peel(f, m, n, ok):
  ok

law Nat.gt_shift:
  for +f: Nat
  for +m: Nat
  for +n: Nat
  for +ok: {C.Nat.gt(f, Nat.add(m, 1n+n)) == True{} : Bool}
  {C.Nat.gt(f, Nat.add(1n+m, n)) == True{} : Bool}

def Nat.gt_shift(f, m, n, ok):
  %N.Nat.add_succ(m, n) : {C.Nat.gt(f, _) == True{} : Bool}
  ok

def Nat.gt_at(+f: Nat, i: Nat) -> Bool:
  C.Nat.gt(f, i)

law Nat.gt_drop:
  for +f: Nat
  for +m: Nat
  for +n: Nat
  for +ok: {C.Nat.gt(f, Nat.add(m, 1n+n)) == True{} : Bool}
  {C.Nat.gt(f, Nat.add(m, n)) == True{} : Bool}

def Nat.gt_drop(f, m, n, ok):
  Bs.Nat.gt.down(f, Nat.add(m, n),
    Equal.trans(Bool, C.Nat.gt(f, 1n+Nat.add(m, n)),
      C.Nat.gt(f, Nat.add(m, 1n+n)), True{},
      Equal.cong(Nat, Bool, Nat.gt_at(f), 1n+Nat.add(m, n),
        Nat.add(m, 1n+n),
        E.Nat.sym(Nat.add(m, 1n+n), 1n+Nat.add(m, n),
          N.Nat.add_succ(m, n))),
      ok))

law Ords.elem_cons:
  for +h: U32
  for +t: List<&2, U32>
  for +x: U32
  for +ok: {O.Ords.elem(t, x) == True{} : Bool}
  {O.Ords.elem(Con{h, t}, x) == True{} : Bool}

def Ords.elem_cons(h, t, x, ok):
  Ins.Ords.elem_go_mono(t, x, U32.is_eq(h, x), ok)

law Ords.diff_nil_elem:
  for +fuel: Nat
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +c: Cmp
  for +hx: Bool
  for +x: U32
  for +ec: {c == O.Ords.head_cmp(a, b) : Cmp}
  for +ehx: {hx == Ins.U32.head_eq(a, x) : Bool}
  for +fok: {C.Nat.gt(fuel, Nat.add(List.length(&2, U32, a),
    List.length(&2, U32, b))) == True{} : Bool}
  for +nil: {O.Ords.diff.go(fuel, a, b, c) == Nil{} : List<&2, U32>}
  for +ea: {O.Ords.elem(a, x) == True{} : Bool}
  {O.Ords.elem(b, x) == True{} : Bool}

# The head of the left list matched the head of the right, and the ordinal
# asked about is that head.
law Cmp.eq_is_eq:
  for +ah: U32
  for +bh: U32
  for +ec: {EQ{} == U32.cmp(ah, bh) : Cmp}
  {U32.is_eq(ah, bh) == True{} : Bool}

def Cmp.eq_is_eq(ah, bh, ec):
  %ec : {Cmp.is_eq(_) == True{} : Bool}
  {==}

law Ords.diff_eq_head:
  for +ah: U32
  for +bh: U32
  for +bt: List<&2, U32>
  for +x: U32
  for +ec: {EQ{} == U32.cmp(ah, bh) : Cmp}
  for +ehx: {True{} == U32.is_eq(ah, x) : Bool}
  {O.Ords.elem(Con{bh, bt}, x) == True{} : Bool}

def Ords.diff_eq_head(ah, bh, bt, x, ec, ehx):
  %E.U32.eq_reflect(ah, bh, Cmp.eq_is_eq(ah, bh, ec))
    : {O.Ords.elem(Con{_, bt}, x) == True{} : Bool}
  %ehx : {O.Ords.elem.go(bt, x, _) == True{} : Bool}
  PO.Ords.elem_go_found(bt, x)

# The head of the left list did not match, so the tail holds the ordinal.
law Ords.tail_elem:
  for +ah: U32
  for +at: List<&2, U32>
  for +x: U32
  for +ehx: {False{} == U32.is_eq(ah, x) : Bool}
  for +ea: {O.Ords.elem(Con{ah, at}, x) == True{} : Bool}
  {O.Ords.elem(at, x) == True{} : Bool}

def Ords.tail_elem(ah, at, x, ehx, ea):
  %E.Bool.sym(False{}, U32.is_eq(ah, x), ehx)
    : {O.Ords.elem.go(at, x, _) == True{} : Bool}
  ea

def Ords.diff_nil_elem(fuel, a, b, c, hx, x, ec, ehx, fok, nil, ea):
  match fuel:
    case 0n:
      E.Bool.noconf({O.Ords.elem(b, x) == True{} : Bool}, fok)
    case 1n+f:
      match a:
        case Nil{}:
          E.Bool.noconf({O.Ords.elem(b, x) == True{} : Bool}, ea)
        case Con{ah, at}:
          match b:
            case Nil{}:
              List.cons_not_nil({O.Ords.elem(Nil{}, x) == True{} : Bool},
                ah, at, nil)
            case Con{bh, bt}:
              match c:
                case LT{}:
                  List.cons_not_nil({O.Ords.elem(Con{bh, bt}, x)
                    == True{} : Bool}, ah,
                    O.Ords.diff.go(f, at, Con{bh, bt},
                      O.Ords.head_cmp(at, Con{bh, bt})), nil)
                case GT{}:
                  Ords.elem_cons(bh, bt, x,
                    Ords.diff_nil_elem(f, Con{ah, at}, bt,
                      O.Ords.head_cmp(Con{ah, at}, bt),
                      Ins.U32.head_eq(Con{ah, at}, x), x, {==}, {==},
                      Nat.gt_shift(f, List.length(&2, U32, at),
                        List.length(&2, U32, bt),
                        Nat.gt_peel(f, List.length(&2, U32, at),
                          1n+List.length(&2, U32, bt), fok)),
                      nil, ea))
                case EQ{}:
                  match hx:
                    case True{}:
                      Ords.diff_eq_head(ah, bh, bt, x, ec, ehx)
                    case False{}:
                      Ords.elem_cons(bh, bt, x,
                        Ords.diff_nil_elem(f, at, bt,
                          O.Ords.head_cmp(at, bt),
                          Ins.U32.head_eq(at, x), x, {==}, {==},
                          Nat.gt_drop(f, List.length(&2, U32, at),
                            List.length(&2, U32, bt),
                            Nat.gt_peel(f, List.length(&2, U32, at),
                              1n+List.length(&2, U32, bt), fok)),
                          nil,
                          Ords.tail_elem(ah, at, x, ehx, ea)))

law Nat.gt_succ_self:
  for +k: Nat
  {C.Nat.gt(1n+k, k) == True{} : Bool}

def Nat.gt_succ_self(k):
  match k:
    case 0n:
      {==}
    case 1n+j:
      Nat.gt_succ_self(j)

law Ords.diff_nil:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +x: U32
  for +nil: {O.Ords.diff(a, b) == Nil{} : List<&2, U32>}
  for +ea: {O.Ords.elem(a, x) == True{} : Bool}
  {O.Ords.elem(b, x) == True{} : Bool}

def Ords.diff_nil(a, b, x, nil, ea):
  Ords.diff_nil_elem(O.Ords.merge_fuel(a, b), a, b,
    O.Ords.head_cmp(a, b), Ins.U32.head_eq(a, x), x, {==}, {==},
    Nat.gt_succ_self(Nat.add(List.length(&2, U32, a),
      List.length(&2, U32, b))), nil, ea)

law List.nil_of_len:
  for +xs: List<&2, U32>
  for +z: {List.length(&2, U32, xs) == 0n : Nat}
  {xs == Nil{} : List<&2, U32>}

def List.nil_of_len(xs, z):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      E.Nat.noconf2({Con{h, t} == Nil{} : List<&2, U32>},
        List.length(&2, U32, t), z)

# ---------------------------------------------------------------------------
# The full leaf's members, as a tile.
#
# `PSet.range(4096n, 4095, Nil{})` and the members of a 128-word tile of ones
# are the same closed list -- 0 through 4095, ascending -- so the one the
# fused difference walks against a sparse leaf is the one the tile laws
# already describe. Both sides are closed terms, so this is a computation.
# ---------------------------------------------------------------------------

law Ords.full_range_is_ones:
  {S.PSet.range(4096n, 4095, Nil{})
    == Wo.Words.members(Wo.Words.ones(128n), 0) : List<&2, U32>}

def Ords.full_range_is_ones():
  {==}

law Ords.elem_full_range:
  for +x: U32
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {O.Ords.elem(S.PSet.range(4096n, 4095, Nil{}), x) == True{} : Bool}

law Ords.elem_members_of_bit:
  for +ws: List<&2, U32>
  for +x: U32
  for +wide: {List.length(&2, U32, ws) == 128n : Nat}
  for +bit: {Wo.Words.bit(ws, x) == True{} : Bool}
  {O.Ords.elem(Wo.Words.members(ws, 0), x) == True{} : Bool}

def Ords.elem_members_of_bit(ws, x, wide, bit):
  %E.Bool.sym(O.Ords.elem(Wo.Words.members(ws, 0), x),
    En.Words.holds(ws, 0, x), En.Words.elem_members(ws, x))
    : {_ == True{} : Bool}
  %E.Bool.sym(En.Words.holds(ws, 0, x), Wo.Words.bit(ws, x),
    Wk.Words.holds_bit(ws, x, wide))
    : {_ == True{} : Bool}
  bit

def Ords.elem_full_range(x, inr):
  %E.List.sym(U32, S.PSet.range(4096n, 4095, Nil{}),
    Wo.Words.members(Wo.Words.ones(128n), 0), Ords.full_range_is_ones())
    : {O.Ords.elem(_, x) == True{} : Bool}
  Ords.elem_members_of_bit(Wo.Words.ones(128n), x,
    Lf.Words.length_ones(128n), Fa.PSet.bit_ones_in_range(x, inr))

# ---------------------------------------------------------------------------
# A leaf. Every arm of the fused count is one of four things: a word count, a
# fused word-difference count, the length of a sorted-list difference, or a
# constant. The first three all say the same thing about an ordinal when they
# are zero, and the constants are absurd.
# ---------------------------------------------------------------------------

def Ords.elem_at(+x: U32, l: List<&2, U32>) -> Bool:
  O.Ords.elem(l, x)

law Ords.empty_absurd:
  for +ao: List<&2, U32>
  for +x: U32
  for +z: {List.length(&2, U32, ao) == 0n : Nat}
  for +ma: {O.Ords.elem(ao, x) == True{} : Bool}
  {False{} == True{} : Bool}

def Ords.empty_absurd(ao, x, z, ma):
  Equal.trans(Bool, False{}, O.Ords.elem(ao, x), True{},
    E.Bool.sym(O.Ords.elem(ao, x), False{},
      Equal.cong(List<&2, U32>, Bool, Ords.elem_at(x), ao, Nil{},
        List.nil_of_len(ao, z))),
    ma)

law Words.count_zero_absurd:
  for +aw: List<&2, U32>
  for +x: U32
  for +z: {Wo.Words.count(aw) == 0n : Nat}
  for +ma: {Wo.Words.bit(aw, x) == True{} : Bool}
  {False{} == True{} : Bool}

def Words.count_zero_absurd(aw, x, z, ma):
  Equal.trans(Bool, False{}, Wo.Words.bit(aw, x), True{},
    E.Bool.sym(Wo.Words.bit(aw, x), False{},
      Ct.Words.count_zero(aw, z, U32.to_nat(U32.shrn(x, 5n)),
        U32.to_nat(U32.and(x, 31)), Ad.U32.low_five_bound(x))),
    ma)

# Two tiles, through the fused count.
law Words.diff_count_bit:
  for +aw: List<&2, U32>
  for +bw: List<&2, U32>
  for +x: U32
  for +z: {Wo.Words.diff_count(aw, bw) == 0n : Nat}
  for +ma: {Wo.Words.bit(aw, x) == True{} : Bool}
  {Wo.Words.bit(bw, x) == True{} : Bool}

# `and(p, not(q)) == False` with `p` true forces `q`.
law Bool.of_and_false:
  for +p: Bool
  for +q: Bool
  for +e: {Bool.and(p, Bool.not(q)) == False{} : Bool}
  for +ep: {p == True{} : Bool}
  {q == True{} : Bool}

def Bool.of_and_false(p, q, e, ep):
  match p:
    case False{}:
      E.Bool.noconf({q == True{} : Bool}, ep)
    case True{}:
      match q:
        case True{}:
          {==}
        case False{}:
          E.Bool.noconf.r({False{} == True{} : Bool}, e)

def Words.diff_count_bit(aw, bw, x, z, ma):
  Bool.of_and_false(Wo.Words.bit(aw, x), Wo.Words.bit(bw, x),
    Equal.trans(Bool,
      Bool.and(Wo.Words.bit(aw, x), Bool.not(Wo.Words.bit(bw, x))),
      Wo.Words.bit(Wo.Words.diff(aw, bw), x), False{},
      E.Bool.sym(Wo.Words.bit(Wo.Words.diff(aw, bw), x),
        Bool.and(Wo.Words.bit(aw, x), Bool.not(Wo.Words.bit(bw, x))),
        PWo.Words.at_diff(aw, bw, U32.to_nat(U32.shrn(x, 5n)),
          U32.to_nat(U32.and(x, 31)))),
      Ct.Words.count_zero(Wo.Words.diff(aw, bw),
        Equal.trans(Nat, Wo.Words.count(Wo.Words.diff(aw, bw)),
          Wo.Words.diff_count(aw, bw), 0n,
          E.Nat.sym(Wo.Words.diff_count(aw, bw),
            Wo.Words.count(Wo.Words.diff(aw, bw)),
            PWo.Words.diff_count_spec(aw, bw)),
          z),
        U32.to_nat(U32.shrn(x, 5n)), U32.to_nat(U32.and(x, 31)),
        Ad.U32.low_five_bound(x))),
    ma)

law Words.bit_of_elem_members:
  for +ws: List<&2, U32>
  for +x: U32
  for +wide: {List.length(&2, U32, ws) == 128n : Nat}
  for +e: {O.Ords.elem(Wo.Words.members(ws, 0), x) == True{} : Bool}
  {Wo.Words.bit(ws, x) == True{} : Bool}

def Words.bit_of_elem_members(ws, x, wide, e):
  Equal.trans(Bool, Wo.Words.bit(ws, x), En.Words.holds(ws, 0, x), True{},
    E.Bool.sym(En.Words.holds(ws, 0, x), Wo.Words.bit(ws, x),
      Wk.Words.holds_bit(ws, x, wide)),
    Equal.trans(Bool, En.Words.holds(ws, 0, x),
      O.Ords.elem(Wo.Words.members(ws, 0), x), True{},
      E.Bool.sym(O.Ords.elem(Wo.Words.members(ws, 0), x),
        En.Words.holds(ws, 0, x), En.Words.elem_members(ws, x)),
      e))

law PSet.leaf_subset_member:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  for +va: {Sh.PSet.wf.leaf(a) == True{} : Bool}
  for +vb: {Sh.PSet.wf.leaf(b) == True{} : Bool}
  for +z: {S.PSet.leaf_diff_count(a, b) == 0n : Nat}
  for +ma: {S.PSet.mem.leaf(a, x) == True{} : Bool}
  {S.PSet.mem.leaf(b, x) == True{} : Bool}

def PSet.leaf_subset_member(a, b, x, inr, va, vb, z, ma):
  match a:
    case S.PZero{}:
      E.Bool.noconf({S.PSet.mem.leaf(b, x) == True{} : Bool}, ma)
    case S.PBranch{l, h}:
      E.Bool.noconf({S.PSet.mem.leaf(b, x) == True{} : Bool}, ma)
    case S.PSparse{ao}:
      match b:
        case S.PFull{}:
          {==}
        case S.PZero{}:
          E.Bool.noconf({S.PSet.mem.leaf(S.PZero{}, x) == True{} : Bool},
            Ords.empty_absurd(ao, x, z, ma))
        case S.PBranch{l, h}:
          E.Bool.noconf({S.PSet.mem.leaf(S.PBranch{l, h}, x)
            == True{} : Bool}, Ords.empty_absurd(ao, x, z, ma))
        case S.PSparse{bo}:
          Ords.diff_nil(ao, bo, x, List.nil_of_len(O.Ords.diff(ao, bo), z),
            ma)
        case S.PDense{bw}:
          Words.bit_of_elem_members(bw, x,
            Sh.PSet.wf_leaf_words_width(S.PDense{bw}, vb),
            Ords.diff_nil(ao, Wo.Words.members(bw, 0), x,
              List.nil_of_len(
                O.Ords.diff(ao, Wo.Words.members(bw, 0)), z), ma))
    case S.PDense{aw}:
      match b:
        case S.PFull{}:
          {==}
        case S.PZero{}:
          E.Bool.noconf({S.PSet.mem.leaf(S.PZero{}, x) == True{} : Bool},
            Words.count_zero_absurd(aw, x, z, ma))
        case S.PBranch{l, h}:
          E.Bool.noconf({S.PSet.mem.leaf(S.PBranch{l, h}, x)
            == True{} : Bool}, Words.count_zero_absurd(aw, x, z, ma))
        case S.PDense{bw}:
          Words.diff_count_bit(aw, bw, x, z, ma)
        case S.PSparse{bo}:
          Ords.diff_nil(Wo.Words.members(aw, 0), bo, x,
            List.nil_of_len(
              O.Ords.diff(Wo.Words.members(aw, 0), bo), z),
            Ords.elem_members_of_bit(aw, x,
              Sh.PSet.wf_leaf_words_width(S.PDense{aw}, va), ma))
    case S.PFull{}:
      match b:
        case S.PFull{}:
          {==}
        case S.PZero{}:
          E.Nat.noconf2({S.PSet.mem.leaf(S.PZero{}, x) == True{} : Bool},
            4095n, z)
        case S.PBranch{l, h}:
          E.Nat.noconf2({S.PSet.mem.leaf(S.PBranch{l, h}, x)
            == True{} : Bool}, 4095n, z)
        case S.PDense{bw}:
          Words.diff_count_bit(Wo.Words.ones(128n), bw, x, z,
            Fa.PSet.bit_ones_in_range(x, inr))
        case S.PSparse{bo}:
          Ords.diff_nil(S.PSet.range(4096n, 4095, Nil{}), bo, x,
            List.nil_of_len(
              O.Ords.diff(S.PSet.range(4096n, 4095, Nil{}), bo), z),
            Ords.elem_full_range(x, inr))

# ---------------------------------------------------------------------------
# A half-width is never zero, which is what makes a `PFull` node's count
# non-zero and so rules out the arms that would otherwise be open.
# ---------------------------------------------------------------------------

law U32.shln_one_not_zero:
  for +k: Nat
  for +kok: {C.Nat.gt(32n, k) == True{} : Bool}
  for +e: {U32.shln(1, k) == 0 : U32}
  {False{} == True{} : Bool}

def U32.bit_at(+k: Nat, w: U32) -> Bool:
  W.U32.bit(w, k)

def U32.shln_one_not_zero(k, kok, e):
  Equal.trans(Bool, False{}, W.U32.bit(0, k), True{},
    E.Bool.sym(W.U32.bit(0, k), False{}, PW.U32.bit_zero(k)),
    Equal.trans(Bool, W.U32.bit(0, k), W.U32.bit(U32.shln(1, k), k),
      True{},
      E.Bool.sym(W.U32.bit(U32.shln(1, k), k), W.U32.bit(0, k),
        Equal.cong(U32, Bool, U32.bit_at(k), U32.shln(1, k), 0, e)),
      Bs.U32.bit_shln_one(k, kok)))

law U32.half_not_zero:
  for +h: U32
  for +k: Nat
  for +eh: {h == U32.shln(1, k) : U32}
  for +kok: {C.Nat.gt(32n, k) == True{} : Bool}
  for +z: {Nat.add(U32.to_nat(h), U32.to_nat(h)) == 0n : Nat}
  {False{} == True{} : Bool}

def U32.half_not_zero(h, k, eh, kok, z):
  U32.shln_one_not_zero(k, kok,
    Equal.trans(U32, U32.shln(1, k), h, 0,
      E.U32.sym(h, U32.shln(1, k), eh),
      Ij.U32.to_nat_inj(h, 0,
        Ct.Nat.add_zero_left(U32.to_nat(h), U32.to_nat(h), z))))

# ---------------------------------------------------------------------------
# A set whose count is zero has no members.
# ---------------------------------------------------------------------------

law PSet.count_zero_leaf:
  for +s: S.PSet
  for +x: U32
  for +z: {S.PSet.count.leaf(s) == 0n : Nat}
  {S.PSet.mem.leaf(s, x) == False{} : Bool}

def PSet.count_zero_leaf(s, x, z):
  match s:
    case S.PZero{}:
      {==}
    case S.PBranch{l, h}:
      {==}
    case S.PFull{}:
      E.Nat.noconf2({S.PSet.mem.leaf(S.PFull{}, x) == False{} : Bool},
        4095n, z)
    case S.PSparse{offs}:
      Equal.cong(List<&2, U32>, Bool, Ords.elem_at(x), offs, Nil{},
        List.nil_of_len(offs, z))
    case S.PDense{ws}:
      Ct.Words.count_zero(ws, z, U32.to_nat(U32.shrn(x, 5n)),
        U32.to_nat(U32.and(x, 31)), Ad.U32.low_five_bound(x))

law PSet.count_zero_mem:
  for +d: Nat
  for +s: S.PSet
  for +bx: Bool
  for +h: U32
  for +x: U32
  for +eh: {h == U32.shln(1, 11n+d) : U32}
  for +dok: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +ebx: {bx == U32.is_lt(x, h) : Bool}
  for +v: {Sh.PSet.wf(d, s, True{}) == True{} : Bool}
  for +z: {S.PSet.count(d, s, h) == 0n : Nat}
  {S.PSet.mem(d, s, h, x) == False{} : Bool}

def PSet.count_zero_mem(d, s, bx, h, x, eh, dok, ebx, v, z):
  match d:
    case 0n:
      PSet.count_zero_leaf(s, x, z)
    case 1n+p:
      match s:
        case S.PZero{}:
          {==}
        case S.PSparse{o}:
          E.Bool.noconf({S.PSet.mem(1n+p, S.PSparse{o}, h, x)
            == False{} : Bool}, v)
        case S.PDense{w}:
          E.Bool.noconf({S.PSet.mem(1n+p, S.PDense{w}, h, x)
            == False{} : Bool}, v)
        case S.PFull{}:
          E.Bool.noconf({S.PSet.mem(1n+p, S.PFull{}, h, x)
            == False{} : Bool},
            U32.half_not_zero(h, 11n+(1n+p), eh, dok, z))
        case S.PBranch{lo, hi}:
          match bx:
            case True{}:
              %ebx : {S.PSet.mem(p, S.PSet.pick(_, lo, hi), U32.shr(h),
                  S.PSet.rebase(_, h, x)) == False{} : Bool}
              PSet.count_zero_mem(p, lo, U32.is_lt(x, U32.shr(h)),
                U32.shr(h), x, Lf.PSet.half_shr(p, h, eh, dok),
                Dc.Nat.gt_down(32n, 11n+p, dok), {==},
                Sh.PSet.wf_lo(p, lo, hi, v),
                Ct.Nat.add_zero_left(S.PSet.count(p, lo, U32.shr(h)),
                  S.PSet.count(p, hi, U32.shr(h)), z))
            case False{}:
              %ebx : {S.PSet.mem(p, S.PSet.pick(_, lo, hi), U32.shr(h),
                  S.PSet.rebase(_, h, x)) == False{} : Bool}
              PSet.count_zero_mem(p, hi,
                U32.is_lt(U32.sub(x, h), U32.shr(h)),
                U32.shr(h), U32.sub(x, h),
                Lf.PSet.half_shr(p, h, eh, dok),
                Dc.Nat.gt_down(32n, 11n+p, dok), {==},
                Sh.PSet.wf_hi(p, lo, hi, v),
                Ct.Nat.add_zero_right(S.PSet.count(p, lo, U32.shr(h)),
                  S.PSet.count(p, hi, U32.shr(h)), z))

# ---------------------------------------------------------------------------
# The tree. A node's fused count is the sum of its halves, so a zero count
# is a zero count in both halves, and the ordinal asked about is in one of
# them.
# ---------------------------------------------------------------------------

law PSet.subset_mem:
  for +d: Nat
  for +a: S.PSet
  for +b: S.PSet
  for +bx: Bool
  for +h: U32
  for +x: U32
  for +eh: {h == U32.shln(1, 11n+d) : U32}
  for +dok: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +ebx: {bx == U32.is_lt(x, h) : Bool}
  for +va: {Sh.PSet.wf(d, a, True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(d, b, True{}) == True{} : Bool}
  for +z: {S.PSet.diff_count(d, a, b, h) == 0n : Nat}
  for +ma: {S.PSet.mem(d, a, h, x) == True{} : Bool}
  {S.PSet.mem(d, b, h, x) == True{} : Bool}

def PSet.subset_mem(d, a, b, bx, h, x, eh, dok, inv, ebx, va, vb, z, ma):
  match d:
    case 0n:
      PSet.leaf_subset_member(a, b, x, inv, va, vb, z, ma)
    case 1n+p:
      match a:
        case S.PZero{}:
          E.Bool.noconf({S.PSet.mem(1n+p, b, h, x) == True{} : Bool}, ma)
        case S.PSparse{o}:
          E.Bool.noconf({S.PSet.mem(1n+p, b, h, x) == True{} : Bool}, va)
        case S.PDense{w}:
          E.Bool.noconf({S.PSet.mem(1n+p, b, h, x) == True{} : Bool}, va)
        case S.PFull{}:
          match b:
            case S.PFull{}:
              {==}
            case S.PZero{}:
              E.Bool.noconf({S.PSet.mem(1n+p, S.PZero{}, h, x)
                == True{} : Bool},
                U32.half_not_zero(h, 11n+(1n+p), eh, dok, z))
            case S.PSparse{o}:
              E.Bool.noconf({S.PSet.mem(1n+p, S.PSparse{o}, h, x)
                == True{} : Bool}, vb)
            case S.PDense{w}:
              E.Bool.noconf({S.PSet.mem(1n+p, S.PDense{w}, h, x)
                == True{} : Bool}, vb)
            case S.PBranch{bl, bh}:
              match bx:
                case True{}:
                  %ebx : {S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                      U32.shr(h), S.PSet.rebase(_, h, x))
                    == True{} : Bool}
                  PSet.subset_mem(p, S.PFull{}, bl,
                    U32.is_lt(x, U32.shr(h)), U32.shr(h), x,
                    Lf.PSet.half_shr(p, h, eh, dok),
                    Dc.Nat.gt_down(32n, 11n+p, dok),
                    Lf.PSet.range_lo(p, h, x, eh, dok, ebx), {==},
                    Sh.PSet.wf_full(p), Sh.PSet.wf_lo(p, bl, bh, vb),
                    Ct.Nat.add_zero_left(
                      S.PSet.diff_count(p, S.PFull{}, bl, U32.shr(h)),
                      S.PSet.diff_count(p, S.PFull{}, bh, U32.shr(h)), z),
                    Co.PSet.mem_full(p, U32.shr(h), x))
                case False{}:
                  %ebx : {S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                      U32.shr(h), S.PSet.rebase(_, h, x))
                    == True{} : Bool}
                  PSet.subset_mem(p, S.PFull{}, bh,
                    U32.is_lt(U32.sub(x, h), U32.shr(h)), U32.shr(h),
                    U32.sub(x, h), Lf.PSet.half_shr(p, h, eh, dok),
                    Dc.Nat.gt_down(32n, 11n+p, dok),
                    Lf.PSet.range_hi(p, h, x, eh, dok, ebx, inv), {==},
                    Sh.PSet.wf_full(p), Sh.PSet.wf_hi(p, bl, bh, vb),
                    Ct.Nat.add_zero_right(
                      S.PSet.diff_count(p, S.PFull{}, bl, U32.shr(h)),
                      S.PSet.diff_count(p, S.PFull{}, bh, U32.shr(h)), z),
                    Co.PSet.mem_full(p, U32.shr(h), U32.sub(x, h)))
        case S.PBranch{al, ah}:
          match b:
            case S.PFull{}:
              {==}
            case S.PSparse{o}:
              E.Bool.noconf({S.PSet.mem(1n+p, S.PSparse{o}, h, x)
                == True{} : Bool}, vb)
            case S.PDense{w}:
              E.Bool.noconf({S.PSet.mem(1n+p, S.PDense{w}, h, x)
                == True{} : Bool}, vb)
            case S.PZero{}:
              match bx:
                case True{}:
                  E.Bool.noconf({S.PSet.mem(1n+p, S.PZero{}, h, x)
                    == True{} : Bool},
                    Equal.trans(Bool, False{},
                      S.PSet.mem(p, al, U32.shr(h), x), True{},
                      E.Bool.sym(S.PSet.mem(p, al, U32.shr(h), x),
                        False{},
                        PSet.count_zero_mem(p, al,
                          U32.is_lt(x, U32.shr(h)), U32.shr(h), x,
                          Lf.PSet.half_shr(p, h, eh, dok),
                          Dc.Nat.gt_down(32n, 11n+p, dok), {==},
                          Sh.PSet.wf_lo(p, al, ah, va),
                          Ct.Nat.add_zero_left(
                            S.PSet.count(p, al, U32.shr(h)),
                            S.PSet.count(p, ah, U32.shr(h)), z))),
                      Ins.PSet.mem_lo(p, al, ah, h, x, ebx, ma)))
                case False{}:
                  E.Bool.noconf({S.PSet.mem(1n+p, S.PZero{}, h, x)
                    == True{} : Bool},
                    Equal.trans(Bool, False{},
                      S.PSet.mem(p, ah, U32.shr(h), U32.sub(x, h)),
                      True{},
                      E.Bool.sym(
                        S.PSet.mem(p, ah, U32.shr(h), U32.sub(x, h)),
                        False{},
                        PSet.count_zero_mem(p, ah,
                          U32.is_lt(U32.sub(x, h), U32.shr(h)),
                          U32.shr(h), U32.sub(x, h),
                          Lf.PSet.half_shr(p, h, eh, dok),
                          Dc.Nat.gt_down(32n, 11n+p, dok), {==},
                          Sh.PSet.wf_hi(p, al, ah, va),
                          Ct.Nat.add_zero_right(
                            S.PSet.count(p, al, U32.shr(h)),
                            S.PSet.count(p, ah, U32.shr(h)), z))),
                      Ins.PSet.mem_hi(p, al, ah, h, x, ebx, ma)))
            case S.PBranch{bl, bh}:
              match bx:
                case True{}:
                  %ebx : {S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                      U32.shr(h), S.PSet.rebase(_, h, x))
                    == True{} : Bool}
                  PSet.subset_mem(p, al, bl, U32.is_lt(x, U32.shr(h)),
                    U32.shr(h), x, Lf.PSet.half_shr(p, h, eh, dok),
                    Dc.Nat.gt_down(32n, 11n+p, dok),
                    Lf.PSet.range_lo(p, h, x, eh, dok, ebx), {==},
                    Sh.PSet.wf_lo(p, al, ah, va),
                    Sh.PSet.wf_lo(p, bl, bh, vb),
                    Ct.Nat.add_zero_left(
                      S.PSet.diff_count(p, al, bl, U32.shr(h)),
                      S.PSet.diff_count(p, ah, bh, U32.shr(h)), z),
                    Ins.PSet.mem_lo(p, al, ah, h, x, ebx, ma))
                case False{}:
                  %ebx : {S.PSet.mem(p, S.PSet.pick(_, bl, bh),
                      U32.shr(h), S.PSet.rebase(_, h, x))
                    == True{} : Bool}
                  PSet.subset_mem(p, ah, bh,
                    U32.is_lt(U32.sub(x, h), U32.shr(h)), U32.shr(h),
                    U32.sub(x, h), Lf.PSet.half_shr(p, h, eh, dok),
                    Dc.Nat.gt_down(32n, 11n+p, dok),
                    Lf.PSet.range_hi(p, h, x, eh, dok, ebx, inv), {==},
                    Sh.PSet.wf_hi(p, al, ah, va),
                    Sh.PSet.wf_hi(p, bl, bh, vb),
                    Ct.Nat.add_zero_right(
                      S.PSet.diff_count(p, al, bl, U32.shr(h)),
                      S.PSet.diff_count(p, ah, bh, U32.shr(h)), z),
                    Ins.PSet.mem_hi(p, al, ah, h, x, ebx, ma))

# At the depth the product runs at, where every `U32` is in range.
law PSet.is_subset_member:
  for +a: S.PSet
  for +b: S.PSet
  for +x: U32
  for +va: {Sh.PSet.wf(20n, a, True{}) == True{} : Bool}
  for +vb: {Sh.PSet.wf(20n, b, True{}) == True{} : Bool}
  for +sub: {S.PSet.is_subset(20n, a, b) == True{} : Bool}
  for +ma: {S.PSet.member(20n, a, x) == True{} : Bool}
  {S.PSet.member(20n, b, x) == True{} : Bool}

def PSet.is_subset_member(a, b, x, va, vb, sub, ma):
  PSet.subset_mem(20n, a, b, U32.is_lt(x, S.PSet.half(20n)),
    S.PSet.half(20n), x, {==}, {==}, Dc.U32.hi_zero_full(x), {==},
    va, vb,
    Lf.Nat.is_eq_reflect(S.PSet.missing_count(20n, a, b), 0n, sub), ma)
