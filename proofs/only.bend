# proofs/only.bend -- inserting adds nothing but the ordinal inserted.
#
# `inserting_adds_exactly_that_ordinal` and `inserting_keeps_every_member`
# are the two directions that say insertion does not lose. This is the third:
# it does not gain either. An ordinal present after an insert was either the
# one inserted or present before.
#
# It is what G-03's converse reduces to. A receiver's inventory is projected
# by folding insertion over the ordinals the identity table named, so "the
# projection contains nothing the report did not mention" is exactly this law
# applied along the fold.
#
# Three places do the work, the same three the other direction needed: a
# sparse leaf's ordered offset list, a dense leaf's bit set, and the descent.
# The bit set is where the addressing arithmetic finally earns its keep --
# setting the bit of `y` changes the word `y >> 5` at position `y & 31` and
# nothing else, so a bit that reads set afterwards and was not set before is
# at that word and that position, and the tile address being injective
# (`the_tile_address_is_injective`) turns that back into `x = y`.

import Base
import ./eq.bend as E
import ./ords.bend as PO
import ./word.bend as PW
import ./bits.bend as PB
import ./addr.bend as PA
import ./leaf.bend as Lf
import ./split.bend as Sp
import ./missing.bend as M
import ./shape.bend as Sh
import ./insert.bend as Ins
import ./preserve.bend as Pr
import ./bridge.bend as Br
import ./faithful.bend as Fa
import ./descend.bend as Dc
import ../core/set.bend as S
import ../core/words.bend as Wo
import ../core/count.bend as C
import ../core/word.bend as W
import ./bitset.bend as Bs
import ../core/ords.bend as O

law Bool.or_true_r:
  for +c: Bool
  {Bool.or(c, True{}) == True{} : Bool}

def Bool.or_true_r(c):
  match c:
    case False{}:
      {==}
    case True{}:
      {==}

law Bool.or_of_go:
  for +e: Bool
  for +l: List<&2, U32>
  for +x: U32
  for +ok: {O.Ords.elem.go(l, x, e) == True{} : Bool}
  {Bool.or(e, O.Ords.elem.go(l, x, False{})) == True{} : Bool}

def Bool.or_of_go(e, l, x, ok):
  match e:
    case True{}:
      {==}
    case False{}:
      ok

law Ords.insert_go_only:
  for +xs: List<&2, U32>
  for +acc: Bool
  for +y: U32
  for +c: Cmp
  for +x: U32
  for +ok: {O.Ords.elem.go(O.Ords.insert.go(xs, y, c), x, acc)
    == True{} : Bool}
  {Bool.or(U32.is_eq(y, x), O.Ords.elem.go(xs, x, acc)) == True{} : Bool}

def Ords.insert_go_only(xs, acc, y, c, x, ok):
  match xs:
    case Nil{}:
      match acc:
        case True{}:
          Bool.or_true_r(U32.is_eq(y, x))
        case False{}:
          %E.Bool.sym(U32.is_eq(y, x), True{}, ok)
            : {Bool.or(_, False{}) == True{} : Bool}
          {==}
    case Con{h, t}:
      match acc:
        case True{}:
          Bool.or_true_r(U32.is_eq(y, x))
        case False{}:
          match c:
            case EQ{}:
              %E.Bool.sym(O.Ords.elem.go(Con{h, t}, x, False{}), True{}, ok)
                : {Bool.or(U32.is_eq(y, x), _) == True{} : Bool}
              Bool.or_true_r(U32.is_eq(y, x))
            case GT{}:
              Bool.or_of_go(U32.is_eq(y, x), Con{h, t}, x, ok)
            case LT{}:
              Ords.insert_go_only(t, U32.is_eq(h, x), y,
                O.Ords.head_one(t, y), x, ok)

law Ords.elem_insert_only:
  for +xs: List<&2, U32>
  for +y: U32
  for +x: U32
  for +ok: {O.Ords.elem(O.Ords.insert(xs, y), x) == True{} : Bool}
  {Bool.or(U32.is_eq(y, x), O.Ords.elem(xs, x)) == True{} : Bool}

def Ords.elem_insert_only(xs, y, x, ok):
  Ords.insert_go_only(xs, False{}, y, O.Ords.head_one(xs, y), x, ok)

# ---------------------------------------------------------------------------
# One word. The mask `1 << b` has bit `b` set and no other, which is the
# half of the bit-set law the other direction never needed: `bitset.bend`
# proves the diagonal, and this is the rest of the row.
# ---------------------------------------------------------------------------

law U32.bit_shl_zero:
  for +a: U32
  {W.U32.bit(U32.shl(a), 0n) == False{} : Bool}

def U32.bit_shl_zero(a):
  match a:
    case U32{w}:
      match w:
        case WCon{b, t}:
          {==}

law U32.bit_mask_one:
  for +b: Nat
  for +c: Nat
  for +bok: {C.Nat.gt(32n, b) == True{} : Bool}
  for +cok: {C.Nat.gt(32n, c) == True{} : Bool}
  {W.U32.bit(U32.shln(1, b), c) == Nat.is_eq(b, c) : Bool}

def U32.bit_mask_one(b, c, bok, cok):
  match b:
    case 0n:
      match c:
        case 0n:
          {==}
        case 1n+j:
          PW.Word.get_zero(31n, j)
    case 1n+i:
      match c:
        case 0n:
          U32.bit_shl_zero(U32.shln(1, i))
        case 1n+j:
          %E.Bool.sym(W.U32.bit(U32.shl(U32.shln(1, i)), 1n+j),
            W.U32.bit(U32.shln(1, i), j),
            Bs.U32.bit_shl(U32.shln(1, i), j, cok))
            : {_ == Nat.is_eq(i, j) : Bool}
          U32.bit_mask_one(i, j, Bs.Nat.gt.down(32n, i, bok),
            Bs.Nat.gt.down(32n, j, cok))

law U32.test_set_only:
  for +w: U32
  for +b: Nat
  for +c: Nat
  for +bok: {C.Nat.gt(32n, b) == True{} : Bool}
  for +cok: {C.Nat.gt(32n, c) == True{} : Bool}
  {Wo.U32.test(U32.or(w, U32.shln(1, b)), c)
    == Bool.or(Wo.U32.test(w, c), Nat.is_eq(b, c)) : Bool}

def U32.test_set_only(w, b, c, bok, cok):
  %E.Bool.sym(Wo.U32.test(U32.or(w, U32.shln(1, b)), c),
    W.U32.bit(U32.or(w, U32.shln(1, b)), c),
    PB.U32.test_spec(U32.or(w, U32.shln(1, b)), c))
    : {_ == Bool.or(Wo.U32.test(w, c), Nat.is_eq(b, c)) : Bool}
  %E.Bool.sym(W.U32.bit(U32.or(w, U32.shln(1, b)), c),
    Bool.or(W.U32.bit(w, c), W.U32.bit(U32.shln(1, b), c)),
    PW.U32.bit_or(w, U32.shln(1, b), c))
    : {_ == Bool.or(Wo.U32.test(w, c), Nat.is_eq(b, c)) : Bool}
  %E.Bool.sym(W.U32.bit(U32.shln(1, b), c), Nat.is_eq(b, c),
    U32.bit_mask_one(b, c, bok, cok))
    : {Bool.or(W.U32.bit(w, c), _)
      == Bool.or(Wo.U32.test(w, c), Nat.is_eq(b, c)) : Bool}
  %PB.U32.test_spec(w, c)
    : {Bool.or(_, Nat.is_eq(b, c))
      == Bool.or(Wo.U32.test(w, c), Nat.is_eq(b, c)) : Bool}
  {==}

# ---------------------------------------------------------------------------
# The tile. Setting position (i, b) changes position (j, c) only when they
# are the same position.
# ---------------------------------------------------------------------------

law Bool.or_comm_true:
  for +p: Bool
  for +q: Bool
  for +ok: {Bool.or(p, q) == True{} : Bool}
  {Bool.or(q, p) == True{} : Bool}

def Bool.or_comm_true(p, q, ok):
  match p:
    case True{}:
      match q:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match q:
        case True{}:
          {==}
        case False{}:
          ok

law Words.at_set_at_only:
  for +ws: List<&2, U32>
  for +i: Nat
  for +j: Nat
  for +b: Nat
  for +c: Nat
  for +bok: {C.Nat.gt(32n, b) == True{} : Bool}
  for +cok: {C.Nat.gt(32n, c) == True{} : Bool}
  for +ok: {Wo.Words.at(Wo.Words.set.at(ws, i, b), j, c) == True{} : Bool}
  {Bool.or(Bool.and(Nat.is_eq(i, j), Nat.is_eq(b, c)),
    Wo.Words.at(ws, j, c)) == True{} : Bool}

def Words.at_set_at_only(ws, i, j, b, c, bok, cok, ok):
  match ws:
    case Nil{}:
      E.Bool.noconf({Bool.or(Bool.and(Nat.is_eq(i, j), Nat.is_eq(b, c)),
        Wo.Words.at(Nil{}, j, c)) == True{} : Bool}, ok)
    case Con{w, t}:
      match i:
        case 0n:
          match j:
            case 0n:
              Bool.or_comm_true(Wo.U32.test(w, c), Nat.is_eq(b, c),
                Equal.trans(Bool,
                  Bool.or(Wo.U32.test(w, c), Nat.is_eq(b, c)),
                  Wo.U32.test(U32.or(w, U32.shln(1, b)), c), True{},
                  E.Bool.sym(Wo.U32.test(U32.or(w, U32.shln(1, b)), c),
                    Bool.or(Wo.U32.test(w, c), Nat.is_eq(b, c)),
                    U32.test_set_only(w, b, c, bok, cok)),
                  ok))
            case 1n+jj:
              ok
        case 1n+ii:
          match j:
            case 0n:
              ok
            case 1n+jj:
              Words.at_set_at_only(t, ii, jj, b, c, bok, cok, ok)

law Bool.or_lift:
  for +a: Bool
  for +a2: Bool
  for +b: Bool
  for +ok: {Bool.or(a, b) == True{} : Bool}
  for +h: {M.Bool.imp(a, a2) == True{} : Bool}
  {Bool.or(a2, b) == True{} : Bool}

def Bool.or_lift(a, a2, b, ok, h):
  match a:
    case True{}:
      match a2:
        case True{}:
          {==}
        case False{}:
          E.Bool.noconf({Bool.or(False{}, b) == True{} : Bool}, h)
    case False{}:
      match a2:
        case True{}:
          {==}
        case False{}:
          ok

law Addr.imp_eq:
  for +y: U32
  for +x: U32
  for +a: Bool
  for +ea: {a == Bool.and(
      Nat.is_eq(U32.to_nat(U32.shrn(y, 5n)), U32.to_nat(U32.shrn(x, 5n))),
      Nat.is_eq(U32.to_nat(U32.and(y, 31)), U32.to_nat(U32.and(x, 31))))
    : Bool}
  {M.Bool.imp(a, U32.is_eq(y, x)) == True{} : Bool}

def Addr.imp_eq(y, x, a, ea):
  match a:
    case False{}:
      {==}
    case True{}:
      %E.U32.sym(y, x,
        Sp.U32.address_inj(y, x,
          Lf.Nat.is_eq_reflect(U32.to_nat(U32.shrn(y, 5n)),
            U32.to_nat(U32.shrn(x, 5n)),
            E.Bool.and_l(
              Nat.is_eq(U32.to_nat(U32.shrn(y, 5n)),
                U32.to_nat(U32.shrn(x, 5n))),
              Nat.is_eq(U32.to_nat(U32.and(y, 31)),
                U32.to_nat(U32.and(x, 31))),
              E.Bool.sym(True{}, Bool.and(
                Nat.is_eq(U32.to_nat(U32.shrn(y, 5n)),
                  U32.to_nat(U32.shrn(x, 5n))),
                Nat.is_eq(U32.to_nat(U32.and(y, 31)),
                  U32.to_nat(U32.and(x, 31)))), ea))),
          Lf.Nat.is_eq_reflect(U32.to_nat(U32.and(y, 31)),
            U32.to_nat(U32.and(x, 31)),
            E.Bool.and_r(
              Nat.is_eq(U32.to_nat(U32.shrn(y, 5n)),
                U32.to_nat(U32.shrn(x, 5n))),
              Nat.is_eq(U32.to_nat(U32.and(y, 31)),
                U32.to_nat(U32.and(x, 31))),
              E.Bool.sym(True{}, Bool.and(
                Nat.is_eq(U32.to_nat(U32.shrn(y, 5n)),
                  U32.to_nat(U32.shrn(x, 5n))),
                Nat.is_eq(U32.to_nat(U32.and(y, 31)),
                  U32.to_nat(U32.and(x, 31)))), ea)))))
        : {U32.is_eq(_, x) == True{} : Bool}
      E.U32.is_eq_refl(x)

law Words.bit_set_only:
  for +ws: List<&2, U32>
  for +y: U32
  for +x: U32
  for +ok: {Wo.Words.bit(Wo.Words.set(ws, y), x) == True{} : Bool}
  {Bool.or(U32.is_eq(y, x), Wo.Words.bit(ws, x)) == True{} : Bool}

def Words.bit_set_only(ws, y, x, ok):
  Bool.or_lift(
    Bool.and(
      Nat.is_eq(U32.to_nat(U32.shrn(y, 5n)), U32.to_nat(U32.shrn(x, 5n))),
      Nat.is_eq(U32.to_nat(U32.and(y, 31)), U32.to_nat(U32.and(x, 31)))),
    U32.is_eq(y, x), Wo.Words.bit(ws, x),
    Words.at_set_at_only(ws, U32.to_nat(U32.shrn(y, 5n)),
      U32.to_nat(U32.shrn(x, 5n)), U32.to_nat(U32.and(y, 31)),
      U32.to_nat(U32.and(x, 31)), PA.U32.low_five_bound(y),
      PA.U32.low_five_bound(x), ok),
    Addr.imp_eq(y, x,
      Bool.and(
        Nat.is_eq(U32.to_nat(U32.shrn(y, 5n)), U32.to_nat(U32.shrn(x, 5n))),
        Nat.is_eq(U32.to_nat(U32.and(y, 31)),
          U32.to_nat(U32.and(x, 31)))), {==}))

# ---------------------------------------------------------------------------
# The leaf.
# ---------------------------------------------------------------------------

law PSet.add_leaf_pick_only:
  for +offs: List<&2, U32>
  for +x: U32
  for +small: Bool
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  for +ok: {S.PSet.mem.leaf(S.PSet.add.leaf.pick(offs, small), x)
    == True{} : Bool}
  {O.Ords.elem(offs, x) == True{} : Bool}

def PSet.add_leaf_pick_only(offs, x, small, inr, ok):
  match small:
    case True{}:
      ok
    case False{}:
      Equal.trans(Bool, O.Ords.elem(offs, x),
        Wo.Words.bit(S.PSet.spread(offs, Wo.Words.zeros(128n)), x), True{},
        E.Bool.sym(
          Wo.Words.bit(S.PSet.spread(offs, Wo.Words.zeros(128n)), x),
          O.Ords.elem(offs, x),
          Br.PSet.sparse_matches_its_tile(offs, x,
            Fa.PSet.zeros_fits(x, inr))),
        ok)

law PSet.add_leaf_only:
  for +s: S.PSet
  for +y: U32
  for +x: U32
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  for +ok: {S.PSet.mem.leaf(S.PSet.add.leaf(s, y), x) == True{} : Bool}
  {Bool.or(U32.is_eq(y, x), S.PSet.mem.leaf(s, x)) == True{} : Bool}

def PSet.add_leaf_only(s, y, x, inr, ok):
  match s:
    case S.PZero{}:
      %E.Bool.sym(U32.is_eq(y, x), True{}, ok)
        : {Bool.or(_, False{}) == True{} : Bool}
      {==}
    case S.PBranch{l, h}:
      %E.Bool.sym(U32.is_eq(y, x), True{}, ok)
        : {Bool.or(_, False{}) == True{} : Bool}
      {==}
    case S.PFull{}:
      Bool.or_true_r(U32.is_eq(y, x))
    case S.PDense{ws}:
      Words.bit_set_only(ws, y, x, ok)
    case S.PSparse{offs}:
      Ords.elem_insert_only(offs, y, x,
        PSet.add_leaf_pick_only(O.Ords.insert(offs, y), x,
          C.Nat.upto(List.length(&2, U32, O.Ords.insert(offs, y)),
            S.PSet.sparse_max()), inr, ok))

# ---------------------------------------------------------------------------
# The tree. Same four combinations as the other direction: when the branch
# the ordinal is in is the branch the insert changed, this is the induction
# step; when it is not, the ordinal was already there or is not there now.
# ---------------------------------------------------------------------------

law PSet.mem_zero:
  for +d: Nat
  for +h: U32
  for +x: U32
  {S.PSet.mem(d, S.PZero{}, h, x) == False{} : Bool}

def PSet.mem_zero(d, h, x):
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

law PSet.add_only:
  for +d: Nat
  for +s: S.PSet
  for +b: Bool
  for +bx: Bool
  for +h: U32
  for +y: U32
  for +x: U32
  for +eh: {h == U32.shln(1, 11n+d) : U32}
  for +eb: {b == U32.is_lt(y, h) : Bool}
  for +dok: {C.Nat.gt(32n, 11n+d) == True{} : Bool}
  for +inv: {Dc.U32.hi_zero(x, 12n+d) == True{} : Bool}
  for +invy: {Dc.U32.hi_zero(y, 12n+d) == True{} : Bool}
  for +ebx: {bx == U32.is_lt(x, h) : Bool}
  for +v: {Sh.PSet.wf(d, s, True{}) == True{} : Bool}
  for +ok: {S.PSet.mem(d, S.PSet.add(d, s, h, y, b), h, x) == True{} : Bool}
  {Bool.or(U32.is_eq(y, x), S.PSet.mem(d, s, h, x)) == True{} : Bool}

law PSet.insert_only:
  for +s: S.PSet
  for +y: U32
  for +x: U32
  for +v: {Sh.PSet.wf(20n, s, True{}) == True{} : Bool}
  for +ok: {S.PSet.member(20n, S.PSet.insert(20n, s, y), x)
    == True{} : Bool}
  {Bool.or(U32.is_eq(y, x), S.PSet.member(20n, s, x)) == True{} : Bool}

def Word.tail(-p: Nat, w: Word(1n+p)) -> Word(p):
  match w:
    case WCon{b, t}:
      t

def Word.head(-p: Nat, w: Word(1n+p)) -> Bool:
  match w:
    case WCon{b, t}:
      b

law Word.clear_inj:
  for +n: Nat
  for +k: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +ba: {W.Word.get(n, a, k) == True{} : Bool}
  for +bb: {W.Word.get(n, b, k) == True{} : Bool}
  for +e: {Dc.Word.clear(n, a, k) == Dc.Word.clear(n, b, k) : Word(n)}
  {a == b : Word(n)}

def Word.clear_inj(n, k, a, b, ba, bb, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match k:
        case 0n:
          match a b:
            case WCon{ab, at} WCon{bb2, bt}:
              %E.Bool.sym(ab, True{}, ba)
                : {WCon{_, at} == WCon{bb2, bt} : Word(1n+p)}
              %E.Bool.sym(bb2, True{}, bb)
                : {WCon{True{}, at} == WCon{_, bt} : Word(1n+p)}
              %Dc.Word.sym(p, at, bt,
                Equal.cong(Word(1n+p), Word(p), Word.tail(p),
                  WCon{False{}, at}, WCon{False{}, bt}, e))
                : {WCon{True{}, _} == WCon{True{}, bt} : Word(1n+p)}
              {==}
        case 1n+j:
          match a b:
            case WCon{ab, at} WCon{bb2, bt}:
              %E.Bool.sym(ab, bb2,
                Equal.cong(Word(1n+p), Bool, Word.head(p),
                  WCon{ab, Dc.Word.clear(p, at, j)},
                  WCon{bb2, Dc.Word.clear(p, bt, j)}, e))
                : {WCon{_, at} == WCon{bb2, bt} : Word(1n+p)}
              %Dc.Word.sym(p, at, bt,
                Word.clear_inj(p, j, at, bt, ba, bb,
                  Equal.cong(Word(1n+p), Word(p), Word.tail(p),
                    WCon{ab, Dc.Word.clear(p, at, j)},
                    WCon{bb2, Dc.Word.clear(p, bt, j)}, e)))
                : {WCon{bb2, _} == WCon{bb2, bt} : Word(1n+p)}
              {==}

law U32.sub_eq_shln:
  for +y: U32
  for +x: U32
  for +h: U32
  for +k: Nat
  for +eh: {h == U32.shln(1, k) : U32}
  for +e: {U32.sub(y, h) == U32.sub(x, h) : U32}
  {U32.sub(y, U32.shln(1, k)) == U32.sub(x, U32.shln(1, k)) : U32}

def U32.sub_eq_shln(y, x, h, k, eh, e):
  %eh : {U32.sub(y, _) == U32.sub(x, _) : U32}
  e

law U32.sub_inj:
  for +y: U32
  for +x: U32
  for +k: Nat
  for +by: {W.U32.bit(y, k) == True{} : Bool}
  for +bx: {W.U32.bit(x, k) == True{} : Bool}
  for +e: {U32.sub(y, U32.shln(1, k)) == U32.sub(x, U32.shln(1, k)) : U32}
  {y == x : U32}

def U32.sub_inj(y, x, k, by, bx, e):
  match y x:
    case U32{wy} U32{wx}:
      Equal.cong(Word(32n), U32, E.U32.pak, wy, wx,
        Word.clear_inj(32n, k, wy, wx, by, bx,
          Equal.cong(U32, Word(32n), W.U32.word,
            U32{Dc.Word.clear(32n, wy, k)},
            U32{Dc.Word.clear(32n, wx, k)},
            Equal.trans(U32, U32{Dc.Word.clear(32n, wy, k)},
              U32.sub(U32{wx}, U32.shln(1, k)),
              U32{Dc.Word.clear(32n, wx, k)},
              Equal.trans(U32, U32{Dc.Word.clear(32n, wy, k)},
                U32.sub(U32{wy}, U32.shln(1, k)),
                U32.sub(U32{wx}, U32.shln(1, k)),
                E.U32.sym(U32.sub(U32{wy}, U32.shln(1, k)),
                  U32{Dc.Word.clear(32n, wy, k)},
                  Dc.U32.sub_shln(U32{wy}, k, by)),
                e),
              Dc.U32.sub_shln(U32{wx}, k, bx)))))

law U32.imp_sub_eq:
  for +a: Bool
  for +y: U32
  for +x: U32
  for +h: U32
  for +k: Nat
  for +ea: {a == U32.is_eq(U32.sub(y, h), U32.sub(x, h)) : Bool}
  for +eh: {h == U32.shln(1, k) : U32}
  for +by: {W.U32.bit(y, k) == True{} : Bool}
  for +bx: {W.U32.bit(x, k) == True{} : Bool}
  {M.Bool.imp(a, U32.is_eq(y, x)) == True{} : Bool}

def U32.imp_sub_eq(a, y, x, h, k, ea, eh, by, bx):
  match a:
    case False{}:
      {==}
    case True{}:
      %E.U32.sym(y, x,
        U32.sub_inj(y, x, k, by, bx,
          U32.sub_eq_shln(y, x, h, k, eh,
            E.U32.eq_reflect(U32.sub(y, h), U32.sub(x, h),
              E.Bool.sym(True{},
                U32.is_eq(U32.sub(y, h), U32.sub(x, h)), ea)))))
        : {U32.is_eq(_, x) == True{} : Bool}
      E.U32.is_eq_refl(x)

def PSet.add_only(d, s, b, bx, h, y, x, eh, eb, dok, inv, invy, ebx, v, ok):
  match d:
    case 0n:
      PSet.add_leaf_only(s, y, x, inv, ok)
    case 1n+p:
      match s:
        case S.PFull{}:
          Bool.or_true_r(U32.is_eq(y, x))
        case S.PSparse{o}:
          E.Bool.noconf({Bool.or(U32.is_eq(y, x),
            S.PSet.mem(1n+p, S.PSparse{o}, h, x)) == True{} : Bool}, v)
        case S.PDense{w}:
          E.Bool.noconf({Bool.or(U32.is_eq(y, x),
            S.PSet.mem(1n+p, S.PDense{w}, h, x)) == True{} : Bool}, v)
        case S.PZero{}:
          match b:
            case True{}:
              match bx:
                case True{}:
                  %PSet.mem_zero(p, U32.shr(h), x)
                    : {Bool.or(U32.is_eq(y, x), _) == True{} : Bool}
                  PSet.add_only(p, S.PZero{}, U32.is_lt(y, U32.shr(h)),
                    U32.is_lt(x, U32.shr(h)), U32.shr(h), y, x,
                    Lf.PSet.half_shr(p, h, eh, dok), {==},
                    Dc.Nat.gt_down(32n, 11n+p, dok),
                    Lf.PSet.range_lo(p, h, x, eh, dok, ebx),
                    Lf.PSet.range_lo(p, h, y, eh, dok, eb),
                    {==}, Sh.PSet.wf_zero(p),
                    Ins.PSet.mem_lo(p,
                      S.PSet.add(p, S.PZero{}, U32.shr(h), y,
                        U32.is_lt(y, U32.shr(h))), S.PZero{}, h, x,
                      ebx, ok))
                case False{}:
                  E.Bool.noconf({Bool.or(U32.is_eq(y, x),
                    S.PSet.mem(1n+p, S.PZero{}, h, x)) == True{} : Bool},
                    Equal.trans(Bool, False{},
                      S.PSet.mem(p, S.PZero{}, U32.shr(h),
                        U32.sub(x, h)), True{},
                      E.Bool.sym(S.PSet.mem(p, S.PZero{}, U32.shr(h),
                        U32.sub(x, h)), False{},
                        PSet.mem_zero(p, U32.shr(h), U32.sub(x, h))),
                      Ins.PSet.mem_hi(p,
                        S.PSet.add(p, S.PZero{}, U32.shr(h), y,
                          U32.is_lt(y, U32.shr(h))), S.PZero{}, h, x,
                        ebx, ok)))
            case False{}:
              match bx:
                case True{}:
                  E.Bool.noconf({Bool.or(U32.is_eq(y, x),
                    S.PSet.mem(1n+p, S.PZero{}, h, x)) == True{} : Bool},
                    Equal.trans(Bool, False{},
                      S.PSet.mem(p, S.PZero{}, U32.shr(h), x), True{},
                      E.Bool.sym(S.PSet.mem(p, S.PZero{}, U32.shr(h), x),
                        False{}, PSet.mem_zero(p, U32.shr(h), x)),
                      Ins.PSet.mem_lo(p, S.PZero{},
                        S.PSet.add(p, S.PZero{}, U32.shr(h),
                          U32.sub(y, h),
                          U32.is_lt(U32.sub(y, h), U32.shr(h))), h, x,
                        ebx, ok)))
                case False{}:
                  %PSet.mem_zero(p, U32.shr(h), U32.sub(x, h))
                    : {Bool.or(U32.is_eq(y, x), _) == True{} : Bool}
                  Bool.or_lift(
                    U32.is_eq(U32.sub(y, h), U32.sub(x, h)),
                    U32.is_eq(y, x),
                    S.PSet.mem(p, S.PZero{}, U32.shr(h), U32.sub(x, h)),
                    PSet.add_only(p, S.PZero{},
                    U32.is_lt(U32.sub(y, h), U32.shr(h)),
                    U32.is_lt(U32.sub(x, h), U32.shr(h)), U32.shr(h),
                    U32.sub(y, h), U32.sub(x, h),
                    Lf.PSet.half_shr(p, h, eh, dok), {==},
                    Dc.Nat.gt_down(32n, 11n+p, dok),
                    Lf.PSet.range_hi(p, h, x, eh, dok, ebx, inv),
                    Lf.PSet.range_hi(p, h, y, eh, dok, eb, invy),
                    {==}, Sh.PSet.wf_zero(p),
                    Ins.PSet.mem_hi(p, S.PZero{},
                      S.PSet.add(p, S.PZero{}, U32.shr(h), U32.sub(y, h),
                        U32.is_lt(U32.sub(y, h), U32.shr(h))), h, x,
                      ebx, ok)),
                    U32.imp_sub_eq(
                      U32.is_eq(U32.sub(y, h), U32.sub(x, h)), y, x, h,
                      12n+p, {==}, eh,
                      Dc.Word.bit_of_not_hi_zero(32n, 12n+p,
                        W.U32.word(y), invy,
                        Lf.PSet.range_hi.no(p, h, y, eh, dok, eb)),
                      Dc.Word.bit_of_not_hi_zero(32n, 12n+p,
                        W.U32.word(x), inv,
                        Lf.PSet.range_hi.no(p, h, x, eh, dok, ebx))))
        case S.PBranch{lo, hi}:
          match b:
            case True{}:
              match bx:
                case True{}:
                  %ebx : {Bool.or(U32.is_eq(y, x),
                      S.PSet.mem(p, S.PSet.pick(_, lo, hi), U32.shr(h),
                        S.PSet.rebase(_, h, x))) == True{} : Bool}
                  PSet.add_only(p, lo, U32.is_lt(y, U32.shr(h)),
                    U32.is_lt(x, U32.shr(h)), U32.shr(h), y, x,
                    Lf.PSet.half_shr(p, h, eh, dok), {==},
                    Dc.Nat.gt_down(32n, 11n+p, dok),
                    Lf.PSet.range_lo(p, h, x, eh, dok, ebx),
                    Lf.PSet.range_lo(p, h, y, eh, dok, eb),
                    {==}, Sh.PSet.wf_lo(p, lo, hi, v),
                    Ins.PSet.mem_lo(p,
                      S.PSet.add(p, lo, U32.shr(h), y,
                        U32.is_lt(y, U32.shr(h))), hi, h, x, ebx, ok))
                case False{}:
                  %ebx : {Bool.or(U32.is_eq(y, x),
                      S.PSet.mem(p, S.PSet.pick(_, lo, hi), U32.shr(h),
                        S.PSet.rebase(_, h, x))) == True{} : Bool}
                  %E.Bool.sym(
                    S.PSet.mem(p, hi, U32.shr(h), U32.sub(x, h)), True{},
                    Ins.PSet.mem_hi(p,
                      S.PSet.add(p, lo, U32.shr(h), y,
                        U32.is_lt(y, U32.shr(h))), hi, h, x, ebx, ok))
                    : {Bool.or(U32.is_eq(y, x), _) == True{} : Bool}
                  Bool.or_true_r(U32.is_eq(y, x))
            case False{}:
              match bx:
                case True{}:
                  %ebx : {Bool.or(U32.is_eq(y, x),
                      S.PSet.mem(p, S.PSet.pick(_, lo, hi), U32.shr(h),
                        S.PSet.rebase(_, h, x))) == True{} : Bool}
                  %E.Bool.sym(S.PSet.mem(p, lo, U32.shr(h), x), True{},
                    Ins.PSet.mem_lo(p, lo,
                      S.PSet.add(p, hi, U32.shr(h), U32.sub(y, h),
                        U32.is_lt(U32.sub(y, h), U32.shr(h))), h, x,
                      ebx, ok))
                    : {Bool.or(U32.is_eq(y, x), _) == True{} : Bool}
                  Bool.or_true_r(U32.is_eq(y, x))
                case False{}:
                  %ebx : {Bool.or(U32.is_eq(y, x),
                      S.PSet.mem(p, S.PSet.pick(_, lo, hi), U32.shr(h),
                        S.PSet.rebase(_, h, x))) == True{} : Bool}
                  Bool.or_lift(
                    U32.is_eq(U32.sub(y, h), U32.sub(x, h)),
                    U32.is_eq(y, x),
                    S.PSet.mem(p, hi, U32.shr(h), U32.sub(x, h)),
                    PSet.add_only(p, hi,
                    U32.is_lt(U32.sub(y, h), U32.shr(h)),
                    U32.is_lt(U32.sub(x, h), U32.shr(h)), U32.shr(h),
                    U32.sub(y, h), U32.sub(x, h),
                    Lf.PSet.half_shr(p, h, eh, dok), {==},
                    Dc.Nat.gt_down(32n, 11n+p, dok),
                    Lf.PSet.range_hi(p, h, x, eh, dok, ebx, inv),
                    Lf.PSet.range_hi(p, h, y, eh, dok, eb, invy),
                    {==}, Sh.PSet.wf_hi(p, lo, hi, v),
                    Ins.PSet.mem_hi(p, lo,
                      S.PSet.add(p, hi, U32.shr(h), U32.sub(y, h),
                        U32.is_lt(U32.sub(y, h), U32.shr(h))), h, x,
                      ebx, ok)),
                    U32.imp_sub_eq(
                      U32.is_eq(U32.sub(y, h), U32.sub(x, h)), y, x, h,
                      12n+p, {==}, eh,
                      Dc.Word.bit_of_not_hi_zero(32n, 12n+p,
                        W.U32.word(y), invy,
                        Lf.PSet.range_hi.no(p, h, y, eh, dok, eb)),
                      Dc.Word.bit_of_not_hi_zero(32n, 12n+p,
                        W.U32.word(x), inv,
                        Lf.PSet.range_hi.no(p, h, x, eh, dok, ebx))))

def PSet.insert_only(s, y, x, v, ok):
  PSet.add_only(20n, s, U32.is_lt(y, S.PSet.half(20n)),
    U32.is_lt(x, S.PSet.half(20n)), S.PSet.half(20n), y, x,
    {==}, {==}, {==}, Dc.U32.hi_zero_full(x), Dc.U32.hi_zero_full(y),
    {==}, v, ok)

# ---------------------------------------------------------------------------
# Rebasing is injective.
#
# The descent subtracts the half-width from an ordinal in the upper half, so
# the induction ends with the two ordinals rebased and has to get back from
# "the rebased ones are equal" to "they are equal". Subtracting a power of
# two from a word that has that bit set clears the bit (proofs/descend.bend),
# and clearing a bit both words have set is injective: the cleared position
# is known on both sides, and every other position is untouched.
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# The fold. A set built from a list has nothing but that list on it.
# ---------------------------------------------------------------------------

law Bool.or_lift_r:
  for +c: Bool
  for +m: Bool
  for +q: Bool
  for +ok: {Bool.or(c, m) == True{} : Bool}
  for +h: {M.Bool.imp(m, q) == True{} : Bool}
  {Bool.or(c, q) == True{} : Bool}

def Bool.or_lift_r(c, m, q, ok, h):
  match c:
    case True{}:
      {==}
    case False{}:
      match m:
        case True{}:
          match q:
            case True{}:
              {==}
            case False{}:
              h
        case False{}:
          E.Bool.noconf({q == True{} : Bool}, ok)

law Bool.or3:
  for +c: Bool
  for +e: Bool
  for +m: Bool
  for +ok: {Bool.or(c, Bool.or(e, m)) == True{} : Bool}
  {Bool.or(Bool.or(e, c), m) == True{} : Bool}

def Bool.or3(c, e, m, ok):
  match c:
    case True{}:
      match e:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          ok

law PSet.imp_insert_only:
  for +q: Bool
  for +s: S.PSet
  for +y: U32
  for +x: U32
  for +eq: {q == S.PSet.member(20n, S.PSet.insert(20n, s, y), x) : Bool}
  for +v: {Sh.PSet.wf(20n, s, True{}) == True{} : Bool}
  {M.Bool.imp(q, Bool.or(U32.is_eq(y, x),
    S.PSet.member(20n, s, x))) == True{} : Bool}

def PSet.imp_insert_only(q, s, y, x, eq, v):
  match q:
    case False{}:
      {==}
    case True{}:
      PSet.insert_only(s, y, x, v,
        E.Bool.sym(True{},
          S.PSet.member(20n, S.PSet.insert(20n, s, y), x), eq))

law PSet.of_list_only:
  for +xs: List<&2, U32>
  for +s: S.PSet
  for +x: U32
  for +v: {Sh.PSet.wf(20n, s, True{}) == True{} : Bool}
  for +ok: {S.PSet.member(20n, S.PSet.of_list(20n, xs, s), x)
    == True{} : Bool}
  {Bool.or(List.contains(~U32, ~U32.is_eq, xs, x),
    S.PSet.member(20n, s, x)) == True{} : Bool}

def PSet.of_list_only(xs, s, x, v, ok):
  match xs:
    case Nil{}:
      ok
    case Con{a, t}:
      Bool.or3(List.contains(~U32, ~U32.is_eq, t, x), U32.is_eq(a, x),
        S.PSet.member(20n, s, x),
        Bool.or_lift_r(List.contains(~U32, ~U32.is_eq, t, x),
          S.PSet.member(20n, S.PSet.insert(20n, s, a), x),
          Bool.or(U32.is_eq(a, x), S.PSet.member(20n, s, x)),
          PSet.of_list_only(t, S.PSet.insert(20n, s, a), x,
            Pr.PSet.wf_insert(20n, s, a, v), ok),
          PSet.imp_insert_only(
            S.PSet.member(20n, S.PSet.insert(20n, s, a), x), s, a, x,
            {==}, v)))

law Bool.or_false_true:
  for +c: Bool
  for +ok: {Bool.or(c, False{}) == True{} : Bool}
  {c == True{} : Bool}

def Bool.or_false_true(c, ok):
  match c:
    case True{}:
      {==}
    case False{}:
      ok

law PSet.from_list_only:
  for +xs: List<&2, U32>
  for +x: U32
  for +ok: {S.PSet.member(20n, S.PSet.from_list(20n, xs), x)
    == True{} : Bool}
  {List.contains(~U32, ~U32.is_eq, xs, x) == True{} : Bool}

def PSet.from_list_only(xs, x, ok):
  Bool.or_false_true(List.contains(~U32, ~U32.is_eq, xs, x),
    PSet.of_list_only(xs, S.PZero{}, x, Sh.PSet.wf_zero(20n), ok))
