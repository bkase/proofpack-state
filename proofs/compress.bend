# proofs/compress.bend -- what compression decides (law S-03).
#
# `PSet.compress` reads one number -- how many bits a tile has set -- and
# picks a representation: `PZero{}`, `PFull{}`, a sparse offset list, or the
# words themselves. S-03 says the choice changes no member. Three of the four
# arms are proved here; the fourth is stated exactly.
#
#   `PZero{}`   the count is zero, so no bit is set (proofs/count.bend).
#   `PFull{}`   the count is 4096 across 128 words, so every bit is
#               (proofs/count.bend -- the pigeonhole).
#   `PDense{}`  the words are unchanged.
#   `PSparse{}` the tile is enumerated, and the list holds what the walk
#               holds (proofs/enum.bend). What is left is that the walk and
#               the tile address name the same positions, which is stated in
#               LAWS.pending.bend as the one remaining addressing claim.

import Base
import ./eq.bend as E
import ./addr.bend as Ad
import ./count.bend as Ct
import ./enum.bend as En
import ./walk.bend as Wk
import ./leaf.bend as Lf
import ./descend.bend as Dc
import ./split.bend as Sp
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/ords.bend as O
import ../core/set.bend as S

# The two decided-by-count arms, as membership statements.

law PSet.compress_zero:
  for +ws: List<&2, U32>
  for +x: U32
  for +z: {Wo.Words.count(ws) == 0n : Nat}
  {Wo.Words.bit(ws, x) == False{} : Bool}

def PSet.compress_zero(ws, x, z):
  Ct.Words.count_zero(ws, z, U32.to_nat(U32.shrn(x, 5n)),
    U32.to_nat(U32.and(x, 31)), Ad.U32.low_five_bound(x))

law PSet.compress_full:
  for +ws: List<&2, U32>
  for +x: U32
  for +wide: {List.length(&2, U32, ws) == 128n : Nat}
  for +full: {Wo.Words.count(ws) == 4096n : Nat}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {Wo.Words.bit(ws, x) == True{} : Bool}

law PSet.compress_full.cap:
  for +ws: List<&2, U32>
  for +wide: {List.length(&2, U32, ws) == 128n : Nat}
  for +full: {Wo.Words.count(ws) == 4096n : Nat}
  {Wo.Words.count(ws)
    == Sp.Nat.dbl(5n, List.length(&2, U32, ws)) : Nat}

def PSet.compress_full.cap(ws, wide, full):
  %E.Nat.sym(List.length(&2, U32, ws), 128n, wide)
    : {Wo.Words.count(ws) == Sp.Nat.dbl(5n, _) : Nat}
  full

law PSet.compress_full.idx:
  for +ws: List<&2, U32>
  for +x: U32
  for +wide: {List.length(&2, U32, ws) == 128n : Nat}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {C.Nat.gt(List.length(&2, U32, ws),
    U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}

def PSet.compress_full.idx(ws, x, wide, inr):
  %E.Nat.sym(List.length(&2, U32, ws), 128n, wide)
    : {C.Nat.gt(_, U32.to_nat(U32.shrn(x, 5n))) == True{} : Bool}
  Lf.PSet.shift_bound(x, inr)

def PSet.compress_full(ws, x, wide, full, inr):
  Ct.Words.count_full(ws,
    PSet.compress_full.cap(ws, wide, full),
    U32.to_nat(U32.shrn(x, 5n)),
    PSet.compress_full.idx(ws, x, wide, inr),
    U32.to_nat(U32.and(x, 31)), Ad.U32.low_five_bound(x))

# ---------------------------------------------------------------------------
# S-03, whole: compression preserves membership.
#
# The count is taken as a parameter with the equation that names it, because
# `PSet.compress` decides on it and Bend matches parameters rather than
# computed values.
# ---------------------------------------------------------------------------

law PSet.compress_keeps:
  for +ws: List<&2, U32>
  for +x: U32
  for +wide: {List.length(&2, U32, ws) == 128n : Nat}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.compress(ws), x)
    == Wo.Words.bit(ws, x) : Bool}

law PSet.compress_keeps.on:
  for +ws: List<&2, U32>
  for +x: U32
  for +wide: {List.length(&2, U32, ws) == 128n : Nat}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  for +k: Nat
  for +ek: {k == Wo.Words.count(ws) : Nat}
  {S.PSet.mem.leaf(S.PSet.compress.pick(ws, Wo.Words.count(ws)), x)
    == Wo.Words.bit(ws, x) : Bool}

law PSet.compress_keeps.pick:
  for +ws: List<&2, U32>
  for +x: U32
  for +wide: {List.length(&2, U32, ws) == 128n : Nat}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  for +k: Nat
  for +ek: {k == Wo.Words.count(ws) : Nat}
  {S.PSet.mem.leaf(S.PSet.compress.pick(ws, k), x)
    == Wo.Words.bit(ws, x) : Bool}

law PSet.compress_keeps.full:
  for +ws: List<&2, U32>
  for +x: U32
  for +wide: {List.length(&2, U32, ws) == 128n : Nat}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  for +k: Nat
  for +ek: {k == Wo.Words.count(ws) : Nat}
  for +f: Bool
  for +ef: {f == Nat.is_eq(k, 4096n) : Bool}
  {S.PSet.mem.leaf(S.PSet.compress.full(ws, k, Nat.is_eq(k, 4096n)), x)
    == Wo.Words.bit(ws, x) : Bool}

law PSet.compress_keeps.full.on:
  for +ws: List<&2, U32>
  for +x: U32
  for +wide: {List.length(&2, U32, ws) == 128n : Nat}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  for +k: Nat
  for +ek: {k == Wo.Words.count(ws) : Nat}
  for +f: Bool
  for +ef: {f == Nat.is_eq(k, 4096n) : Bool}
  {S.PSet.mem.leaf(S.PSet.compress.full(ws, k, f), x)
    == Wo.Words.bit(ws, x) : Bool}

law PSet.compress_keeps.count4096:
  for +ws: List<&2, U32>
  for +k: Nat
  for +ek: {k == Wo.Words.count(ws) : Nat}
  for +ef: {True{} == Nat.is_eq(k, 4096n) : Bool}
  {Wo.Words.count(ws) == 4096n : Nat}

def PSet.compress_keeps.count4096(ws, k, ek, ef):
  %ek : {_ == 4096n : Nat}
  Lf.Nat.is_eq_reflect(k, 4096n,
    E.Bool.sym(True{}, Nat.is_eq(k, 4096n), ef))

law PSet.compress_keeps.sparse:
  for +ws: List<&2, U32>
  for +x: U32
  for +wide: {List.length(&2, U32, ws) == 128n : Nat}
  for +inr: {Dc.U32.hi_zero(x, 12n) == True{} : Bool}
  for +sp: Bool
  {S.PSet.mem.leaf(S.PSet.compress.sparse(ws, sp), x)
    == Wo.Words.bit(ws, x) : Bool}

def PSet.compress_keeps.sparse(ws, x, wide, inr, sp):
  match sp:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Bool, O.Ords.elem(Wo.Words.members(ws, 0), x),
        En.Words.holds(ws, 0, x), Wo.Words.bit(ws, x),
        En.Words.elem_members(ws, x),
        Wk.Words.holds_bit(ws, x, wide))

def PSet.compress_keeps.full.on(ws, x, wide, inr, k, ek, f, ef):
  match f:
    case True{}:
      E.Bool.sym(Wo.Words.bit(ws, x), True{},
        PSet.compress_full(ws, x, wide,
          PSet.compress_keeps.count4096(ws, k, ek, ef), inr))
    case False{}:
      PSet.compress_keeps.sparse(ws, x, wide, inr,
        C.Nat.upto(k, S.PSet.sparse_max()))

def PSet.compress_keeps.full(ws, x, wide, inr, k, ek, f, ef):
  %ef : {S.PSet.mem.leaf(S.PSet.compress.full(ws, k, _), x)
    == Wo.Words.bit(ws, x) : Bool}
  PSet.compress_keeps.full.on(ws, x, wide, inr, k, ek, f, ef)

def PSet.compress_keeps.pick(ws, x, wide, inr, k, ek):
  match k:
    case 0n:
      E.Bool.sym(Wo.Words.bit(ws, x), False{},
        PSet.compress_zero(ws, x,
          E.Nat.sym(k, Wo.Words.count(ws), ek)))
    case 1n+p:
      PSet.compress_keeps.full(ws, x, wide, inr, 1n+p, ek,
        Nat.is_eq(1n+p, 4096n), {==})

def PSet.compress_keeps.on(ws, x, wide, inr, k, ek):
  %ek : {S.PSet.mem.leaf(S.PSet.compress.pick(ws, _), x)
    == Wo.Words.bit(ws, x) : Bool}
  PSet.compress_keeps.pick(ws, x, wide, inr, k, ek)

def PSet.compress_keeps(ws, x, wide, inr):
  PSet.compress_keeps.on(ws, x, wide, inr, Wo.Words.count(ws), {==})

# The obligation as `LAWS.pending.bend` stated it, with its hypotheses in the
# form they were written: a decidable width test and a `U32` comparison.

law PSet.compress_keeps_pending:
  for +ws: List<&2, U32>
  for +x: U32
  for +wide: {Nat.is_eq(List.length(&2, U32, ws), 128n) == True{} : Bool}
  for +inr: {U32.is_lt(x, 4096) == True{} : Bool}
  {S.PSet.mem.leaf(S.PSet.compress(ws), x)
    == Wo.Words.bit(ws, x) : Bool}

law PSet.range_of_lt:
  for +x: U32
  for +inr: {U32.is_lt(x, 4096) == True{} : Bool}
  {Dc.U32.hi_zero(x, 12n) == True{} : Bool}

def PSet.range_of_lt(x, inr):
  %Dc.U32.is_lt_shln(x, 12n, {==}) : {_ == True{} : Bool}
  inr

def PSet.compress_keeps_pending(ws, x, wide, inr):
  PSet.compress_keeps(ws, x,
    Lf.Nat.is_eq_reflect(List.length(&2, U32, ws), 128n, wide),
    PSet.range_of_lt(x, inr))
