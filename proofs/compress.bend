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
