# proofs/enum.bend -- enumerating a tile lists exactly its members (law S-03,
# the sparse arm).
#
# `PSet.compress` turns a tile into a sparse leaf by enumerating it:
# `Words.members` walks the words, and within each word the bits, building
# ordinals with `ord + 1` and `ord + 32`. For that to preserve membership --
# which is the last thing law S-03 needs -- the list it produces has to hold
# exactly the ordinals whose bits are set.
#
# The walk and the address are two different ways of naming the same
# position, so the proof has two halves. The structural half mirrors the walk
# with `Words.holds`, a predicate shaped exactly like it. The arithmetic half
# connects `Words.holds(ws, 0, x)` to `Words.bit(ws, x)`, and that is where
# the division identity and the adder are spent.

import Base
import ./eq.bend as E
import ./nat.bend as N
import ./ords.bend as PO
import ./descend.bend as Dc
import ./split.bend as Sp
import ./adder.bend as Ad
import ./leaf.bend as Lf
import ../core/count.bend as C
import ../core/word.bend as W
import ../core/words.bend as Wo
import ../core/ords.bend as O

# The walk's own notion of membership: `ws` starts at ordinal `ord`.
def Words.bit_at(k: Nat, +w: U32, +ord: U32, +x: U32) -> Bool:
  match k:
    case 0n:
      False{}
    case 1n+j:
      Bool.or(Bool.and(Wo.Nat.is_one(W.U32.low(w)), U32.is_eq(ord, x)),
        Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x))

def Words.holds(ws: List<&2, U32>, +ord: U32, +x: U32) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{w, t}:
      Bool.or(Words.bit_at(32n, w, ord, x),
        Words.holds(t, (ord + 32 : U32), x))

# ---------------------------------------------------------------------------
# `Ords.elem` is `List.contains`, and membership survives a reversal.
# ---------------------------------------------------------------------------

law Ords.elem_contains:
  for +xs: List<&2, U32>
  for +x: U32
  {O.Ords.elem(xs, x)
    == List.contains(~U32, ~U32.is_eq, xs, x) : Bool}

law Ords.elem_contains.step:
  for +h: U32
  for +t: List<&2, U32>
  for +x: U32
  for +e: Bool
  for +ee: {e == U32.is_eq(h, x) : Bool}
  for +ih: {O.Ords.elem(t, x)
    == List.contains(~U32, ~U32.is_eq, t, x) : Bool}
  {O.Ords.elem.go(t, x, U32.is_eq(h, x))
    == Bool.or(U32.is_eq(h, x),
         List.contains(~U32, ~U32.is_eq, t, x)) : Bool}

def Ords.elem_contains.step(h, t, x, e, ee, ih):
  match e:
    case True{}:
      %ee : {O.Ords.elem.go(t, x, _) == Bool.or(_,
        List.contains(~U32, ~U32.is_eq, t, x)) : Bool}
      PO.Ords.elem_go_found(t, x)
    case False{}:
      %ee : {O.Ords.elem.go(t, x, _) == Bool.or(_,
        List.contains(~U32, ~U32.is_eq, t, x)) : Bool}
      ih

def Ords.elem_contains(xs, x):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Ords.elem_contains.step(h, t, x, U32.is_eq(h, x), {==},
        Ords.elem_contains(t, x))

# ---------------------------------------------------------------------------
# Membership over append and reverse.
# ---------------------------------------------------------------------------

law List.contains_append:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +x: U32
  {List.contains(~U32, ~U32.is_eq, List.append(&2, U32, a, b), x)
    == Bool.or(List.contains(~U32, ~U32.is_eq, a, x),
         List.contains(~U32, ~U32.is_eq, b, x)) : Bool}

law Bool.or_assoc:
  for a: Bool
  for b: Bool
  for c: Bool
  {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}

def Bool.or_assoc(a, b, c):
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def List.contains_append(a, b, x):
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %E.Bool.sym(
        List.contains(~U32, ~U32.is_eq, List.append(&2, U32, t, b), x),
        Bool.or(List.contains(~U32, ~U32.is_eq, t, x),
          List.contains(~U32, ~U32.is_eq, b, x)),
        List.contains_append(t, b, x))
        : {Bool.or(U32.is_eq(h, x), _)
          == Bool.or(Bool.or(U32.is_eq(h, x),
               List.contains(~U32, ~U32.is_eq, t, x)),
               List.contains(~U32, ~U32.is_eq, b, x)) : Bool}
      Bool.or_assoc(U32.is_eq(h, x),
        List.contains(~U32, ~U32.is_eq, t, x),
        List.contains(~U32, ~U32.is_eq, b, x))

law List.contains_reverse_go:
  for +xs: List<&2, U32>
  for +acc: List<&2, U32>
  for +x: U32
  {List.contains(~U32, ~U32.is_eq, List.reverse.go(&2, U32, xs, acc), x)
    == Bool.or(List.contains(~U32, ~U32.is_eq, xs, x),
         List.contains(~U32, ~U32.is_eq, acc, x)) : Bool}

law Bool.or_rotate:
  for a: Bool
  for b: Bool
  for c: Bool
  {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(b, a), c) : Bool}

def Bool.or_rotate(a, b, c):
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def List.contains_reverse_go(xs, acc, x):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %E.Bool.sym(
        List.contains(~U32, ~U32.is_eq,
          List.reverse.go(&2, U32, t, Con{h, acc}), x),
        Bool.or(List.contains(~U32, ~U32.is_eq, t, x),
          Bool.or(U32.is_eq(h, x),
            List.contains(~U32, ~U32.is_eq, acc, x))),
        List.contains_reverse_go(t, Con{h, acc}, x))
        : {_ == Bool.or(Bool.or(U32.is_eq(h, x),
            List.contains(~U32, ~U32.is_eq, t, x)),
            List.contains(~U32, ~U32.is_eq, acc, x)) : Bool}
      Bool.or_rotate(List.contains(~U32, ~U32.is_eq, t, x),
        U32.is_eq(h, x), List.contains(~U32, ~U32.is_eq, acc, x))

law List.contains_reverse:
  for +xs: List<&2, U32>
  for +x: U32
  {List.contains(~U32, ~U32.is_eq, List.reverse(&2, U32, xs), x)
    == List.contains(~U32, ~U32.is_eq, xs, x) : Bool}

law Bool.or_false_r2:
  for v: Bool
  {Bool.or(v, False{}) == v : Bool}

def Bool.or_false_r2(v):
  match v:
    case False{}:
      {==}
    case True{}:
      {==}

def List.contains_reverse(xs, x):
  %E.Bool.sym(
    List.contains(~U32, ~U32.is_eq, List.reverse.go(&2, U32, xs, Nil{}), x),
    Bool.or(List.contains(~U32, ~U32.is_eq, xs, x), False{}),
    List.contains_reverse_go(xs, Nil{}, x))
    : {_ == List.contains(~U32, ~U32.is_eq, xs, x) : Bool}
  Bool.or_false_r2(List.contains(~U32, ~U32.is_eq, xs, x))

# ---------------------------------------------------------------------------
# The walk. `Words.bits_rev` conses an ordinal exactly when the bit is set,
# and `Words.members.go` chains that across the words -- which is what
# `Words.bit_at` and `Words.holds` say, by construction.
# ---------------------------------------------------------------------------

law Words.contains_bits_rev:
  for +k: Nat
  for +w: U32
  for +ord: U32
  for +acc: List<&2, U32>
  for +x: U32
  {List.contains(~U32, ~U32.is_eq,
      Wo.Words.bits_rev(k, w, ord, acc), x)
    == Bool.or(Words.bit_at(k, w, ord, x),
         List.contains(~U32, ~U32.is_eq, acc, x)) : Bool}

law Words.contains_bits_rev.step:
  for +j: Nat
  for +w: U32
  for +ord: U32
  for +acc: List<&2, U32>
  for +x: U32
  for +s: Bool
  for +es: {s == Wo.Nat.is_one(W.U32.low(w)) : Bool}
  for +ih: {List.contains(~U32, ~U32.is_eq,
      Wo.Words.bits_rev(j, U32.shr(w), (ord + 1 : U32),
        Wo.Words.cons_if(Wo.Nat.is_one(W.U32.low(w)), ord, acc)), x)
    == Bool.or(Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x),
         List.contains(~U32, ~U32.is_eq,
           Wo.Words.cons_if(Wo.Nat.is_one(W.U32.low(w)), ord, acc), x))
    : Bool}
  {List.contains(~U32, ~U32.is_eq,
      Wo.Words.bits_rev(1n+j, w, ord, acc), x)
    == Bool.or(Words.bit_at(1n+j, w, ord, x),
         List.contains(~U32, ~U32.is_eq, acc, x)) : Bool}

law Words.contains_bits_rev.arm:
  for +j: Nat
  for +w: U32
  for +ord: U32
  for +acc: List<&2, U32>
  for +x: U32
  for +s: Bool
  for +es: {s == Wo.Nat.is_one(W.U32.low(w)) : Bool}
  {Bool.or(Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x),
      List.contains(~U32, ~U32.is_eq,
        Wo.Words.cons_if(Wo.Nat.is_one(W.U32.low(w)), ord, acc), x))
    == Bool.or(Bool.or(Bool.and(Wo.Nat.is_one(W.U32.low(w)),
         U32.is_eq(ord, x)),
         Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x)),
         List.contains(~U32, ~U32.is_eq, acc, x)) : Bool}

def Words.contains_bits_rev.arm(j, w, ord, acc, x, s, es):
  match s:
    case False{}:
      %es : {Bool.or(Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x),
          List.contains(~U32, ~U32.is_eq,
            Wo.Words.cons_if(_, ord, acc), x))
        == Bool.or(Bool.or(Bool.and(_, U32.is_eq(ord, x)),
             Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x)),
             List.contains(~U32, ~U32.is_eq, acc, x)) : Bool}
      {==}
    case True{}:
      %es : {Bool.or(Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x),
          List.contains(~U32, ~U32.is_eq,
            Wo.Words.cons_if(_, ord, acc), x))
        == Bool.or(Bool.or(Bool.and(_, U32.is_eq(ord, x)),
             Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x)),
             List.contains(~U32, ~U32.is_eq, acc, x)) : Bool}
      Bool.or_rotate(Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x),
        U32.is_eq(ord, x), List.contains(~U32, ~U32.is_eq, acc, x))

def Words.contains_bits_rev.step(j, w, ord, acc, x, s, es, ih):
  %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
      Wo.Words.bits_rev(j, U32.shr(w), (ord + 1 : U32),
        Wo.Words.cons_if(Wo.Nat.is_one(W.U32.low(w)), ord, acc)), x),
    Bool.or(Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x),
      List.contains(~U32, ~U32.is_eq,
        Wo.Words.cons_if(Wo.Nat.is_one(W.U32.low(w)), ord, acc), x)),
    ih)
    : {_ == Bool.or(Bool.or(Bool.and(Wo.Nat.is_one(W.U32.low(w)),
      U32.is_eq(ord, x)),
      Words.bit_at(j, U32.shr(w), (ord + 1 : U32), x)),
      List.contains(~U32, ~U32.is_eq, acc, x)) : Bool}
  Words.contains_bits_rev.arm(j, w, ord, acc, x, s, es)

def Words.contains_bits_rev(k, w, ord, acc, x):
  match k:
    case 0n:
      {==}
    case 1n+j:
      Words.contains_bits_rev.step(j, w, ord, acc, x,
        Wo.Nat.is_one(W.U32.low(w)), {==},
        Words.contains_bits_rev(j, U32.shr(w), (ord + 1 : U32),
          Wo.Words.cons_if(Wo.Nat.is_one(W.U32.low(w)), ord, acc), x))

law Words.contains_members_go:
  for +ws: List<&2, U32>
  for +ord: U32
  for +acc: List<&2, U32>
  for +x: U32
  {List.contains(~U32, ~U32.is_eq,
      Wo.Words.members.go(ws, ord, acc), x)
    == Bool.or(Words.holds(ws, ord, x),
         List.contains(~U32, ~U32.is_eq, acc, x)) : Bool}

def Words.contains_members_go(ws, ord, acc, x):
  match ws:
    case Nil{}:
      {==}
    case Con{w, t}:
      %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
          Wo.Words.members.go(t, (ord + 32 : U32),
            Wo.Words.bits_rev(32n, w, ord, acc)), x),
        Bool.or(Words.holds(t, (ord + 32 : U32), x),
          List.contains(~U32, ~U32.is_eq,
            Wo.Words.bits_rev(32n, w, ord, acc), x)),
        Words.contains_members_go(t, (ord + 32 : U32),
          Wo.Words.bits_rev(32n, w, ord, acc), x))
        : {_ == Bool.or(Bool.or(Words.bit_at(32n, w, ord, x),
            Words.holds(t, (ord + 32 : U32), x)),
            List.contains(~U32, ~U32.is_eq, acc, x)) : Bool}
      %E.Bool.sym(List.contains(~U32, ~U32.is_eq,
          Wo.Words.bits_rev(32n, w, ord, acc), x),
        Bool.or(Words.bit_at(32n, w, ord, x),
          List.contains(~U32, ~U32.is_eq, acc, x)),
        Words.contains_bits_rev(32n, w, ord, acc, x))
        : {Bool.or(Words.holds(t, (ord + 32 : U32), x), _)
          == Bool.or(Bool.or(Words.bit_at(32n, w, ord, x),
               Words.holds(t, (ord + 32 : U32), x)),
               List.contains(~U32, ~U32.is_eq, acc, x)) : Bool}
      Bool.or_rotate(Words.holds(t, (ord + 32 : U32), x),
        Words.bit_at(32n, w, ord, x),
        List.contains(~U32, ~U32.is_eq, acc, x))

law Words.elem_members:
  for +ws: List<&2, U32>
  for +x: U32
  {O.Ords.elem(Wo.Words.members(ws, 0), x)
    == Words.holds(ws, 0, x) : Bool}

law Words.elem_members.fin:
  for +ws: List<&2, U32>
  for +x: U32
  for +e: {List.contains(~U32, ~U32.is_eq,
      Wo.Words.members.go(ws, 0, Nil{}), x)
    == Bool.or(Words.holds(ws, 0, x), False{}) : Bool}
  {List.contains(~U32, ~U32.is_eq,
      Wo.Words.members.go(ws, 0, Nil{}), x)
    == Words.holds(ws, 0, x) : Bool}

def Words.elem_members.fin(ws, x, e):
  Equal.trans(Bool,
    List.contains(~U32, ~U32.is_eq,
      Wo.Words.members.go(ws, 0, Nil{}), x),
    Bool.or(Words.holds(ws, 0, x), False{}),
    Words.holds(ws, 0, x),
    e, Bool.or_false_r2(Words.holds(ws, 0, x)))

def Words.elem_members(ws, x):
  Equal.trans(Bool, O.Ords.elem(Wo.Words.members(ws, 0), x),
    List.contains(~U32, ~U32.is_eq, Wo.Words.members(ws, 0), x),
    Words.holds(ws, 0, x),
    Ords.elem_contains(Wo.Words.members(ws, 0), x),
    Equal.trans(Bool,
      List.contains(~U32, ~U32.is_eq, Wo.Words.members(ws, 0), x),
      List.contains(~U32, ~U32.is_eq,
        Wo.Words.members.go(ws, 0, Nil{}), x),
      Words.holds(ws, 0, x),
      List.contains_reverse(Wo.Words.members.go(ws, 0, Nil{}), x),
      Words.elem_members.fin(ws, x,
        Words.contains_members_go(ws, 0, Nil{}, x))))
