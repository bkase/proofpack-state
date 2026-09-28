# proofs/interninj.bend -- interning is injective (law U-01).
#
# Two different object ids never end up sharing an ordinal. That is not a
# property of one write: it is a property of every write ever made into the
# table, so it is stated over a universe that was *built* by interning a list,
# which is what the importer does as it discovers objects.
#
# What makes it provable is that the argument never has to relate a key to the
# path the trie takes for it. It cases on the *paths*: two keys whose descents
# agree reach the same node, and a key whose descent diverges never meets the
# node another key's write rebuilt (proofs/trieput.bend). Then the ordinals
# themselves separate the cases, because every ordinal already in the table is
# below `next` and the one being handed out is `next`.

import Base
import ./eq.bend as E
import ./trie.bend as Tr
import ./intern.bend as PIn
import ./trieput.bend as Tp
import ./childtest.bend as Ct2
import ./orderlist.bend as Ol
import ../core/count.bend as C
import ../core/trie.bend as T
import ../adapters/git/oid.bend as O
import ../adapters/git/intern.bend as I

def Uni.next_of(u: I.Universe) -> U32:
  match u:
    case I.Uni{f, next, table, oids}:
      next

def Uni.oids_of(u: I.Universe) -> List<&2, O.Oid>:
  match u:
    case I.Uni{f, next, table, oids}:
      oids

law Uni.eta:
  for +u: I.Universe
  {u == I.Uni{I.Uni.fmt(u), Uni.next_of(u), I.Uni.table(u),
    Uni.oids_of(u)} : I.Universe}

def Uni.eta(u):
  match u:
    case I.Uni{f, next, table, oids}:
      {==}

# ---------------------------------------------------------------------------
# Every ordinal in the table is below a bound.
# ---------------------------------------------------------------------------

def Uni.slots_below(+b: List<&2, I.Slot>, +m: Nat) -> Bool:
  match b:
    case Nil{}:
      True{}
    case Con{s, t}:
      match s:
        case I.Slot{sid, ord}:
          Bool.and(C.Nat.gt(m, U32.to_nat(ord)),
            Uni.slots_below(t, m))

def Uni.bounded(+t: T.Trie<I.Bucket>, +m: Nat) -> Bool:
  match t:
    case T.TGap{}:
      True{}
    case T.TVal{b}:
      Uni.slots_below(b, m)
    case T.TBr{lo, hi}:
      Bool.and(Uni.bounded(lo, m), Uni.bounded(hi, m))

law Uni.slots_below_up:
  for +b: List<&2, I.Slot>
  for +m: Nat
  for +m2: Nat
  for +le: {C.Nat.upto(m, m2) == True{} : Bool}
  for +bd: {Uni.slots_below(b, m) == True{} : Bool}
  {Uni.slots_below(b, m2) == True{} : Bool}

def Uni.slots_below_up(b, m, m2, le, bd):
  match b:
    case Nil{}:
      {==}
    case Con{s, t}:
      match s:
        case I.Slot{sid, ord}:
          E.Bool.and_both(C.Nat.gt(m2, U32.to_nat(ord)),
            Uni.slots_below(t, m2),
            Ct2.Nat.gt_up(m, m2, U32.to_nat(ord), le,
              E.Bool.and_l(C.Nat.gt(m, U32.to_nat(ord)),
                Uni.slots_below(t, m), bd)),
            Uni.slots_below_up(t, m, m2, le,
              E.Bool.and_r(C.Nat.gt(m, U32.to_nat(ord)),
                Uni.slots_below(t, m), bd)))

law Uni.bounded_up:
  for +t: T.Trie<I.Bucket>
  for +m: Nat
  for +m2: Nat
  for +le: {C.Nat.upto(m, m2) == True{} : Bool}
  for +bd: {Uni.bounded(t, m) == True{} : Bool}
  {Uni.bounded(t, m2) == True{} : Bool}

def Uni.bounded_up(t, m, m2, le, bd):
  match t:
    case T.TGap{}:
      {==}
    case T.TVal{b}:
      Uni.slots_below_up(b, m, m2, le, bd)
    case T.TBr{lo, hi}:
      E.Bool.and_both(Uni.bounded(lo, m2), Uni.bounded(hi, m2),
        Uni.bounded_up(lo, m, m2, le,
          E.Bool.and_l(Uni.bounded(lo, m), Uni.bounded(hi, m), bd)),
        Uni.bounded_up(hi, m, m2, le,
          E.Bool.and_r(Uni.bounded(lo, m), Uni.bounded(hi, m), bd)))

law Uni.bounded_pick:
  for +b: Bool
  for +lo: T.Trie<I.Bucket>
  for +hi: T.Trie<I.Bucket>
  for +m: Nat
  for +bd: {Uni.bounded(T.TBr{lo, hi}, m) == True{} : Bool}
  {Uni.bounded(T.Trie.pick(I.Bucket, b, lo, hi), m) == True{}
    : Bool}

def Uni.bounded_pick(b, lo, hi, m, bd):
  match b:
    case True{}:
      E.Bool.and_l(Uni.bounded(lo, m), Uni.bounded(hi, m), bd)
    case False{}:
      E.Bool.and_r(Uni.bounded(lo, m), Uni.bounded(hi, m), bd)

law Uni.bounded_get:
  for +d: Nat
  for +t: T.Trie<I.Bucket>
  for +h: U32
  for +k: U32
  for +m: Nat
  for +bd: {Uni.bounded(t, m) == True{} : Bool}
  {Uni.slots_below(I.Uni.bucket.un(T.Trie.get(I.Bucket, d, t, h,
    k)), m) == True{} : Bool}

def Uni.bounded_get(d, t, h, k, m, bd):
  match d:
    case 0n:
      match t:
        case T.TGap{}:
          {==}
        case T.TVal{b}:
          bd
        case T.TBr{lo, hi}:
          {==}
    case 1n+p:
      match t:
        case T.TGap{}:
          {==}
        case T.TVal{b}:
          {==}
        case T.TBr{lo, hi}:
          Uni.bounded_get(p,
            T.Trie.pick(I.Bucket, U32.is_lt(k, h), lo, hi),
            U32.shr(h), T.Trie.rebase(U32.is_lt(k, h), h, k), m,
            Uni.bounded_pick(U32.is_lt(k, h), lo, hi, m, bd))

law Uni.bounded_put:
  for +d: Nat
  for +t: T.Trie<I.Bucket>
  for +h: U32
  for +k: U32
  for +nb: List<&2, I.Slot>
  for +b: Bool
  for +m: Nat
  for +bd: {Uni.bounded(t, m) == True{} : Bool}
  for +nbd: {Uni.slots_below(nb, m) == True{} : Bool}
  {Uni.bounded(T.Trie.put(I.Bucket, d, t, h, k, nb, b), m)
    == True{} : Bool}

def Uni.bounded_put(d, t, h, k, nb, b, m, bd, nbd):
  match d:
    case 0n:
      nbd
    case 1n+p:
      match t:
        case T.TBr{lo, hi}:
          match b:
            case True{}:
              E.Bool.and_both(Uni.bounded(T.Trie.put(I.Bucket, p,
                lo, U32.shr(h), k, nb,
                U32.is_lt(k, U32.shr(h))), m), Uni.bounded(hi, m),
                Uni.bounded_put(p, lo, U32.shr(h), k, nb,
                  U32.is_lt(k, U32.shr(h)), m,
                  E.Bool.and_l(Uni.bounded(lo, m),
                    Uni.bounded(hi, m), bd), nbd),
                E.Bool.and_r(Uni.bounded(lo, m), Uni.bounded(hi, m),
                  bd))
            case False{}:
              E.Bool.and_both(Uni.bounded(lo, m),
                Uni.bounded(T.Trie.put(I.Bucket, p, hi, U32.shr(h),
                  U32.sub(k, h), nb,
                  U32.is_lt(U32.sub(k, h), U32.shr(h))), m),
                E.Bool.and_l(Uni.bounded(lo, m), Uni.bounded(hi, m),
                  bd),
                Uni.bounded_put(p, hi, U32.shr(h), U32.sub(k, h),
                  nb, U32.is_lt(U32.sub(k, h), U32.shr(h)), m,
                  E.Bool.and_r(Uni.bounded(lo, m),
                    Uni.bounded(hi, m), bd), nbd))
        case T.TGap{}:
          match b:
            case True{}:
              E.Bool.and_both(Uni.bounded(T.Trie.put(I.Bucket, p,
                T.TGap{}, U32.shr(h), k, nb,
                U32.is_lt(k, U32.shr(h))), m),
                Uni.bounded(T.TGap{}, m),
                Uni.bounded_put(p, T.TGap{}, U32.shr(h), k, nb,
                  U32.is_lt(k, U32.shr(h)), m, {==}, nbd), {==})
            case False{}:
              E.Bool.and_both(Uni.bounded(T.TGap{}, m),
                Uni.bounded(T.Trie.put(I.Bucket, p, T.TGap{},
                  U32.shr(h), U32.sub(k, h), nb,
                  U32.is_lt(U32.sub(k, h), U32.shr(h))), m), {==},
                Uni.bounded_put(p, T.TGap{}, U32.shr(h),
                  U32.sub(k, h), nb,
                  U32.is_lt(U32.sub(k, h), U32.shr(h)), m, {==},
                  nbd))
        case T.TVal{old}:
          match b:
            case True{}:
              E.Bool.and_both(Uni.bounded(T.Trie.put(I.Bucket, p,
                T.TGap{}, U32.shr(h), k, nb,
                U32.is_lt(k, U32.shr(h))), m),
                Uni.bounded(T.TGap{}, m),
                Uni.bounded_put(p, T.TGap{}, U32.shr(h), k, nb,
                  U32.is_lt(k, U32.shr(h)), m, {==}, nbd), {==})
            case False{}:
              E.Bool.and_both(Uni.bounded(T.TGap{}, m),
                Uni.bounded(T.Trie.put(I.Bucket, p, T.TGap{},
                  U32.shr(h), U32.sub(k, h), nb,
                  U32.is_lt(U32.sub(k, h), U32.shr(h))), m), {==},
                Uni.bounded_put(p, T.TGap{}, U32.shr(h),
                  U32.sub(k, h), nb,
                  U32.is_lt(U32.sub(k, h), U32.shr(h)), m, {==},
                  nbd))

# ---------------------------------------------------------------------------
# One interning step, in terms of the table and the next ordinal.
# ---------------------------------------------------------------------------

def Uni.tab(+f: O.Fmt, +os: List<&2, O.Oid>) -> T.Trie<I.Bucket>:
  I.Uni.table(PIn.Uni.of_list(f, os))

def Uni.nxt(+f: O.Fmt, +os: List<&2, O.Oid>) -> U32:
  Uni.next_of(PIn.Uni.of_list(f, os))

law Uni.tab_hit:
  for +f: O.Fmt
  for +o: O.Oid
  for +rest: List<&2, O.Oid>
  for +k: U32
  for +fo: {I.Uni.find(Uni.tab(f, rest), o) == Some{k}
    : Maybe<&2, U32>}
  {Uni.tab(f, Con{o, rest}) == Uni.tab(f, rest)
    : T.Trie<I.Bucket>}

def Uni.tab_hit(f, o, rest, k, fo):
  %Equal.sym(I.Universe, PIn.Uni.of_list(f, rest),
    I.Uni{I.Uni.fmt(PIn.Uni.of_list(f, rest)),
      Uni.next_of(PIn.Uni.of_list(f, rest)),
      I.Uni.table(PIn.Uni.of_list(f, rest)),
      Uni.oids_of(PIn.Uni.of_list(f, rest))},
    Uni.eta(PIn.Uni.of_list(f, rest)))
    : {I.Uni.table(I.Interned.uni(I.Uni.intern(_, o)))
      == Uni.tab(f, rest) : T.Trie<I.Bucket>}
  %E.Maybe.sym(U32, I.Uni.find(Uni.tab(f, rest), o), Some{k}, fo)
    : {I.Uni.table(I.Interned.uni(I.Uni.intern.go(
      I.Uni.fmt(PIn.Uni.of_list(f, rest)),
      Uni.next_of(PIn.Uni.of_list(f, rest)),
      I.Uni.table(PIn.Uni.of_list(f, rest)),
      Uni.oids_of(PIn.Uni.of_list(f, rest)), o, _)))
    == Uni.tab(f, rest) : T.Trie<I.Bucket>}
  {==}

law Uni.nxt_hit:
  for +f: O.Fmt
  for +o: O.Oid
  for +rest: List<&2, O.Oid>
  for +k: U32
  for +fo: {I.Uni.find(Uni.tab(f, rest), o) == Some{k}
    : Maybe<&2, U32>}
  {Uni.nxt(f, Con{o, rest}) == Uni.nxt(f, rest) : U32}

def Uni.nxt_hit(f, o, rest, k, fo):
  %Equal.sym(I.Universe, PIn.Uni.of_list(f, rest),
    I.Uni{I.Uni.fmt(PIn.Uni.of_list(f, rest)),
      Uni.next_of(PIn.Uni.of_list(f, rest)),
      I.Uni.table(PIn.Uni.of_list(f, rest)),
      Uni.oids_of(PIn.Uni.of_list(f, rest))},
    Uni.eta(PIn.Uni.of_list(f, rest)))
    : {Uni.next_of(I.Interned.uni(I.Uni.intern(_, o)))
      == Uni.nxt(f, rest) : U32}
  %E.Maybe.sym(U32, I.Uni.find(Uni.tab(f, rest), o), Some{k}, fo)
    : {Uni.next_of(I.Interned.uni(I.Uni.intern.go(
      I.Uni.fmt(PIn.Uni.of_list(f, rest)),
      Uni.next_of(PIn.Uni.of_list(f, rest)),
      I.Uni.table(PIn.Uni.of_list(f, rest)),
      Uni.oids_of(PIn.Uni.of_list(f, rest)), o, _)))
    == Uni.nxt(f, rest) : U32}
  {==}

law Uni.tab_miss:
  for +f: O.Fmt
  for +o: O.Oid
  for +rest: List<&2, O.Oid>
  for +fo: {I.Uni.find(Uni.tab(f, rest), o) == None{}
    : Maybe<&2, U32>}
  {Uni.tab(f, Con{o, rest})
    == T.Trie.set(I.Bucket, 20n, Uni.tab(f, rest),
         I.Uni.slot_key(o),
         Con{I.Slot{o, Uni.nxt(f, rest)},
           I.Uni.bucket(Uni.tab(f, rest), I.Uni.slot_key(o))})
    : T.Trie<I.Bucket>}

def Uni.tab_miss(f, o, rest, fo):
  %Equal.sym(I.Universe, PIn.Uni.of_list(f, rest),
    I.Uni{I.Uni.fmt(PIn.Uni.of_list(f, rest)),
      Uni.next_of(PIn.Uni.of_list(f, rest)),
      I.Uni.table(PIn.Uni.of_list(f, rest)),
      Uni.oids_of(PIn.Uni.of_list(f, rest))},
    Uni.eta(PIn.Uni.of_list(f, rest)))
    : {I.Uni.table(I.Interned.uni(I.Uni.intern(_, o)))
      == T.Trie.set(I.Bucket, 20n, Uni.tab(f, rest),
           I.Uni.slot_key(o),
           Con{I.Slot{o, Uni.nxt(f, rest)},
             I.Uni.bucket(Uni.tab(f, rest), I.Uni.slot_key(o))})
      : T.Trie<I.Bucket>}
  %E.Maybe.sym(U32, I.Uni.find(Uni.tab(f, rest), o), None{}, fo)
    : {I.Uni.table(I.Interned.uni(I.Uni.intern.go(
      I.Uni.fmt(PIn.Uni.of_list(f, rest)),
      Uni.next_of(PIn.Uni.of_list(f, rest)),
      I.Uni.table(PIn.Uni.of_list(f, rest)),
      Uni.oids_of(PIn.Uni.of_list(f, rest)), o, _)))
    == T.Trie.set(I.Bucket, 20n, Uni.tab(f, rest),
         I.Uni.slot_key(o),
         Con{I.Slot{o, Uni.nxt(f, rest)},
           I.Uni.bucket(Uni.tab(f, rest), I.Uni.slot_key(o))})
      : T.Trie<I.Bucket>}
  {==}

law Uni.nxt_miss:
  for +f: O.Fmt
  for +o: O.Oid
  for +rest: List<&2, O.Oid>
  for +fo: {I.Uni.find(Uni.tab(f, rest), o) == None{}
    : Maybe<&2, U32>}
  {Uni.nxt(f, Con{o, rest}) == (Uni.nxt(f, rest) + 1 : U32) : U32}

def Uni.nxt_miss(f, o, rest, fo):
  %Equal.sym(I.Universe, PIn.Uni.of_list(f, rest),
    I.Uni{I.Uni.fmt(PIn.Uni.of_list(f, rest)),
      Uni.next_of(PIn.Uni.of_list(f, rest)),
      I.Uni.table(PIn.Uni.of_list(f, rest)),
      Uni.oids_of(PIn.Uni.of_list(f, rest))},
    Uni.eta(PIn.Uni.of_list(f, rest)))
    : {Uni.next_of(I.Interned.uni(I.Uni.intern(_, o)))
      == (Uni.nxt(f, rest) + 1 : U32) : U32}
  %E.Maybe.sym(U32, I.Uni.find(Uni.tab(f, rest), o), None{}, fo)
    : {Uni.next_of(I.Interned.uni(I.Uni.intern.go(
      I.Uni.fmt(PIn.Uni.of_list(f, rest)),
      Uni.next_of(PIn.Uni.of_list(f, rest)),
      I.Uni.table(PIn.Uni.of_list(f, rest)),
      Uni.oids_of(PIn.Uni.of_list(f, rest)), o, _)))
    == (Uni.nxt(f, rest) + 1 : U32) : U32}
  {==}

# ---------------------------------------------------------------------------
# The bound holds all the way along a run.
# ---------------------------------------------------------------------------

def Uni.room(+os: List<&2, O.Oid>, +f: O.Fmt) -> Bool:
  match os:
    case Nil{}:
      True{}
    case Con{o, rest}:
      Bool.and(C.Nat.gt(U32.to_nat((Uni.nxt(f, rest) + 1 : U32)),
        U32.to_nat(Uni.nxt(f, rest))), Uni.room(rest, f))

law Uni.bounded_of_list:
  for +os: List<&2, O.Oid>
  for +f: O.Fmt
  for +rm: {Uni.room(os, f) == True{} : Bool}
  {Uni.bounded(Uni.tab(f, os), U32.to_nat(Uni.nxt(f, os)))
    == True{} : Bool}

def Uni.bounded_of_list.step(+f: O.Fmt, +o: O.Oid,
  +rest: List<&2, O.Oid>, +m: Maybe<&2, U32>,
  +em: {m == I.Uni.find(Uni.tab(f, rest), o) : Maybe<&2, U32>},
  +gr: {C.Nat.gt(U32.to_nat((Uni.nxt(f, rest) + 1 : U32)),
    U32.to_nat(Uni.nxt(f, rest))) == True{} : Bool},
  +ih: {Uni.bounded(Uni.tab(f, rest),
    U32.to_nat(Uni.nxt(f, rest))) == True{} : Bool})
  -> {Uni.bounded(Uni.tab(f, Con{o, rest}),
    U32.to_nat(Uni.nxt(f, Con{o, rest}))) == True{} : Bool}:
  match m:
    case Some{k}:
      %Equal.sym(T.Trie<I.Bucket>, Uni.tab(f, Con{o, rest}),
        Uni.tab(f, rest), Uni.tab_hit(f, o, rest, k,
          E.Maybe.sym(U32, m, I.Uni.find(Uni.tab(f, rest), o), em)))
        : {Uni.bounded(_, U32.to_nat(Uni.nxt(f, Con{o, rest})))
          == True{} : Bool}
      %E.U32.sym(Uni.nxt(f, Con{o, rest}), Uni.nxt(f, rest),
        Uni.nxt_hit(f, o, rest, k,
          E.Maybe.sym(U32, m, I.Uni.find(Uni.tab(f, rest), o), em)))
        : {Uni.bounded(Uni.tab(f, rest), U32.to_nat(_)) == True{}
          : Bool}
      ih
    case None{}:
      %Equal.sym(T.Trie<I.Bucket>, Uni.tab(f, Con{o, rest}),
        T.Trie.set(I.Bucket, 20n, Uni.tab(f, rest),
          I.Uni.slot_key(o),
          Con{I.Slot{o, Uni.nxt(f, rest)},
            I.Uni.bucket(Uni.tab(f, rest), I.Uni.slot_key(o))}),
        Uni.tab_miss(f, o, rest,
          E.Maybe.sym(U32, m, I.Uni.find(Uni.tab(f, rest), o), em)))
        : {Uni.bounded(_, U32.to_nat(Uni.nxt(f, Con{o, rest})))
          == True{} : Bool}
      %E.U32.sym(Uni.nxt(f, Con{o, rest}),
        (Uni.nxt(f, rest) + 1 : U32),
        Uni.nxt_miss(f, o, rest,
          E.Maybe.sym(U32, m, I.Uni.find(Uni.tab(f, rest), o), em)))
        : {Uni.bounded(T.Trie.set(I.Bucket, 20n, Uni.tab(f, rest),
          I.Uni.slot_key(o),
          Con{I.Slot{o, Uni.nxt(f, rest)},
            I.Uni.bucket(Uni.tab(f, rest), I.Uni.slot_key(o))}),
          U32.to_nat(_)) == True{} : Bool}
      Uni.bounded_put(20n, Uni.tab(f, rest), T.Trie.half(20n),
        I.Uni.slot_key(o),
        Con{I.Slot{o, Uni.nxt(f, rest)},
          I.Uni.bucket(Uni.tab(f, rest), I.Uni.slot_key(o))},
        U32.is_lt(I.Uni.slot_key(o), T.Trie.half(20n)),
        U32.to_nat((Uni.nxt(f, rest) + 1 : U32)),
        Uni.bounded_up(Uni.tab(f, rest),
          U32.to_nat(Uni.nxt(f, rest)),
          U32.to_nat((Uni.nxt(f, rest) + 1 : U32)),
          Ol.Nat.le_of_gt_lt(U32.to_nat(Uni.nxt(f, rest)),
            U32.to_nat((Uni.nxt(f, rest) + 1 : U32)), gr), ih),
        E.Bool.and_both(C.Nat.gt(
          U32.to_nat((Uni.nxt(f, rest) + 1 : U32)),
          U32.to_nat(Uni.nxt(f, rest))),
          Uni.slots_below(
            I.Uni.bucket(Uni.tab(f, rest), I.Uni.slot_key(o)),
            U32.to_nat((Uni.nxt(f, rest) + 1 : U32))), gr,
          Uni.slots_below_up(
            I.Uni.bucket(Uni.tab(f, rest), I.Uni.slot_key(o)),
            U32.to_nat(Uni.nxt(f, rest)),
            U32.to_nat((Uni.nxt(f, rest) + 1 : U32)),
            Ol.Nat.le_of_gt_lt(U32.to_nat(Uni.nxt(f, rest)),
              U32.to_nat((Uni.nxt(f, rest) + 1 : U32)), gr),
            Uni.bounded_get(20n, Uni.tab(f, rest),
              T.Trie.half(20n), I.Uni.slot_key(o),
              U32.to_nat(Uni.nxt(f, rest)), ih))))

def Uni.bounded_of_list(os, f, rm):
  match os:
    case Nil{}:
      {==}
    case Con{o, rest}:
      Uni.bounded_of_list.step(f, o, rest,
        I.Uni.find(Uni.tab(f, rest), o), {==},
        E.Bool.and_l(C.Nat.gt(
          U32.to_nat((Uni.nxt(f, rest) + 1 : U32)),
          U32.to_nat(Uni.nxt(f, rest))), Uni.room(rest, f), rm),
        Uni.bounded_of_list(rest, f,
          E.Bool.and_r(C.Nat.gt(
            U32.to_nat((Uni.nxt(f, rest) + 1 : U32)),
            U32.to_nat(Uni.nxt(f, rest))), Uni.room(rest, f), rm)))

# ---------------------------------------------------------------------------
# Reading a bucket.
# ---------------------------------------------------------------------------

def Maybe.code(-B: Data, m: Maybe<&2, B>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def Maybe.empty(-B: Data, -k: B,
  e: {None{} == Some{k} : Maybe<&2, B>}) -> Empty:
  %e : Maybe.code(B, _)
  Unit{}

def Maybe.noconf(-A: Type, -B: Data, -k: B,
  e: {None{} == Some{k} : Maybe<&2, B>}) -> A:
  Empty.absurd(A, Maybe.empty(B, k, e))

def Maybe.un(-B: Data, +d: B, m: Maybe<&2, B>) -> B:
  match m:
    case None{}:
      d
    case Some{x}:
      x

law Maybe.some_inj:
  for -B: Data
  for +d: B
  for +a: B
  for +b: B
  for +e: {Some{a} == Some{b} : Maybe<&2, B>}
  {a == b : B}

def Maybe.some_inj(B, d, a, b, e):
  Equal.cong(Maybe<&2, B>, B, Maybe.un(B, d), Some{a}, Some{b}, e)

law Slot.find_some:
  for +bs: List<&2, I.Slot>
  for +o: O.Oid
  for +k: U32
  {I.Slot.find(bs, o, Some{k}) == Some{k} : Maybe<&2, U32>}

def Slot.find_some(bs, o, k):
  match bs:
    case Nil{}:
      {==}
    case Con{s, t}:
      {==}

law Slot.find_hit:
  for +sid: O.Oid
  for +ord: U32
  for +t: List<&2, I.Slot>
  for +o: O.Oid
  for +ee: {True{} == O.Oid.eq(sid, o) : Bool}
  {I.Slot.find(Con{I.Slot{sid, ord}, t}, o, None{}) == Some{ord}
    : Maybe<&2, U32>}

def Slot.find_hit(sid, ord, t, o, ee):
  %ee : {I.Slot.find(t, o, I.Slot.match_one.pick(ord, _))
    == Some{ord} : Maybe<&2, U32>}
  Slot.find_some(t, o, ord)

law Slot.find_miss:
  for +sid: O.Oid
  for +ord: U32
  for +t: List<&2, I.Slot>
  for +o: O.Oid
  for +ee: {False{} == O.Oid.eq(sid, o) : Bool}
  {I.Slot.find(Con{I.Slot{sid, ord}, t}, o, None{})
    == I.Slot.find(t, o, None{}) : Maybe<&2, U32>}

def Slot.find_miss(sid, ord, t, o, ee):
  %ee : {I.Slot.find(t, o, I.Slot.match_one.pick(ord, _))
    == I.Slot.find(t, o, None{}) : Maybe<&2, U32>}
  {==}

law Slot.find_below:
  for +bs: List<&2, I.Slot>
  for +o: O.Oid
  for +a: U32
  for +m: Nat
  for +bd: {Uni.slots_below(bs, m) == True{} : Bool}
  for ff: {I.Slot.find(bs, o, None{}) == Some{a} : Maybe<&2, U32>}
  {C.Nat.gt(m, U32.to_nat(a)) == True{} : Bool}

def Slot.find_below.pick(+sid: O.Oid, +ord: U32,
  +t: List<&2, I.Slot>, +o: O.Oid, +a: U32, +m: Nat, +e: Bool,
  +ee: {e == O.Oid.eq(sid, o) : Bool},
  +hd: {C.Nat.gt(m, U32.to_nat(ord)) == True{} : Bool},
  ih: {I.Slot.find(t, o, None{}) == Some{a} : Maybe<&2, U32>} ->
    {C.Nat.gt(m, U32.to_nat(a)) == True{} : Bool},
  ff: {I.Slot.find(Con{I.Slot{sid, ord}, t}, o, None{}) == Some{a}
    : Maybe<&2, U32>})
  -> {C.Nat.gt(m, U32.to_nat(a)) == True{} : Bool}:
  match e:
    case True{}:
      %Maybe.some_inj(U32, ord, ord, a,
        Equal.trans(Maybe<&2, U32>, Some{ord},
          I.Slot.find(Con{I.Slot{sid, ord}, t}, o, None{}),
          Some{a},
          E.Maybe.sym(U32,
            I.Slot.find(Con{I.Slot{sid, ord}, t}, o, None{}),
            Some{ord}, Slot.find_hit(sid, ord, t, o, ee)), ff))
        : {C.Nat.gt(m, U32.to_nat(_)) == True{} : Bool}
      hd
    case False{}:
      ih(Equal.trans(Maybe<&2, U32>, I.Slot.find(t, o, None{}),
        I.Slot.find(Con{I.Slot{sid, ord}, t}, o, None{}), Some{a},
        E.Maybe.sym(U32,
          I.Slot.find(Con{I.Slot{sid, ord}, t}, o, None{}),
          I.Slot.find(t, o, None{}),
          Slot.find_miss(sid, ord, t, o, ee)), ff))

def Slot.find_below(bs, o, a, m, bd, ff):
  match bs:
    case Nil{}:
      Maybe.noconf({C.Nat.gt(m, U32.to_nat(a)) == True{} : Bool},
        U32, a, ff)
    case Con{s, t}:
      match s:
        case I.Slot{sid, ord}:
          Slot.find_below.pick(sid, ord, t, o, a, m,
            O.Oid.eq(sid, o), {==},
            E.Bool.and_l(C.Nat.gt(m, U32.to_nat(ord)),
              Uni.slots_below(t, m), bd),
            Slot.find_below(t, o, a, m,
              E.Bool.and_r(C.Nat.gt(m, U32.to_nat(ord)),
                Uni.slots_below(t, m), bd)), ff)
law Oid.eq_reflect:
  for +a: O.Oid
  for +b: O.Oid
  for +ok: {O.Oid.eq(a, b) == True{} : Bool}
  {a == b : O.Oid}

def Oid.eq_reflect(a, b, ok):
  match a b:
    case O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
      O.Oid{b0, b1, b2, b3, b4, b5, b6, b7}:
      %E.U32.eq_reflect(a0, b0, E.Bool.and_l(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok))
        : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
          == O.Oid{_, b1, b2, b3, b4, b5, b6, b7} : O.Oid}
      %E.U32.eq_reflect(a1, b1, E.Bool.and_l(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))))), E.Bool.and_r(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok)))
        : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
          == O.Oid{a0, _, b2, b3, b4, b5, b6, b7} : O.Oid}
      %E.U32.eq_reflect(a2, b2, E.Bool.and_l(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))), E.Bool.and_r(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))))), E.Bool.and_r(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok))))
        : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
          == O.Oid{a0, a1, _, b3, b4, b5, b6, b7} : O.Oid}
      %E.U32.eq_reflect(a3, b3, E.Bool.and_l(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))), E.Bool.and_r(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))), E.Bool.and_r(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))))), E.Bool.and_r(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok)))))
        : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
          == O.Oid{a0, a1, a2, _, b4, b5, b6, b7} : O.Oid}
      %E.U32.eq_reflect(a4, b4, E.Bool.and_l(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))), E.Bool.and_r(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))), E.Bool.and_r(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))), E.Bool.and_r(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))))), E.Bool.and_r(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok))))))
        : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
          == O.Oid{a0, a1, a2, a3, _, b5, b6, b7} : O.Oid}
      %E.U32.eq_reflect(a5, b5, E.Bool.and_l(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)), E.Bool.and_r(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))), E.Bool.and_r(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))), E.Bool.and_r(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))), E.Bool.and_r(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))))), E.Bool.and_r(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok)))))))
        : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
          == O.Oid{a0, a1, a2, a3, a4, _, b6, b7} : O.Oid}
      %E.U32.eq_reflect(a6, b6, E.Bool.and_l(U32.is_eq(a6, b6), U32.is_eq(a7, b7), E.Bool.and_r(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)), E.Bool.and_r(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))), E.Bool.and_r(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))), E.Bool.and_r(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))), E.Bool.and_r(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))))), E.Bool.and_r(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok))))))))
        : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
          == O.Oid{a0, a1, a2, a3, a4, a5, _, b7} : O.Oid}
      %E.U32.eq_reflect(a7, b7, E.Bool.and_r(U32.is_eq(a6, b6), U32.is_eq(a7, b7), E.Bool.and_r(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)), E.Bool.and_r(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))), E.Bool.and_r(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))), E.Bool.and_r(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))), E.Bool.and_r(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7)))))), E.Bool.and_r(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), Bool.and(U32.is_eq(a3, b3), Bool.and(U32.is_eq(a4, b4), Bool.and(U32.is_eq(a5, b5), Bool.and(U32.is_eq(a6, b6), U32.is_eq(a7, b7))))))), ok))))))))
        : {O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}
          == O.Oid{a0, a1, a2, a3, a4, a5, a6, _} : O.Oid}
      {==}

# ---------------------------------------------------------------------------
# One interning write, seen through the bucket it touches.
#
# `Uni.tab1` is the table after a miss on `o`: the slot goes at the front of
# `o`'s bucket, and nothing else moves. Reading it back splits on whether the
# key being read descends the same way as `o`'s key -- `Trie.path_ne` is that
# test, and the two laws below are the two answers. Neither needs the keys to
# be equal, only their descents to agree, which is what the trie can see.
# ---------------------------------------------------------------------------

def Uni.tab1(+t: T.Trie<I.Bucket>, +o: O.Oid, +n: U32) ->
  T.Trie<I.Bucket>:
  T.Trie.set(I.Bucket, 20n, t, I.Uni.slot_key(o),
    Con{I.Slot{o, n}, I.Uni.bucket(t, I.Uni.slot_key(o))})

law Uni.bucket_other:
  for +t: T.Trie<I.Bucket>
  for +o: O.Oid
  for +n: U32
  for +kx: U32
  for +pe: {Tp.Trie.path_ne(20n, T.Trie.half(20n),
    I.Uni.slot_key(o), kx) == True{} : Bool}
  {I.Uni.bucket(Uni.tab1(t, o, n), kx) == I.Uni.bucket(t, kx)
    : I.Bucket}

def Uni.bucket_other(t, o, n, kx, pe):
  Equal.cong(Maybe<&2, I.Bucket>, I.Bucket, I.Uni.bucket.un,
    T.Trie.at(I.Bucket, 20n, Uni.tab1(t, o, n), kx),
    T.Trie.at(I.Bucket, 20n, t, kx),
    Tp.Trie.get_put_other(I.Bucket, 20n, t, T.Trie.half(20n),
      I.Uni.slot_key(o), kx,
      Con{I.Slot{o, n}, I.Uni.bucket(t, I.Uni.slot_key(o))},
      U32.is_lt(I.Uni.slot_key(o), T.Trie.half(20n)), {==},
      U32.is_lt(kx, T.Trie.half(20n)), {==}, pe))

law Uni.bucket_same:
  for +t: T.Trie<I.Bucket>
  for +o: O.Oid
  for +n: U32
  for +kx: U32
  for +pe: {Tp.Trie.path_ne(20n, T.Trie.half(20n),
    I.Uni.slot_key(o), kx) == False{} : Bool}
  {I.Uni.bucket(Uni.tab1(t, o, n), kx)
    == Con{I.Slot{o, n}, I.Uni.bucket(t, I.Uni.slot_key(o))}
    : I.Bucket}

def Uni.bucket_same(t, o, n, kx, pe):
  Equal.cong(Maybe<&2, I.Bucket>, I.Bucket, I.Uni.bucket.un,
    T.Trie.at(I.Bucket, 20n, Uni.tab1(t, o, n), kx),
    Some{Con{I.Slot{o, n}, I.Uni.bucket(t, I.Uni.slot_key(o))}},
    Equal.trans(Maybe<&2, I.Bucket>,
      T.Trie.at(I.Bucket, 20n, Uni.tab1(t, o, n), kx),
      T.Trie.at(I.Bucket, 20n, Uni.tab1(t, o, n),
        I.Uni.slot_key(o)),
      Some{Con{I.Slot{o, n}, I.Uni.bucket(t, I.Uni.slot_key(o))}},
      E.Maybe.sym(I.Bucket,
        T.Trie.at(I.Bucket, 20n, Uni.tab1(t, o, n),
          I.Uni.slot_key(o)),
        T.Trie.at(I.Bucket, 20n, Uni.tab1(t, o, n), kx),
        Tp.Trie.get_same_path(I.Bucket, 20n, Uni.tab1(t, o, n),
          T.Trie.half(20n), I.Uni.slot_key(o), kx, pe)),
      Tr.Trie.at_set(I.Bucket, 20n, t, I.Uni.slot_key(o),
        Con{I.Slot{o, n}, I.Uni.bucket(t, I.Uni.slot_key(o))})))

law Oid.eq_refl:
  for +a: O.Oid
  {O.Oid.eq(a, a) == True{} : Bool}

def Oid.eq_refl(a):
  match a:
    case O.Oid{a0, a1, a2, a3, a4, a5, a6, a7}:
      %E.Bool.sym(U32.is_eq(a0, a0), True{}, E.U32.is_eq_refl(a0))
        : {Bool.and(_, Bool.and(U32.is_eq(a1, a1), Bool.and(U32.is_eq(a2, a2), Bool.and(U32.is_eq(a3, a3), Bool.and(U32.is_eq(a4, a4), Bool.and(U32.is_eq(a5, a5), Bool.and(U32.is_eq(a6, a6), U32.is_eq(a7, a7)))))))) == True{} : Bool}
      %E.Bool.sym(U32.is_eq(a1, a1), True{}, E.U32.is_eq_refl(a1))
        : {Bool.and(_, Bool.and(U32.is_eq(a2, a2), Bool.and(U32.is_eq(a3, a3), Bool.and(U32.is_eq(a4, a4), Bool.and(U32.is_eq(a5, a5), Bool.and(U32.is_eq(a6, a6), U32.is_eq(a7, a7))))))) == True{} : Bool}
      %E.Bool.sym(U32.is_eq(a2, a2), True{}, E.U32.is_eq_refl(a2))
        : {Bool.and(_, Bool.and(U32.is_eq(a3, a3), Bool.and(U32.is_eq(a4, a4), Bool.and(U32.is_eq(a5, a5), Bool.and(U32.is_eq(a6, a6), U32.is_eq(a7, a7)))))) == True{} : Bool}
      %E.Bool.sym(U32.is_eq(a3, a3), True{}, E.U32.is_eq_refl(a3))
        : {Bool.and(_, Bool.and(U32.is_eq(a4, a4), Bool.and(U32.is_eq(a5, a5), Bool.and(U32.is_eq(a6, a6), U32.is_eq(a7, a7))))) == True{} : Bool}
      %E.Bool.sym(U32.is_eq(a4, a4), True{}, E.U32.is_eq_refl(a4))
        : {Bool.and(_, Bool.and(U32.is_eq(a5, a5), Bool.and(U32.is_eq(a6, a6), U32.is_eq(a7, a7)))) == True{} : Bool}
      %E.Bool.sym(U32.is_eq(a5, a5), True{}, E.U32.is_eq_refl(a5))
        : {Bool.and(_, Bool.and(U32.is_eq(a6, a6), U32.is_eq(a7, a7))) == True{} : Bool}
      %E.Bool.sym(U32.is_eq(a6, a6), True{}, E.U32.is_eq_refl(a6))
        : {Bool.and(_, U32.is_eq(a7, a7)) == True{} : Bool}
      %E.Bool.sym(U32.is_eq(a7, a7), True{}, E.U32.is_eq_refl(a7))
        : {_ == True{} : Bool}
      {==}

# ---------------------------------------------------------------------------
# Looking up a key after that write.
#
# Two answers, and which one applies is decided by the object ids, not by the
# keys: the slot just written matches `x` exactly when `Oid.eq(o, x)`, and
# otherwise the lookup sees what it would have seen before. The trie part of
# that -- a key with the same descent as `o` reads the rewritten bucket, one
# with a different descent reads its own -- is the two bucket laws above, and
# both roads lead back to the old table.
# ---------------------------------------------------------------------------

def Slot.findx(x: O.Oid, bs: List<&2, I.Slot>) -> Maybe<&2, U32>:
  I.Slot.find(bs, x, None{})

law Uni.bucket_path:
  for +t: T.Trie<I.Bucket>
  for +k1: U32
  for +k2: U32
  for +pe: {Tp.Trie.path_ne(20n, T.Trie.half(20n), k1, k2)
    == False{} : Bool}
  {I.Uni.bucket(t, k1) == I.Uni.bucket(t, k2) : I.Bucket}

def Uni.bucket_path(t, k1, k2, pe):
  Equal.cong(Maybe<&2, I.Bucket>, I.Bucket, I.Uni.bucket.un,
    T.Trie.at(I.Bucket, 20n, t, k1),
    T.Trie.at(I.Bucket, 20n, t, k2),
    Tp.Trie.get_same_path(I.Bucket, 20n, t, T.Trie.half(20n),
      k1, k2, pe))

law Uni.find_new_hit:
  for +t: T.Trie<I.Bucket>
  for +o: O.Oid
  for +n: U32
  for +x: O.Oid
  for +eq: {O.Oid.eq(o, x) == True{} : Bool}
  {I.Uni.find(Uni.tab1(t, o, n), x) == Some{n} : Maybe<&2, U32>}

def Uni.find_new_hit(t, o, n, x, eq):
  %Oid.eq_reflect(o, x, eq)
    : {I.Uni.find(Uni.tab1(t, o, n), _) == Some{n} : Maybe<&2, U32>}
  %Equal.sym(I.Bucket,
    I.Uni.bucket(Uni.tab1(t, o, n), I.Uni.slot_key(o)),
    Con{I.Slot{o, n}, I.Uni.bucket(t, I.Uni.slot_key(o))},
    Uni.bucket_same(t, o, n, I.Uni.slot_key(o),
      Tp.Trie.path_ne_refl(20n, T.Trie.half(20n),
        I.Uni.slot_key(o))))
    : {I.Slot.find(_, o, None{}) == Some{n} : Maybe<&2, U32>}
  Slot.find_hit(o, n, I.Uni.bucket(t, I.Uni.slot_key(o)), o,
    E.Bool.sym(O.Oid.eq(o, o), True{}, Oid.eq_refl(o)))

law Uni.find_new_miss:
  for +t: T.Trie<I.Bucket>
  for +o: O.Oid
  for +n: U32
  for +x: O.Oid
  for +ne: {O.Oid.eq(o, x) == False{} : Bool}
  {I.Uni.find(Uni.tab1(t, o, n), x) == I.Uni.find(t, x)
    : Maybe<&2, U32>}

def Uni.find_new_miss.pick(+t: T.Trie<I.Bucket>, +o: O.Oid, +n: U32,
  +x: O.Oid, +pn: Bool,
  +ep: {pn == Tp.Trie.path_ne(20n, T.Trie.half(20n),
    I.Uni.slot_key(o), I.Uni.slot_key(x)) : Bool},
  +ne: {O.Oid.eq(o, x) == False{} : Bool})
  -> {I.Uni.find(Uni.tab1(t, o, n), x) == I.Uni.find(t, x)
    : Maybe<&2, U32>}:
  match pn:
    case True{}:
      Equal.cong(I.Bucket, Maybe<&2, U32>, Slot.findx(x),
        I.Uni.bucket(Uni.tab1(t, o, n), I.Uni.slot_key(x)),
        I.Uni.bucket(t, I.Uni.slot_key(x)),
        Uni.bucket_other(t, o, n, I.Uni.slot_key(x),
          E.Bool.sym(True{},
            Tp.Trie.path_ne(20n, T.Trie.half(20n),
              I.Uni.slot_key(o), I.Uni.slot_key(x)), ep)))
    case False{}:
      %Equal.sym(I.Bucket,
        I.Uni.bucket(Uni.tab1(t, o, n), I.Uni.slot_key(x)),
        Con{I.Slot{o, n}, I.Uni.bucket(t, I.Uni.slot_key(o))},
        Uni.bucket_same(t, o, n, I.Uni.slot_key(x),
          E.Bool.sym(False{},
            Tp.Trie.path_ne(20n, T.Trie.half(20n),
              I.Uni.slot_key(o), I.Uni.slot_key(x)), ep)))
        : {I.Slot.find(_, x, None{}) == I.Uni.find(t, x)
          : Maybe<&2, U32>}
      Equal.trans(Maybe<&2, U32>,
        I.Slot.find(Con{I.Slot{o, n},
          I.Uni.bucket(t, I.Uni.slot_key(o))}, x, None{}),
        I.Slot.find(I.Uni.bucket(t, I.Uni.slot_key(o)), x, None{}),
        I.Uni.find(t, x),
        Slot.find_miss(o, n, I.Uni.bucket(t, I.Uni.slot_key(o)), x,
          E.Bool.sym(O.Oid.eq(o, x), False{}, ne)),
        Equal.cong(I.Bucket, Maybe<&2, U32>, Slot.findx(x),
          I.Uni.bucket(t, I.Uni.slot_key(o)),
          I.Uni.bucket(t, I.Uni.slot_key(x)),
          Uni.bucket_path(t, I.Uni.slot_key(o), I.Uni.slot_key(x),
            E.Bool.sym(False{},
              Tp.Trie.path_ne(20n, T.Trie.half(20n),
                I.Uni.slot_key(o), I.Uni.slot_key(x)), ep))))

def Uni.find_new_miss(t, o, n, x, ne):
  Uni.find_new_miss.pick(t, o, n, x,
    Tp.Trie.path_ne(20n, T.Trie.half(20n), I.Uni.slot_key(o),
      I.Uni.slot_key(x)), {==}, ne)

# ---------------------------------------------------------------------------
# Injectivity.
# ---------------------------------------------------------------------------

law Nat.gt_irrefl:
  for +m: Nat
  {C.Nat.gt(m, m) == False{} : Bool}

def Nat.gt_irrefl(m):
  match m:
    case 0n:
      {==}
    case 1n+p:
      Nat.gt_irrefl(p)

def Uni.findx(x: O.Oid, t: T.Trie<I.Bucket>) -> Maybe<&2, U32>:
  I.Uni.find(t, x)

law Uni.find_cast:
  for +t1: T.Trie<I.Bucket>
  for +t2: T.Trie<I.Bucket>
  for +x: O.Oid
  for +a: U32
  for +et: {t1 == t2 : T.Trie<I.Bucket>}
  for ff: {I.Uni.find(t1, x) == Some{a} : Maybe<&2, U32>}
  {I.Uni.find(t2, x) == Some{a} : Maybe<&2, U32>}

def Uni.find_cast(t1, t2, x, a, et, ff):
  %et : {I.Uni.find(_, x) == Some{a} : Maybe<&2, U32>}
  ff

# The ordinal handed to `x` by the write itself.
law Uni.new_ord:
  for +t: T.Trie<I.Bucket>
  for +o: O.Oid
  for +n: U32
  for +x: O.Oid
  for +a: U32
  for +eq: {O.Oid.eq(o, x) == True{} : Bool}
  for fx: {I.Uni.find(Uni.tab1(t, o, n), x) == Some{a}
    : Maybe<&2, U32>}
  {n == a : U32}

def Uni.new_ord(t, o, n, x, a, eq, fx):
  Maybe.some_inj(U32, a, n, a,
    Equal.trans(Maybe<&2, U32>, Some{n},
      I.Uni.find(Uni.tab1(t, o, n), x), Some{a},
      E.Maybe.sym(U32, I.Uni.find(Uni.tab1(t, o, n), x), Some{n},
        Uni.find_new_hit(t, o, n, x, eq)), fx))

# And the lookup an untouched key still gets.
law Uni.old_find:
  for +t: T.Trie<I.Bucket>
  for +o: O.Oid
  for +n: U32
  for +x: O.Oid
  for +a: U32
  for +ne: {O.Oid.eq(o, x) == False{} : Bool}
  for fx: {I.Uni.find(Uni.tab1(t, o, n), x) == Some{a}
    : Maybe<&2, U32>}
  {I.Uni.find(t, x) == Some{a} : Maybe<&2, U32>}

def Uni.old_find(t, o, n, x, a, ne, fx):
  Equal.trans(Maybe<&2, U32>, I.Uni.find(t, x),
    I.Uni.find(Uni.tab1(t, o, n), x), Some{a},
    E.Maybe.sym(U32, I.Uni.find(Uni.tab1(t, o, n), x),
      I.Uni.find(t, x), Uni.find_new_miss(t, o, n, x, ne)), fx)

# An ordinal already in the table is below the counter.
law Uni.old_below:
  for +t: T.Trie<I.Bucket>
  for +x: O.Oid
  for +a: U32
  for +m: Nat
  for +bd: {Uni.bounded(t, m) == True{} : Bool}
  for ff: {I.Uni.find(t, x) == Some{a} : Maybe<&2, U32>}
  {C.Nat.gt(m, U32.to_nat(a)) == True{} : Bool}

def Uni.old_below(t, x, a, m, bd, ff):
  Slot.find_below(I.Uni.bucket(t, I.Uni.slot_key(x)), x, a, m,
    Uni.bounded_get(20n, t, T.Trie.half(20n), I.Uni.slot_key(x),
      m, bd), ff)

# One side new, the other already there: the counter would have to be below
# itself.
law Uni.split_absurd:
  for -A: Type
  for +n: U32
  for +a: U32
  for +b: U32
  for +an: {n == a : U32}
  for +same: {a == b : U32}
  for +bb: {C.Nat.gt(U32.to_nat(n), U32.to_nat(b)) == True{} : Bool}
  A

def Nat.gt.at(i: Nat, k: Nat) -> Bool:
  C.Nat.gt(k, i)

def Uni.split_absurd(A, n, a, b, an, same, bb):
  E.Bool.noconf.r(A,
    Equal.trans(Bool, True{},
      C.Nat.gt(U32.to_nat(n), U32.to_nat(b)), False{},
      E.Bool.sym(C.Nat.gt(U32.to_nat(n), U32.to_nat(b)), True{}, bb),
      Equal.trans(Bool, C.Nat.gt(U32.to_nat(n), U32.to_nat(b)),
        C.Nat.gt(U32.to_nat(b), U32.to_nat(b)), False{},
        Equal.cong(Nat, Bool, Nat.gt.at(U32.to_nat(b)),
          U32.to_nat(n), U32.to_nat(b),
          Equal.cong(U32, Nat, U32.to_nat, n, b,
            Equal.trans(U32, n, a, b, an, same))),
        Nat.gt_irrefl(U32.to_nat(b)))))

# The four ways two lookups can land after one write: both on the new slot,
# both on the old table, or one of each -- and the mixed cases are where the
# counter does the work, because the new ordinal is the counter and every old
# one is below it.
def Uni.inj.pick(+f: O.Fmt, +o: O.Oid, +rest: List<&2, O.Oid>,
  +x: O.Oid, +y: O.Oid, +a: U32, +b: U32,
  +ex: Bool, +eex: {ex == O.Oid.eq(o, x) : Bool},
  +ey: Bool, +eey: {ey == O.Oid.eq(o, y) : Bool},
  +bd: {Uni.bounded(Uni.tab(f, rest),
    U32.to_nat(Uni.nxt(f, rest))) == True{} : Bool},
  +same: {a == b : U32},
  fx: {I.Uni.find(Uni.tab1(Uni.tab(f, rest), o, Uni.nxt(f, rest)), x)
    == Some{a} : Maybe<&2, U32>},
  fy: {I.Uni.find(Uni.tab1(Uni.tab(f, rest), o, Uni.nxt(f, rest)), y)
    == Some{b} : Maybe<&2, U32>},
  ih: {I.Uni.find(Uni.tab(f, rest), x) == Some{a} : Maybe<&2, U32>} ->
    {I.Uni.find(Uni.tab(f, rest), y) == Some{b} : Maybe<&2, U32>} ->
    {O.Oid.eq(x, y) == True{} : Bool})
  -> {O.Oid.eq(x, y) == True{} : Bool}:
  match ex:
    case True{}:
      match ey:
        case True{}:
          %Oid.eq_reflect(o, x,
            E.Bool.sym(True{}, O.Oid.eq(o, x), eex))
            : {O.Oid.eq(_, y) == True{} : Bool}
          %Oid.eq_reflect(o, y,
            E.Bool.sym(True{}, O.Oid.eq(o, y), eey))
            : {O.Oid.eq(o, _) == True{} : Bool}
          Oid.eq_refl(o)
        case False{}:
          Uni.split_absurd({O.Oid.eq(x, y) == True{} : Bool},
            Uni.nxt(f, rest), a, b,
            Uni.new_ord(Uni.tab(f, rest), o, Uni.nxt(f, rest), x, a,
              E.Bool.sym(True{}, O.Oid.eq(o, x), eex), fx),
            same,
            Uni.old_below(Uni.tab(f, rest), y, b,
              U32.to_nat(Uni.nxt(f, rest)), bd,
              Uni.old_find(Uni.tab(f, rest), o, Uni.nxt(f, rest), y, b,
                E.Bool.sym(False{}, O.Oid.eq(o, y), eey), fy)))
    case False{}:
      match ey:
        case True{}:
          Uni.split_absurd({O.Oid.eq(x, y) == True{} : Bool},
            Uni.nxt(f, rest), b, a,
            Uni.new_ord(Uni.tab(f, rest), o, Uni.nxt(f, rest), y, b,
              E.Bool.sym(True{}, O.Oid.eq(o, y), eey), fy),
            E.U32.sym(a, b, same),
            Uni.old_below(Uni.tab(f, rest), x, a,
              U32.to_nat(Uni.nxt(f, rest)), bd,
              Uni.old_find(Uni.tab(f, rest), o, Uni.nxt(f, rest), x, a,
                E.Bool.sym(False{}, O.Oid.eq(o, x), eex), fx)))
        case False{}:
          ih(Uni.old_find(Uni.tab(f, rest), o, Uni.nxt(f, rest), x, a,
              E.Bool.sym(False{}, O.Oid.eq(o, x), eex), fx),
            Uni.old_find(Uni.tab(f, rest), o, Uni.nxt(f, rest), y, b,
              E.Bool.sym(False{}, O.Oid.eq(o, y), eey), fy))

def Uni.inj.step(+f: O.Fmt, +o: O.Oid, +rest: List<&2, O.Oid>,
  +x: O.Oid, +y: O.Oid, +a: U32, +b: U32, +m: Maybe<&2, U32>,
  +em: {m == I.Uni.find(Uni.tab(f, rest), o) : Maybe<&2, U32>},
  +bd: {Uni.bounded(Uni.tab(f, rest),
    U32.to_nat(Uni.nxt(f, rest))) == True{} : Bool},
  +same: {a == b : U32},
  fx: {I.Uni.find(Uni.tab(f, Con{o, rest}), x) == Some{a}
    : Maybe<&2, U32>},
  fy: {I.Uni.find(Uni.tab(f, Con{o, rest}), y) == Some{b}
    : Maybe<&2, U32>},
  ih: {I.Uni.find(Uni.tab(f, rest), x) == Some{a} : Maybe<&2, U32>} ->
    {I.Uni.find(Uni.tab(f, rest), y) == Some{b} : Maybe<&2, U32>} ->
    {O.Oid.eq(x, y) == True{} : Bool})
  -> {O.Oid.eq(x, y) == True{} : Bool}:
  match m:
    case Some{k}:
      ih(Uni.find_cast(Uni.tab(f, Con{o, rest}), Uni.tab(f, rest), x, a,
          Uni.tab_hit(f, o, rest, k,
            E.Maybe.sym(U32, Some{k},
              I.Uni.find(Uni.tab(f, rest), o), em)), fx),
        Uni.find_cast(Uni.tab(f, Con{o, rest}), Uni.tab(f, rest), y, b,
          Uni.tab_hit(f, o, rest, k,
            E.Maybe.sym(U32, Some{k},
              I.Uni.find(Uni.tab(f, rest), o), em)), fy))
    case None{}:
      Uni.inj.pick(f, o, rest, x, y, a, b,
        O.Oid.eq(o, x), {==}, O.Oid.eq(o, y), {==}, bd, same,
        Uni.find_cast(Uni.tab(f, Con{o, rest}),
          Uni.tab1(Uni.tab(f, rest), o, Uni.nxt(f, rest)), x, a,
          Uni.tab_miss(f, o, rest,
            E.Maybe.sym(U32, None{},
              I.Uni.find(Uni.tab(f, rest), o), em)), fx),
        Uni.find_cast(Uni.tab(f, Con{o, rest}),
          Uni.tab1(Uni.tab(f, rest), o, Uni.nxt(f, rest)), y, b,
          Uni.tab_miss(f, o, rest,
            E.Maybe.sym(U32, None{},
              I.Uni.find(Uni.tab(f, rest), o), em)), fy),
        ih)

law Uni.inj:
  for +f: O.Fmt
  for +os: List<&2, O.Oid>
  for +x: O.Oid
  for +y: O.Oid
  for +a: U32
  for +b: U32
  for +rm: {Uni.room(os, f) == True{} : Bool}
  for +same: {a == b : U32}
  for fx: {I.Uni.find(Uni.tab(f, os), x) == Some{a} : Maybe<&2, U32>}
  for fy: {I.Uni.find(Uni.tab(f, os), y) == Some{b} : Maybe<&2, U32>}
  {O.Oid.eq(x, y) == True{} : Bool}

def Uni.inj(f, os, x, y, a, b, rm, same, fx, fy):
  match os:
    case Nil{}:
      Maybe.noconf({O.Oid.eq(x, y) == True{} : Bool}, U32, a, fx)
    case Con{o, rest}:
      Uni.inj.step(f, o, rest, x, y, a, b,
        I.Uni.find(Uni.tab(f, rest), o), {==},
        Uni.bounded_of_list(rest, f,
          E.Bool.and_r(C.Nat.gt(
            U32.to_nat((Uni.nxt(f, rest) + 1 : U32)),
            U32.to_nat(Uni.nxt(f, rest))), Uni.room(rest, f), rm)),
        same, fx, fy,
        Uni.inj(f, rest, x, y, a, b,
          E.Bool.and_r(C.Nat.gt(
            U32.to_nat((Uni.nxt(f, rest) + 1 : U32)),
            U32.to_nat(Uni.nxt(f, rest))), Uni.room(rest, f), rm),
          same))
