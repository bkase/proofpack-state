# adapters/git/inventory.bend -- what a store reports as present.
#
# A graph snapshot says what named objects require. An inventory observation
# says what a selected object store reports as locally present. They are
# different data products and this is the second one (SPEC 8.1).
#
# The receiver may be a partial clone or an incomplete cache. Nothing here
# assumes its inventory is graph-closed -- that is the whole point of the
# least-missing theorem, which holds for an arbitrary H (SPEC 3.4).
#
# Law G-03, inventory projection: the projection into the source universe
# contains exactly the recorded object ids that the source universe names.
# An object the receiver has that the source graph never mentions is *not*
# silently discarded: it is counted and reported as out-of-scope, because
# "we have 4000 objects you have never heard of" is a fact about the
# receiver, not a fact about the requirement.
#
# The observation is an assertion about a moment. `availability_scope` in
# every result envelope says so: this is a recorded observation, never a
# lease or a promise that the objects are still there (SPEC 9.4).

import Base
import ../../core/count.bend as C
import ../../core/set.bend as S
import ../../core/trie.bend as T
import ./bytes.bend as B
import ./oid.bend as O
import ./intern.bend as I
import ./parse.bend as Pa

# 64 MiB of `--batch-check` output: about a million objects at ~60 bytes an
# entry. Past that the call fails rather than truncating, and the caller
# reports ResourceLimit.
def Inv.max_bytes() -> U32:
  67108864

type Inventory is Data:
  Inv{present: S.PSet, in_scope: Nat, out_of_scope: Nat, total: Nat}

def Inventory.present(+v: Inventory) -> S.PSet:
  match v:
    case Inv{present, in_scope, out_of_scope, total}:
      present

def Inventory.in_scope(+v: Inventory) -> Nat:
  match v:
    case Inv{present, in_scope, out_of_scope, total}:
      in_scope

def Inventory.out_of_scope(+v: Inventory) -> Nat:
  match v:
    case Inv{present, in_scope, out_of_scope, total}:
      out_of_scope

def Inventory.total(+v: Inventory) -> Nat:
  match v:
    case Inv{present, in_scope, out_of_scope, total}:
      total

type InvResult is Data:
  IOk{inv: Inventory}
  IErr{msg: String}

# ---------------------------------------------------------------------------
# Projection. The universe's interning table is the lookup: an object id the
# source never named has no ordinal, which is precisely what out-of-scope
# means.
# ---------------------------------------------------------------------------

def Inv.add.hit(s: S.PSet, in_scope: Nat, out: Nat,
  m: Maybe<&2, U32>) -> Inventory:
  match m:
    case None{}:
      Inv{s, in_scope, 1n+out, 0n}
    case Some{x}:
      Inv{S.PSet.insert(20n, s, x), 1n+in_scope, out, 0n}

def Inv.step(+tbl: T.Trie<I.Bucket>, acc: Inventory, +o: O.Oid) ->
  Inventory:
  match acc:
    case Inv{present, in_scope, out_of_scope, total}:
      Inv.add.hit(present, in_scope, out_of_scope, I.Uni.find(tbl, o))

def Inv.fold(+tbl: T.Trie<I.Bucket>, oids: List<&2, O.Oid>,
  acc: Inventory) -> Inventory:
  match oids:
    case Nil{}:
      acc
    case Con{o, t}:
      Inv.fold(tbl, t, Inv.step(tbl, acc, o))

def Inv.finish(v: Inventory) -> Inventory:
  match v:
    case Inv{present, in_scope, out_of_scope, total}:
      +a = in_scope
      +b = out_of_scope
      Inv{present, a, b, Nat.add(a, b)}

def Inv.project(+u: I.Universe, oids: List<&2, O.Oid>) -> Inventory:
  Inv.finish(Inv.fold(I.Uni.table(u), oids,
    Inv{S.PSet.empty(), 0n, 0n, 0n}))

# ---------------------------------------------------------------------------
# Observing a repository.
# ---------------------------------------------------------------------------
