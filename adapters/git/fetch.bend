# adapters/git/fetch.bend -- the effectful half of the importer.
#
# adapters/git/import.bend holds the pure import: the object table, the
# parse-to-rows step, and the walk that assigns ordinals. This module holds
# the four places that actually start `git`: resolving the requested roots,
# pulling object bodies in chunks, listing every object in the store, and the
# loop that ties those to the pure walk.
#
# The split is what keeps the proof closure clean. `bend PROOF.bend
# --verdict` reports every definition that reaches unsafe or foreign code,
# and a module reaches it by importing it, not by calling it -- so the pure
# module must not import adapters/git/git.bend at all.

import Base
import ../../core/count.bend as C
import ./bytes.bend as B
import ./oid.bend as O
import ./intern.bend as I
import ./parse.bend as Pa
import ./git.bend as Gi
import ./gitout.bend as Go
import ../../core/trie.bend as T
import ./import.bend as Im

def Imp.roots(refs: List<&2, String>, +repo: String, +f: O.Fmt,
  acc: Im.Roots) -> IO(Im.Roots):
  match refs:
    case Nil{}:
      IO.pure(Im.Roots, acc)
    case Con{ref, t}:
      +r = ref
      do IO<Im.Roots>:
        out : Go.Out <- Gi.Git.resolve(repo, r)
        +o2 : Go.Out = out
        Imp.roots(t, repo, f,
          Im.Imp.root.read(acc, f, r, o2, U32.is_zero(Go.Out.status(o2))))

# ---------------------------------------------------------------------------
# The object table: complete object id -> type, size, and the object ids the
# body names. Bucketed on a digest word like the interning table, and
# compared on the complete key, so a collision costs a list step and never a
# wrong answer.
#
# This is *not* the universe. Nothing here has an ordinal; an object is in the
# universe only once the walk below reaches it.
# ---------------------------------------------------------------------------

def Imp.bodies(+fuel: Nat, +repo: String, +f: O.Fmt, l: Im.Load,
  oids: List<&2, O.Oid>) -> IO(Im.Load):
  match fuel:
    case 0n:
      IO.pure(Im.Load, Im.Ld{Im.Load.tab(l), False{},
        "ResourceLimit: too many body chunks"})
    case 1n+g:
      match oids:
        case Nil{}:
          IO.pure(Im.Load, l)
        case Con{o, t}:
          +q = {Con{o, t} : List<&2, O.Oid>}
          do IO<Im.Load>:
            out : Go.Out <- Gi.Git.batch(repo,
              Im.Imp.hex_lines(f, List.take(&2, O.Oid, q, Im.Imp.chunk())),
              Im.Imp.batch_bytes())
            +o2 : Go.Out = out
            Imp.bodies(g, repo, f,
              Im.Imp.bodies.add(f, l, o2, U32.is_zero(Go.Out.status(o2))),
              List.drop(&2, O.Oid, q, Im.Imp.chunk()))

# The whole import: one `--batch-check --batch-all-objects` call, the body
# chunks, then the pure walk.
def Imp.all.parsed(+repo: String, +f: O.Fmt, inf: Pa.Infos, ok: Bool) ->
  IO(Im.Load):
  match ok:
    case False{}:
      IO.pure(Im.Load, Im.Ld{T.Trie.gap(Im.ObjBucket), False{},
        "InvalidInput: malformed cat-file --batch-check stream"})
    case True{}:
      +items = Pa.Infos.items(inf)
      Imp.bodies(1n+List.length(&2, Pa.Info, items), repo, f,
        Im.Ld{Im.Tab.of_infos(items, T.Trie.gap(Im.ObjBucket)), True{}, ""},
        Im.Imp.nonblob(items))

def Imp.all.checked(+repo: String, +f: O.Fmt, out: Go.Out, ran: Bool) ->
  IO(Im.Load):
  match ran:
    case False{}:
      IO.pure(Im.Load, Im.Ld{T.Trie.gap(Im.ObjBucket), False{},
        "UnsupportedRepository: git cat-file --batch-all-objects failed: "
          ++ Go.Out.err(out)})
    case True{}:
      +inf = Pa.Parse.infos(f, Go.Out.body(out))
      Imp.all.parsed(repo, f, inf, Pa.Infos.ok(inf))

# 256 MiB of `--batch-check --batch-all-objects` output: about four million
# objects at ~60 bytes an entry. Past that the call fails rather than
# truncating, and the caller reports ResourceLimit.
def Imp.all_bytes() -> U32:
  268435456

def Imp.all(+repo: String, +f: O.Fmt) -> IO(Im.Load):
  do IO<Im.Load>:
    out : Go.Out <- Gi.Git.all_objects(repo, Imp.all_bytes())
    +o2 : Go.Out = out
    Imp.all.checked(repo, f, o2, U32.is_zero(Go.Out.status(o2)))

# Every object in the store, doubled -- the walk visits each reachable one
# once and can never see more than the store holds.
def Imp.walk_fuel(+t: T.Trie<Im.ObjBucket>) -> Nat:
  4194304n

def Imp.loop.walk(+l: Im.Load, u: I.Universe, queue: List<&2, O.Oid>,
  ok: Bool) -> Im.FAcc:
  match ok:
    case False{}:
      Im.FA{u, Nil{}, Nil{}, Nil{}, Nil{}, False{}, Im.Load.err(l)}
    case True{}:
      Im.Imp.walk(Imp.walk_fuel(Im.Load.tab(l)), Im.Load.tab(l),
        Im.FA{u, Nil{}, Nil{}, Nil{}, Nil{}, True{}, ""}, queue, Nil{})

def Imp.loop(+fuel: Nat, +repo: String, +f: O.Fmt, +a: Im.FAcc,
  queue: List<&2, O.Oid>) -> IO(Im.FAcc):
  +q = queue
  +u = Im.FAcc.uni(a)
  do IO<Im.FAcc>:
    l : Im.Load <- Imp.all(repo, f)
    +l2 : Im.Load = l
    return Imp.loop.walk(l2, u, q, Im.Load.ok(l2))
