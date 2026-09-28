# adapters/git/observe.bend -- the one Git call the inventory needs.
#
# adapters/git/inventory.bend projects a universe onto a list of observed
# object ids and counts what is in scope; that is pure and is what LAWS.bend
# talks about. This module holds the `git cat-file --batch-all-objects`
# invocation that produces the list, so the pure module does not import
# adapters/git/git.bend and the proof closure stays free of foreign code.

import Base
import ../../core/count.bend as C
import ../../core/set.bend as S
import ../../core/trie.bend as T
import ./bytes.bend as B
import ./oid.bend as O
import ./intern.bend as I
import ./parse.bend as Pa
import ./git.bend as Gi
import ./gitout.bend as Go
import ./inventory.bend as Iv

def Inv.observe.parsed(+u: I.Universe, ol: Pa.OidList, ok: Bool) ->
  Iv.InvResult:
  match ok:
    case False{}:
      Iv.IErr{"InvalidInput: malformed cat-file --batch-check stream"}
    case True{}:
      Iv.IOk{Iv.Inv.project(u, Pa.OidList.oids(ol))}

def Inv.observe.checked(+u: I.Universe, +f: O.Fmt, out: Go.Out,
  ran: Bool) -> Iv.InvResult:
  match ran:
    case False{}:
      Iv.IErr{"UnsupportedRepository: git cat-file --batch-all-objects failed: "
        ++ Go.Out.err(out)}
    case True{}:
      +ol = Pa.Parse.oids(f, Go.Out.body(out))
      Inv.observe.parsed(u, ol, Pa.OidList.ok(ol))

def Inv.observe(repo: String, +u: I.Universe, +f: O.Fmt) ->
  IO(Iv.InvResult):
  do IO<Iv.InvResult>:
    out : Go.Out <- Gi.Git.all_objects(repo, Iv.Inv.max_bytes())
    +o2 : Go.Out = out
    return Inv.observe.checked(u, f, o2, U32.is_zero(Go.Out.status(o2)))
