# index/publish.bend -- the atomic write of a derived-store generation.
#
# index/store.bend is the pure manifest: the line grammar, the encoder and
# the decoder that LAWS.bend reasons about. This module holds the single
# effectful step -- mkdir, write to a temporary name, rename into place --
# which is what SPEC 6.5 requires, and which reaches host/proc.bend.
#
# It lives apart so index/store.bend itself imports no foreign code.

import Base
import ../core/count.bend as C
import ../core/trie.bend as T
import ../host/proc.bend as P
import ./store.bend as St
import ../adapters/git/bytes.bend as B
import ../adapters/git/oid.bend as O
import ../adapters/git/intern.bend as I
import ../adapters/git/import.bend as Im
import ../closure/graph.bend as G
import ./source.bend as Idx
def Store.publish(store: String, name: String, text: String) -> IO(Bool):
  +st = store
  +nm = name
  do IO<Bool>:
    md : Result<&1, &1, U32 & String, U32 & (P.Bytes & String)> <-
      P.Host.mkdir_p(st)
    f : Result<&1, &1, U32 & String, File> <-
      File.open(St.Store.temp(st, nm), "w")
    ok : Bool <- St.Store.write.opened(text, f)
    mv : Result<&1, &1, U32 & String, U32 & (P.Bytes & String)> <-
      P.Host.rename(St.Store.temp(st, nm), St.Store.path(st, nm))
    return ok
