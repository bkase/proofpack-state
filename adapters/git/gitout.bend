# adapters/git/gitout.bend -- what a Git invocation answers.
#
# The result shape of the plumbing boundary, with no effect in it. Splitting
# it out from adapters/git/git.bend is what lets everything downstream --
# parsing, interning, the index, the closure -- be imported by LAWS.bend
# without dragging the subprocess effect into the proof closure. `bend
# PROOF.bend --verdict` reports any definition that reaches unsafe or
# foreign code, and a module that imports git.bend reaches it whether or not
# it calls it.
#
# `Bytes` here is adapters/git/bytes.bend's, which is the same definition as
# host/proc.bend's: the boundary hands back raw bytes because `git cat-file
# --batch` frames its records by a declared byte length.

import Base
import ../../core/count.bend as C
import ./bytes.bend as B
import ./oid.bend as O

type Out is Data:
  Out{status: U32, body: B.Bytes, err: String}

def Out.status(o: Out) -> U32:
  match o:
    case Out{status, body, err}:
      status

def Out.body(o: Out) -> B.Bytes:
  match o:
    case Out{status, body, err}:
      body

def Out.err(o: Out) -> String:
  match o:
    case Out{status, body, err}:
      err

# `git rev-parse --show-object-format` answers "sha1" or "sha256" on stdout.
def Git.fmt_of.pick(two: Bool, one: Bool) -> Maybe<&2, O.Fmt>:
  match two:
    case True{}:
      Some{O.Sha256{}}
    case False{}:
      match one:
        case True{}:
          Some{O.Sha1{}}
        case False{}:
          None{}

def Git.fmt_of(+bs: B.Bytes) -> Maybe<&2, O.Fmt>:
  Git.fmt_of.pick(B.Bytes.starts(B.Bytes.of_string("sha256"), bs),
    B.Bytes.starts(B.Bytes.of_string("sha1"), bs))
