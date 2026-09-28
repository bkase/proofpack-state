# adapters/git/git.bend -- the Git plumbing boundary.
#
# Every Git invocation in this program is built here, and every one of them is
# read-only. SPEC 8.3 requires a sanitized environment and literal argv, with
# replacement objects and lazy fetching disabled, and forbids invoking
# filters, text conversion, hooks or shell aliases. `Git.base` is where that
# is enforced, once:
#
#   --no-replace-objects   grafts and replacements do not change what an
#                          object id means underneath us
#   --no-lazy-fetch        a partial clone never reaches the network during a
#                          query; a missing object stays missing and is
#                          reported
#   --no-optional-locks    nothing in the user's repository is written, not
#                          even an index refresh
#   --literal-pathspecs    no pathspec magic from any argument
#
# `cat-file` is used only as an IO boundary for object decoding and metadata,
# never as the reachability algorithm: closure, set algebra and missing state
# are computed by this library. `--batch-check` runs first so blob *contents*
# are never fetched -- only their type and size (SPEC 8.3).

import Base
import ../../core/count.bend as C
import ../../host/proc.bend as P
import ./bytes.bend as B
import ./oid.bend as O
import ./gitout.bend as Go

def Git.base(repo: String) -> List<&2, String>:
  ["-C", repo, "--no-replace-objects", "--no-lazy-fetch",
    "--no-optional-locks", "--literal-pathspecs"]

def Git.timeout() -> U32:
  600000

def Git.pack(r: U32 & (P.Bytes & String)) -> Go.Out:
  match r:
    case Tuple{st, rest}:
      match rest:
        case Tuple{body, err}:
          Go.Out{st, body, err}

def Git.fail(e: U32 & String) -> Go.Out:
  match e:
    case Tuple{code, msg}:
      Go.Out{U32.or(code, 4294967040), Nil{}, msg}

def Git.wrap(r: Result<&1, &1, U32 & String, U32 & (P.Bytes & String)>) ->
  Go.Out:
  match r:
    case Fail{e}:
      Git.fail(e)
    case Done{v}:
      Git.pack(v)

def Git.run(repo: String, sub: List<&2, String>, input: String,
  +max: U32) -> IO(Go.Out):
  do IO<Go.Out>:
    r : Result<&1, &1, U32 & String, U32 & (P.Bytes & String)> <-
      P.Host.run_bytes("git",
        List.append(&2, String, Git.base(repo), sub), input, max,
        Git.timeout())
    return Git.wrap(r)

# ---------------------------------------------------------------------------
# The individual calls.
# ---------------------------------------------------------------------------

def Git.object_format(repo: String) -> IO(Go.Out):
  Git.run(repo, ["rev-parse", "--show-object-format"], "", 4096)

def Git.git_dir(repo: String) -> IO(Go.Out):
  Git.run(repo, ["rev-parse", "--absolute-git-dir"], "", 65536)

# Resolve one requested root to a complete object id. `--verify` refuses an
# ambiguous or absent name rather than guessing, and `--end-of-options` stops
# a ref that looks like a flag from becoming one.
def Git.resolve(repo: String, ref: String) -> IO(Go.Out):
  Git.run(repo, ["rev-parse", "--verify", "--end-of-options", ref], "", 4096)

# Type and size for each object id on stdin. No contents, so a blob's bytes
# are never read.
def Git.batch_check(repo: String, oids: String, +max: U32) -> IO(Go.Out):
  Git.run(repo, ["cat-file", "--batch-check", "--buffer"], oids, max)

# Contents for each object id on stdin. Only ever called with commits, trees
# and tags.
def Git.batch(repo: String, oids: String, +max: U32) -> IO(Go.Out):
  Git.run(repo, ["cat-file", "--batch", "--buffer"], oids, max)

# Every object the selected store reports as present, including alternates.
# This is an inventory observation, not a graph (SPEC 8.1).
def Git.all_objects(repo: String, +max: U32) -> IO(Go.Out):
  Git.run(repo,
    ["cat-file", "--batch-check", "--batch-all-objects", "--unordered",
      "--buffer"], "", max)

# The independent oracle for the differential tests of SPEC 11.1. Never used
# to build a graph.
def Git.rev_list_objects(repo: String, root: String, +max: U32) -> IO(Go.Out):
  Git.run(repo,
    ["rev-list", "--objects", "--no-object-names", "--end-of-options", root],
    "", max)
