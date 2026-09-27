# host/proc.bend -- the process boundary.
#
# One effect, and it is the only way anything in this program starts another
# one. It takes a literal argv -- no shell, no `sh -c`, no PATH games beyond
# execvp on the program name -- and answers the child's stdout as raw bytes.
#
# SPEC 8.3 requires a sanitized subprocess environment and literal argv, and
# forbids invoking filters, text conversion, hooks or shell aliases. The
# adapter in adapters/git/ is what builds the argv; this module only runs it.
#
# Why bytes and not Base's `Process.run`: `Process.run` answers a `String`,
# and this runtime builds a String by decoding UTF-8 with U+FFFD substitution
# for invalid sequences. A Git tree object's entries hold raw binary object
# ids, and `git cat-file --batch` frames its records by a declared byte
# length, so one invalid sequence shifts every following record. See TRUST.md.

import Base

def Bytes() -> Data:
  List<&2, U32>

# Run `program` with `args`, writing `input` to its stdin. Answers
# (status, (stdout-bytes, stderr-text)), or Fail on a failure to start, a
# timeout, or output past `max_output` bytes.
def Host.run_bytes(program: String, args: List<&2, String>, input: String,
  max_output: U32, timeout_ms: U32) ->
  IO(Result<&1, &1, U32 & String, U32 & (Bytes & String)>):
  import "./run_bytes.c"
  import "./run_bytes.js"

# Whether a `!` call actually reaches the GPU in this process. The runtime
# decides that once at start-up, from whether a GPU was found and whether
# `--gpu off` was passed; this reads its answer. SPEC 7.6 requires a forced
# Metal run to fail when GPU execution cannot occur, which needs the actual
# backend and not the requested one.
def Host.gpu_enabled() -> IO(Bool):
  import "./gpu.c"
  import "./gpu.js"

# Two filesystem operations the Base library does not expose, done through
# the same literal-argv boundary as everything else rather than by adding
# more C. `mkdir -p` creates the derived-store directory; `mv` is the atomic
# publish of SPEC 6.5 -- a manifest is written to a temporary name and
# renamed into place, so a crash or a cancellation can never publish a
# half-built generation.
#
# Both write only inside the derived store. Nothing here touches a user's
# repository; SPEC 1.2 requires that, and adapters/git/git.bend is where it
# is enforced for the read side.
def Host.mkdir_p(path: String) -> IO(Result<&1, &1, U32 & String,
  U32 & (Bytes & String)>):
  Host.run_bytes("mkdir", ["-p", path], "", 4096, 30000)

def Host.rename(from: String, to: String) -> IO(Result<&1, &1,
  U32 & String, U32 & (Bytes & String)>):
  Host.run_bytes("mv", ["-f", from, to], "", 4096, 30000)
