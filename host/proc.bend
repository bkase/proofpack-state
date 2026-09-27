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
