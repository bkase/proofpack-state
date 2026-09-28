# pp.bend -- the ProofPack State executable.
#
# Build:  tools/bend pp.bend -o build/pp
# Run:    build/pp git stats --repo /path/to/repo --root refs/heads/main
#
# The entry point lives at the repository root because Bend keys a module by
# its import path normalized against the entry file's directory; see
# docs/MODULES.md.

import Base
import ./cli/run.bend as Cli

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    Cli.Cli.entry(args)
