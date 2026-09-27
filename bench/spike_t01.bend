# T01 / T03 substrate spike: fused difference + popcount over dense U32 word
# tiles, on the CPU pool and on Metal, using the pinned Bend toolchain.
#
# What this measures, and why it is the first thing built:
#
#   * Whether `U32` bit operations lower to native machine ops (they do: the
#     compiler maps `U32.and`/`U32.shr`/... onto `U32_BIN(a, op, b)`), so the
#     `Word(32n)` bit-vector that `U32` is *defined* as stays in the proofs and
#     never materializes in the hot loop.
#   * Whether a host-built immutable word list can be read by every lane
#     without reference-count traffic (SPEC 7.5): `Spike.fused` only matches
#     its lists, so the compiler borrows them.
#   * Whether a fork tree over such tiles reaches the GPU lane cube at all, and
#     what it costs against the same leaf code on the CPU pool.
#
# It deliberately does NOT use the production set representation: it is the
# substrate experiment that decides what that representation may assume.
#
# `seed` is threaded from the clock so the compiler cannot hoist a trial out of
# the timed region; every call site passes a seed that is always 0.

import Base

# ---------------------------------------------------------------------------
# popcount: one shift step per bit, all native U32 ops, no allocation.
# ---------------------------------------------------------------------------

def Spike.popcount.go(+k: Nat, +x: U32, acc: U32) -> U32:
  match k:
    case 0n:
      acc
    case 1n+p:
      Spike.popcount.go(p, U32.shr(x), (acc + U32.and(x, 1) : U32))

def Spike.popcount(+x: U32) -> U32:
  Spike.popcount.go(32n, x, 0)

# ---------------------------------------------------------------------------
# One tile: a flat loop over two word lists, accumulating popcount(a AND NOT b).
# ---------------------------------------------------------------------------

def Spike.fused(a: List<&2, U32>, b: List<&2, U32>, acc: U32) -> U32:
  match a b:
    case Con{ah, at} Con{bh, bt}:
      d = U32.and(ah, U32.not(bh))
      Spike.fused(at, bt, (acc + Spike.popcount(d) : U32))
    case _ _:
      acc

# ---------------------------------------------------------------------------
# Tile generation.
# ---------------------------------------------------------------------------

def Spike.gen(+n: Nat, +seed: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +w = (seed * 1103515245 + 12345 : U32)
      w <> Spike.gen(p, w)

# ---------------------------------------------------------------------------
# Variant A: every lane reads the SAME host-built pair of tiles (shared,
# immutable words). This is the case SPEC 7.5 asks about.
# ---------------------------------------------------------------------------

def Spike.shared.node(+d: Nat, +req: List<&2, U32>, +inv: List<&2, U32>) -> U32:
  match d:
    case 0n:
      Spike.fused(req, inv, 0)
    case 1n+p:
      x y = Spike.shared.node(p, req, inv) Spike.shared.node(p, req, inv)
      (x + y : U32)

# ---------------------------------------------------------------------------
# Variant B: every lane builds its own tile-local words (no shared reads).
# ---------------------------------------------------------------------------

def Spike.owned.node(+d: Nat, +n: Nat, +seed: U32) -> U32:
  match d:
    case 0n:
      Spike.fused(Spike.gen(n, seed), Spike.gen(n, (seed + 7 : U32)), 0)
    case 1n+p:
      x y = Spike.owned.node(p, n, seed) Spike.owned.node(p, n, (seed + 1 : U32))
      (x + y : U32)

# ---------------------------------------------------------------------------
# Entry points. `!` sends the fork tree to Metal; the bare call uses the CPU
# pool. Both run the identical leaf code, which is what makes them comparable.
# ---------------------------------------------------------------------------

def Spike.shared.cpu(+d: Nat, +n: Nat, +s: U32) -> U32:
  Spike.shared.node(d, Spike.gen(n, (s + 1 : U32)), Spike.gen(n, (s + 2 : U32)))

def Spike.shared.gpu(+d: Nat, +n: Nat, +s: U32) -> U32:
  Spike.shared.node!(d, Spike.gen(n, (s + 1 : U32)), Spike.gen(n, (s + 2 : U32)))

def Spike.owned.cpu(+d: Nat, +n: Nat, +s: U32) -> U32:
  Spike.owned.node(d, n, (s + 1 : U32))

def Spike.owned.gpu(+d: Nat, +n: Nat, +s: U32) -> U32:
  Spike.owned.node!(d, n, (s + 1 : U32))

# ---------------------------------------------------------------------------
# Harness.
# ---------------------------------------------------------------------------

def Spike.us(t0: Nat, t1: Nat) -> String:
  Nat.show(Nat.sub(t1, t0))

def Spike.run(~f: @+d:Nat -> @+n:Nat -> @+s:U32 -> U32, name: String,
  +d: Nat, +n: Nat) -> IO(Unit):
  do IO<Unit>:
    t0r : Nat <- IO.now()
    +t0 : Nat = t0r
    # `Nat.mod(t0, 1n)` is always 0, but the compiler cannot hoist the trial
    # past the clock read, so the work happens between t0 and t1.
    s : U32 = U32.from_nat(Nat.mod(t0, 1n))
    IO.write(name ++ " sum=" ++ U32.show(f(d, n, s)))
    t1 : Nat <- IO.now()
    IO.print("  ms=" ++ Spike.us(t0, t1))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("# T01 substrate spike -- 2^16 leaves x 128 words")
    IO.print("# = 8388608 U32 words = 268435456 bits scanned per trial")
    Spike.run(~Spike.owned.cpu,  "owned.cpu ", 16n, 128n)
    Spike.run(~Spike.owned.gpu,  "owned.gpu ", 16n, 128n)
    Spike.run(~Spike.owned.cpu,  "owned.cpu ", 16n, 128n)
    Spike.run(~Spike.owned.gpu,  "owned.gpu ", 16n, 128n)
    Spike.run(~Spike.shared.cpu, "shared.cpu", 16n, 128n)
    Spike.run(~Spike.shared.gpu, "shared.gpu", 16n, 128n)
    Spike.run(~Spike.shared.cpu, "shared.cpu", 16n, 128n)
    Spike.run(~Spike.shared.gpu, "shared.gpu", 16n, 128n)
    IO.print("# A-vs-A noise control")
    Spike.run(~Spike.owned.cpu,  "owned.cpu ", 16n, 128n)
    Spike.run(~Spike.owned.cpu,  "owned.cpu ", 16n, 128n)
