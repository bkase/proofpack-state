# proofs/missing.bend -- the least-additional-set theorem (laws M-01..M-03).
#
# SPEC 3.4, for roots R and *any* recorded inventory H, with K = C(R) and
# M = K \ H:
#
#     K is inside H u M,  and  for every candidate transfer set T,
#     K inside H u T   <=>   M inside T.
#
# So M is the unique least additional object set that covers the requirement,
# ordered by inclusion. It excludes what H already has and contains every
# missing required object.
#
# The content of that theorem is pointwise and Boolean: it holds position by
# position, for whatever k, h and t say at that position, and it needs no
# induction and no structure on the sets. That is also why it does not
# require H to be graph-closed -- which is exactly what makes it usable
# against a partial cache.
#
# The laws below are those pointwise facts, over the same `Bool` values that
# `Words.at` and `PSet.mem` answer. `LAWS.bend` states them again over the
# production reader, and the tile laws of proofs/words.bend are what connect
# the two.
#
# What the theorem does *not* say is recorded next to it in the CLI envelope:
# it does not say the transfer encoding is byte-minimal, that a receiver
# really possesses its advertised inventory, or that objects remain available
# after the observation (SPEC 3.4).

import Base
import ../core/count.bend as C

# Material implication, as a Bool-valued def, so a law can be an equation.
def Bool.imp(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      True{}
    case True{}:
      b

# The difference, pointwise.
def Bool.sub(k: Bool, h: Bool) -> Bool:
  Bool.and(k, Bool.not(h))

# ---------------------------------------------------------------------------
# M-01, first half: H u (K \ H) covers K.
# ---------------------------------------------------------------------------

law Missing.covers:
  for k: Bool
  for h: Bool
  {Bool.imp(k, Bool.or(h, Bool.sub(k, h))) == True{} : Bool}

def Missing.covers(k, h):
  match k:
    case False{}:
      {==}
    case True{}:
      match h:
        case False{}:
          {==}
        case True{}:
          {==}

# ---------------------------------------------------------------------------
# M-01, second half: T covers what H is missing exactly when H u T covers K.
# This is the leastness: any T that completes the requirement must contain
# every position of M, and M itself is such a T.
# ---------------------------------------------------------------------------

law Missing.least:
  for k: Bool
  for h: Bool
  for t: Bool
  {Bool.imp(k, Bool.or(h, t)) == Bool.imp(Bool.sub(k, h), t) : Bool}

def Missing.least(k, h, t):
  match k:
    case False{}:
      {==}
    case True{}:
      match h:
        case False{}:
          match t:
            case False{}:
              {==}
            case True{}:
              {==}
        case True{}:
          match t:
            case False{}:
              {==}
            case True{}:
              {==}

# ---------------------------------------------------------------------------
# M-02: readiness is inclusion, and inclusion is an empty difference.
# ---------------------------------------------------------------------------

law Missing.ready:
  for k: Bool
  for h: Bool
  {Bool.imp(k, h) == Bool.not(Bool.sub(k, h)) : Bool}

def Missing.ready(k, h):
  match k:
    case False{}:
      {==}
    case True{}:
      match h:
        case False{}:
          {==}
        case True{}:
          {==}

# ---------------------------------------------------------------------------
# M-03: missing state composes.
#
# The first is why two requirements can share one inventory scan. The second
# is what permits successive local, LAN and upstream inventory filtering --
# and, as SPEC 4.2 insists, it does *not* imply those tiers are authorized or
# reachable. That is a service contract, not an algebraic one.
# ---------------------------------------------------------------------------

law Missing.union_split:
  for a: Bool
  for b: Bool
  for h: Bool
  {Bool.sub(Bool.or(a, b), h)
    == Bool.or(Bool.sub(a, h), Bool.sub(b, h)) : Bool}

def Missing.union_split(a, b, h):
  match a:
    case False{}:
      match b:
        case False{}:
          {==}
        case True{}:
          match h:
            case False{}:
              {==}
            case True{}:
              {==}
    case True{}:
      match b:
        case False{}:
          match h:
            case False{}:
              {==}
            case True{}:
              {==}
        case True{}:
          match h:
            case False{}:
              {==}
            case True{}:
              {==}

law Missing.tiers:
  for a: Bool
  for h1: Bool
  for h2: Bool
  {Bool.sub(a, Bool.or(h1, h2))
    == Bool.sub(Bool.sub(a, h1), h2) : Bool}

def Missing.tiers(a, h1, h2):
  match a:
    case False{}:
      {==}
    case True{}:
      match h1:
        case False{}:
          match h2:
            case False{}:
              {==}
            case True{}:
              {==}
        case True{}:
          {==}

# ---------------------------------------------------------------------------
# I-01: an additions-only inventory update needs no re-derivation.
#
#     M' = K \ (H u A) = (K \ H) \ A
#
# which is `Missing.tiers` read the other way round, and is what makes an
# inventory patch cheap. SPEC 4.2's general patch, `patch(H, D, A) =
# (H \ D) u A`, is the "add wins" precedence; such patches are not
# automatically commutative, and nothing here claims they are.
# ---------------------------------------------------------------------------

law Missing.added:
  for k: Bool
  for h: Bool
  for a: Bool
  {Bool.sub(k, Bool.or(h, a)) == Bool.sub(Bool.sub(k, h), a) : Bool}

def Missing.added(k, h, a):
  Missing.tiers(k, h, a)

# "Add wins" in SPEC 4.2's patch semantics: `patch(H, D, A) = (H \ D) u A`
# holds whichever way the union is written, because union is commutative
# pointwise. That is *all* it says. Two patches to the same inventory are not
# automatically commutative with each other, and SPEC 4.2 requires a
# restricted commuting-update law to be certified separately before such
# updates are parallelised. Nothing here certifies one.
law Missing.add_wins:
  for h: Bool
  for d: Bool
  for a: Bool
  {Bool.or(Bool.sub(h, d), a) == Bool.or(a, Bool.sub(h, d)) : Bool}

def Missing.add_wins(h, d, a):
  match h:
    case False{}:
      match a:
        case False{}:
          {==}
        case True{}:
          {==}
    case True{}:
      match d:
        case False{}:
          match a:
            case False{}:
              {==}
            case True{}:
              {==}
        case True{}:
          match a:
            case False{}:
              {==}
            case True{}:
              {==}
