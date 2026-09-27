# proofs/cert.bend -- what an accepted certificate means (law C-04, restated).
#
# SPEC 4.4's certificate is four conditions, and `pp git verify` runs all four
# on every query. What this release cannot mechanise is their *meaning* --
# that conditions 1 and 2 put `Reach(R)` inside `C` and condition 3's
# well-founded predecessor chains put `C` inside `Reach(R)`. That argument is
# written out in closure/cert.bend and in TRUST.md, and it stays argued.
#
# What can be mechanised, and is worth having, is the other half: that an
# accepted certificate really does establish each of the four conditions,
# rather than some weaker conjunction. A reader of `pp git verify`'s output
# can then read these four laws instead of the checker.
#
# So C-04 is restated as "acceptance means exactly these four facts" and
# discharged; "these four facts mean exactness" stays in LAWS.pending.bend.

import Base
import ./eq.bend as E
import ./descend.bend as Dc
import ../core/set.bend as S
import ../closure/graph.bend as G
import ../closure/reach.bend as R
import ../closure/cert.bend as Ct
import ../spec/closure.bend as Sp

law Cert.accepts_roots:
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +roots: List<&2, U32>
  for +levels: R.Levels
  for +c: S.PSet
  for +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool}
  {S.PSet.is_subset(sd, S.PSet.from_list(sd, roots), c) == True{} : Bool}

def Cert.accepts_roots(td, g, sd, roots, levels, c, ok):
  Dc.Bool.and_left(
    S.PSet.is_subset(sd, S.PSet.from_list(sd, roots), c),
    Bool.and(Sp.Spec.closed(td, g, sd, c),
      Bool.and(Ct.Cert.same(sd, S.PSet.from_list(sd,
          Ct.Cert.concat(levels, Nil{})), c),
        Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
          Ct.Cert.first(levels, roots),
          S.PSet.is_subset(sd, S.PSet.from_list(sd,
            Ct.Cert.first(levels, roots)),
            S.PSet.from_list(sd, roots))))), ok)

law Cert.accepts_closed:
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +roots: List<&2, U32>
  for +levels: R.Levels
  for +c: S.PSet
  for +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool}
  {Sp.Spec.closed(td, g, sd, c) == True{} : Bool}

def Cert.accepts_closed(td, g, sd, roots, levels, c, ok):
  Dc.Bool.and_left(Sp.Spec.closed(td, g, sd, c),
    Bool.and(Ct.Cert.same(sd, S.PSet.from_list(sd,
        Ct.Cert.concat(levels, Nil{})), c),
      Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
        Ct.Cert.first(levels, roots),
        S.PSet.is_subset(sd, S.PSet.from_list(sd,
          Ct.Cert.first(levels, roots)),
          S.PSet.from_list(sd, roots)))),
    Dc.Bool.and_right(
      S.PSet.is_subset(sd, S.PSet.from_list(sd, roots), c),
      Bool.and(Sp.Spec.closed(td, g, sd, c),
        Bool.and(Ct.Cert.same(sd, S.PSet.from_list(sd,
            Ct.Cert.concat(levels, Nil{})), c),
          Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
            Ct.Cert.first(levels, roots),
            S.PSet.is_subset(sd, S.PSet.from_list(sd,
              Ct.Cert.first(levels, roots)),
              S.PSet.from_list(sd, roots))))), ok))

# The last two conditions, reached by peeling the same conjunction.
law Cert.accepts_levels:
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +roots: List<&2, U32>
  for +levels: R.Levels
  for +c: S.PSet
  for +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool}
  {Ct.Cert.same(sd, S.PSet.from_list(sd,
    Ct.Cert.concat(levels, Nil{})), c) == True{} : Bool}

law Cert.accepts_layers:
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +roots: List<&2, U32>
  for +levels: R.Levels
  for +c: S.PSet
  for +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool}
  {Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
    Ct.Cert.first(levels, roots),
    S.PSet.is_subset(sd, S.PSet.from_list(sd,
      Ct.Cert.first(levels, roots)),
      S.PSet.from_list(sd, roots))) == True{} : Bool}

# The conjunction with its first two conditions peeled off.
law Cert.tail2:
  for +td: Nat
  for +g: G.Graph()
  for +sd: Nat
  for +roots: List<&2, U32>
  for +levels: R.Levels
  for +c: S.PSet
  for +ok: {Ct.Cert.check(td, g, sd, roots, levels, c) == True{} : Bool}
  {Bool.and(Ct.Cert.same(sd, S.PSet.from_list(sd,
        Ct.Cert.concat(levels, Nil{})), c),
      Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
        Ct.Cert.first(levels, roots),
        S.PSet.is_subset(sd, S.PSet.from_list(sd,
          Ct.Cert.first(levels, roots)),
          S.PSet.from_list(sd, roots)))) == True{} : Bool}

def Cert.tail2(td, g, sd, roots, levels, c, ok):
  Dc.Bool.and_right(Sp.Spec.closed(td, g, sd, c),
    Bool.and(Ct.Cert.same(sd, S.PSet.from_list(sd,
        Ct.Cert.concat(levels, Nil{})), c),
      Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
        Ct.Cert.first(levels, roots),
        S.PSet.is_subset(sd, S.PSet.from_list(sd,
          Ct.Cert.first(levels, roots)),
          S.PSet.from_list(sd, roots)))),
    Dc.Bool.and_right(
      S.PSet.is_subset(sd, S.PSet.from_list(sd, roots), c),
      Bool.and(Sp.Spec.closed(td, g, sd, c),
        Bool.and(Ct.Cert.same(sd, S.PSet.from_list(sd,
        Ct.Cert.concat(levels, Nil{})), c),
      Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
        Ct.Cert.first(levels, roots),
        S.PSet.is_subset(sd, S.PSet.from_list(sd,
          Ct.Cert.first(levels, roots)),
          S.PSet.from_list(sd, roots))))), ok))

def Cert.accepts_levels(td, g, sd, roots, levels, c, ok):
  Dc.Bool.and_left(Ct.Cert.same(sd, S.PSet.from_list(sd,
    Ct.Cert.concat(levels, Nil{})), c),
    Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
    Ct.Cert.first(levels, roots),
    S.PSet.is_subset(sd, S.PSet.from_list(sd,
      Ct.Cert.first(levels, roots)),
      S.PSet.from_list(sd, roots))),
    Cert.tail2(td, g, sd, roots, levels, c, ok))

def Cert.accepts_layers(td, g, sd, roots, levels, c, ok):
  Dc.Bool.and_right(Ct.Cert.same(sd, S.PSet.from_list(sd,
    Ct.Cert.concat(levels, Nil{})), c),
    Ct.Cert.layers_ok(td, g, Ct.Cert.rest(levels),
    Ct.Cert.first(levels, roots),
    S.PSet.is_subset(sd, S.PSet.from_list(sd,
      Ct.Cert.first(levels, roots)),
      S.PSet.from_list(sd, roots))),
    Cert.tail2(td, g, sd, roots, levels, c, ok))
