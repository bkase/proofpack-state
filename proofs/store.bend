# proofs/store.bend -- what accepting a stored generation means (law D-01).
#
# A store file is untrusted input. SPEC 6.5 requires bounds, node references
# and universe bindings to be validated on load and says plainly that a
# checksum is not a substitute; `index/store.bend` validates the magic line,
# the declared format, the declared object count against the objects actually
# present, each object id's hex width, and each successor index against the
# declared universe, and answers `CorruptIndex` rather than a wrong answer.
#
# Two things about that are worth stating as laws rather than as prose.
#
# The first is the count, which is the check a truncated or padded file trips
# and the one `tools/differential.sh` corrupts: a decode that is accepted
# declared exactly as many objects as the file holds. The second is that a
# rejection is never silent: a field-level check failing sets a flag deep
# inside a fold with no message, and `Store.decode.named` is what turns that
# into a stable machine-readable class (SPEC 9.3). Accepting a file with no
# error, or rejecting it with no reason, are the two ways a loader can be
# quietly wrong, and neither can happen.

import Base
import ./eq.bend as E
import ../index/store.bend as St

def Store.ok_at(+d: St.Dec, c: Bool) -> Bool:
  St.Dec.ok(St.Store.decode.named(St.Store.decode.count(d, c)))

def Store.ok_named_at(+d: St.Dec, b: Bool) -> Bool:
  St.Dec.ok(St.Store.decode.named.go(d, b))

law Store.count_fail_not_ok:
  for +d: St.Dec
  {Store.ok_at(d, False{}) == False{} : Bool}

def Store.count_fail_not_ok(d):
  match d:
    case St.D{uni, metas, rows, ext, roots, n, seen, dok, err}:
      {==}

law Store.accepted_count:
  for +c: Bool
  for +d: St.Dec
  for +ec: {c == Nat.is_eq(St.Dec.n(d), St.Dec.seen(d)) : Bool}
  for +ok: {St.Dec.ok(St.Store.decode.fin(d)) == True{} : Bool}
  {Nat.is_eq(St.Dec.n(d), St.Dec.seen(d)) == True{} : Bool}

def Store.accepted_count(c, d, ec, ok):
  match c:
    case True{}:
      E.Bool.sym(True{}, Nat.is_eq(St.Dec.n(d), St.Dec.seen(d)), ec)
    case False{}:
      E.Bool.noconf({Nat.is_eq(St.Dec.n(d), St.Dec.seen(d))
        == True{} : Bool},
        Equal.trans(Bool, False{}, Store.ok_at(d, False{}), True{},
          E.Bool.sym(Store.ok_at(d, False{}), False{},
            Store.count_fail_not_ok(d)),
          Equal.trans(Bool, Store.ok_at(d, False{}),
            Store.ok_at(d, Nat.is_eq(St.Dec.n(d), St.Dec.seen(d))),
            True{},
            Equal.cong(Bool, Bool, Store.ok_at(d), False{},
              Nat.is_eq(St.Dec.n(d), St.Dec.seen(d)), ec),
            ok)))

law Store.fail_reports:
  for +d: St.Dec
  {String.is_empty(St.Dec.err(St.Store.decode.named.go(d, True{})))
    == False{} : Bool}

def Store.fail_reports(d):
  match d:
    case St.D{uni, metas, rows, ext, roots, n, seen, dok, err}:
      {==}

law Store.rejection_is_reported:
  for +u: Bool
  for +d: St.Dec
  for +eu: {u == Bool.and(Bool.not(St.Dec.ok(d)),
    String.is_empty(St.Dec.err(d))) : Bool}
  for +no: {St.Dec.ok(St.Store.decode.named(d)) == False{} : Bool}
  {String.is_empty(St.Dec.err(St.Store.decode.named(d)))
    == False{} : Bool}

# The `named` step left the decode alone, so it was already rejected with a
# message -- otherwise the conjunction it tests would have been `True{}`.
law Store.not_ok_empty:
  for +dok: Bool
  for +empty: Bool
  for +eu: {Bool.and(Bool.not(dok), empty) == False{} : Bool}
  for +no: {dok == False{} : Bool}
  {empty == False{} : Bool}

def Store.not_ok_empty(dok, empty, eu, no):
  match dok:
    case True{}:
      E.Bool.noconf.r({empty == False{} : Bool}, no)
    case False{}:
      eu

def Store.rejection_is_reported(u, d, eu, no):
  match u:
    case True{}:
      %eu : {String.is_empty(St.Dec.err(St.Store.decode.named.go(d, _)))
        == False{} : Bool}
      Store.fail_reports(d)
    case False{}:
      %eu : {String.is_empty(St.Dec.err(St.Store.decode.named.go(d, _)))
        == False{} : Bool}
      Store.not_ok_empty(St.Dec.ok(d), String.is_empty(St.Dec.err(d)),
        E.Bool.sym(False{}, Bool.and(Bool.not(St.Dec.ok(d)),
          String.is_empty(St.Dec.err(d))), eu),
        Equal.trans(Bool, Store.ok_named_at(d, False{}),
          Store.ok_named_at(d, Bool.and(Bool.not(St.Dec.ok(d)),
            String.is_empty(St.Dec.err(d)))), False{},
          Equal.cong(Bool, Bool, Store.ok_named_at(d), False{},
            Bool.and(Bool.not(St.Dec.ok(d)),
              String.is_empty(St.Dec.err(d))), eu),
          no))
