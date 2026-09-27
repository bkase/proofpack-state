# proofs/batch.bend -- Q-04, the half that is about order.
#
# `pp git matrix` answers one cell per distinct inventory and points every
# duplicate at the cell it shares with. The obligation has two halves: that
# deduplicating changes no answer, and that restoring caller positions
# changes no order. This file is the second.
#
# `Cmd.matrix.rows` builds the output with an accumulator and reverses once
# at the end, which is the shape that makes the order question worth asking
# at all -- the rows are produced in reverse and put back. `Rows.spec` is the
# same walk written the obvious way, in order and without an accumulator, and
# the law says the two agree. So a cell's position in the output is its
# position in the input, whatever the deduplication did to its answer.

import Base
import ./eq.bend as E
import ../core/set.bend as S
import ../cli/main.bend as M

def Rows.spec(+cx: M.Ctx, +k: S.PSet, cells: List<&2, M.Cell>,
  +done: List<&2, M.Answered>) -> List<&2, String>:
  match cells:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      +cc = c
      +ans = M.Cmd.matrix.answer_of(cx, k, cc,
        M.Cmd.matrix.seen(done, M.Cell.same_as(cc)))
      Con{M.Cmd.matrix.wrap(cc, ans),
        Rows.spec(cx, k, t, Con{M.An{M.Cell.name(cc), ans}, done})}

# ---------------------------------------------------------------------------
# The accumulator, put back in order.
# ---------------------------------------------------------------------------

law List.append_nil:
  for -A: Data
  for +xs: List<&2, A>
  {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}

def List.append_nil(A, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %E.List.sym(A, List.append(&2, A, t, Nil{}), t,
        List.append_nil(A, t))
        : {Con{h, _} == Con{h, t} : List<&2, A>}
      {==}

law List.append_assoc:
  for -A: Data
  for +xs: List<&2, A>
  for +ys: List<&2, A>
  for +zs: List<&2, A>
  {List.append(&2, A, List.append(&2, A, xs, ys), zs)
    == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}

def List.append_assoc(A, xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %E.List.sym(A,
        List.append(&2, A, List.append(&2, A, t, ys), zs),
        List.append(&2, A, t, List.append(&2, A, ys, zs)),
        List.append_assoc(A, t, ys, zs))
        : {Con{h, _} == Con{h, List.append(&2, A, t,
            List.append(&2, A, ys, zs))} : List<&2, A>}
      {==}

law List.reverse_go:
  for -A: Data
  for +xs: List<&2, A>
  for +acc: List<&2, A>
  {List.reverse.go(&2, A, xs, acc)
    == List.append(&2, A, List.reverse.go(&2, A, xs, Nil{}), acc)
    : List<&2, A>}

def List.reverse_go(A, xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %E.List.sym(A,
        List.reverse.go(&2, A, t, Con{h, Nil{}}),
        List.append(&2, A, List.reverse.go(&2, A, t, Nil{}),
          Con{h, Nil{}}),
        List.reverse_go(A, t, Con{h, Nil{}}))
        : {List.reverse.go(&2, A, t, Con{h, acc})
          == List.append(&2, A, _, acc) : List<&2, A>}
      Equal.trans(List<&2, A>,
        List.reverse.go(&2, A, t, Con{h, acc}),
        List.append(&2, A, List.reverse.go(&2, A, t, Nil{}),
          Con{h, acc}),
        List.append(&2, A,
          List.append(&2, A, List.reverse.go(&2, A, t, Nil{}),
            Con{h, Nil{}}), acc),
        List.reverse_go(A, t, Con{h, acc}),
        E.List.sym(A,
          List.append(&2, A,
            List.append(&2, A, List.reverse.go(&2, A, t, Nil{}),
              Con{h, Nil{}}), acc),
          List.append(&2, A, List.reverse.go(&2, A, t, Nil{}),
            Con{h, acc}),
          List.append_assoc(A, List.reverse.go(&2, A, t, Nil{}),
            Con{h, Nil{}}, acc)))

# ---------------------------------------------------------------------------
# The rows, in the caller's order.
# ---------------------------------------------------------------------------

law Rows.in_order:
  for +cx: M.Ctx
  for +k: S.PSet
  for +cells: List<&2, M.Cell>
  for +done: List<&2, M.Answered>
  for +out: List<&2, String>
  {M.Cmd.matrix.rows(cx, k, cells, done, out)
    == List.append(&2, String, List.reverse(&2, String, out),
         Rows.spec(cx, k, cells, done)) : List<&2, String>}

def Rows.answer(+cx: M.Ctx, +k: S.PSet, +c: M.Cell,
  +done: List<&2, M.Answered>) -> String:
  M.Cmd.matrix.answer_of(cx, k, c,
    M.Cmd.matrix.seen(done, M.Cell.same_as(c)))

# One row moved from the accumulator to the front of the rest.
law Rows.shift:
  for +w: String
  for +out: List<&2, String>
  for +rest: List<&2, String>
  {List.append(&2, String, List.reverse(&2, String, Con{w, out}), rest)
    == List.append(&2, String, List.reverse(&2, String, out),
         Con{w, rest}) : List<&2, String>}

def Rows.shift(w, out, rest):
  %E.List.sym(String,
    List.reverse.go(&2, String, out, Con{w, Nil{}}),
    List.append(&2, String, List.reverse.go(&2, String, out, Nil{}),
      Con{w, Nil{}}),
    List.reverse_go(String, out, Con{w, Nil{}}))
    : {List.append(&2, String, _, rest)
      == List.append(&2, String, List.reverse(&2, String, out),
           Con{w, rest}) : List<&2, String>}
  List.append_assoc(String, List.reverse.go(&2, String, out, Nil{}),
    Con{w, Nil{}}, rest)

def Rows.in_order(cx, k, cells, done, out):
  match cells:
    case Nil{}:
      E.List.sym(String, List.append(&2, String,
        List.reverse(&2, String, out), Nil{}),
        List.reverse(&2, String, out),
        List.append_nil(String, List.reverse(&2, String, out)))
    case Con{c, t}:
      Equal.trans(List<&2, String>,
        M.Cmd.matrix.rows(cx, k, t,
          Con{M.An{M.Cell.name(c), Rows.answer(cx, k, c, done)}, done},
          Con{M.Cmd.matrix.wrap(c, Rows.answer(cx, k, c, done)), out}),
        List.append(&2, String,
          List.reverse(&2, String,
            Con{M.Cmd.matrix.wrap(c, Rows.answer(cx, k, c, done)), out}),
          Rows.spec(cx, k, t,
            Con{M.An{M.Cell.name(c), Rows.answer(cx, k, c, done)}, done})),
        List.append(&2, String, List.reverse(&2, String, out),
          Rows.spec(cx, k, Con{c, t}, done)),
        Rows.in_order(cx, k, t,
          Con{M.An{M.Cell.name(c), Rows.answer(cx, k, c, done)}, done},
          Con{M.Cmd.matrix.wrap(c, Rows.answer(cx, k, c, done)), out}),
        Rows.shift(M.Cmd.matrix.wrap(c, Rows.answer(cx, k, c, done)), out,
          Rows.spec(cx, k, t,
            Con{M.An{M.Cell.name(c), Rows.answer(cx, k, c, done)},
              done})))

law Rows.one_per_cell:
  for +cx: M.Ctx
  for +k: S.PSet
  for +cells: List<&2, M.Cell>
  for +done: List<&2, M.Answered>
  {List.length(&2, String, Rows.spec(cx, k, cells, done))
    == List.length(&2, M.Cell, cells) : Nat}

def Rows.one_per_cell(cx, k, cells, done):
  match cells:
    case Nil{}:
      {==}
    case Con{c, t}:
      %E.Nat.sym(List.length(&2, String, Rows.spec(cx, k, t,
          Con{M.An{M.Cell.name(c), Rows.answer(cx, k, c, done)}, done})),
        List.length(&2, M.Cell, t),
        Rows.one_per_cell(cx, k, t,
          Con{M.An{M.Cell.name(c), Rows.answer(cx, k, c, done)}, done}))
        : {1n+_ == 1n+List.length(&2, M.Cell, t) : Nat}
      {==}

law Rows.from_empty:
  for +cx: M.Ctx
  for +k: S.PSet
  for +cells: List<&2, M.Cell>
  for +done: List<&2, M.Answered>
  {M.Cmd.matrix.rows(cx, k, cells, done, Nil{})
    == Rows.spec(cx, k, cells, done) : List<&2, String>}

def Rows.from_empty(cx, k, cells, done):
  Rows.in_order(cx, k, cells, done, Nil{})

# ---------------------------------------------------------------------------
# And what a reused answer is.
#
# `Cmd.matrix.lookup` walks the answers already produced with an accumulator
# that stops the walk once it has hit. `Rows.found` is the same search
# written as a find-first, and the law says they agree -- so the answer a
# duplicate cell reuses is the recorded answer of the first cell whose name
# it points at, and not something the deduplication invented.
# ---------------------------------------------------------------------------

def Rows.found.pick(ans: String, rest: Maybe<&2, String>, hit: Bool) ->
  Maybe<&2, String>:
  match hit:
    case True{}:
      Some{ans}
    case False{}:
      rest

def Rows.found(done: List<&2, M.Answered>, +want: String) ->
  Maybe<&2, String>:
  match done:
    case Nil{}:
      None{}
    case Con{e, t}:
      +ee = e
      Rows.found.pick(M.Answered.answer(ee), Rows.found(t, want),
        String.eq(M.Answered.name(ee), want))

def Rows.head_hit(done: List<&2, M.Answered>, +want: String) -> Bool:
  match done:
    case Nil{}:
      False{}
    case Con{e, t}:
      String.eq(M.Answered.name(e), want)

def Rows.got_or(got: Maybe<&2, String>, rest: Maybe<&2, String>) ->
  Maybe<&2, String>:
  match got:
    case Some{x}:
      Some{x}
    case None{}:
      rest

law Rows.lookup_finds:
  for +done: List<&2, M.Answered>
  for +want: String
  for +got: Maybe<&2, String>
  for +hit: Bool
  for +eh: {hit == Rows.head_hit(done, want) : Bool}
  {M.Cmd.matrix.lookup(done, want, got)
    == Rows.got_or(got, Rows.found(done, want)) : Maybe<&2, String>}

law Rows.got_or_none:
  for +got: Maybe<&2, String>
  {got == Rows.got_or(got, None{}) : Maybe<&2, String>}

def Rows.got_or_none(got):
  match got:
    case Some{x}:
      {==}
    case None{}:
      {==}

def Rows.lookup_finds(done, want, got, hit, eh):
  match done:
    case Nil{}:
      Rows.got_or_none(got)
    case Con{e, t}:
      match got:
        case Some{x}:
          {==}
        case None{}:
          match hit:
            case True{}:
              %eh : {M.Cmd.matrix.lookup(t, want,
                  M.Cmd.matrix.hit(e, _))
                == Rows.found.pick(M.Answered.answer(e),
                     Rows.found(t, want), _) : Maybe<&2, String>}
              Rows.lookup_finds(t, want, Some{M.Answered.answer(e)},
                Rows.head_hit(t, want), {==})
            case False{}:
              %eh : {M.Cmd.matrix.lookup(t, want,
                  M.Cmd.matrix.hit(e, _))
                == Rows.found.pick(M.Answered.answer(e),
                     Rows.found(t, want), _) : Maybe<&2, String>}
              Rows.lookup_finds(t, want, None{},
                Rows.head_hit(t, want), {==})

law Rows.lookup_is_find:
  for +done: List<&2, M.Answered>
  for +want: String
  {M.Cmd.matrix.lookup(done, want, None{})
    == Rows.found(done, want) : Maybe<&2, String>}

def Rows.lookup_is_find(done, want):
  Rows.lookup_finds(done, want, None{}, Rows.head_hit(done, want), {==})
