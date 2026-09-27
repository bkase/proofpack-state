# proofs/machine.bend -- a failure the evaluator notices is a failure it
# reports.
#
# `closure/reach.bend` returns `done = False` when its budget runs out, and
# says the caller must report that: SPEC 3.3 is explicit that an unfinished
# traversal is never dressed up as a successful result. The evaluator is an
# explicit machine -- a control word, a stack of frames and one tail call per
# step -- and it reacts to an unfinished traversal by emptying its own stack,
# which stops it at once.
#
# Stopping at once is not the same as failing. The machine's accepting state
# is "no frames left", so emptying the stack lands on exactly the state that
# reports success; what makes it a failure is the flag the machine threads
# alongside. This law is that the flag cannot be lost: once it is `False{}`,
# no continuation of the machine reports `ok`.
#
# The law is worth having because the alternative is invisible. A truncated
# closure is a *smaller* answer, not a malformed one, and every consumer
# downstream would read it as a complete one.

import Base
import ./eq.bend as E
import ../core/set.bend as S
import ../index/source.bend as Idx
import ../query/ast.bend as A
import ../spec/query.bend as Den
import ../closure/reach.bend as R
import ../query/eval.bend as Q

law Mach.failure_is_reported:
  for +fuel: Nat
  for +src: Idx.Source
  for +c: Q.Ctl
  for +k: List<&2, Q.Frame>
  {Q.Val.ok(Q.Ev.go(fuel, src, c, k, False{})) == False{} : Bool}

def Mach.failure_is_reported(fuel, src, c, k):
  match fuel:
    case 0n:
      {==}
    case 1n+g:
      match c:
        case Q.CVal{v}:
          match k:
            case Nil{}:
              {==}
            case Con{f, rest}:
              match f:
                case Q.FRight{op, rhs}:
                  Mach.failure_is_reported(g, src, Q.CEval{rhs},
                    Con{Q.FComb{op, v}, rest})
                case Q.FComb{op, lhs}:
                  Mach.failure_is_reported(g, src,
                    Q.CVal{Q.Ev.apply(lhs, v, op)}, rest)
                case Q.FFilter{kind}:
                  Mach.failure_is_reported(g, src,
                    Q.CVal{Den.Den.filter(src, kind, v)}, rest)
                case Q.FReach{policy}:
                  Mach.failure_is_reported(g, src,
                    Q.CVal{R.Reach.seen(20n,
                      R.Reach.closure(Idx.Source.n(src), 32n,
                        Idx.Source.graph(src, policy), 20n,
                        S.PSet.to_list(20n, v)))},
                    Q.Ev.reach.stack(R.Reach.done(20n,
                      R.Reach.closure(Idx.Source.n(src), 32n,
                        Idx.Source.graph(src, policy), 20n,
                        S.PSet.to_list(20n, v))), rest))
        case Q.CEval{e}:
          match e:
            case A.EEmpty{}:
              Mach.failure_is_reported(g, src,
                Q.CVal{S.PSet.empty()}, k)
            case A.EFull{}:
              Mach.failure_is_reported(g, src,
                Q.CVal{Den.Den.universe(Idx.Source.n(src))}, k)
            case A.ELit{set}:
              Mach.failure_is_reported(g, src, Q.CVal{set}, k)
            case A.EUnion{a, b}:
              Mach.failure_is_reported(g, src, Q.CEval{a},
                Con{Q.FRight{0n, b}, k})
            case A.EInter{a, b}:
              Mach.failure_is_reported(g, src, Q.CEval{a},
                Con{Q.FRight{1n, b}, k})
            case A.EDiff{a, b}:
              Mach.failure_is_reported(g, src, Q.CEval{a},
                Con{Q.FRight{2n, b}, k})
            case A.EReach{policy, a}:
              Mach.failure_is_reported(g, src, Q.CEval{a},
                Con{Q.FReach{policy}, k})
            case A.EFilter{kind, a}:
              Mach.failure_is_reported(g, src, Q.CEval{a},
                Con{Q.FFilter{kind}, k})

# ---------------------------------------------------------------------------
# Q-03, the half that is about the machine.
#
# SPEC 3.6's compiler contract is `observe(execute(compile(W, q))) = [[q]]_W`.
# Three things stand between the evaluator and that: the rewrite pass in
# front of it (Q-01), reachability being computed by the frontier traversal
# rather than the specification iteration (C-02), and the evaluator being an
# explicit machine rather than a fold.
#
# The third is the one nobody else is blocked on, and it is the one this
# release introduced for a reason that has nothing to do with semantics: two
# non-tail self-calls in one def overrun the runtime's frame limit, so
# evaluation is a control word, a stack of frames and one tail call per step.
# `Ev.direct` is the fold that could not be written, and `Ev.unwind` says
# what a stack of frames means. The law is that the machine computes the
# fold -- so the shape the runtime forced is not a semantic choice.

def Ev.direct(+src: Idx.Source, e: A.SetExpr) -> S.PSet:
  match e:
    case A.EEmpty{}:
      S.PSet.empty()
    case A.EFull{}:
      Den.Den.universe(Idx.Source.n(src))
    case A.ELit{set}:
      set
    case A.EUnion{a, b}:
      Q.Ev.apply(Ev.direct(src, a), Ev.direct(src, b), 0n)
    case A.EInter{a, b}:
      Q.Ev.apply(Ev.direct(src, a), Ev.direct(src, b), 1n)
    case A.EDiff{a, b}:
      Q.Ev.apply(Ev.direct(src, a), Ev.direct(src, b), 2n)
    case A.EReach{policy, a}:
      R.Reach.seen(20n, R.Reach.closure(Idx.Source.n(src), 32n,
        Idx.Source.graph(src, policy), 20n,
        S.PSet.to_list(20n, Ev.direct(src, a))))
    case A.EFilter{kind, a}:
      Den.Den.filter(src, kind, Ev.direct(src, a))

def Ev.unwind(+src: Idx.Source, k: List<&2, Q.Frame>, v: S.PSet) -> S.PSet:
  match k:
    case Nil{}:
      v
    case Con{f, rest}:
      match f:
        case Q.FRight{op, rhs}:
          Ev.unwind(src, rest, Q.Ev.apply(v, Ev.direct(src, rhs), op))
        case Q.FComb{op, lhs}:
          Ev.unwind(src, rest, Q.Ev.apply(lhs, v, op))
        case Q.FFilter{kind}:
          Ev.unwind(src, rest, Den.Den.filter(src, kind, v))
        case Q.FReach{policy}:
          Ev.unwind(src, rest, R.Reach.seen(20n,
            R.Reach.closure(Idx.Source.n(src), 32n,
              Idx.Source.graph(src, policy), 20n, S.PSet.to_list(20n, v))))

def Ev.state(+src: Idx.Source, c: Q.Ctl, k: List<&2, Q.Frame>) -> S.PSet:
  match c:
    case Q.CVal{v}:
      Ev.unwind(src, k, v)
    case Q.CEval{e}:
      Ev.unwind(src, k, Ev.direct(src, e))

law Mach.computes_the_fold:
  for +fuel: Nat
  for +src: Idx.Source
  for +c: Q.Ctl
  for +k: List<&2, Q.Frame>
  for +ok: Bool
  for +good: {Q.Val.ok(Q.Ev.go(fuel, src, c, k, ok)) == True{} : Bool}
  {Q.Val.set(Q.Ev.go(fuel, src, c, k, ok)) == Ev.state(src, c, k) : S.PSet}

# The accepting state answers the value it was holding.
law Mach.done_set:
  for +v: S.PSet
  for +ok: Bool
  {Q.Val.set(Q.Ev.done(v, ok)) == v : S.PSet}

law Mach.absurd:
  for -A: Type
  for +good: {False{} == True{} : Bool}
  A

# If the traversal did not finish, the flag is gone and the machine cannot
# have reported `ok` -- so a machine that did report `ok` ran a traversal
# that finished. This is what lets the step below be an ordinary induction
# instead of a case split the recursion cannot express.
def Mach.done_set(v, ok):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Mach.absurd(A, good):
  E.Bool.noconf(A, good)

law Bool.and_true_r:
  for +p: Bool
  {Bool.and(p, True{}) == p : Bool}

def Bool.and_true_r(p):
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

# The traversal step. The induction hypothesis comes in as an argument and
# is used exactly once, which is what an affine value allows: the case where
# the traversal did not finish does not need it, because there the machine
# cannot have reported `ok` at all.
law Mach.reach_step:
  for +g: Nat
  for +src: Idx.Source
  for +seen: S.PSet
  for +rest: List<&2, Q.Frame>
  for +fin: Bool
  for +ok: Bool
  for ih: {Q.Val.ok(Q.Ev.go(g, src, Q.CVal{seen}, rest, ok))
      == True{} : Bool} ->
    {Q.Val.set(Q.Ev.go(g, src, Q.CVal{seen}, rest, ok))
      == Ev.unwind(src, rest, seen) : S.PSet}
  for +good: {Q.Val.ok(Q.Ev.go(g, src, Q.CVal{seen},
    Q.Ev.reach.stack(fin, rest), Bool.and(ok, fin))) == True{} : Bool}
  {Q.Val.set(Q.Ev.go(g, src, Q.CVal{seen},
      Q.Ev.reach.stack(fin, rest), Bool.and(ok, fin)))
    == Ev.unwind(src, rest, seen) : S.PSet}

law Mach.flag_absurd.k:
  for +g: Nat
  for +src: Idx.Source
  for +seen: S.PSet
  for +rest: List<&2, Q.Frame>
  for +good: {Q.Val.ok(Q.Ev.go(g, src, Q.CVal{seen}, rest, False{}))
    == True{} : Bool}
  {False{} == True{} : Bool}

def Mach.flag_absurd.k(g, src, seen, rest, good):
  Equal.trans(Bool, False{},
    Q.Val.ok(Q.Ev.go(g, src, Q.CVal{seen}, rest, False{})), True{},
    E.Bool.sym(Q.Val.ok(Q.Ev.go(g, src, Q.CVal{seen}, rest, False{})),
      False{}, Mach.failure_is_reported(g, src, Q.CVal{seen}, rest)),
    good)

law Mach.reach_flag:
  for +g: Nat
  for +src: Idx.Source
  for +seen: S.PSet
  for +rest: List<&2, Q.Frame>
  for +fin: Bool
  for +ok: Bool
  for +good: {Q.Val.ok(Q.Ev.go(g, src, Q.CVal{seen},
    Q.Ev.reach.stack(fin, rest), Bool.and(ok, fin))) == True{} : Bool}
  {fin == True{} : Bool}

law Mach.flag_absurd:
  for +g: Nat
  for +src: Idx.Source
  for +seen: S.PSet
  for +good: {Q.Val.ok(Q.Ev.go(g, src, Q.CVal{seen}, Nil{}, False{}))
    == True{} : Bool}
  {False{} == True{} : Bool}

def Mach.flag_absurd(g, src, seen, good):
  Equal.trans(Bool, False{},
    Q.Val.ok(Q.Ev.go(g, src, Q.CVal{seen}, Nil{}, False{})), True{},
    E.Bool.sym(Q.Val.ok(Q.Ev.go(g, src, Q.CVal{seen}, Nil{}, False{})),
      False{}, Mach.failure_is_reported(g, src, Q.CVal{seen}, Nil{})),
    good)

def Mach.reach_step(g, src, seen, rest, fin, ok, ih, good):
  match fin:
    case True{}:
      match ok:
        case True{}:
          ih(good)
        case False{}:
          Mach.absurd({Q.Val.set(Q.Ev.go(g, src, Q.CVal{seen}, rest,
              False{})) == Ev.unwind(src, rest, seen) : S.PSet},
            Mach.flag_absurd.k(g, src, seen, rest, good))
    case False{}:
      match ok:
        case True{}:
          Mach.absurd({Q.Val.set(Q.Ev.go(g, src, Q.CVal{seen}, Nil{},
              False{})) == Ev.unwind(src, rest, seen) : S.PSet},
            Mach.flag_absurd(g, src, seen, good))
        case False{}:
          Mach.absurd({Q.Val.set(Q.Ev.go(g, src, Q.CVal{seen}, Nil{},
              False{})) == Ev.unwind(src, rest, seen) : S.PSet},
            Mach.flag_absurd(g, src, seen, good))

def Mach.reach_flag(g, src, seen, rest, fin, ok, good):
  match fin:
    case True{}:
      {==}
    case False{}:
      match ok:
        case True{}:
          Mach.absurd({False{} == True{} : Bool},
            Mach.flag_absurd(g, src, seen, good))
        case False{}:
          Mach.absurd({False{} == True{} : Bool},
            Mach.flag_absurd(g, src, seen, good))

def Mach.computes_the_fold(fuel, src, c, k, ok, good):
  match fuel:
    case 0n:
      Mach.absurd({Q.Val.set(Q.Ev.go(0n, src, c, k, ok))
        == Ev.state(src, c, k) : S.PSet}, good)
    case 1n+g:
      match c:
        case Q.CVal{v}:
          match k:
            case Nil{}:
              Mach.done_set(v, ok)
            case Con{f, rest}:
              match f:
                case Q.FRight{op, rhs}:
                  Mach.computes_the_fold(g, src, Q.CEval{rhs},
                    Con{Q.FComb{op, v}, rest}, ok, good)
                case Q.FComb{op, lhs}:
                  Mach.computes_the_fold(g, src,
                    Q.CVal{Q.Ev.apply(lhs, v, op)}, rest, ok, good)
                case Q.FFilter{kind}:
                  Mach.computes_the_fold(g, src,
                    Q.CVal{Den.Den.filter(src, kind, v)}, rest, ok, good)
                case Q.FReach{policy}:
                  Mach.reach_step(g, src,
                    R.Reach.seen(20n,
                      R.Reach.closure(Idx.Source.n(src), 32n,
                        Idx.Source.graph(src, policy), 20n,
                        S.PSet.to_list(20n, v))),
                    rest,
                    R.Reach.done(20n,
                      R.Reach.closure(Idx.Source.n(src), 32n,
                        Idx.Source.graph(src, policy), 20n,
                        S.PSet.to_list(20n, v))), ok,
                    h => Mach.computes_the_fold(g, src,
                      Q.CVal{R.Reach.seen(20n,
                      R.Reach.closure(Idx.Source.n(src), 32n,
                        Idx.Source.graph(src, policy), 20n,
                        S.PSet.to_list(20n, v)))},
                      rest, ok, h),
                    good)
        case Q.CEval{e}:
          match e:
            case A.EEmpty{}:
              Mach.computes_the_fold(g, src, Q.CVal{S.PSet.empty()}, k,
                ok, good)
            case A.EFull{}:
              Mach.computes_the_fold(g, src,
                Q.CVal{Den.Den.universe(Idx.Source.n(src))}, k, ok, good)
            case A.ELit{set}:
              Mach.computes_the_fold(g, src, Q.CVal{set}, k, ok, good)
            case A.EUnion{a, b}:
              Mach.computes_the_fold(g, src, Q.CEval{a},
                Con{Q.FRight{0n, b}, k}, ok, good)
            case A.EInter{a, b}:
              Mach.computes_the_fold(g, src, Q.CEval{a},
                Con{Q.FRight{1n, b}, k}, ok, good)
            case A.EDiff{a, b}:
              Mach.computes_the_fold(g, src, Q.CEval{a},
                Con{Q.FRight{2n, b}, k}, ok, good)
            case A.EReach{policy, a}:
              Mach.computes_the_fold(g, src, Q.CEval{a},
                Con{Q.FReach{policy}, k}, ok, good)
            case A.EFilter{kind, a}:
              Mach.computes_the_fold(g, src, Q.CEval{a},
                Con{Q.FFilter{kind}, k}, ok, good)

# The machine, on an expression: it computes the fold.
law Mach.set_computes:
  for +src: Idx.Source
  for +e: A.SetExpr
  for +good: {Q.Val.ok(Q.Ev.set(src, e)) == True{} : Bool}
  {Q.Val.set(Q.Ev.set(src, e)) == Ev.direct(src, e) : S.PSet}

def Mach.set_computes(src, e, good):
  Mach.computes_the_fold(1n+Nat.mul(4n, Q.Ev.size(e)), src, Q.CEval{e},
    Nil{}, True{}, good)
