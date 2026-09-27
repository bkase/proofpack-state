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
