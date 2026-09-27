# cli/args.bend -- command line parsing.
#
# `--key value` pairs and bare positionals. A key may repeat (`--root` takes
# several), so lookups come in two shapes: `Args.values` for every value in
# the order they were given, and `Args.one` for the last.
#
# Nothing here interprets a value. Resolving a ref to an object id, or a mode
# name to a policy, happens afterwards and can fail with a named error class:
# an unparsed flag never becomes a default.
#
# The loop is one self-recursive def over a `PStep`, because Bend forbids
# mutual recursion and a `match` cannot scrutinize a computed value. The fuel
# is the argument count, so it is always enough.

import Base
import ../core/count.bend as C

type Arg is Data:
  Flag{key: String, val: String}
  Pos{val: String}

def Args() -> Data:
  List<&2, Arg>

type PStep is Data:
  PDone{}
  PTake{arg: Arg, rest: List<&2, String>}

def Args.dup(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{h, Args.dup(t)}

def Args.is_flag(+s: String) -> Bool:
  String.starts_with(s, "--")

def Args.strip(+s: String) -> String:
  String.drop(s, 2n)

def Args.head(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      h

def Args.tail(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

# A flag takes the next token as its value, unless that token is itself a
# flag or the arguments ran out -- then it is a switch with an empty value.
def Args.step.val(key: String, +t: List<&2, String>, +v: String,
  stop: Bool) -> PStep:
  match stop:
    case True{}:
      PTake{Flag{key, ""}, t}
    case False{}:
      PTake{Flag{key, v}, Args.tail(t)}

def Args.step.kind(+h: String, +t: List<&2, String>, flag: Bool) -> PStep:
  match flag:
    case False{}:
      PTake{Pos{h}, t}
    case True{}:
      +v = Args.head(t)
      Args.step.val(Args.strip(h), t, v,
        Bool.or(List.is_empty(&2, String, t), Args.is_flag(v)))

def Args.step.pick(+xs: List<&2, String>, empty: Bool) -> PStep:
  match empty:
    case True{}:
      PDone{}
    case False{}:
      +h = Args.head(xs)
      Args.step.kind(h, Args.tail(xs), Args.is_flag(h))

def Args.step(+xs: List<&2, String>) -> PStep:
  Args.step.pick(xs, List.is_empty(&2, String, xs))

def Args.parse(+fuel: Nat, acc: Args, s: PStep) -> Args:
  match fuel:
    case 0n:
      List.reverse(&2, Arg, acc)
    case 1n+g:
      match s:
        case PDone{}:
          List.reverse(&2, Arg, acc)
        case PTake{a, rest}:
          +r = rest
          Args.parse(g, Con{a, acc}, Args.step(r))

def Args.of(xs: List<&1, String>) -> Args:
  +ys = Args.dup(xs)
  Args.parse(1n+List.length(&2, String, ys), Nil{}, Args.step(ys))

# ---------------------------------------------------------------------------
# Lookups.
# ---------------------------------------------------------------------------

def Args.all.pick(val: String, acc: List<&2, String>, hit: Bool) ->
  List<&2, String>:
  match hit:
    case False{}:
      acc
    case True{}:
      Con{val, acc}

def Args.all.push(a: Arg, +key: String, acc: List<&2, String>) ->
  List<&2, String>:
  match a:
    case Pos{val}:
      acc
    case Flag{k, val}:
      Args.all.pick(val, acc, String.eq(k, key))

def Args.all(ar: Args, +key: String, acc: List<&2, String>) ->
  List<&2, String>:
  match ar:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{a, t}:
      Args.all(t, key, Args.all.push(a, key, acc))

def Args.values(+ar: Args, +key: String) -> List<&2, String>:
  Args.all(ar, key, Nil{})

def Args.one.un(m: Maybe<&2, String>, dflt: String) -> String:
  match m:
    case None{}:
      dflt
    case Some{x}:
      x

def Args.one(+ar: Args, +key: String, dflt: String) -> String:
  Args.one.un(List.last(&2, String, Args.values(ar, key)), dflt)

def Args.has(+ar: Args, +key: String) -> Bool:
  Bool.not(List.is_empty(&2, String, Args.values(ar, key)))

def Args.positional.push(a: Arg, acc: List<&2, String>) ->
  List<&2, String>:
  match a:
    case Flag{k, val}:
      acc
    case Pos{val}:
      Con{val, acc}

def Args.positional(ar: Args, acc: List<&2, String>) -> List<&2, String>:
  match ar:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{a, t}:
      Args.positional(t, Args.positional.push(a, acc))

def Args.words(+ar: Args) -> List<&2, String>:
  Args.positional(ar, Nil{})

def Args.word.un(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      ""
    case Some{x}:
      x

def Args.word(+ar: Args, n: Nat) -> String:
  Args.word.un(List.get(&2, String, Args.words(ar), n))
