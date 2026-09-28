# proofs/trieput.bend -- a write is seen only where it was written.
#
# `Trie.get` and `Trie.put` descend by the same comparisons, so what a key
# reaches is decided entirely by the sequence of branch bits it takes. Two
# keys that take the same bits reach the same node, whatever the trie holds;
# a key that takes a different bit at some level never meets the node another
# key's write rebuilt.
#
# That is all the identity table needs, and it is worth noting what it does
# *not* need: nothing here says two different keys take different paths. The
# injectivity proof cases on the paths rather than on the keys, so the
# arithmetic that would relate a key to its path never has to be written.

import Base
import ./eq.bend as E
import ./sublist.bend as Sp
import ../core/trie.bend as T

def Bool.ne(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      Bool.not(b)
    case False{}:
      b

# Do `x` and `y` take a different branch at some level of the descent?
def Trie.path_ne(+d: Nat, +h: U32, +x: U32, +y: U32) -> Bool:
  match d:
    case 0n:
      False{}
    case 1n+p:
      Bool.or(Bool.ne(U32.is_lt(x, h), U32.is_lt(y, h)),
        Trie.path_ne(p, U32.shr(h),
          T.Trie.rebase(U32.is_lt(x, h), h, x),
          T.Trie.rebase(U32.is_lt(y, h), h, y)))

law Bool.ne_off:
  for +a: Bool
  for +b: Bool
  for +z: {Bool.ne(a, b) == False{} : Bool}
  {a == b : Bool}

def Bool.ne_off(a, b, z):
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          z
    case False{}:
      match b:
        case True{}:
          E.Bool.noconf.r({False{} == True{} : Bool}, z)
        case False{}:
          {==}

law Trie.get_same_path:
  for -A: Data
  for +d: Nat
  for +t: T.Trie<A>
  for +h: U32
  for +x: U32
  for +y: U32
  for +pe: {Trie.path_ne(d, h, x, y) == False{} : Bool}
  {T.Trie.get(A, d, t, h, x) == T.Trie.get(A, d, t, h, y)
    : Maybe<&2, A>}

def Trie.get_same_path(A, d, t, h, x, y, pe):
  match d:
    case 0n:
      match t:
        case T.TGap{}:
          {==}
        case T.TVal{v}:
          {==}
        case T.TBr{lo, hi}:
          {==}
    case 1n+p:
      match t:
        case T.TGap{}:
          {==}
        case T.TVal{v}:
          {==}
        case T.TBr{lo, hi}:
          %Bool.ne_off(U32.is_lt(x, h), U32.is_lt(y, h),
              Sp.Bool.or_off_l(Bool.ne(U32.is_lt(x, h),
                U32.is_lt(y, h)),
                Trie.path_ne(p, U32.shr(h),
                  T.Trie.rebase(U32.is_lt(x, h), h, x),
                  T.Trie.rebase(U32.is_lt(y, h), h, y)), pe))
            : {T.Trie.get(A, p,
              T.Trie.pick(A, U32.is_lt(x, h), lo, hi), U32.shr(h),
              T.Trie.rebase(U32.is_lt(x, h), h, x))
              == T.Trie.get(A, p, T.Trie.pick(A, _, lo, hi),
                U32.shr(h),
                T.Trie.rebase(U32.is_lt(y, h), h, y))
              : Maybe<&2, A>}
          Trie.get_same_path(A, p,
            T.Trie.pick(A, U32.is_lt(x, h), lo, hi), U32.shr(h),
            T.Trie.rebase(U32.is_lt(x, h), h, x),
            T.Trie.rebase(U32.is_lt(y, h), h, y),
            Sp.Bool.or_off_r(Bool.ne(U32.is_lt(x, h),
              U32.is_lt(y, h)),
              Trie.path_ne(p, U32.shr(h),
                T.Trie.rebase(U32.is_lt(x, h), h, x),
                T.Trie.rebase(U32.is_lt(y, h), h, y)), pe))

law Trie.get_gap:
  for -A: Data
  for +d: Nat
  for +h: U32
  for +y: U32
  {T.Trie.get(A, d, T.TGap{}, h, y) == None{} : Maybe<&2, A>}

def Trie.get_gap(A, d, h, y):
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

law Trie.get_put_other:
  for -A: Data
  for +d: Nat
  for +t: T.Trie<A>
  for +h: U32
  for +x: U32
  for +y: U32
  for +v: A
  for +bx: Bool
  for +ebx: {bx == U32.is_lt(x, h) : Bool}
  for +by: Bool
  for +eby: {by == U32.is_lt(y, h) : Bool}
  for pe: {Trie.path_ne(d, h, x, y) == True{} : Bool}
  {T.Trie.get(A, d, T.Trie.put(A, d, t, h, x, v, bx), h, y)
    == T.Trie.get(A, d, t, h, y) : Maybe<&2, A>}

def Trie.gpo.tail(+p: Nat, +h: U32, +x: U32, +y: U32, +bx: Bool,
  +by: Bool,
  +ebx: {bx == U32.is_lt(x, h) : Bool},
  +eby: {by == U32.is_lt(y, h) : Bool},
  +pe: {Trie.path_ne(1n+p, h, x, y) == True{} : Bool})
  -> {Bool.or(Bool.ne(bx, by),
    Trie.path_ne(p, U32.shr(h), T.Trie.rebase(bx, h, x),
      T.Trie.rebase(by, h, y))) == True{} : Bool}:
  %E.Bool.sym(bx, U32.is_lt(x, h), ebx)
    : {Bool.or(Bool.ne(_, by),
      Trie.path_ne(p, U32.shr(h), T.Trie.rebase(_, h, x),
        T.Trie.rebase(by, h, y))) == True{} : Bool}
  %E.Bool.sym(by, U32.is_lt(y, h), eby)
    : {Bool.or(Bool.ne(U32.is_lt(x, h), _),
      Trie.path_ne(p, U32.shr(h),
        T.Trie.rebase(U32.is_lt(x, h), h, x),
        T.Trie.rebase(_, h, y))) == True{} : Bool}
  pe

def Trie.gpo.gap(-A: Data, +p: Nat, +t: T.Trie<A>, +h: U32, +x: U32,
  +y: U32, +v: A, +bx: Bool,
  +ebx: {bx == U32.is_lt(x, h) : Bool}, +by: Bool,
  +eby: {by == U32.is_lt(y, h) : Bool},
  +none: {T.Trie.get(A, 1n+p, t, h, y) == None{} : Maybe<&2, A>},
  +pe: {Trie.path_ne(1n+p, h, x, y) == True{} : Bool},
  ihT: {Trie.path_ne(p, U32.shr(h), x, y) == True{} : Bool} ->
    {T.Trie.get(A, p, T.Trie.put(A, p, T.TGap{}, U32.shr(h), x, v,
      U32.is_lt(x, U32.shr(h))), U32.shr(h), y)
      == T.Trie.get(A, p, T.TGap{}, U32.shr(h), y)
      : Maybe<&2, A>},
  ihF: {Trie.path_ne(p, U32.shr(h), U32.sub(x, h), U32.sub(y, h))
      == True{} : Bool} ->
    {T.Trie.get(A, p, T.Trie.put(A, p, T.TGap{}, U32.shr(h),
      U32.sub(x, h), v, U32.is_lt(U32.sub(x, h), U32.shr(h))),
      U32.shr(h), U32.sub(y, h))
      == T.Trie.get(A, p, T.TGap{}, U32.shr(h), U32.sub(y, h))
      : Maybe<&2, A>})
  -> {T.Trie.get(A, p, T.Trie.pick(A, U32.is_lt(y, h),
    T.Trie.pick(A, bx,
      T.Trie.put(A, p, T.TGap{}, U32.shr(h), x, v,
        U32.is_lt(x, U32.shr(h))), T.TGap{}),
    T.Trie.pick(A, bx, T.TGap{},
      T.Trie.put(A, p, T.TGap{}, U32.shr(h), U32.sub(x, h), v,
        U32.is_lt(U32.sub(x, h), U32.shr(h))))), U32.shr(h),
    T.Trie.rebase(U32.is_lt(y, h), h, y))
    == T.Trie.get(A, 1n+p, t, h, y) : Maybe<&2, A>}:
  match bx:
    case True{}:
      match by:
        case True{}:
          %E.Maybe.sym(A, T.Trie.get(A, 1n+p, t, h, y), None{},
            none)
            : {T.Trie.get(A, p, T.Trie.pick(A, U32.is_lt(y, h),
              T.Trie.put(A, p, T.TGap{}, U32.shr(h), x, v,
                U32.is_lt(x, U32.shr(h))), T.TGap{}), U32.shr(h),
              T.Trie.rebase(U32.is_lt(y, h), h, y)) == _
              : Maybe<&2, A>}
          %eby : {T.Trie.get(A, p, T.Trie.pick(A, _,
            T.Trie.put(A, p, T.TGap{}, U32.shr(h), x, v,
              U32.is_lt(x, U32.shr(h))), T.TGap{}), U32.shr(h),
            T.Trie.rebase(_, h, y)) == None{} : Maybe<&2, A>}
          Equal.trans(Maybe<&2, A>,
            T.Trie.get(A, p, T.Trie.put(A, p, T.TGap{}, U32.shr(h),
              x, v, U32.is_lt(x, U32.shr(h))), U32.shr(h), y),
            T.Trie.get(A, p, T.TGap{}, U32.shr(h), y), None{},
            ihT(Trie.gpo.tail(p, h, x, y, True{}, True{}, ebx, eby,
              pe)),
            Trie.get_gap(A, p, U32.shr(h), y))
        case False{}:
          %E.Maybe.sym(A, T.Trie.get(A, 1n+p, t, h, y), None{},
            none)
            : {T.Trie.get(A, p, T.Trie.pick(A, U32.is_lt(y, h),
              T.Trie.put(A, p, T.TGap{}, U32.shr(h), x, v,
                U32.is_lt(x, U32.shr(h))), T.TGap{}), U32.shr(h),
              T.Trie.rebase(U32.is_lt(y, h), h, y)) == _
              : Maybe<&2, A>}
          %eby : {T.Trie.get(A, p, T.Trie.pick(A, _,
            T.Trie.put(A, p, T.TGap{}, U32.shr(h), x, v,
              U32.is_lt(x, U32.shr(h))), T.TGap{}), U32.shr(h),
            T.Trie.rebase(_, h, y)) == None{} : Maybe<&2, A>}
          Trie.get_gap(A, p, U32.shr(h), U32.sub(y, h))
    case False{}:
      match by:
        case True{}:
          %E.Maybe.sym(A, T.Trie.get(A, 1n+p, t, h, y), None{},
            none)
            : {T.Trie.get(A, p, T.Trie.pick(A, U32.is_lt(y, h),
              T.TGap{}, T.Trie.put(A, p, T.TGap{}, U32.shr(h),
                U32.sub(x, h), v,
                U32.is_lt(U32.sub(x, h), U32.shr(h)))), U32.shr(h),
              T.Trie.rebase(U32.is_lt(y, h), h, y)) == _
              : Maybe<&2, A>}
          %eby : {T.Trie.get(A, p, T.Trie.pick(A, _, T.TGap{},
            T.Trie.put(A, p, T.TGap{}, U32.shr(h), U32.sub(x, h), v,
              U32.is_lt(U32.sub(x, h), U32.shr(h)))), U32.shr(h),
            T.Trie.rebase(_, h, y)) == None{} : Maybe<&2, A>}
          Trie.get_gap(A, p, U32.shr(h), y)
        case False{}:
          %E.Maybe.sym(A, T.Trie.get(A, 1n+p, t, h, y), None{},
            none)
            : {T.Trie.get(A, p, T.Trie.pick(A, U32.is_lt(y, h),
              T.TGap{}, T.Trie.put(A, p, T.TGap{}, U32.shr(h),
                U32.sub(x, h), v,
                U32.is_lt(U32.sub(x, h), U32.shr(h)))), U32.shr(h),
              T.Trie.rebase(U32.is_lt(y, h), h, y)) == _
              : Maybe<&2, A>}
          %eby : {T.Trie.get(A, p, T.Trie.pick(A, _, T.TGap{},
            T.Trie.put(A, p, T.TGap{}, U32.shr(h), U32.sub(x, h), v,
              U32.is_lt(U32.sub(x, h), U32.shr(h)))), U32.shr(h),
            T.Trie.rebase(_, h, y)) == None{} : Maybe<&2, A>}
          Equal.trans(Maybe<&2, A>,
            T.Trie.get(A, p, T.Trie.put(A, p, T.TGap{}, U32.shr(h),
              U32.sub(x, h), v,
              U32.is_lt(U32.sub(x, h), U32.shr(h))), U32.shr(h),
              U32.sub(y, h)),
            T.Trie.get(A, p, T.TGap{}, U32.shr(h), U32.sub(y, h)),
            None{},
            ihF(Trie.gpo.tail(p, h, x, y, False{}, False{}, ebx,
              eby, pe)),
            Trie.get_gap(A, p, U32.shr(h), U32.sub(y, h)))

def Trie.get_put_other(A, d, t, h, x, y, v, bx, ebx, by, eby, pe):
  match d:
    case 0n:
      E.Bool.noconf({T.Trie.get(A, 0n, T.TVal{v}, h, y)
        == T.Trie.get(A, 0n, t, h, y) : Maybe<&2, A>}, pe)
    case 1n+p:
      match t:
        case T.TBr{lo, hi}:
          match bx:
            case True{}:
              match by:
                case True{}:
                  %eby : {T.Trie.get(A, p, T.Trie.pick(A, _,
                    T.Trie.put(A, p, lo, U32.shr(h), x, v,
                      U32.is_lt(x, U32.shr(h))), hi), U32.shr(h),
                    T.Trie.rebase(_, h, y))
                    == T.Trie.get(A, p, T.Trie.pick(A, _, lo, hi),
                      U32.shr(h), T.Trie.rebase(_, h, y))
                    : Maybe<&2, A>}
                  Trie.get_put_other(A, p, lo, U32.shr(h), x, y, v,
                    U32.is_lt(x, U32.shr(h)), {==},
                    U32.is_lt(y, U32.shr(h)), {==},
                    Trie.gpo.tail(p, h, x, y, True{}, True{}, ebx,
                      eby, pe))
                case False{}:
                  %eby : {T.Trie.get(A, p, T.Trie.pick(A, _,
                    T.Trie.put(A, p, lo, U32.shr(h), x, v,
                      U32.is_lt(x, U32.shr(h))), hi), U32.shr(h),
                    T.Trie.rebase(_, h, y))
                    == T.Trie.get(A, p, T.Trie.pick(A, _, lo, hi),
                      U32.shr(h), T.Trie.rebase(_, h, y))
                    : Maybe<&2, A>}
                  {==}
            case False{}:
              match by:
                case True{}:
                  %eby : {T.Trie.get(A, p, T.Trie.pick(A, _, lo,
                    T.Trie.put(A, p, hi, U32.shr(h),
                      U32.sub(x, h), v,
                      U32.is_lt(U32.sub(x, h), U32.shr(h)))),
                    U32.shr(h), T.Trie.rebase(_, h, y))
                    == T.Trie.get(A, p, T.Trie.pick(A, _, lo, hi),
                      U32.shr(h), T.Trie.rebase(_, h, y))
                    : Maybe<&2, A>}
                  {==}
                case False{}:
                  %eby : {T.Trie.get(A, p, T.Trie.pick(A, _, lo,
                    T.Trie.put(A, p, hi, U32.shr(h),
                      U32.sub(x, h), v,
                      U32.is_lt(U32.sub(x, h), U32.shr(h)))),
                    U32.shr(h), T.Trie.rebase(_, h, y))
                    == T.Trie.get(A, p, T.Trie.pick(A, _, lo, hi),
                      U32.shr(h), T.Trie.rebase(_, h, y))
                    : Maybe<&2, A>}
                  Trie.get_put_other(A, p, hi, U32.shr(h),
                    U32.sub(x, h), U32.sub(y, h), v,
                    U32.is_lt(U32.sub(x, h), U32.shr(h)), {==},
                    U32.is_lt(U32.sub(y, h), U32.shr(h)), {==},
                    Trie.gpo.tail(p, h, x, y, False{}, False{}, ebx,
                      eby, pe))
        case T.TGap{}:
          match bx:
            case True{}:
              match by:
                case True{}:
                  %eby : {T.Trie.get(A, p, T.Trie.pick(A, _,
                    T.Trie.put(A, p, T.TGap{}, U32.shr(h), x, v,
                      U32.is_lt(x, U32.shr(h))), T.TGap{}),
                    U32.shr(h), T.Trie.rebase(_, h, y)) == None{}
                    : Maybe<&2, A>}
                  Equal.trans(Maybe<&2, A>,
                    T.Trie.get(A, p, T.Trie.put(A, p, T.TGap{},
                      U32.shr(h), x, v,
                      U32.is_lt(x, U32.shr(h))), U32.shr(h), y),
                    T.Trie.get(A, p, T.TGap{}, U32.shr(h), y),
                    None{},
                    Trie.get_put_other(A, p, T.TGap{}, U32.shr(h),
                      x, y, v, U32.is_lt(x, U32.shr(h)), {==},
                      U32.is_lt(y, U32.shr(h)), {==},
                      Trie.gpo.tail(p, h, x, y, True{}, True{}, ebx,
                        eby, pe)),
                    Trie.get_gap(A, p, U32.shr(h), y))
                case False{}:
                  %eby : {T.Trie.get(A, p, T.Trie.pick(A, _,
                    T.Trie.put(A, p, T.TGap{}, U32.shr(h), x, v,
                      U32.is_lt(x, U32.shr(h))), T.TGap{}),
                    U32.shr(h), T.Trie.rebase(_, h, y)) == None{}
                    : Maybe<&2, A>}
                  Trie.get_gap(A, p, U32.shr(h), U32.sub(y, h))
            case False{}:
              match by:
                case True{}:
                  %eby : {T.Trie.get(A, p, T.Trie.pick(A, _,
                    T.TGap{}, T.Trie.put(A, p, T.TGap{}, U32.shr(h),
                      U32.sub(x, h), v,
                      U32.is_lt(U32.sub(x, h), U32.shr(h)))),
                    U32.shr(h), T.Trie.rebase(_, h, y)) == None{}
                    : Maybe<&2, A>}
                  Trie.get_gap(A, p, U32.shr(h), y)
                case False{}:
                  %eby : {T.Trie.get(A, p, T.Trie.pick(A, _,
                    T.TGap{}, T.Trie.put(A, p, T.TGap{}, U32.shr(h),
                      U32.sub(x, h), v,
                      U32.is_lt(U32.sub(x, h), U32.shr(h)))),
                    U32.shr(h), T.Trie.rebase(_, h, y)) == None{}
                    : Maybe<&2, A>}
                  Equal.trans(Maybe<&2, A>,
                    T.Trie.get(A, p, T.Trie.put(A, p, T.TGap{},
                      U32.shr(h), U32.sub(x, h), v,
                      U32.is_lt(U32.sub(x, h), U32.shr(h))),
                      U32.shr(h), U32.sub(y, h)),
                    T.Trie.get(A, p, T.TGap{}, U32.shr(h),
                      U32.sub(y, h)), None{},
                    Trie.get_put_other(A, p, T.TGap{}, U32.shr(h),
                      U32.sub(x, h), U32.sub(y, h), v,
                      U32.is_lt(U32.sub(x, h), U32.shr(h)), {==},
                      U32.is_lt(U32.sub(y, h), U32.shr(h)), {==},
                      Trie.gpo.tail(p, h, x, y, False{}, False{},
                        ebx, eby, pe)),
                    Trie.get_gap(A, p, U32.shr(h), U32.sub(y, h)))
        case T.TVal{old}:
          match bx:
            case True{}:
              match by:
                case True{}:
                  %eby : {T.Trie.get(A, p, T.Trie.pick(A, _,
                    T.Trie.put(A, p, T.TGap{}, U32.shr(h), x, v,
                      U32.is_lt(x, U32.shr(h))), T.TGap{}),
                    U32.shr(h), T.Trie.rebase(_, h, y)) == None{}
                    : Maybe<&2, A>}
                  Equal.trans(Maybe<&2, A>,
                    T.Trie.get(A, p, T.Trie.put(A, p, T.TGap{},
                      U32.shr(h), x, v,
                      U32.is_lt(x, U32.shr(h))), U32.shr(h), y),
                    T.Trie.get(A, p, T.TGap{}, U32.shr(h), y),
                    None{},
                    Trie.get_put_other(A, p, T.TGap{}, U32.shr(h),
                      x, y, v, U32.is_lt(x, U32.shr(h)), {==},
                      U32.is_lt(y, U32.shr(h)), {==},
                      Trie.gpo.tail(p, h, x, y, True{}, True{}, ebx,
                        eby, pe)),
                    Trie.get_gap(A, p, U32.shr(h), y))
                case False{}:
                  %eby : {T.Trie.get(A, p, T.Trie.pick(A, _,
                    T.Trie.put(A, p, T.TGap{}, U32.shr(h), x, v,
                      U32.is_lt(x, U32.shr(h))), T.TGap{}),
                    U32.shr(h), T.Trie.rebase(_, h, y)) == None{}
                    : Maybe<&2, A>}
                  Trie.get_gap(A, p, U32.shr(h), U32.sub(y, h))
            case False{}:
              match by:
                case True{}:
                  %eby : {T.Trie.get(A, p, T.Trie.pick(A, _,
                    T.TGap{}, T.Trie.put(A, p, T.TGap{}, U32.shr(h),
                      U32.sub(x, h), v,
                      U32.is_lt(U32.sub(x, h), U32.shr(h)))),
                    U32.shr(h), T.Trie.rebase(_, h, y)) == None{}
                    : Maybe<&2, A>}
                  Trie.get_gap(A, p, U32.shr(h), y)
                case False{}:
                  %eby : {T.Trie.get(A, p, T.Trie.pick(A, _,
                    T.TGap{}, T.Trie.put(A, p, T.TGap{}, U32.shr(h),
                      U32.sub(x, h), v,
                      U32.is_lt(U32.sub(x, h), U32.shr(h)))),
                    U32.shr(h), T.Trie.rebase(_, h, y)) == None{}
                    : Maybe<&2, A>}
                  Equal.trans(Maybe<&2, A>,
                    T.Trie.get(A, p, T.Trie.put(A, p, T.TGap{},
                      U32.shr(h), U32.sub(x, h), v,
                      U32.is_lt(U32.sub(x, h), U32.shr(h))),
                      U32.shr(h), U32.sub(y, h)),
                    T.Trie.get(A, p, T.TGap{}, U32.shr(h),
                      U32.sub(y, h)), None{},
                    Trie.get_put_other(A, p, T.TGap{}, U32.shr(h),
                      U32.sub(x, h), U32.sub(y, h), v,
                      U32.is_lt(U32.sub(x, h), U32.shr(h)), {==},
                      U32.is_lt(U32.sub(y, h), U32.shr(h)), {==},
                      Trie.gpo.tail(p, h, x, y, False{}, False{},
                        ebx, eby, pe)),
                    Trie.get_gap(A, p, U32.shr(h), U32.sub(y, h)))

# A key never diverges from itself.
def Trie.pnr.step(+p: Nat, +h: U32, +x: U32, +b: Bool,
  +eb: {b == U32.is_lt(x, h) : Bool},
  +ih: {Trie.path_ne(p, U32.shr(h), T.Trie.rebase(b, h, x),
    T.Trie.rebase(b, h, x)) == False{} : Bool})
  -> {Bool.or(Bool.ne(U32.is_lt(x, h), U32.is_lt(x, h)),
      Trie.path_ne(p, U32.shr(h),
        T.Trie.rebase(U32.is_lt(x, h), h, x),
        T.Trie.rebase(U32.is_lt(x, h), h, x))) == False{} : Bool}:
  match b:
    case True{}:
      %eb : {Bool.or(Bool.ne(_, _), Trie.path_ne(p, U32.shr(h),
        T.Trie.rebase(_, h, x), T.Trie.rebase(_, h, x)))
        == False{} : Bool}
      ih
    case False{}:
      %eb : {Bool.or(Bool.ne(_, _), Trie.path_ne(p, U32.shr(h),
        T.Trie.rebase(_, h, x), T.Trie.rebase(_, h, x)))
        == False{} : Bool}
      ih

law Trie.path_ne_refl:
  for +d: Nat
  for +h: U32
  for +x: U32
  {Trie.path_ne(d, h, x, x) == False{} : Bool}

def Trie.path_ne_refl(d, h, x):
  match d:
    case 0n:
      {==}
    case 1n+p:
      Trie.pnr.step(p, h, x, U32.is_lt(x, h), {==},
        Trie.path_ne_refl(p, U32.shr(h),
          T.Trie.rebase(U32.is_lt(x, h), h, x)))
