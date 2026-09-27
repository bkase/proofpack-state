# proofs/policylift.bend -- G-02, lifted from a row to an edge.
#
# `a_filtered_row_drops_exactly_the_commit_targets` says what the tree-data
# filter does to one successor row. The obligation is about `Graph.edge` over
# the two assembled adjacency tables, and this file is the lift.
#
# Both tables are `Trie.of_list` over lists that run in ordinal order and in
# step with each other: `Idx.full_rows` is the successor row of each object,
# `Idx.tree_rows` is the same row filtered when the object is a commit, and
# the metadata table is `Trie.of_list` over the same metadata list the filter
# consults. proofs/table.bend says a built table answers whatever the same
# descent over its list answers, so the three tables descend together and the
# question reduces to the three lists at a position -- where the row-level law
# applies.
#
# The one hypothesis is that the rows and the metadata run to the same length,
# which is what `Idx.assemble.tries` is handed: the importer appends to both
# in the same step. It is needed, not decorative -- `Idx.tree_rows` stops at
# the shorter of the two, so a row without a matching metadata entry is absent
# from the tree-data table while still present in the full one, and the two
# policies would then disagree about an edge for a reason that has nothing to
# do with the policy.

import Base
import ./eq.bend as E
import ./table.bend as Tb
import ./policy.bend as Pl
import ../core/trie.bend as T
import ../closure/graph.bend as G
import ../adapters/git/import.bend as Im
import ../index/source.bend as Sc

# ---------------------------------------------------------------------------
# Splitting the lists.
# ---------------------------------------------------------------------------

law Idx.take_full_rows:
  for +rows: List<&2, Im.Row>
  for +k: Nat
  {List.take(&2, G.Succ, Sc.Idx.full_rows(rows), k)
    == Sc.Idx.full_rows(List.take(&2, Im.Row, rows, k)) : List<&2, G.Succ>}

def Idx.take_full_rows(rows, k):
  match rows:
    case Nil{}:
      {==}
    case Con{r, rt}:
      match k:
        case 0n:
          {==}
        case 1n+j:
          %E.List.sym(G.Succ,
            List.take(&2, G.Succ, Sc.Idx.full_rows(rt), j),
            Sc.Idx.full_rows(List.take(&2, Im.Row, rt, j)),
            Idx.take_full_rows(rt, j))
            : {Con{Im.Row.succ(r), _}
              == Sc.Idx.full_rows(Con{r, List.take(&2, Im.Row, rt, j)})
              : List<&2, G.Succ>}
          {==}

law Idx.drop_full_rows:
  for +rows: List<&2, Im.Row>
  for +k: Nat
  {List.drop(&2, G.Succ, Sc.Idx.full_rows(rows), k)
    == Sc.Idx.full_rows(List.drop(&2, Im.Row, rows, k)) : List<&2, G.Succ>}

def Idx.drop_full_rows(rows, k):
  match rows:
    case Nil{}:
      {==}
    case Con{r, rt}:
      match k:
        case 0n:
          {==}
        case 1n+j:
          Idx.drop_full_rows(rt, j)

law Idx.take_tree_rows:
  for +mt: T.Trie<Im.Meta>
  for +rows: List<&2, Im.Row>
  for +metas: List<&2, Im.Meta>
  for +k: Nat
  {List.take(&2, G.Succ, Sc.Idx.tree_rows(mt, rows, metas), k)
    == Sc.Idx.tree_rows(mt, List.take(&2, Im.Row, rows, k),
         List.take(&2, Im.Meta, metas, k)) : List<&2, G.Succ>}

def Idx.take_tree_rows(mt, rows, metas, k):
  match rows:
    case Nil{}:
      {==}
    case Con{r, rt}:
      match metas:
        case Nil{}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              {==}
        case Con{m, mtl}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              %E.List.sym(G.Succ,
                List.take(&2, G.Succ, Sc.Idx.tree_rows(mt, rt, mtl), j),
                Sc.Idx.tree_rows(mt, List.take(&2, Im.Row, rt, j),
                  List.take(&2, Im.Meta, mtl, j)),
                Idx.take_tree_rows(mt, rt, mtl, j))
                : {Con{Sc.Idx.tree_row(mt, Im.Row.succ(r),
                    Sc.Idx.is_commit(m)), _}
                  == Sc.Idx.tree_rows(mt, Con{r, List.take(&2, Im.Row, rt, j)},
                       Con{m, List.take(&2, Im.Meta, mtl, j)})
                  : List<&2, G.Succ>}
              {==}

law Idx.tree_rows_no_metas:
  for +mt: T.Trie<Im.Meta>
  for +rows: List<&2, Im.Row>
  {Sc.Idx.tree_rows(mt, rows, Nil{}) == Nil{} : List<&2, G.Succ>}

def Idx.tree_rows_no_metas(mt, rows):
  match rows:
    case Nil{}:
      {==}
    case Con{r, rt}:
      {==}

law Idx.drop_tree_rows:
  for +mt: T.Trie<Im.Meta>
  for +rows: List<&2, Im.Row>
  for +metas: List<&2, Im.Meta>
  for +k: Nat
  {List.drop(&2, G.Succ, Sc.Idx.tree_rows(mt, rows, metas), k)
    == Sc.Idx.tree_rows(mt, List.drop(&2, Im.Row, rows, k),
         List.drop(&2, Im.Meta, metas, k)) : List<&2, G.Succ>}

def Idx.drop_tree_rows(mt, rows, metas, k):
  match rows:
    case Nil{}:
      {==}
    case Con{r, rt}:
      match metas:
        case Nil{}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              E.List.sym(G.Succ,
                Sc.Idx.tree_rows(mt, List.drop(&2, Im.Row, rt, j), Nil{}),
                Nil{},
                Idx.tree_rows_no_metas(mt, List.drop(&2, Im.Row, rt, j)))
        case Con{m, mtl}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              Idx.drop_tree_rows(mt, rt, mtl, j)

# ---------------------------------------------------------------------------
# The three lists, at a position.
# ---------------------------------------------------------------------------

def Idx.tree_at(+mt: T.Trie<Im.Meta>, mrow: Maybe<&2, G.Succ>,
  mmeta: Maybe<&2, Im.Meta>) -> Maybe<&2, G.Succ>:
  match mrow:
    case None{}:
      None{}
    case Some{row}:
      match mmeta:
        case None{}:
          None{}
        case Some{m}:
          Some{Sc.Idx.tree_row(mt, row, Sc.Idx.is_commit(m))}

law Idx.tree_at_no_meta:
  for +mt: T.Trie<Im.Meta>
  for +mrow: Maybe<&2, G.Succ>
  {Idx.tree_at(mt, mrow, None{}) == None{} : Maybe<&2, G.Succ>}

def Idx.tree_at_no_meta(mt, mrow):
  match mrow:
    case None{}:
      {==}
    case Some{row}:
      {==}

law Idx.split_full:
  for +rows: List<&2, Im.Row>
  for +b: Bool
  for +k: Nat
  {Tb.List.pick(G.Succ, b,
      List.take(&2, G.Succ, Sc.Idx.full_rows(rows), k),
      List.drop(&2, G.Succ, Sc.Idx.full_rows(rows), k))
    == Sc.Idx.full_rows(Tb.List.pick(Im.Row, b,
         List.take(&2, Im.Row, rows, k),
         List.drop(&2, Im.Row, rows, k))) : List<&2, G.Succ>}

def Idx.split_full(rows, b, k):
  match b:
    case True{}:
      Idx.take_full_rows(rows, k)
    case False{}:
      Idx.drop_full_rows(rows, k)

law Idx.split_tree:
  for +mt: T.Trie<Im.Meta>
  for +rows: List<&2, Im.Row>
  for +metas: List<&2, Im.Meta>
  for +b: Bool
  for +k: Nat
  {Tb.List.pick(G.Succ, b,
      List.take(&2, G.Succ, Sc.Idx.tree_rows(mt, rows, metas), k),
      List.drop(&2, G.Succ, Sc.Idx.tree_rows(mt, rows, metas), k))
    == Sc.Idx.tree_rows(mt,
         Tb.List.pick(Im.Row, b, List.take(&2, Im.Row, rows, k),
           List.drop(&2, Im.Row, rows, k)),
         Tb.List.pick(Im.Meta, b, List.take(&2, Im.Meta, metas, k),
           List.drop(&2, Im.Meta, metas, k))) : List<&2, G.Succ>}

def Idx.split_tree(mt, rows, metas, b, k):
  match b:
    case True{}:
      Idx.take_tree_rows(mt, rows, metas, k)
    case False{}:
      Idx.drop_tree_rows(mt, rows, metas, k)

law Idx.at_tree_rows:
  for +d: Nat
  for +mt: T.Trie<Im.Meta>
  for +rows: List<&2, Im.Row>
  for +metas: List<&2, Im.Meta>
  for +h: U32
  for +x: U32
  {Tb.List.at_ord(G.Succ, d, Sc.Idx.tree_rows(mt, rows, metas), h, x)
    == Idx.tree_at(mt,
         Tb.List.at_ord(G.Succ, d, Sc.Idx.full_rows(rows), h, x),
         Tb.List.at_ord(Im.Meta, d, metas, h, x)) : Maybe<&2, G.Succ>}

def Idx.at_tree_rows(d, mt, rows, metas, h, x):
  match d:
    case 0n:
      match rows:
        case Nil{}:
          {==}
        case Con{r, rt}:
          match metas:
            case Nil{}:
              E.Maybe.sym(G.Succ,
                Idx.tree_at(mt,
                  Tb.List.at_ord(G.Succ, 0n,
                    Sc.Idx.full_rows(Con{r, rt}), h, x), None{}),
                None{},
                Idx.tree_at_no_meta(mt,
                  Tb.List.at_ord(G.Succ, 0n,
                    Sc.Idx.full_rows(Con{r, rt}), h, x)))
            case Con{m, mtl}:
              {==}
    case 1n+p:
      match rows:
        case Nil{}:
          {==}
        case Con{r, rt}:
          match metas:
            case Nil{}:
              E.Maybe.sym(G.Succ,
                Idx.tree_at(mt,
                  Tb.List.at_ord(G.Succ, 1n+p,
                    Sc.Idx.full_rows(Con{r, rt}), h, x), None{}),
                None{},
                Idx.tree_at_no_meta(mt,
                  Tb.List.at_ord(G.Succ, 1n+p,
                    Sc.Idx.full_rows(Con{r, rt}), h, x)))
            case Con{m, mtl}:
              %E.List.sym(G.Succ,
                Tb.List.pick(G.Succ, U32.is_lt(x, h),
                  List.take(&2, G.Succ,
                    Sc.Idx.tree_rows(mt, Con{r, rt}, Con{m, mtl}),
                    U32.to_nat(h)),
                  List.drop(&2, G.Succ,
                    Sc.Idx.tree_rows(mt, Con{r, rt}, Con{m, mtl}),
                    U32.to_nat(h))),
                Sc.Idx.tree_rows(mt, Tb.List.pick(Im.Row, U32.is_lt(x, h),
                  List.take(&2, Im.Row, Con{r, rt}, U32.to_nat(h)),
                  List.drop(&2, Im.Row, Con{r, rt}, U32.to_nat(h))), Tb.List.pick(Im.Meta, U32.is_lt(x, h),
                  List.take(&2, Im.Meta, Con{m, mtl}, U32.to_nat(h)),
                  List.drop(&2, Im.Meta, Con{m, mtl}, U32.to_nat(h)))),
                Idx.split_tree(mt, Con{r, rt}, Con{m, mtl},
                  U32.is_lt(x, h), U32.to_nat(h)))
                : {Tb.List.at_ord(G.Succ, p, _, U32.shr(h),
                    T.Trie.rebase(U32.is_lt(x, h), h, x))
                  == Idx.tree_at(mt,
                       Tb.List.at_ord(G.Succ, p,
                         Tb.List.pick(G.Succ, U32.is_lt(x, h),
                           List.take(&2, G.Succ,
                             Sc.Idx.full_rows(Con{r, rt}), U32.to_nat(h)),
                           List.drop(&2, G.Succ,
                             Sc.Idx.full_rows(Con{r, rt}), U32.to_nat(h))),
                         U32.shr(h), T.Trie.rebase(U32.is_lt(x, h), h, x)),
                       Tb.List.at_ord(Im.Meta, p, Tb.List.pick(Im.Meta, U32.is_lt(x, h),
                  List.take(&2, Im.Meta, Con{m, mtl}, U32.to_nat(h)),
                  List.drop(&2, Im.Meta, Con{m, mtl}, U32.to_nat(h))), U32.shr(h),
                         T.Trie.rebase(U32.is_lt(x, h), h, x)))
                  : Maybe<&2, G.Succ>}
              %E.List.sym(G.Succ,
                Tb.List.pick(G.Succ, U32.is_lt(x, h),
                  List.take(&2, G.Succ, Sc.Idx.full_rows(Con{r, rt}),
                    U32.to_nat(h)),
                  List.drop(&2, G.Succ, Sc.Idx.full_rows(Con{r, rt}),
                    U32.to_nat(h))),
                Sc.Idx.full_rows(Tb.List.pick(Im.Row, U32.is_lt(x, h),
                  List.take(&2, Im.Row, Con{r, rt}, U32.to_nat(h)),
                  List.drop(&2, Im.Row, Con{r, rt}, U32.to_nat(h)))),
                Idx.split_full(Con{r, rt}, U32.is_lt(x, h), U32.to_nat(h)))
                : {Tb.List.at_ord(G.Succ, p,
                     Sc.Idx.tree_rows(mt, Tb.List.pick(Im.Row, U32.is_lt(x, h),
                  List.take(&2, Im.Row, Con{r, rt}, U32.to_nat(h)),
                  List.drop(&2, Im.Row, Con{r, rt}, U32.to_nat(h))), Tb.List.pick(Im.Meta, U32.is_lt(x, h),
                  List.take(&2, Im.Meta, Con{m, mtl}, U32.to_nat(h)),
                  List.drop(&2, Im.Meta, Con{m, mtl}, U32.to_nat(h)))), U32.shr(h),
                     T.Trie.rebase(U32.is_lt(x, h), h, x))
                  == Idx.tree_at(mt,
                       Tb.List.at_ord(G.Succ, p, _, U32.shr(h),
                         T.Trie.rebase(U32.is_lt(x, h), h, x)),
                       Tb.List.at_ord(Im.Meta, p, Tb.List.pick(Im.Meta, U32.is_lt(x, h),
                  List.take(&2, Im.Meta, Con{m, mtl}, U32.to_nat(h)),
                  List.drop(&2, Im.Meta, Con{m, mtl}, U32.to_nat(h))), U32.shr(h),
                         T.Trie.rebase(U32.is_lt(x, h), h, x)))
                  : Maybe<&2, G.Succ>}
              Idx.at_tree_rows(p, mt, Tb.List.pick(Im.Row, U32.is_lt(x, h),
                  List.take(&2, Im.Row, Con{r, rt}, U32.to_nat(h)),
                  List.drop(&2, Im.Row, Con{r, rt}, U32.to_nat(h))), Tb.List.pick(Im.Meta, U32.is_lt(x, h),
                  List.take(&2, Im.Meta, Con{m, mtl}, U32.to_nat(h)),
                  List.drop(&2, Im.Meta, Con{m, mtl}, U32.to_nat(h))), U32.shr(h),
                T.Trie.rebase(U32.is_lt(x, h), h, x))

# ---------------------------------------------------------------------------
# The edge.
#
# The decision is carried as a parameter with an equation naming it, because
# the two tables are consulted at the same ordinal and the answer has to stay
# tied to the list across the match.
# ---------------------------------------------------------------------------

law Bool.and_true_r:
  for +p: Bool
  {Bool.and(p, True{}) == p : Bool}

def Bool.and_true_r(p):
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

law Idx.tree_edge.arm:
  for +mt: T.Trie<Im.Meta>
  for +row: G.Succ
  for +v: U32
  for +pc: Bool
  {List.contains(~U32, ~U32.is_eq, Sc.Idx.tree_row(mt, row, pc), v)
    == Bool.and(List.contains(~U32, ~U32.is_eq, row, v),
         Bool.not(Bool.and(pc,
           Sc.Idx.is_commit(Sc.Source.meta_of.un(
             T.Trie.at(Im.Meta, 32n, mt, v)))))) : Bool}

def Idx.tree_edge.arm(mt, row, v, pc):
  match pc:
    case False{}:
      E.Bool.sym(
        Bool.and(List.contains(~U32, ~U32.is_eq, row, v), True{}),
        List.contains(~U32, ~U32.is_eq, row, v),
        Bool.and_true_r(List.contains(~U32, ~U32.is_eq, row, v)))
    case True{}:
      E.Bool.sym(
        Bool.and(List.contains(~U32, ~U32.is_eq, row, v),
          Bool.not(Sc.Idx.is_commit(Sc.Source.meta_of.un(
            T.Trie.at(Im.Meta, 32n, mt, v))))),
        List.contains(~U32, ~U32.is_eq,
          Sc.Idx.filter_succ(mt, row), v),
        Pl.Policy.filter_drops_commits(mt, row, v))

law Idx.tree_edge.on:
  for +mt: T.Trie<Im.Meta>
  for +v: U32
  for +m: Im.Meta
  for +mrow: Maybe<&2, G.Succ>
  {List.contains(~U32, ~U32.is_eq,
      G.Graph.succ.un(Idx.tree_at(mt, mrow, Some{m})), v)
    == Bool.and(List.contains(~U32, ~U32.is_eq,
           G.Graph.succ.un(mrow), v),
         Bool.not(Bool.and(Sc.Idx.is_commit(m),
           Sc.Idx.is_commit(Sc.Source.meta_of.un(
             T.Trie.at(Im.Meta, 32n, mt, v)))))) : Bool}

def Idx.tree_edge.on(mt, v, m, mrow):
  match mrow:
    case None{}:
      {==}
    case Some{row}:
      Idx.tree_edge.arm(mt, row, v, Sc.Idx.is_commit(m))


law Idx.tree_data_edge:
  for +rows: List<&2, Im.Row>
  for +metas: List<&2, Im.Meta>
  for +u: U32
  for +v: U32
  for +m: Im.Meta
  for +hm: {T.Trie.at(Im.Meta, 32n, T.Trie.of_list(Im.Meta, 32n, metas), u) == Some{m} : Maybe<&2, Im.Meta>}
  {G.Graph.edge(32n, T.Trie.of_list(G.Succ, 32n, Sc.Idx.tree_rows(T.Trie.of_list(Im.Meta, 32n, metas), rows, metas)), u, v)
    == Bool.and(
         G.Graph.edge(32n, T.Trie.of_list(G.Succ, 32n, Sc.Idx.full_rows(rows)), u, v),
         Bool.not(Bool.and(Sc.Idx.is_commit(m),
           Sc.Idx.is_commit(Sc.Source.meta_of.un(
             T.Trie.at(Im.Meta, 32n, T.Trie.of_list(Im.Meta, 32n, metas), v)))))) : Bool}

def Idx.tree_data_edge(rows, metas, u, v, m, hm):
  %E.Maybe.sym(G.Succ,
    T.Trie.at(G.Succ, 32n, T.Trie.of_list(G.Succ, 32n, Sc.Idx.tree_rows(T.Trie.of_list(Im.Meta, 32n, metas), rows, metas)), u),
    Tb.List.at_ord(G.Succ, 32n, Sc.Idx.tree_rows(T.Trie.of_list(Im.Meta, 32n, metas), rows, metas), T.Trie.half(32n), u),
    Tb.Trie.at_of_list(G.Succ, 32n, Sc.Idx.tree_rows(T.Trie.of_list(Im.Meta, 32n, metas), rows, metas), u))
    : {List.contains(~U32, ~U32.is_eq, G.Graph.succ.un(_), v)
      == Bool.and(
           G.Graph.edge(32n, T.Trie.of_list(G.Succ, 32n, Sc.Idx.full_rows(rows)), u, v),
           Bool.not(Bool.and(Sc.Idx.is_commit(m),
             Sc.Idx.is_commit(Sc.Source.meta_of.un(
               T.Trie.at(Im.Meta, 32n, T.Trie.of_list(Im.Meta, 32n, metas), v)))))) : Bool}
  %E.Maybe.sym(G.Succ,
    Tb.List.at_ord(G.Succ, 32n, Sc.Idx.tree_rows(T.Trie.of_list(Im.Meta, 32n, metas), rows, metas), T.Trie.half(32n), u),
    Idx.tree_at(T.Trie.of_list(Im.Meta, 32n, metas), Tb.List.at_ord(G.Succ, 32n, Sc.Idx.full_rows(rows), T.Trie.half(32n), u), Tb.List.at_ord(Im.Meta, 32n, metas, T.Trie.half(32n), u)),
    Idx.at_tree_rows(32n, T.Trie.of_list(Im.Meta, 32n, metas), rows, metas, T.Trie.half(32n), u))
    : {List.contains(~U32, ~U32.is_eq, G.Graph.succ.un(_), v)
      == Bool.and(
           G.Graph.edge(32n, T.Trie.of_list(G.Succ, 32n, Sc.Idx.full_rows(rows)), u, v),
           Bool.not(Bool.and(Sc.Idx.is_commit(m),
             Sc.Idx.is_commit(Sc.Source.meta_of.un(
               T.Trie.at(Im.Meta, 32n, T.Trie.of_list(Im.Meta, 32n, metas), v)))))) : Bool}
  %E.Maybe.sym(G.Succ,
    T.Trie.at(G.Succ, 32n, T.Trie.of_list(G.Succ, 32n, Sc.Idx.full_rows(rows)), u),
    Tb.List.at_ord(G.Succ, 32n, Sc.Idx.full_rows(rows), T.Trie.half(32n), u),
    Tb.Trie.at_of_list(G.Succ, 32n, Sc.Idx.full_rows(rows), u))
    : {List.contains(~U32, ~U32.is_eq,
         G.Graph.succ.un(Idx.tree_at(T.Trie.of_list(Im.Meta, 32n, metas), Tb.List.at_ord(G.Succ, 32n, Sc.Idx.full_rows(rows), T.Trie.half(32n), u), Tb.List.at_ord(Im.Meta, 32n, metas, T.Trie.half(32n), u))), v)
      == Bool.and(
           List.contains(~U32, ~U32.is_eq, G.Graph.succ.un(_), v),
           Bool.not(Bool.and(Sc.Idx.is_commit(m),
             Sc.Idx.is_commit(Sc.Source.meta_of.un(
               T.Trie.at(Im.Meta, 32n, T.Trie.of_list(Im.Meta, 32n, metas), v)))))) : Bool}
  %E.Maybe.sym(Im.Meta, Tb.List.at_ord(Im.Meta, 32n, metas, T.Trie.half(32n), u), Some{m},
    Equal.trans(Maybe<&2, Im.Meta>, Tb.List.at_ord(Im.Meta, 32n, metas, T.Trie.half(32n), u),
      T.Trie.at(Im.Meta, 32n, T.Trie.of_list(Im.Meta, 32n, metas), u), Some{m},
      E.Maybe.sym(Im.Meta, T.Trie.at(Im.Meta, 32n, T.Trie.of_list(Im.Meta, 32n, metas), u), Tb.List.at_ord(Im.Meta, 32n, metas, T.Trie.half(32n), u),
        Tb.Trie.at_of_list(Im.Meta, 32n, metas, u)),
      hm))
    : {List.contains(~U32, ~U32.is_eq,
         G.Graph.succ.un(Idx.tree_at(T.Trie.of_list(Im.Meta, 32n, metas), Tb.List.at_ord(G.Succ, 32n, Sc.Idx.full_rows(rows), T.Trie.half(32n), u), _)), v)
      == Bool.and(
           List.contains(~U32, ~U32.is_eq, G.Graph.succ.un(Tb.List.at_ord(G.Succ, 32n, Sc.Idx.full_rows(rows), T.Trie.half(32n), u)), v),
           Bool.not(Bool.and(Sc.Idx.is_commit(m),
             Sc.Idx.is_commit(Sc.Source.meta_of.un(
               T.Trie.at(Im.Meta, 32n, T.Trie.of_list(Im.Meta, 32n, metas), v)))))) : Bool}
  Idx.tree_edge.on(T.Trie.of_list(Im.Meta, 32n, metas), v, m, Tb.List.at_ord(G.Succ, 32n, Sc.Idx.full_rows(rows), T.Trie.half(32n), u))
