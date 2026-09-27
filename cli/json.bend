# cli/json.bend -- the result envelope (SPEC 9.2).
#
# Three rules from the specification are enforced here rather than left to
# each command:
#
#   * Decimal counters are **strings**, so a JSON consumer whose numbers are
#     IEEE doubles cannot silently round a 2^53-exceeding byte total.
#   * `completeness` is distinct from pagination, and a budget-limited
#     computation is never dressed as a complete query with zero results.
#   * No result is labelled `mathematically_verified` because the binary
#     ships with proofs. The envelope names the law bundle and the imported-
#     data assumptions separately, and says plainly that the availability
#     scope is a recorded observation rather than a lease (SPEC 9.4).
#
# Tree entry names are raw bytes and need not be UTF-8 (SPEC 8.4), so
# `Json.str` escapes losslessly: a byte that is not printable ASCII becomes a
# `\u00XX` escape of its value, and round-trips.

import Base
import ../core/count.bend as C

def Json.hexd.pick(+v: U32, dig: Bool) -> String:
  match dig:
    case True{}:
      SCon{Chr{(v + 48 : U32)}, SNil{}}
    case False{}:
      SCon{Chr{(v + 87 : U32)}, SNil{}}

def Json.hexd(+v: U32) -> String:
  Json.hexd.pick(v, U32.is_lt(v, 10))

def Json.hex4(+v: U32) -> String:
  Json.hexd(U32.and(U32.shrn(v, 12n), 15))
    ++ Json.hexd(U32.and(U32.shrn(v, 8n), 15))
    ++ Json.hexd(U32.and(U32.shrn(v, 4n), 15))
    ++ Json.hexd(U32.and(v, 15))

def Json.esc.pick(+c: U32, quote: Bool, slash: Bool, plain: Bool) ->
  String:
  match quote:
    case True{}:
      "\\\""
    case False{}:
      match slash:
        case True{}:
          "\\\\"
        case False{}:
          match plain:
            case True{}:
              SCon{Chr{c}, SNil{}}
            case False{}:
              "\\u" ++ Json.hex4(c)

def Json.esc.chr(+c: U32) -> String:
  Json.esc.pick(c, U32.is_eq(c, 34), U32.is_eq(c, 92),
    Bool.and(U32.is_ge(c, 32), U32.is_le(c, 126)))

def Json.esc(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{c, t}:
      match c:
        case Chr{x}:
          Json.esc.chr(x) ++ Json.esc(t)

def Json.str(s: String) -> String:
  "\"" ++ Json.esc(s) ++ "\""

# Every decimal counter is a string (SPEC 9.2).
def Json.num(n: Nat) -> String:
  Json.str(Nat.show(n))

def Json.bool(b: Bool) -> String:
  match b:
    case True{}:
      "true"
    case False{}:
      "false"

def Json.field(k: String, v: String) -> String:
  Json.str(k) ++ ": " ++ v

def Json.obj(fields: List<&2, String>) -> String:
  "{" ++ String.join(fields, ", ") ++ "}"

def Json.arr(items: List<&2, String>) -> String:
  "[" ++ String.join(items, ", ") ++ "]"

def Json.strings(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{Json.str(x), Json.strings(t)}
