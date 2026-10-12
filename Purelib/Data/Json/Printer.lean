module

-- Printing clients retain this original JSON value owner and its scalar fields.
public import Purelib.Data.Json.Basic
import Purelib.Data.Json.Number
import Purelib.Data.String.Basic
import Init.Data.String.Bootstrap
import Init.Data.Format.Basic

/-!
# JSON rendering

Compact output retains canonical object-key order and ordered array entries.
Pretty output uses the original format layout with a default width of eighty.
Decimal fields and string escapes keep their original JSON wire conventions.
-/

namespace Purelib.Data.Json

open Purelib.Data.String (append)

/-- Detect bytes requiring the original JSON string escape path.

ASCII controls, quotes and backslashes require escaping. Non-ASCII UTF-8 bytes
select the character path, which retains their original Unicode scalar values. -/
private def needEscape (value : String) : Bool :=
  value.toByteArray.data.toList.any fun byte =>
    byte.toNat < 32 || byte.toNat == 34 || byte.toNat == 92 || 128 ≤ byte.toNat

/-- Append one JSON-escaped character to the retained output string.

Quote, backslash, newline and carriage return use the original short escapes.
Other controls use four hexadecimal digits; ordinary Unicode scalars remain literal. -/
private def escapeChar (output : String) (character : Char) : String :=
  let value := character.toNat
  if value == 34 then append output "\\\""
  else if value == 92 then append output "\\\\"
  else if value == 10 then append output "\\n"
  else if value == 13 then append output "\\r"
  else if 32 ≤ value && value ≤ 0x10ffff then
    String.Internal.pushn output character 1
  else
    let output := append output "\\u"
    let output := String.Internal.pushn output (Nat.digitChar (value / 4096)) 1
    let output := String.Internal.pushn output (Nat.digitChar ((value % 4096) / 256)) 1
    let output := String.Internal.pushn output (Nat.digitChar ((value % 256) / 16)) 1
    String.Internal.pushn output (Nat.digitChar (value % 16)) 1

/-- Append a JSON string's escaped contents to the retained output.

The ASCII fast path appends the input string directly. The character path uses
Lean's original bootstrap fold primitive and the same scalar escape convention. -/
private def escape (value output : String) : String :=
  if needEscape value then String.Internal.foldl escapeChar output value
  else append output value

/-- Append the quoted and escaped representation of a JSON string.

Both quote bytes enclose the original scalar contents after JSON escaping.
The supplied output prefix is retained before those bytes. -/
private def renderString (value : String) (output : String := "") : String :=
  append (escape value (append output "\"")) "\""

set_option backward.match.sparseCases false in
/-- Build the original grouped pretty layout for a finite JSON value.

Arrays retain their entry order. Object fields use decreasing canonical key order,
as in the original format fold, independently of the compact printer's key order. -/
private partial def render : Json → Std.Format
  | .null => .text "null"
  | .bool true => .text "true"
  | .bool false => .text "false"
  | .num number => .text (Number.repr number)
  | .str value => .text (renderString value)
  | .arr entries =>
      let separator := Std.Format.append (.text ",") .line
      let contents := Std.Format.joinSep (entries.toList.map render) separator
      Std.Format.bracket "[" contents "]"
  | .obj fields =>
      let layouts := (objectFields fields).foldl (fun retained field =>
        let layout := Std.Format.group
          (Std.Format.append (.text (renderString field.1))
            (Std.Format.append (.text ":") (Std.Format.append .line (render field.2))))
        layout :: retained) []
      let separator := Std.Format.append (.text ",") .line
      Std.Format.bracket "{" (Std.Format.joinSep layouts separator) "}"

/-- Render a finite JSON value using the original grouped pretty layout.

The default line width is eighty, matching the original JSON display convention.
Nested layout groups retain the original formatter's indentation and line choices. -/
public def pretty (value : Json) (lineWidth : Nat := 80) : String :=
  Std.Format.pretty (render value) lineWidth

set_option backward.match.sparseCases false in
/-- Render a finite JSON value without insignificant whitespace.

Arrays retain their original order, and normalized objects retain increasing key
order with the last input value at each key. String escapes and decimal scalars
use the same wire representation as the original JSON encoder. -/
public partial def compress (value : Json) : String :=
  write value ""
where
  /-- Append one retained JSON value to the compact output prefix.

  Scalar contents append their encoded bytes directly. Arrays and canonical
  objects fold their retained entries in order with explicit comma separators. -/
  write (value : Json) (output : String) : String :=
    match value with
    | .null => append output "null"
    | .bool true => append output "true"
    | .bool false => append output "false"
    | .num number => append output (Number.repr number)
    | .str value => renderString value output
    | .arr entries =>
        let output := append output "["
        let output := match entries.toList with
          | [] => output
          | first :: rest =>
              rest.foldl (fun output entry => write entry (append output ","))
                (write first output)
        append output "]"
    | .obj fields =>
        let output := append output "{"
        let output := match objectFields fields with
          | [] => output
          | first :: rest =>
              let output := write first.2 (append (renderString first.1 output) ":")
              rest.foldl (fun output field =>
                write field.2 (append (renderString field.1 (append output ",")) ":")) output
        append output "}"

/-- Display JSON using the original default-width pretty representation.

Scalar decoder errors retain that representation when they include a complete
JSON value. Compact wire output remains available through compress separately. -/
public instance : ToString Json where
  toString := pretty

end Purelib.Data.Json
