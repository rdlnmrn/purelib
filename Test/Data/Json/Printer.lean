module

import Purelib.Data.Json.Printer
import Purelib.Data.String.Basic
import Init.System.IO
import Init.System.IOError

open Purelib.Data (Json)
open scoped Purelib.Data.String

namespace Test.Data.Json.Printer

/-- Check exact compact bytes against a retained independent wire fixture.

The expectation preserves scalar spelling, string escapes and canonical field
order. This runtime check invokes only the owned printer and carrier. -/
private def wire (label : String) (value : Json) (expected : String) : IO Unit := do
  let actual := Json.compress value
  unless actual == expected do
    throw (IO.userError s!"{label}: compact JSON differs: '{actual}' versus '{expected}'")

/-- Check the exact pretty layout against a retained width-specific fixture.

The supplied width, spaces and newlines determine the expected original layout.
The fixture does not import an old comparator or infer agreement from compact text. -/
private def display (label : String) (value : Json) (width : Nat) (expected : String) : IO Unit := do
  let actual := Json.pretty value width
  unless actual == expected do
    throw (IO.userError s!"{label}: pretty JSON differs: '{actual}' versus '{expected}'")

/-- Exercise retained JSON wire spelling and width-dependent layout.

Fixtures cover Unicode and control escaping, scientific scales, final duplicate
keys, nested data and the distinct compact/pretty object orders. Runtime outputs
are checked against explicit strings rather than used as mathematical proofs. -/
public def run : IO Unit := do
  wire "null" .null "null"
  wire "Boolean true" (.bool true) "true"
  wire "empty array" (.arr #[]) "[]"
  wire "empty object" (Json.mkObj []) "{}"
  wire "ordinary ASCII" (.str "alpha / beta") "\"alpha / beta\""
  wire "Unicode" (.str "éδ🙂") "\"éδ🙂\""
  wire "escape boundaries" (.str "\"\\\n\x0d\t\x08\x0c")
    "\"\\\"\\\\\\n\\r\\u0009\\u0008\\u000c\""
  wire "retained negative integer" (.num ⟨-2345, 0⟩) "-2345"
  wire "fractional scale" (.num ⟨12345, 3⟩) "12.345"
  wire "negative whole decimal" (.num ⟨-1000, 2⟩) "-10"
  wire "trailing fractional zeros" (.num ⟨1230000, 5⟩) "12.3"
  wire "scientific small scalar" (.num ⟨1, 20⟩) "0.0000000001e-10"
  wire "scientific negative scalar" (.num ⟨-123, 30⟩) "-0.000000000123e-18"
  -- Retain this original scalar spelling without asserting a parser round-trip.
  wire "scaled zero spelling" (.num ⟨0, 20⟩) "0.e-10"
  let object := Json.mkObj [("z", .bool true), ("a", .null)]
  wire "distinct object keys" object "{\"a\":null,\"z\":true}"
  wire "final duplicate value" (.obj [("key", .bool false), ("key", .bool true)])
    "{\"key\":true}"
  wire "Unicode object key order"
    (Json.mkObj [("🙂", .null), ("δ", .null), ("é", .null), ("a", .null)])
    "{\"a\":null,\"é\":null,\"δ\":null,\"🙂\":null}"
  wire "nested layout"
    (Json.mkObj [("numbers", .arr #[.num ⟨12345678901234567890, 0⟩, .num ⟨12345, 3⟩]),
      ("nested", Json.mkObj [("escaped", .str "δ\n🙂"), ("ordered", .arr #[.null, .bool false])])])
    "{\"nested\":{\"escaped\":\"δ\\n🙂\",\"ordered\":[null,false]},\"numbers\":[12345678901234567890,12.345]}"
  display "pretty object order" object 80 "{\"z\": true, \"a\": null}"
  display "pretty object narrow" object 1 "{\"z\":\n true,\n \"a\":\n null}"
  display "pretty array wide" (.arr #[.null, .bool false]) 80 "[null, false]"
  display "pretty array narrow" (.arr #[.null, .bool false]) 8 "[null,\n false]"
  unless toString object == "{\"z\": true, \"a\": null}" do
    throw (IO.userError "JSON display did not retain the default pretty width")
  let stdout ← IO.getStdout
  stdout.putStr "18 owned JSON wire fixtures and explicit pretty layouts passed\n"

end Test.Data.Json.Printer
