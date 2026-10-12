module

import Purelib.Data.Json.Parser
import Purelib.Data.String.Basic
import Init.System.IO
import Init.System.IOError

open Purelib.Data (Json)
open scoped Purelib.Data.String

namespace Test.Data.Json.Parser

/-- Check successful finite parsing against an independently retained JSON value.

Numeric comparison retains exact mantissa and scale; arrays retain their order.
An object also checks its raw retained key order rather than hiding it behind
field-order-independent equality. -/
private def success (input : String) (expected : Json) : IO Unit := do
  match Json.parse input with
  | .error error => throw (IO.userError s!"unexpected JSON failure for {input}: {error}")
  | .ok actual =>
      unless actual == expected do
        throw (IO.userError s!"JSON data differs from the fixture for {input}")
      match expected.getObj? with
      | .error _ => pure ()
      | .ok expected =>
          match actual.getObj? with
          | .error error => throw (IO.userError error)
          | .ok actual =>
              unless actual.map Prod.fst == expected.map Prod.fst do
                throw (IO.userError s!"retained object key order differs for {input}")

/-- Check the exact original grammar message and consumed byte offset.

A successful parse is rejected by the malformed-input fixture. Error strings are
compared directly without an old JSON parser, codec or representation bridge. -/
private def failure (input expected : String) : IO Unit := do
  match Json.parse input with
  | .ok _ => throw (IO.userError s!"malformed JSON was accepted: {input}")
  | .error error =>
      unless error == expected do
        throw (IO.userError s!"JSON error differs: '{error}' versus '{expected}'")

/-- Exercise exact decimal fields, Unicode escape behavior and grammar failures.

The valid corpus preserves surrogate fallback/rollback, ordered finite data,
whitespace and duplicate keys. Malformed fixtures retain independently supplied
error strings and byte positions, including non-ASCII input offsets. -/
public def run : IO Unit := do
  let valid : List (String × Json) := [
    ("null", .null), ("true", .bool true), ("false", .bool false),
    (" \t\n\x0d [ ] \t\n", .arr #[]), ("{}", .obj []), ("[]", .arr #[]),
    ("0", .num ⟨0, 0⟩), ("-0", .num ⟨0, 0⟩),
    ("12345", .num ⟨12345, 0⟩), ("-12345", .num ⟨-12345, 0⟩),
    ("0.0", .num ⟨0, 1⟩), ("-0.00", .num ⟨0, 2⟩),
    ("123.4500", .num ⟨1234500, 4⟩), ("1e2", .num ⟨100, 0⟩),
    ("1E+2", .num ⟨100, 0⟩), ("123.4500e-2", .num ⟨1234500, 6⟩),
    ("1e-20", .num ⟨1, 20⟩), ("1e0002", .num ⟨100, 0⟩),
    ("\"ASCII /\"", .str "ASCII /"), ("\"éδ🙂\"", .str "éδ🙂"),
    ("\"\\\"\\\\\\/\\b\\f\\n\\r\\t\"", .str "\"\\/\x08\x0c\n\x0d\t"),
    ("\"\\u0000\\u007f\\u0080\\u07ff\\u0800\\uffff\"", .str "\x00\x7f\u0080\u07ff\u0800\uffff"),
    ("\"\\uD800\\uDC00\"", .str "𐀀"), ("\"\\uDbFf\\uDfFf\"", .str "􏿿"),
    ("\"\\uD83D\\uDE42\"", .str "🙂"),
    ("\"\\uD800\"", .str "�"), ("\"\\uDC00\"", .str "�"),
    ("\"\\uD800x\"", .str "�x"), ("\"\\uD800\\u0041\"", .str "�A"),
    ("\"\\uD800\\uD800\\uDC00\"", .str "�𐀀"), ("\"\\uD800\\n\"", .str "�\n"),
    ("{\"a\":false,\"a\":true}", Json.mkObj [("a", .bool true)]),
    ("{\"🙂\":0,\"δ\":1,\"é\":2,\"a\":3}",
      Json.mkObj [("a", .num ⟨3, 0⟩), ("é", .num ⟨2, 0⟩), ("δ", .num ⟨1, 0⟩), ("🙂", .num ⟨0, 0⟩)]),
    ("[null,{\"nested\":[true,false,12.30]},\"δ\"]",
      .arr #[.null, Json.mkObj [("nested", .arr #[.bool true, .bool false, .num ⟨1230, 2⟩])], .str "δ"])]
  valid.forM fun entry => success entry.1 entry.2
  let malformed := [
    ("", "offset 0: unexpected end of input"),
    (" \t\n", "offset 3: unexpected end of input"),
    ("x", "offset 0: unexpected input"),
    ("nul", "offset 0: expected: null"),
    ("tru", "offset 0: expected: true"),
    ("falsex", "offset 5: expected end of input"),
    ("01", "offset 1: expected end of input"),
    ("-", "offset 1: unexpected end of input"),
    ("--1", "offset 1: expected 1-9"),
    ("1.", "offset 2: unexpected end of input"),
    ("1.e2", "offset 2: expected digit"),
    ("1e", "offset 2: unexpected end of input"),
    ("1e+", "offset 3: unexpected end of input"),
    ("1e-x", "offset 3: expected 0-9"),
    ("[", "offset 1: unexpected end of input"),
    ("[1,]", "offset 3: unexpected input"),
    ("[1 true]", "offset 4: unexpected character in array"),
    ("{", "offset 1: unexpected end of input"),
    ("{x:1}", "offset 1: expected \""),
    ("{\"a\"1}", "offset 4: expected :"),
    ("{\"a\":1,}", "offset 7: expected \""),
    ("\"unterminated", "offset 13: unexpected end of input"),
    ("\"\n\"", "offset 2: unexpected character in string"),
    ("\"\\x\"", "offset 3: illegal \\u escape"),
    ("\"\\u0G00\"", "offset 5: invalid hex character"),
    ("\"\\uD800\\x\"", "offset 9: illegal \\u escape"),
    ("\"é\" false", "offset 5: expected end of input")]
  malformed.forM fun entry => failure entry.1 entry.2
  let oversized := "1e" ++ Nat.repr (USize.size + 1)
  failure oversized s!"offset {oversized.utf8ByteSize}: exp too large"
  let stdout ← IO.getStdout
  stdout.putStr "34 owned JSON parse fixtures and exact malformed-input errors passed\n"

end Test.Data.Json.Parser
