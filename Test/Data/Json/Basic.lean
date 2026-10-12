module

import Purelib.Data.Json.Basic
import Purelib.Data.String.Basic
import Init.System.IO
import Init.System.IOError

open Purelib.Data
open scoped Purelib.Data.String

namespace Test.Data.Json.Basic

/-- Arbitrary original String scalar bytes decode without rebuilding the value. -/
private theorem retained_string (value : String) : Json.getStr? (.str value) = .ok value := rfl
/-- Arbitrary original integer scalars decode without changing the signed value. -/
private theorem retained_integer (value : Int) :
    Json.getInt? (.num (Lean.JsonNumber.fromInt value)) = .ok value := rfl
/-- Arbitrary original natural scalars decode without changing the retained value. -/
private theorem retained_natural (value : Nat) :
    Json.getNat? (.num (Lean.JsonNumber.fromNat value)) = .ok value := rfl
/-- A nonzero retained decimal scale is rejected as an integer. -/
private theorem rejected_scale (value : Int) (exponent : Nat) :
    Json.getInt? (.num ⟨value, exponent + 1⟩) = .error "Integer expected" := rfl

/-- Object construction retains increasing ASCII key order. -/
private theorem ascii_keys :
    Json.mkObj [("z", .null), ("a", .bool true)] =
      .obj [("a", .bool true), ("z", .null)] := rfl
/-- Object construction retains the last original value at a repeated key. -/
private theorem last_duplicate :
    Json.mkObj [("key", .bool false), ("key", .bool true)] =
      .obj [("key", .bool true)] := rfl
/-- Lookup retains the last value even in a directly constructed raw field list. -/
private theorem raw_duplicate :
    Json.getObjValD (.obj [("key", .bool false), ("key", .bool true)]) "key" =
      .bool true := rfl
/-- Missing object fields retain the original null convention. -/
private theorem missing_field : Json.getObjValD (.obj [("key", .bool true)]) "missing" =
    .null := rfl
/-- Object construction retains the UTF-8 ordering of non-ASCII scalar boundaries. -/
private theorem unicode_keys :
    Json.mkObj [("🙂", .null), ("δ", .null), ("é", .null), ("a", .null)] =
      .obj [("a", .null), ("é", .null), ("δ", .null), ("🙂", .null)] := rfl

/-- Numeric constructor injectivity identifies the retained original decimal records. -/
private theorem numeric_fields (left right : Lean.JsonNumber) :
    (Json.num left = Json.num right) ↔ left = right := Json.num.injEq left right
/-- Array constructor injectivity identifies the retained original entry arrays. -/
private theorem array_fields (left right : Array Json) :
    (Json.arr left = Json.arr right) ↔ left = right := Json.arr.injEq left right
/-- Object constructor injectivity identifies the retained original field lists. -/
private theorem object_fields (left right : List (String × Json)) :
    (Json.obj left = Json.obj right) ↔ left = right := Json.obj.injEq left right

/-- Check the public owned equality result against its independently supplied Boolean.

The retained expectation specifies ordered-array and canonical-object behavior.
No old JSON carrier or comparator is imported by this audited regression owner. -/
private def check (label : String) (left right : Json) (expected : Bool) : IO Unit := do
  unless (left == right) == expected do
    throw (IO.userError s!"{label}: owned equality differs from the expected Boolean")

/-- Check actual public-instance comparison on retained nested finite data.

Cases include ordered arrays, field-order independence, final duplicate keys,
original decimal-scale equality and Unicode/control/escape key bytes. The runner
uses executable Boolean comparisons, not native mathematical proof generation. -/
public def run : IO Unit := do
  check "same scalar array"
    (.arr #[.num ⟨1, 0⟩, .str "é", .bool true])
    (.arr #[.num ⟨1, 0⟩, .str "é", .bool true]) true
  check "ordered array mismatch"
    (.arr #[.null, .bool true]) (.arr #[.bool true, .null]) false
  check "array length mismatch" (.arr #[.null]) (.arr #[]) false
  check "nested object input order"
    (Json.mkObj [("z", .arr #[.num ⟨2, 0⟩]), ("a", Json.mkObj [("inner", .str "δ🙂")])])
    (Json.mkObj [("a", Json.mkObj [("inner", .str "δ🙂")]), ("z", .arr #[.num ⟨2, 0⟩])]) true
  check "raw object input order"
    (.obj [("z", .bool true), ("a", .null)]) (.obj [("a", .null), ("z", .bool true)]) true
  check "raw final duplicate retained"
    (.obj [("key", .bool false), ("key", .bool true)]) (Json.mkObj [("key", .bool true)]) true
  check "raw final duplicate changes equality"
    (.obj [("key", .bool true), ("key", .bool false)]) (Json.mkObj [("key", .bool true)]) false
  check "scale-sensitive number" (.num ⟨1, 0⟩) (.num ⟨10, 1⟩) false
  check "same retained decimal record" (.num ⟨-10, 1⟩) (.num ⟨-10, 1⟩) true
  check "Unicode and escape keys"
    (Json.mkObj [("🙂", .str "é"), ("δ", .null), ("\"\\\n", .bool true)])
    (Json.mkObj [("\"\\\n", .bool true), ("δ", .null), ("🙂", .str "é")]) true
  check "Unicode key distinction" (Json.mkObj [("é", .null)]) (Json.mkObj [("e", .null)]) false
  check "different constructor" .null (.arr #[]) false
  let stdout ← IO.getStdout
  stdout.putStr "12 owned JSON equality cases passed\n"

end Test.Data.Json.Basic
