module

meta import Purelib.Elab.Deriving.Json
import Purelib.Data.Json.Codec
import Purelib.Data.String.Basic
import Init.System.IO
import Init.System.IOError
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data
open Purelib.Data.Json (fromJson? toJson)
open scoped Purelib.Data.String

namespace Test.Data.Json.Codec

set_option genInjectivity false in
/-- Retained scalar and optional fields with the original record wire convention.

The trailing question mark omits an absent caption from the object. The count is
required by decoding even though its record constructor has a default value. -/
private structure Entry where
  /-- The retained entry name. -/
  name : String
  /-- A retained required count with a constructor default. -/
  count : Nat := 7
  /-- An optional caption omitted when absent. -/
  caption? : Option String := none
  deriving Json.ToJson, Json.FromJson

constructive_injectivity Entry

set_option genInjectivity false in
/-- A nested record retaining ordered entry data and a paired scalar field.

This tests the original flattened record convention together with ordered list
and nested-pair codecs. No copied owner or positional field reconstruction occurs. -/
private structure Bundle where
  /-- Original ordered entries. -/
  entries : List Entry
  /-- An ordered name and Boolean pair. -/
  pair : String × Bool
  deriving Json.ToJson, Json.FromJson

constructive_injectivity Bundle

/-- Natural scalars retain the original exponent-zero builder. -/
private theorem encode_natural (value : Nat) :
    toJson value = Json.num (Lean.JsonNumber.fromNat value) := rfl
/-- Original integer scalars decode without changing their signed value. -/
private theorem decode_integer (value : Int) :
    (fromJson? (Json.num (Lean.JsonNumber.fromInt value)) : Except String Int) = .ok value := rfl
/-- Ordered natural arrays retain each original decoded entry. -/
private theorem decode_array :
    (fromJson? (Json.arr #[.num ⟨2, 0⟩, .num ⟨5, 0⟩]) : Except String (Array Nat)) =
      .ok #[2, 5] := rfl
/-- List decoding retains the original array order. -/
private theorem decode_list :
    (fromJson? (Json.arr #[.bool true, .bool false]) : Except String (List Bool)) =
      .ok [true, false] := rfl
/-- Null retains the original nested optional-value ambiguity. -/
private theorem nested_null :
    (fromJson? Json.null : Except String (Option (Option Nat))) = .ok none := rfl
/-- The first bad array entry retains the original scalar diagnostic. -/
private theorem first_array_error :
    (fromJson? (Json.arr #[.num ⟨1, 0⟩, .str "wrong", .bool false]) :
      Except String (Array Nat)) = .error "Natural number expected" := rfl
/-- Two entries retain the original pair order and scalar results. -/
private theorem decode_pair :
    (fromJson? (Json.arr #[.str "name", .bool true]) : Except String (String × Bool)) =
      .ok ("name", true) := rfl
/-- A missing optional object field decodes through the retained null value. -/
private theorem optional_missing :
    Json.getObjValAs? (Json.mkObj []) (Option String) "caption" = .ok none := rfl
/-- A missing required field retains its scalar failure despite constructor defaults. -/
private theorem required_missing :
    Json.getObjValAs? (Json.mkObj []) Nat "count" = .error "Natural number expected" := rfl
/-- Present optional captions retain the original field key without its suffix. -/
private theorem optional_key :
    Json.opt "caption" (some "retained") = [("caption", Json.str "retained")] := rfl
/-- An absent optional caption emits no object field. -/
private theorem absent_key : Json.opt "caption" (none : Option String) = [] := rfl
/-- Exactly the empty JSON object retains the original Unit value. -/
private theorem decode_unit : (fromJson? (Json.obj []) : Except String Unit) = .ok () := rfl

/-- Retain a supplied Boolean expectation for an executable codec fixture.

The check only runs owned public codecs and printers. Failures identify the exact
fixture without introducing a native mathematical decision proof. -/
private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw (IO.userError s!"{label}: owned JSON codec result differs from the fixture")

/-- Recognize the retained diagnostic of a failed codec attempt.

A successful value is rejected by this fixture check. A failed attempt compares
its exact diagnostic bytes with the expected error text. -/
private def hasError {Alpha : Type} (result : Except String Alpha) (expected : String) : Bool :=
  match result with
  | .ok _ => false
  | .error message => message == expected

/-- Exercise derived records and scalar/container failure behavior at runtime.

The fixtures retain missing required fields, omitted optional fields, ordered
nested data and default-width diagnostic rendering. They import no old JSON
carrier, codec or comparison instance. -/
public def run : IO Unit := do
  let entry : Entry := ⟨"éδ🙂", 3, none⟩
  let withCaption : Entry := ⟨"retained", 4, some "caption"⟩
  check "optional omitted"
    (toJson entry == Json.mkObj [("name", .str "éδ🙂"), ("count", .num ⟨3, 0⟩)])
  check "optional retained"
    (toJson withCaption == Json.mkObj [("name", .str "retained"), ("count", .num ⟨4, 0⟩),
      ("caption", .str "caption")])
  match (fromJson? (toJson entry) : Except String Entry) with
  | .error message => throw (IO.userError message)
  | .ok retained =>
      check "record original fields"
        (retained.name == entry.name && retained.count == entry.count && retained.caption? == entry.caption?)
  let bundle : Bundle := ⟨[entry, withCaption], ("ordered", true)⟩
  match (fromJson? (toJson bundle) : Except String Bundle) with
  | .error message => throw (IO.userError message)
  | .ok retained =>
      check "nested retained encoding" (toJson retained == toJson bundle)
  check "array shape diagnostic"
    (hasError (fromJson? Json.null : Except String (Array Nat)) "expected JSON array, got 'null'")
  check "pair shape diagnostic"
    (hasError (fromJson? (Json.arr #[]) : Except String (Nat × Nat)) "expected pair, got '[]'")
  check "unit shape diagnostic"
    (hasError (fromJson? Json.null : Except String Unit) "expected {} to decode Unit, got null")
  check "scaled integer rejection"
    (hasError (fromJson? (Json.num ⟨10, 1⟩) : Except String Int) "Integer expected")
  check "negative natural rejection"
    (hasError (fromJson? (Json.num ⟨-1, 0⟩) : Except String Nat) "Natural number expected")
  let stdout ← IO.getStdout
  stdout.putStr "owned scalar/container and derived JSON codec cases passed\n"

end Test.Data.Json.Codec
