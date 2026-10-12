module

-- Codec fields and executable diagnostics retain the owned JSON printer API.
public import Purelib.Data.Json.Printer
-- Public path codec signatures retain this original nominal path owner.
public import Init.System.FilePath
import Purelib.Data.Json.Basic
import Purelib.Data.String.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open scoped Purelib.Data.String

/-!
# Finite JSON value codecs

These codecs preserve the scalar representations, container ordering, missing
optional fields and first-error behavior of the original JSON wire format.
-/

public section

namespace Purelib.Data.Json

universe u v

set_option genInjectivity false in
/-- Decode a finite JSON value into its retained typed data.

Failure retains the original diagnostic text. Container decoders stop at the
first invalid entry and preserve the input order of all preceding entries. -/
public class FromJson (Alpha : Type u) where
  /-- Decode the supplied JSON value or retain its scalar or structural error. -/
  fromJson? : Json → Except String Alpha

constructive_injectivity FromJson

set_option genInjectivity false in
/-- Encode typed data into its finite JSON value.

The representation uses original decimal scalars, ordered arrays and finite
objects. Optional values use null, including the original nested-option ambiguity. -/
public class ToJson (Alpha : Type u) where
  /-- Encode the supplied value with its retained scalar and container data. -/
  toJson : Alpha → Json

constructive_injectivity ToJson

export FromJson (fromJson?)
export ToJson (toJson)

/-- JSON values decode without rebuilding their retained finite data.

The instance uses the displayed owned decoder and retains its original scalar
or container mismatch diagnostic. It does not supply missing required values. -/
public instance : FromJson Json := ⟨Except.ok⟩
/-- JSON values encode without rebuilding their retained finite data.

The instance uses the displayed original scalar or container convention.
It retains supplied data and introduces no additional normalization. -/
public instance : ToJson Json := ⟨id⟩
/-- Decimal scalars decode without normalization of the retained scale.

The instance uses the displayed owned decoder and retains its original scalar
or container mismatch diagnostic. It does not supply missing required values. -/
public instance : FromJson Lean.JsonNumber := ⟨Json.getNum?⟩
/-- Decimal scalars encode with their original nominal mantissa and exponent.

The instance uses the displayed original scalar or container convention.
It retains supplied data and introduces no additional normalization. -/
public instance : ToJson Lean.JsonNumber := ⟨Json.num⟩
/-- Boolean values decode from the exact Boolean constructor.

The instance uses the displayed owned decoder and retains its original scalar
or container mismatch diagnostic. It does not supply missing required values. -/
public instance : FromJson Bool := ⟨Json.getBool?⟩
/-- Boolean values encode with their original truth value.

The instance uses the displayed original scalar or container convention.
It retains supplied data and introduces no additional normalization. -/
public instance : ToJson Bool := ⟨Json.bool⟩
/-- Natural values decode only from original nonnegative exponent-zero records.

The instance uses the displayed owned decoder and retains its original scalar
or container mismatch diagnostic. It does not supply missing required values. -/
public instance : FromJson Nat := ⟨Json.getNat?⟩
/-- Natural values encode with the original decimal builder.

The instance uses the displayed original scalar or container convention.
It retains supplied data and introduces no additional normalization. -/
public instance : ToJson Nat := ⟨fun value => .num (Lean.JsonNumber.fromNat value)⟩
/-- Integer values decode only from original exponent-zero records.

The instance uses the displayed owned decoder and retains its original scalar
or container mismatch diagnostic. It does not supply missing required values. -/
public instance : FromJson Int := ⟨Json.getInt?⟩
/-- Integer values encode with the original signed decimal builder.

The instance uses the displayed original scalar or container convention.
It retains supplied data and introduces no additional normalization. -/
public instance : ToJson Int := ⟨fun value => .num (Lean.JsonNumber.fromInt value)⟩
/-- Strings decode with their original valid UTF-8 byte owner.

The instance uses the displayed owned decoder and retains its original scalar
or container mismatch diagnostic. It does not supply missing required values. -/
public instance : FromJson String := ⟨Json.getStr?⟩
/-- Strings encode with their original valid UTF-8 byte owner.

The instance uses the displayed original scalar or container convention.
It retains supplied data and introduces no additional normalization. -/
public instance : ToJson String := ⟨Json.str⟩
/-- File paths decode from their original string representation.

The instance uses the displayed owned decoder and retains its original scalar
or container mismatch diagnostic. It does not supply missing required values. -/
public instance : FromJson System.FilePath :=
  ⟨fun value => (Json.getStr? value).map System.FilePath.mk⟩
/-- File paths encode with their original string representation.

The instance uses the displayed original scalar or container convention.
It retains supplied data and introduces no additional normalization. -/
public instance : ToJson System.FilePath := ⟨fun value => .str value.toString⟩

/-- Decode a finite entry list, retaining the first invalid entry's diagnostic.

Each successful head retains the original typed decoded value. The recursive
call consumes only the original tail, without reordering or retrying any entry. -/
@[expose] public def decodeEntries {Alpha : Type u} [FromJson Alpha] :
    List Json → Except String (List Alpha)
  | [] => .ok []
  | head :: tail => do
      let value ← fromJson? head
      let retained ← decodeEntries tail
      return value :: retained

set_option backward.match.sparseCases false in
/-- Decode a JSON array in its original order.

A successful array retains each scalar decoder result. A non-array returns the
original array mismatch diagnostic, rendered with the owned default JSON printer. -/
@[expose] public def decodeArray {Alpha : Type u} [FromJson Alpha] :
    Json → Except String (Array Alpha)
  | .arr values => (decodeEntries values.toList).map List.toArray
  | value => .error s!"expected JSON array, got '{value}'"

/-- Arrays decode in their original entry order.

The instance uses the displayed owned decoder and retains its original scalar
or container mismatch diagnostic. It does not supply missing required values. -/
public instance {Alpha : Type u} [FromJson Alpha] : FromJson (Array Alpha) := ⟨decodeArray⟩
/-- Arrays encode in their original entry order.

The instance uses the displayed original scalar or container convention.
It retains supplied data and introduces no additional normalization. -/
public instance {Alpha : Type u} [ToJson Alpha] : ToJson (Array Alpha) :=
  ⟨fun values => .arr (values.toList.map toJson).toArray⟩
/-- Lists decode from ordered JSON arrays.

The instance uses the displayed owned decoder and retains its original scalar
or container mismatch diagnostic. It does not supply missing required values. -/
public instance {Alpha : Type u} [FromJson Alpha] : FromJson (List Alpha) :=
  ⟨fun value => (decodeArray value).map Array.toList⟩
/-- Lists encode as ordered JSON arrays.

The instance uses the displayed original scalar or container convention.
It retains supplied data and introduces no additional normalization. -/
public instance {Alpha : Type u} [ToJson Alpha] : ToJson (List Alpha) :=
  ⟨fun values => .arr (values.map toJson).toArray⟩

set_option backward.match.sparseCases false in
/-- Decode null as none and every other value with the retained element codec.

The decoder preserves the original nested-option ambiguity: null becomes none
rather than some none. A non-null failure retains the scalar decoder's error. -/
@[expose] public def decodeOption {Alpha : Type u} [FromJson Alpha] :
    Json → Except String (Option Alpha)
  | .null => .ok none
  | value => (fromJson? value).map some

/-- Optional values decode with the original null convention.

The instance uses the displayed owned decoder and retains its original scalar
or container mismatch diagnostic. It does not supply missing required values. -/
public instance {Alpha : Type u} [FromJson Alpha] : FromJson (Option Alpha) := ⟨decodeOption⟩
/-- Optional values encode none as null and some with the retained element codec.

The instance uses the displayed original scalar or container convention.
It retains supplied data and introduces no additional normalization. -/
public instance {Alpha : Type u} [ToJson Alpha] : ToJson (Option Alpha) where
  toJson
    | none => .null
    | some value => toJson value

set_option backward.match.sparseCases false in
/-- Decode a pair from exactly two ordered JSON array entries.

The first scalar failure is retained; the second codec runs only after the
first succeeds. Every other shape returns the original pair mismatch diagnostic. -/
@[expose] public def decodePair {Alpha : Type u} {Beta : Type v}
    [FromJson Alpha] [FromJson Beta] (value : Json) : Except String (Alpha × Beta) :=
  match value with
  | .arr values =>
      match values.toList with
      | [left, right] => do
          let ⟨first⟩ : ULift.{v} Alpha ← (fromJson? left).map ULift.up
          let ⟨second⟩ : ULift.{u} Beta ← (fromJson? right).map ULift.up
          return (first, second)
      | _ => .error s!"expected pair, got '{value}'"
  | _ => .error s!"expected pair, got '{value}'"

/-- Pairs decode from exactly two ordered JSON entries.

The instance uses the displayed owned decoder and retains its original scalar
or container mismatch diagnostic. It does not supply missing required values. -/
public instance {Alpha : Type u} {Beta : Type v} [FromJson Alpha] [FromJson Beta] :
    FromJson (Alpha × Beta) := ⟨decodePair⟩
/-- Pairs encode as two ordered entries, preserving nested-pair structure.

The instance uses the displayed original scalar or container convention.
It retains supplied data and introduces no additional normalization. -/
public instance {Alpha : Type u} {Beta : Type v} [ToJson Alpha] [ToJson Beta] :
    ToJson (Alpha × Beta) := ⟨fun (left, right) => .arr #[toJson left, toJson right]⟩

set_option backward.match.sparseCases false in
/-- Decode Unit from exactly an empty JSON object.

An object is accepted exactly when its retained field list is empty. Every other
value retains the original mismatch diagnostic rendered by the default JSON printer. -/
@[expose] public def decodeUnit (value : Json) : Except String Unit :=
  match value with
  | .obj [] => .ok ()
  | _ => .error s!"expected \{} to decode Unit, got {value}"

/-- Unit decodes only from an empty JSON object.

The instance uses the displayed owned decoder and retains its original scalar
or container mismatch diagnostic. It does not supply missing required values. -/
public instance : FromJson Unit := ⟨decodeUnit⟩
/-- Unit encodes as an empty JSON object.

The instance uses the displayed original scalar or container convention.
It retains supplied data and introduces no additional normalization. -/
public instance : ToJson Unit := ⟨fun _ => .obj []⟩

/-- Decode a named field using the original null convention for missing keys.

The retained field codec decides whether null is valid. Missing optional values
become none; missing required values retain their original scalar error. -/
@[expose] public def getObjValAs? (value : Json) (Alpha : Type u) [FromJson Alpha]
    (key : String) : Except String Alpha :=
  fromJson? (value.getObjValD key)

/-- Omit an absent optional object field and retain a present field's original value.

Record encoders use this operation for field names ending in a question mark.
Present values retain the original key with that suffix removed. -/
@[expose] public def opt {Alpha : Type u} [ToJson Alpha] (key : String) :
    Option Alpha → List (String × Json)
  | none => []
  | some value => [(key, toJson value)]

end Purelib.Data.Json
