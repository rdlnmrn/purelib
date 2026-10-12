module

-- The public numeric field retains the original decimal scalar owner.
public import Purelib.Data.Json.Number
-- Exposed diagnostics retain the original native String append record.
public import Purelib.Data.String.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open scoped Purelib.Data.String

/-!
# Finite JSON values

JSON values retain ordered arrays and finite object entries. Object construction
uses a deterministic bytewise key order and replaces earlier duplicate keys.
-/

namespace Purelib.Data

set_option genInjectivity false in
/-- A finite JSON value containing scalar data, ordered arrays and object fields.

The scalar numeric representation retains Lean's original mantissa and decimal
exponent. Object operations normalize finite field lists without ordered maps. -/
public inductive Json where
  /-- The JSON null value. -/ | null
  /-- A Boolean JSON value. -/ | bool (value : Bool)
  /-- A numeric JSON value with the original decimal scalar representation. -/
  | num (value : Lean.JsonNumber)
  /-- A Unicode string retaining its original UTF-8 bytes. -/ | str (value : String)
  /-- An ordered finite array of JSON values. -/ | arr (values : Array Json)
  /-- A finite list of JSON object fields; object operations canonicalize this list. -/
  | obj (fields : List (String × Json))

constructive_injectivity Json

namespace Json

/-- Insert a field in a sorted finite object, replacing an existing matching key.

The retained fields before and after the selected key keep their original values
and order. Replacement implements the original last-occurrence-wins behavior. -/
@[expose] public def insertField (key : String) (value : Json) :
    List (String × Json) → List (String × Json)
  | [] => [(key, value)]
  | (priorKey, priorValue) :: rest =>
      match Purelib.Data.String.compare key priorKey with
      | .lt => (key, value) :: (priorKey, priorValue) :: rest
      | .eq => (key, value) :: rest
      | .gt => (priorKey, priorValue) :: insertField key value rest

/-- Canonicalize finite object fields in their original insertion order.

Each later field replaces the earlier field at its key. The resulting entries
have increasing key order and retain the last value for every key. -/
@[expose] public def objectFields (fields : List (String × Json)) : List (String × Json) :=
  let rec loop (remaining : List (String × Json)) (retained : List (String × Json)) :=
    match remaining with
    | [] => retained
    | (key, value) :: rest => loop rest (insertField key value retained)
  loop fields []

/-- Construct a JSON object from a finite sequence of named values.

For distinct keys, input order does not affect the resulting canonical fields.
Repeated keys retain the last input value under the original key bytes. -/
@[expose] public def mkObj (fields : List (String × Json)) : Json :=
  .obj (objectFields fields)

/-- Look up the last retained value of a key in a finite field list.

Scanning the complete list makes lookup agree with object construction even for
object values assembled directly with repeated or unsorted fields. -/
@[expose] public def findField (key : String) : List (String × Json) → Option Json
  | [] => none
  | (priorKey, priorValue) :: rest =>
      match findField key rest with
      | some value => some value
      | none =>
          match Purelib.Data.String.compare key priorKey with
          | .eq => some priorValue
          | .lt => none
          | .gt => none

/-- Read an object field, returning JSON null when the field is absent.

This preserves the existing decoder convention: missing optional fields become
none through the null codec; missing required fields fail their own scalar codec. -/
@[expose] public def getObjValD (json : Json) (key : String) : Json :=
  match json with
  | .obj fields =>
      match findField key fields with
      | some value => value
      | none => .null
  | .null => .null
  | .bool _ => .null
  | .num _ => .null
  | .str _ => .null
  | .arr _ => .null

/-- Recognize exactly the null JSON constructor.

Recognition reads only the displayed constructor. Every scalar, array and object
value returns false without inspecting its retained data. -/
@[expose] public def isNull : Json → Bool
  | .null => true
  | .bool _ => false
  | .num _ => false
  | .str _ => false
  | .arr _ => false
  | .obj _ => false

set_option backward.match.sparseCases false in
/-- Read the retained string, with the original scalar mismatch diagnostic.

String values return their original valid UTF-8 byte owner. Every other
constructor returns the exact original String mismatch diagnostic. -/
@[expose] public def getStr? : Json → Except String String
  | .str value => .ok value
  | _ => .error "String expected"

set_option backward.match.sparseCases false in
/-- Read the retained Boolean, with the original scalar mismatch diagnostic.

Boolean values return their original truth value. Every other constructor
returns the exact original Bool mismatch diagnostic. -/
@[expose] public def getBool? : Json → Except String Bool
  | .bool value => .ok value
  | _ => .error "Bool expected"

set_option backward.match.sparseCases false in
/-- Read the original decimal-number representation without normalizing its scale.

Every numeric constructor returns its exact retained mantissa and exponent.
Other JSON constructors return the original numeric mismatch diagnostic. -/
@[expose] public def getNum? : Json → Except String Lean.JsonNumber
  | .num value => .ok value
  | _ => .error "number expected"

set_option backward.match.sparseCases false in
/-- Decode the original natural-number JSON representation.

The original decimal-number codec rejects negative values and positive decimal
scales. Other JSON constructors retain the original scalar mismatch diagnostic. -/
@[expose] public def getNat? : Json → Except String Nat
  | .num value => Number.getNat? value
  | _ => .error "Natural number expected"

set_option backward.match.sparseCases false in
/-- Decode the original integer JSON representation.

Exponent-zero records retain their original signed mantissa. Positive decimal
scales and other JSON constructors retain the original mismatch diagnostic. -/
@[expose] public def getInt? : Json → Except String Int
  | .num value => Number.getInt? value
  | _ => .error "Integer expected"

set_option backward.match.sparseCases false in
/-- Read an ordered JSON array, with the original constructor mismatch diagnostic.

Array values return their exact retained entry array without rebuilding it.
Every other constructor returns the original array mismatch diagnostic. -/
@[expose] public def getArr? : Json → Except String (Array Json)
  | .arr values => .ok values
  | _ => .error "array expected"

set_option backward.match.sparseCases false in
/-- Read a finite object's canonical retained fields.

The fields use last-occurrence-wins insertion and increasing UTF-8 key order.
Other constructors retain the original object mismatch diagnostic. -/
@[expose] public def getObj? : Json → Except String (List (String × Json))
  | .obj fields => .ok (objectFields fields)
  | _ => .error "object expected"

set_option backward.match.sparseCases false in
/-- Read a retained object property or identify its missing key.

Lookup consumes the original field list and selects its final occurrence. A
non-object retains the original object mismatch diagnostic. -/
@[expose] public def getObjVal? (value : Json) (key : String) : Except String Json :=
  match value with
  | .obj fields =>
      match findField key fields with
      | some entry => .ok entry
      | none => .error s!"property not found: {key}"
  | _ => .error "object expected"

/-- Natural values retain the original decimal mantissa and exponent zero.

The coercion uses Lean.JsonNumber.fromNat directly. It introduces no decimal
normalization or change to the retained natural value. -/
public instance : Coe Nat Json := ⟨fun value => .num (Lean.JsonNumber.fromNat value)⟩
/-- Integer values retain the original signed mantissa and exponent zero.

The coercion uses Lean.JsonNumber.fromInt directly. It introduces no decimal
normalization or change to the retained signed value. -/
public instance : Coe Int Json := ⟨fun value => .num (Lean.JsonNumber.fromInt value)⟩
/-- Strings retain their original valid UTF-8 byte owner.

The coercion stores the exact original String value. Its byte array and
validity certificate are not rebuilt or decoded. -/
public instance : Coe String Json := ⟨Json.str⟩
/-- Booleans retain their original scalar truth value.

The coercion stores the exact supplied Boolean in the displayed constructor.
It introduces no encoding or interpretation step. -/
public instance : Coe Bool Json := ⟨Json.bool⟩
/-- Natural literals retain the original decimal mantissa and exponent zero.

The literal instance uses Lean.JsonNumber.fromNat directly. The original
value and exponent-zero convention are retained without normalization. -/
public instance : OfNat Json value := ⟨.num (Lean.JsonNumber.fromNat value)⟩
/-- The default finite JSON value is null.

The instance supplies the displayed null constructor. No scalar, array, object
or retained owner is selected to provide the default. -/
public instance : Inhabited Json := ⟨.null⟩

set_option backward.match.sparseCases false in
/-- Compare finite JSON data by its original scalar and container representations.

Arrays retain their entry order. Objects compare their canonical key sets and
retained values, matching the original field-order-independent comparison; numeric
records compare their exact original mantissa and exponent without normalization. -/
private partial def beq (left right : Json) : Bool :=
  match left, right with
  | .null, .null => true
  | .bool first, .bool second => first == second
  | .num first, .num second => Number.beq first second
  | .str first, .str second => first == second
  | .arr first, .arr second =>
      let _ : BEq Json := ⟨beq⟩
      first == second
  | .obj first, .obj second =>
      let first := objectFields first
      let second := objectFields second
      first.length == second.length && first.all fun (key, value) =>
        match findField key second with
        | none => false
        | some other => beq value other
  | _, _ => false

/-- JSON Boolean comparison retains ordered arrays and canonical object fields.

The instance uses the same recursive scalar and container comparison. Object
comparison ignores insertion order while retaining each final key value. -/
public instance : BEq Json where
  beq := private beq

end Json
end Purelib.Data
