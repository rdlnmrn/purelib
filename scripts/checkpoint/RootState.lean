module

meta import Purelib.Elab.ConstructiveInjectivity
meta import Purelib.Elab.Deriving.Json
import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.String.Basic
import Purelib.Data.List.Control
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic

public import Purelib.RootIsolation.SquareRoot.Replay.PreparedRootStateReplay
public import scripts.checkpoint.Integration
import Init.Prelude
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.RootIsolation.SquareRoot.Replay

section
open Purelib.Data (Json)
open scoped Purelib.Data.String Purelib.Data.List
open Purelib.Data.Json (toJson)

public section

/-!
Finite codecs shared by the real snapshot producer and its checked loader.
The optional ambient bounds preserve old snapshots as explicitly incomplete
inputs; the loader never substitutes the boundary minimum for missing values.
-/

namespace RootStateCheckpoint

open IntegrationCheckpoint

set_option genInjectivity false in
/-- Serialized root-box and clearance data with explicit optional ambient bounds.

Missing legacy ambient bounds remain incomplete inputs and are never reconstructed from an unrelated boundary bound. -/
structure RawData where
  /-- The four exact serialized coordinates of the retained root box. -/ box : List FractionData
  /-- The exact serialized boundary clearance. -/ clearance : FractionData
  /-- The optional four original ambient-line clearances, in left/right/bottom/top order. -/ ambientClearances : Option
    (List FractionData) := none
deriving Json.ToJson, Json.FromJson

constructive_injectivity RawData

set_option genInjectivity false in
/-- A later point query can reconstruct its nonstationary transport from the saved source state. This records the actual
request, not a guessed step.

The target, reserve and optional retention floor retain distinct exact
encodings. Decoding checks them before transporting the original root state. -/
structure TransportRequest where
  /-- The original requested target point. -/ target : GaussianData
  /-- The exact retained reserve requested for transport. -/ reserve : FractionData
  /-- Absent in legacy point-query records. A prepared-spine successor also applies this floor after transport; it must
  not be guessed on reload. -/
  retentionFloor : Option FractionData := none
deriving Json.ToJson, Json.FromJson

constructive_injectivity TransportRequest

/-- Serialize box coordinates in lower-x, upper-x, lower-y, upper-y order. -/
@[expose] def boxData (box : Rational.Box) : List FractionData :=
  [box.xLower, box.xUpper, box.yLower, box.yUpper].map fractionData

/-- Serialize a root state's box, boundary bound and four original ambient-line bounds. -/
@[expose] def encode (data : PreparedRootStateReplay.Data) : RawData :=
  ⟨boxData data.box, fractionData data.boundary,
    some ([data.left, data.right, data.bottom, data.top].map fractionData)⟩

/-- Capture the exact numerical replay data of the original retained root state. -/
@[expose] def capture {parameter : Data.Gaussian.Basic.Canonical} {ambient : Rational.Box}
    (state : PreparedRootStateReplay.State parameter ambient) : RawData :=
  encode (PreparedRootStateReplay.capture state)

set_option genInjectivity false in
/-- A scalar decoding, coordinate-count or interval-order failure for a saved box. -/
inductive BoxFailure where
  /-- An invalid exact scalar encoding. -/ | field (failure : InvalidData)
  /-- The decoded coordinate list has a certified length different from four. -/ | arity (values : List
    Fraction.Rational) (failed : values.length ≠ 4)
  /-- The actual horizontal bounds fail their required order. -/ | horizontal (lower upper : Fraction.Rational) (failed
    : ¬ lower ≤ upper)
  /-- The actual vertical bounds fail their required order. -/ | vertical (lower upper : Fraction.Rational) (failed : ¬
    lower ≤ upper)

constructive_injectivity BoxFailure

/-- Decode four rational coordinates and certify both interval orders.

Failure retains the invalid field, wrong coordinate list or exact unordered interval operands. -/
@[expose] def decodeBox (raw : List FractionData) : Except BoxFailure Rational.Box := do
  let values ← (raw.mapM decodeFraction).mapError .field
  if count : values.length = 4 then
    let xl := values[0]'(by omega)
    let xu := values[1]'(by omega)
    let yl := values[2]'(by omega)
    let yu := values[3]'(by omega)
    if x : xl ≤ xu then
      if y : yl ≤ yu then return ⟨xl, xu, yl, yu, x, y⟩
      else .error (.vertical yl yu y)
    else .error (.horizontal xl xu x)
  else .error (.arity values count)

set_option genInjectivity false in
/-- A certified invalidity or missing-data condition for the original saved root record. -/
inductive Failure (raw : RawData) where
  /-- The original record explicitly omits its ambient-line bounds. -/ | missingAmbientBounds (omitted :
    raw.ambientClearances = none)
  /-- An exact scalar field fails decoding. -/ | field (failure : InvalidData)
  /-- The retained box fails its coordinate or interval checks. -/ | box (failure : BoxFailure)
  /-- The original ambient-bound list has a certified length different from four. -/ | arity (values : List
    FractionData)
      (recorded : raw.ambientClearances = some values) (failed : values.length ≠ 4)

constructive_injectivity Failure

/-- Decode the complete retained root-state payload.

Reject absent or incorrectly sized ambient bounds while retaining their association with the original raw record. -/
@[expose] def decode (raw : RawData) : Except (Failure raw) PreparedRootStateReplay.Data := do
  match recorded : raw.ambientClearances with
  | none => .error (.missingAmbientBounds recorded)
  | some values =>
    if count : values.length = 4 then
      let box ← (decodeBox raw.box).mapError .box
      let boundary ← (decodeFraction raw.clearance).mapError .field
      let left ← (decodeFraction (values[0]'(by omega))).mapError .field
      let right ← (decodeFraction (values[1]'(by omega))).mapError .field
      let bottom ← (decodeFraction (values[2]'(by omega))).mapError .field
      let top ← (decodeFraction (values[3]'(by omega))).mapError .field
      return ⟨box, boundary, left, right, bottom, top⟩
    else .error (.arity values recorded count)

/-- A nested state payload must agree with the parent record's original box and boundary number. Keep the actual unequal
operands on rejection. -/
@[expose] def checkBoxBoundary (actualBox : Rational.Box) (actualBoundary : Fraction.Rational)
    (box : Rational.Box) (boundary : Fraction.Rational) : Except InvalidData Unit := do
  for (label, actual, expected) in
      [("root xLower", actualBox.xLower, box.xLower),
       ("root xUpper", actualBox.xUpper, box.xUpper),
       ("root yLower", actualBox.yLower, box.yLower),
       ("root yUpper", actualBox.yUpper, box.yUpper),
       ("root boundary", actualBoundary, boundary)] do
    if same : actual = expected then pure ()
    else .error (.rationalMismatch label actual expected same)

/-- Check the saved replay data against its original parent's box and boundary bound. -/
@[expose] def checkParent (data : PreparedRootStateReplay.Data) (box : Rational.Box) (boundary :
  Fraction.Rational) : Except InvalidData Unit :=
  checkBoxBoundary data.box data.boundary box boundary

/-- Serialize the exact box-coordinate or interval-order failure. -/
@[expose] def BoxFailure.report : BoxFailure → Json
  | .field failure => Json.mkObj [("kind", toJson failure.message)]
  | .arity values _ => Json.mkObj
      [("kind", toJson "box coordinate count"), ("actual", toJson values.length),
       ("expected", toJson (4 : Nat))]
  | .horizontal lower upper _ => Json.mkObj
      [("kind", toJson "inverted horizontal interval"),
       ("lower", toJson (fractionData lower)), ("upper", toJson (fractionData upper))]
  | .vertical lower upper _ => Json.mkObj
      [("kind", toJson "inverted vertical interval"),
       ("lower", toJson (fractionData lower)), ("upper", toJson (fractionData upper))]

/-- Serialize the invalidity and retain the original record when required bounds are incomplete. -/
@[expose] def Failure.report {raw : RawData} : Failure raw → Json
  | .missingAmbientBounds _ => Json.mkObj
      [("kind", toJson "incomplete saved state; original ambient-line bounds missing"),
       ("missing", toJson (["left", "right", "bottom", "top"] : List String)),
       ("retained", toJson raw)]
  | .field failure => Json.mkObj [("kind", toJson failure.message)]
  | .box failure => failure.report
  | .arity values _ _ => Json.mkObj
      [("kind", toJson "ambient-line bound count"),
       ("actual", toJson values.length), ("expected", toJson (4 : Nat)),
       ("retained", toJson raw)]

end RootStateCheckpoint

end
