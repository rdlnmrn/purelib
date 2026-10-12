module

import Purelib.System.IO
import Purelib.System.FilePath
import Purelib.Data.String.Parsing

meta import Purelib.Elab.ConstructiveInjectivity
meta import Purelib.Elab.Deriving.Json
import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.String.Basic
import Purelib.Data.Int.Decimal
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Pair.Bezout
import Purelib.Polynomial.Clearance.Pair.Replay
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Bounds.AffineHorner
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.Riemann.Transport.PreparedCenterReplay

import Purelib.Polynomial.Dense.GCD
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
import Purelib.RootIsolation.SquareRoot.Replay.PreparedBoundaryReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedOwnerTransportReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedRawStateReplay
public import Purelib.RootIsolation.SquareRoot.Replay.PreparedRetainedTransportReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedRootStateReplay
public import scripts.checkpoint.Center
import scripts.checkpoint.RootState
public import scripts.checkpoint.Integration.Import
import Init.Data.Int.Basic
import Init.Data.Repr
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Riemann.RootContinuation.SquareRootContinuation
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Std.Data.DTreeMap.Internal.Def
import Std.Data.DTreeMap.Raw.Basic
import Std.Data.TreeMap.Raw.Basic
import scripts.checkpoint.Integration

-- Use complete constructor eliminators for the original match arms.
set_option backward.match.sparseCases false

open Purelib

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Cast

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

section
open Purelib.Data (Json)
open scoped Purelib.Data.List Purelib.Data.Range Purelib.Data.String Purelib.Data.Int.Decimal
open Purelib.Data.Json (toJson fromJson?)

public section

/-!
Restore the exact boundary-clearance numbers in saved v1 root-owner records.
Extended Euclid is an untrusted witness producer only.  Reload checks finite
coefficient identities and bound products without Euclidean generation.
All attempts, including insufficient witnesses, are saved incrementally.
Complete-state mode also restores all four original ambient-line certificates
and checks winding from the producer's extended payload.  Missing legacy
fields and unidentified owner construction/history remain explicit gaps.
Transport mode consumes the actual saved endpoint request, reconstructs the
inexpensive nonstationary branch without the incoming refinement function,
then applies a saved endpoint-retention floor when present.  Point-transport
and complete endpoint payloads have separate checked caches; legacy missing
floors are never guessed.  Reset-required results preserve both failed bounds
without running the reset.  Canonical source
association is a separate obligation; stationary moves still need history.
Run under an explicit SIGKILL timeout and systemd memory bounds.
-/

namespace SavedBoundaryHarness

open Purelib.RootIsolation.SquareRoot.Replay.PreparedBoundaryReplay
  (Witness Witnesses Box Polynomial Gaussian Coordinate)

open IntegrationCheckpoint

open Purelib.Polynomial.Dense.Basic.DensePolynomial (scale constant)
open Purelib.Data.Gaussian.Cast.Winding (verticalBase)
open Purelib.Data.Gaussian.Constants renaming imaginaryUnit -> verticalDirection

set_option genInjectivity false in
/-- The header of an ordered saved refinement-parent stream.

The retained count identifies the finite number of supplied parent records.
It supplies no original parent ownership or relation witness by itself. -/
structure Header where
  /-- The exact number of ordered parent records in the input stream. -/ parentCount : Nat
deriving Json.FromJson, Json.ToJson

constructive_injectivity Header

set_option genInjectivity false in
/-- Serialized original parent data with explicit optional complete-state and transport payloads.

Legacy omissions remain absent; they do not imply reconstructed ambient bounds, retention floors or canonical source
history. -/
structure Parent where
  /-- The original zero-based parent index. -/ parent : Nat
  /-- The exact serialized Gaussian square-root parameter. -/ parameter : GaussianData
  /-- The original root box coordinates. -/ box : List FractionData
  /-- The original boundary-clearance bound. -/ clearance : FractionData
  /-- The original ambient box coordinates, absent in legacy incomplete records. -/ ambient : List FractionData := []
  /-- The optional complete original state payload including ambient-line bounds. -/ rootState : Option
    RootStateCheckpoint.RawData := none
  /-- The optional exact transport request and optional endpoint-retention floor. -/ transport : Option
    RootStateCheckpoint.TransportRequest := none
deriving Json.FromJson, Json.ToJson

constructive_injectivity Parent

set_option genInjectivity false in
/-- Serialized rational Bézout cofactors for a boundary-line clearance check.

The ordered left and right scalar encodings retain the original witness data.
Their numerical relation is checked before constructing a boundary witness. -/
structure WitnessData where
  /-- The exact coefficient list of the first Bézout cofactor. -/ left : List FractionData
  /-- The exact coefficient list of the second Bézout cofactor. -/ right : List FractionData
deriving Json.FromJson, Json.ToJson

constructive_injectivity WitnessData

set_option genInjectivity false in
/-- The four ordered pairs of proposed boundary-clearance cofactors.

The four directional witnesses retain their original boundary positions.
No pair of sides is identified or recomputed during serialization. -/
structure BoundaryData where
  /-- The proposed cofactor pair for the left boundary line. -/ left : WitnessData
  /-- The proposed cofactor pair for the right boundary line. -/ right : WitnessData
  /-- The proposed cofactor pair for the bottom boundary line. -/ bottom : WitnessData
  /-- The proposed cofactor pair for the top boundary line. -/ top : WitnessData
deriving Json.FromJson, Json.ToJson

constructive_injectivity BoundaryData

/-- Serialize both exact rational polynomial cofactors of a clearance witness. -/
@[expose] def witnessData (witness : SquareRoot.Replay.PreparedBoundaryReplay.Witness) : WitnessData :=
  ⟨witness.left.coeffs.map fractionData, witness.right.coeffs.map fractionData⟩

/-- Serialize the left, right, bottom and top clearance witnesses. -/
@[expose] def boundaryData (witnesses : SquareRoot.Replay.PreparedBoundaryReplay.Witnesses) : BoundaryData :=
  ⟨witnessData witnesses.left, witnessData witnesses.right,
    witnessData witnesses.bottom, witnessData witnesses.top⟩

/-- Decode both exact cofactor polynomials, rejecting invalid rational fields. -/
@[expose] def decodeWitness (raw : WitnessData) : IO Witness := do
  let left ← raw.left.mapM fun value => checked "left cofactor" (decodeFraction value)
  let right ← raw.right.mapM fun value => checked "right cofactor" (decodeFraction value)
  return ⟨⟨left⟩, ⟨right⟩⟩

/-- Decode all four boundary cofactor pairs in their retained side order. -/
@[expose] def decodeBoundary (raw : BoundaryData) : IO Witnesses := do
  return ⟨← decodeWitness raw.left, ← decodeWitness raw.right,
    ← decodeWitness raw.bottom, ← decodeWitness raw.top⟩

/-- Decode exactly four rational box coordinates and verify both interval orders. -/
@[expose] def decodeBox (raw : List FractionData) : IO Box := do
  let [xl, xu, yl, yu] ← raw.mapM fun value => checked "root box" (decodeFraction value)
    | throw (IO.userError "root box needs four coordinates")
  if x : xl ≤ xu then
    if y : yl ≤ yu then return ⟨xl, xu, yl, yu, x, y⟩
    else throw (IO.userError "inverted vertical root interval")
  else throw (IO.userError "inverted horizontal root interval")

/-- The quadratic Gaussian polynomial associated with the retained square-root parameter. -/
@[expose] def rootPolynomial (parameter : Data.Gaussian.Basic.Canonical) : Polynomial :=
  SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter

/-- No correctness is assumed of these cofactors. Nonconstant gcds or a majorant too large for the requested bound yield
retained failed checks. -/
@[expose] def propose (p q : Dense.Rational.Basic.CoordinatePolynomial) : Witness :=
  let result := Dense.GCD.extendedGCD p q
  let multiplier := result.gcd.leadingCoeff⁻¹
  ⟨scale multiplier result.left, Dense.Basic.DensePolynomial.scale multiplier result.right⟩

/-- Produce four untrusted Bézout cofactor pairs for the original box boundary lines. -/
@[expose] def proposeBoundary (polynomial : SquareRoot.Replay.PreparedBoundaryReplay.Polynomial) (box :
  Rational.Box) : Witnesses :=
  ⟨propose (Dense.Gaussian.Path.Components.pathReal polynomial (verticalBase box.xLower) verticalDirection)
      (Dense.Gaussian.Path.Components.pathImag polynomial (verticalBase box.xLower) verticalDirection),
    propose (Dense.Gaussian.Path.Components.pathReal polynomial (verticalBase box.xUpper) verticalDirection)
      (Dense.Gaussian.Path.Components.pathImag polynomial (verticalBase box.xUpper) verticalDirection),
    propose (Dense.Gaussian.Path.Components.pathReal polynomial (Imaginary.horizontalBase box.yLower)
      Constants.horizontalDirection)
      (Dense.Gaussian.Path.Components.pathImag polynomial (Imaginary.horizontalBase box.yLower)
        Constants.horizontalDirection),
    propose (Dense.Gaussian.Path.Components.pathReal polynomial (Imaginary.horizontalBase box.yUpper)
      Constants.horizontalDirection)
      (Dense.Gaussian.Path.Components.pathImag polynomial (Imaginary.horizontalBase box.yUpper)
        Constants.horizontalDirection)⟩

/-- Generate boundary cofactor proposals with periodic generation diagnostics. -/
@[noinline, expose] def generate (index : Nat) (polynomial : SquareRoot.Replay.PreparedBoundaryReplay.Polynomial) (box :
  Rational.Box) : Witnesses :=
  if index < 2 || index % 128 == 0 then
    dbg_trace s!"SAVED_BOUNDARY_GENERATED_{index}"
    proposeBoundary polynomial box
  else proposeBoundary polynomial box

/-- Evaluate a thunk through IO without inlining its computation boundary. -/
@[noinline, expose] def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

/-- Serializable operands of the typed failed check. Proofs are recovered by rechecking the saved witness; the JSON
report alone is not a certificate. -/
@[expose] def failureData (failure : SquareRoot.Replay.PreparedBoundaryReplay.Failure) : Json :=
  let details := match failure.reason with
    | .nonpositive _ _ _ bound _ =>
        [("kind", toJson "invalid requested bound"), ("bound", toJson (fractionData bound))]
    | .identity _ _ _ actual _ _ =>
        [("kind", toJson "invalid proposed Bezout witness; no line-invalidity conclusion"),
         ("actualIdentityPolynomial", toJson (actual.coeffs.map fractionData))]
    | .insufficient _ _ interval bound _ majorant _ product _ _ =>
        [("kind", toJson "inconclusive witness strength; saved bound unchanged"),
         ("interval", toJson ([interval.lower, interval.upper].map fractionData)),
         ("bound", toJson (fractionData bound)),
         ("majorant", toJson (fractionData majorant)),
         ("product", toJson (fractionData product)),
         ("requiredUpper", toJson (fractionData 1))]
  Json.mkObj (("side", toJson (reprStr failure.side)) :: details)

/-- Serialize invalid or insufficient boundary evidence while retaining the requested unchanged bound. -/
@[expose] def quadraticFailureData {parameter : Data.Gaussian.Basic.Canonical} {box : Rational.Box}
  {bound : Fraction.Rational}
    {witnesses : SquareRoot.Replay.PreparedBoundaryReplay.Witnesses} :
      SquareRoot.Replay.PreparedBoundaryReplay.QuadraticFailure parameter box bound witnesses → Json
  | .nonpositive _ => Json.mkObj
      [("kind", toJson "invalid requested bound"), ("bound", toJson (fractionData bound))]
  | .invalidWitness failure _ => failureData failure
  | .insufficient failure _ ceiling _ _ => Json.mkObj
      [("kind", toJson "inconclusive: both checked methods miss; saved bound unchanged"),
       ("bezout", failureData failure), ("quadraticCeiling", toJson (fractionData ceiling)),
       ("bound", toJson (fractionData bound))]

/-- Serialize the exact ambient side, requested bound and failed finite line-clearance evidence. -/
@[expose] def lineFailureData {axis : SquareRoot.Replay.PreparedRootStateReplay.Axis}
    {parameter : Data.Gaussian.Basic.Canonical} {ambient : Rational.Box} {coordinate bound :
      Fraction.Rational}
    {witness : SquareRoot.Replay.PreparedBoundaryReplay.Witness} (side : SquareRoot.Replay.PreparedBoundaryReplay.Side)
      :
    SquareRoot.Replay.PreparedRootStateReplay.LineFailure axis parameter ambient coordinate bound witness → Json
  | .nonpositive _ => Json.mkObj
      [("kind", toJson "invalid original ambient-line bound"),
       ("side", toJson (reprStr side)), ("bound", toJson (fractionData bound))]
  | .invalidWitness failure _ => failureData ⟨rootPolynomial parameter, ambient, bound, side, failure⟩
  | .insufficient failure _ ceiling _ _ => Json.mkObj
      [("kind", toJson "inconclusive original ambient-line bound"),
       ("side", toJson (reprStr side)), ("coordinate", toJson (fractionData coordinate)),
       ("bezout", failureData ⟨rootPolynomial parameter, ambient, bound, side, failure⟩),
       ("quadraticCeiling", toJson (fractionData ceiling)),
       ("bound", toJson (fractionData bound))]

/-- Serialize a failed complete-state check, including box geometry, ambient bounds or winding. -/
@[expose] def rootFailureData {parameter : Data.Gaussian.Basic.Canonical} {ambient : Rational.Box}
    {data : SquareRoot.Replay.PreparedRootStateReplay.Data} {witnesses :
      SquareRoot.Replay.PreparedBoundaryReplay.Witnesses} :
    SquareRoot.Replay.PreparedRootStateReplay.Failure parameter ambient data witnesses → Json
  | .notProper _ => Json.mkObj [("kind", toJson "nonproper saved root box"),
      ("box", toJson (RootStateCheckpoint.boxData data.box))]
  | .outsideAmbient _ => Json.mkObj [("kind", toJson "saved root box outside ambient"),
      ("box", toJson (RootStateCheckpoint.boxData data.box)),
      ("ambient", toJson (RootStateCheckpoint.boxData ambient))]
  | .boundary failure => quadraticFailureData failure
  | .left failure => lineFailureData .left failure
  | .right failure => lineFailureData .right failure
  | .bottom failure => lineFailureData .bottom failure
  | .top failure => lineFailureData .top failure
  | .winding actual _ _ => Json.mkObj [("kind", toJson "saved box does not have winding one"),
      ("actualQuadrupledWinding", toJson actual), ("expected", toJson (4 : Int))]

set_option genInjectivity false in
/-- A decoded original root-state payload with its ambient box and checked reconstruction. -/
structure RestoredRoot (parameter : Data.Gaussian.Basic.Canonical) where
  /-- The decoded original ambient box. -/ ambient : Rational.Box
  /-- The exact retained root-box and clearance payload. -/ data : SquareRoot.Replay.PreparedRootStateReplay.Data
  /-- The checked reconstruction of that payload for the original parameter and ambient box. -/ checked :
    SquareRoot.Replay.PreparedRootStateReplay.Checked parameter ambient data

constructive_injectivity RestoredRoot

/-- Shared checked source-state loader for state and transport replay. -/
@[expose] def restoreRootRecord (raw : Parent) (parameter : Data.Gaussian.Basic.Canonical) (box :
  Rational.Box)
    (bound : Fraction.Rational) (witnesses : SquareRoot.Replay.PreparedBoundaryReplay.Witnesses) :
    IO (Except Json (RestoredRoot parameter)) := do
  let saved := raw.rootState.getD ⟨raw.box, raw.clearance, none⟩
  match RootStateCheckpoint.decode saved with
  | .error failure => return .error failure.report
  | .ok data =>
    match RootStateCheckpoint.checkParent data box bound with
    | .error failure => return .error (Json.mkObj
        [("kind", toJson "nested state disagrees with original parent fields"),
         ("failure", toJson failure.message), ("retainedParent", toJson raw)])
    | .ok _ => pure ()
    match RootStateCheckpoint.decodeBox raw.ambient with
    | .error failure => return .error failure.report
    | .ok ambient =>
      let result ← evaluate fun _ => SquareRoot.Replay.PreparedRootStateReplay.check parameter ambient data witnesses
      match result with
      | .error failure => return .error (rootFailureData failure)
      | .ok restored => return .ok ⟨ambient, data, restored⟩

/-- The Bool is only this IO driver's internal counter; the shared loader constructs the evidence-bearing state, also
consumed by transport replay. -/
@[expose] def checkRootRecord (raw : Parent) (parameter : Data.Gaussian.Basic.Canonical) (box :
  Rational.Box)
    (bound : Fraction.Rational) (witnesses : SquareRoot.Replay.PreparedBoundaryReplay.Witnesses) : IO (Bool × Json) :=
      do
  match ← restoreRootRecord raw parameter box bound witnesses with
  | .error failure => return (false, failure)
  | .ok restored => return (true, Json.mkObj
      [("status", toJson "complete finite root state restored; owner recipe/history unresolved"),
       ("rootState", toJson (RootStateCheckpoint.capture restored.checked.state))])

/-- Serialize a failed or unresolved point transport with the original parameters and bound comparisons. -/
@[expose] def transportFailureData {parameter target : Data.Gaussian.Basic.Canonical} {ambient :
  Rational.Box}
    {state : SquareRoot.Replay.PreparedRootStateReplay.State parameter ambient} {reserve : Fraction.Rational} :
    SquareRoot.Replay.PreparedOwnerTransportReplay.Failure state target reserve → Json
  | .sourceZero _ => Json.mkObj [("kind", toJson "invalid zero source parameter")]
  | .targetZero _ => Json.mkObj [("kind", toJson "invalid zero target parameter")]
  | .stationary _ => Json.mkObj
      [("kind", toJson "inconclusive stationary move: original owner history required"),
       ("parameter", toJson (gaussianData parameter))]
  | .clearance field displacement _ _ => Json.mkObj
      [("kind", toJson "inconclusive fast transport: clearance comparison failed"),
       ("field", toJson (reprStr field)),
       ("displacement", toJson (fractionData displacement)),
       ("bound", toJson (fractionData (field.bound state)))]
  | .reserve displacement _ _ carried _ _ => Json.mkObj
      [("kind", toJson "inconclusive fast transport: reserve comparison failed"),
       ("displacement", toJson (fractionData displacement)),
       ("carried", toJson (fractionData carried)),
       ("reserve", toJson (fractionData reserve))]

/-- Serialize the two failed endpoint-retention bounds and their retained original and strengthened states. -/
@[expose] def retentionFailureData {parameter target : Data.Gaussian.Basic.Canonical} {ambient :
  Rational.Box}
    {state : SquareRoot.Replay.PreparedRootStateReplay.State parameter ambient} {reserve floor : Fraction.Rational}
    {transport : SquareRoot.Replay.PreparedOwnerTransportReplay.Checked state target reserve}
    (report : SquareRoot.Replay.PreparedRetainedTransportReplay.NeedsReset transport floor) : Json :=
  Json.mkObj
    [("kind", toJson "inconclusive endpoint retention: canonical moving reset required but not executed"),
     ("floor", toJson (fractionData floor)),
     ("originalBound", toJson (fractionData report.originalBound)),
     ("refreshedBound", toJson (fractionData report.refreshedBound)),
     ("transportedAmbient", toJson (RootStateCheckpoint.boxData transport.value.ambient)),
     ("transportedState", toJson (RootStateCheckpoint.capture transport.value.track.initial)),
     ("refreshedAmbient", toJson (RootStateCheckpoint.boxData report.refreshed.ambient)),
     ("refreshedState", toJson (RootStateCheckpoint.capture report.refreshed.track.initial))]

/-- Serialize failed legacy raw-state geometry, clearance or winding checks. -/
@[expose] def rawFailureData {parameter : Data.Gaussian.Basic.Canonical} {ambient : Rational.Box}
    {data : SquareRoot.Replay.PreparedRawStateReplay.Data} {witnesses :
      SquareRoot.Replay.PreparedBoundaryReplay.Witnesses} :
    SquareRoot.Replay.PreparedRawStateReplay.Failure parameter ambient data witnesses → Json
  | .notProper _ => Json.mkObj [("kind", toJson "nonproper legacy root box")]
  | .outsideAmbient _ => Json.mkObj [("kind", toJson "legacy root box outside original ambient")]
  | .boundary failure => quadraticFailureData failure
  | .line side failure _ => failureData ⟨rootPolynomial parameter, ambient, data.boundary, side, failure⟩
  | .winding actual _ _ => Json.mkObj
      [("kind", toJson "legacy box does not have winding one"),
       ("actualQuadrupledWinding", toJson actual), ("expected", toJson (4 : Int))]

/-- Legacy mode restores the raw state only. Its new ambient-line bounds are certified auxiliary data for operations
proved to ignore the old ones. -/
@[expose] def checkRawRecord (raw : Parent) (parameter : Data.Gaussian.Basic.Canonical) (box :
  Rational.Box)
    (bound : Fraction.Rational) (witnesses : SquareRoot.Replay.PreparedBoundaryReplay.Witnesses) : IO (Bool × Json) :=
      do
  if let some nested := raw.rootState then
    let nestedBox ← decodeBox nested.box
    let nestedBound ← checked "nested legacy boundary" (decodeFraction nested.clearance)
    discard <| checked "legacy parent consistency"
      (RootStateCheckpoint.checkBoxBoundary nestedBox nestedBound box bound)
  match RootStateCheckpoint.decodeBox raw.ambient with
  | .error failure => return (false, failure.report)
  | .ok ambient =>
    match ← evaluate fun _ => SquareRoot.Replay.PreparedRawStateReplay.check parameter ambient ⟨box, bound⟩ witnesses
      with
    | .error failure => return (false, rawFailureData failure)
    | .ok restored =>
      return (true, Json.mkObj
        [("status", toJson "raw state restored; auxiliary bounds are not the original ambient-line bounds"),
         ("box", toJson (RootStateCheckpoint.boxData restored.representative.box)),
         ("boundary", toJson (fractionData restored.representative.clearance.bound)),
         ("ambient", toJson (RootStateCheckpoint.boxData ambient)),
         ("auxiliaryRepresentative", toJson (RootStateCheckpoint.capture restored.representative)),
         ("unresolved", toJson (["original ambient-line bounds", "incoming refiner", "canonical source association"] :
           List String))])

/-- Calibrate against the original total constructor, with the accelerated source refiner rather than the loader's
deferred representative. Ordinary replay never invokes this generator or either source refinement function. -/
@[noinline, expose] def generateTransport {parameter target : Data.Gaussian.Basic.Canonical} {ambient :
  Rational.Box}
    (index : Nat) (state : SquareRoot.Replay.PreparedRootStateReplay.State parameter ambient)
    (sourceNonzero : parameter ≠ 0) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (parameter - target) < state.clearance.bound)
    (reserve : Fraction.Rational) : Topology.SquareRootContinuationChain.Owner target :=
  dbg_trace s!"SAVED_TRANSPORT_GENERATED_{index}"
  SquareRoot.Clearance.ExactQuadraticOwnerClearance.reservedTransport
    (Topology.SquareRootContinuationChain.Owner.ofState sourceNonzero state)
    targetNonzero small reserve

/-- Restore a checked nonstationary transport and its optional original endpoint-retention floor.

Keep point-transport and retained-endpoint caches distinct, compare complete payloads on reuse and retain unresolved
reset obligations without executing them. -/
@[expose] def checkTransportRecord (directory : System.FilePath) (raw : Parent)
    (parameter : Data.Gaussian.Basic.Canonical) (box : Rational.Box) (bound : Fraction.Rational)
      (witnesses : SquareRoot.Replay.PreparedBoundaryReplay.Witnesses)
    (compareOriginal : Bool) (prior : Option System.FilePath := none) : IO (Bool × Json) := do
  match ← restoreRootRecord raw parameter box bound witnesses with
  | .error failure => return (false, failure)
  | .ok restored =>
    let some request := raw.transport
      | return (false, Json.mkObj [("kind", toJson "incomplete checkpoint: transport request missing")])
    let target ← checked "transport target" (decodeGaussian request.target)
    let reserve ← checked "transport reserve" (decodeFraction request.reserve)
    let floor ← request.retentionFloor.mapM fun value => checked "endpoint retention floor" (decodeFraction value)
    match ← evaluate fun _ => SquareRoot.Replay.PreparedOwnerTransportReplay.check
        restored.checked.state target reserve with
    | .error failure => return (false, transportFailureData failure)
    | .ok result =>
      let retained : Except Json (Topology.SquareRootContinuationChain.Owner target × Json) ←
        evaluate fun _ => match floor with
        | none => .ok (result.value, Json.mkObj
            [("kind", toJson "retention floor absent; point transport only")])
        | some floor =>
            match SquareRoot.Replay.PreparedRetainedTransportReplay.retain result floor with
            | .error report => .error (retentionFailureData report)
            | .ok accepted => .ok (accepted.value, Json.mkObj
                [("branch", toJson (reprStr accepted.branch)),
                 ("bound", toJson (fractionData accepted.bound)),
                 ("floor", toJson (fractionData floor))])
      match retained with
      | .error failure => return (false, failure)
      | .ok (value, retention) =>
        let payload := RootStateCheckpoint.capture value.track.initial
        let targetRecord := Json.mkObj
          [("ambient", toJson (RootStateCheckpoint.boxData value.ambient)),
           ("rootState", toJson payload)]
        -- Never reinterpret an old point-transport cache as an endpoint after
        -- retention; preserve both compatible formats independently.
        let subdirectory := if floor.isSome then "advances" else "transports"
        IO.FS.createDirAll ((Purelib.System.FilePath.join directory (System.FilePath.mk (subdirectory))))
        let path := (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk
          (subdirectory))) (System.FilePath.mk (s!"{raw.parent}.json")))
        let readPath := if ← path.pathExists then path
          else Purelib.System.FilePath.join (prior.getD directory) (Purelib.System.FilePath.join subdirectory
            (System.FilePath.mk (s!"{raw.parent}.json")))
        let reused ← readPath.pathExists
        if reused then
          let previous : Json ← loadJson readPath
          unless previous == targetRecord do
            throw (IO.userError s!"parent {raw.parent}: saved transport differs from the checked result")
        unless ← path.pathExists do saveJson path targetRecord
        if compareOriginal then
          IO.FS.createDirAll ((Purelib.System.FilePath.join directory (System.FilePath.mk
            (s!"{subdirectory}-originals"))))
          let originalPath := (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk
            (s!"{subdirectory}-originals"))) (System.FilePath.mk (s!"{raw.parent}.json")))
          let originalRecord ← if ← originalPath.pathExists then loadJson originalPath else do
            let original ← evaluate fun _ => generateTransport raw.parent restored.checked.state
              result.sourceNonzero result.targetNonzero result.small reserve
            let original ← evaluate fun _ => match floor with
              | none => original
              | some floor => Branches.PreparedSheetContinuation.retainedAtReserve original floor
            let record := Json.mkObj
              [("ambient", toJson (RootStateCheckpoint.boxData original.ambient)),
               ("rootState", toJson (RootStateCheckpoint.capture original.track.initial))]
            saveJson originalPath record
            pure record
          unless originalRecord == targetRecord do
            throw (IO.userError "replay disagrees with the original transport from the accelerated source owner")
        return (true, Json.mkObj
          [("status", toJson (if floor.isSome then
              "nonstationary retained endpoint reconstructed; canonical source association unresolved"
            else "reserved transport only; endpoint retention floor absent; canonical source association unresolved")),
           ("retention", retention),
           ("displacement", toJson (fractionData result.displacement)),
           ("carried", toJson (fractionData result.carried)),
           ("targetCheckpointReused", toJson reused),
           ("reserve", toJson request.reserve), ("target", toJson request.target),
           ("result", targetRecord)])

/-- Process the ordered saved parent stream with checked reusable boundary witnesses.

Retain every attempted witness and report, distinguish complete, raw and transport restoration, and preserve completed
work across interruption. -/
@[expose] def loadParents (source directory : System.FilePath) (onlySaved crashAfterFirst : Bool)
    (prior : Option System.FilePath) (states : Bool)
    (transports compareOriginal rawStates : Bool := false) (maximum : Option Nat := none) : IO Unit := do
  let reports := if rawStates then "raw-reports" else if transports then "transport-reports" else if states then
    "state-reports" else "reports"
  IO.FS.createDirAll ((Purelib.System.FilePath.join directory (System.FilePath.mk ("witnesses"))))
  IO.FS.createDirAll ((Purelib.System.FilePath.join directory (System.FilePath.mk (reports))))
  if transports then IO.FS.createDirAll ((Purelib.System.FilePath.join directory (System.FilePath.mk ("transports"))))
  if compareOriginal then IO.FS.createDirAll ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("transport-originals"))))
  IO.FS.withFile source .read fun handle => do
    unless (Purelib.Data.String.trimAscii (← handle.getLine)) == "ccl-canonical-refinement-inputs-v1" do
      throw (IO.userError "expected canonical refinement inputs v1")
    let header : Header ← parseJson "header" (← handle.getLine)
    let count := min header.parentCount (maximum.getD header.parentCount)
    let mut reused := 0
    let mut restored := 0
    for index in [:count] do
      let raw : Parent ← parseJson s!"parent {index}" (← handle.getLine)
      unless raw.parent == index do throw (IO.userError "parent order does not match the snapshot")
      let parameter ← checked "root parameter" (decodeGaussian raw.parameter)
      let box ← decodeBox raw.box
      let bound ← checked "original boundary bound" (decodeFraction raw.clearance)
      let polynomial := rootPolynomial parameter
      let path := (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk
        ("witnesses"))) (System.FilePath.mk (s!"{index}.json")))
      let readPath := if ← path.pathExists then path
        else (Purelib.System.FilePath.join (Purelib.System.FilePath.join (prior.getD directory) (System.FilePath.mk
          ("witnesses"))) (System.FilePath.mk (s!"{index}.json")))
      let witnesses ← if ← readPath.pathExists then do
        let data : BoundaryData ← loadJson readPath
        let witnesses ← decodeBoundary data
        reused := reused + 1
        pure witnesses
      else do
        if onlySaved then throw (IO.userError s!"parent {index}: restart would invoke Euclidean generation")
        let witnesses ← evaluate fun _ => generate index polynomial box
        saveJson path (boundaryData witnesses)
        pure witnesses
      let (accepted, report) ← if rawStates then checkRawRecord raw parameter box bound witnesses
        else if transports then
          checkTransportRecord directory raw parameter box bound witnesses compareOriginal prior
        else if states then checkRootRecord raw parameter box bound witnesses else do
        let result ← evaluate fun _ => SquareRoot.Replay.PreparedBoundaryReplay.checkQuadratic parameter box bound
          witnesses
        match result with
        | .ok verified =>
          -- Consume the reconstructed certificate; its bound must remain exact.
          unless verified.result.clearance.bound == bound do throw (IO.userError "restored clearance bound changed")
          pure (true,
            (Json.mkObj [("status", toJson "boundary certificate restored; owner history unresolved"),
              ("method", toJson (reprStr verified.method)),
              ("bound", toJson (fractionData verified.result.clearance.bound))]))
        | .error failure => pure (false, quadraticFailureData failure)
      if accepted then restored := restored + 1
      -- Failed attempts are useful restart data, but never restored states.
      if readPath != path then saveJson path (boundaryData witnesses)
      saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk (reports)))
        (System.FilePath.mk (s!"{index}.json")))) report
      if crashAfterFirst && index == 0 then
        let pid ← IO.Process.getPID
        discard <| Purelib.System.IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
        throw (IO.userError "checkpoint-boundary SIGKILL failed")
      if (index + 1) % 128 == 0 then
        profile directory s!"{reports} {index + 1}/{header.parentCount}; restored={restored}; reused={reused}"
    if count == header.parentCount then
      unless (← handle.getLine).isEmpty do throw (IO.userError "unexpected extra parent records")
    let summary := if count < header.parentCount then "raw-prefix-summary.json"
      else if rawStates then "raw-summary.json" else if transports then "transport-summary.json"
      else if states then "state-summary.json" else "summary.json"
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (summary)))) (count, restored, reused)
    profile directory
      s!"CHECKED {reports}: processed={count}/{header.parentCount}; restored={restored}; \
        unresolved={count - restored}; reused={reused}; generated={count - reused}; owner recipe/history unresolved; \
        no period receipt"
    unless restored == count do
      throw (IO.userError "some requested restoration checks remain unresolved; exact failed attempts retained")

/-- Bind a saved-boundary replay store to its exact source bytes and requested restoration mode.

Check any prior store's import identity before creating the destination; retain distinct old and new provenance when
importing validated numerical artifacts. -/
@[expose] def run (source directory : System.FilePath) (onlySaved : Bool)
    (crashAfterFirst : Bool := false) (prior : Option System.FilePath := none)
    (states transports compareOriginal rawStates : Bool := false)
    (maximum : Option Nat := none) : IO Unit := do
  let hash ← Purelib.System.IO.Process.output { cmd := "sha256sum", args := #[source.toString] }
  unless hash.exitCode == 0 do throw (IO.userError "snapshot fingerprint failed")
  let digest := ((Purelib.Data.String.splitOn hash.stdout " ")).head!
  let identity := s!"saved original root boundary v1; source sha256={digest}; owner history unresolved"
  let origin ← match prior with
    | none => pure none
    | some previous => do
        let resolved ← IO.FS.realPath previous
        if ← directory.pathExists then
          if (← IO.FS.realPath directory) == resolved then
            throw (IO.userError "import source and destination must be distinct")
        let manifest : Manifest ← loadJson ((Purelib.System.FilePath.join previous (System.FilePath.mk
          ("manifest.json"))))
        match checkImportIdentity identity manifest with
        | .ok _ => pure ()
        | .error (.format actual _) => throw (IO.userError s!"import format rejected: {actual}")
        | .error (.identity actual expected _) =>
            throw (IO.userError s!"import source identity differs: {actual}; expected {expected}")
        pure (some (resolved.toString, manifest))
  openStore directory identity
  if let some (previous, manifest) := origin then
    let destination : Manifest ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("manifest.json"))))
    let record : ImportOrigin := ⟨previous, manifest, destination⟩
    let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("boundary-import.json")))
    if ← path.pathExists then
      let retained : ImportOrigin ← loadJson path
      unless retained == record do throw (IO.userError "destination already records a different import")
    else saveJson path record
  profile directory
    s!"BEGIN original \
      {if rawStates then "raw-state" else if transports then "transport" else if states then "root-state" else
      "boundary"} recovery; no branch preparation"
  loadParents source directory onlySaved crashAfterFirst prior states transports compareOriginal rawStates maximum

/-- This fixture exercises the numeric cursor codec, not canonical sample association or a complete period restart. It
calls no root sampler. -/
@[expose] def centerMetadata : Transport.PreparedCenterReplay.Metadata :=
  ⟨⟨2, 1⟩, ⟨-2, 2, -2, 2, by decide, by decide⟩,
    ⟨1 / 2, 3 / 2, 0, 1, by decide, by decide⟩,
    1, 1, 1 / 64, 1 / 16⟩

/-- Generate the finite center-metadata cursor used by the codec restart regression. -/
@[noinline, expose] def generateCenterCursor (_ : Unit) : CenterCheckpoint.RawCursor :=
  dbg_trace "CENTER_CURSOR_GENERATED"
  CenterCheckpoint.cursor centerMetadata

/-- Run one center-cursor save or replay phase and reject corrupted cursor, scalar and box data. -/
@[expose] def centerChild (directory : System.FilePath) (mode : String) : IO Unit := do
  IO.FS.createDirAll directory
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("cursor.json")))
  let raw ← if ← path.pathExists then
    loadJson path
  else do
    if mode == "resume" then throw (IO.userError "completed center cursor would be generated again")
    let raw ← evaluate generateCenterCursor
    saveJson path raw
    if mode == "crash" then
      let pid ← IO.Process.getPID
      discard <| Purelib.System.IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
      throw (IO.userError "checkpoint SIGKILL failed")
    pure raw
  match CenterCheckpoint.check raw with
  | .error _ => throw (IO.userError "center cursor rejected")
  | .ok checked =>
      unless toJson (CenterCheckpoint.encode checked.data) ==
          toJson (CenterCheckpoint.encode centerMetadata) do
        throw (IO.userError "cursor metadata differs from the retained fixture inputs")
      unless checked.index == raw.index do throw (IO.userError "saved cursor not retained")
      match CenterCheckpoint.check { raw with index := raw.index + 1 } with
      | .error (.index (.cursor saved expected _)) =>
          unless saved == raw.index + 1 && expected == raw.index do
            throw (IO.userError "cursor failure lost the mismatching operands")
      | _ => throw (IO.userError "modified cursor was accepted")
      match CenterCheckpoint.check { raw with metadata :=
          { raw.metadata with readingTarget := ⟨"1", "0"⟩ } } with
      | .error (.field (.denominator 0 _)) => pure ()
      | _ => throw (IO.userError "zero denominator was accepted")
      match CenterCheckpoint.check { raw with metadata :=
          { raw.metadata with rootBox := [] } } with
      | .error (.box (.arity _ _)) => pure ()
      | _ => throw (IO.userError "malformed root box was accepted")
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("checked.json")))) (Json.mkObj
        [("index", toJson checked.index),
         ("sampleIndex", toJson checked.data.sampleIndex),
         ("scope", toJson "numeric cursor only; canonical source/sample association not inferred")])
      Purelib.System.IO.println
        s!"center cursor: saved index {checked.index} checked; corrupt cursor/fraction/box rejected"

/-- Check atomic-save interruption, repeated cold reuse and generator-free center-cursor replay. -/
@[expose] def centerSelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "center self-test requires a fresh directory")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let run := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "15s", executable,
        "center-child", directory.toString, mode] }
  let marker := fun (result : IO.Process.Output) =>
    ((Purelib.Data.String.splitOn (result.stdout ++ result.stderr) "CENTER_CURSOR_GENERATED")).length > 1
  let interrupted ← run "crash"
  unless interrupted.exitCode != 0 && marker interrupted &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk ("cursor.json")))).pathExists) do
    throw (IO.userError "center cursor interruption did not leave its completed checkpoint")
  for _ in [:2] do
    let resumed ← run "resume"
    unless resumed.exitCode == 0 && !marker resumed do
      throw (IO.userError ("center cursor restart failed or regenerated\n" ++ resumed.stdout ++ resumed.stderr))
    IO.print resumed.stdout
  Purelib.System.IO.println "Center cursor codec: interrupted save, checked cold restart and repeat reuse passed."

/-- Check saved-boundary, complete/raw-state and endpoint-transport replay with exact finite fixtures.

Exercise retained invalidity and inconclusivity, atomic interruption recovery, source-preserving cross-build import and
rejection of corrupted witnesses or requests. -/
@[expose] def selfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "self-test requires a fresh directory")
  IO.FS.createDirAll directory
  let source := (Purelib.System.FilePath.join directory (System.FilePath.mk ("inputs.jsonl")))
  let interval : Data.Rat.Interval.Bounds := ⟨0, 1, by decide⟩
  let sharpWitness : Witness := ⟨constant 1, Dense.Basic.DensePolynomial.constant 1⟩
  match Clearance.Pair.Replay.check ⟨[1, 0]⟩ ⟨[-1, 1]⟩ interval (1 / 2) sharpWitness with
  | .ok verified =>
      unless 1 < (1 / 2 : Fraction.Rational) * Clearance.Pair.Bezout.bezoutSqMajorant verified.coprime interval do
        throw (IO.userError "sharp-bound fixture did not distinguish the old majorant")
  | .error _ => throw (IO.userError "exact attainable bound rejected by the sharper checker")
  unless Dense.Rational.Bounds.AffineHorner.coefficientSqBound ⟨[-2, 1]⟩ interval == 1 do
    throw (IO.userError "negative-slope endpoint bound regression")
  let farBox : Box := ⟨2, 3, 2, 3, by decide, by decide⟩
  let farWitness := proposeBoundary (rootPolynomial 1) farBox
  match SquareRoot.Replay.PreparedBoundaryReplay.checkQuadratic 1 farBox 2 farWitness with
  | .ok ⟨verified, .quadratic⟩ =>
      unless verified.clearance.bound == 2 do throw (IO.userError "quadratic supplement changed the requested bound")
  | _ => throw (IO.userError "quadratic component-gap supplement was not exercised")
  match SquareRoot.Replay.PreparedBoundaryReplay.checkQuadratic 1 farBox 10000 farWitness with
  | .error (.insufficient _ _ _ _ _) => pure ()
  | _ => throw (IO.userError "joint finite-method inconclusivity was not retained")
  match SquareRoot.Replay.PreparedBoundaryReplay.checkQuadratic 1 farBox 2 { farWitness with left := ⟨0, 0⟩ } with
  | .error (.invalidWitness _ _) => pure ()
  | _ => throw (IO.userError "quadratic supplement hid invalid supplied cofactors")
  match SquareRoot.Replay.PreparedBoundaryReplay.checkQuadratic 1 farBox 2 { farWitness with top := ⟨0, 0⟩ } with
  | .error (.invalidWitness _ _) => pure ()
  | _ => throw (IO.userError "an early weak bound hid invalid cofactors on a later side")
  let parameter : Gaussian := ⟨1, 1⟩
  let box : Box := ⟨1 / 2, 3 / 2, 1 / 4, 3 / 4, by decide, by decide⟩
  let bound : Coordinate := 1 / 1024
  let stateData : SquareRoot.Replay.PreparedRootStateReplay.Data :=
    ⟨box, bound, bound / 2, bound / 3, bound / 4, bound / 5⟩
  let stateWitnesses := proposeBoundary (rootPolynomial parameter) box
  let .ok fixture := SquareRoot.Replay.PreparedRootStateReplay.check parameter box stateData stateWitnesses
    | throw (IO.userError "complete-state fixture failed its finite checks")
  let .ok rawFixture := SquareRoot.Replay.PreparedRawStateReplay.check parameter box ⟨box, bound⟩ stateWitnesses
    | throw (IO.userError "legacy raw-state fixture failed its finite checks")
  unless toJson (RootStateCheckpoint.capture rawFixture.representative) !=
      toJson (RootStateCheckpoint.capture fixture.state) do
    throw (IO.userError "raw fixture must distinguish auxiliary bounds from the five original ones")
  have parameterNonzero : parameter ≠ 0 := by decide
  let originalOwner := Topology.SquareRootContinuationChain.Owner.ofState parameterNonzero fixture.state
  let representative := SquareRoot.Clearance.ExactQuadraticOwnerClearance.ownerOfState parameterNonzero
    rawFixture.representative
  let originalStrengthened := SquareRoot.Clearance.QuadraticCoefficientClearance.strengthen originalOwner
  let replayStrengthened := SquareRoot.Clearance.QuadraticCoefficientClearance.strengthen representative
  unless toJson (RootStateCheckpoint.capture originalStrengthened.track.initial) ==
      toJson (RootStateCheckpoint.capture replayStrengthened.track.initial) do
    throw (IO.userError "coefficient strengthening depended on omitted ambient bounds/refiner")
  let constantPolynomial : Polynomial := Dense.Basic.DensePolynomial.constant parameter
  let domain : Box := ⟨0, 1, -1, 1, by decide, by decide⟩
  let constantSegment : Geometry.ClearPath.ClearSegment constantPolynomial domain
      (Components.Basic.point 0 0) (Components.Basic.point 1 0) :=
    .horizontal 0 1 0 (by decide) (by decide) (by decide) (by decide)
      { bound := 1, positive := by decide, lower := by
          intro x _ _
          rw [show constantPolynomial = Dense.Basic.DensePolynomial.constant parameter from rfl,
            Dense.Basic.DensePolynomial.eval_constant]
          decide }
  have evaluation : constantPolynomial.eval (constantSegment.pointAt 0) = parameter :=
    Dense.Basic.DensePolynomial.eval_constant _ _
  let originalAt := evaluation.symm ▸ originalOwner
  let representativeAt := evaluation.symm ▸ representative
  -- Both successful and failed bounded diameter attempts must agree after
  -- replacing the source's refiner and all four ambient-line numbers.
  for diameter in ([1 / 4, 0] : List Fraction.Rational) do
    let originalReport := RootContinuation.CheckedSquareRootPreparation.attempt constantSegment 0 originalAt diameter
    let replayReport := RootContinuation.CheckedSquareRootPreparation.attempt constantSegment 0
      representativeAt diameter
    let originalAttempt := originalReport.value constantSegment 0 originalAt diameter
    let replayAttempt := replayReport.value constantSegment 0 representativeAt diameter
    unless originalReport.warmup.steps.length ≤ 2 && originalReport.search.steps.length ≤ 6 do
      throw (IO.userError "bounded preparation lost its retained finite work accounting")
    match originalAttempt, replayAttempt with
    | some first, some second =>
        unless 0 < diameter && toJson (RootStateCheckpoint.capture first.value.track.initial) ==
            toJson (RootStateCheckpoint.capture second.value.track.initial) do
          throw (IO.userError "diameter replay disagreed on its successful owner")
    | none, none =>
        unless diameter == 0 do throw (IO.userError "positive diameter fixture did not exercise success")
    | _, _ => throw (IO.userError "diameter replay changed success/failure")
  -- Exercise the exact serializer used by the real observation producer.
  let payload := RootStateCheckpoint.capture fixture.state
  let transportTarget : Gaussian := ⟨1 + 1 / 1024, 1⟩
  let transportRequest : RootStateCheckpoint.TransportRequest :=
    { target := gaussianData transportTarget, reserve := fractionData 0 }
  let legacyRequest : Except String RootStateCheckpoint.TransportRequest :=
    fromJson? (Json.mkObj
      [("target", toJson transportRequest.target), ("reserve", toJson transportRequest.reserve)])
  match legacyRequest with
  | .ok request =>
      unless request.retentionFloor.isNone do
        throw (IO.userError "legacy request decoder invented an endpoint retention floor")
  | .error message => throw (IO.userError s!"legacy transport request no longer decodes: {message}")
  let .ok moved := SquareRoot.Replay.PreparedOwnerTransportReplay.check fixture.state transportTarget 0
    | throw (IO.userError "retained endpoint fixture failed its transport check")
  let originalBound := moved.value.track.initial.clearance.bound
  let refreshed := SquareRoot.Clearance.QuadraticCoefficientClearance.strengthen moved.value
  let refreshedBound := refreshed.track.initial.clearance.bound
  unless originalBound < refreshedBound do
    throw (IO.userError
      s!"retention fixture needs a strict coefficient improvement: {originalBound.num}/{originalBound.den} versus \
        {refreshedBound.num}/{refreshedBound.den}")
  let refreshFloor := (originalBound + refreshedBound) / 2
  for (floor, branch) in
      [(0, SquareRoot.Replay.PreparedRetainedTransportReplay.Branch.inherited),
       (refreshFloor, .coefficientStrengthened)] do
    match SquareRoot.Replay.PreparedRetainedTransportReplay.retain moved floor with
    | .error _ => throw (IO.userError "retention fixture unexpectedly requires a moving reset")
    | .ok accepted =>
        unless accepted.branch == branch && floor ≤ accepted.bound do
          throw (IO.userError "retention did not preserve its selected branch and sufficient bound")
  let resetFloor := originalBound + refreshedBound + 1
  match SquareRoot.Replay.PreparedRetainedTransportReplay.retain moved resetFloor with
  | .ok _ => throw (IO.userError "oversized retention floor was accepted")
  | .error report =>
      unless report.originalBound == originalBound && report.refreshedBound == refreshedBound &&
          report.originalBound < resetFloor && report.refreshedBound < resetFloor do
        throw (IO.userError "reset-required report lost the actual two failed bounds")
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("reset-required.json"))))
        (retentionFailureData report)
  let parent := fun index : Nat => Parent.mk index (gaussianData parameter)
    (RootStateCheckpoint.boxData box) (fractionData bound)
    (RootStateCheckpoint.boxData box) (some payload)
    (some { transportRequest with retentionFloor := some (fractionData (if index == 0 then 0 else refreshFloor)) })
  match SquareRoot.Replay.PreparedOwnerTransportReplay.check fixture.state parameter 0 with
  | .error (.stationary _) => pure ()
  | _ => throw (IO.userError "stationary transport must retain the missing source-history boundary")
  match SquareRoot.Replay.PreparedOwnerTransportReplay.check fixture.state 0 0 with
  | .error (.targetZero _) => pure ()
  | _ => throw (IO.userError "zero transport target was not certified invalid")
  match SquareRoot.Replay.PreparedOwnerTransportReplay.check fixture.state 3 0 with
  | .error (.clearance .boundary _ _ _) => pure ()
  | _ => throw (IO.userError "large displacement did not retain the failed boundary comparison")
  match SquareRoot.Replay.PreparedOwnerTransportReplay.check fixture.state transportTarget 1 with
  | .error (.reserve _ _ _ carried _ _) =>
      unless carried < 1 do throw (IO.userError "wrong reserve failure operands")
  | _ => throw (IO.userError "failed reserve silently ran fallback transport")
  let thin : Coordinate := 1 / 16777216
  let sideCases : List (SquareRoot.Replay.PreparedOwnerTransportReplay.Field ×
      SquareRoot.Replay.PreparedRootStateReplay.Data) :=
    [(.left, { stateData with left := thin }), (.right, { stateData with right := thin }),
     (.bottom, { stateData with bottom := thin }), (.top, { stateData with top := thin })]
  for (expected, data) in sideCases do
    let .ok sourceState := SquareRoot.Replay.PreparedRootStateReplay.check parameter box data stateWitnesses
      | throw (IO.userError "thin ambient-line fixture failed")
    match SquareRoot.Replay.PreparedOwnerTransportReplay.check sourceState.state transportTarget 0 with
    | .error (.clearance actual displacement _ _) =>
        unless actual == expected && thin < displacement do
          throw (IO.userError "failed ambient-line check lost its side/operands")
    | _ => throw (IO.userError "failed ambient-line check silently ran fallback transport")
  match RootStateCheckpoint.decode { payload with ambientClearances := none } with
  | .error (.missingAmbientBounds _) => pure ()
  | _ => throw (IO.userError "legacy missing side bounds were guessed")
  match RootStateCheckpoint.decode { payload with ambientClearances := some [] } with
  | .error (.arity _ _ _) => pure ()
  | _ => throw (IO.userError "wrong side-bound count was accepted")
  let legacy ← checkRootRecord { parent 0 with rootState := none } parameter box bound stateWitnesses
  unless !legacy.1 do throw (IO.userError "legacy parent was mislabeled as a complete state")
  let inconsistent ← checkRootRecord
    { parent 0 with rootState := some { payload with clearance := fractionData (2 * bound) } }
    parameter box bound stateWitnesses
  unless !inconsistent.1 do throw (IO.userError "nested state disagrees with original parent bound")
  match SquareRoot.Replay.PreparedRootStateReplay.check parameter box { stateData with left := 0 } stateWitnesses with
  | .error (.left (.nonpositive _)) => pure ()
  | _ => throw (IO.userError "invalid saved left bound was not retained")
  match SquareRoot.Replay.PreparedRootStateReplay.check parameter box { stateData with top := 10000 } stateWitnesses
    with
  | .error (.top (.insufficient ..)) => pure ()
  | _ => throw (IO.userError "weak top-bound evidence was not retained as inconclusive")
  match SquareRoot.Replay.PreparedRootStateReplay.check parameter farBox stateData stateWitnesses with
  | .error (.outsideAmbient _) => pure ()
  | _ => throw (IO.userError "wrong ambient accepted")
  let flat : Box := ⟨1, 1, 1 / 4, 3 / 4, by decide, by decide⟩
  match SquareRoot.Replay.PreparedRootStateReplay.check parameter box { stateData with box := flat } stateWitnesses with
  | .error (.notProper _) => pure ()
  | _ => throw (IO.userError "nonproper box accepted")
  match SquareRoot.Replay.PreparedRootStateReplay.check 1 farBox
      ⟨farBox, bound, bound, bound, bound, bound⟩ farWitness with
  | .error (.winding actual _ _) =>
      unless actual == 0 do throw (IO.userError "wrong winding diagnostic")
  | _ => throw (IO.userError "root-free box was accepted or its winding check was not reached")
  atomicText source ("ccl-canonical-refinement-inputs-v1\n" ++ jsonText (Header.mk 2) ++ "\n" ++
    jsonText (parent 0) ++ "\n" ++ jsonText (parent 1) ++ "\n")
  let executable := (← IO.appPath).toString
  let invoke := fun (store mode : String) => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable,
        source.toString, ((Purelib.System.FilePath.join directory (System.FilePath.mk (store)))).toString, mode] }
  let fresh ← invoke "store" "generate"
  unless fresh.exitCode == 0 && ((Purelib.Data.String.splitOn (fresh.stdout ++ fresh.stderr)
    "SAVED_BOUNDARY_GENERATED_0")).length > 1 do
    throw (IO.userError ("fresh marker calibration failed\n" ++ fresh.stdout ++ fresh.stderr))
  let resumed ← invoke "store" "saved-only"
  unless resumed.exitCode == 0 && ((Purelib.Data.String.splitOn (resumed.stdout ++ resumed.stderr) "GENERATED_")).length
    == 1 do
    throw (IO.userError ("restart repeated generation\n" ++ resumed.stdout ++ resumed.stderr))
  let states ← invoke "store" "states-saved-only"
  unless states.exitCode == 0 && ((Purelib.Data.String.splitOn (states.stdout ++ states.stderr) "GENERATED_")).length ==
    1 do
    throw (IO.userError ("full state reload failed or generated witnesses\n" ++ states.stdout ++ states.stderr))
  let stateReport : Json ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join
    (Purelib.System.FilePath.join directory (System.FilePath.mk ("store"))) (System.FilePath.mk ("state-reports")))
    (System.FilePath.mk ("0.json"))))
  let savedFields ← match stateReport.getObjVal? "rootState" with
    | .ok value => pure value
    | .error failure => throw (IO.userError failure)
  unless savedFields == toJson payload do throw (IO.userError "restored original side bounds changed")
  let transports ← invoke "store" "transports-compare"
  let transportOutput := transports.stdout ++ transports.stderr
  unless transports.exitCode == 0 && ((Purelib.Data.String.splitOn transportOutput
    "SAVED_TRANSPORT_GENERATED_0")).length > 1 &&
      ((Purelib.Data.String.splitOn transportOutput "SAVED_TRANSPORT_GENERATED_1")).length > 1 &&
      ((Purelib.Data.String.splitOn transportOutput "SAVED_BOUNDARY_GENERATED_")).length == 1 do
    throw (IO.userError ("transport calibration failed or regenerated source witnesses\n" ++ transportOutput))
  let compareAgain ← invoke "store" "transports-compare"
  unless compareAgain.exitCode == 0 && ((Purelib.Data.String.splitOn (compareAgain.stdout ++ compareAgain.stderr)
    "GENERATED_")).length == 1 do
    throw (IO.userError "completed original transport comparison was generated again")
  let transported ← invoke "store" "transports-saved-only"
  unless transported.exitCode == 0 && ((Purelib.Data.String.splitOn (transported.stdout ++ transported.stderr)
    "GENERATED_")).length == 1 do
    throw (IO.userError "saved transport replay invoked a source or target generator")
  let transportReport : Json ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join
    (Purelib.System.FilePath.join directory (System.FilePath.mk ("store"))) (System.FilePath.mk ("transport-reports")))
    (System.FilePath.mk ("0.json"))))
  let .ok (.bool true) := transportReport.getObjVal? "targetCheckpointReused"
    | throw (IO.userError "transport replay did not reuse its completed target checkpoint")
  for index in [:2] do
    unless ← ((Purelib.System.FilePath.join (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
      (System.FilePath.mk ("store"))) (System.FilePath.mk ("advances"))) (System.FilePath.mk
      (s!"{index}.json")))).pathExists do
      throw (IO.userError "complete endpoint cache was not saved separately from point transport")
  let legacyTransport ← checkTransportRecord ((Purelib.System.FilePath.join directory (System.FilePath.mk ("store"))))
    { parent 0 with transport := some transportRequest } parameter box bound stateWitnesses false
  unless legacyTransport.1 && (← ((Purelib.System.FilePath.join (Purelib.System.FilePath.join
    (Purelib.System.FilePath.join directory (System.FilePath.mk ("store"))) (System.FilePath.mk ("transports")))
    (System.FilePath.mk ("0.json")))).pathExists) do
    throw (IO.userError "legacy point transport was not preserved alongside complete endpoint data")
  let crashedTransport ← invoke "store" "transports-crash"
  unless crashedTransport.exitCode == 137 do throw (IO.userError "transport interruption did not receive SIGKILL")
  let transportAgain ← invoke "store" "transports-saved-only"
  unless transportAgain.exitCode == 0 && ((Purelib.Data.String.splitOn (transportAgain.stdout ++ transportAgain.stderr)
    "GENERATED_")).length == 1 do
    throw (IO.userError "transport restart regenerated completed work")
  let missingRequest ← checkTransportRecord directory { parent 0 with transport := none }
    parameter box bound stateWitnesses false
  unless !missingRequest.1 do throw (IO.userError "missing transport request was guessed")
  let legacyRaw ← checkRawRecord { parent 0 with rootState := none } parameter box bound stateWitnesses
  unless legacyRaw.1 do throw (IO.userError "legacy raw-state check required omitted ambient bounds")
  let rawSource := (Purelib.System.FilePath.join directory (System.FilePath.mk ("legacy-raw-inputs.jsonl")))
  atomicText rawSource ("ccl-canonical-refinement-inputs-v1\n" ++ jsonText (Header.mk 2) ++ "\n" ++
    jsonText { parent 0 with rootState := none, transport := none } ++ "\n" ++
    jsonText { parent 1 with rootState := none, transport := none } ++ "\n")
  let invokeRaw := fun (mode : String) => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable,
        rawSource.toString, ((Purelib.System.FilePath.join directory (System.FilePath.mk ("legacy-raw")))).toString,
          mode] }
  let generatedRaw ← invokeRaw "generate"
  unless generatedRaw.exitCode == 0 do throw (IO.userError "legacy fixture witnesses failed")
  let restoredRaw ← invokeRaw "raw-saved-only"
  unless restoredRaw.exitCode == 0 && ((Purelib.Data.String.splitOn (restoredRaw.stdout ++ restoredRaw.stderr)
    "GENERATED_")).length == 1 do
    throw (IO.userError ("legacy raw-state restoration regenerated witnesses\n" ++ restoredRaw.stdout ++
      restoredRaw.stderr))
  let crashedRaw ← invokeRaw "raw-crash"
  unless crashedRaw.exitCode == 137 do throw (IO.userError "raw-state interruption did not receive SIGKILL")
  let restartedRaw ← invokeRaw "raw-saved-only"
  unless restartedRaw.exitCode == 0 && ((Purelib.Data.String.splitOn (restartedRaw.stdout ++ restartedRaw.stderr)
    "GENERATED_")).length == 1 do
    throw (IO.userError "legacy raw-state restart regenerated completed witnesses")
  let rawManifest : Manifest ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("legacy-raw"))) (System.FilePath.mk ("manifest.json"))))
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk ("legacy-raw")))
    (System.FilePath.mk ("manifest.json")))) { rawManifest with binarySha256 := "simulated-old-raw-binary" }
  let importedRaw ← Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable, "import-raw",
        rawSource.toString, ((Purelib.System.FilePath.join directory (System.FilePath.mk ("legacy-raw")))).toString,
          ((Purelib.System.FilePath.join directory (System.FilePath.mk ("imported-raw")))).toString] }
  unless importedRaw.exitCode == 0 && ((Purelib.Data.String.splitOn (importedRaw.stdout ++ importedRaw.stderr)
    "GENERATED_")).length == 1 do
    throw (IO.userError ("legacy raw-state cross-build import failed\n" ++ importedRaw.stdout ++ importedRaw.stderr))
  let crashedState ← invoke "store" "states-crash"
  unless crashedState.exitCode == 137 do throw (IO.userError "state-check interruption did not receive SIGKILL")
  let statesAgain ← invoke "store" "states-saved-only"
  unless statesAgain.exitCode == 0 && ((Purelib.Data.String.splitOn (statesAgain.stdout ++ statesAgain.stderr)
    "GENERATED_")).length == 1 do
    throw (IO.userError "interrupted full-state check repeated generation")
  let crashed ← invoke "partial" "crash"
  unless crashed.exitCode == 137 do throw (IO.userError "partial fixture did not receive SIGKILL")
  unless ← ((Purelib.System.FilePath.join (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("partial"))) (System.FilePath.mk ("witnesses"))) (System.FilePath.mk ("0.json")))).pathExists
    do
    throw (IO.userError "interruption lost its completed witness")
  let resumedPartial ← invoke "partial" "generate"
  let output := resumedPartial.stdout ++ resumedPartial.stderr
  unless resumedPartial.exitCode == 0 && ((Purelib.Data.String.splitOn output "SAVED_BOUNDARY_GENERATED_0")).length == 1
    &&
      ((Purelib.Data.String.splitOn output "SAVED_BOUNDARY_GENERATED_1")).length > 1 do
    throw (IO.userError ("partial restart failed to skip its completed prefix\n" ++ output))
  let raw : BoundaryData ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join
    (Purelib.System.FilePath.join directory (System.FilePath.mk ("store"))) (System.FilePath.mk ("witnesses")))
    (System.FilePath.mk ("0.json"))))
  let witnesses ← decodeBoundary raw
  match SquareRoot.Replay.PreparedBoundaryReplay.check (rootPolynomial parameter) box 0 witnesses with
  | .error ⟨_, _, _, _, .nonpositive _ _ _ _ _⟩ => pure ()
  | _ => throw (IO.userError "nonpositive requested bound was not certified invalid")
  match SquareRoot.Replay.PreparedBoundaryReplay.check (rootPolynomial parameter) box bound { witnesses with left := ⟨0,
    0⟩ } with
  | .error ⟨_, _, _, .left, .identity _ _ _ _ _ _⟩ => pure ()
  | _ => throw (IO.userError "wrong cofactors were not certified invalid")
  match SquareRoot.Replay.PreparedBoundaryReplay.check (rootPolynomial parameter) box 2 witnesses with
  | .error ⟨_, _, _, _, .insufficient _ _ _ _ _ _ _ _ _ _⟩ => pure ()
  | _ => throw (IO.userError "insufficient witness was not reported with its operands")
  let original : Manifest ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("store"))) (System.FilePath.mk ("manifest.json"))))
  let old : Manifest := { original with binarySha256 := "simulated-old-boundary-binary" }
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk ("store")))
    (System.FilePath.mk ("manifest.json")))) old
  let rejected ← invoke "store" "saved-only"
  unless rejected.exitCode != 0 do throw (IO.userError "ordinary resume silently accepted a changed binary")
  let importRun := fun (mode target : String) => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable, mode,
        source.toString, ((Purelib.System.FilePath.join directory (System.FilePath.mk ("store")))).toString,
          ((Purelib.System.FilePath.join directory (System.FilePath.mk (target)))).toString] }
  let interrupted ← importRun "import-crash" "imported"
  unless interrupted.exitCode == 137 do throw (IO.userError "import fixture did not receive SIGKILL")
  let imported ← importRun "import-saved" "imported"
  unless imported.exitCode == 0 && ((Purelib.Data.String.splitOn (imported.stdout ++ imported.stderr)
    "GENERATED_")).length == 1 do
    throw (IO.userError ("checked cross-build import failed\n" ++ imported.stdout ++ imported.stderr))
  let importedStates ← importRun "import-states" "imported-states"
  unless importedStates.exitCode == 0 && ((Purelib.Data.String.splitOn (importedStates.stdout ++ importedStates.stderr)
    "GENERATED_")).length == 1 do
    throw (IO.userError ("complete-state cross-build import failed\n" ++ importedStates.stdout ++
      importedStates.stderr))
  let importedTransports ← importRun "import-transports" "imported-transports"
  unless importedTransports.exitCode == 0 && ((Purelib.Data.String.splitOn (importedTransports.stdout ++
    importedTransports.stderr) "GENERATED_")).length == 1 do
    throw (IO.userError ("transport cross-build import failed\n" ++ importedTransports.stdout ++
      importedTransports.stderr))
  let importedTransportReport : Json ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join
    (Purelib.System.FilePath.join directory (System.FilePath.mk ("imported-transports"))) (System.FilePath.mk
    ("transport-reports"))) (System.FilePath.mk ("0.json"))))
  let .ok (.bool true) := importedTransportReport.getObjVal? "targetCheckpointReused"
    | throw (IO.userError "cross-build transport import ignored the original completed checkpoint")
  let originalTransport : Json ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join
    (Purelib.System.FilePath.join directory (System.FilePath.mk ("store"))) (System.FilePath.mk ("advances")))
    (System.FilePath.mk ("0.json"))))
  let changedTransport := Json.mkObj [("wrong", toJson true)]
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("store"))) (System.FilePath.mk ("advances"))) (System.FilePath.mk ("0.json"))))
    changedTransport
  let badTransport ← importRun "import-transports" "bad-transport"
  unless badTransport.exitCode != 0 && ((Purelib.Data.String.splitOn (badTransport.stdout ++ badTransport.stderr)
    "GENERATED_")).length == 1 do
    throw (IO.userError "modified transport checkpoint was accepted or regenerated")
  let preservedBadTransport : Json ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join
    (Purelib.System.FilePath.join directory (System.FilePath.mk ("store"))) (System.FilePath.mk ("advances")))
    (System.FilePath.mk ("0.json"))))
  unless preservedBadTransport == changedTransport do throw (IO.userError
    "failed import overwrote its source checkpoint")
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("store"))) (System.FilePath.mk ("advances"))) (System.FilePath.mk ("0.json"))))
    originalTransport
  let preserved : Manifest ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("store"))) (System.FilePath.mk ("manifest.json"))))
  unless preserved == old do throw (IO.userError "import changed original provenance")
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk ("store")))
    (System.FilePath.mk ("manifest.json")))) { old with sourceIdentity := "different source" }
  let wrong ← importRun "import-saved" "wrong-source"
  if wrong.exitCode == 0 || (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("wrong-source")))).pathExists) then
    throw (IO.userError "wrong source was not rejected before destination creation")
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk ("store")))
    (System.FilePath.mk ("manifest.json")))) old
  let bad : BoundaryData := { raw with left := ⟨[], []⟩ }
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("partial"))) (System.FilePath.mk ("witnesses"))) (System.FilePath.mk ("1.json")))) bad
  let malformed ← invoke "partial" "saved-only"
  unless malformed.exitCode != 0 do throw (IO.userError "modified saved witness was accepted")
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("store"))) (System.FilePath.mk ("witnesses"))) (System.FilePath.mk ("1.json")))) bad
  let failedImport ← importRun "import-saved" "failed-attempt"
  unless failedImport.exitCode != 0 &&
      ((Purelib.Data.String.splitOn (failedImport.stdout ++ failedImport.stderr) "GENERATED_")).length == 1 do
    throw (IO.userError "failed-attempt import falsely accepted or regenerated its witness")
  unless ← ((Purelib.System.FilePath.join (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("failed-attempt"))) (System.FilePath.mk ("witnesses"))) (System.FilePath.mk
    ("1.json")))).pathExists do
    throw (IO.userError "checked failed-attempt import lost its diagnostic witness")
  unless ← ((Purelib.System.FilePath.join (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("failed-attempt"))) (System.FilePath.mk ("reports"))) (System.FilePath.mk
    ("1.json")))).pathExists do
    throw (IO.userError "checked failed-attempt import lost its failure operands")
  Purelib.System.IO.println
    "Saved boundary, full/raw root states and retained nonstationary endpoints: inherited/strengthened retention and \
      reset-required certificates, legacy point-transport separation, original constructor agreement, no-generator \
      restart/import, interrupted reuse and malformed-checkpoint rejection passed."

end SavedBoundaryHarness

/-- Dispatch saved-boundary generation, checked restoration, explicit import or finite restart regressions. -/
@[expose] def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["center-self-test", directory] => SavedBoundaryHarness.centerSelfTest directory
  | ["center-child", directory, mode] => SavedBoundaryHarness.centerChild directory mode
  | ["self-test", directory] => SavedBoundaryHarness.selfTest directory
  | ["import-saved", source, previous, directory] =>
      SavedBoundaryHarness.run source directory true false (some previous)
  | ["import-crash", source, previous, directory] =>
      SavedBoundaryHarness.run source directory true true (some previous)
  | ["import-states", source, previous, directory] =>
      SavedBoundaryHarness.run source directory true false (some previous) true
  | ["import-transports", source, previous, directory] =>
      SavedBoundaryHarness.run source directory true false (some previous) true true
  | ["import-raw", source, previous, directory] =>
      SavedBoundaryHarness.run source directory true false (some previous) false false false true
  | ["import-raw-prefix", source, previous, directory, count] =>
      let some count := (Purelib.Data.String.toNat? count) | throw (IO.userError
        "prefix count must be a natural number")
      SavedBoundaryHarness.run source directory true false (some previous) false false false true (some count)
  | [source, directory, mode] =>
      unless ["generate", "saved-only", "crash", "states-saved-only", "states-crash",
          "transports-saved-only", "transports-crash", "transports-compare", "raw-saved-only", "raw-crash"].contains
            mode do
        throw (IO.userError "use generate, saved-only, states-saved-only, raw-saved-only or transports-saved-only")
      let transports := mode == "transports-saved-only" || mode == "transports-crash" || mode == "transports-compare"
      let states := mode == "states-saved-only" || mode == "states-crash" || transports
      let rawStates := mode == "raw-saved-only" || mode == "raw-crash"
      SavedBoundaryHarness.run source directory (mode == "saved-only" || states || rawStates)
        (mode == "crash" || mode == "states-crash" || mode == "transports-crash" || mode == "raw-crash") none states
          transports
        (mode == "transports-compare") rawStates
  | _ => throw (IO.userError
    "usage: saved_boundary_harness self-test FRESH_DIRECTORY | INPUTS_JSONL STORE generate|saved-only|\
      states-saved-only|raw-saved-only|transports-saved-only | import-saved|import-states|import-raw|import-transports \
      INPUTS_JSONL OLD_STORE NEW_STORE")

end
