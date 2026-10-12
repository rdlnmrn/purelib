module

import Purelib.Data.Int.Decimal

import Purelib.Data.Range

import Purelib.Data.List.Control

import Purelib.System.FilePath

import Purelib.System.IO

import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.Json.Printer
import Purelib.Data.String.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.Readings.BoundedPreparedSource
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import scripts.checkpoint.InitialExtraction
import scripts.checkpoint.RootRefinement
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.SquareRoot.Newton.Search
import Purelib.Integration.Path.Dyadic.DyadicRequestCursor

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Grid.RootEdges
import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive
import Purelib.RootIsolation.SquareRoot.Preparation.Terminal
import Purelib.RootIsolation.SquareRoot.Replay.BoundedMovingReplay
import Purelib.RootIsolation.SquareRoot.Replay.BoundedPreparedSourceReplay
import Purelib.RootIsolation.SquareRoot.Replay.MovingRecenterReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedRawStateReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay
import Purelib.Riemann.Transport.PreparedEdgeReplay
import Purelib.Riemann.Paths.PreparedPathTrace
import scripts.checkpoint.Integration
import scripts.checkpoint.RootState
import scripts.checkpoint.DiameterPreparation
public import scripts.checkpoint.PreparedBank
public import Purelib.Riemann.RootContinuation.RootReturnBox
public import scripts.checkpoint.SquareRootFamily
import Purelib.Tactic.Ring
import Init.Data.Int.Basic
import Init.Data.List.Basic
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.BoundedPreparedBanks
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Transport.BoundedPreparedBankReplay
import Purelib.RootIsolation.SquareRoot.Newton.Replay.Trace
import Purelib.RootIsolation.SquareRoot.Replay.CheckedDiameterReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedBoundaryReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedRawSourceReplay
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

-- Use complete constructor eliminators for the original match arms.
set_option backward.match.sparseCases false

open Purelib.Data (Json)
open scoped Purelib.Data.String Purelib.Data.List Purelib.Data.Range
open Purelib.Data.Json (toJson)

public section

/-!
Short checked prepared-source replay regression.  It reconstructs a recorded
choice in a separate process and calibrates a marker on the canonical search.
This exercises the prepared-source boundary only: neither a complete cycle
checkpoint nor the required normalized-period observation is claimed.
The terminal regression compares complete safe-depth acquisition spines and
cached endpoint owners. The preferred-depth regression also exercises the checked uniform-source fallback.
Run under an explicit SIGKILL timeout and systemd memory bound.
-/

open Purelib.Riemann.Transport Purelib.Riemann.RootContinuation Purelib.Riemann.Integration
open Purelib.Riemann.Branches Purelib.Riemann.Readings Purelib.Riemann.Paths Purelib.Riemann.Topology

namespace PreparedSourceReplayHarnessTrace
/-- Emit the retained native diagnostic marker before evaluating the supplied continuation. -/
@[expose, never_extract, extern "lean_dbg_trace"] def trace {α : Type u}
    (message : String) (work : Unit → α) : α := work ()

/-- The diagnostic marker retains the exact value of its continuation. -/
theorem trace_eq {α : Type u} (message : String) (work : Unit → α) :
    trace message work = work () := rfl
end PreparedSourceReplayHarnessTrace

macro_rules
  | `(dbg_trace $arg:interpolatedStr; $body) =>
      `(PreparedSourceReplayHarnessTrace.trace (s! $arg) fun _ => $body)

namespace MovingResetCheckpointTests

open Purelib.Riemann IntegrationCheckpoint
open Purelib.Riemann.Branches.PreparedSheetContinuation

/-- The asymmetric rational root box used to exercise successful finite moving resets. -/
@[expose] def fixture : Box := ⟨1 / 4, 3 / 2, -1 / 2, 3 / 4, by decide, by decide⟩

open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Check a proper box's four axis determinants and winding before constructing the exact root owner of one. -/
@[expose] def sourceAtBox (box : Box) (proper : box.Proper) :
    IO (Owner (1 : Gaussian)) := do
  let parameter : Gaussian := 1
  have nonzero : parameter ≠ 0 := by decide
  if left : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter box.xLower ≠ 0 then
    if right : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter box.xUpper ≠ 0 then
      if bottom : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter box.yLower ≠ 0 then
        if top : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter box.yUpper ≠ 0 then
          if winding : Winding.Box.Basic.quadrupledBoxWinding
              (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter) box = 4 then
            return SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOfBox parameter nonzero
              box proper left right bottom top winding
          else throw (IO.userError "fixture winding rejected")
        else throw (IO.userError "fixture top determinant rejected")
      else throw (IO.userError "fixture bottom determinant rejected")
    else throw (IO.userError "fixture right determinant rejected")
  else throw (IO.userError "fixture left determinant rejected")

section
open Purelib.RootIsolation
/-- Evaluate the original finite moving reset with a calibrated generation marker. -/
@[expose, noinline] def canonical {parameter : Gaussian} (owner : PreparedSheetContinuation.Owner parameter) :=
  dbg_trace "CANONICAL_MOVING_RESET_FORCED"
  SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner

/-- Serialize the original reset availability, complete retained owner and bridge state. -/
@[expose] def snapshot {parameter : Gaussian} {source : PreparedSheetContinuation.Owner parameter} :
    Option (SquareRoot.Clearance.ExactQuadraticOwnerClearance.MovingRecenter parameter source) → Json
  | none => Json.mkObj [("kind", toJson "original finite reset unavailable")]
  | some reset => Json.mkObj
      [("kind", toJson "original reset restored"),
       ("owner", InitialExtractionCheckpoint.stateData reset.owner.track.initial),
       ("bridge", InitialExtractionCheckpoint.stateData reset.bridgeOwner.track.initial),
       ("ambient", toJson (RootStateCheckpoint.boxData reset.owner.ambient))]

/-- Calibrate or replay the original moving reset using checked shared winding checkpoints.

Verify exact owner and bridge readbacks, atomic interruption and reuse at another depth. -/
@[expose] def run (directory : System.FilePath) (mode : String) : IO Unit := do
  let owner ← sourceAtBox fixture ⟨by decide, by decide⟩
  IO.FS.createDirAll directory
  if mode == "calibrate" then
    let result := canonical owner
    match result with
    | none => throw (IO.userError "fixture must exercise a successful original reset")
    | some _ => saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical.json")))) (snapshot
      result)
  else
    let control : WindingCheckpoint.Control :=
      { savedOnly := mode == "replay" || mode == "shared" || mode == "corrupt"
        afterSave := if mode == "crash" then do
          (← IO.getStdout).flush
          let pid ← IO.Process.getPID
          discard <| Purelib.System.IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
          throw (IO.userError "reset regression kill unexpectedly returned")
        else pure () }
    let occurrence := if mode == "shared" then (Purelib.System.FilePath.join directory (System.FilePath.mk
      ("another-depth"))) else (Purelib.System.FilePath.join directory (System.FilePath.mk ("first-depth")))
    let restored ← MovingResetCheckpoint.runPlan control ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("pool")))) occurrence
      (SquareRoot.Replay.MovingRecenterReplay.moving owner)
    let expected : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical.json"))))
    unless snapshot restored.val == expected do
      throw (IO.userError "restored reset changed original owner or bridge state")
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"result-{mode}.json")))) (snapshot
      restored.val)
    Purelib.System.IO.println "Original moving reset and full bridge restored."

end

namespace Bounded

open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Data.Gaussian.Components.Basic (point)

open Purelib.Data.Rat in
/-- The unit rational slope of the bounded-reset affine fixture. -/
@[expose] def slope : Fraction.Rational := 1

/-- The unit-slope affine Gaussian polynomial of the bounded-reset fixture. -/
@[expose] def polynomial : GaussianPolynomial := ⟨[⟨slope, 0⟩, 1]⟩

open Purelib.Polynomial in
/-- The bounded-reset polynomial evaluates to its explicit affine formula. -/
theorem polynomial_eval (value : Gaussian) :
    polynomial.eval value = (⟨slope, 0⟩ : Gaussian) * value + 1 := by
  simp only [-eq_self, -iff_self, polynomial, Dense.Basic.DensePolynomial.eval,
    Dense.Basic.DensePolynomial.evalCoeffs, List.foldl_cons,
    List.foldl_nil, zero_mul, zero_add]
  rfl

/-- The bounded-reset polynomial is nonzero at the initial point. -/
theorem initial_nonzero : polynomial.eval (point 0 0) ≠ 0 := by
  rw [polynomial_eval]
  change (⟨slope, 0⟩ : Gaussian) * 0 + 1 ≠ 0
  rw [mul_zero, zero_add]
  decide

/-- The rational rectangle containing the fixture's unit real segment. -/
@[expose] def ambient : Box where
  xLower := 0
  xUpper := 1
  yLower := -1
  yUpper := 1
  x_valid := by decide
  y_valid := by decide

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- A unit squared-norm lower bound for the affine polynomial on the retained real interval. -/
@[expose] def clearance : Clearance.Box.Line.Basic.HorizontalLineClearance polynomial ambient 0 where
  bound := 1
  positive := by decide
  lower := by
    intro x lower _upper
    rw [polynomial_eval]
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    simp only [Data.Gaussian.Norm.Basic.normSq,
      Data.Gaussian.Basic.Canonical.add_re, Data.Gaussian.Basic.Canonical.add_im,
      Data.Gaussian.Basic.Canonical.mul_re, Data.Gaussian.Basic.Canonical.mul_im,
      Data.Gaussian.Basic.Canonical.one_re, Data.Gaussian.Basic.Canonical.one_im,
      Components.Basic.point]
    have zeroNeg : -(0 : Fraction.Rational) = 0 := rfl
    simp only [-eq_self, -iff_self, zero_mul, mul_zero,
      Fraction.Arithmetic.sub_eq_add_neg_direct, zeroNeg, add_zero, zero_pow (by decide : 2 ≠ 0)]
    have nonnegative : (0 : Fraction.Rational) ≤ slope * x :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) lower
    have bound : (1 : Fraction.Rational) ≤ slope * x + 1 := by
      simpa only [zero_add] using Fraction.Order.Arithmetic.add_le_add_right_direct nonnegative 1
    simpa only [one_pow] using Fraction.Order.Arithmetic.pow_le_pow_direct (by decide : (0 : Fraction.Rational) ≤ 1)
      bound 2

open Purelib.Polynomial in
/-- The certified clear unit horizontal segment of the bounded-reset fixture. -/
@[expose] def segment : Geometry.ClearPath.ClearSegment polynomial ambient (point 0 0) (point 1 0) :=
  .horizontal 0 1 0 (by decide) (by decide) (by decide) (by decide) clearance

/-- The initial endpoint at parameter zero. -/
@[expose] def current : Endpoint := ⟨0, by decide⟩

open Purelib.RootIsolation in
/-- Serialize the original bounded miss or accepted retained preparation. -/
@[expose] def outcomeSnapshot (request : StepRequest) (owner : Owner (polynomial.eval (segment.pointAt
  current.parameter)))
    (value : SquareRoot.Replay.BoundedPreparedSourceReplay.Outcome segment current owner request) : Json :=
  match value with
  | .error failure => Json.mkObj
      [("kind", toJson "certified original bounded miss"),
       ("movement", toJson (fractionData failure.variation))]
  | .ok accepted => Json.mkObj
      [("kind", toJson "original bounded success"),
       ("prepared", InitialExtractionCheckpoint.stateData accepted.cached.preparedOwner.track.initial)]

/-- Run the original bounded source check with a calibrated generation marker. -/
@[expose, noinline] def canonicalCheck (request : StepRequest)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :=
  dbg_trace "CANONICAL_BOUNDED_RESET_FORCED"
  BoundedPreparedSource.check segment current owner request

open Purelib.Data.Rat in
open Purelib.RootIsolation in
/-- Compare thirteen dyadic bounded source requests against their original outcomes.

Require actual moving resets, accepted preparations and certified misses, and verify saved-only winding reuse. -/
@[expose] def run (directory : System.FilePath) (mode : String) : IO Unit := do
  let originalOwner ← sourceAtBox fixture ⟨by decide, by decide⟩
  have parameterEq : (1 : Gaussian) = polynomial.eval (segment.pointAt current.parameter) := by decide
  let owner : Owner (polynomial.eval (segment.pointAt current.parameter)) := parameterEq ▸ originalOwner
  let control : WindingCheckpoint.Control := ⟨mode == "bounded-replay", pure ()⟩
  let mut movingCount := 0
  let mut acceptedCount := 0
  let mut missedCount := 0
  for depth in List.range 13 do
    let right : Fraction.Rational := 1 / Fraction.Cast.fromInt (2 ^ depth)
    if inside : (0 : Fraction.Rational) ≤ right ∧ right ≤ 1 then
      let request : StepRequest := ⟨⟨right, inside⟩, 4, by decide⟩
      let stepDirectory := (Purelib.System.FilePath.join directory (System.FilePath.mk (s!"bounded-{depth}")))
      IO.FS.createDirAll stepDirectory
      if mode == "bounded-calibrate" then
        saveJson ((Purelib.System.FilePath.join stepDirectory (System.FilePath.mk ("canonical.json")))) (outcomeSnapshot
          request owner (canonicalCheck request owner))
      else
        let checked ← match SquareRoot.Replay.BoundedPreparedSourceReplay.begin segment current owner request
            (SquareRoot.Replay.PreparedSourceReplay.Inputs.capture segment request.rootDiameter) with
          | .checked result => pure result
          | .diameter _ _ => throw (IO.userError "bounded reset fixture unexpectedly needs diameter preparation")
          | .moving pending => do
              movingCount := movingCount + 1
              let first ← MovingResetCheckpoint.runPlan control ((Purelib.System.FilePath.join directory
                (System.FilePath.mk ("pool"))))
                ((Purelib.System.FilePath.join stepDirectory (System.FilePath.mk ("first"))))
                  (SquareRoot.Replay.MovingRecenterReplay.moving owner)
              MovingResetCheckpoint.runPlan control ((Purelib.System.FilePath.join directory (System.FilePath.mk
                ("pool")))) ((Purelib.System.FilePath.join stepDirectory (System.FilePath.mk ("later"))))
                (SquareRoot.Replay.BoundedMovingReplay.finishMoves segment current owner request pending first)
        let expected : Json ← loadJson ((Purelib.System.FilePath.join stepDirectory (System.FilePath.mk
          ("canonical.json"))))
        unless outcomeSnapshot request owner checked.value == expected do
          throw (IO.userError s!"bounded reset replay differs from original at depth {depth}")
        match checked.value with
        | .ok _ => acceptedCount := acceptedCount + 1
        | .error _ => missedCount := missedCount + 1
    else throw (IO.userError "dyadic fixture endpoint outside unit interval")
  if mode != "bounded-calibrate" then
    unless movingCount > 0 && acceptedCount > 0 && missedCount > 0 do
      throw (IO.userError
        s!"bounded fixture missed required coverage: moves={movingCount} accepted={acceptedCount} missed={missedCount}")
    Purelib.System.IO.println
      s!"Bounded reset replay: {movingCount} moving cases, {acceptedCount} successes, {missedCount} certified misses."

end Bounded

open Purelib.RootIsolation in
/-- A midpoint through the displayed root stops before the first winding request. The source remains valid; only this
reset attempt is unavailable. -/
@[expose] def unavailable (directory : System.FilePath) : IO Unit := do
  let centered : Box := ⟨1 / 2, 3 / 2, -1 / 2, 1 / 2, by decide, by decide⟩
  let owner ← sourceAtBox centered ⟨by decide, by decide⟩
  let restored ← MovingResetCheckpoint.runPlan ⟨true, pure ()⟩ ((Purelib.System.FilePath.join directory
    (System.FilePath.mk ("unused-pool"))))
    ((Purelib.System.FilePath.join directory (System.FilePath.mk ("unavailable"))))
      (SquareRoot.Replay.MovingRecenterReplay.moving owner)
  match found : restored.val with
  | none =>
      have exactUnavailable : SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner = none :=
        restored.property.symm.trans found
      let certified : {value : Option (SquareRoot.Clearance.ExactQuadraticOwnerClearance.MovingRecenter _ owner) //
          value = SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner} := ⟨none,
            exactUnavailable.symm⟩
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("unavailable-result.json")))) (snapshot
        certified.val)
  | some _ => throw (IO.userError "midpoint-through-root reset unexpectedly accepted")
  if ← ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk ("unavailable")))
    (System.FilePath.mk ("request.json")))).pathExists then
    throw (IO.userError "unavailable midpoint reset incorrectly requested a winding calculation")

/-- Dispatch the unavailable-reset, bounded-reset or shared winding replay fixture. -/
@[expose] def child (directory : System.FilePath) (mode : String) : IO Unit :=
  if mode == "unavailable" then unavailable directory
  else if (Purelib.Data.String.startsWith mode "bounded-") then Bounded.run directory mode else run directory mode

/-- Interrupt after one atomically saved division, then require exact cold replay and reuse at another depth without any
winding generator call. -/
@[expose] def selfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "moving-reset self-test requires a fresh artifact directory")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let copy ← Purelib.System.IO.Process.output
    { cmd := "/bin/cp", args := #[executable, ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("tested-harness")))).toString] }
  unless copy.exitCode == 0 do throw (IO.userError copy.stderr)
  let invoke := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "45s", executable, "moving-child", directory.toString, mode]
      }
  for mode in ["calibrate", "crash", "resume", "replay", "shared",
      "bounded-calibrate", "bounded-resume", "bounded-replay"] do
    let result ← invoke mode
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{mode}-result.json"))))
      (result.exitCode.toNat, result.stdout, result.stderr)
    let count := fun marker => ((Purelib.Data.String.splitOn (result.stdout ++ result.stderr) marker)).length - 1
    if mode == "calibrate" || mode == "bounded-calibrate" then
      let marker := if mode == "calibrate" then "CANONICAL_MOVING_RESET_FORCED" else "CANONICAL_BOUNDED_RESET_FORCED"
      let expected := if mode == "calibrate" then 1 else 13
      unless result.exitCode == 0 && count marker == expected do
        throw (IO.userError ("moving-reset calibration failed\n" ++ result.stdout ++ result.stderr))
    else
      unless count "CANONICAL_MOVING_RESET_FORCED" == 0 && count "CANONICAL_BOUNDED_RESET_FORCED" == 0 do
        throw (IO.userError "reset replay invoked a canonical generator")
      if mode == "crash" then
        unless result.exitCode != 0 && count "WINDING_DIVISION_GENERATOR_FORCED" == 1 do
          throw (IO.userError ("reset checkpoint interruption failed\n" ++ result.stdout ++ result.stderr))
      else
        unless result.exitCode == 0 && count "REUSED winding division" > 0 do
          throw (IO.userError ("reset restart failed\n" ++ result.stdout ++ result.stderr))
        if mode == "replay" || mode == "shared" || mode == "bounded-replay" then
          unless count "WINDING_DIVISION_GENERATOR_FORCED" == 0 do
            throw (IO.userError "cold reset replay regenerated a completed winding division")
        Purelib.System.IO.println
          s!"{mode}: exact original result; winding divisions generated={count "WINDING_DIVISION_GENERATOR_FORCED"}"
  let unavailableResult ← invoke "unavailable"
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("unavailable-child.json"))))
    (unavailableResult.exitCode.toNat, unavailableResult.stdout, unavailableResult.stderr)
  unless unavailableResult.exitCode == 0 &&
      ((Purelib.Data.String.splitOn (unavailableResult.stdout ++ unavailableResult.stderr) "GENERATOR_FORCED")).length
        == 1 do
    throw (IO.userError "unavailable reset regenerated a winding or failed its exact replay")
  let path := (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk
    ("first-depth"))) (System.FilePath.mk ("request.json")))
  let saved : MovingResetCheckpoint.RequestData ← loadJson path
  saveJson path ({saved with schema := saved.schema + 1} : MovingResetCheckpoint.RequestData)
  let corrupt ← invoke "corrupt"
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("corrupt-result.json"))))
    (corrupt.exitCode.toNat, corrupt.stdout, corrupt.stderr)
  saveJson path saved
  unless corrupt.exitCode != 0 && (← ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("first-depth"))) (System.FilePath.mk ("invalid-request.json")))).pathExists) do
    throw (IO.userError "incompatible moving-reset winding request was accepted")
  Purelib.System.IO.println
    "Moving reset: SIGKILL restart, original owner and bridge, original bounded successes and misses, generator-free \
      cold/cross-depth replay, and incompatible-request rejection passed."

end MovingResetCheckpointTests

namespace PreparedSourceReplayHarness

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

open Purelib.Riemann
open Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay

open Purelib.Polynomial in
/-- The constant Gaussian polynomial one. -/
@[expose] def polynomial : Polynomial := Dense.Basic.DensePolynomial.constant 1

/-- The rational rectangle around the unit real path. -/
@[expose] def ambient : Box := ⟨0, 1, -1, 1, by decide, by decide⟩

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- The unit horizontal path with exact unit polynomial clearance. -/
@[expose] def segment : Geometry.ClearPath.ClearSegment polynomial ambient
    (Components.Basic.point 0 0) (Components.Basic.point 1 0) :=
  .horizontal 0 1 0 (by decide) (by decide) (by decide) (by decide)
    { bound := 1
      positive := by decide
      lower := by
        intro x _ _
        rw [polynomial, Dense.Basic.DensePolynomial.eval_constant]
        exact le_rfl }

/-- The source endpoint at parameter zero. -/
@[expose] def current : Endpoint := ⟨0, by decide⟩

/-- The quarter-interval prepared-source request with root diameter four. -/
@[expose] def request : PreparedSheetContinuation.StepRequest :=
  ⟨⟨1 / 4, by decide⟩, 4, by decide⟩

/-- The symmetric rational box retaining the positive root of one. -/
@[expose] def initialBox : Box := ⟨1 / 2, 3 / 2, -1 / 2, 1 / 2, by decide, by decide⟩

open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Validate a proper fixture box's exact determinants and winding before constructing its original source owner. -/
@[expose] def sourceAtBox (box : Box) (proper : box.Proper) :
    IO (Owner (polynomial.eval (segment.pointAt current.parameter))) := do
  let parameter := polynomial.eval (segment.pointAt current.parameter)
  have nonzero : parameter ≠ 0 := by
    simp only [parameter, polynomial, Dense.Basic.DensePolynomial.eval_constant]
    decide
  if left : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter box.xLower ≠ 0 then
    if right : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter box.xUpper ≠ 0 then
      if bottom : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter box.yLower ≠ 0 then
        if top : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter box.yUpper ≠ 0 then
          if winding : Winding.Box.Basic.quadrupledBoxWinding
              (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter) box = 4 then
            return SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOfBox parameter nonzero
              box proper left right bottom top winding
          else throw (IO.userError "fixture winding rejected")
        else throw (IO.userError "fixture top determinant rejected")
      else throw (IO.userError "fixture bottom determinant rejected")
    else throw (IO.userError "fixture right determinant rejected")
  else throw (IO.userError "fixture left determinant rejected")

/-- Construct the checked source owner in the original symmetric fixture box. -/
@[expose] def source : IO (Owner (polynomial.eval (segment.pointAt current.parameter))) :=
  sourceAtBox initialBox ⟨by decide, by decide⟩

/-- Run the original prepared-source constructor with a calibrated search marker. -/
@[expose, noinline] def canonical (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :=
  dbg_trace "PREPARED_SOURCE_CANONICAL_SEARCH_FORCED"
  PreparedSheetContinuation.prepared segment current owner request

open Purelib.RootIsolation in
/-- The equality to the marked canonical constructor must survive elaboration while the constructor itself must
disappear from the replay executable path. -/
@[expose] def accepted (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    IO { value : Owner (polynomial.eval (segment.pointAt current.parameter)) //
      value = canonical owner } := do
  match SquareRoot.Replay.PreparedSourceReplay.replay segment current owner request .inherited with
  | .ok result => return ⟨result.cached.preparedOwner, result.cached.preparedOwner_eq⟩
  | .error (.notReady _ data _) =>
      throw (IO.userError
        s!"inherited fixture not ready: diameter={IntegrationCheckpoint.fractionText data.diameter}; \
          predicted={IntegrationCheckpoint.fractionText data.predicted}; \
          clearance={IntegrationCheckpoint.fractionText data.clearance}")
  | .error (.selectedMisses data _) =>
      throw (IO.userError
        s!"inherited fixture misses: movement={IntegrationCheckpoint.fractionText data.movement}; \
          clearance={IntegrationCheckpoint.fractionText data.clearance}")
  | .error (.earlierCarries _ _ _ _) => throw (IO.userError "inherited fixture has an earlier choice")

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Retain the same root state with its boundary bound capped at one thirty-second.

The exact weaker clearance permits testing the original strengthening branch without changing the raw root box. -/
@[expose] def weakened (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    Owner (polynomial.eval (segment.pointAt current.parameter)) :=
  have smallPositive : (0 : Fraction.Rational) < 1 / 32 :=
    Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide))
  let initial := owner.track.initial
  let clearance : Clearance.Box.Boundary.Basic.BoundaryClearance
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial
        (polynomial.eval (segment.pointAt current.parameter))) initial.box :=
    { bound := min initial.clearance.bound (1 / 32)
      positive := Fraction.Order.Basic.lt_min initial.clearance.positive smallPositive
      lower := fun z onBoundary => (Fraction.Order.Basic.min_le_left _ _).trans (initial.clearance.lower z onBoundary) }
  SquareRoot.Clearance.ExactQuadraticOwnerClearance.ownerOfState owner.parameterNonzero
    { initial with clearance := clearance }

open Purelib.Data.Rat in
open Purelib.RootIsolation in
/-- A valid representative with a different left-side number. Its raw state is unchanged; the original accelerated
refiner is not retained. -/
@[expose] def rawFixture {parameter : Gaussian} (owner : Owner parameter) :
    SquareRoot.Replay.PreparedRawStateReplay.Checked parameter owner.ambient
      (SquareRoot.Replay.PreparedRawStateReplay.capture owner.track.initial) :=
  let initial := owner.track.initial
  let old := initial.ambientLeftClearance
  have halfLe : old.bound / 2 ≤ old.bound :=
    (Fraction.Order.Field.div_le_iff_pos (show (0 : Fraction.Rational) < 2 by decide)).mpr (by
      calc
        old.bound ≤ old.bound + old.bound := le_add_of_nonneg_right old.positive.le
        _ = old.bound * 2 := by ring1)
  let left :=
    { old with
      bound := old.bound / 2
      positive := Fraction.Order.Field.div_pos_direct old.positive (by decide)
      lower := fun y lower upper => halfLe.trans (old.lower y lower upper) }
  ⟨{ initial with ambientLeftClearance := left }, rfl⟩

/-- Build the small dyadic request without a million-step unary Nat cast. -/
@[expose] def dyadicEndpoint : Nat → Endpoint
  | 0 => ⟨1, by decide⟩
  | depth + 1 =>
      let previous := dyadicEndpoint depth
      ⟨ClearSheetContinuation.midpoint 0 previous.parameter,
        ClearSheetContinuation.midpoint_inside (by decide) previous.inside⟩

/-- The depth-twenty dyadic request with root diameter one quarter. -/
@[expose] def rawRequest : PreparedSheetContinuation.StepRequest :=
  ⟨dyadicEndpoint 20, 1 / 4, by decide⟩

/-- Mark evaluation of the original incoming owner to detect unwanted source reconstruction. -/
@[expose, noinline] def markedIncoming
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :=
  dbg_trace "PREPARED_RAW_INCOMING_SOURCE_FORCED"
  owner

/-- Run canonical preparation for the small raw-state request with a calibrated marker. -/
@[expose, noinline] def canonicalRaw
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :=
  dbg_trace "PREPARED_RAW_CANONICAL_SEARCH_FORCED"
  PreparedSheetContinuation.prepared segment current owner rawRequest

/-- Replay the bounded raw-state diameter preparation with equality to the original canonical result.

Retain readiness, finite-attempt or movement failure instead of substituting another source. -/
@[expose] def acceptedRaw (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    m { value : Owner (polynomial.eval (segment.pointAt current.parameter)) //
      value = canonicalRaw (markedIncoming owner) } := do
  match ← DiameterPreparationCheckpoint.replayRaw segment current (markedIncoming owner) rawRequest
      (rawFixture owner) rfl control directory with
  | .ok result => return ⟨result.cached.preparedOwner, result.cached.preparedOwner_eq⟩
  | .error (.alreadyReady _ _) => throw (IO.userError "raw fixture must need diameter preparation")
  | .error (.attemptMiss _ _ _ _) => throw (IO.userError "raw fixture missed its bounded diameter attempt")
  | .error (.doesNotCarry _ movement _ _) =>
      throw (IO.userError s!"raw fixture does not carry movement {IntegrationCheckpoint.fractionText movement}")

open Purelib.Data.Rat in
/-- Check raw-state preparation against the canonical owner while exercising all retained inconclusive branches.

Save proposal counters and verify that cold replay invokes neither incoming-source nor completed proposal generation. -/
@[expose] def rawChild (directory : System.FilePath) (mode : String) : IO Unit := do
  let initial ← source
  let owner := SquareRootContinuationChain.Owner.ofState initial.parameterNonzero initial.track.initial
  let raw := rawFixture owner
  unless raw.representative.ambientLeftClearance.bound != owner.track.initial.ambientLeftClearance.bound do
    throw (IO.userError "raw fixture did not change the original side bound")
  let capture := fun (value : Owner (polynomial.eval (segment.pointAt current.parameter))) =>
    Json.mkObj
      [("ambient", toJson (RootStateCheckpoint.boxData value.ambient)),
       ("rootState", toJson (RootStateCheckpoint.capture value.track.initial))]
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("raw-prepared-owner.json")))
  if mode == "calibrate" then
    IntegrationCheckpoint.saveJson path (capture (canonicalRaw (markedIncoming owner)))
    return
  let savedOnly := mode == "restart"
  let killAfter := if mode == "kill-newton" || mode == "kill-rounding" then some 1 else none
  let counterAction : RootRefinementCheckpoint.Execution Unit := do
    let control ← RootRefinementCheckpoint.Control.create savedOnly killAfter
    let result ← acceptedRaw control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("diameter")))) owner
    let saved : Json ← IntegrationCheckpoint.loadJson path
    unless saved == capture result.val do
      throw (IO.userError "raw replay differs from canonical preparation")
    let small := result.val.track.initial.box.diagonalSq
    unless small < rawRequest.rootDiameter do throw (IO.userError "raw replay lost requested diameter")
    match ← DiameterPreparationCheckpoint.replayRaw segment current owner request raw rfl control
        ((Purelib.System.FilePath.join directory (System.FilePath.mk ("already-ready")))) with
    | .error (.alreadyReady data _) =>
        unless data.diameter == owner.track.initial.box.diagonalSq do
          throw (IO.userError "ready-branch report lost its original diameter")
    | _ => throw (IO.userError "raw route must not replace an already-ready source")
    let far : PreparedSheetContinuation.StepRequest := { rawRequest with endpoint := ⟨1, by decide⟩ }
    match ← DiameterPreparationCheckpoint.replayRaw segment current owner far raw rfl control
        ((Purelib.System.FilePath.join directory (System.FilePath.mk ("diameter")))) with
    | .error (.doesNotCarry candidate movement _ _) =>
        unless candidate.result.value.track.initial.clearance.bound ≤ movement do
          throw (IO.userError "raw failed-movement operands are inconsistent")
    | _ => throw (IO.userError "raw missed movement did not retain the failed comparison")
    let radius := (dyadicEndpoint 80).parameter
    if x : (1 : Fraction.Rational) - radius ≤ 1 + radius then do
      if y : -radius ≤ radius then do
        let thin : Box := ⟨1 - radius, 1 + radius, -radius, radius, x, y⟩
        letI : Decidable thin.Proper := by unfold Purelib.Geometry.Rational.Box.Proper; infer_instance
        if proper : thin.Proper then do
          let narrow ← sourceAtBox thin proper
          match ← DiameterPreparationCheckpoint.replayRaw segment current narrow rawRequest (rawFixture narrow) rfl
              control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("narrow")))) with
          | .error (.attemptMiss data _ _ _) =>
              unless data.clearance < data.predicted do
                throw (IO.userError "missed-attempt fixture lost its insufficient starting clearance")
          | _ => throw (IO.userError "narrow raw fixture did not exercise bounded-attempt failure")
        else throw (IO.userError "narrow raw fixture is not proper")
      else throw (IO.userError "narrow raw fixture has inverted y bounds")
    else throw (IO.userError "narrow raw fixture has inverted x bounds")
    let counts ← RootRefinementCheckpoint.Execution.counts
    if savedOnly then
      unless counts.generatedNewton == 0 && counts.generatedRounding == 0 do
        throw (IO.userError "saved-only diameter replay regenerated proposals")
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"counts-{mode}.json")))) counts
    Purelib.System.IO.println (toJson counts).compress
    Purelib.System.IO.println
      "Raw-state canonical preparation: exact result and all three inconclusive branches passed."
  let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult

open Purelib.Data.Rat in
open Purelib.RootIsolation in
/-- Check inherited and strengthened prepared-source choices and reject unjustified later hints.

Retain exact readiness and movement operands when the requested choice cannot carry the step. -/
@[expose] def child (directory : System.FilePath) (mode : String) : IO Unit := do
  let owner ← source
  if mode == "calibrate" then
    Purelib.System.IO.println (IntegrationCheckpoint.fractionText (canonical owner).track.initial.clearance.bound)
    return
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("prepared-source-hint.json")))
  if mode == "save" then
    let result ← accepted owner
    IntegrationCheckpoint.saveJson path (0 : Nat)
    Purelib.System.IO.println
      s!"saved certified inherited choice; \
        diameter={IntegrationCheckpoint.fractionText result.val.track.initial.box.diagonalSq}"
  else
    let hint : Nat ← IntegrationCheckpoint.loadJson path
    unless hint == 0 do throw (IO.userError "saved fixture hint does not select inherited preparation")
    let result ← accepted owner
    unless result.val.track.initial.box.diagonalSq == initialBox.diagonalSq do
      throw (IO.userError "replayed owner changed its certified box")
    Purelib.System.IO.println "restored checked canonical choice without the canonical search"
  for hint in [Hint.strengthened, Hint.recentered] do
    match SquareRoot.Replay.PreparedSourceReplay.replay segment current owner request hint with
    | .error (.earlierCarries .inherited _ comparison _) =>
        unless comparison.movement == (1 / 16 : Fraction.Rational) ∧ comparison.clearance ==
          owner.track.initial.clearance.bound do
          throw (IO.userError "wrong-choice report lost its checked comparison")
    | _ => throw (IO.userError "wrong later choice was not rejected with earlier-branch evidence")
  let tooSmall : PreparedSheetContinuation.StepRequest :=
    { request with rootDiameter := 1, rootDiameterPositive := by decide }
  match SquareRoot.Replay.PreparedSourceReplay.replay segment current owner tooSmall .inherited with
  | .error (.notReady .inherited data _) =>
      unless data.diameter == initialBox.diagonalSq do
        throw (IO.userError "readiness failure lost the attempted diameter")
  | _ => throw (IO.userError "undersized diameter was not reported as inconclusive")
  let tooFar : PreparedSheetContinuation.StepRequest := { request with endpoint := ⟨1, by decide⟩ }
  match SquareRoot.Replay.PreparedSourceReplay.replay segment current owner tooFar .inherited with
  | .error (.selectedMisses data _) =>
      unless data.movement == (1 : Fraction.Rational) ∧ data.clearance == owner.track.initial.clearance.bound do
        throw (IO.userError "missed movement report lost its checked operands")
  | _ => throw (IO.userError "non-carrying choice was not reported as inconclusive")
  let weak := weakened owner
  match SquareRoot.Replay.PreparedSourceReplay.replay segment current weak request .strengthened with
  | .ok result =>
      unless result.movement == (1 / 16 : Fraction.Rational) ∧ result.clearance == owner.track.initial.clearance.bound
        do
        throw (IO.userError "strengthened replay lost its cached successful comparison")
  | .error _ => throw (IO.userError "same-box strengthening fixture unexpectedly inconclusive")
  match SquareRoot.Replay.PreparedSourceReplay.replay segment current weak request .recentered with
  | .error (.earlierCarries .strengthened _ _ _) => pure ()
  | _ => throw (IO.userError "recenter hint did not retain the earlier strengthening success")

/-- Check exact prepared-source replay across two atomic interruption boundaries.

Calibrate original-generator markers, reuse completed Newton and rounding witnesses, reject corrupted data and retain
certified inconclusivity. -/
@[expose] def selfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "regression requires a fresh output directory")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let run := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable, "child", directory.toString, mode] }
  let marker := fun (output : IO.Process.Output) =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) "PREPARED_SOURCE_CANONICAL_SEARCH_FORCED")).length >
      1
  let calibration ← run "calibrate"
  unless calibration.exitCode == 0 && marker calibration do
    throw (IO.userError ("canonical search marker calibration failed\n" ++ calibration.stdout ++ calibration.stderr))
  for mode in ["save", "resume"] do
    let output ← run mode
    unless output.exitCode == 0 && !marker output do
      throw (IO.userError ("prepared replay invoked canonical search or failed\n" ++ output.stdout ++ output.stderr))
    IO.print output.stdout
  let runRaw := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable, "raw-child", directory.toString, mode] }
  let rawMarker := fun (output : IO.Process.Output) =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) "PREPARED_RAW_CANONICAL_SEARCH_FORCED")).length > 1
  let incomingMarker := fun (output : IO.Process.Output) =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) "PREPARED_RAW_INCOMING_SOURCE_FORCED")).length > 1
  let occurrences := fun (output : IO.Process.Output) marker =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) marker)).length - 1
  let record := fun label (output : IO.Process.Output) =>
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"raw-{label}-result.json"))))
      (output.exitCode.toNat, output.stdout, output.stderr)
  let rawCalibration ← runRaw "calibrate"
  record "calibrate" rawCalibration
  unless rawCalibration.exitCode == 0 && rawMarker rawCalibration && incomingMarker rawCalibration do
    throw (IO.userError ("raw canonical marker calibration failed\n" ++ rawCalibration.stdout ++ rawCalibration.stderr))
  let newton ← runRaw "kill-newton"
  record "kill-newton" newton
  unless newton.exitCode != 0 && !rawMarker newton && !incomingMarker newton &&
      occurrences newton "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 1 &&
      occurrences newton "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 0 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("diameter/warmup/proposal-0-newton.json")))).pathExists) do
    throw (IO.userError ("warm-up Newton interruption failed\n" ++ newton.stdout ++ newton.stderr))
  let incomplete ← runRaw "restart"
  record "incomplete-restart" incomplete
  unless incomplete.exitCode != 0 && !rawMarker incomplete && !incomingMarker incomplete &&
      occurrences incomplete "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 0 &&
      occurrences incomplete "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 0 do
    throw (IO.userError "incomplete saved-only replay must report missing evidence without generating")
  let rounding ← runRaw "kill-rounding"
  record "kill-rounding" rounding
  unless rounding.exitCode != 0 && !rawMarker rounding && !incomingMarker rounding &&
      occurrences rounding "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 0 &&
      occurrences rounding "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 1 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("diameter/warmup/proposal-0-rounding.json")))).pathExists) do
    throw (IO.userError ("warm-up rounding interruption repeated Newton generation or failed\n" ++ rounding.stdout ++
      rounding.stderr))
  for mode in ["replay", "restart"] do
    let output ← runRaw mode
    record mode output
    unless output.exitCode == 0 && !rawMarker output && !incomingMarker output do
      throw (IO.userError ("raw replay invoked canonical preparation or failed\n" ++ output.stdout ++ output.stderr))
    if mode == "restart" then
      unless occurrences output "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 0 &&
          occurrences output "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 0 do
        throw (IO.userError "cold diameter restart regenerated a completed proposal")
    IO.print output.stdout
  let nextPath := (Purelib.System.FilePath.join directory (System.FilePath.mk
    ("diameter/warmup/proposal-0-newton.json")))
  let savedNext : IntegrationCheckpoint.GaussianData ← IntegrationCheckpoint.loadJson nextPath
  IntegrationCheckpoint.saveJson nextPath (IntegrationCheckpoint.gaussianData (0 : Gaussian))
  let badNewton ← runRaw "restart"
  record "bad-newton" badNewton
  unless badNewton.exitCode != 0 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk ("diameter/warmup/invalid.json")))).pathExists) do
    throw (IO.userError "corrupt warm-up Newton update was accepted")
  IntegrationCheckpoint.saveJson nextPath savedNext
  let roundingPath := (Purelib.System.FilePath.join directory (System.FilePath.mk
    ("diameter/warmup/proposal-0-rounding.json")))
  let savedRounding : RootRefinementCheckpoint.RawWitness ← IntegrationCheckpoint.loadJson roundingPath
  IntegrationCheckpoint.saveJson roundingPath
    ({ savedRounding with realFloor := "0" } : RootRefinementCheckpoint.RawWitness)
  let badRounding ← runRaw "restart"
  record "bad-rounding" badRounding
  unless badRounding.exitCode != 0 do throw (IO.userError "corrupt warm-up rounding was accepted")
  IntegrationCheckpoint.saveJson roundingPath savedRounding
  let finalReplay ← runRaw "restart"
  record "final-restart" finalReplay
  unless finalReplay.exitCode == 0 && !rawMarker finalReplay && !incomingMarker finalReplay &&
      occurrences finalReplay "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 0 &&
      occurrences finalReplay "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 0 do
    throw (IO.userError "restored witnesses failed final generator-free replay")
  Purelib.System.IO.println
    "Prepared-source replay: two SIGKILL checkpoints, generator-free restart, exact canonical equality, \
      corrupt-witness rejection and certified inconclusivity passed."

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- The one-segment clear path used by the bounded bank regression. -/
@[expose] def bankPath : Purelib.Polynomial.Geometry.ClearPath polynomial ambient (Components.Basic.point 0 0)
  (Components.Basic.point 1 0) :=
  .cons segment (.nil _)

open Purelib.Data.Rat in
/-- The bank path remains inside its retained rational ambient box. -/
theorem bankWithin : bankPath.WithinAmbient := .cons (by
  change (-1 : Fraction.Rational) ≤ 0 ∧ (0 : Fraction.Rational) ≤ 1
  constructor <;> decide) (.nil _)

open Purelib.RootIsolation in
/-- The singleton bank task using the original fixture path and retained owner. -/
@[expose] def bankTasks (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :=
  [SquareRoot.Preparation.Bank.Adaptive.Task.ofPath bankPath bankWithin owner]

section

open Purelib.RootIsolation

/-- Run the original adaptive bank selector with a calibrated generation marker. -/
@[expose, noinline] def canonicalBank (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :=
  dbg_trace "CANONICAL_BANK_GENERATOR_FORCED"
  SquareRoot.Preparation.Bank.Adaptive.select (bankTasks owner) 1 (by decide)

/-- The marked bank constructor retains the original adaptive selection exactly. -/
theorem canonicalBank_eq (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    canonicalBank owner = SquareRoot.Preparation.Bank.Adaptive.select (bankTasks owner) 1 (by decide) := by
  unfold canonicalBank
  exact PreparedSourceReplayHarnessTrace.trace_eq "CANONICAL_BANK_GENERATOR_FORCED" (fun _ =>
    SquareRoot.Preparation.Bank.Adaptive.select (bankTasks owner) 1 (by decide))

end

section
open Purelib.Polynomial
/-- Serialize the complete ordered subdivision requests and their source and prepared owner states. -/
@[expose] def subdivisionSnapshot {p : Polynomial} {box : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment p box start finish} {within : segment.WithinAmbient} :
    {left : Endpoint} → {owner : Owner (p.eval (segment.pointAt left.parameter))} →
      PreparedSheetContinuation.Subdivision segment within left owner → List Json
  | _, _, .stop left owner => [Json.mkObj
      [("stop", toJson (IntegrationCheckpoint.fractionData left.parameter)),
       ("owner", InitialExtractionCheckpoint.stateData owner.track.initial)]]
  | _, _, .next left owner request cached _ _ rest => Json.mkObj
      [("left", toJson (IntegrationCheckpoint.fractionData left.parameter)),
       ("right", toJson (IntegrationCheckpoint.fractionData request.endpoint.parameter)),
       ("diameter", toJson (IntegrationCheckpoint.fractionData request.rootDiameter)),
       ("source", InitialExtractionCheckpoint.stateData owner.track.initial),
       ("prepared", InitialExtractionCheckpoint.stateData cached.preparedOwner.track.initial)] :: subdivisionSnapshot
         rest

/-- Serialize every retained segment subdivision and the terminal path owner. -/
@[expose] def pathSnapshot {p : Polynomial} {box : Box} :
    {start finish : Gaussian} → {path : Purelib.Polynomial.Geometry.ClearPath p box start finish} →
      {owner : Owner (p.eval start)} → PreparedClearPathModels.PreparedPath path owner → List Json
  | _, _, _, _, .nil _ owner => [InitialExtractionCheckpoint.stateData owner.track.initial]
  | _, _, _, _, .cons _ _ _ _ head tail => toJson (subdivisionSnapshot head.subdivision) :: pathSnapshot tail

end

open Purelib.RootIsolation in
/-- Serialize the selected depth, step count and complete prepared owner spine. -/
@[expose] def bankSnapshot (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (selected : SquareRoot.Preparation.Bank.Adaptive.Selected (bankTasks owner) 1 (by decide)) : Json :=
  Json.mkObj [("depth", toJson selected.depth),
    ("steps", toJson selected.banks.head.prepared.stepCount),
    ("spine", toJson (pathSnapshot selected.banks.head.prepared))]

/-- Restore the exact original bank selection and compare its full retained spine with calibration data. -/
@[expose] def bankChild (directory : System.FilePath) (mode : String) : IO Unit := do
  IO.FS.createDirAll directory
  let owner ← source
  if mode == "calibrate" then
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("canonical-bank.json")))) (bankSnapshot owner (canonicalBank owner))
    return
  let counterAction : RootRefinementCheckpoint.Execution Unit := do
    let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
      (if mode == "crash" then some 1 else none)
    let result ← PreparedBankCheckpoint.select (bankTasks owner) 1 (by decide) control ((Purelib.System.FilePath.join
      directory (System.FilePath.mk ("bank"))))
    have exactOriginal : result.val = canonicalBank owner :=
      result.property.trans (canonicalBank_eq owner).symm
    let linked : {value // value = canonicalBank owner} := ⟨result.val, exactOriginal⟩
    let expected : Json ← IntegrationCheckpoint.loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("canonical-bank.json"))))
    unless bankSnapshot owner linked.val == expected do
      throw (IO.userError "bank replay changed selected depth, requests or owner states")
    let counts ← RootRefinementCheckpoint.Execution.counts
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"counts-{mode}.json")))) counts
    if mode == "replay" then
      unless counts.generatedNewton == 0 && counts.generatedRounding == 0 do
        throw (IO.userError "cold bank replay regenerated a diameter proposal")
    Purelib.System.IO.println s!"Original bank restored at depth {linked.val.depth}: {(toJson counts).compress}"
  let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult

/-- Check bank interruption recovery, exact selected depth and owner spine, and generator-free cold replay. -/
@[expose] def bankSelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "bank self-test requires a fresh artifact directory")
  IO.FS.createDirAll directory
  let copy ← Purelib.System.IO.Process.output
    { cmd := "/bin/cp", args := #[(← IO.appPath).toString, ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("tested-harness")))).toString] }
  unless copy.exitCode == 0 do throw (IO.userError copy.stderr)
  let executable := (← IO.appPath).toString
  for mode in ["calibrate", "crash", "resume", "replay"] do
    let result ← Purelib.System.IO.Process.output
      { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "45s", executable, "bank-child", directory.toString, mode]
        }
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"{mode}-result.json")))) (result.exitCode.toNat, result.stdout, result.stderr)
    let count := fun marker => ((Purelib.Data.String.splitOn (result.stdout ++ result.stderr) marker)).length - 1
    if mode == "calibrate" then
      unless result.exitCode == 0 && count "CANONICAL_BANK_GENERATOR_FORCED" == 1 do
        throw (IO.userError ("bank calibration failed\n" ++ result.stdout ++ result.stderr))
    else if mode == "crash" then
      unless result.exitCode != 0 && count "CANONICAL_BANK_GENERATOR_FORCED" == 0 &&
          count "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 1 do
        throw (IO.userError ("bank checkpoint interruption failed\n" ++ result.stdout ++ result.stderr))
    else
      unless result.exitCode == 0 && count "CANONICAL_BANK_GENERATOR_FORCED" == 0 do
        throw (IO.userError ("bank restart failed\n" ++ result.stdout ++ result.stderr))
      let counts : RootRefinementCheckpoint.Counts ← IntegrationCheckpoint.loadJson ((Purelib.System.FilePath.join
        directory (System.FilePath.mk (s!"counts-{mode}.json"))))
      unless 0 < counts.reusedNewton do throw (IO.userError "bank restart did not reuse the saved Newton proposal")
      if mode == "replay" then
        unless count "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 0 && count "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 0 do
          throw (IO.userError "cold bank replay forced a completed proposal generator")
      IO.print result.stdout
  Purelib.System.IO.println
    "Bounded bank: atomic restart, original depth and full-spine equality, generator-free cold replay passed."

open Purelib.Data.Rat in
open Purelib.Integration in
/-- Expose a finite prefix of the original dyadic request cursor without forcing its unvisited suffix. -/
@[expose] def requestPrefix (diameter : Fraction.Rational) (positive : 0 < diameter) :
    Nat → Path.Dyadic.DyadicRequestCursor.Cursor → List PreparedSheetContinuation.StepRequest
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, frame :: rest =>
      let head := Path.Dyadic.DyadicRequestCursor.expose diameter positive frame.depth frame.left frame.right rest
      head.request :: requestPrefix diameter positive fuel head.remaining

/-- Materialize the original complete dyadic request list with a calibrated marker. -/
@[expose, noinline] def originalRequests (depth : Nat) :=
  dbg_trace "ORIGINAL_DYADIC_REQUEST_LIST_FORCED"
  PreparedSheetContinuation.Subdivision.dyadicRequests depth PreparedClearPathModels.zeroEndpoint
    PreparedClearPathModels.oneEndpoint 1 (by decide)

open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.RootIsolation in
/-- Compare small cursor expansions or restore eight depth-thirty-five requests with their exact unvisited stacks.

The rejected-suffix case checks that an early unordered request does not force the remaining complete list. -/
@[expose] def cursorChild (directory : System.FilePath) (mode : String) : IO Unit := do
  if mode == "calibrate" then
    for depth in [:8] do
      let original := originalRequests depth
      let restored := requestPrefix 1 (by decide) (2 ^ depth)
        (Path.Dyadic.DyadicRequestCursor.initial depth PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint)
      let snapshot := fun (requests : List PreparedSheetContinuation.StepRequest) =>
        requests.map fun request => (IntegrationCheckpoint.fractionText request.endpoint.parameter,
          IntegrationCheckpoint.fractionText request.rootDiameter)
      unless snapshot original == snapshot restored do
        throw (IO.userError s!"incremental requests changed the original ordered list at depth {depth}")
    Purelib.System.IO.println "All original requests agree at depths zero through seven."
    return
  if mode == "rejected-suffix" then
    let owner ← source
    let counterAction : RootRefinementCheckpoint.Execution Unit := do
      let control ← RootRefinementCheckpoint.Control.create true
      have diameterPositive : (0 : Fraction.Rational) < 1 := by decide
      let result ← PreparedBankCheckpoint.steps segment bankWithin.head control ((Purelib.System.FilePath.join directory
        (System.FilePath.mk ("unordered"))))
        (1 : Fraction.Rational) diameterPositive (SquareRoot.Replay.PreparedSourceReplay.Inputs.capture segment 1)
          PreparedClearPathModels.oneEndpoint owner 0
        (Path.Dyadic.DyadicRequestCursor.initial 35 PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint)
      match result.val with
      | .ok _ => throw (IO.userError "backward request unexpectedly accepted")
      | .error _ =>
          Purelib.System.IO.println
            "Original depth-35 rejection retained without constructing its unvisited suffix."
      return
    let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
    (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult
    return

  let mut cursor := Path.Dyadic.DyadicRequestCursor.initial 35 PreparedClearPathModels.zeroEndpoint
    PreparedClearPathModels.oneEndpoint
  let mut current := PreparedClearPathModels.zeroEndpoint
  for index in [:8] do
    match cursor with
    | [] => throw (IO.userError "depth-35 request cursor ended prematurely")
    | frame :: rest =>
        let head := Path.Dyadic.DyadicRequestCursor.expose 1 (by decide) frame.depth frame.left frame.right rest
        let data := PreparedBankCheckpoint.cursorData index current head
        let expected := Fraction.Cast.fromInt (Int.ofNat (index + 1)) /
          Fraction.Cast.fromInt (Int.ofNat (2 ^ 35))
        unless head.request.endpoint.parameter == expected && data.remainingCount == 2 ^ 35 - index - 1 do
          throw (IO.userError "depth-35 cursor changed a target or the complete unvisited request count")
        let step := (Purelib.System.FilePath.join directory (System.FilePath.mk (s!"step-{index}")))
        let savedAlready ← ((Purelib.System.FilePath.join step (System.FilePath.mk ("request-cursor.json")))).pathExists
        if mode == "replay" && !savedAlready then
          throw (IO.userError "cold cursor replay lost a saved request")
        PreparedBankCheckpoint.retainCursor step data
        Purelib.System.IO.println (if savedAlready then "REUSED checked request cursor" else
          "SAVED checked request cursor")
        if mode == "crash" then
          (← IO.getStdout).flush
          let pid ← IO.Process.getPID
          discard <| Purelib.System.IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
          throw (IO.userError "cursor interruption unexpectedly returned")
        current := head.request.endpoint
        cursor := head.remaining
  Purelib.System.IO.println "Eight original depth-35 requests restored with their exact unvisited interval stacks."

/-- Check cursor equivalence, atomic restart and rejection of altered request indices, counts, endpoints, stacks or
diameters. -/
@[expose] def cursorSelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "cursor self-test requires a fresh artifact directory")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let run := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "15s", executable,
        "cursor-child", directory.toString, mode] }
  for mode in ["calibrate", "rejected-suffix", "crash", "resume", "replay", "replay"] do
    let result ← run mode
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"{mode}-result.json"))))
      (result.exitCode.toNat, result.stdout, result.stderr)
    let count := fun marker => ((Purelib.Data.String.splitOn (result.stdout ++ result.stderr) marker)).length - 1
    if mode == "calibrate" then
      unless result.exitCode == 0 && count "ORIGINAL_DYADIC_REQUEST_LIST_FORCED" == 8 do
        throw (IO.userError ("original request comparison failed\n" ++ result.stdout ++ result.stderr))
    else if mode == "rejected-suffix" then
      unless result.exitCode == 0 && count "ORIGINAL_DYADIC_REQUEST_LIST_FORCED" == 0 do
        throw (IO.userError ("rejected suffix was forced\n" ++ result.stdout ++ result.stderr))
    else if mode == "crash" then
      unless result.exitCode != 0 && count "SAVED checked request cursor" == 1 do
        throw (IO.userError "cursor interruption did not preserve exactly its first request")
    else
      unless result.exitCode == 0 && count "ORIGINAL_DYADIC_REQUEST_LIST_FORCED" == 0 &&
          count "REUSED checked request cursor" == (if mode == "resume" then 1 else 8) do
        throw (IO.userError ("incremental cursor restart failed\n" ++ result.stdout ++ result.stderr))
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("step-0/request-cursor.json")))
  let saved : PreparedBankCheckpoint.CursorData ← IntegrationCheckpoint.loadJson path
  for corrupt in [{saved with index := 1}, {saved with remainingCount := 0},
      {saved with endpoint := "1/1"}, {saved with intervals := []}, {saved with diameter := "2/1"}] do
    IntegrationCheckpoint.saveJson path corrupt
    let result ← run "replay"
    unless result.exitCode != 0 && (1 < (Purelib.Data.String.splitOn (result.stdout ++ result.stderr)
      "saved request cursor differs").length) do
      throw (IO.userError "corrupted request cursor was not rejected")
  IntegrationCheckpoint.saveJson path saved
  let result ← run "replay"
  unless result.exitCode == 0 do throw (IO.userError "repaired cursor did not replay")
  Purelib.System.IO.println
    "Dyadic cursor: original list equality, depth-35 SIGKILL restart, two cold replays and corrupt-cursor rejection \
      passed."
open Purelib.Data.Gaussian in
/-- Serialize the complete terminal-acquisition spine and retained endpoint owner. -/
@[expose] def terminalSnapshot {owner : Owner (polynomial.eval (Components.Basic.point 0 0))}
    (prepared : PreparedClearPathModels.CompleteSegment segment bankWithin.head owner)
    (finishOwner : Owner (polynomial.eval (Components.Basic.point 1 0))) : Json :=
  Json.mkObj [("spine", toJson (subdivisionSnapshot prepared.subdivision)),
    ("terminal", InitialExtractionCheckpoint.stateData finishOwner.track.initial)]

open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Acquire the original segment at its proved safe dyadic depth. -/
@[expose] def canonicalTerminalFor {p : Polynomial} {box : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment p box start finish) (within : segment.WithinAmbient)
    (owner : Owner (p.eval start))
    (budget : Purelib.Riemann.Paths.PreparedTraceBudget segment
      PreparedClearPathModels.zeroEndpoint PreparedClearPathModels.oneEndpoint) :=
  (SquareRoot.Preparation.Terminal.AcquiredDyadic.acquire segment within owner
    budget.rootDiameter budget.rootDiameter_positive budget.depth budget.depth
    (budget.meshSafe (PreparedClearPathModels.ownerAtStart segment owner) (by decide))).val

open Purelib.Polynomial in
/-- Restore safe-depth terminal acquisition with its exact original constructor equation. -/
@[expose] def acquireSafeFor {p : Polynomial} {box : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment p box start finish) (within : segment.WithinAmbient)
    (owner : Owner (p.eval start))
    (budget : Purelib.Riemann.Paths.PreparedTraceBudget segment
      PreparedClearPathModels.zeroEndpoint PreparedClearPathModels.oneEndpoint)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :=
  PreparedBankCheckpoint.terminalAcquire (m := m) segment within owner budget.rootDiameter budget.rootDiameter_positive
    budget.depth budget.depth (budget.meshSafe (PreparedClearPathModels.ownerAtStart segment owner) (by decide))
    control directory

open Purelib.Data.Gaussian in
/-- Run the original safe-depth terminal acquisition with a calibrated marker. -/
@[expose, noinline] def canonicalTerminal (owner : Owner (polynomial.eval (Components.Basic.point 0 0))) :=
  dbg_trace "CANONICAL_TERMINAL_GENERATOR_FORCED"
  canonicalTerminalFor segment bankWithin.head owner
    (Purelib.Riemann.Paths.PreparedTraceBudget.build segment
      PreparedClearPathModels.zeroEndpoint PreparedClearPathModels.oneEndpoint)

/-- Restore safe-depth acquisition and compare all original requests, owner states and retained endpoint data. -/
@[expose] def terminalChild (directory : System.FilePath) (mode : String) : IO Unit := do
  IO.FS.createDirAll directory
  let owner ← source
  if mode == "calibrate" then
    let original := canonicalTerminal owner
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("canonical-terminal.json"))))
      (terminalSnapshot original.prepared original.finishOwner)
    return
  let counterAction : RootRefinementCheckpoint.Execution Unit := do
    let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
      (if mode == "crash" then some 1 else none)
    let budget := Purelib.Riemann.Paths.PreparedTraceBudget.build segment
      PreparedClearPathModels.zeroEndpoint PreparedClearPathModels.oneEndpoint
    let linked ← acquireSafeFor segment bankWithin.head owner budget control ((Purelib.System.FilePath.join directory
      (System.FilePath.mk ("terminal"))))
    let expected : Json ← IntegrationCheckpoint.loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("canonical-terminal.json"))))
    unless terminalSnapshot linked.val.prepared linked.val.finishOwner == expected do
      IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("invalid-terminal.json"))))
        (terminalSnapshot linked.val.prepared linked.val.finishOwner, expected)
      throw (IO.userError "terminal replay changed canonical requests, owner spine or retained endpoint")
    let counts ← RootRefinementCheckpoint.Execution.counts
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"counts-{mode}.json")))) counts
    if mode == "replay" then
      unless counts.generatedNewton == 0 && counts.generatedRounding == 0 do
        throw (IO.userError "cold terminal replay regenerated a diameter proposal")
    Purelib.System.IO.println s!"Canonical terminal acquisition restored: {(toJson counts).compress}"
  let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult

open Purelib.Data.Gaussian in
/-- Run the original preferred-depth segment trace with its safe fallback and calibrated marker. -/
@[expose, noinline] def canonicalPreferredTerminal (owner : Owner (polynomial.eval (Components.Basic.point 0 0))) :=
  dbg_trace "CANONICAL_TERMINAL_GENERATOR_FORCED"
  PreparedPathTrace.TracedSegment.build segment bankWithin.head owner

/-- Restore preferred-depth acquisition and check its full original spine and retained endpoint. -/
@[expose] def preferredTerminalChild (directory : System.FilePath) (mode : String) : IO Unit := do
  IO.FS.createDirAll directory
  let owner ← source
  if mode == "calibrate" then
    let original := canonicalPreferredTerminal owner
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("canonical-terminal.json"))))
      (terminalSnapshot original.prepared original.finishOwner)
    return
  let counterAction : RootRefinementCheckpoint.Execution Unit := do
    let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
      (if mode == "crash" then some 1 else none)
    let result ← PreparedBankCheckpoint.tracedSegment segment bankWithin.head owner control
      ((Purelib.System.FilePath.join directory (System.FilePath.mk ("terminal"))))
    let value := result.val
    let expected : Json ← IntegrationCheckpoint.loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("canonical-terminal.json"))))
    unless terminalSnapshot value.prepared value.finishOwner == expected do
      IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("invalid-terminal.json"))))
        (terminalSnapshot value.prepared value.finishOwner, expected)
      throw (IO.userError "terminal replay changed canonical requests, owner spine or retained endpoint")
    let counts ← RootRefinementCheckpoint.Execution.counts
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"counts-{mode}.json")))) counts
    if mode == "replay" then
      unless counts.generatedNewton == 0 && counts.generatedRounding == 0 do
        throw (IO.userError "cold terminal replay regenerated a diameter proposal")
    Purelib.System.IO.println s!"Canonical terminal acquisition restored: {(toJson counts).compress}"
  let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- The fixture segment followed by its exact reversed clear segment. -/
@[expose] def traceLoop : Purelib.Polynomial.Geometry.ClearPath polynomial ambient (Components.Basic.point 0 0)
  (Components.Basic.point 0 0) :=
  .cons segment (.cons (Branches.BranchCutLifts.ClearSegment.reverse segment) (.nil _))

open Purelib.Curves.Hyperelliptic in
/-- Both legs of the retained trace loop lie within the original ambient box. -/
theorem traceLoopWithin : traceLoop.WithinAmbient :=
  .cons bankWithin.head (.cons (Branches.BranchCutLifts.ClearSegment.reverse_withinAmbient segment bankWithin.head)
    (.nil _))

section
open Purelib.Data.Gaussian
/-- Construct the original loop trace with a calibrated generation marker. -/
@[expose, noinline] def canonicalTracedPath (owner : Owner (polynomial.eval (Components.Basic.point 0 0))) :=
  dbg_trace "CANONICAL_TERMINAL_GENERATOR_FORCED"
  PreparedPathTrace.TracedPath.build traceLoop traceLoopWithin owner

/-- Serialize the original moving vertices and terminal owner of the trace loop. -/
@[expose] def tracedPathSnapshot {owner : Owner (polynomial.eval (Components.Basic.point 0 0))}
    (value : PreparedPathTrace.TracedPath traceLoop owner) : Json :=
  Json.mkObj [("vertices", toJson (value.movingVertices.map IntegrationCheckpoint.gaussianData)),
    ("terminal", InitialExtractionCheckpoint.stateData value.finishOwner.track.initial)]

end

/-- Restore the loop trace and verify exact vertices, terminal owner and generator-free saved replay. -/
@[expose] def tracedPathChild (directory : System.FilePath) (mode : String) : IO Unit := do
  IO.FS.createDirAll directory
  let owner ← source
  if mode == "calibrate" then
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("canonical-path.json")))) (tracedPathSnapshot (canonicalTracedPath owner))
    return
  let counterAction : RootRefinementCheckpoint.Execution Unit := do
    let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
      (if mode == "crash" then some 1 else none)
    let result ← PreparedBankCheckpoint.tracedPath control ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("path")))) traceLoop traceLoopWithin owner 0
    let expected : Json ← IntegrationCheckpoint.loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("canonical-path.json"))))
    unless tracedPathSnapshot result.val == expected do
      throw (IO.userError "restored path changed canonical moving vertices or terminal owner")
    let counts ← RootRefinementCheckpoint.Execution.counts
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"counts-{mode}.json")))) counts
    if mode == "replay" then
      unless counts.generatedNewton == 0 && counts.generatedRounding == 0 do
        throw (IO.userError "cold path replay regenerated a completed witness")
    Purelib.System.IO.println s!"Canonical traced path restored: {(toJson counts).compress}"
  let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult

section
open Purelib.Data.Gaussian
open Purelib.RootIsolation
/-- Build the original reversible root edge between retained owner frames with a calibrated marker. -/
@[expose, noinline] def canonicalRootEdge
    (first : RootOwnerFrames.OwnerFrame (polynomial.eval (Components.Basic.point 0 0)))
    (last : RootOwnerFrames.OwnerFrame (polynomial.eval (Components.Basic.point 1 0))) :=
  dbg_trace "CANONICAL_TERMINAL_GENERATOR_FORCED"
  SquareRoot.Grid.RootEdges.RootEdge.build segment bankWithin.head first last

/-- Serialize all forward and reverse sheet targets and their exact terminal owner states. -/
@[expose] def rootEdgeSnapshot
    {first : RootOwnerFrames.OwnerFrame (polynomial.eval (Components.Basic.point 0 0))}
    {last : RootOwnerFrames.OwnerFrame (polynomial.eval (Components.Basic.point 1 0))}
    (value : SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) first last) : Json :=
  Json.mkObj [("targets", toJson
    [value.forward.zero.target.val, value.forward.one.target.val,
      value.backward.zero.target.val, value.backward.one.target.val]),
    ("terminals", toJson
      [InitialExtractionCheckpoint.stateData value.forward.zero.traced.finishOwner.track.initial,
       InitialExtractionCheckpoint.stateData value.forward.one.traced.finishOwner.track.initial,
       InitialExtractionCheckpoint.stateData value.backward.zero.traced.finishOwner.track.initial,
       InitialExtractionCheckpoint.stateData value.backward.one.traced.finishOwner.track.initial])]

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- Restore the original finite owner frame and reversible root edge with checked canonical sheet assignments. -/
@[expose] def rootEdgeChild (directory : System.FilePath) (mode : String) : IO Unit := do
  IO.FS.createDirAll directory
  let counterAction : RootRefinementCheckpoint.Execution Unit := do
    let frameControl ← RootRefinementCheckpoint.Control.create (mode == "replay")
    have nonzero : polynomial.eval (Components.Basic.point 0 0) ≠ 0 := by
      rw [polynomial, Dense.Basic.DensePolynomial.eval_constant]
      decide
    SquareRootFamilyCheckpoint.withFrame nonzero frameControl ((Purelib.System.FilePath.join directory
      (System.FilePath.mk ("frame")))) fun frame => do
      if mode == "calibrate" then
        IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
          ("canonical-edge.json"))))
          (rootEdgeSnapshot (canonicalRootEdge frame.val frame.val))
        return
      let counterAction : RootRefinementCheckpoint.Execution Unit := do
        let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
          (if mode == "crash" then some 1 else none)
        let result ← RootTransportCheckpoint.edge segment bankWithin.head frame.val frame.val
          (RootTransportCheckpoint.classify nonzero frame.val frame.property)
          (RootTransportCheckpoint.classify nonzero frame.val frame.property) control ((Purelib.System.FilePath.join
            directory (System.FilePath.mk ("edge"))))
        let actual := rootEdgeSnapshot result.val
        IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
          ("restored-edge.json")))) actual
        if mode != "acquire" then
          let expected : Json ← IntegrationCheckpoint.loadJson ((Purelib.System.FilePath.join directory
            (System.FilePath.mk ("canonical-edge.json"))))
          unless actual == expected do
            throw (IO.userError "restored reversible edge changed its canonical sheet targets or terminal owners")
        let counts ← RootRefinementCheckpoint.Execution.counts
        IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
          (s!"counts-{mode}.json")))) counts
        if mode == "replay" then
          unless counts.generatedNewton == 0 && counts.generatedRounding == 0 do
            throw (IO.userError "cold edge replay regenerated a trace witness")
        Purelib.System.IO.println s!"Canonical reversible root edge restored (mode={mode}): {(toJson counts).compress}"
      let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
      (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult
  let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult

open Purelib in
/-- The exact squared residual criterion below one over 4096 for a square root of two. -/
@[expose] def sampleAcceptable (point : Gaussian) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (point * point - 2) < 1 / 4096

/-- Decide the exact rational residual bound for a proposed Gaussian sample. -/
instance (point : Gaussian) : Decidable (sampleAcceptable point) := by
  unfold sampleAcceptable
  infer_instance

open Purelib.RootIsolation in
/-- Run the original eight-step rounded root sample search with a calibrated marker. -/
@[expose, noinline] def canonicalSample (parameter : Gaussian) :=
  dbg_trace "CANONICAL_SAMPLE_GENERATOR_FORCED"
  SquareRoot.Newton.Search.search parameter sampleAcceptable 8 (1 / 1024) 1

/-- Restore the original rounded sample search while retaining its checked inverse and rounding witnesses. -/
@[expose] def uniformSearchChild (directory : System.FilePath) (mode : String) : IO Unit := do
  IO.FS.createDirAll directory
  if mode == "calibrate" then
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("canonical-sample.json"))))
      ((canonicalSample 2).map fun point => IntegrationCheckpoint.gaussianData point.val)
    return
  let counterAction : RootRefinementCheckpoint.Execution Unit := do
    let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
      (if mode == "crash" then some 1 else none)
    let trace ← UniformSampleCheckpoint.search 2 sampleAcceptable control ((Purelib.System.FilePath.join directory
      (System.FilePath.mk ("search")))) 8 (1 / 1024) 1
    let actual := toJson (trace.result.map fun point => IntegrationCheckpoint.gaussianData point.val)
    let expected : Json ← IntegrationCheckpoint.loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("canonical-sample.json"))))
    unless actual == expected do throw (IO.userError "rounded sample trace changed original finite search")
    let counts ← RootRefinementCheckpoint.Execution.counts
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"counts-{mode}.json")))) counts
    unless counts.generatedNewton + counts.reusedNewton > 0 do
      throw (IO.userError "sample regression did not exercise a Newton inverse witness")
    if mode == "replay" then
      unless counts.generatedNewton == 0 && counts.generatedRounding == 0 do
        throw (IO.userError "cold sample replay regenerated a proposal")
    Purelib.System.IO.println s!"Exact rounded sample search restored: {(toJson counts).compress}"
  let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult

/-- Check atomic interruption, exact original results and cold witness reuse for terminal, sample or path replay. -/
@[expose] def terminalSelfTest (directory : System.FilePath) (preferred : Bool := false) (sample : Bool := false) (path
  : Bool := false) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "terminal self-test requires a fresh artifact directory")
  IO.FS.createDirAll directory
  let copy ← Purelib.System.IO.Process.output
    { cmd := "/bin/cp", args := #[(← IO.appPath).toString, ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("tested-harness")))).toString] }
  unless copy.exitCode == 0 do throw (IO.userError copy.stderr)
  let executable := (← IO.appPath).toString
  for mode in ["calibrate", "crash", "resume", "replay"] do
    let result ← Purelib.System.IO.Process.output
      { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "45s", executable, (if path then "traced-path-child" else
        if sample then "uniform-sample-child" else if preferred then "preferred-terminal-child" else "terminal-child"),
        directory.toString, mode] }
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"{mode}-result.json")))) (result.exitCode.toNat, result.stdout, result.stderr)
    let count := fun marker => ((Purelib.Data.String.splitOn (result.stdout ++ result.stderr) marker)).length - 1
    if mode == "calibrate" then
      unless result.exitCode == 0 && count (if sample then "CANONICAL_SAMPLE_GENERATOR_FORCED" else
        "CANONICAL_TERMINAL_GENERATOR_FORCED") == 1 do
        throw (IO.userError ("terminal calibration failed\n" ++ result.stdout ++ result.stderr))
    else if mode == "crash" then
      unless result.exitCode != 0 && count (if sample then "CANONICAL_SAMPLE_GENERATOR_FORCED" else
        "CANONICAL_TERMINAL_GENERATOR_FORCED") == 0 &&
          count (if sample then "UNIFORM_SAMPLE_ROUNDING_GENERATOR_FORCED" else "ROOT_TRACE_NEWTON_GENERATOR_FORCED") ==
            1 do
        throw (IO.userError ("terminal checkpoint interruption failed\n" ++ result.stdout ++ result.stderr))
    else
      unless result.exitCode == 0 && count (if sample then "CANONICAL_SAMPLE_GENERATOR_FORCED" else
        "CANONICAL_TERMINAL_GENERATOR_FORCED") == 0 do
        throw (IO.userError ("terminal restart failed\n" ++ result.stdout ++ result.stderr))
      let counts : RootRefinementCheckpoint.Counts ← IntegrationCheckpoint.loadJson ((Purelib.System.FilePath.join
        directory (System.FilePath.mk (s!"counts-{mode}.json"))))
      unless 0 < (if sample then counts.reusedRounding else counts.reusedNewton) do throw (IO.userError
        "terminal restart did not reuse the saved Newton proposal")
      if mode == "replay" then
        unless count "UNIFORM_SAMPLE_ROUNDING_GENERATOR_FORCED" == 0 && count "UNIFORM_SAMPLE_INVERSE_GENERATOR_FORCED"
          == 0 && count "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 0 && count "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 0
          do
          throw (IO.userError "cold terminal replay forced a completed proposal generator")
      IO.print result.stdout
  if path then
    Purelib.System.IO.println
      "Canonical traced path: atomic restart, original vertices and endpoint, generator-free cold replay passed."
  else if sample then
    Purelib.System.IO.println
      "Rounded sample search: atomic restart, canonical result and generator-free cold replay passed."
  else
    Purelib.System.IO.println
      s!"Canonical terminal acquisition (preferred={preferred}): atomic restart, original full-spine and endpoint \
        readbacks, generator-free cold replay passed."

end PreparedSourceReplayHarness

namespace RootReturnCheckpointTests
open Purelib.Riemann IntegrationCheckpoint
open PreparedSheetContinuation

/-- Select the exact containment, common-box, opposite-root or zero-axis return fixture. -/
@[expose] def boxFor (kind : String) : Box :=
  if kind == "inner" then ⟨3 / 4, 5 / 4, -1 / 4, 1 / 4, by decide, by decide⟩
  else if kind == "opposite" then ⟨-3 / 2, -1 / 4, -1 / 2, 3 / 4, by decide, by decide⟩
  else if kind == "axis-first" then ⟨1 / 4, 17 / 4, -1 / 2, 3 / 4, by decide, by decide⟩
  else if kind == "axis-last" then ⟨1 / 2, 9 / 2, -1 / 4, 1, by decide, by decide⟩
  else if kind == "shifted" then ⟨1 / 2, 7 / 4, -1 / 4, 1, by decide, by decide⟩
  else MovingResetCheckpointTests.fixture

/-- Validate the selected return-fixture box and construct its retained root owner. -/
@[expose] def source (kind : String) : IO (Owner (1 : Gaussian)) := do
  let box := boxFor kind
  if proper : box.xLower < box.xUpper ∧ box.yLower < box.yUpper then
    MovingResetCheckpointTests.sourceAtBox box proper
  else throw (IO.userError "invalid root-return fixture")

/-- Run the original root-return check with a calibrated generation marker. -/
@[expose, noinline] def canonical (first last : Owner (1 : Gaussian)) :=
  dbg_trace "CANONICAL_ROOT_RETURN_CHECK_FORCED"
  RootReturnBox.check first last

open scoped Purelib.Data.Int.Decimal in
/-- Serialize containment, checked common-owner data or the exact finite return-check failure. -/
@[expose] def snapshot {first last : Owner (1 : Gaussian)} :
    Except (RootReturnBox.Inconclusive first last) (RootReturnBox.Certificate first last) → Json
  | .ok (.lastInside _) => Json.mkObj [("kind", toJson "last inside")]
  | .ok (.firstInside _) => Json.mkObj [("kind", toJson "first inside")]
  | .ok (.common attempt winding _ _ owner _) => Json.mkObj
      [("kind", toJson "common box"), ("winding", toJson winding),
       ("box", toJson (RootStateCheckpoint.boxData attempt.box)),
       ("owner", InitialExtractionCheckpoint.stateData owner.track.initial)]
  | .error failure =>
      let reason := match failure.reason with
        | .leftZero _ => "left determinant zero"
        | .rightZero .. => "right determinant zero"
        | .bottomZero .. => "bottom determinant zero"
        | .topZero .. => "top determinant zero"
        | .windingMiss _ _ _ _ winding _ _ => s!"winding {winding} differs from four"
      Json.mkObj [("kind", toJson "certified finite miss"), ("reason", toJson reason),
        ("box", toJson (RootStateCheckpoint.boxData failure.attempt.box)),
        ("queries", toJson failure.reason.windingQueries)]

/-- Calibrate or replay five exact root-return cases through checked shared winding requests. -/
@[expose] def child (directory : System.FilePath) (mode : String) : IO Unit := do
  IO.FS.createDirAll directory
  for (label, firstKind, lastKind) in
      [("last-inside", "outer", "inner"), ("first-inside", "inner", "outer"),
       ("shifted", "outer", "shifted"), ("opposite", "outer", "opposite"),
       ("axis", "axis-first", "axis-last")] do
    let first ← source firstKind
    let last ← source lastKind
    if mode == "calibrate" then
      let outcome := canonical first last
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{label}-canonical.json")))) (snapshot
        outcome)
      match outcome with
      | .ok certificate =>
          if label == "opposite" || label == "axis" then
            throw (IO.userError "root-return negative fixture unexpectedly accepted")
          match certificate with
          | .common .. => unless label == "shifted" do throw (IO.userError "unexpected common-box fixture")
          | _ => unless label != "shifted" do throw (IO.userError "shifted fixture must exercise the common box")
      | .error failure =>
          match failure.reason with
          | .windingMiss _ _ _ _ winding _ _ =>
              unless label == "opposite" && winding == 8 do throw (IO.userError "wrong winding-miss fixture")
          | .leftZero _ => unless label == "axis" do throw (IO.userError "wrong axis-miss fixture")
          | _ => throw (IO.userError "unexpected root-return stop")
    else
      let control : WindingCheckpoint.Control :=
        { savedOnly := mode == "replay" || mode == "shared"
          afterSave := if mode == "crash" then do
            (← IO.getStdout).flush
            let pid ← IO.Process.getPID
            discard <| Purelib.System.IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
            throw (IO.userError "root-return regression kill unexpectedly returned")
          else pure () }
      let occurrence := (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk ((if
        mode == "shared" then "another-occurrence" else "first-occurrence")))) (System.FilePath.mk (label)))
      let restored ← MovingResetCheckpoint.runPlan control ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("pool")))) occurrence
        (RootReturnBox.replay first last)
      let expected : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
        (s!"{label}-canonical.json"))))
      unless snapshot restored.val == expected do throw (IO.userError "root-return replay changed its canonical result")
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{label}-{mode}.json")))) (snapshot
        restored.val)
  Purelib.System.IO.println
    "Exact root-return cases restored: both containments, shifted common box, winding-eight miss, and zero-axis miss."

/-- Check both containments, common-box success and exact winding or axis misses across interrupted and shared replay.
-/
@[expose] def selfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "root-return self-test requires a fresh directory")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let copy ← Purelib.System.IO.Process.output { cmd := "/bin/cp", args := #[executable, ((Purelib.System.FilePath.join
    directory (System.FilePath.mk ("tested-harness")))).toString] }
  unless copy.exitCode == 0 do throw (IO.userError copy.stderr)
  for mode in ["calibrate", "crash", "resume", "replay", "shared"] do
    let result ← Purelib.System.IO.Process.output
      { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable,
          "return-child", directory.toString, mode] }
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{mode}-result.json"))))
      (result.exitCode.toNat, result.stdout, result.stderr)
    let count := fun marker => ((Purelib.Data.String.splitOn (result.stdout ++ result.stderr) marker)).length - 1
    if mode == "calibrate" then
      unless result.exitCode == 0 && count "CANONICAL_ROOT_RETURN_CHECK_FORCED" == 5 do
        throw (IO.userError ("root-return calibration failed\n" ++ result.stdout ++ result.stderr))
    else
      unless count "CANONICAL_ROOT_RETURN_CHECK_FORCED" == 0 do throw (IO.userError
        "replay forced canonical root-return checking")
      if mode == "crash" then
        unless result.exitCode != 0 && count "WINDING_DIVISION_GENERATOR_FORCED" == 1 do
          throw (IO.userError "root-return interruption missed its first atomic division checkpoint")
      else
        unless result.exitCode == 0 && count "REUSED winding division" > 0 do
          throw (IO.userError ("root-return restart failed\n" ++ result.stdout ++ result.stderr))
        if mode == "replay" || mode == "shared" then
          unless count "WINDING_DIVISION_GENERATOR_FORCED" == 0 do throw (IO.userError
            "root-return replay regenerated a saved division")
        Purelib.System.IO.println
          s!"{mode}: exact root-return result; winding divisions generated={count "WINDING_DIVISION_GENERATOR_FORCED"}"
  Purelib.System.IO.println
    "Root return: five source-exact cases, SIGKILL restart, generator-free cold replay and cross-occurrence reuse \
      passed."
end RootReturnCheckpointTests

/-- Dispatch the requested finite source, bank, cursor, terminal, trace, sample or root-return checkpoint regression. -/
@[expose] def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["return-self-test", directory] => RootReturnCheckpointTests.selfTest directory
  | ["return-child", directory, mode] => RootReturnCheckpointTests.child directory mode
  | ["moving-self-test", directory] => MovingResetCheckpointTests.selfTest directory
  | ["moving-child", directory, mode] => MovingResetCheckpointTests.child directory mode
  | ["self-test", directory] => PreparedSourceReplayHarness.selfTest directory
  | ["child", directory, mode] => PreparedSourceReplayHarness.child directory mode
  | ["raw-child", directory, mode] => PreparedSourceReplayHarness.rawChild directory mode
  | ["uniform-sample-child", directory, mode] => PreparedSourceReplayHarness.uniformSearchChild directory mode
  | ["uniform-sample-self-test", directory] => PreparedSourceReplayHarness.terminalSelfTest directory false true
  | ["root-edge-child", directory, mode] => PreparedSourceReplayHarness.rootEdgeChild directory mode
  | ["traced-path-child", directory, mode] => PreparedSourceReplayHarness.tracedPathChild directory mode
  | ["traced-path-self-test", directory] => PreparedSourceReplayHarness.terminalSelfTest directory false false true
  | ["preferred-terminal-child", directory, mode] => PreparedSourceReplayHarness.preferredTerminalChild directory mode
  | ["preferred-terminal-self-test", directory] => PreparedSourceReplayHarness.terminalSelfTest directory true
  | ["terminal-child", directory, mode] => PreparedSourceReplayHarness.terminalChild directory mode
  | ["terminal-self-test", directory] => PreparedSourceReplayHarness.terminalSelfTest directory
  | ["bank-child", directory, mode] => PreparedSourceReplayHarness.bankChild directory mode
  | ["bank-self-test", directory] => PreparedSourceReplayHarness.bankSelfTest directory
  | ["cursor-child", directory, mode] => PreparedSourceReplayHarness.cursorChild directory mode
  | ["cursor-self-test", directory] => PreparedSourceReplayHarness.cursorSelfTest directory
  | _ => throw (IO.userError
    "usage: prepared_source_replay_harness return-self-test DIRECTORY | moving-self-test DIRECTORY | moving-child \
      DIRECTORY MODE | self-test FRESH_DIRECTORY | bank-self-test FRESH_DIRECTORY | cursor-self-test FRESH_DIRECTORY | \
      terminal-self-test FRESH_DIRECTORY | preferred-terminal-self-test FRESH_DIRECTORY | uniform-sample-self-test \
      FRESH_DIRECTORY | traced-path-self-test FRESH_DIRECTORY")
