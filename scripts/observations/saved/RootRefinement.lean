module

import Purelib.Data.Range

import Purelib.Data.List.Control

import Purelib.System.FilePath

import Purelib.System.IO

meta import Purelib.Elab.ConstructiveInjectivity
meta import Purelib.Elab.Deriving.Json
import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.String.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.Power.Isolation
import scripts.checkpoint.RootRefinement
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSourceRefinementReplay.Restoration
import Purelib.Curves.Hyperelliptic.Integration.Surface.PreparedCycleReplay.Readiness
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Transport.PreparedDeferredRecipeReplay
import Purelib.Riemann.Transport.PreparedDirectRefinementReplay
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.Newton.Search.Replay.Input

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticFallbackReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackSampleReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay
import scripts.checkpoint.Integration
import scripts.checkpoint.RootState
import scripts.checkpoint.QuadraticSample
import scripts.checkpoint.Center
public import scripts.checkpoint.PreparedCenter
public import Purelib.Riemann.RootContinuation.PreparedInitialRootReplay
public import Purelib.Riemann.Periods.PeriodCurves
import Purelib.Tactic.Ring
import Init.Core
public import Init.Data.List.TakeDrop
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Grid.Box
import Purelib.Approximation.Gaussian.Grid.Replay
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.Curves.Hyperelliptic.Integration.Preparation.Roots.PreparedRootSafeReplay.Selection
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.RootContinuation.PreparedRootSafeReplay
import Purelib.Riemann.Topology.PreparedCycleReplay
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.Newton.Search.Iteration
import Purelib.RootIsolation.Newton.Search.Trace
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.SquareRoot.Replay.PreparedOwnerTransportReplay
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.RootIsolation.Track.Basic

-- Use complete constructor eliminators for the original match arms.
set_option backward.match.sparseCases false

open Purelib.Data (Json)
open scoped Purelib.Data.String Purelib.Data.List Purelib.Data.Range
open Purelib.Data.Json (toJson)

public section

/-!
Replay the checked quadratic-refinement branch on a saved canonical cell's
actual parameter, ambient, root box and requested index.  No branch isolation,
cycle preparation or preceding coefficient generation is performed.

The initial box is rechecked using finite determinants and winding.  Its new
clearance certificate need not equal the saved one.  The checked cursor now
proves exact sample-box equality for the displayed deferred constructor even
with different incoming bounds.  It does not reconstruct an unidentified
original period owner or certify identical generic fallback choices.
Each rounding witness and Newton update is saved atomically and checked on
reload without its generator. Winding divisions also have checked restart;
candidate geometry and clearance construction still run, but
the production attempt/refiner is not called a second time.  Rejected
proposals retain the certified prefix and distinguish the stopping reason.
This is not yet a complete canonical-period preparation loader.
Use a SIGKILL timeout and systemd memory bound for this runtime diagnostic.
-/

open Purelib.Riemann.Transport Purelib.Riemann.RootContinuation Purelib.Riemann.Integration
open Purelib.Riemann.Branches Purelib.Riemann.Readings Purelib.Riemann.Paths Purelib.Riemann.Topology

namespace SavedRootRefinementHarnessTrace
/-- Emit the retained native diagnostic marker before evaluating the continuation. -/
@[expose, never_extract, extern "lean_dbg_trace"] def trace {α : Type u}
    (message : String) (work : Unit → α) : α := work ()
end SavedRootRefinementHarnessTrace

macro_rules
  | `(dbg_trace $arg:interpolatedStr; $body) =>
      `(SavedRootRefinementHarnessTrace.trace (s! $arg) fun _ => $body)

namespace SavedRootRefinementHarness

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

open IntegrationCheckpoint
open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance

set_option genInjectivity false in
/-- The saved numerical square-root request with its original ambient, root box and sample index.

These fields specify a finite replay calculation; they do not reconstruct an unidentified period owner or its
construction history. -/
structure Snapshot where
  /-- The exact serialized Gaussian square-root parameter. -/ parameter : GaussianData
  /-- The original ambient box coordinates. -/ ambient : List FractionData
  /-- The original retained root box coordinates. -/ box : List FractionData
  /-- The saved original boundary-clearance value. -/ clearance : FractionData
  /-- The original source track's retained base sample index. -/ baseIndex : Nat
deriving Json.FromJson

constructive_injectivity Snapshot

section
open Purelib.RootIsolation
/-- Serialize all four exact box coordinates in lower-x, upper-x, lower-y, upper-y order. -/
@[expose] public def boxData (box : SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Box) : List
  FractionData :=
  [box.xLower, box.xUpper, box.yLower, box.yUpper].map fractionData

/-- Decode four exact rational coordinates and check both interval orders. -/
@[expose] public def decodeBox (label : String) (data : List FractionData) : IO Box := do
  let [xl, xu, yl, yu] ← data.mapM (fun value => checked label (decodeFraction value))
    | throw (IO.userError s!"{label}: expected four coordinates")
  if xOrdered : xl ≤ xu then
    if yOrdered : yl ≤ yu then return ⟨xl, xu, yl, yu, xOrdered, yOrdered⟩
    else throw (IO.userError s!"{label}: inverted vertical interval")
  else throw (IO.userError s!"{label}: inverted horizontal interval")

end

section
open Purelib
open Purelib.Polynomial
open Purelib.RootIsolation
/-- Build only the finite initial state needed by the checked branch. Keep the saved ambient rather than replacing it by
the smaller source root box. -/
@[expose] public def checkedOwner (parameter :
  SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Gaussian)
  (ambient box : SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Box) :
    IO (Riemann.Topology.SquareRootContinuationChain.Owner parameter) := do
  if nonzero : parameter ≠ 0 then
    if proper : box.xLower < box.xUpper ∧ box.yLower < box.yUpper then
      letI : Decidable (box.Refines ambient) := by
        unfold Purelib.Geometry.Rational.Box.Refines
        infer_instance
      if within : box.Refines ambient then
        if left : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter box.xLower ≠ 0 then
          if right : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter box.xUpper ≠ 0 then
            if bottom : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter box.yLower ≠ 0
              then
              if top : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter box.yUpper ≠ 0 then
                if winding : Winding.Box.Basic.quadrupledBoxWinding
                    (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
                      Riemann.RootContinuation.SquareRootDegree.degreeTwo) box = 4 then
                  return SquareRoot.Clearance.ExactQuadraticOwnerClearance.ownerOfState nonzero
                    { box := box, refinesAmbient := within, proper := proper,
                      clearance := SquareRoot.Clearance.ExactQuadraticOwnerClearance.directBoundaryClearance parameter
                        box left right bottom top,
                      rawWindingFour := winding,
                      ambientLeftClearance :=
                        SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearance
                        parameter ambient box.xLower left,
                      ambientRightClearance :=
                        SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearance
                        parameter ambient box.xUpper right,
                      ambientBottomClearance :=
                      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearance
                        parameter ambient box.yLower bottom,
                      ambientTopClearance :=
                      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearance
                        parameter ambient box.yUpper top }
                else throw (IO.userError "saved root box does not have winding four")
              else throw (IO.userError "saved top determinant is zero")
            else throw (IO.userError "saved bottom determinant is zero")
          else throw (IO.userError "saved right determinant is zero")
        else throw (IO.userError "saved left determinant is zero")
      else throw (IO.userError "saved root box is outside its ambient")
    else throw (IO.userError "saved root box is not proper")
  else throw (IO.userError "saved quadratic parameter is zero")

/-- Evaluate a thunk through IO without inlining its computation boundary. -/
@[expose, noinline] public def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

end

open Purelib.RootIsolation in
/-- Replay the exact saved finite root request using checked rounding, Newton and reciprocal witnesses.

Bind the complete numerical request before restoring the deferred sample track, retaining failed prefixes and forbidding
generation during saved-only replay. -/
@[expose] def runWith (source directory : System.FilePath) (control : RootRefinementCheckpoint.Control) : m Unit := do
  let snapshot : Snapshot ← loadJson ((Purelib.System.FilePath.join source (System.FilePath.mk ("owner.json"))))
  let requested : Nat ← loadJson ((Purelib.System.FilePath.join source (System.FilePath.mk ("reading-index.json"))))
  let parameter ← checked "saved parameter" (decodeGaussian snapshot.parameter)
  let ambient ← decodeBox "saved ambient" snapshot.ambient
  let box ← decodeBox "saved root box" snapshot.box
  let savedClearance ← checked "saved clearance" (decodeFraction snapshot.clearance)
  IO.FS.createDirAll directory
  let identity := Json.mkObj
    [("format", toJson "ccl-root-refinement-traces-v1"),
     ("parameter", toJson (gaussianData parameter)),
     ("ambient", toJson (boxData ambient)), ("box", toJson (boxData box)),
     ("baseIndex", toJson snapshot.baseIndex), ("readingIndex", toJson requested),
     ("recipe", toJson "deferred")]
  let identityPath := (Purelib.System.FilePath.join directory (System.FilePath.mk ("trace-request.json")))
  if ← identityPath.pathExists then
    let saved : Json ← loadJson identityPath
    unless saved == identity do
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-request.json")))) (saved,
        identity)
      throw (IO.userError "root trace source/request differs; exact old and new inputs retained")
  else
    if control.savedOnly then throw (IO.userError "missing root trace request; generation forbidden")
    saveJson identityPath identity
  profile directory "BEGIN finite initial root-box checks"
  let owner ← checkedOwner parameter ambient box
  profile directory
    s!"END finite initial root-box checks; clearance \
      unchanged={decide (savedClearance = owner.track.initial.clearance.bound)}"
  let count := max snapshot.baseIndex requested
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("request.json")))) (snapshot.baseIndex,
    requested, count)
  profile directory s!"Checking {count} actual root steps; no cycle preparation or generic fallback"
  let result ← QuadraticSampleCheckpoint.run
    (SquareRoot.Replay.QuadraticSampleReplay.Recipe.deferred.track owner.parameterNonzero owner.track.initial)
    (SquareRoot.Replay.QuadraticTrackReplay.recipe .deferred _ _)
    (pure (.deferred owner.parameterNonzero (by intros; rfl)))
    control directory count
  let cursor ← match result with
    | .ok cursor => pure cursor
    | .error stopped => throw (IO.userError
      s!"checked root branch stopped at index {stopped.index}; certified prefix and stopping trace retained")
  let value := cursor.state.box.anchor
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("root.json")))) (gaussianData value)
  let reciprocalPath := (Purelib.System.FilePath.join directory (System.FilePath.mk ("reciprocal.json")))
  if ← reciprocalPath.pathExists then
    let raw : GaussianData ← loadJson reciprocalPath
    let reciprocal ← checked "saved reciprocal" (decodeGaussian raw)
    if value == 0 then
      unless reciprocal == 0 do throw (IO.userError "saved zero-denominator reciprocal differs")
    else
      unless reciprocal * value == 1 do throw (IO.userError "saved reciprocal product differs from one")
    profile directory "REUSED checked reciprocal of final root witness; no division"
  else
    if control.savedOnly then throw (IO.userError "missing saved reciprocal; generation forbidden")
    profile directory "BEGIN reciprocal of final root witness"
    let reciprocal ← evaluate fun _ => (1 :
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Gaussian) / value
    saveJson reciprocalPath (gaussianData reciprocal)
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("reuse-counts.json")))) (←
    RootRefinementCheckpoint.Execution.counts)
  profile directory "COMPLETE checked root steps and reciprocal; diagnostic only, no period receipt"

/-- Replay the supplied root snapshot with fresh generation permitted for missing checked stages. -/
@[expose] def run (source directory : System.FilePath) : IO Unit := do
  let action : RootRefinementCheckpoint.Execution Unit :=
    runWith source directory (← RootRefinementCheckpoint.Control.create)
  let (result, _) ← RootRefinementCheckpoint.Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

open Purelib in
open Purelib.Data.Rat in
open Purelib.RootIsolation in
/-- Small regression of both exact recipe equations. This never invokes a long canonical preparation, and keeps its
finite calibration results. -/
@[expose] def selfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "sample self-test requires a fresh directory")
  IO.FS.createDirAll directory
  let box : Box := ⟨1 / 2, 3 / 2, -1 / 2, 1 / 2, by decide, by decide⟩
  let owner ← checkedOwner 1 box box
  let original := owner.track.initial
  let source := (Purelib.System.FilePath.join directory (System.FilePath.mk ("fixture-input")))
  IO.FS.createDirAll source
  saveJson ((Purelib.System.FilePath.join source (System.FilePath.mk ("owner.json")))) (Json.mkObj
    [("parameter", toJson (gaussianData (1 :
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Gaussian))),
     ("ambient", toJson (boxData owner.ambient)),
     ("box", toJson (boxData original.box)),
     ("clearance", toJson (fractionData original.clearance.bound)),
     ("baseIndex", toJson (Riemann.RootContinuation.CertifiedSquareRoot.baseIndex owner.track))])
  saveJson ((Purelib.System.FilePath.join source (System.FilePath.mk ("reading-index.json")))) (8 : Nat)
  run source ((Purelib.System.FilePath.join directory (System.FilePath.mk ("migrated-run"))))
  let weakened : SquareRoot.Replay.QuadraticSampleReplay.State 1 owner.ambient :=
    { original with clearance :=
        { bound := original.clearance.bound / 2
          positive := Fraction.Order.Field.div_pos_direct original.clearance.positive (by decide)
          lower := fun point boundary => (by
            have half : original.clearance.bound / 2 ≤ original.clearance.bound :=
              (Fraction.Order.Field.div_le_iff_pos (show (0 :
                SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Coordinate) < 2 by decide)).mpr
                (by
                calc
                  original.clearance.bound ≤ original.clearance.bound + original.clearance.bound :=
                    le_add_of_nonneg_right original.clearance.positive.le
                  _ = original.clearance.bound * 2 := by ring1)
            exact half.trans (original.clearance.lower point boundary)) } }
  for recipe in [SquareRoot.Replay.QuadraticSampleReplay.Recipe.accelerated, .deferred] do
    let track := recipe.track owner.parameterNonzero original
    let mut cursor : (index : Nat) × SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor track index :=
      ⟨0, SquareRoot.Replay.QuadraticTrackSampleReplay.first track
        (SquareRoot.Replay.QuadraticTrackReplay.recipe recipe _ _) weakened
        (by rw [show track.initial = original from recipe.initial_eq _ _])⟩
    for _ in [:8] do
      match SquareRoot.Replay.QuadraticTrackSampleReplay.advance cursor.2 with
      | .error failure => throw (IO.userError s!"fixture failed at {failure.atIndex}")
      | .ok next => cursor := ⟨cursor.1 + 1, next⟩
    let actual ← evaluate fun _ => Riemann.RootContinuation.CoherentRoot.state
      (recipe.track owner.parameterNonzero original) cursor.1
    let restoredData := RootStateCheckpoint.capture cursor.2.state
    unless toJson restoredData == toJson (RootStateCheckpoint.capture actual) do
      throw (IO.userError "sample replay differs from the complete original state")
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{reprStr recipe}.json")))) restoredData
    Purelib.System.IO.println s!"quadratic sample: {reprStr recipe}, eight steps, complete original state matches"
  match SquareRoot.Replay.QuadraticSampleReplay.attempt weakened 0 with
  | none => pure ()
  | some _ => throw (IO.userError "zero-target finite attempt unexpectedly succeeded")
  let nearRoot := Fraction.Cast.fromInt 1414213562373095 /
    Fraction.Cast.fromInt 1000000000000000
  if ordered : nearRoot ≤ 2 then
    let thinBox : Box := ⟨nearRoot, 2, -1 / 2, 1 / 2, ordered, by decide⟩
    let thin ← checkedOwner 2 thinBox thinBox
    let track := SquareRoot.Replay.QuadraticSampleReplay.Recipe.deferred.track thin.parameterNonzero thin.track.initial
    let cursor := SquareRoot.Replay.QuadraticTrackSampleReplay.first track
      (SquareRoot.Replay.QuadraticTrackReplay.recipe .deferred _ _) thin.track.initial rfl
    match SquareRoot.Replay.QuadraticTrackSampleReplay.advance cursor with
    | .ok _ => throw (IO.userError "near-boundary fixture did not exercise finite inconclusivity")
    | .error failure =>
        unless failure.atIndex == 0 && failure.proposalBudget == 6 && failure.epsilon > 0 do
          throw (IO.userError "inconclusive result lost its finite stopping data")
        saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("inconclusive.json"))))
          (failure.atIndex, failure.proposalBudget, fractionData failure.epsilon,
            RootStateCheckpoint.capture failure.retained.state)
  else throw (IO.userError "near-root fixture bounds inverted")
  Purelib.System.IO.println "Quadratic sample replay: both constructors and changed incoming boundary passed."

open Purelib in
open Purelib.RootIsolation in
/-- Cold-process replay of the migrated disk-input client, with generators forbidden after successful completion. The
fixture requires Newton updates, not just acceptance of the initial midpoint. -/
@[expose, noinline] def referenceSample {parameter :
  SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Gaussian}
    (owner : Riemann.Topology.SquareRootContinuationChain.Owner parameter) :=
  dbg_trace "ROOT_TRACE_ORIGINAL_REFINER_FORCED"
  Riemann.RootContinuation.CoherentRoot.state owner.track 8

/-- Run one calibrated, interrupted or saved-only eight-step root trace and compare its complete original state. -/
@[expose] def traceChild (directory : System.FilePath) (mode : String) : IO Unit := do
  if mode == "calibrate" then
    let box : Box := ⟨1, 2, -1 / 2, 1 / 2, by decide, by decide⟩
    let owner ← checkedOwner 2 box box
    let actual ← evaluate fun _ => referenceSample owner
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("reference-state.json"))))
      (RootStateCheckpoint.capture actual)
    return
  let source := (Purelib.System.FilePath.join directory (System.FilePath.mk ("fixture-input")))
  let target := (Purelib.System.FilePath.join directory (System.FilePath.mk ("root-run")))
  let counterAction : RootRefinementCheckpoint.Execution Unit := do
    let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
      (if mode == "crash-rounding" then some 1 else if mode == "crash-newton" then some 1 else none)
    runWith source target control
    let actual : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("reference-state.json"))))
    let saved : Json ← loadJson ((Purelib.System.FilePath.join target (System.FilePath.mk ("step-8-output.json"))))
    unless saved == actual do
      throw (IO.userError "disk trace result differs from complete original canonical state")
    Purelib.System.IO.println "Eight saved refinements match the complete original state."
  let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult

open Purelib.Data.Rat in
open Purelib.RootIsolation in
/-- Check distinct zero-derivative and six-proposal exhaustion outcomes with their retained certified prefixes. -/
@[expose] def traceStops (directory : System.FilePath) (savedOnly : Bool) : IO Unit := do
  let counterAction : RootRefinementCheckpoint.Execution Unit := do
    let control ← RootRefinementCheckpoint.Control.create savedOnly
    let almostOne := Fraction.Cast.fromInt 999 / 1000
    let overOne := Fraction.Cast.fromInt 1001 / 1000
    if ordered : -almostOne ≤ overOne then
      let box : Box := ⟨-almostOne, overOne, -2, 2, ordered, by decide⟩
      let owner ← checkedOwner 1 box box
      let result ← RootRefinementCheckpoint.run
        (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination 1)
        owner.track.initial.raw 1
        (SquareRoot.Clearance.QuadraticLineClearance.Owner.quadraticAxisClearances 1)
        (.direct _ _)
        control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("zero-derivative"))))
      match result with
      | .zeroDerivative _ _ 1 _ _ _ _ _ => pure ()
      | _ => throw (IO.userError "zero-derivative fixture did not stop after exactly one proposal")
    else throw (IO.userError "zero-derivative fixture inverted")
    let nearRoot := Fraction.Cast.fromInt 1414213562373095 /
      Fraction.Cast.fromInt 1000000000000000
    if ordered : nearRoot ≤ 2 then
      let box : Box := ⟨nearRoot, 2, -1 / 2, 1 / 2, ordered, by decide⟩
      let owner ← checkedOwner 2 box box
      let track := SquareRoot.Replay.QuadraticSampleReplay.Recipe.deferred.track owner.parameterNonzero
        owner.track.initial
      let cursor := SquareRoot.Replay.QuadraticTrackSampleReplay.first track
        (SquareRoot.Replay.QuadraticTrackReplay.recipe .deferred _ _) owner.track.initial rfl
      let result ← RootRefinementCheckpoint.run
        (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination 2)
        cursor.state.raw cursor.epsilon
        (SquareRoot.Clearance.QuadraticLineClearance.Owner.quadraticAxisClearances 2)
        (.direct _ _)
        control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("exhausted"))))
      match result with
      | .exhausted 6 _ _ _ => pure ()
      | _ => throw (IO.userError "thin-root fixture did not exhaust exactly six proposals")
      let replayed ← QuadraticSampleCheckpoint.run
        (SquareRoot.Replay.QuadraticSampleReplay.Recipe.deferred.track owner.parameterNonzero owner.track.initial)
        (SquareRoot.Replay.QuadraticTrackReplay.recipe .deferred _ _)
        (pure .checkedFirstOnly)
        control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("exhausted-prefix")))) 1
      match replayed with
      | .ok _ => throw (IO.userError "sample driver lost the thin-root stopping reason")
      | .error stopped =>
          unless stopped.index == 0 && stopped.failure.proposalBudget == 6 do
            throw (IO.userError "sample driver lost its certified prefix or finite budget")
          match stopped.trace with
          | .exhausted 6 _ _ _ => pure ()
          | _ => throw (IO.userError "sample driver did not retain the exact exhausted trace")
    else throw (IO.userError "exhausted fixture inverted")
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("stopping-counts.json")))) (←
      RootRefinementCheckpoint.Execution.counts)
    Purelib.System.IO.println
      "Distinct checked stopping reasons: zero derivative after one proposal, budget exhausted after six."
  let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult

open Purelib.RootIsolation in
/-- Check exact root-trace restart across separate rounding and Newton saves.

Verify complete original states, repeated generator-free replay, corrupt-request rejection and precise finite stopping
evidence. -/
@[expose] def traceSelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "trace self-test requires a fresh directory")
  let source := (Purelib.System.FilePath.join directory (System.FilePath.mk ("fixture-input")))
  IO.FS.createDirAll source
  let box : Box := ⟨1, 2, -1 / 2, 1 / 2, by decide, by decide⟩
  let owner ← checkedOwner 2 box box
  saveJson ((Purelib.System.FilePath.join source (System.FilePath.mk ("owner.json")))) (Json.mkObj
    [("parameter", toJson (gaussianData (2 :
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Gaussian))),
     ("ambient", toJson (boxData owner.ambient)),
     ("box", toJson (boxData owner.track.initial.box)),
     ("clearance", toJson (fractionData owner.track.initial.clearance.bound)),
     ("baseIndex", toJson (0 : Nat))])
  saveJson ((Purelib.System.FilePath.join source (System.FilePath.mk ("reading-index.json")))) (8 : Nat)
  let executable := (← IO.appPath).toString
  let child := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable,
        "trace-child", directory.toString, mode] }
  let occurrences := fun (output : IO.Process.Output) marker =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) marker)).length - 1
  let record := fun mode (output : IO.Process.Output) => do
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{mode}-result.json"))))
      (output.exitCode.toNat, output.stdout, output.stderr)
  let calibration ← child "calibrate"
  record "calibrate" calibration
  unless calibration.exitCode == 0 &&
      occurrences calibration "ROOT_TRACE_ORIGINAL_REFINER_FORCED" == 1 do
    throw (IO.userError ("reference marker calibration failed\n" ++ calibration.stdout ++ calibration.stderr))
  let rounding ← child "crash-rounding"
  record "crash-rounding" rounding
  unless rounding.exitCode != 0 &&
      occurrences rounding "ROOT_TRACE_ORIGINAL_REFINER_FORCED" == 0 &&
      occurrences rounding "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 1 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("root-run/step-1-trace/proposal-0-rounding.json")))).pathExists) do
    throw (IO.userError ("rounding interruption failed\n" ++ rounding.stdout ++ rounding.stderr))
  let newton ← child "crash-newton"
  record "crash-newton" newton
  unless newton.exitCode != 0 &&
      occurrences newton "ROOT_TRACE_ORIGINAL_REFINER_FORCED" == 0 &&
      occurrences newton "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 0 &&
      occurrences newton "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 1 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("root-run/step-1-trace/proposal-0-newton.json")))).pathExists) do
    throw (IO.userError ("Newton interruption failed or repeated rounding\n" ++ newton.stdout ++ newton.stderr))
  let resumed ← child "resume"
  record "resume" resumed
  unless resumed.exitCode == 0 && occurrences resumed "ROOT_TRACE_ORIGINAL_REFINER_FORCED" == 0 do
    throw (IO.userError ("trace restart failed\n" ++ resumed.stdout ++ resumed.stderr))
  let firstCounts : RootRefinementCheckpoint.Counts ← loadJson ((Purelib.System.FilePath.join directory
    (System.FilePath.mk ("root-run/reuse-counts.json"))))
  unless firstCounts.reusedRounding == 1 && firstCounts.reusedNewton == 1 do
    throw (IO.userError "restart did not reuse the two completed proposal stages")
  for index in [:2] do
    let replay ← child "replay"
    record s!"replay-{index}" replay
    unless replay.exitCode == 0 &&
        occurrences replay "ROOT_TRACE_ORIGINAL_REFINER_FORCED" == 0 &&
        occurrences replay "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 0 &&
        occurrences replay "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 0 do
      throw (IO.userError ("cold trace replay regenerated or failed\n" ++ replay.stdout ++ replay.stderr))
    let counts : RootRefinementCheckpoint.Counts ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("root-run/reuse-counts.json"))))
    unless counts.generatedRounding == 0 && counts.generatedNewton == 0 &&
        counts.reusedRounding > 8 && counts.reusedNewton > 0 do
      throw (IO.userError "cold replay did not exercise rejected and accepted saved proposals")
  let roundingPath := (Purelib.System.FilePath.join directory (System.FilePath.mk
    ("root-run/step-1-trace/proposal-0-rounding.json")))
  let savedRounding : RootRefinementCheckpoint.RawWitness ← loadJson roundingPath
  saveJson roundingPath ({ savedRounding with realFloor := "0" } : RootRefinementCheckpoint.RawWitness)
  let badRounding ← child "replay"
  record "bad-rounding" badRounding
  unless badRounding.exitCode != 0 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("root-run/step-1-trace/invalid.json")))).pathExists) do
    throw (IO.userError "corrupt rounded coordinate was accepted")
  saveJson roundingPath savedRounding
  let nextPath := (Purelib.System.FilePath.join directory (System.FilePath.mk
    ("root-run/step-1-trace/proposal-0-newton.json")))
  let savedNext : GaussianData ← loadJson nextPath
  saveJson nextPath (gaussianData (0 :
    SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Gaussian))
  let badNewton ← child "replay"
  record "bad-newton" badNewton
  unless badNewton.exitCode != 0 do throw (IO.userError "corrupt Newton update was accepted")
  saveJson nextPath savedNext
  saveJson ((Purelib.System.FilePath.join source (System.FilePath.mk ("reading-index.json")))) (9 : Nat)
  let badRequest ← child "replay"
  record "bad-request" badRequest
  unless badRequest.exitCode != 0 do throw (IO.userError "changed source request was accepted")
  saveJson ((Purelib.System.FilePath.join source (System.FilePath.mk ("reading-index.json")))) (8 : Nat)
  for mode in ["generate", "replay"] do
    let output ← Purelib.System.IO.Process.output
      { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable,
          "trace-stops", directory.toString, mode] }
    record s!"stops-{mode}" output
    unless output.exitCode == 0 do
      throw (IO.userError ("stopping-reason test failed\n" ++ output.stdout ++ output.stderr))
    if mode == "replay" then
      unless occurrences output "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 0 &&
          occurrences output "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 0 do
        throw (IO.userError "inconclusive trace replay regenerated a completed proposal")
    IO.print output.stdout
  match Newton.Search.Replay.Input.checkRounded box 1 0 ⟨-1 / 3, -1 / 2⟩ ⟨-22, -32⟩ with
  | .ok _ => pure ()
  | .error _ => throw (IO.userError "negative rational rounding was rejected")
  match Newton.Search.Replay.Input.checkRounded box 1 0 ⟨-1 / 3, -1 / 2⟩ ⟨-22, -33⟩ with
  | .error (.upper true _ _ _ _) => pure ()
  | _ => throw (IO.userError "floor strict upper bound was not enforced")
  match Newton.Search.Replay.Input.checkRounded box 0 0 0 ⟨0, 0⟩ with
  | .error (.nonpositiveGrid _ _) => pure ()
  | _ => throw (IO.userError "zero grid did not return its failed positivity evidence")
  selfTest ((Purelib.System.FilePath.join directory (System.FilePath.mk ("cursor-regression"))))
  Purelib.System.IO.println
    "Root trace: two SIGKILL checkpoints, exact cold restart, two generator-free replays, and corrupt witness/request \
      rejection passed."

section Center

open Purelib.Riemann

open Purelib in
/-- The retained cubic curve used by the coefficient-center regression. -/
@[expose] def centerCurve := Riemann.Periods.PeriodCurves.cubicCurve
open Purelib.Curves.Hyperelliptic in
/-- The first standard differential on the genus-one center fixture. -/
@[expose] def centerDifferential : Differentials.Basic.Differential 1 := ⟨⟨0, by decide⟩⟩
/-- The degenerate real-coordinate ambient box for the stationary center segment. -/
@[expose] def centerAmbient : Box := ⟨2, 2, -1, 1, by decide, by decide⟩

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- The stationary clear segment at real coordinate two with certified unit clearance. -/
@[expose] def centerSegment : Geometry.ClearPath.ClearSegment centerCurve.polynomial centerAmbient
    (Components.Basic.point 2 0) (Components.Basic.point 2 0) :=
  .horizontal 2 2 0 (by decide) (by decide) (by decide) (by decide)
    { bound := 1, positive := by decide
      lower := by
        intro x lower upper
        have same : x = 2 := le_antisymm upper lower
        subst x
        decide }

open Purelib.RootIsolation in
/-- Construct the original stationary prepared edge with its exact deferred source-recipe witness. -/
@[expose] def centerFixture : IO {edge : PreparedConstantModels.PreparedEdge centerCurve centerDifferential //
    SquareRoot.Replay.QuadraticSampleReplay.Recipe.Matches .deferred (edge.directQueryOwner 0 edge.baseInside)} := do
  let left : PreparedSheetContinuation.Endpoint := ⟨0, by decide⟩
  let request : PreparedSheetContinuation.StepRequest := ⟨⟨1, by decide⟩, 4, by decide⟩
  let box : Box := ⟨2, 3, -1 / 2, 1 / 2, by decide, by decide⟩
  let supplied ← checkedOwner (centerCurve.polynomial.eval (centerSegment.pointAt left.parameter)) box box
  let owner := SquareRoot.Clearance.ExactQuadraticOwnerClearance.ownerOfState supplied.parameterNonzero
    supplied.track.initial
  let ready := SquareRoot.Replay.PreparedSourceReplay.Readiness.capture centerSegment left request owner
    (SquareRoot.Replay.PreparedSourceReplay.Inputs.capture centerSegment request.rootDiameter)
  if prepared : ready.Ready then
    if small : ClearSheetContinuation.variationBound centerSegment left.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound then
      let same := PreparedSheetContinuation.prepared_eq_self_of_ready centerSegment left owner request
        (ready.ready_iff.mp prepared) small
      let edge : PreparedConstantModels.PreparedEdge centerCurve centerDifferential :=
        { ambient := centerAmbient, start := _, finish := _, segment := centerSegment
          within := by change (-1 : SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Coordinate)
            ≤ 0 ∧ 0 ≤ 1; constructor <;> decide
          left := left, owner := owner, request := request, cached := ⟨owner, same.symm⟩
          ordered := by decide, small := by rw [same]; exact small, sheet := 0 }
      return ⟨edge, SquareRoot.Replay.QuadraticSampleReplay.matches_baseQuery edge .deferred
        (SquareRoot.Replay.QuadraticSampleReplay.matches_ownerOfState _ _)⟩
    else throw (IO.userError "stationary center fixture unexpectedly moves")
  else throw (IO.userError
    s!"center fixture not ready: diameter={fractionText ready.diameter}, predicted={fractionText ready.predicted}, \
      clearance={fractionText ready.clearance}")

/-- Compute the original canonical coefficient center with a calibrated generation marker. -/
@[expose, noinline] def canonicalCenter
    (edge : PreparedConstantModels.PreparedEdge centerCurve centerDifferential) :=
  dbg_trace "CENTER_ORIGINAL_GENERATOR_FORCED"
  PreparedConstantModels.PreparedEdge.CenterState.canonical edge

/-- Read the original center's source index, cached denominator and exact coefficient value. -/
@[expose] def centerData {edge : PreparedConstantModels.PreparedEdge centerCurve centerDifferential}
    (center : PreparedConstantModels.PreparedEdge.CenterState edge) :=
  ((show Nat from center.state.2.source), gaussianData center.cachedDenominator.get, gaussianData center.value)

section
open Purelib.RootIsolation
/-- Restore a coefficient center with equality to its complete original state and cached quotient. -/
@[expose] def centerChild (directory : System.FilePath) (mode : String) : IO Unit := do
  let fixture ← centerFixture
  let edge := fixture.val
  if mode == "calibrate" then
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical-center.json")))) (centerData
      (canonicalCenter edge))
    return
  let counterAction : RootRefinementCheckpoint.Execution Unit := do
    let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
      (if mode == "crash" then some 1 else none)
    let result ← CenterCheckpoint.run edge
      (SquareRoot.Replay.QuadraticTrackReplay.ofRecipe _ .deferred fixture.property)
      (pure (SquareRoot.Replay.QuadraticFallbackReplay.Plan.ofDeferred _ fixture.property)) control
        ((Purelib.System.FilePath.join directory (System.FilePath.mk ("center"))))
    match result with
    | .error failure =>
        saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("center-failure.json")))) (failure.report
          edge)
        throw (IO.userError "checked center restoration rejected the fixture or saved evidence")
    | .ok result =>
        have same : result.val = canonicalCenter edge := result.property
        let linked : {center // center = canonicalCenter edge} := ⟨result.val, same⟩
        let expected : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
          ("canonical-center.json"))))
        unless toJson (centerData linked.val) == expected do
          throw (IO.userError "restored center differs from the complete original coefficient/state")
        saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"center-counts-{mode}.json")))) (←
          RootRefinementCheckpoint.Execution.counts)
        Purelib.System.IO.println
          "Complete original center restored with source equality; no original coefficient generator."
  let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult

/-- Check interrupted center restoration, generator-free replay and rejection of a corrupted quotient. -/
@[expose] def centerSelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "center self-test requires a fresh directory")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let child := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "45s", executable,
        "center-child", directory.toString, mode] }
  let occurrences := fun (output : IO.Process.Output) marker =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) marker)).length - 1
  let record := fun mode (output : IO.Process.Output) =>
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"center-{mode}-result.json"))))
      (output.exitCode.toNat, output.stdout, output.stderr)
  let calibration ← child "calibrate"
  record "calibrate" calibration
  unless calibration.exitCode == 0 && occurrences calibration "CENTER_ORIGINAL_GENERATOR_FORCED" == 1 do
    throw (IO.userError ("center marker calibration failed\n" ++ calibration.stdout ++ calibration.stderr))
  let crash ← child "crash"
  record "crash" crash
  unless crash.exitCode != 0 && occurrences crash "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 1 &&
      occurrences crash "CENTER_ORIGINAL_GENERATOR_FORCED" == 0 do
    throw (IO.userError ("center interruption guard failed\n" ++ crash.stdout ++ crash.stderr))
  for mode in ["resume", "replay"] do
    let output ← child mode
    record mode output
    unless output.exitCode == 0 && occurrences output "CENTER_ORIGINAL_GENERATOR_FORCED" == 0 do
      throw (IO.userError ("center restart failed\n" ++ output.stdout ++ output.stderr))
    let counts : RootRefinementCheckpoint.Counts ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"center-counts-{mode}.json"))))
    unless counts.reusedRounding > 0 do throw (IO.userError "center restart reused no completed proposal")
    if mode == "replay" then
      unless counts.generatedRounding == 0 && counts.generatedNewton == 0 &&
          occurrences output "CENTER_QUOTIENT_GENERATOR_FORCED" == 0 do
        throw (IO.userError "cold center replay regenerated a completed sample or quotient")
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("center/coefficient.json")))
  let saved : GaussianData ← loadJson path
  saveJson path (gaussianData (0 : SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Gaussian))
  let corrupt ← child "replay"
  record "corrupt-quotient" corrupt
  unless corrupt.exitCode != 0 && (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("center-failure.json")))).pathExists) do
    throw (IO.userError "corrupt coefficient was accepted")
  saveJson path saved
  Purelib.System.IO.println
    "Center checkpoint: SIGKILL restart, exact original coefficient/state, cold generator-free replay and corrupt \
      quotient rejection passed."

end

open Purelib.RootIsolation.SquareRoot.Replay in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Supply the original two-bank stationary bridge with readiness for its retained accelerated tracks.

Keep the inherited total fallback and exact supplied owners rather than replacing their construction histories. -/
@[expose] def withCycleFixture
    (use : (data : PreparedCycleModels.PreparedCycleData centerCurve) →
      Integration.Surface.PreparedCycleReplay.Readiness.CycleReady centerCurve data → IO Unit) : IO Unit := do
  let box : Box := ⟨2, 3, -1 / 2, 1 / 2, by decide, by decide⟩
  let supplied ← checkedOwner (centerCurve.polynomial.eval (Components.Basic.point 2 0)) box box
  -- Accelerate the actual supplied track: its inherited total fallback is
  -- deliberately retained, rather than replaced with the ofState recipe.
  let owner : SquareRootContinuationChain.Owner (centerCurve.polynomial.eval (Components.Basic.point 2 0)) :=
    ⟨supplied.parameterNonzero, supplied.ambient, SquareRoot.Clearance.QuadraticLineClearance.Owner.accelerateTrack _
      supplied.track⟩
  let path : Purelib.Polynomial.Geometry.ClearPath centerCurve.polynomial centerAmbient
      (Components.Basic.point 2 0) (Components.Basic.point 2 0) :=
    .cons centerSegment (.cons centerSegment (.nil _))
  have inside : centerSegment.WithinAmbient := by
    change (-1 : SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Coordinate) ≤ 0 ∧ 0 ≤ 1
    constructor <;> decide
  let data := PreparedCycleModels.PreparedCycleData.bridge
    (PreparedCycleModels.PreparedDoublePath.total path
      (.cons inside (.cons inside (.nil _))) owner owner 4 (by decide))
  use data ⟨QuadraticTrackReplay.accelerated _, SquareRoot.Replay.QuadraticTrackReplay.accelerated _⟩

/-- Construct the original compact centered cycle with a calibrated generation marker. -/
@[expose, noinline] def canonicalCycle (data : PreparedCycleModels.PreparedCycleData centerCurve) :=
  dbg_trace "CYCLE_ORIGINAL_GENERATOR_FORCED"
  PreparedSwitchedRefinements.compactCycleState centerCurve centerDifferential data

/-- Serialize the ordered cycle parents, cached centers and original aggregate allowance. -/
@[expose] def cycleSnapshot
    (state : PreparedSwitchedRefinements.DirectSwitchedState centerCurve centerDifferential) : Json :=
  Json.mkObj
    [("parents", toJson (state.parents.map fun parent =>
      (parent.edge.sheet.val, CenterCheckpoint.capture parent.edge,
        (show Nat from parent.center.state.2.source),
        gaussianData parent.center.cachedDenominator.get, gaussianData parent.center.value))),
     ("allowance", toJson (fractionData (state.initialAllowanceBound centerDifferential)))]

open Purelib.Approximation in
/-- Read each retained child center directly from the original root-chain spine. -/
@[expose] def rootCenters
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge centerCurve centerDifferential)}
    {first last : Gaussian.Name.Basic.Named}
    (roots : PreparedRefinementRootChains.RootChain parents first last) :
    List (Nat × GaussianData × GaussianData) :=
  PreparedRefinementRootChains.RootChain.casesOn
    (motive := fun _ _ _ _ => List (Nat × GaussianData × GaussianData)) roots
    (fun {_ _} _ => [])
    (fun child {_ _ _} _ tail => centerData child.center :: rootCenters tail)
termination_by structural roots

/-- Read the original forward and backward bank-root centers with a calibrated generation marker. -/
@[expose, noinline] def canonicalRootCenters
    (data : PreparedCycleModels.PreparedDoublePath centerCurve) :=
  dbg_trace "CYCLE_ROOT_ORIGINAL_GENERATOR_FORCED"
  rootCenters (PreparedBankRootChains.dyadicBankRootChain centerCurve centerDifferential 0 data.forwardChecked) ++
    rootCenters (PreparedBankRootChains.dyadicBankRootChain centerCurve centerDifferential 1 data.backwardChecked)

open Purelib in
/-- Restore the original bank-root center lists using exact retained parent-list equations.

Split the restored parents at the original forward step count and preserve both bank identities. -/
@[expose] def restoredRootCenters
    (data : PreparedCycleModels.PreparedDoublePath centerCurve)
    (state : PreparedSwitchedRefinements.DirectSwitchedState centerCurve centerDifferential)
    (equal : state = PreparedSwitchedRefinements.compactCycleState centerCurve centerDifferential (.bridge data)) :
    List (Nat × GaussianData × GaussianData) :=
  let count := data.forwardChecked.prepared.stepCount
  have parentsEqual := (congrArg (fun state => state.parents) equal).trans
    (PreparedSwitchedRefinements.bridgeState_parents centerCurve centerDifferential data)
  have lengthEqual :=
    (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
      centerCurve centerDifferential 0 data.forwardChecked).trans data.forwardChecked.prepared_stepCount.symm
  have forwardEqual : state.parents.take count =
      (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
        centerCurve centerDifferential 0 data.forwardChecked).parents := by
    rw [parentsEqual]
    exact List.take_left' lengthEqual
  have backwardEqual : state.parents.drop count =
      (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
        centerCurve centerDifferential 1 data.backwardChecked).parents := by
    rw [parentsEqual]
    exact List.drop_left' lengthEqual
  let forward := Riemann.RootContinuation.PreparedInitialRootReplay.bankRoots
    centerCurve centerDifferential 0 data.forwardChecked
    (state.parents.take count) forwardEqual
  let backward := Riemann.RootContinuation.PreparedInitialRootReplay.bankRoots
    centerCurve centerDifferential 1 data.backwardChecked
    (state.parents.drop count) backwardEqual
  rootCenters forward ++ rootCenters backward

/-- Restore the complete four-parent cycle and its original bank-root chains from saved centers.

Check all center readbacks and the cached source allowance while retaining the full canonical-state equation. -/
@[expose] def cycleChild (directory : System.FilePath) (mode : String) : IO Unit :=
  withCycleFixture fun data ready => do
    if mode == "calibrate" then
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical-cycle.json")))) (cycleSnapshot
        (canonicalCycle data))
      match data with
      | .bridge bridge => saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("canonical-cycle-roots.json")))) (canonicalRootCenters bridge)
      | .finiteCut _ => throw (IO.userError "cycle restart fixture expected its two-bank bridge")
      return
    let counterAction : RootRefinementCheckpoint.Execution Unit := do
      let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
        (if mode == "crash" then some 1 else none)
      PreparedCenterCheckpoint.withCycle centerCurve centerDifferential data ready control
        ((Purelib.System.FilePath.join directory (System.FilePath.mk ("cycle")))) fun cached => do
          have original : cached.restore = canonicalCycle data := cached.restore_eq
          let restored := cached.restore
          have retained : restored = canonicalCycle data := original
          let checked : {state // state = canonicalCycle data} := ⟨restored, retained⟩
          let expected : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
            ("canonical-cycle.json"))))
          unless cycleSnapshot checked.val == expected do
            throw (IO.userError "assembled cycle differs from original centres, cursors or allowance")
          unless checked.val.parents.length == 4 do
            throw (IO.userError "cycle fixture lost a prepared segment or bank")
          match observed : data with
          | .bridge bridge =>
              let expectedRoots : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
                ("canonical-cycle-roots.json"))))
              let roots := restoredRootCenters bridge checked.val
                (checked.property.trans (congrArg canonicalCycle observed))
              unless toJson roots == expectedRoots && roots.length == 4 do
                throw (IO.userError "saved-centre root assembly differs from the original bank chains")
          | .finiteCut _ => throw (IO.userError "cycle restart fixture expected its two-bank bridge")
          saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"cycle-counts-{mode}.json")))) (←
            RootRefinementCheckpoint.Execution.counts)
          Purelib.System.IO.println
            "Complete four-parent cycle, original bank root chains and allowance restored with source equality."
    let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
    (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult

open Purelib.RootIsolation in
/-- Check cycle interruption recovery, original root-chain identity and generator-free cold center reuse. -/
@[expose] def cycleSelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "cycle self-test requires a fresh directory")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let child := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "60s", executable,
        "cycle-child", directory.toString, mode] }
  let occurrences := fun (output : IO.Process.Output) marker =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) marker)).length - 1
  let record := fun mode (output : IO.Process.Output) =>
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"cycle-{mode}-result.json"))))
      (output.exitCode.toNat, output.stdout, output.stderr)
  let calibration ← child "calibrate"
  record "calibrate" calibration
  unless calibration.exitCode == 0 && occurrences calibration "CYCLE_ORIGINAL_GENERATOR_FORCED" == 1 &&
      occurrences calibration "CYCLE_ROOT_ORIGINAL_GENERATOR_FORCED" == 1 do
    throw (IO.userError ("cycle calibration failed\n" ++ calibration.stdout ++ calibration.stderr))
  let crash ← child "crash"
  record "crash" crash
  unless crash.exitCode != 0 && occurrences crash "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 1 &&
      occurrences crash "CYCLE_ORIGINAL_GENERATOR_FORCED" == 0 do
    throw (IO.userError ("cycle interruption guard failed\n" ++ crash.stdout ++ crash.stderr))
  for mode in ["resume", "replay"] do
    let output ← child mode
    record mode output
    unless output.exitCode == 0 && occurrences output "CYCLE_ORIGINAL_GENERATOR_FORCED" == 0 &&
        occurrences output "CYCLE_ROOT_ORIGINAL_GENERATOR_FORCED" == 0 do
      throw (IO.userError ("cycle restart failed\n" ++ output.stdout ++ output.stderr))
    let counts : RootRefinementCheckpoint.Counts ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"cycle-counts-{mode}.json"))))
    unless counts.reusedRounding > 0 do throw (IO.userError "cycle restart reused no completed proposal")
    if mode == "replay" then
      unless counts.generatedRounding == 0 && counts.generatedNewton == 0 &&
          occurrences output "CENTER_QUOTIENT_GENERATOR_FORCED" == 0 do
        throw (IO.userError "cold cycle replay regenerated a completed centre")
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("cycle/source-allowance.json")))
  let saved : FractionData ← loadJson path
  saveJson path (fractionData (-1 :
    SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Coordinate))
  let corrupt ← child "replay"
  record "corrupt-allowance" corrupt
  unless corrupt.exitCode != 0 && (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("cycle/invalid-allowance.json")))).pathExists) do
    throw (IO.userError "corrupt cycle allowance was accepted")
  saveJson path saved
  Purelib.System.IO.println
    "Cycle checkpoint: SIGKILL restart, original inherited refiner, four parents and original bank root chains, exact \
      allowance and generator-free cold replay passed."

/-- Serialize the original refinement selection, allowance and ordered retained child centers. -/
@[expose] def refinementSnapshot
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge centerCurve centerDifferential)}
    (accuracy : PreparedRootSafeAccuracy.RootSafeAccuracy parents [centerDifferential] 1) : Json :=
  Json.mkObj
    [("depth", toJson accuracy.result.depth),
     ("diameter", toJson (fractionData accuracy.result.rootDiameter)),
     ("allowance", toJson (fractionData (accuracy.result.allowanceFor centerDifferential))),
     ("children", toJson (accuracy.blocks.children.map fun child =>
       (child.edge.sheet.val, CenterCheckpoint.capture child.edge, centerData child.center)))]

/-- Acquire the original root-safe finite refinement with a calibrated generation marker. -/
@[expose, noinline] def originalRefinement
    (state : PreparedSwitchedRefinements.DirectSwitchedState centerCurve centerDifferential) :=
  dbg_trace "REFINEMENT_ORIGINAL_GENERATOR_FORCED"
  PreparedRootSafeAccuracy.RootSafeAccuracy.acquire state.parents state.proper
    [centerDifferential] 1 (by decide)

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.RootIsolation in
/-- Restore the original root-safe selection and all selected child centers with complete accuracy equality. -/
@[expose] def refinementChild (directory : System.FilePath) (mode : String) : IO Unit :=
  withCycleFixture fun data ready => do
    let counterAction : RootRefinementCheckpoint.Execution Unit := do
      let parentControl ← RootRefinementCheckpoint.Control.create (mode != "calibrate")
      PreparedCenterCheckpoint.withCycle centerCurve centerDifferential data ready parentControl
        ((Purelib.System.FilePath.join directory (System.FilePath.mk ("parents")))) fun cached => do
          let state := cached.restore
          let parentsReady := Integration.Surface.PreparedCycleReplay.Readiness.restored centerCurve centerDifferential
            ready cached
          if mode == "calibrate" then
            saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical-refinement.json"))))
              (refinementSnapshot (originalRefinement state))
            return
          let counterAction : RootRefinementCheckpoint.Execution Unit := do
            let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
              (if mode == "crash" then some 1 else none)
            have targetPositive : (0 :
              SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Coordinate) < 1 := by decide
            PreparedRefinementCheckpoint.withSelected state.parents state.proper [centerDifferential]
              1 targetPositive control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("refinement"))))
                fun result => do
                match result with
                | .error _ => throw (IO.userError "finite refinement fixture selection did not complete")
                | .ok selected =>
                    PreparedRefinementCheckpoint.withBankCenters control ((Purelib.System.FilePath.join directory
                      (System.FilePath.mk ("refinement/centers"))))
                      selected.val.meshes parentsReady
                      (Riemann.Transport.PreparedDeferredRecipeReplay.Histories.inherited state.parents) 0
                      fun (result : Except (PreparedRefinementCheckpoint.PendingBankCenters selected.val.meshes)
                        (Riemann.Transport.PreparedDirectRefinementReplay.BankCenters selected.val.meshes)) => do
                        match result with
                        | .error _ => throw (IO.userError "finite refinement fixture centers did not complete")
                        | .ok centers =>
                            let accuracy := PreparedRootSafeReplay.fromCenters state.parents state.proper
                              [centerDifferential] 1 targetPositive selected.val selected.property centers
                            have equal : accuracy = originalRefinement state :=
                              PreparedRootSafeReplay.fromCenters_eq state.parents state.proper
                                [centerDifferential] 1 targetPositive selected.val selected.property centers
                            let checked : {value // value = originalRefinement state} := ⟨accuracy, equal⟩
                            let expected : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
                              ("canonical-refinement.json"))))
                            unless refinementSnapshot checked.val == expected do
                              throw (IO.userError
                                "restored refinement differs from the original selection, allowance or centers")
                            saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
                              (s!"refinement-counts-{mode}.json")))) (← RootRefinementCheckpoint.Execution.counts)
                            Purelib.System.IO.println
                              "Original finite refinement selection, allowance and child centers restored with source \
                                equality."
          let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
          (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult
    let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
    (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult

/-- Check refinement interruption recovery, exact original child blocks and generator-free cold replay. -/
@[expose] def refinementSelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "refinement self-test requires a fresh directory")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let child := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "90s", executable,
        "refinement-child", directory.toString, mode] }
  let occurrences := fun (output : IO.Process.Output) marker =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) marker)).length - 1
  let record := fun mode (output : IO.Process.Output) =>
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"refinement-{mode}-result.json"))))
      (output.exitCode.toNat, output.stdout, output.stderr)
  let calibration ← child "calibrate"
  record "calibrate" calibration
  unless calibration.exitCode == 0 && occurrences calibration "REFINEMENT_ORIGINAL_GENERATOR_FORCED" == 1 do
    throw (IO.userError ("refinement marker calibration failed\n" ++ calibration.stdout ++ calibration.stderr))
  let crash ← child "crash"
  record "crash" crash
  unless crash.exitCode != 0 &&
      occurrences crash "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" + occurrences crash "ROOT_TRACE_NEWTON_GENERATOR_FORCED"
        == 1 &&
      occurrences crash "REFINEMENT_ORIGINAL_GENERATOR_FORCED" == 0 do
    throw (IO.userError ("refinement interruption guard failed\n" ++ crash.stdout ++ crash.stderr))
  for mode in ["resume", "replay"] do
    let output ← child mode
    record mode output
    unless output.exitCode == 0 && occurrences output "REFINEMENT_ORIGINAL_GENERATOR_FORCED" == 0 do
      throw (IO.userError ("refinement restart failed\n" ++ output.stdout ++ output.stderr))
    let counts : RootRefinementCheckpoint.Counts ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"refinement-counts-{mode}.json"))))
    unless counts.reusedRounding + counts.reusedNewton > 0 do
      throw (IO.userError "refinement restart reused no completed root proposal")
    if mode == "replay" then
      unless counts.generatedRounding == 0 && counts.generatedNewton == 0 &&
          occurrences output "CENTER_QUOTIENT_GENERATOR_FORCED" == 0 do
        throw (IO.userError "cold refinement replay regenerated a completed root or center")
  Purelib.System.IO.println
    "Refinement checkpoint: SIGKILL restart, exact original selection and child blocks, generator-free cold replay \
      passed."

/-- Serialize a source-only state's exact endpoints, allowance and ordered child centers. -/
@[expose] def sourceStateSnapshot
    (state : PreparedSwitchedRefinements.DirectSwitchedState centerCurve centerDifferential) : Json :=
  Json.mkObj
    [("start", toJson (gaussianData state.start.coordinate)),
     ("finish", toJson (gaussianData state.finish.coordinate)),
     ("allowance", toJson (fractionData (state.initialAllowanceBound centerDifferential))),
     ("children", toJson (state.parents.map fun child =>
       (child.edge.sheet.val, CenterCheckpoint.capture child.edge, centerData child.center)))]

/-- Compute the original source-only refinement successor with a calibrated generation marker. -/
@[expose, noinline] def originalSourceStep
    (state : PreparedSwitchedRefinements.DirectSwitchedState centerCurve centerDifferential) :=
  dbg_trace "SOURCE_STEP_ORIGINAL_GENERATOR_FORCED"
  state.refineSource (PreparedDirectDyadicRefinements.accurateDirectRefinement state.parents state.proper 1 (by decide))

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.RootIsolation in
/-- Restore the exact original source-only successor from retained parents and checked child checkpoints.

Keep the complete successor equation and readiness, or save the typed unresolved attempt. -/
@[expose] def sourceRefinementChild (directory parents : System.FilePath) (mode : String) : IO Unit :=
  withCycleFixture fun data ready => do
    let counterAction : RootRefinementCheckpoint.Execution Unit := do
      let parentControl ← RootRefinementCheckpoint.Control.create true
      PreparedCenterCheckpoint.withCycle centerCurve centerDifferential data ready parentControl parents fun cached =>
        do
        let state := cached.restore
        let parentsReady := Integration.Surface.PreparedCycleReplay.Readiness.restored centerCurve centerDifferential
          ready cached
        if mode == "calibrate" then
          saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical-source-state.json"))))
            (sourceStateSnapshot (originalSourceStep state))
          return
        let counterAction : RootRefinementCheckpoint.Execution Unit := do
          let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
            (if mode == "crash" then some 1 else none)
          have targetPositive : (0 :
            SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Coordinate) < 1 := by decide
          PreparedRefinementCheckpoint.Source.withStep state parentsReady
            (Riemann.Transport.PreparedDeferredRecipeReplay.Histories.inherited state.parents) 1 targetPositive control
              ((Purelib.System.FilePath.join directory (System.FilePath.mk ("source-step")))) fun (result : Except
                (PreparedRefinementCheckpoint.Source.PendingStep state 1 targetPositive)
                (Integration.Preparation.Replay.PreparedSourceRefinementReplay.Restoration.RestoredStep state 1
                  targetPositive)) => do
            match result with
            | .error pending =>
                saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("inconclusive.json"))))
                  pending.report
                throw (IO.userError "original source-only step unresolved; typed attempt retained")
            | .ok restored =>
                have same : restored.value = originalSourceStep state := restored.equal
                let checked : {value // value = originalSourceStep state} := ⟨restored.value, same⟩
                let expected : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
                  ("canonical-source-state.json"))))
                unless sourceStateSnapshot checked.val == expected do
                  throw (IO.userError "restored source step differs from original child state")
                saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"source-counts-{mode}.json"))))
                  (← RootRefinementCheckpoint.Execution.counts)
                Purelib.System.IO.println
                  "Original source-only successor restored with complete state equation and parent readiness."
        let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
        (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult
    let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
    (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult

/-- Check interrupted source-only refinement, complete successor identity and generator-free cold replay. -/
@[expose] def sourceRefinementSelfTest (directory parents : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "source refinement regression requires a fresh output directory")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let child := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "90s", executable,
        "source-refinement-child", directory.toString, parents.toString, mode] }
  let occurrences := fun (output : IO.Process.Output) marker =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) marker)).length - 1
  let record := fun mode (output : IO.Process.Output) =>
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"source-{mode}-result.json"))))
      (output.exitCode.toNat, output.stdout, output.stderr)
  let calibration ← child "calibrate"
  record "calibrate" calibration
  unless calibration.exitCode == 0 && occurrences calibration "SOURCE_STEP_ORIGINAL_GENERATOR_FORCED" == 1 do
    throw (IO.userError ("source step marker calibration failed\n" ++ calibration.stdout ++ calibration.stderr))
  let crash ← child "crash"
  record "crash" crash
  unless crash.exitCode != 0 &&
      occurrences crash "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" + occurrences crash "ROOT_TRACE_NEWTON_GENERATOR_FORCED"
        == 1 &&
      occurrences crash "SOURCE_STEP_ORIGINAL_GENERATOR_FORCED" == 0 do
    throw (IO.userError ("source step interruption guard failed\n" ++ crash.stdout ++ crash.stderr))
  for mode in ["resume", "replay"] do
    let output ← child mode
    record mode output
    unless output.exitCode == 0 && occurrences output "SOURCE_STEP_ORIGINAL_GENERATOR_FORCED" == 0 do
      throw (IO.userError ("source step restart failed\n" ++ output.stdout ++ output.stderr))
    let counts : RootRefinementCheckpoint.Counts ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"source-counts-{mode}.json"))))
    unless counts.reusedRounding + counts.reusedNewton > 0 do
      throw (IO.userError "source step restart reused no saved proposal")
    if mode == "replay" then
      unless counts.generatedRounding == 0 && counts.generatedNewton == 0 &&
          occurrences output "CENTER_QUOTIENT_GENERATOR_FORCED" == 0 do
        throw (IO.userError "cold source step replay regenerated a completed root or centre")
  Purelib.System.IO.println
    "Source-only refinement: interrupted restart, original successor equation and generator-free cold replay passed."

end Center

section
open Purelib.Polynomial
open Purelib.RootIsolation
/-- Compute the four original elimination-based line bounds with a calibrated generation marker. -/
@[expose, noinline] def originalClearanceBounds : IO (List FractionData) := do
  dbg_trace "CLEARANCE_ORIGINAL_GENERATOR_FORCED"
  let polynomial : Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial := ⟨[1, 0, -2]⟩
  let source : Purelib.RootIsolation.FTA.Squarefree.Input polynomial :=
    Power.Isolation.isolationInput (show (2 :
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Gaussian) ≠ 0 by decide)
      ⟨2, by decide⟩ (by decide)
  let ambient : Box := ⟨-2, 2, -2, 2, by decide, by decide⟩
  let clearances := Clearance.Box.Line.Elimination.Provider.AxisClearances.canonical source.elimination
  let mut result := []
  for x in ([1 / 2, 2] : List SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Coordinate) do
    if safe : source.elimination.vertical.eval x ≠ 0 then
      result := result ++ [fractionData (clearances.vertical ambient x safe).bound]
    else throw (IO.userError "clearance fixture vertical side is not eliminant-safe")
  for y in ([-1 / 2, 1 / 2] : List SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Coordinate)
    do
    if safe : source.elimination.horizontal.eval y ≠ 0 then
      result := result ++ [fractionData (clearances.horizontal ambient y safe).bound]
    else throw (IO.userError "clearance fixture horizontal side is not eliminant-safe")
  return result

/-- Restore all four original line-clearance bounds from checked separated-Sylvester columns. -/
@[expose] def clearanceChild (directory : System.FilePath) (mode : String) : IO Unit := do
  IO.FS.createDirAll directory
  if mode == "calibrate" then
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("original-bounds.json")))) (←
      originalClearanceBounds)
    return
  let polynomial : Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial := ⟨[1, 0, -2]⟩
  let source : Purelib.RootIsolation.FTA.Squarefree.Input polynomial :=
    Power.Isolation.isolationInput (show (2 :
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Gaussian) ≠ 0 by decide)
      ⟨2, by decide⟩ (by decide)
  let ambient : Box := ⟨-2, 2, -2, 2, by decide, by decide⟩
  let control : ClearanceCheckpoint.Control :=
    { savedOnly := mode == "replay"
      afterSave := do
        if mode == "crash" then
          (← IO.getStdout).flush
          let pid ← IO.Process.getPID
          discard <| Purelib.System.IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
          throw (IO.userError "clearance interruption unexpectedly returned") }
  let loader := RootRefinementCheckpoint.ClearanceLoader.separated control polynomial source.nonzero
    source.degreePositive
  let mut result := []
  for (name, x) in ([ ("left", 1 / 2), ("right", 2)] : List (String ×
    SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Coordinate)) do
    if safe : source.elimination.vertical.eval x ≠ 0 then
      let line ← loader.vertical ((Purelib.System.FilePath.join directory (System.FilePath.mk (name)))) ambient x safe
      result := result ++ [fractionData line.val.bound]
    else throw (IO.userError "clearance fixture vertical side is not eliminant-safe")
  for (name, y) in ([ ("bottom", -1 / 2), ("top", 1 / 2)] : List (String ×
    SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Coordinate)) do
    if safe : source.elimination.horizontal.eval y ≠ 0 then
      let line ← loader.horizontal ((Purelib.System.FilePath.join directory (System.FilePath.mk (name)))) ambient y safe
      result := result ++ [fractionData line.val.bound]
    else throw (IO.userError "clearance fixture horizontal side is not eliminant-safe")
  let expected : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("original-bounds.json"))))
  unless toJson result == expected do
    throw (IO.userError "restored clearance bounds differ from the original symbolic constructor")
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("restored-bounds.json")))) result
  Purelib.System.IO.println "Four original vertical/horizontal clearance bounds restored."

end

/-- Check clearance-column interruption recovery and exact original bound equality.

Reject altered equations, source polynomials, parameters and dimensions; retain missing-stage requests without
regeneration. -/
@[expose] def clearanceSelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "clearance self-test requires a fresh directory")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let child := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable,
        "clearance-child", directory.toString, mode] }
  let occurrences := fun (output : IO.Process.Output) marker =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) marker)).length - 1
  let record := fun mode (output : IO.Process.Output) => do
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{mode}-result.json"))))
      (output.exitCode.toNat, output.stdout, output.stderr)
  let reference ← child "calibrate"
  record "reference" reference
  unless reference.exitCode == 0 && occurrences reference "CLEARANCE_ORIGINAL_GENERATOR_FORCED" == 1 do
    throw (IO.userError ("original clearance calibration failed\n" ++ reference.stdout ++ reference.stderr))
  let crash ← child "crash"
  record "crash" crash
  unless crash.exitCode != 0 && occurrences crash "CLEARANCE_COLUMN_GENERATOR_FORCED" == 1 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk ("left/column.json")))).pathExists) do
    throw (IO.userError ("clearance interruption failed\n" ++ crash.stdout ++ crash.stderr))
  let resumed ← child "resume"
  record "resume" resumed
  unless resumed.exitCode == 0 && occurrences resumed "CLEARANCE_COLUMN_GENERATOR_FORCED" == 3 &&
      occurrences resumed "REUSED original clearance column" == 1 &&
      occurrences resumed "CLEARANCE_ORIGINAL_GENERATOR_FORCED" == 0 do
    throw (IO.userError ("clearance restart regenerated or changed the source\n" ++ resumed.stdout ++ resumed.stderr))
  for index in [:2] do
    let replay ← child "replay"
    record s!"replay-{index}" replay
    unless replay.exitCode == 0 && occurrences replay "CLEARANCE_COLUMN_GENERATOR_FORCED" == 0 &&
        occurrences replay "CLEARANCE_ORIGINAL_GENERATOR_FORCED" == 0 &&
        occurrences replay "REUSED original clearance column" == 4 do
      throw (IO.userError ("cold clearance replay failed\n" ++ replay.stdout ++ replay.stderr))
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("left/column.json")))
  let saved : ClearanceCheckpoint.RawColumn ← loadJson path
  for (name, corrupt) in
      [("equation", { saved with values := saved.values.map fun _ => gaussianData 0 }),
       ("source", { saved with polynomial := [gaussianData 42] }),
       ("parameter", { saved with parameter := fractionData 0 }),
       ("dimension", { saved with values := [] })] do
    saveJson path corrupt
    let rejected ← child "replay"
    record s!"corrupt-{name}" rejected
    unless rejected.exitCode != 0 && occurrences rejected "CLEARANCE_COLUMN_GENERATOR_FORCED" == 0 &&
        (← ((Purelib.System.FilePath.join directory (System.FilePath.mk ("left/invalid.json")))).pathExists) do
      throw (IO.userError s!"corrupt clearance {name} was accepted or regenerated")
  IO.FS.removeFile path
  let missing ← child "replay"
  record "missing" missing
  unless missing.exitCode != 0 && occurrences missing "CLEARANCE_COLUMN_GENERATOR_FORCED" == 0 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk ("left/missing.json")))).pathExists) do
    throw (IO.userError "missing clearance column regenerated or lost its request")
  saveJson path saved
  Purelib.System.IO.println
    "Clearance checkpoint: original bounds, SIGKILL restart, two generator-free cold replays, invalid-witness \
      rejection and missing-stage retention passed."

open Purelib.Polynomial in
/-- A cubic box exercises nonconstant remainders and all four orientations. The returned winding carries its equality to
the original finite algorithm. -/
@[expose] def windingChild (directory : System.FilePath) (mode : String) : IO Unit := do
  let polynomial : Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial := ⟨[1, 0, 0, 1]⟩
  let box : Box := ⟨1 / 4, 3 / 4, 3 / 4, 1, by decide, by decide⟩
  let afterSave : IO Unit := do
    if mode == "crash" then
      (← IO.getStdout).flush
      let pid ← IO.Process.getPID
      discard <| Purelib.System.IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
      throw (IO.userError "winding interruption unexpectedly returned")
  let value ← WindingCheckpoint.box ⟨mode == "replay", afterSave⟩ directory polynomial box
  unless value.val == 4 do throw (IO.userError "cubic fixture winding differs from four")
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("winding.json")))) value.val
  Purelib.System.IO.println "Original cubic box winding restored."

/-- Check the exact original cubic winding through resumable finite division chains.

Verify interruption recovery, repeated generator-free replay and rejection of altered operands, identities,
normalization or degree bounds. -/
@[expose] def windingSelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "winding self-test requires a fresh directory")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let child := fun location mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable,
        "winding-child", ((Purelib.System.FilePath.join directory (System.FilePath.mk (location)))).toString, mode] }
  let occurrences := fun (output : IO.Process.Output) marker =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) marker)).length - 1
  let record := fun mode (output : IO.Process.Output) => do
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{mode}-result.json"))))
      (output.exitCode.toNat, output.stdout, output.stderr)
  let calibration ← child "reference" "generate"
  record "reference" calibration
  let divisions := occurrences calibration "WINDING_DIVISION_GENERATOR_FORCED"
  unless calibration.exitCode == 0 && divisions > 4 do
    throw (IO.userError ("winding calibration failed\n" ++ calibration.stdout ++ calibration.stderr))
  let crash ← child "resumed" "crash"
  record "crash" crash
  unless crash.exitCode != 0 && occurrences crash "WINDING_DIVISION_GENERATOR_FORCED" == 1 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk ("resumed/bottom/division-0.json")))).pathExists)
        do
    throw (IO.userError "winding interruption did not preserve exactly the first division")
  let resume ← child "resumed" "generate"
  record "resume" resume
  unless resume.exitCode == 0 && occurrences resume "REUSED winding division" == 1 &&
      occurrences resume "WINDING_DIVISION_GENERATOR_FORCED" + 1 == divisions do
    throw (IO.userError ("restart regenerated a completed division\n" ++ resume.stdout ++ resume.stderr))
  for index in [:2] do
    let replay ← child "resumed" "replay"
    record s!"replay-{index}" replay
    unless replay.exitCode == 0 && occurrences replay "WINDING_DIVISION_GENERATOR_FORCED" == 0 &&
        occurrences replay "REUSED winding division" == divisions do
      throw (IO.userError ("cold winding replay regenerated or failed\n" ++ replay.stdout ++ replay.stderr))
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("resumed/bottom/division-0.json")))
  let saved : WindingCheckpoint.RawStep ← loadJson path
  for (label, corrupt) in
      [("identity", { saved with quotient := [fractionData 1] }),
       ("normalization", { saved with remainder := fractionData 0 :: saved.remainder }),
       ("degree", { saved with remainder := saved.divisor }),
       ("source", { saved with dividend := [fractionData 42] })] do
    saveJson path corrupt
    let rejected ← child "resumed" "replay"
    record s!"corrupt-{label}" rejected
    unless rejected.exitCode != 0 && occurrences rejected "WINDING_DIVISION_GENERATOR_FORCED" == 0 &&
        (← ((Purelib.System.FilePath.join directory (System.FilePath.mk ("resumed/bottom/invalid.json")))).pathExists)
          do
      throw (IO.userError s!"corrupt winding {label} accepted or regenerated")
    let failure : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("resumed/bottom/invalid.json"))))
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"corrupt-{label}-evidence.json")))) failure
  saveJson path saved
  IO.FS.removeFile path
  let missing ← child "resumed" "replay"
  record "missing" missing
  unless missing.exitCode != 0 && occurrences missing "WINDING_DIVISION_GENERATOR_FORCED" == 0 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk ("resumed/bottom/missing.json")))).pathExists) do
    throw (IO.userError "missing winding witness regenerated or lacked next-step evidence")
  saveJson path saved
  Purelib.System.IO.println
    s!"Winding checkpoint: {divisions} divisions, SIGKILL restart, two generator-free cold replays, \
      corrupt-source/witness rejection and missing-stage retention passed."

set_option genInjectivity false in
/-- The saved finite state, requested tolerance and completed sample index at an unresolved fallback.

The retained state, target epsilon and completed index remain separate
encodings. Their exact request relation is checked before resuming the
finite fallback procedure. -/
structure SavedFallbackInput where
  /-- The exact retained state at the completed source-track prefix. -/ state : RootStateCheckpoint.RawData
  /-- The original requested positive refinement tolerance. -/ epsilon : FractionData
  /-- The last completed sample index before the fallback attempt. -/ completedIndex : Nat
deriving Json.FromJson

constructive_injectivity SavedFallbackInput

open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance in
open Purelib in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Rebuild the same ambient-line state used by a checked Newton result. Its input winding chain is checkpointed
separately from the fallback. -/
@[expose] public def fallbackOwner (parameter :
  SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Gaussian) (ambient box :
  SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Box)
    (control : WindingCheckpoint.Control) (directory : System.FilePath) :
    IO {owner : Riemann.Topology.SquareRootContinuationChain.Owner parameter //
      Riemann.Transport.PreparedDeferredRecipeReplay.Deferred owner} := do
  if nonzero : parameter ≠ 0 then
    if proper : box.xLower < box.xUpper ∧ box.yLower < box.yUpper then
      letI : Decidable (box.Refines ambient) := by
        unfold Purelib.Geometry.Rational.Box.Refines; infer_instance
      if within : box.Refines ambient then
        if leftNonzero : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter box.xLower ≠ 0 then
          if rightNonzero : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter box.xUpper ≠ 0
            then
            if bottomNonzero : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter box.yLower
              ≠ 0 then
              if topNonzero : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter box.yUpper ≠
                0 then do
                let winding ← WindingCheckpoint.box control directory (rootPolynomial parameter) box
                if four : winding.val = 4 then
                  let left :=
                    SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearance
                    parameter ambient box.xLower leftNonzero
                  let right :=
                    SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearance
                    parameter ambient box.xUpper rightNonzero
                  let bottom :=
                    SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearance
                    parameter ambient box.yLower bottomNonzero
                  let top :=
                    SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearance
                    parameter ambient box.yUpper topNonzero
                  let state : SquareRoot.Replay.QuadraticSampleReplay.State parameter ambient :=
                    ⟨box, within, proper,
                      Clearance.Box.Boundary.Lines.boundaryOfLines (left.restrict within) (right.restrict within)
                        (bottom.restrict within) (top.restrict within),
                      winding.property.symm.trans four, left, right, bottom, top⟩
                  return ⟨ownerOfState nonzero state,
                    SquareRoot.Replay.QuadraticSampleReplay.matches_ownerOfState nonzero state⟩
                else throw (IO.userError "fallback fixture input winding differs from four")
              else throw (IO.userError "fallback fixture top determinant is zero")
            else throw (IO.userError "fallback fixture bottom determinant is zero")
          else throw (IO.userError "fallback fixture right determinant is zero")
        else throw (IO.userError "fallback fixture left determinant is zero")
      else throw (IO.userError "fallback fixture lies outside its saved ambient")
    else throw (IO.userError "fallback fixture box is not proper")
  else throw (IO.userError "fallback fixture parameter is zero")

open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance in
open Purelib in
open Purelib.Polynomial in
open Purelib.RootIsolation in
open Purelib in
open Purelib.RootIsolation in
/-- Run the retained owner's original refiner at the requested positive tolerance with a calibrated marker. -/
@[expose, noinline] public def originalFallback {parameter :
  SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Gaussian}
    (owner : Riemann.Topology.SquareRootContinuationChain.Owner parameter)
    (epsilon : SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Coordinate) (positive : 0 <
      epsilon) :=
  dbg_trace "FALLBACK_ORIGINAL_GENERATOR_FORCED"
  owner.track.refine owner.track.initial epsilon positive

open Purelib in
open Purelib.RootIsolation in
open Purelib in
open Purelib.RootIsolation in
/-- Check that two stationary transports preserve the exact original deferred-recipe equation.

Missing inherited history remains inconclusive; only the supplied constructor equation justifies the retained recipe. -/
@[expose] public def stationaryRecipe {parameter :
  SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Gaussian}
    (owner : Riemann.Topology.SquareRootContinuationChain.Owner parameter)
    (same : Riemann.Transport.PreparedDeferredRecipeReplay.Deferred owner) :
    IO (PLift (Riemann.Transport.PreparedDeferredRecipeReplay.Deferred owner)) := do
  have small : Data.Gaussian.Norm.Basic.normSq (parameter - parameter) <
      owner.track.initial.clearance.bound := by
    simpa only [sub_self, Data.Gaussian.Norm.Basic.normSq_zero] using owner.track.initial.clearance.positive
  match Riemann.Transport.PreparedDeferredRecipeReplay.transport owner
      (Riemann.Transport.PreparedDeferredRecipeReplay.History.inherited owner) owner.parameterNonzero small 0 with
  | .error (.inherited _) => pure ()
  | _ => throw (IO.userError "stationary history silently classified an inherited refiner")
  let first := Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance.reservedTransport owner
    owner.parameterNonzero small 0
  let retained : Riemann.Transport.PreparedDeferredRecipeReplay.History first := ⟨fun _ =>
    Riemann.Transport.PreparedDeferredRecipeReplay.transport owner
      (Riemann.Transport.PreparedDeferredRecipeReplay.History.deferred owner same) owner.parameterNonzero small 0⟩
  have firstSmall : Data.Gaussian.Norm.Basic.normSq (parameter - parameter) <
      first.track.initial.clearance.bound := by
    simpa only [sub_self, Data.Gaussian.Norm.Basic.normSq_zero] using first.track.initial.clearance.positive
  match Riemann.Transport.PreparedDeferredRecipeReplay.transport first retained first.parameterNonzero firstSmall 0 with
  | .error _ => throw (IO.userError "stationary transport lost the retained original refiner equation")
  | .ok result =>
      have firstEqual : first = owner := by
        unfold first Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance.reservedTransport
        rw [dif_pos rfl]
      have preserved : Riemann.Transport.PreparedDeferredRecipeReplay.Deferred owner := by
        have ready := result.down
        rw [Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance.reservedTransport, dif_pos rfl,
          firstEqual] at ready
        exact ready
      Purelib.System.IO.println
        "Two stationary transports retained the original deferred recipe; missing source history stayed inconclusive."
      return ⟨preserved⟩

open Purelib in
open Purelib.RootIsolation in
open Purelib.RootIsolation in
/-- Restore the original fallback after checking its exact saved state and failed Newton trace.

Preserve the complete fallback-state equation, checked winding reuse and original stationary source history. -/
@[expose] def fallbackChild (directory source : System.FilePath) (mode : String) : IO Unit := do
  let metadata : CenterCheckpoint.RawCursor ← loadJson ((Purelib.System.FilePath.join source (System.FilePath.mk
    ("center-cursor.json"))))
  let saved : SavedFallbackInput ← loadJson ((Purelib.System.FilePath.join source (System.FilePath.mk
    ("sample/inconclusive.json"))))
  let parameter ← checked "fallback parameter" (decodeGaussian metadata.metadata.parameter)
  let ambient ← decodeBox "fallback ambient" metadata.metadata.rootAmbient
  let box ← decodeBox "fallback box" saved.state.box
  let epsilon ← checked "fallback epsilon" (decodeFraction saved.epsilon)
  if positive : 0 < epsilon then
    let restoredOwner ← fallbackOwner parameter ambient box ⟨mode == "replay", pure ()⟩
      ((Purelib.System.FilePath.join directory (System.FilePath.mk ("input-winding"))))
    let owner := restoredOwner.val
    let history ← stationaryRecipe owner restoredOwner.property
    unless toJson (RootStateCheckpoint.capture owner.track.initial) == toJson saved.state do
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("input-mismatch.json"))))
        (RootStateCheckpoint.capture owner.track.initial, saved.state)
      throw (IO.userError "fallback fixture differs from the saved finite state; all operands retained")
    let counterAction : RootRefinementCheckpoint.Execution Unit := do
      let traceControl ← RootRefinementCheckpoint.Control.create true
      let trace ← RootRefinementCheckpoint.run
        (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination parameter)
        owner.track.initial.raw epsilon
        (SquareRoot.Clearance.QuadraticLineClearance.Owner.quadraticAxisClearances parameter)
        (.direct _ _) traceControl ((Purelib.System.FilePath.join (Purelib.System.FilePath.join source
          (System.FilePath.mk ("sample"))) (System.FilePath.mk (s!"step-{saved.completedIndex + 1}-trace"))))
      match missed : trace.value with
      | some _ => throw (IO.userError "fallback fixture did not retain a missed original Newton attempt")
      | none =>
        if mode == "calibrate" then
          saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical-fallback.json"))))
            (RootStateCheckpoint.capture (originalFallback owner epsilon positive))
          Purelib.System.IO.println "Original deferred fallback calibrated once on the checked saved failure operands."
        else
          let afterSave : IO Unit := do
            if mode == "crash" then
              (← IO.getStdout).flush
              let pid ← IO.Process.getPID
              discard <| Purelib.System.IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
              throw (IO.userError "fallback interruption unexpectedly returned")
          let result ← QuadraticFallbackCheckpoint.run owner.track.initial epsilon positive
            ⟨mode == "replay", afterSave⟩ ((Purelib.System.FilePath.join directory (System.FilePath.mk ("fallback"))))
          match result with
          | .error pending =>
              saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("inconclusive.json"))))
                (pending.report owner.track.initial)
              throw (IO.userError "saved fallback fixture reached an unresolved original branch")
          | .ok accepted =>
              have equation := SquareRoot.Replay.QuadraticFallbackReplay.deferred_refine owner.parameterNonzero
                owner.track.initial owner.track.initial epsilon positive (trace.equation.trans missed)
                accepted.val accepted.property
              let certified : { state : SquareRoot.Replay.QuadraticSampleReplay.State parameter owner.ambient //
                  state = owner.track.refine owner.track.initial epsilon positive } :=
                ⟨SquareRoot.Replay.QuadraticFallbackReplay.fastState (current := owner.track.initial) accepted.val,
                  equation.symm.trans (congrArg (fun track => track.refine owner.track.initial epsilon positive)
                    history.down)⟩
              let expected : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
                ("canonical-fallback.json"))))
              let actual := toJson (RootStateCheckpoint.capture certified.val)
              unless actual == expected do throw (IO.userError "fallback replay changed an original finite state field")
              saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"fallback-output-{mode}.json"))))
                actual
              Purelib.System.IO.println
                "Original deferred fallback restored with its complete state equation; no period ownership inferred \
                  from fixture input."
    let (counterResult, _) ← RootRefinementCheckpoint.Execution.run counterAction {}
    (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) counterResult

  else throw (IO.userError "fallback fixture epsilon is not positive")

/-- Check original fallback calibration, atomic winding interruption and exact generator-free cold restoration. -/
@[expose] def fallbackSelfTest (directory source : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "fallback restart regression requires a fresh directory")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let child := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "60s", executable,
        "fallback-child", directory.toString, source.toString, mode] }
  let occurrences := fun (output : IO.Process.Output) marker =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) marker)).length - 1
  let record := fun mode (output : IO.Process.Output) =>
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"fallback-{mode}-result.json"))))
      (output.exitCode.toNat, output.stdout, output.stderr)
  let calibration ← child "calibrate"
  record "calibrate" calibration
  unless calibration.exitCode == 0 && occurrences calibration "FALLBACK_ORIGINAL_GENERATOR_FORCED" == 1 do
    throw (IO.userError ("fallback calibration failed\n" ++ calibration.stdout ++ calibration.stderr))
  let crash ← child "crash"
  record "crash" crash
  unless crash.exitCode != 0 && occurrences crash "WINDING_DIVISION_GENERATOR_FORCED" == 1 &&
      occurrences crash "FALLBACK_ORIGINAL_GENERATOR_FORCED" == 0 do
    throw (IO.userError ("fallback interruption guard failed\n" ++ crash.stdout ++ crash.stderr))
  for mode in ["resume", "replay"] do
    let output ← child mode
    record mode output
    unless output.exitCode == 0 && occurrences output "FALLBACK_ORIGINAL_GENERATOR_FORCED" == 0 &&
        occurrences output "Two stationary transports retained the original deferred recipe" == 1 &&
        occurrences output "REUSED winding division" > 0 do
      throw (IO.userError ("fallback restart failed\n" ++ output.stdout ++ output.stderr))
    if mode == "replay" && occurrences output "WINDING_DIVISION_GENERATOR_FORCED" != 0 then
      throw (IO.userError "cold fallback replay regenerated a completed winding division")
  Purelib.System.IO.println
    "Original fallback: SIGKILL after one saved division, exact complete state, resumed work and generator-free cold \
      replay passed."

end SavedRootRefinementHarness

/-- Dispatch finite root, center, cycle, refinement, clearance, winding and fallback replay diagnostics. -/
@[expose] def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["fallback-self-test", directory, source] => SavedRootRefinementHarness.fallbackSelfTest directory source
  | ["fallback-child", directory, source, mode] => SavedRootRefinementHarness.fallbackChild directory source mode
  | ["source-refinement-self-test", directory, parents] =>
      SavedRootRefinementHarness.sourceRefinementSelfTest directory parents
  | ["source-refinement-child", directory, parents, mode] =>
      SavedRootRefinementHarness.sourceRefinementChild directory parents mode
  | ["refinement-self-test", directory] => SavedRootRefinementHarness.refinementSelfTest directory
  | ["refinement-child", directory, mode] => SavedRootRefinementHarness.refinementChild directory mode
  | ["clearance-self-test", directory] => SavedRootRefinementHarness.clearanceSelfTest directory
  | ["clearance-child", directory, mode] => SavedRootRefinementHarness.clearanceChild directory mode
  | ["winding-self-test", directory] => SavedRootRefinementHarness.windingSelfTest directory
  | ["winding-child", directory, mode] => SavedRootRefinementHarness.windingChild directory mode
  | ["cycle-self-test", directory] => SavedRootRefinementHarness.cycleSelfTest directory
  | ["cycle-child", directory, mode] => SavedRootRefinementHarness.cycleChild directory mode
  | ["center-self-test", directory] => SavedRootRefinementHarness.centerSelfTest directory
  | ["center-child", directory, mode] => SavedRootRefinementHarness.centerChild directory mode
  | ["trace-self-test", directory] => SavedRootRefinementHarness.traceSelfTest directory
  | ["trace-child", directory, mode] => SavedRootRefinementHarness.traceChild directory mode
  | ["trace-stops", directory, mode] => SavedRootRefinementHarness.traceStops directory (mode == "replay")
  | ["replay", source, directory] => do
      let action : RootRefinementCheckpoint.Execution Unit :=
        SavedRootRefinementHarness.runWith source directory (← RootRefinementCheckpoint.Control.create true)
      let (result, _) ← RootRefinementCheckpoint.Execution.run action {}
      (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result
  | ["self-test", directory] => SavedRootRefinementHarness.selfTest directory
  | [source, directory] => SavedRootRefinementHarness.run source directory
  | _ => throw (IO.userError
    "usage: saved_root_refinement_harness [replay] CELL_SNAPSHOT_DIRECTORY OUTPUT_DIRECTORY | fallback-self-test \
      FRESH_DIRECTORY SAVED_LEAF_DIRECTORY | fallback-child DIRECTORY SAVED_LEAF_DIRECTORY MODE | \
      source-refinement-self-test FRESH_DIRECTORY SAVED_PARENTS_DIRECTORY | source-refinement-child DIRECTORY \
      SAVED_PARENTS_DIRECTORY MODE | self-test|trace-self-test|center-self-test|cycle-self-test|refinement-self-test|\
      winding-self-test FRESH_DIRECTORY")
