module

import Purelib.Data.List.Control
import Purelib.Data.Int.Order

import Purelib.System.FilePath

import Purelib.System.IO

import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.String.Basic
public import Test.RootIsolation.Checkpoint.Core
import scripts.checkpoint.InitialExtraction
import scripts.checkpoint.RootRefinement
import scripts.checkpoint.RootState
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Nonnegative.Squarefree
import Purelib.Polynomial.Winding.Box.Region.Selection
import Purelib.Polynomial.Winding.Box.Region.Sum
import Purelib.RootIsolation.Exact.State
import Purelib.RootIsolation.Exact.Step
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.Newton.Extraction.Source.Replay
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Newton.Refinement
import Purelib.RootIsolation.Exact.LargeSquare.Region

-- Child-state certificates reduce the unexposed dbgTrace body owned by Init.Util.
import all Init.Util

import Test.RootIsolation.Checkpoint.GridStages
import Purelib.Data.Gaussian.Basic
import Init.Data.List.Basic
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.Isolation.InitialExtractionReplay
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw.FromRegion
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.RootIsolation.Track.Basic
import scripts.checkpoint.Integration

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Polynomial.Winding.Box

open Purelib.Polynomial.Winding.Box.Region

open Purelib.Riemann.RootContinuation

open Purelib.RootIsolation.Exact

open Purelib.RootIsolation.Exact.LargeSquare

open Purelib.RootIsolation.Exact.State

open Purelib.RootIsolation.FTA.Squarefree

open Purelib.RootIsolation.Newton.Extraction.Source

open Purelib.RootIsolation.State

open Purelib.RootIsolation.Track.Newton

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data (Json)
open scoped Purelib.Data.String Purelib.Data.List
open Purelib.Data.Json (toJson)

public section

namespace CanonicalIsolationCheckpointHarness

open IntegrationCheckpoint

namespace NewtonRefinement

/-- The winding-one state of the quadratic fixture in its original coefficient-derived large square. -/
abbrev State := WindingOne.Basic.WindingOneState polynomial (RootRadius.Box.largeSquareBox polynomial)

/-- The original initial state of the first isolated quadratic root. -/
@[expose] def initial : State := (input.isolation.trackAt ⟨0, by decide⟩).initial

/-- The coefficient-derived subdivision depth for unit-accuracy Newton refinement. -/
@[expose] def depth : Nat := Replay.depth input.squarefree initial.raw 1

/-- Evaluate the original total Newton refinement with its generation marker. -/
@[expose, noinline] def canonical (state : State) : State :=
  dbg_trace "CANONICAL_NEWTON_REFINEMENT_GENERATOR_FORCED"
  Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination state 1 (by decide)

/-- Calibrate or restore the exact original Newton state and its ambient-line bounds.

Cold replay must reuse every original subdivision stage without generating a completed grid. -/
@[expose] def child (directory : System.FilePath) (mode : String) : IO Unit := do
  let action : PolynomialInverseCheckpoint.Execution Unit := do
    IO.FS.createDirAll directory
    if mode == "calibrate" then
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical.json"))))
        (InitialExtractionCheckpoint.stateData (canonical initial))
      return
    let control ← PolynomialInverseCheckpoint.Control.create (mode == "replay")
      (if mode == "crash" then some 1 else none)
    let restored ← NewtonExtractionCheckpoint.refineState input.degreeAtLeastTwo input.squarefree input.elimination
      initial 1 (by decide) control directory
    let linked : {value // value = canonical initial} := ⟨restored.val, by with_unfolding_all exact restored.property⟩
    let actual := toJson (InitialExtractionCheckpoint.stateData linked.val)
    let expected : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical.json"))))
    unless actual == expected do throw (IO.userError "Newton replay changed the canonical state or ambient-line bounds")
    let counts ← PolynomialInverseCheckpoint.Execution.counts
    if mode == "replay" then
      unless counts.generated == 0 && counts.reused == depth do
        throw (IO.userError "Newton replay did not reuse the complete original subdivision")
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"counts-{mode}.json")))) counts
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"state-{mode}.json")))) actual
  let (result, _) ← PolynomialInverseCheckpoint.Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

end NewtonRefinement

/-- Check interrupted Newton recovery and exact reuse of the retained subdivision prefix.

Preserve the original depth and ambient bounds, then reject a corrupted source cut with retained evidence. -/
@[expose] def newtonSelfTest (directory : System.FilePath) (resume : Bool := false) : IO Unit := do
  if resume then
    unless ← directory.pathExists do throw (IO.userError "Newton restart test has no retained directory")
  else if ← directory.pathExists then throw (IO.userError "Newton test requires a fresh artifact directory")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let copy ← Purelib.System.IO.Process.output {cmd := "/bin/cp", args := #[executable, ((Purelib.System.FilePath.join
    directory (System.FilePath.mk ((if resume then "tested-resume-harness" else "tested-harness"))))).toString]}
  unless copy.exitCode == 0 do throw (IO.userError copy.stderr)
  let child := fun mode => Purelib.System.IO.Process.output
    {cmd := "/usr/bin/timeout", args := #["--signal=KILL", "120s", executable, "newton-child", directory.toString,
      mode]}
  let count := fun (result : IO.Process.Output) marker => ((Purelib.Data.String.splitOn (result.stdout ++ result.stderr)
    marker)).length - 1
  let record := fun mode (result : IO.Process.Output) =>
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{mode}-result.json"))))
      (result.exitCode.toNat, result.stdout, result.stderr)
  let reload := fun mode => do
    let saved : Nat × String × String ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"{mode}-result.json"))))
    pure ({exitCode := saved.1.toUInt32, stdout := saved.2.1, stderr := saved.2.2} : IO.Process.Output)
  let calibration ← if resume then reload "calibrate" else child "calibrate"
  record "calibrate" calibration
  unless calibration.exitCode == 0 && count calibration "CANONICAL_NEWTON_REFINEMENT_GENERATOR_FORCED" == 1 do
    throw (IO.userError ("Newton calibration failed\n" ++ calibration.stdout ++ calibration.stderr))
  let crash ← if resume then reload "crash" else child "crash"
  record "crash" crash
  unless crash.exitCode != 0 && (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("subdivision/grid-v1.json")))).pathExists) &&
      count crash "CANONICAL_NEWTON_REFINEMENT_GENERATOR_FORCED" == 0 do
    throw (IO.userError ("Newton interruption failed\n" ++ crash.stdout ++ crash.stderr))
  let mut retained := 0
  let mut stage := (Purelib.System.FilePath.join directory (System.FilePath.mk ("subdivision")))
  for _ in List.range NewtonRefinement.depth do
    if ← ((Purelib.System.FilePath.join stage (System.FilePath.mk ("grid-v1.json")))).pathExists then
      retained := retained + 1
      stage := (Purelib.System.FilePath.join stage (System.FilePath.mk ("next")))
    else break
  let resumed ← child "resume"
  record s!"resume-from-{retained}" resumed
  record "resume" resumed
  unless resumed.exitCode == 0 && count resumed "CANONICAL_NEWTON_REFINEMENT_GENERATOR_FORCED" == 0 do
    throw (IO.userError ("Newton resume failed\n" ++ resumed.stdout ++ resumed.stderr))
  let counts : PolynomialInverseCheckpoint.Counts ← loadJson ((Purelib.System.FilePath.join directory
    (System.FilePath.mk ("counts-resume.json"))))
  unless counts.generated + retained == NewtonRefinement.depth && counts.reused == retained do
    throw (IO.userError "Newton source restoration regenerated its first grid")
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("subdivision/grid-v1.json")))
  let original : RawSubdivisionCheckpoint.Data ← loadJson path
  for mode in ["replay", "corrupt", "replay"] do
    if mode == "corrupt" then saveJson path {original with x := fractionData 0}
    let result ← child "replay"
    record mode result
    unless count result "CANONICAL_NEWTON_REFINEMENT_GENERATOR_FORCED" == 0 &&
        count result "RAW_SUBDIVISION_GRID_GENERATOR_FORCED" == 0 do
      throw (IO.userError "Newton cold replay forced a completed producer")
    if mode == "corrupt" then
      unless result.exitCode != 0 && (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("subdivision/invalid-grid.json")))).pathExists) do
        throw (IO.userError "corrupt Newton source cut was not rejected with retained evidence")
    else unless result.exitCode == 0 do
      throw (IO.userError ("Newton cold replay failed\n" ++ result.stdout ++ result.stderr))
    if mode == "corrupt" then saveJson path original
  Purelib.System.IO.println
    s!"Newton refinement: {NewtonRefinement.depth} original steps, atomic restart, exact ambient bounds and cold \
      replay passed."

namespace InitialFallback

/-- The exact Gaussian parameter with real part minus one and imaginary part eighteen. -/
@[expose] def parameter : Gaussian := ⟨-1, 18⟩
/-- The displayed fallback parameter is nonzero. -/
theorem nonzero : parameter ≠ 0 := by decide
/-- The quadratic polynomial associated with the retained fallback parameter. -/
abbrev Polynomial := SquareRootReconditioning.rootPolynomial parameter

/-- The exact squarefree isolation input derived from the fallback parameter. -/
@[expose] def source : Purelib.RootIsolation.FTA.Squarefree.Input Polynomial := SquareRootReconditioning.isolationInput
    nonzero

/-- The original large-square isolation region for the retained polynomial. -/
@[expose] def initial := Region.largeSquareRegion source.degreeAtLeastTwo

/-- The initial exact isolation state containing the original large-square region. -/
@[expose] def state := IsolationState.initial initial

/-- The original region list has strictly positive total quadrupled winding. -/
theorem positive : 0 < Region.Sum.totalRaw state.regions := by
  change 0 < Winding.Box.Basic.quadrupledBoxWinding _ initial.box + 0
  rw [initial, Region.largeSquareRegion_winding source.degreeAtLeastTwo]
  decide

/-- Every retained region has nonnegative quadrupled winding for the squarefree polynomial. -/
theorem nonnegative : ∀ region ∈ state.regions, 0 ≤ Winding.Box.Basic.quadrupledBoxWinding Polynomial region.box := by
  intro region _
  exact Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative source.degreeAtLeastTwo
    source.squarefree source.elimination region.refinesAmbient region.proper region.clearance

/-- Serialize the ordered output tracks and remaining regions of an exact isolation step. -/
@[expose] def snapshot {p : Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Rational.Box} {state :
  State.IsolationState p ambient}
    (result : Step.StepResult state) : Json :=
  Json.mkObj
    [("tracks", toJson (result.next.tracks.map fun track => InitialExtractionCheckpoint.stateData track.initial)),
     ("regions", toJson (result.next.regions.map fun region =>
       (RootStateCheckpoint.boxData region.box, fractionData region.clearance.bound)))]

/-- Evaluate the original total extraction step with its generation marker. -/
@[expose, noinline] def canonical {p :
  Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Rational.Box}
  (input : Purelib.RootIsolation.FTA.Squarefree.Input p)
    (initial : State.IsolationState p ambient) (nonnegative : ∀ region ∈ initial.regions,
    0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box) (positive : 0 < Region.Sum.totalRaw initial.regions) :=
  dbg_trace "CANONICAL_INITIAL_FALLBACK_GENERATOR_FORCED"
  Step.step input.degreeAtLeastTwo input.squarefree input.elimination initial nonnegative positive

open Purelib in
/-- Calibrate, inspect finite seed failure or replay the original total isolation step.

The result retains full source equality; replay verifies saved subdivision reuse and records unequal outputs on
rejection. -/
@[expose] def childFor {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Rational.Box} (input :
  RootIsolation.FTA.Squarefree.Input p)
    (state : State.IsolationState p ambient)
    (nonnegative : ∀ region ∈ state.regions, 0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box)
    (positive : 0 < Region.Sum.totalRaw state.regions) (directory : System.FilePath) (mode : String) : IO Unit := do
  let action : RootRefinementCheckpoint.Execution Unit := do
    IO.FS.createDirAll directory
    if mode == "calibrate" then
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical.json")))) (snapshot (canonical
        input state nonnegative positive))
      return
    let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
      (if mode == "crash" then some 1 else none)
    if mode == "seeds" then
      let selected := Selection.selectPositive state.regions nonnegative positive
      let result ← InitialExtractionCheckpoint.run input.elimination
        (selected.selected.raw (fun zero => Data.Int.Order.lt_irrefl 0 (zero ▸ selected.positive))) 1
        (.separated ⟨control.savedOnly, pure ()⟩ _ input.nonzero input.degreePositive) control
          ((Purelib.System.FilePath.join directory (System.FilePath.mk ("step"))))
      unless result.value.isNone do throw (IO.userError
        "actual endpoint fixture no longer exercises the total fallback")
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("seed-counts.json")))) (←
        RootRefinementCheckpoint.Execution.counts)
      return
    let result ← InitialExtractionCheckpoint.step input.elimination
      (.separated ⟨control.savedOnly, pure ()⟩ _ input.nonzero input.degreePositive) input.degreeAtLeastTwo
        input.squarefree
      state nonnegative positive control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("step"))))
    let linked : {value // value = canonical input state nonnegative positive} := ⟨result.val, by with_unfolding_all
      exact result.property⟩
    let actual := snapshot linked.val
    let expected : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical.json"))))
    unless actual == expected do
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-result.json")))) (actual,
        expected)
      throw (IO.userError "total initial fallback changed canonical track or complement regions")
    let counts : PolynomialInverseCheckpoint.Counts ← loadJson ((Purelib.System.FilePath.join directory
      (System.FilePath.mk ("step/fallback-counts.json"))))
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"counts-{mode}.json")))) counts
    if mode == "replay" then
      unless counts.generated == 0 && counts.reused > 0 do
        throw (IO.userError "cold total extraction did not reuse its saved subdivision")
    Purelib.System.IO.println s!"Canonical total extraction restored: {(toJson counts).compress}"
  let (result, _) ← RootRefinementCheckpoint.Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

/-- Run the selected total-extraction diagnostic for the retained quadratic fallback fixture. -/
@[expose] def child (directory : System.FilePath) (mode : String) : IO Unit :=
  childFor source state nonnegative positive directory mode

end InitialFallback

end CanonicalIsolationCheckpointHarness
