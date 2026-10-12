module

import Purelib.Data.List.Control

import Purelib.System.FilePath

import Purelib.System.IO

import Purelib.Data.Json.Codec
import Purelib.Data.String.Basic
import scripts.checkpoint.InitialExtraction
import scripts.checkpoint.RootRefinement
import scripts.checkpoint.RootState
import scripts.checkpoint.SquareRootFamily
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.Newton.Extraction.Source.Replay
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.Subdivision.Raw.Iteration.Forward

import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
-- Child-state certificates reduce the unexposed dbgTrace body owned by Init.Util.
import all Init.Util

public import Test.RootIsolation.Checkpoint.Core
import Purelib.Polynomial.Geometry.ClearPath
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.RootIsolation.Track.Basic
import scripts.checkpoint.Integration

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Polynomial.Geometry.Grid

open Purelib.RootIsolation.Newton.Extraction.Source

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.RootIsolation.State

open Purelib.RootIsolation.Subdivision.Raw.Iteration

open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)

open Purelib.Data (Json)
open scoped Purelib.Data.String Purelib.Data.List
open Purelib.Data.Json (toJson)

public section

namespace CanonicalIsolationCheckpointHarness

open IntegrationCheckpoint

namespace FrameGrid

open Purelib.RootIsolation.SquareRoot.Grid.RootFrames
open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.ClearGrid

/-- The constant Gaussian polynomial two used by the endpoint-grid fixture. -/
@[expose] def polynomial : GaussianPolynomial := DensePolynomial.constant 2

/-- The closed rational unit square. -/
@[expose] def box : Rational.Box := ⟨0, 1, 0, 1, by decide, by decide⟩

/-- A vertical grid line at the supplied unit-interval coordinate with exact constant-polynomial clearance. -/
@[expose] def vertical (x : Fraction.Rational) (inside : 0 ≤ x ∧ x ≤ 1) :
    ClearGrid.VerticalLine polynomial box where
  coordinate := x
  inside := inside
  clearance := ⟨1, by decide, fun _ _ _ => by
    rw [polynomial, DensePolynomial.eval_constant]
    decide⟩

/-- A horizontal grid line at the supplied unit-interval coordinate with exact constant-polynomial clearance. -/
@[expose] def horizontal (y : Fraction.Rational) (inside : 0 ≤ y ∧ y ≤ 1) :
    ClearGrid.HorizontalLine polynomial box where
  coordinate := y
  inside := inside
  clearance := ⟨1, by decide, fun _ _ _ => by
    rw [polynomial, DensePolynomial.eval_constant]
    decide⟩

/-- The four-vertex grid formed by the two boundary coordinates in each direction. -/
@[expose] def grid : Grid polynomial box :=
  Grid.build [vertical 0 (by decide), vertical 1 (by decide)]
    [horizontal 0 (by decide), horizontal 1 (by decide)]

/-- Evaluate the original grid root-frame constructor with its generation marker. -/
@[expose, noinline] def canonicalFrames (source : Grid polynomial box) :=
  dbg_trace "CANONICAL_GRID_FRAMES_GENERATOR_FORCED"
  RootFrames.build source

/-- Serialize the original ordered endpoint points and complete frame-owner state data. -/
@[expose] def snapshot (frames : RootFrames grid) : Json :=
  toJson (frames.entries.map fun entry =>
    (gaussianData entry.point, frameData entry.frame))

/-- Calibrate or restore the exact four-entry grid frame cache.

Retain equality to the original constructor and verify that cold replay generates no completed proposals. -/
@[expose] def child (directory : System.FilePath) (mode : String) : IO Unit := do
  let action : RootRefinementCheckpoint.Execution Unit := do
    IO.FS.createDirAll directory
    if mode == "calibrate" then
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("grid-canonical.json")))) (snapshot
        (canonicalFrames grid))
      return
    let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
      (if mode == "crash" then some 1 else none)
    let restored ← SquareRootFamilyCheckpoint.GridFrames.restore control directory grid
    let linked : {frames // frames = canonicalFrames grid} := ⟨restored.val, by with_unfolding_all exact
      restored.property⟩
    let actual := snapshot linked.val
    let expected : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("grid-canonical.json"))))
    unless actual == expected && linked.val.entries.length == 4 do
      throw (IO.userError "grid frame replay changed the four ordered vertex entries")
    let counts ← RootRefinementCheckpoint.Execution.counts
    if mode == "replay" then
      unless counts.generatedNewton == 0 && counts.generatedRounding == 0 do
        throw (IO.userError "grid frame replay regenerated proposals")
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"counts-{mode}.json")))) counts
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"grid-{mode}.json")))) actual
  let (result, _) ← RootRefinementCheckpoint.Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

end FrameGrid

/-- Check atomic interruption, exact original vertex ordering and generator-free frame-cache reload. -/
@[expose] def gridFramesSelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "frame test requires a fresh artifact directory")
  IO.FS.createDirAll directory
  let copy ← Purelib.System.IO.Process.output
    { cmd := "/bin/cp", args := #[(← IO.appPath).toString, ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("tested-harness")))).toString] }
  unless copy.exitCode == 0 do throw (IO.userError copy.stderr)
  let executable := (← IO.appPath).toString
  let child := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "45s", executable, "grid-frames-child", directory.toString,
      mode] }
  let count := fun (output : IO.Process.Output) marker =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) marker)).length - 1
  let record := fun mode (output : IO.Process.Output) =>
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{mode}-result.json"))))
      (output.exitCode.toNat, output.stdout, output.stderr)
  let calibration ← child "calibrate"
  record "calibrate" calibration
  unless calibration.exitCode == 0 && count calibration "CANONICAL_GRID_FRAMES_GENERATOR_FORCED" == 1 do
    throw (IO.userError ("frame marker calibration failed\n" ++ calibration.stdout ++ calibration.stderr))
  let crash ← child "crash"
  record "crash" crash
  unless crash.exitCode != 0 && count crash "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 1 &&
      count crash "CANONICAL_GRID_FRAMES_GENERATOR_FORCED" == 0 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("0/0/isolation/step-0/seed-0/proposal-0-rounding.json")))).pathExists) do
    throw (IO.userError ("frame atomic interruption failed\n" ++ crash.stdout ++ crash.stderr))
  let resumed ← child "resume"
  record "resume" resumed
  unless resumed.exitCode == 0 && count resumed "CANONICAL_GRID_FRAMES_GENERATOR_FORCED" == 0 do
    throw (IO.userError ("frame resume failed\n" ++ resumed.stdout ++ resumed.stderr))
  let reused : RootRefinementCheckpoint.Counts ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("counts-resume.json"))))
  unless reused.reusedRounding == 1 do throw (IO.userError "frame resume regenerated the saved first proposal")
  for mode in ["replay", "replay"] do
    let result ← child mode
    record (if mode == "replay" then "replay" else mode) result
    unless count result "CANONICAL_GRID_FRAMES_GENERATOR_FORCED" == 0 &&
        count result "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 0 &&
        count result "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 0 do
      throw (IO.userError "frame cold reload forced a completed generator")
    unless result.exitCode == 0 do
      throw (IO.userError ("grid frame cold reload failed\n" ++ result.stdout ++ result.stderr))
  Purelib.System.IO.println
    "Grid frames: atomic restart, four original vertex entries and generator-free cold reload passed."

namespace Subdivision

/-- The original raw state of the first isolated quadratic root. -/
@[expose] def source : Raw.RawWindingState polynomial (RootRadius.Box.largeSquareBox polynomial) :=
  (input.isolation.trackAt ⟨0, by decide⟩).initial.raw

/-- Evaluate the original two-step forward raw subdivision with its generation marker. -/
@[expose, noinline] def canonical (state : Raw.RawWindingState polynomial (RootRadius.Box.largeSquareBox polynomial)) :=
  dbg_trace "CANONICAL_RAW_SUBDIVISION_GENERATOR_FORCED"
  Forward.refineForwardN input.elimination 2 state

/-- Serialize the retained root box and exact boundary clearance. -/
@[expose] def snapshot (state : Raw.RawWindingState polynomial (RootRadius.Box.largeSquareBox polynomial)) : Json :=
  toJson (RootStateCheckpoint.boxData state.box, fractionData state.clearance.bound)

/-- Calibrate or replay the original two-step subdivision and reject changed depth requests.

The retained result carries exact source equality and cold replay must reuse both completed grids. -/
@[expose] def child (directory : System.FilePath) (mode : String) : IO Unit := do
  let action : PolynomialInverseCheckpoint.Execution Unit := do
    IO.FS.createDirAll directory
    if mode == "calibrate" then
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical.json")))) (snapshot (canonical
        source))
      return
    let control ← PolynomialInverseCheckpoint.Control.create (mode == "replay" || mode == "wrong-depth")
      (if mode == "crash" then some 1 else none)
    if mode == "wrong-depth" then
      discard <| RawSubdivisionCheckpoint.run input.elimination control directory 3 source
      throw (IO.userError "wrong subdivision depth was accepted")
    let restored ← RawSubdivisionCheckpoint.run input.elimination control directory 2 source
    let linked : {value // value = canonical source} := ⟨restored.val, by with_unfolding_all exact restored.property⟩
    let actual := snapshot linked.val
    let expected : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical.json"))))
    unless actual == expected do throw (IO.userError "subdivision replay changed the canonical box or clearance")
    let counts ← PolynomialInverseCheckpoint.Execution.counts
    if mode == "replay" then
      unless counts.generated == 0 && counts.reused == 2 do
        throw (IO.userError "subdivision replay did not reuse both completed grids")
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"counts-{mode}.json")))) counts
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"state-{mode}.json")))) actual
  let (result, _) ← PolynomialInverseCheckpoint.Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

/-- Report the original coefficient-derived Newton extraction depth. -/
@[expose] def newtonDepth : IO Unit := do
  let depth := Replay.depth input.squarefree source 1
  Purelib.System.IO.println s!"Canonical Newton source depth: {depth}"

end Subdivision

/-- Check interrupted subdivision recovery, original state equality and corruption rejection.

The fresh-directory protocol verifies completed-grid reuse and retains exact invalid-request or invalid-grid evidence.
-/
@[expose] def subdivisionSelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "subdivision test requires a fresh artifact directory")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let copy ← Purelib.System.IO.Process.output {cmd := "/bin/cp", args := #[executable, ((Purelib.System.FilePath.join
    directory (System.FilePath.mk ("tested-harness")))).toString]}
  unless copy.exitCode == 0 do throw (IO.userError copy.stderr)
  let child := fun mode => Purelib.System.IO.Process.output
    {cmd := "/usr/bin/timeout", args := #["--signal=KILL", "45s", executable, "subdivision-child", directory.toString,
      mode]}
  let count := fun (result : IO.Process.Output) marker => ((Purelib.Data.String.splitOn (result.stdout ++ result.stderr)
    marker)).length - 1
  let record := fun mode (result : IO.Process.Output) =>
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{mode}-result.json"))))
      (result.exitCode.toNat, result.stdout, result.stderr)
  let calibration ← child "calibrate"
  record "calibrate" calibration
  unless calibration.exitCode == 0 && count calibration "CANONICAL_RAW_SUBDIVISION_GENERATOR_FORCED" == 1 do
    throw (IO.userError ("subdivision calibration failed\n" ++ calibration.stdout ++ calibration.stderr))
  let crash ← child "crash"
  record "crash" crash
  unless crash.exitCode != 0 && (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("grid-v1.json")))).pathExists) &&
      count crash "CANONICAL_RAW_SUBDIVISION_GENERATOR_FORCED" == 0 do
    throw (IO.userError ("subdivision interruption failed\n" ++ crash.stdout ++ crash.stderr))
  let resumed ← child "resume"
  record "resume" resumed
  unless resumed.exitCode == 0 && count resumed "CANONICAL_RAW_SUBDIVISION_GENERATOR_FORCED" == 0 do
    throw (IO.userError ("subdivision resume failed\n" ++ resumed.stdout ++ resumed.stderr))
  let counts : PolynomialInverseCheckpoint.Counts ← loadJson ((Purelib.System.FilePath.join directory
    (System.FilePath.mk ("counts-resume.json"))))
  unless counts.generated == 1 && counts.reused == 1 do throw (IO.userError "saved subdivision grid was regenerated")
  let original : RawSubdivisionCheckpoint.Data ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("grid-v1.json"))))
  for mode in ["replay", "wrong-depth", "corrupt", "replay"] do
    if mode == "corrupt" then
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("grid-v1.json"))))
        {original with vertical := fractionData 0}
    let result ← child (if mode == "corrupt" then "replay" else mode)
    record mode result
    unless count result "CANONICAL_RAW_SUBDIVISION_GENERATOR_FORCED" == 0 &&
        count result "RAW_SUBDIVISION_GRID_GENERATOR_FORCED" == 0 do
      throw (IO.userError "subdivision cold replay forced a completed producer")
    if mode == "wrong-depth" || mode == "corrupt" then
      let report := if mode == "corrupt" then "invalid-grid.json" else "invalid-request.json"
      unless result.exitCode != 0 && (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
        (report)))).pathExists) do
        throw (IO.userError "invalid subdivision checkpoint lacked retained rejection evidence")
    else unless result.exitCode == 0 do
      throw (IO.userError ("subdivision cold replay failed\n" ++ result.stdout ++ result.stderr))
    if mode == "corrupt" then
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("grid-v1.json")))) original
  Purelib.System.IO.println
    "Raw subdivision: atomic restart, exact two-step state, producer-free replay and corruption rejection passed."

end CanonicalIsolationCheckpointHarness
