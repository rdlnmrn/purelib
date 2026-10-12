module

import Purelib.Data.List.Control

import Purelib.System.FilePath

import Purelib.System.IO

import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.Json.Printer
import Purelib.Data.String.Basic
import Purelib.Data.Nat.Positive
public import Purelib.Riemann.Periods.PeriodCurves
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Power.Isolation
import scripts.checkpoint.RootRefinement
import scripts.checkpoint.RootState
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Riemann.RootContinuation.SquareRootOwnerFamily
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.FTA.Squarefree.Input

import Init.Util
import all Init.Util

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolationReplay
import scripts.checkpoint.InitialExtraction
public import scripts.checkpoint.SquareRootFamily
import Init.Data.List.OfFn
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Exact.LargeSquare
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.Track.Basic
import scripts.checkpoint.Integration

open Purelib

open Purelib.Data.Nat

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Polynomial.Power.Gaussian

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.RootOwnerFrames

open Purelib.RootIsolation

open Purelib.RootIsolation.FTA.Squarefree

open Purelib.RootIsolation.Power

open Purelib.Data (Json)
open scoped Purelib.Data.String Purelib.Data.List
open Purelib.Data.Json (toJson)

public section

/-!
Short end-to-end isolation checkpoint regression, without period preparation
or generated coefficient banks.  The fixture uses the original coefficient-
computed eliminant, large square, ordered seed selection and track constructor.
No alternate root boxes or direct quadratic clearance formulas are supplied.
Run with an explicit SIGKILL deadline and systemd memory bound.
-/

namespace CanonicalIsolationCheckpointHarness

open Purelib.Riemann.Periods.PeriodCurves (GaussianPolynomial)

open IntegrationCheckpoint

/-- The retained positive quadratic degree two. -/
@[expose] def degree : Positive.RootDegree := ⟨2, by decide⟩
/-- The Gaussian polynomial X squared minus two. -/
@[expose] def polynomial : GaussianPolynomial := Purelib.Polynomial.Power.Gaussian.rootPolynomial 2 degree
/-- The exact coefficient-derived squarefree isolation input for the quadratic fixture. -/
@[expose] def input : RootIsolation.FTA.Squarefree.Input polynomial :=
  Isolation.isolationInput (show (2 : Data.Gaussian.Basic.Canonical) ≠ 0 by decide) degree (by decide)

/-- Serialize the original ordered isolation tracks, support and remainder clearance data. -/
@[expose] def outputData (output : Exact.Basic.Output polynomial (RootRadius.Box.largeSquareBox polynomial)
  polynomial.natDegree) :
    Json :=
  Json.mkObj
    [("support", toJson (RootStateCheckpoint.boxData output.support)),
     ("tracks", toJson (output.tracks.map fun track => InitialExtractionCheckpoint.stateData track.initial)),
     ("remainder", toJson (output.remainder.map fun region =>
       (RootStateCheckpoint.boxData region.box, fractionData region.clearance.bound)))]

/-- Evaluate the original isolation constructor with its diagnostic generation marker. -/
@[expose, noinline] def canonical (source : RootIsolation.FTA.Squarefree.Input polynomial) :
    Exact.Basic.Output polynomial (RootRadius.Box.largeSquareBox polynomial) polynomial.natDegree :=
  dbg_trace "CANONICAL_ISOLATION_GENERATOR_FORCED"
  source.isolation

/-- Run calibration, interrupted generation, resume or cold replay for exact canonical isolation.

Compare retained output data and preserve equality to the complete original constructor while checking proposal reuse.
-/
@[expose] def child (directory : System.FilePath) (mode : String) : IO Unit := do
  let action : RootRefinementCheckpoint.Execution Unit := do
    IO.FS.createDirAll directory
    if mode == "calibrate" then
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical.json")))) (outputData (canonical
        input))
      return
    let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
      (if mode == "crash" then some 1 else none)
    let result ← InitialExtractionCheckpoint.isolateLargeSquare input.elimination
      (.separated ⟨control.savedOnly, pure ()⟩ _ input.nonzero input.degreePositive)
      input.degreeAtLeastTwo input.squarefree
      control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("isolation"))))
    have exactOriginal : result.val = canonical input := by
      with_unfolding_all exact result.property
    let snapshot := outputData result.val
    let expected : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical.json"))))
    unless snapshot == expected do throw (IO.userError "replay changed the original ordered isolation or its bounds")
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"isolation-{mode}.json")))) snapshot
    let counts ← RootRefinementCheckpoint.Execution.counts
    if mode == "replay" then
      unless counts.generatedNewton == 0 && counts.generatedRounding == 0 do
        throw (IO.userError "cold isolation replay regenerated proposals")
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"counts-{mode}.json")))) counts
    Purelib.System.IO.println (toJson counts).compress
    -- Retain the full exact equality in an executable client result, while
    -- the marked original constructor remains a proof-only argument.
    let linked : { output : Exact.Basic.Output polynomial (RootRadius.Box.largeSquareBox polynomial)
      polynomial.natDegree //
        output = canonical input } := ⟨result.val, exactOriginal⟩
    Purelib.System.IO.println s!"Exact canonical isolation restored: {linked.val.tracks.length} ordered tracks."
  let (result, _) ← RootRefinementCheckpoint.Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

/-- Evaluate the original independent square-root family with its generation marker. -/
@[expose, noinline] def canonicalFamily (parameter : Data.Gaussian.Basic.Canonical) (nonzero : parameter ≠ 0) :=
  dbg_trace "CANONICAL_FAMILY_GENERATOR_FORCED"
  SquareRootOwnerFamily.independentFamily nonzero

/-- Serialize the two retained original sheet-owner states in their finite index order. -/
@[expose] def familyData {parameter : Data.Gaussian.Basic.Canonical}
    (family : SquareRootOwnerFamily.IndependentFamily parameter) : Json :=
  toJson (List.ofFn fun sheet : Fin 2 => InitialExtractionCheckpoint.stateData (family.owner sheet).track.initial)

/-- Exercise the same family loader as the period consumer, including both original sheet owners and all retained state
bounds. -/
@[expose] def familyChild (directory : System.FilePath) (mode : String) : IO Unit := do
  let action : RootRefinementCheckpoint.Execution Unit := do
    IO.FS.createDirAll directory
    if mode == "calibrate" then
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("family-canonical.json"))))
        (familyData (canonicalFamily 2 (by decide)))
      return
    let control ← RootRefinementCheckpoint.Control.create (mode == "replay" || mode == "wrong-parameter")
      (if mode == "crash" then some 1 else none)
    if mode == "wrong-parameter" then
      SquareRootFamilyCheckpoint.withFamily (parameter := 3) (by decide) control directory fun _ =>
        throw (IO.userError "wrong family parameter reached its consumer")
      return
    SquareRootFamilyCheckpoint.withFamily (parameter := 2) (by decide) control directory fun family => do
      have leftExact : family.owner 0 = (canonicalFamily 2 (by decide)).owner 0 :=
        by with_unfolding_all exact family.owner_eq_independent 0
      have rightExact : family.owner 1 = (canonicalFamily 2 (by decide)).owner 1 :=
        by with_unfolding_all exact family.owner_eq_independent 1
      let leftLinked : {owner // owner = (canonicalFamily 2 (by decide)).owner 0} := ⟨family.owner 0, leftExact⟩
      let rightLinked : {owner // owner = (canonicalFamily 2 (by decide)).owner 1} := ⟨family.owner 1, rightExact⟩
      let snapshot := toJson
        [InitialExtractionCheckpoint.stateData leftLinked.val.track.initial,
         InitialExtractionCheckpoint.stateData rightLinked.val.track.initial]
      let expected : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("family-canonical.json"))))
      unless snapshot == expected do throw (IO.userError
        "family reload changed sheet owners or their full-state bounds")
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"family-{mode}.json")))) snapshot
      let counts ← RootRefinementCheckpoint.Execution.counts
      if mode == "replay" then
        unless counts.generatedNewton == 0 && counts.generatedRounding == 0 do
          throw (IO.userError "cold family reload regenerated proposals")
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"counts-{mode}.json")))) counts
      Purelib.System.IO.println s!"Exact original endpoint family restored: {(toJson counts).compress}"
  let (result, _) ← RootRefinementCheckpoint.Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

/-- Check endpoint-family interruption recovery, exact ordered owners and wrong-parameter rejection.

Cold reloads must reuse completed proposals and retain evidence of the rejected original request. -/
@[expose] def familySelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "family test requires a fresh artifact directory")
  IO.FS.createDirAll directory
  let copy ← Purelib.System.IO.Process.output
    { cmd := "/bin/cp", args := #[(← IO.appPath).toString, ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("tested-harness")))).toString] }
  unless copy.exitCode == 0 do throw (IO.userError copy.stderr)
  let executable := (← IO.appPath).toString
  let child := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "45s", executable, "family-child", directory.toString, mode]
      }
  let count := fun (output : IO.Process.Output) marker =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) marker)).length - 1
  let record := fun mode (output : IO.Process.Output) =>
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{mode}-result.json"))))
      (output.exitCode.toNat, output.stdout, output.stderr)
  let calibration ← child "calibrate"
  record "calibrate" calibration
  unless calibration.exitCode == 0 && count calibration "CANONICAL_FAMILY_GENERATOR_FORCED" == 1 do
    throw (IO.userError ("family marker calibration failed\n" ++ calibration.stdout ++ calibration.stderr))
  let crash ← child "crash"
  record "crash" crash
  unless crash.exitCode != 0 && count crash "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 1 &&
      count crash "CANONICAL_FAMILY_GENERATOR_FORCED" == 0 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("isolation/step-0/seed-0/proposal-0-rounding.json")))).pathExists) do
    throw (IO.userError ("family atomic interruption failed\n" ++ crash.stdout ++ crash.stderr))
  let resumed ← child "resume"
  record "resume" resumed
  unless resumed.exitCode == 0 && count resumed "CANONICAL_FAMILY_GENERATOR_FORCED" == 0 do
    throw (IO.userError ("family resume failed\n" ++ resumed.stdout ++ resumed.stderr))
  let reused : RootRefinementCheckpoint.Counts ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("counts-resume.json"))))
  unless reused.reusedRounding == 1 do throw (IO.userError "family resume regenerated the saved first proposal")
  for mode in ["replay", "wrong-parameter", "replay"] do
    let result ← child mode
    record (if mode == "replay" then "replay" else mode) result
    unless count result "CANONICAL_FAMILY_GENERATOR_FORCED" == 0 &&
        count result "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 0 &&
        count result "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 0 do
      throw (IO.userError "family cold reload forced a completed generator")
    if mode == "wrong-parameter" then
      unless result.exitCode != 0 && (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("isolation/step-0/invalid-request.json")))).pathExists) do
        throw (IO.userError "wrong endpoint-family parameter was not rejected with retained evidence")
    else unless result.exitCode == 0 do
      throw (IO.userError ("family cold reload failed\n" ++ result.stdout ++ result.stderr))
  Purelib.System.IO.println
    "Endpoint families: atomic restart, exact ordered owners, generator-free cold reload and wrong-parameter rejection \
      passed."

/-- Evaluate the complete original endpoint frame with its generation marker. -/
@[expose, noinline] def canonicalFrame (parameter : Data.Gaussian.Basic.Canonical) (nonzero : parameter ≠ 0) :=
  dbg_trace "CANONICAL_FRAME_GENERATOR_FORCED"
  OwnerFrame.build nonzero

/-- Serialize the retained states of the frame's two original sheet owners. -/
@[expose] def frameData {parameter : Data.Gaussian.Basic.Canonical} (frame : RootOwnerFrames.OwnerFrame parameter) :
  Json :=
  toJson (List.ofFn fun sheet : Fin 2 => InitialExtractionCheckpoint.stateData (frame.owners sheet).track.initial)

/-- The restored frame retains exact classifier identity as well as its two ordered initial states; the original
constructor is erased from replay. -/
@[expose] def frameChild (directory : System.FilePath) (mode : String) : IO Unit := do
  let action : RootRefinementCheckpoint.Execution Unit := do
    IO.FS.createDirAll directory
    if mode == "calibrate" then
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("frame-canonical.json")))) (frameData
        (canonicalFrame 2 (by decide)))
      return
    let control ← RootRefinementCheckpoint.Control.create (mode == "replay" || mode == "wrong-parameter")
      (if mode == "crash" then some 1 else none)
    if mode == "wrong-parameter" then
      SquareRootFamilyCheckpoint.withFrame (parameter := 3) (by decide) control directory fun _ =>
        throw (IO.userError "wrong frame parameter reached its consumer")
      return
    SquareRootFamilyCheckpoint.withFrame (parameter := 2) (by decide) control directory fun frame => do
      let linked : { value // value = canonicalFrame 2 (by decide) } := ⟨frame.val, by with_unfolding_all exact
        frame.property⟩
      let snapshot := frameData linked.val
      let expected : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("frame-canonical.json"))))
      unless snapshot == expected do throw (IO.userError "frame reload changed ordered owners or their state bounds")
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"frame-{mode}.json")))) snapshot
      let counts ← RootRefinementCheckpoint.Execution.counts
      if mode == "replay" then
        unless counts.generatedNewton == 0 && counts.generatedRounding == 0 do
          throw (IO.userError "cold frame reload regenerated proposals")
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"counts-{mode}.json")))) counts
      Purelib.System.IO.println s!"Exact original endpoint frame restored: {(toJson counts).compress}"
  let (result, _) ← RootRefinementCheckpoint.Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

/-- Check frame interruption recovery and generator-free reload of the exact original classifier.

The protocol checks ordered owner states and rejects a changed parameter with retained request evidence. -/
@[expose] def frameSelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "frame test requires a fresh artifact directory")
  IO.FS.createDirAll directory
  let copy ← Purelib.System.IO.Process.output
    { cmd := "/bin/cp", args := #[(← IO.appPath).toString, ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("tested-harness")))).toString] }
  unless copy.exitCode == 0 do throw (IO.userError copy.stderr)
  let executable := (← IO.appPath).toString
  let child := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "45s", executable, "frame-child", directory.toString, mode]
      }
  let count := fun (output : IO.Process.Output) marker =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) marker)).length - 1
  let record := fun mode (output : IO.Process.Output) =>
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{mode}-result.json"))))
      (output.exitCode.toNat, output.stdout, output.stderr)
  let calibration ← child "calibrate"
  record "calibrate" calibration
  unless calibration.exitCode == 0 && count calibration "CANONICAL_FRAME_GENERATOR_FORCED" == 1 do
    throw (IO.userError ("frame marker calibration failed\n" ++ calibration.stdout ++ calibration.stderr))
  let crash ← child "crash"
  record "crash" crash
  unless crash.exitCode != 0 && count crash "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 1 &&
      count crash "CANONICAL_FRAME_GENERATOR_FORCED" == 0 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("isolation/step-0/seed-0/proposal-0-rounding.json")))).pathExists) do
    throw (IO.userError ("frame atomic interruption failed\n" ++ crash.stdout ++ crash.stderr))
  let resumed ← child "resume"
  record "resume" resumed
  unless resumed.exitCode == 0 && count resumed "CANONICAL_FRAME_GENERATOR_FORCED" == 0 do
    throw (IO.userError ("frame resume failed\n" ++ resumed.stdout ++ resumed.stderr))
  let reused : RootRefinementCheckpoint.Counts ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("counts-resume.json"))))
  unless reused.reusedRounding == 1 do throw (IO.userError "frame resume regenerated the saved first proposal")
  for mode in ["replay", "wrong-parameter", "replay"] do
    let result ← child mode
    record (if mode == "replay" then "replay" else mode) result
    unless count result "CANONICAL_FRAME_GENERATOR_FORCED" == 0 &&
        count result "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 0 &&
        count result "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 0 do
      throw (IO.userError "frame cold reload forced a completed generator")
    if mode == "wrong-parameter" then
      unless result.exitCode != 0 && (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("isolation/step-0/invalid-request.json")))).pathExists) do
        throw (IO.userError "wrong endpoint-frame parameter was not rejected with retained evidence")
    else unless result.exitCode == 0 do
      throw (IO.userError ("frame cold reload failed\n" ++ result.stdout ++ result.stderr))
  Purelib.System.IO.println
    "Endpoint frames: atomic restart, exact ordered owners, generator-free cold reload and wrong-parameter rejection \
      passed."

end CanonicalIsolationCheckpointHarness
