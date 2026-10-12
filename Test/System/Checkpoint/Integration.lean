module

import Purelib.Data.Int.Decimal

meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.System.FilePath
import Purelib.Data.String.Parsing

import Purelib.Data.Json.Codec
import Purelib.Data.String.Basic
-- IntegrationCheckpoint retains these deliberate public paths for exposed clients.
import Purelib.System.IO
import Purelib.Data.List.ToString
import Purelib.Data.List.Control
import scripts.checkpoint.Integration
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Program.Gaussian.Exact
import Purelib.Polynomial.Ascending.Gaussian.Basic

import Purelib.Integration.CertifiedProgram

public import scripts.checkpoint.Integration.Import
import Init.Util
import all Init.Util
import Init.Core
import Init.Data.List.Basic
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic

-- Use complete constructor eliminators for the original match arms.
set_option backward.match.sparseCases false

open Purelib.CCL.Progressive

open Purelib.Integration

open Purelib.Integration.Polynomial.Gaussian

open Purelib.Integration.Polynomial.Gaussian.Cell.Basic

open Purelib.Integration.Polynomial.Gaussian.Path.Basic

open Purelib.Integration.Program.Gaussian.Basic

open Purelib.Polynomial

open Purelib.Data (Json)
open Purelib.System.IO
open scoped Purelib.Data.String Purelib.Data.List

public section

/-! Short native checkpoint regression: no Riemann preparation, generated
banks or expanded Lean limits.  Run it under an explicit SIGKILL timeout and
a systemd memory bound.  Completed stores are retained for separate-process
replay and restart tests rather than being silently deleted. -/

namespace IntegrationCheckpointHarness

open Purelib.Integration.CertifiedProgram (Request InvalidRequest)

open Purelib.CCL.Progressive.IntegrationReplay
open IntegrationCheckpoint

/-- The exact cached integration program for the constant polynomial one on the unit segment. -/
@[expose] def source : CachedProgram :=
  (RefinementProgram.exactPolynomial 0 1 (Ascending.Gaussian.Basic.constant 1)).certifiedView.program

/-- The original index-zero observation request with target one. -/
@[expose] def request : Request := ⟨0, 1, by decide⟩

/-- Check typed rejection of malformed fractions, cells and cached replies.

Retain a positive control showing that a valid exact local observation is accepted. -/
@[expose] def unitChecks : IO Unit := do
  let zero := fractionData 0
  let one := fractionData 1
  match decodeFraction ⟨"1", "0"⟩ with
  | .error (.denominator 0 _) => pure ()
  | _ => throw (IO.userError "zero denominator was not certified invalid")
  let exact := CellModel.exact 0 1
    (Ascending.Gaussian.Basic.constant 1)
  let raw := cellData exact
  match decodeCell { raw with allowance := fractionData (-1) } with
  | .error (.negative _ _ _) => pure ()
  | _ => throw (IO.userError "negative cell allowance was not certified invalid")
  let badLocal : LocalData := ⟨zero, gaussianData 1, gaussianData 1⟩
  match decodeCell { raw with observations := [badLocal] } with
  | .error (.gaussianMismatch _ _ _ _) => pure ()
  | _ => throw (IO.userError "altered local error was not certified invalid")
  let tooFar : LocalData := ⟨zero, gaussianData 2, gaussianData 1⟩
  match decodeCell { raw with observations := [tooFar] } with
  | .error (.localBound _ _ _) => pure ()
  | _ => throw (IO.userError "excessive local error was not certified invalid")
  let model : Path.Basic.PathModel := ⟨[exact]⟩
  match decodeReply model ⟨gaussianData 2, zero⟩ with
  | .error (.gaussianMismatch _ _ _ _) => pure ()
  | _ => throw (IO.userError "altered sample was not certified invalid")
  match decodeReply model ⟨gaussianData 1, one⟩ with
  | .error (.rationalMismatch _ _ _ _) => pure ()
  | _ => throw (IO.userError "altered aggregate allowance was not certified invalid")
  let validLocal : LocalData := ⟨zero, gaussianData 1, gaussianData 0⟩
  discard <| checked "valid local observation" (decodeCell { raw with observations := [validLocal] })
  println "Typed malformed-data and valid local-observation checks passed."

/-- Generate and source-free replay the eight-bit checkpoint fixture. -/
@[expose] def generate (directory : System.FilePath) : IO Unit := do
  unitChecks
  let retained := Thunk.mk fun _ => source
  IntegrationCheckpoint.observe directory "checkpoint regression: integral of 1 on [0,1]" retained
    (fun index => pure ⟨(retained.get.stage index).model, some ⟨rfl⟩⟩) .numericalOnly request 8
  replayOnly directory 8

/-- Resume the complete observation while forbidding every source-generation callback.

The original completed checkpoints supply all requested replies. Any callback
would fail the action, so success certifies that the retained replay reused them. -/
@[expose] def resumeWithoutSource (directory : System.FilePath) : IO Unit := do
  let retained := Thunk.mk fun _ => source
  IntegrationCheckpoint.observe directory "checkpoint regression: integral of 1 on [0,1]" retained
    (fun _ => throw (IO.userError "restart unexpectedly invoked source generation")) .numericalOnly request 8
  println "Restart passed without calling the source generator."

/-- Evaluate the original source constructor with its diagnostic marker. -/
@[expose, noinline] def markedSource (token : Unit) : CachedProgram :=
  match token with
  | () =>
      dbg_trace "CHECKPOINT_ORIGINAL_CONSTRUCTOR_FORCED"
      source

/-- The traced constructor is definitionally the original source, but the native marker detects any accidental runtime
reconstruction. -/
@[expose] def phasedChild (directory : System.FilePath) (diskOnly : Bool := false) : IO Unit := do
  let retained := Thunk.mk fun _ => markedSource ()
  let prepare : IO (Preparation retained.get) := do
    let seeds : List (KnownReply retained.get) := (List.range 16).map fun index =>
      { index := index, reply := source.stage index, equal := by rfl }
    for seed in seeds do
      saveModel directory seed.index seed.reply.model
      saveReply directory seed.index seed.reply
    if diskOnly then
      pure (.checked (IntegrationReplay.control source)
        (seeds.map fun seed => (seed.index, seed.reply)))
    else pure (.certified ⟨IntegrationReplay.control source, by rfl, by rfl⟩ seeds)
  observeWithPreparation directory "phased checkpoint: exact original source, retained control" retained
    prepare (fun _ => throw (IO.userError "phased run unexpectedly requested an uncached source stage"))
    .numericalOnly request 8
  replayOnly directory 8
  let receipt : ReceiptData ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("receipt-8.json"))))
  unless receipt.freshSourceVerified == !diskOnly do
    throw (IO.userError "preparation reported the wrong source-verification boundary")

/-- Check that certified and numerical-only prepared replay avoid forcing the marked source constructor.

The original marker calibration and two child requests distinguish native source
reconstruction from retained prepared work. Their captured output and exit codes
must satisfy the same marker and replay checks. -/
@[expose] def phasedSelfTest (directory : System.FilePath) : IO Unit := do
  let executable := (← IO.appPath).toString
  let hasMarker (output : IO.Process.Output) :=
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) "CHECKPOINT_ORIGINAL_CONSTRUCTOR_FORCED")).length > 1
  let calibration ← Process.output { cmd := executable, args := #["marker-child"] }
  unless calibration.exitCode == 0 && hasMarker calibration do
    throw (IO.userError "constructor-marker calibration failed")
  let output ← Process.output { cmd := executable, args := #["phased-child", directory.toString] }
  unless output.exitCode == 0 do throw (IO.userError (output.stdout ++ output.stderr))
  unless !hasMarker output do throw (IO.userError "phased replay forced the original source constructor")
  IO.print output.stdout
  let checkedOutput ← Process.output
    { cmd := executable, args := #["checked-child", ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("checked")))).toString] }
  unless checkedOutput.exitCode == 0 && !hasMarker checkedOutput do
    throw (IO.userError (checkedOutput.stdout ++ checkedOutput.stderr))
  IO.print checkedOutput.stdout
  println
    "Phased preparation, original-runner comparison and disk replay passed without forcing the marked source \
      constructor."

/-- Construct one adjacent exact constant-one cell with its per-index generation marker. -/
@[expose, noinline] def markedCell (index : Nat) : Polynomial.Gaussian.Cell.Basic.CellModel :=
  dbg_trace s!"CHECKPOINT_CELL_FORCED_{index}"
  .exact (index : Gaussian) ((index + 1 : Nat) : Gaussian)
    (Ascending.Gaussian.Basic.constant 1)

/-- Materialize the requested cell prefix and preserve its exact numerical and source-evidence boundary.

The original mode determines the retained ordered cell requests. The crash mode
signals this child only after the first complete checkpoint has been published,
so later reuse preserves its data and numerical verification boundary. -/
@[expose] def cellsChild (directory : System.FilePath) (mode : String) : IO Unit := do
  openStore directory "incremental checkpoint regression: two adjacent constant-one cells"
  let work := [Thunk.mk fun _ => markedCell 0] ++
    (if mode == "prefix" || mode == "crash" then [] else [Thunk.mk fun _ => markedCell 1])
  let batch ← materializeCells directory 0 0 (work.map CellTask.numerical)
  unless batch.cells.length == work.length && batch.source_eq.isSome == (mode != "resume") do
    throw (IO.userError "incremental cells lost count or incorrectly claimed a source equality")
  let model : Path.Basic.PathModel := ⟨batch.cells⟩
  unless model.integralSample == (work.length : Gaussian) && model.aggregateAllowance == 0 do
    throw (IO.userError "incremental cell data failed exact numerical checks")
  println s!"Incremental cells {mode}: count={batch.cells.length}; fresh={batch.source_eq.isSome}"
  (← IO.getStdout).flush
  if mode == "crash" then
    -- Signal this child only after the atomic checkpoint exists.  This avoids
    -- a short wall-clock race on the shared machine; the parent also applies
    -- an explicit timeout in case the child fails to reach this boundary.
    let pid ← IO.Process.getPID
    discard <| Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
    throw (IO.userError "SIGKILL did not terminate the checkpoint child")

/-- Check that interruption preserves the completed first cell and resume generates only the missing second cell.

The original fresh, interrupted and resumed process requests retain their marker
checks and exit codes. The saved first cell must survive interruption without
forcing its generator during resumed materialization. -/
@[expose] def cellsSelfTest (directory : System.FilePath) : IO Unit := do
  let executable := (← IO.appPath).toString
  let hasMarker (output : IO.Process.Output) (index : Nat) :=
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) s!"CHECKPOINT_CELL_FORCED_{index}")).length > 1
  let fresh ← Process.output
    { cmd := executable, args := #["cells-child", ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("fresh")))).toString, "fresh"] }
  unless fresh.exitCode == 0 && hasMarker fresh 0 && hasMarker fresh 1 do
    throw (IO.userError ("fresh-cell marker calibration failed\n" ++ fresh.stdout ++ fresh.stderr))
  let partialOutput ← Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable,
      "cells-child", ((Purelib.System.FilePath.join directory (System.FilePath.mk ("resume")))).toString, "crash"] }
  unless partialOutput.exitCode == 137 && hasMarker partialOutput 0 && !hasMarker partialOutput 1 &&
      (← ((Purelib.System.FilePath.join (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
        (System.FilePath.mk ("resume"))) (System.FilePath.mk ("model-0.cells"))) (System.FilePath.mk
        ("cell-0.json")))).pathExists) do
    throw (IO.userError ("SIGKILL partial-cell checkpoint failed\n" ++ partialOutput.stdout ++ partialOutput.stderr))
  let resumed ← Process.output
    { cmd := executable, args := #["cells-child", ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("resume")))).toString, "resume"] }
  unless resumed.exitCode == 0 && !hasMarker resumed 0 && hasMarker resumed 1 do
    throw (IO.userError ("restart regenerated a saved cell or failed to generate the missing cell\n" ++ resumed.stdout
      ++ resumed.stderr))
  IO.print fresh.stdout
  IO.print partialOutput.stdout
  IO.print resumed.stdout
  println
    "SIGKILL restart checked and reused cell zero without forcing its generator; only missing cell one was generated."

/-- Identify saved cells from restored finite source data without evaluating their marked constructors.

The retained per-index cached cells carry exact equations to their original
source cells. Crash mode publishes its certified prefix before interruption;
the other modes retain the same checked source identity. -/
@[expose] def certifiedCellsChild (directory : System.FilePath) (mode : String) : IO Unit := do
  openStore directory "source-certified incremental cell regression"
  let indices := if mode == "crash" then [0] else [0, 1]
  let tasks := indices.map fun index =>
    CellTask.fromCached (Thunk.mk fun _ => markedCell index)
      (Thunk.mk fun _ => CellModel.exact (index : Gaussian)
        ((index + 1 : Nat) : Gaussian) (Ascending.Gaussian.Basic.constant 1)) (by rfl)
  let batch ← materializeCells directory 0 0 tasks
  unless batch.cells.length == indices.length && batch.source_eq.isSome do
    throw (IO.userError "checked cell reload lost its source equation")
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"certified-cells-{mode}.json"))))
    (batch.cells.length, batch.source_eq.isSome)
  if mode == "crash" then
    let pid ← IO.Process.getPID
    discard <| Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
    throw (IO.userError "SIGKILL did not terminate the certified-cell child")
  println "Every loaded cell retains its original-source equation."

/-- Check interrupted certified-cell reuse and reject a different source polynomial with the same integral.

The original crash, resume and replay requests retain their captured outcomes.
A saved cell is reused only with its source equation; equal numerical integrals
do not justify replacing its original polynomial. -/
@[expose] def certifiedCellsSelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "certified-cell regression requires a fresh directory")
  let executable := (← IO.appPath).toString
  let child := fun mode => Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable,
        "certified-cells-child", directory.toString, mode] }
  let marked := fun (output : IO.Process.Output) index =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) s!"CHECKPOINT_CELL_FORCED_{index}")).length > 1
  let record := fun mode (output : IO.Process.Output) =>
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"certified-{mode}-result.json"))))
      (output.exitCode.toNat, output.stdout, output.stderr)
  let crash ← child "crash"
  record "crash" crash
  unless crash.exitCode == 137 && marked crash 0 && !marked crash 1 do
    throw (IO.userError ("certified-cell interruption failed\n" ++ crash.stdout ++ crash.stderr))
  let resume ← child "resume"
  record "resume" resume
  unless resume.exitCode == 0 && !marked resume 0 && marked resume 1 do
    throw (IO.userError ("certified-cell resume regenerated a completed cell\n" ++ resume.stdout ++ resume.stderr))
  let replay ← child "replay"
  record "replay" replay
  unless replay.exitCode == 0 && !marked replay 0 && !marked replay 1 do
    throw (IO.userError ("cold certified-cell replay forced a generator\n" ++ replay.stdout ++ replay.stderr))
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("model-0.cells/cell-0.json")))
  let saved : CellData ← loadJson path
  -- Integral of 2t on [0,1] equals that of 1, but the source models differ.
  saveJson path { saved with coefficients := [gaussianData 0, gaussianData 2] }
  let corrupt ← child "replay"
  record "different-source-same-integral" corrupt
  unless corrupt.exitCode != 0 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("model-0.cells/cell-0-source-mismatch.json")))).pathExists) do
    throw (IO.userError "same-integral replacement polynomial was accepted as the original source")
  saveJson path saved
  println
    "Certified cell restart: exact source equations, no repeated generators, and same-integral source substitution \
      rejected."

set_option genInjectivity false in
/-- Match the universe of actual prepared refinement caches. -/
structure HighState : Type 2 where
  /-- The retained sequence of newly acquired query indices. -/ seen : List Nat

constructive_injectivity HighState

/-- Thread the supplied preparation state through original requests and disk hits.

New requests retain their computed updates. Disk reuse preserves that state
without invoking a completed generator or inventing a new source equation. -/
@[expose] def stateful (directory : System.FilePath) : IO Unit := do
  openStore directory "state-threaded acquisition regression"
  let retained := Thunk.mk fun _ => source
  let generate : ModelGenerator retained.get HighState := fun {_} index state done =>
    done ⟨(retained.get.stage index).model, some ⟨rfl⟩⟩ ⟨index :: state.seen⟩
  acquireReply directory retained generate .numericalOnly 3 ⟨[]⟩ fun first firstKnown firstState => do
    unless first.sample == 1 && firstKnown.isSome && firstState.seen == [3] do
      throw (IO.userError "first stateful generation lost its reply, state or source equality")
    acquireReply directory retained generate .numericalOnly 0 firstState fun second secondKnown secondState => do
      unless second.sample == 1 && secondKnown.isSome && secondState.seen == [0, 3] do
        throw (IO.userError "out-of-order stateful generation lost the retained state")
      acquireReply directory retained generate .numericalOnly 3 secondState fun cached cachedKnown cachedState => do
        unless cached.sample == 1 && cachedKnown.isNone && cachedState.seen == [0, 3] do
          throw (IO.userError "disk hit changed state, regenerated a model or claimed fresh source evidence")
        acquireReply directory retained generate .numericalOnly 2 cachedState fun final finalKnown finalState => do
          unless final.sample == 1 && finalKnown.isSome && finalState.seen == [2, 0, 3] do
            throw (IO.userError "generation after disk reuse lost retained state")
          println "Higher-universe state survived new, out-of-order and disk-cached model requests."

/-- Exercise the complete observation through saved control and whole-model cache hits. The original source, preparation
and model generators are all forbidden on reload; only the independent finite restored data are available. -/
@[expose] def certifiedObservationChild (directory : System.FilePath) (mode : String) : IO Unit := do
  let identity := "source-certified whole observation reload regression"
  openStore directory identity
  let retained := Thunk.mk fun _ => markedSource ()
  if mode == "crash" || mode == "model-crash" then
    for index in List.range 16 do
      let reply := source.stage index
      saveModel directory index reply.model
      if mode == "crash" then saveReply directory index reply
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("control.json")))) (controlData
      (IntegrationReplay.control source))
    let pid ← IO.Process.getPID
    discard <| Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
    throw (IO.userError "SIGKILL did not terminate the source-observation child")
  let prepare : IO (Preparation retained.get) := do
    unless mode == "numerical" do
      throw (IO.userError "saved control reran the preparation generator")
    let seeds : List (KnownReply retained.get) := (List.range 16).map fun index =>
      ⟨index, source.stage index, by rfl⟩
    for seed in seeds do
      saveModel directory seed.index seed.reply.model
      saveReply directory seed.index seed.reply
    pure (.checked (IntegrationReplay.control source)
      (seeds.map fun seed => (seed.index, seed.reply)))
  let reload : Reload retained.get HighState :=
    if mode == "numerical" then .numericalOnly else
      ⟨.certified (pure ⟨IntegrationReplay.control source, by rfl, by rfl⟩),
        .certified fun index state done =>
          done ⟨(source.stage index).model, by rfl⟩ ⟨index :: state.seen⟩⟩
  observeWithState directory identity retained prepare (HighState.mk [])
    (fun _ _ _ => throw (IO.userError "saved reply reran the model generator")) reload request 8
  replayOnly directory 8
  if mode != "numerical" then
    let receipt : ReceiptData ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("source-verified-receipt-8.json"))))
    unless receipt.freshSourceVerified do
      throw (IO.userError "source-certified restart did not record new original-runner acceptance")
  println "Whole-observation cache reload retained source equations without calling the forbidden generators."

/-- Check certified control, model and reply restart without rerunning forbidden generators.

Preserve historical numerical receipts and reject numerically valid substitutes that lack the original source identity.
-/
@[expose] def certifiedObservationSelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "source-observation regression requires a fresh directory")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let child := fun (store : System.FilePath) mode => Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable,
        "certified-observation-child", store.toString, mode] }
  let run := fun name store mode => do
    let output ← child store mode
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{name}.json")))) (output.exitCode.toNat,
      output.stdout, output.stderr)
    unless ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr)
      "CHECKPOINT_ORIGINAL_CONSTRUCTOR_FORCED")).length == 1 do
      throw (IO.userError "source-certified reload forced the original source constructor")
    pure output
  for mode in ["crash", "model-crash"] do
    let store := (Purelib.System.FilePath.join directory (System.FilePath.mk (mode)))
    let crash ← run mode store mode
    unless crash.exitCode == 137 do
      throw (IO.userError ("source-observation crash checkpoint failed\n" ++ crash.stdout ++ crash.stderr))
    let resumed ← run s!"{mode}-resume" store "resume"
    unless resumed.exitCode == 0 do throw (IO.userError (resumed.stdout ++ resumed.stderr))
    if mode == "crash" then
      unless ((Purelib.Data.String.splitOn resumed.stdout "BEGIN aggregate integral/allowance")).length == 1 do
        throw (IO.userError "saved reply reran its aggregate generator")
    let cold ← run s!"{mode}-cold" store "resume"
    unless cold.exitCode == 0 && ((Purelib.Data.String.splitOn cold.stdout "BEGIN aggregate integral/allowance")).length
      == 1 do
      throw (IO.userError ("cold source-observation restart repeated aggregation\n" ++ cold.stdout ++ cold.stderr))
  let numericalStore := (Purelib.System.FilePath.join directory (System.FilePath.mk ("numerical")))
  let numerical ← run "numerical" numericalStore "numerical"
  unless numerical.exitCode == 0 do throw (IO.userError (numerical.stdout ++ numerical.stderr))
  let historical ← FS.readFile ((Purelib.System.FilePath.join numericalStore (System.FilePath.mk ("receipt-8.json"))))
  let certified ← run "numerical-new-source-acceptance" numericalStore "resume"
  unless certified.exitCode == 0 && historical == (← FS.readFile ((Purelib.System.FilePath.join numericalStore
    (System.FilePath.mk ("receipt-8.json"))))) do
    throw (IO.userError "source re-verification failed or silently rewrote the historical numerical-only receipt")
  let store := (Purelib.System.FilePath.join directory (System.FilePath.mk ("crash")))
  let originalControl : ControlData ← loadJson ((Purelib.System.FilePath.join store (System.FilePath.mk
    ("control.json"))))
  saveJson ((Purelib.System.FilePath.join store (System.FilePath.mk ("control.json")))) { originalControl with
    centerBound := fractionData 99 }
  let badControl ← run "wrong-source-control" store "resume"
  unless badControl.exitCode != 0 && (← ((Purelib.System.FilePath.join store (System.FilePath.mk
    ("control-source-mismatch.json")))).pathExists) do
    throw (IO.userError "numerically valid but wrong-source control was not rejected")
  saveJson ((Purelib.System.FilePath.join store (System.FilePath.mk ("control.json")))) originalControl
  let queries : List Nat ← loadJson ((Purelib.System.FilePath.join store (System.FilePath.mk ("trace-8.json"))))
  let some index := queries.head? | throw (IO.userError "source-observation fixture had no query")
  let originalModel ← loadModel store index
  let substitute : Path.Basic.PathModel :=
    ⟨[.exact 0 1 ⟨[0, 2]⟩]⟩
  unless substitute.integralSample == originalModel.integralSample do
    throw (IO.userError "whole-model source-substitution test is not same-integral")
  saveModel store index substitute
  let badModel ← run "same-integral-wrong-source-model" store "resume"
  unless badModel.exitCode != 0 && (← ((Purelib.System.FilePath.join store (System.FilePath.mk
    (s!"model-{index}-source-mismatch.json")))).pathExists) do
    throw (IO.userError "same-integral whole-model substitution bypassed source comparison")
  saveModel store index originalModel
  println
    "PASS source-certified control/model/reply restart, partial aggregation, historical-receipt preservation and \
      wrong-source rejection."

/-- Retain numerical reuse of a partial per-cell checkpoint.

Fresh controller preparation supplies its own source equations. It does not
identify previously saved cells with original source cells without comparison. -/
@[expose] def partialReply (directory : System.FilePath) : IO Unit := do
  let identity := "partial-model source-boundary regression"
  openStore directory identity
  let retained := Thunk.mk fun _ => source
  let work := [Thunk.mk fun _ => CellModel.exact 0 1
    (Ascending.Gaussian.Basic.constant 1)]
  let first ← materializeCells directory 0 0 (work.map CellTask.numerical)
  unless first.source_eq.isSome do
    throw (IO.userError "partial-model regression requires a fresh directory")
  let generate : (index : Nat) → IO (PendingModel retained.get index) := fun index => do
    let batch ← materializeCells directory index 0 (work.map CellTask.numerical)
    let equal := batch.source_eq.map fun witness =>
      (PLift.up (show PathModel.mk batch.cells =
        (retained.get.stage index).model from by
        rw [witness.down]
        rfl))
    pure ⟨⟨batch.cells⟩, equal⟩
  IntegrationCheckpoint.observe directory identity retained generate .numericalOnly request 8
  replayOnly directory 8
  let receipt : ReceiptData ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("receipt-8.json"))))
  unless !receipt.freshSourceVerified do
    throw (IO.userError "partial disk reuse incorrectly claimed fresh source verification")
  println "Partial model reuse completed and replayed without claiming fresh source verification."

/-- Validate a retained model without accessing its source generator.

The original model checkpoint is checked independently of a complete observation
receipt. An interrupted enclosing observation does not invalidate completed data. -/
@[expose] def checkModel (directory : System.FilePath) (index : Nat) : IO Unit := do
  profile directory s!"BEGIN source-free checked model {index}"
  let reply ← loadReply directory index
  profile directory s!"PASS source-free checked model {index}; cells={reply.model.cells.length}"
  println "Numerical model consistency only; no source ownership reconstruction or complete observation claimed."

/-- Require the supplied regression action to fail. -/
@[expose] public def expectImportFailure (description : String) (action : IO Unit) : IO Unit := do
  let failed ← try action; pure false catch _ => pure true
  unless failed do throw (IO.userError s!"{description}: unexpected success")

/-- Only regression fixtures are retagged. Production import preserves the original fingerprint and writes a separate
destination provenance record. -/
@[expose] public def retagImportFixture (directory : System.FilePath) : IO Unit := do
  let manifest : Manifest ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("manifest.json"))))
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("manifest.json"))))
    { manifest with binarySha256 := "different-executable-regression-fixture" }

/-- Check explicit numerical import across executable identities and interruption recovery.

Preserve the original store, retain validated cell prefixes and avoid importing source-ownership claims. -/
@[expose] def importSelfTest (directory : System.FilePath) : IO Unit := do
  let identity := "checkpoint regression: integral of 1 on [0,1]"
  let original := (Purelib.System.FilePath.join directory (System.FilePath.mk ("original")))
  let imported := (Purelib.System.FilePath.join directory (System.FilePath.mk ("imported")))
  generate original
  retagImportFixture original
  let manifestBefore ← FS.readFile ((Purelib.System.FilePath.join original (System.FilePath.mk ("manifest.json"))))
  match checkImportIdentity "different input" (← loadJson ((Purelib.System.FilePath.join original (System.FilePath.mk
    ("manifest.json"))))) with
  | .error (.identity _ _ _) => pure ()
  | _ => throw (IO.userError "input mismatch did not return typed invalidity")
  expectImportFailure "ordinary open must reject changed executable" (openStore original identity)
  expectImportFailure "import must preserve the original directory" do
    discard <| importNumerical original original identity
  expectImportFailure "import must reject wrong input" do
    discard <| importNumerical original ((Purelib.System.FilePath.join directory (System.FilePath.mk ("wrong-input"))))
      "different input"
  unless !(← ((Purelib.System.FilePath.join directory (System.FilePath.mk ("wrong-input")))).pathExists) do
    throw (IO.userError "rejected input created a destination")
  let report ← importNumerical original imported identity
  unless report.control && report.request && !report.models.isEmpty do
    throw (IO.userError "import lost completed numerical work")
  unless !(← ((Purelib.System.FilePath.join imported (System.FilePath.mk ("receipt-8.json")))).pathExists) do
    throw (IO.userError "import copied a receipt/source-verification claim")
  unless (← FS.readFile ((Purelib.System.FilePath.join original (System.FilePath.mk ("manifest.json"))))) ==
    manifestBefore do
    throw (IO.userError "import changed the original store")
  let executable := (← IO.appPath).toString
  let resumed ← Process.output
    { cmd := executable, args := #["resume-without-source", imported.toString] }
  unless resumed.exitCode == 0 do throw (IO.userError (resumed.stdout ++ resumed.stderr))
  let oldReceipt : ReceiptData ← loadJson ((Purelib.System.FilePath.join original (System.FilePath.mk
    ("receipt-8.json"))))
  let newReceipt : ReceiptData ← loadJson ((Purelib.System.FilePath.join imported (System.FilePath.mk
    ("receipt-8.json"))))
  unless jsonText { oldReceipt with freshSourceVerified := false } == jsonText newReceipt do
    throw (IO.userError "imported observation changed its numerical result or claimed fresh source ownership")
  replayOnly imported 8
  IO.print resumed.stdout
  let cellsIdentity := "incremental checkpoint regression: two adjacent constant-one cells"
  let originalCells := (Purelib.System.FilePath.join directory (System.FilePath.mk ("original-cells")))
  let importedCells := (Purelib.System.FilePath.join directory (System.FilePath.mk ("imported-cells")))
  let prefixRun ← Process.output
    { cmd := executable, args := #["cells-child", originalCells.toString, "prefix"] }
  unless prefixRun.exitCode == 0 do throw (IO.userError (prefixRun.stdout ++ prefixRun.stderr))
  retagImportFixture originalCells
  discard <| importNumerical originalCells importedCells cellsIdentity
  let continued ← Process.output
    { cmd := executable, args := #["cells-child", importedCells.toString, "resume"] }
  let output := continued.stdout ++ continued.stderr
  unless continued.exitCode == 0 &&
      ((Purelib.Data.String.splitOn output "CHECKPOINT_CELL_FORCED_0")).length == 1 &&
      1 < ((Purelib.Data.String.splitOn output "CHECKPOINT_CELL_FORCED_1")).length do
    throw (IO.userError ("cross-executable partial restart regenerated completed work\n" ++ output))
  IO.print continued.stdout
  -- A malformed second cell stops an import after the first cell has been
  -- durably copied.  Repair only this test fixture, then resume that import.
  let malformed := (Purelib.System.FilePath.join directory (System.FilePath.mk ("malformed")))
  let repairedImport := (Purelib.System.FilePath.join directory (System.FilePath.mk ("repaired-import")))
  openStore malformed cellsIdentity
  IO.FS.createDirAll ((Purelib.System.FilePath.join malformed (System.FilePath.mk ("model-0.cells"))))
  let first := cellData (CellModel.exact 0 1
    (Ascending.Gaussian.Basic.constant 1))
  let second := cellData (CellModel.exact 1 2
    (Ascending.Gaussian.Basic.constant 1))
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join malformed (System.FilePath.mk
    ("model-0.cells"))) (System.FilePath.mk ("cell-0.json")))) first
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join malformed (System.FilePath.mk
    ("model-0.cells"))) (System.FilePath.mk ("cell-1.json"))))
    { second with allowance := fractionData (-1) }
  retagImportFixture malformed
  expectImportFailure "import must reject malformed cell" do
    discard <| importNumerical malformed repairedImport cellsIdentity
  unless (← ((Purelib.System.FilePath.join (Purelib.System.FilePath.join repairedImport (System.FilePath.mk
    ("model-0.cells"))) (System.FilePath.mk ("cell-0.json")))).pathExists) &&
      !(← ((Purelib.System.FilePath.join (Purelib.System.FilePath.join repairedImport (System.FilePath.mk
        ("model-0.cells"))) (System.FilePath.mk ("cell-1.json")))).pathExists) do
    throw (IO.userError "failed import did not preserve exactly the checked prefix")
  let firstBefore ← FS.readFile ((Purelib.System.FilePath.join (Purelib.System.FilePath.join repairedImport
    (System.FilePath.mk ("model-0.cells"))) (System.FilePath.mk ("cell-0.json"))))
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join malformed (System.FilePath.mk
    ("model-0.cells"))) (System.FilePath.mk ("cell-1.json")))) second
  let completed ← importNumerical malformed repairedImport cellsIdentity
  unless completed.cells == 2 &&
      (← FS.readFile ((Purelib.System.FilePath.join (Purelib.System.FilePath.join repairedImport (System.FilePath.mk
        ("model-0.cells"))) (System.FilePath.mk ("cell-0.json"))))) == firstBefore do
    throw (IO.userError "interrupted import did not resume with its checked prefix intact")
  println
    "PASS checked cross-executable numerical import, cold reply/cell reuse, typed identity rejection and \
      interrupted-import recovery; no source-ownership claim imported."

/-- Require exact equality between retained checkpoint bytes and the expected bytes. -/
@[expose] public def requireBytes (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  unless (← IO.FS.readBinFile path) == bytes do
    throw (IO.userError s!"shared JSON changed checkpoint bytes at {path}")

/-- Interrupt after publishing the first record. Subsequent processes must reuse it; a missing completed record fails
instead of invoking its producer. -/
@[expose] def sharedJsonChild (directory : System.FilePath) (mode : String) : IO Unit := do
  IO.FS.createDirAll directory
  let objects := (Purelib.System.FilePath.join directory (System.FilePath.mk ("objects")))
  let first := (Purelib.System.FilePath.join directory (System.FilePath.mk ("first.json")))
  let bytes := "{\"value\":1}\n".toUTF8
  if mode == "crash" then
    if ← first.pathExists then throw (IO.userError "completed producer called again")
    SharedJson.write objects first bytes
    let pid ← IO.Process.getPID
    discard <| Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
    throw (IO.userError "shared JSON interruption unexpectedly returned")
  unless mode == "resume" || mode == "replay" do
    throw (IO.userError "unknown shared JSON child mode")
  requireBytes first bytes
  let second := (Purelib.System.FilePath.join directory (System.FilePath.mk ("second.json")))
  if mode == "resume" then SharedJson.write objects second bytes
  requireBytes second bytes
  unless 3 ≤ (← first.metadata).numLinks do
    throw (IO.userError "equal JSON records did not share an immutable object")
  println "PASS shared JSON restart: completed producer not called."

/-- Check immutable JSON sharing, collision handling and interrupted atomic-write recovery.

Verify unchanged retained objects, safe adoption and independent appendable logs. -/
@[expose] def sharedJsonSelfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then
    throw (IO.userError "shared JSON self-test requires a fresh directory")
  let executable := (← IO.appPath).toString
  let crash ← Process.output
    { cmd := executable, args := #["shared-json-child", directory.toString, "crash"] }
  unless crash.exitCode == 137 do
    throw (IO.userError s!"shared JSON expected SIGKILL, received {crash.exitCode}")
  for mode in ["resume", "replay"] do
    let output ← Process.output
      { cmd := executable, args := #["shared-json-child", directory.toString, mode] }
    unless output.exitCode == 0 do throw (IO.userError (output.stdout ++ output.stderr))
    IO.print output.stdout
  let objects := (Purelib.System.FilePath.join directory (System.FilePath.mk ("objects")))
  let first := (Purelib.System.FilePath.join directory (System.FilePath.mk ("first.json")))
  let second := (Purelib.System.FilePath.join directory (System.FilePath.mk ("second.json")))
  let oldBytes := "{\"value\":1}\n".toUTF8
  let newBytes := "{\"value\":2}\n".toUTF8
  SharedJson.write objects first newBytes
  requireBytes first newBytes
  requireBytes second oldBytes
  requireBytes (SharedJson.objectPath objects oldBytes) oldBytes
  -- Equal length, unequal bytes deliberately occupy the requested lookup key.
  let collisionBytes := "{\"value\":3}\n".toUTF8
  let collision := SharedJson.objectPath objects collisionBytes
  if let some parent := (Purelib.System.FilePath.parent collision) then IO.FS.createDirAll parent
  IO.FS.writeBinFile collision oldBytes
  let collisionTarget := (Purelib.System.FilePath.join directory (System.FilePath.mk ("collision.json")))
  SharedJson.write objects collisionTarget collisionBytes
  requireBytes collisionTarget collisionBytes
  requireBytes collision oldBytes
  -- Simulate a crash after publishing a temporary inode as an object. Reusing
  -- that pathname must unlink it before writing different bytes.
  let staleTarget := (Purelib.System.FilePath.join directory (System.FilePath.mk ("stale.json")))
  let stale := System.FilePath.mk (staleTarget.toString ++ ".shared-write.pending")
  IO.FS.hardLink (SharedJson.objectPath objects oldBytes) stale
  let staleBytes := "{\"value\":4}\n".toUTF8
  SharedJson.write objects staleTarget staleBytes
  requireBytes staleTarget staleBytes
  requireBytes second oldBytes
  requireBytes (SharedJson.objectPath objects oldBytes) oldBytes
  let adopted := (Purelib.System.FilePath.join directory (System.FilePath.mk ("adopted.json")))
  let adoptBytes := "{\"value\":5}\n".toUTF8
  atomicBytes adopted adoptBytes
  SharedJson.write objects adopted adoptBytes
  requireBytes adopted adoptBytes
  requireBytes (SharedJson.objectPath objects adoptBytes) adoptBytes
  unless 2 ≤ (← adopted.metadata).numLinks do
    throw (IO.userError "existing JSON was not adopted without copying")
  -- The common writer must leave appendable records independent even when
  -- CCL_CHECKPOINT_SHARED_JSON is enabled for the enclosing regression.
  let logA := (Purelib.System.FilePath.join directory (System.FilePath.mk ("a.jsonl")))
  let logB := (Purelib.System.FilePath.join directory (System.FilePath.mk ("b.jsonl")))
  atomicBytes logA oldBytes
  atomicBytes logB oldBytes
  IO.FS.withFile logA .append fun handle => handle.write newBytes
  requireBytes logB oldBytes
  requireBytes logA (oldBytes ++ newBytes)
  println
    "PASS immutable JSON byte equality, collision rejection, atomic replacement, interrupted temporary recovery, \
      adoption and independent append logs."

/-- Run the checkpoint persistence, exact source-boundary and state-threading regression suite. -/
@[expose] def selfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then
    throw (IO.userError "checkpoint self-test requires a fresh directory")
  sharedJsonSelfTest ((Purelib.System.FilePath.join directory (System.FilePath.mk ("shared-json"))))
  generate ((Purelib.System.FilePath.join directory (System.FilePath.mk ("generated"))))
  checkModel ((Purelib.System.FilePath.join directory (System.FilePath.mk ("generated")))) 0
  let executable := (← IO.appPath).toString
  for mode in ["resume-without-source", "replay"] do
    let output ← Process.output
      { cmd := executable, args := #[mode, ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("generated")))).toString] }
    unless output.exitCode == 0 do throw (IO.userError (output.stdout ++ output.stderr))
    IO.print output.stdout
  phasedSelfTest ((Purelib.System.FilePath.join directory (System.FilePath.mk ("phased"))))
  cellsSelfTest ((Purelib.System.FilePath.join directory (System.FilePath.mk ("cells"))))
  certifiedCellsSelfTest ((Purelib.System.FilePath.join directory (System.FilePath.mk ("certified-cells"))))
  stateful ((Purelib.System.FilePath.join directory (System.FilePath.mk ("stateful"))))
  certifiedObservationSelfTest ((Purelib.System.FilePath.join directory (System.FilePath.mk ("certified-observation"))))
  partialReply ((Purelib.System.FilePath.join directory (System.FilePath.mk ("partial-reply"))))
  importSelfTest ((Purelib.System.FilePath.join directory (System.FilePath.mk ("import"))))
  println "PASS all checkpoint persistence, state-threading and source-boundary regressions."

end IntegrationCheckpointHarness

open scoped Purelib.Data.Int.Decimal in
/-- Dispatch the requested checkpoint generation, replay, import or regression phase. -/
@[expose] def main (arguments : List String) : IO Unit :=
  match arguments with
  | ["generate", directory] => IntegrationCheckpointHarness.generate directory
  | ["resume-without-source", directory] => IntegrationCheckpointHarness.resumeWithoutSource directory
  | ["phased", directory] => IntegrationCheckpointHarness.phasedSelfTest directory
  | ["phased-child", directory] => IntegrationCheckpointHarness.phasedChild directory
  | ["checked-child", directory] => IntegrationCheckpointHarness.phasedChild directory true
  | ["cells", directory] => IntegrationCheckpointHarness.cellsSelfTest directory
  | ["certified-cells", directory] => IntegrationCheckpointHarness.certifiedCellsSelfTest directory
  | ["certified-cells-child", directory, mode] => IntegrationCheckpointHarness.certifiedCellsChild directory mode
  | ["stateful", directory] => IntegrationCheckpointHarness.stateful directory
  | ["certified-observation", directory] => IntegrationCheckpointHarness.certifiedObservationSelfTest directory
  | ["certified-observation-child", directory, mode] =>
      IntegrationCheckpointHarness.certifiedObservationChild directory mode
  | ["partial-reply", directory] => IntegrationCheckpointHarness.partialReply directory
  | ["import-selftest", directory] => IntegrationCheckpointHarness.importSelfTest directory
  | ["shared-json", directory] => IntegrationCheckpointHarness.sharedJsonSelfTest directory
  | ["shared-json-child", directory, mode] => IntegrationCheckpointHarness.sharedJsonChild directory mode
  | ["selftest", directory] => IntegrationCheckpointHarness.selfTest directory
  | ["check-model", directory, index] =>
      match (Purelib.Data.String.toNat? index) with
      | some index => IntegrationCheckpointHarness.checkModel directory index
      | none => throw (IO.userError "model index must be a natural number")
  | ["cells-child", directory, mode] => IntegrationCheckpointHarness.cellsChild directory mode
  | ["marker-child"] => println s!"marker calibration: {(IntegrationCheckpointHarness.markedSource ()).errorScale.num}"
  | ["replay", directory] => IntegrationCheckpoint.replayOnly directory 8
  | _ => throw (IO.userError
    "usage: integration_checkpoint_harness generate|resume-without-source|phased|cells|certified-cells|\
      certified-observation|stateful|partial-reply|import-selftest|shared-json|selftest|replay DIRECTORY | check-model \
      DIRECTORY INDEX")
