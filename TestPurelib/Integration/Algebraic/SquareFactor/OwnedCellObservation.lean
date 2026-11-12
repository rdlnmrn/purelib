module

import Purelib.Integration.Algebraic.SquareFactor.OwnedCells.Observation
import Purelib.Integration.Algebraic.SquareFactor.OwnedCells.Compilation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor

/-! # Original prepared-edge root and coefficient callbacks -/

namespace TestPurelib.Integration.Algebraic.SquareFactor.OwnedCellObservation

open Purelib
open Purelib.Integration.Algebraic.SquareFactor
open Purelib.Riemann.Branches

/-- Check every retained edge's source calls, exact replay, and early wrong-position rejection. -/
private def checkCompilation {polynomial : GaussianPolynomial}
    {request : Request}
    {prepared : Prepared polynomial request}
    {segment : PathInput.Segment} {data : PathInput.Data prepared segment} {safe : data.Safe}
    (edges : List (OwnedCells.Edge safe)) : IO Unit := do
  let computation := OwnedCells.Compilation.compile edges
  let recorded := computation.run OwnedCells.Compilation.answer
  match recorded.value with
  | .error _ => throw (IO.userError "ordered cell compilation rejected an original source reply")
  | .ok cells =>
      unless cells.val.length == edges.length && recorded.trace.length == 3 * edges.length do
        throw (IO.userError "ordered cell compilation omitted a cell or one of its original source calls")
      match computation.replayExact recorded.trace with
      | .ok (.ok replayed) =>
          unless decide (replayed.val.map (fun cell => cell.model.center) =
              cells.val.map (fun cell => cell.model.center)) do
            throw (IO.userError "ordered cell replay changed a cached original coefficient")
      | _ => throw (IO.userError "ordered cell compilation failed exact replay")
  match edges with
  | first :: second :: remaining =>
      let wrong := (OwnedCells.Compilation.compile (first :: second :: remaining)).run
        (fun _ => OwnedCells.Compilation.answer (.later (.first .root)))
      match wrong.value with
      | .error .expectedFirst =>
          unless wrong.trace.length == 1 do
            throw (IO.userError "wrong cell position did not stop before later callbacks")
      | _ => throw (IO.userError "ordered cell compilation accepted a reply from a different retained position")
  | _ => throw (IO.userError "ordered cell fixture must retain at least two original edges")

/-- Check the actual retained original root and both polynomial replies used to assemble one prepared edge model. -/
private def check {polynomial : GaussianPolynomial}
    {request : Request}
    {prepared : Prepared polynomial request}
    {segment : PathInput.Segment} {data : PathInput.Data prepared segment} {safe : data.Safe}
    (edge : OwnedCells.Edge safe) : IO Unit := do
  let computation := OwnedCells.Edge.Observation.model edge
  let recorded := computation.run (OwnedCells.Edge.Observation.answer edge)
  match recorded.value, recorded.trace with
  | .ok model, [rootEntry, numeratorEntry, denominatorEntry] =>
      let model := model.val
      match rootEntry.reply, numeratorEntry.reply, denominatorEntry.reply with
      | .root root, .numerator numerator, .denominator denominator =>
          unless decide (model.centerRoot = root.reading.val) &&
              decide (model.center = numerator.value / denominator.value / root.reading.val) do
            throw (IO.userError "original cell assembly lost its retained root or polynomial values")
          match computation.replayExact recorded.trace with
          | .ok (.ok replayed) =>
              let replayed := replayed.val
              unless decide (replayed.centerRoot = model.centerRoot) && decide (replayed.center = model.center) do
                throw (IO.userError "original cell replay changed its exact retained root or coefficient")
          | _ => throw (IO.userError "original cell replay rejected its source-generated replies")
      | _, _, _ => throw (IO.userError "original cell callback trace lost its actual operation tags")
  | _, _ => throw (IO.userError "original cell construction failed or omitted a source callback")
  let wrong := computation.run (fun _ => OwnedCells.Edge.Observation.answer edge .numerator)
  match wrong.value with
  | .error (.operation .root .numerator _) =>
      unless wrong.trace.length == 1 do
        throw (IO.userError "wrong root-operation reply failed to stop before subsequent source callbacks")
  | _ => throw (IO.userError "original cell handler failed to identify its wrong-operation reply")

/-- Inspect the first actual prepared step while retaining its exact dependent endpoint and root owner. -/
private def checkRun {polynomial : GaussianPolynomial}
    {request : Request}
    {prepared : Prepared polynomial request}
    {segment : PathInput.Segment} {data : PathInput.Data prepared segment} {safe : data.Safe}
    {left : PathContinuation.Endpoint}
    {owner : PathContinuation.Owner (data.radicand.parameterPolynomial.eval
      ((PathContinuation.clearSegment safe).pointAt left.parameter))} :
    PreparedSheetContinuation.Subdivision (PathContinuation.clearSegment safe) (PathContinuation.within safe)
      left owner → IO Unit
  | .stop _ _ => throw (IO.userError "owned cell fixture has no actual prepared continuation edge")
  | .next left owner step cached ordered small _ =>
      check (safe := safe) (OwnedCells.Edge.mk left owner step cached ordered small)

/-- Execute the real prepared constant-path edge and its original root-owner callbacks. -/
public def run : IO Unit := do
  match PathInput.prepare ⟨[1]⟩ (.original 0) ⟨0, 1⟩ with
  | .error _ => throw (IO.userError "owned cell fixture failed original coefficient preparation")
  | .ok prepared =>
      match prepared.outcome with
      | .endpointObstruction _ _ => throw (IO.userError "owned cell fixture has an unexpected endpoint obstruction")
      | .inconclusive _ => throw (IO.userError "owned cell fixture has uncertified original path margins")
      | .accepted safe =>
          let mesh := PathContinuation.selectMesh safe ⟨0, by decide⟩ (1 / 2) (by decide) 0
          checkRun mesh.run
          checkCompilation (OwnedCells.edges mesh.run)
  IO.print "original cell callbacks: retained root and polynomial caches, replay and typed early rejection passed\n"

end TestPurelib.Integration.Algebraic.SquareFactor.OwnedCellObservation
