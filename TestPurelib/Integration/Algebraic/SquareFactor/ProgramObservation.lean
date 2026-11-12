module

import Purelib.Integration.Algebraic.SquareFactor.IntegrationProgram.Observation
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor

/-! # Actual chronological layer construction and cached model assembly -/

namespace TestPurelib.Integration.Algebraic.SquareFactor.ProgramObservation

open Purelib
open Purelib.Integration.Algebraic.SquareFactor

/-- Check two original successors, their chronological trace, exact replay and wrong-index early rejection. -/
private def check {polynomial : GaussianPolynomial}
    {request : Request}
    {prepared : Prepared polynomial request}
    {segment : PathInput.Segment} {data : PathInput.Data prepared segment} {safe : data.Safe}
    (start : IntegrationLayers.Layer safe 0) : IO Unit := do
  let computation := IntegrationProgram.Observation.layerFrom start 2
  let recorded := computation.run IntegrationProgram.Observation.answer
  match recorded.value with
  | .error _ => throw (IO.userError "chronological layer construction rejected its original source reply")
  | .ok retained =>
      let layer := retained.val
      unless layer.cells.length == 2 ^ layer.depth && decide (layer.allowance ≤ 1 / 16) do
        throw (IO.userError "second chronological layer lost its original geometry or quarter-radius target")
      let indices := recorded.trace.map fun entry => match entry.query with | .next index _ _ => index
      let later := recorded.trace.dropWhile fun entry => match entry.query with | .next index _ _ => index == 0
      match later with
      | firstLater :: _ =>
          match firstLater.query with
          | .next 1 request _ =>
              let firstCount := 1 + 3 * request.parent.val.cells.length
              let secondCount := 1 + 3 * layer.cells.length
              unless indices == List.replicate firstCount 0 ++ List.replicate secondCount 1 do
                throw (IO.userError "chronological trace lost the actual first-to-second parent or source counts")
          | _ => throw (IO.userError "chronological sequence omitted its original second-step request")
      | [] => throw (IO.userError "chronological sequence omitted the original second-step source calls")
      match computation.replayExact recorded.trace with
      | .ok (.ok replayed) =>
          unless replayed.val.depth == layer.depth && decide (replayed.val.allowance = layer.allowance) &&
              decide (replayed.val.cells.map (fun (cell : OwnedCells.Cell safe) => cell.model.center) =
                layer.cells.map (fun (cell : OwnedCells.Cell safe) => cell.model.center)) do
            throw (IO.userError "chronological replay changed the original returned layer caches")
      | _ => throw (IO.userError "chronological layer replay failed its actual saved source trace")
      let cached := IntegrationProgram.Observation.ModelRealization.ofLayer retained
      unless decide (cached.val.sample = layer.model.integralSample) &&
          decide (cached.val.allowance = layer.model.aggregateAllowance) do
        throw (IO.userError "stage-cache assembly lost its actual returned layer model")
      match recorded.trace.reverse with
      | last :: _ =>
          let wrong := computation.run (fun _ => last.reply)
          match wrong.value with
          | .error (.index 0 1 _) =>
              unless wrong.trace.length == 1 do
                throw (IO.userError "wrong chronological index did not stop before any successor callback")
          | _ => throw (IO.userError "chronological layer construction accepted a reply from another original step")
      | [] => throw (IO.userError "chronological layer construction omitted its source requests")

/-- Construct the exact original initial layer once before checking its actual two-successor sequence. -/
private def checkSafe {polynomial : GaussianPolynomial}
    {request : Request}
    {prepared : Prepared polynomial request}
    {segment : PathInput.Segment} {data : PathInput.Data prepared segment} (safe : data.Safe) : IO Unit := do
  let resolution := Accuracy.resolve safe 1 (by decide) 1 (by decide)
  let sheet : Fin 2 := ⟨0, by decide⟩
  let initial := IntegrationLayers.Observation.initial safe sheet resolution rfl
  let recorded := initial.run (IntegrationLayers.Observation.initialAnswer safe sheet resolution)
  match (recorded.value : Except OwnedCells.Preparation.Invalidity
      (IntegrationLayers.Observation.InitialRealization safe sheet)) with
  | .error _ => throw (IO.userError "chronological fixture failed original initial-layer preparation")
  | .ok retained => check retained.val

/-- Run chronological original layer construction on a prepared constant-position path. -/
public def run : IO Unit := do
  match PathInput.prepare ⟨[1]⟩ (.original 0) ⟨0, 0⟩ with
  | .error _ => throw (IO.userError "chronological fixture failed original coefficient preparation")
  | .ok prepared =>
      match prepared.outcome with
      | .endpointObstruction _ _ => throw (IO.userError "chronological fixture has an endpoint obstruction")
      | .inconclusive _ => throw (IO.userError "chronological fixture lacks certified original path margins")
      | .accepted safe => checkSafe safe
  IO.print "chronological layers: two successors, cached model, replay and wrong-index rejection passed\n"

end TestPurelib.Integration.Algebraic.SquareFactor.ProgramObservation
