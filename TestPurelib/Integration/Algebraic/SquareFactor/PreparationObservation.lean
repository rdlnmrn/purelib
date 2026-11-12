module

import Purelib.Integration.Algebraic.SquareFactor.PathContinuation.Observation
import Purelib.Integration.Algebraic.SquareFactor.OwnedCells.Preparation
import Purelib.Integration.Algebraic.SquareFactor.IntegrationLayers.Observation
import Purelib.Integration.Algebraic.SquareFactor.IntegrationProgram
import Purelib.Integration.Algebraic.SquareFactor.Accuracy
import Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.Compilation
import Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.Observation
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.RootIsolation.Track.Observation
import Purelib.RootIsolation.CCL.Persistent.Terminal.Observation.Refinement
import Purelib.RootIsolation.CCL.Persistent.Terminal.Observation.Pair
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.RootIsolation.CCL.Persistent.Terminal
open Purelib.RootIsolation.Track.Observation

/-! # Actual mesh preparation and retained winding-refinement callbacks -/

namespace TestPurelib.Integration.Algebraic.SquareFactor.PreparationObservation

open Purelib
open Purelib.Integration.Algebraic.SquareFactor

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

/-- Check the retained parent's actual next accuracy target and exact replay of the returned refinement caches. -/
private def checkNext {polynomial : SquareFactor.GaussianPolynomial}
    {request : SquareFactor.Request}
    {prepared : SquareFactor.Prepared polynomial request}
    {segment : PathInput.Segment} {data : PathInput.Data prepared segment} {safe : data.Safe} {index : Nat}
    (parent : IntegrationLayers.Layer safe index) : IO Unit := do
  let target := Approximation.Rational.Geometric.Basic.quarterRadius 1 (index + 1)
  have positive := Approximation.Rational.Geometric.Basic.quarterRadius_pos
    (by decide : (0 : OwnedCells.Coordinate) < 1) (index + 1)
  let resolution := Accuracy.resolve safe 1 (by decide) target positive
  let computation := IntegrationLayers.Observation.next parent resolution rfl
  let recorded := computation.run (IntegrationLayers.Observation.nextAnswer parent resolution)
  match recorded.value with
  | .error _ => throw (IO.userError "next layer rejected its original selected-bank or cell receipt")
  | .ok retained =>
      let layer := retained.val.layer
      unless layer.cells.length == 2 ^ layer.depth && layer.model.cells.length == layer.cells.length &&
          recorded.trace.length == 1 + 3 * layer.cells.length && decide (layer.allowance ≤ target) do
        throw (IO.userError "next layer lost its parent's geometry, next-target accuracy or complete source calls")
      match computation.replayExact recorded.trace with
      | .ok (.ok replayed) =>
          unless replayed.val.layer.depth == layer.depth &&
              decide (replayed.val.layer.allowance = layer.allowance) &&
              decide (replayed.val.layer.cells.map (fun (cell : OwnedCells.Cell safe) => cell.model.center) =
                layer.cells.map (fun (cell : OwnedCells.Cell safe) => cell.model.center)) do
            throw (IO.userError "next-layer replay changed its original refinement depth, allowance or cached model")
      | _ => throw (IO.userError "next-layer replay rejected its actual retained refinement source trace")

/-- Build the exact initial layer and refine that returned original parent at its next accuracy target. -/
private def checkNextFromSafe {polynomial : SquareFactor.GaussianPolynomial}
    {request : SquareFactor.Request}
    {prepared : SquareFactor.Prepared polynomial request}
    {segment : PathInput.Segment} {data : PathInput.Data prepared segment} (safe : data.Safe) : IO Unit := do
  let resolution := Accuracy.resolve safe 1 (by decide) 1 (by decide)
  let sheet : Fin 2 := ⟨0, by decide⟩
  let computation := IntegrationLayers.Observation.initial safe sheet resolution rfl
  let recorded := computation.run (IntegrationLayers.Observation.initialAnswer safe sheet resolution)
  match (recorded.value : Except OwnedCells.Preparation.Invalidity
      (IntegrationLayers.Observation.InitialRealization safe sheet)) with
  | .error _ => throw (IO.userError "next-layer fixture failed its actual initial-layer construction")
  | .ok parent => checkNext (safe := safe) (index := 0) parent.val

/-- Run actual successor refinement of a prepared constant-position path without changing its original owners. -/
private def checkNextFixture : IO Unit := do
  match PathInput.prepare ⟨[1]⟩ (.original 0) ⟨0, 0⟩ with
  | .error _ => throw (IO.userError "next-layer fixture failed original coefficient preparation")
  | .ok prepared =>
      match prepared.outcome with
      | .endpointObstruction _ _ => throw (IO.userError "next-layer fixture has an endpoint obstruction")
      | .inconclusive _ => throw (IO.userError "next-layer fixture lacks certified path margins")
      | .accepted safe => checkNextFromSafe safe

/-- Check original selected mesh-bank construction, all cell calls, exact replay and early wrong-stage rejection. -/
private def checkSynchronization {polynomial : SquareFactor.GaussianPolynomial}
    {request : SquareFactor.Request}
    {prepared : SquareFactor.Prepared polynomial request}
    {segment : PathInput.Segment} {data : PathInput.Data prepared segment} {safe : data.Safe}
    (parents : List (OwnedCells.Cell safe)) : IO Unit := do
  let computation := UniformRefinement.Observation.synchronize parents (1 / 2) (by decide) 0
  let recorded := computation.run (UniformRefinement.Observation.answer parents (1 / 2) (by decide) 0)
  match recorded.value with
  | .error _ => throw (IO.userError "mesh-bank compilation rejected an original cell reply")
  | .ok retained =>
      let cells := retained.val.expansion.cells
      unless cells.length == parents.length * 2 ^ retained.val.depth &&
          recorded.trace.length == 1 + 3 * cells.length do
        throw (IO.userError "mesh-bank assembly lost a parent block, dyadic child or source request")
      match computation.replayExact recorded.trace with
      | .ok (.ok replayed) =>
          unless decide (replayed.val.expansion.cells.map (fun (cell : OwnedCells.Cell safe) => cell.model.center) =
              cells.map (fun (cell : OwnedCells.Cell safe) => cell.model.center)) do
            throw (IO.userError "mesh-bank replay changed an original cached coefficient")
      | _ => throw (IO.userError "mesh-bank replay rejected the actual original cell trace")
      match recorded.trace with
      | first :: second :: _ =>
          match first.reply, second.query with
          | .selected original, .cell cached _ =>
              unless original.val.depth == cached.val.depth && cached.val.depth == retained.val.depth do
                throw (IO.userError "cell callback lost its actual selected mesh-bank depth")
              let wrong := computation.run (fun _ => first.reply)
              match wrong.value with
              | .error .expectedCell =>
                  unless wrong.trace.length == 2 do
                    throw (IO.userError "wrong-stage mesh-bank reply executed later cell callbacks")
              | _ => throw (IO.userError "mesh-bank construction accepted selection data as a cell reading")
          | _, _ => throw (IO.userError "mesh-bank trace lost selection before its first actual cell request")
      | _ => throw (IO.userError "mesh-bank fixture has no actual selected cell requests")

/-- Check actual initial-layer model assembly and replay from its original unit-accuracy request. -/
private def checkInitialLayer {polynomial : SquareFactor.GaussianPolynomial}
    {request : SquareFactor.Request}
    {prepared : SquareFactor.Prepared polynomial request}
    {segment : PathInput.Segment} {data : PathInput.Data prepared segment} (safe : data.Safe) : IO Unit := do
  let resolution := Accuracy.resolve safe 1 (by decide) 1 (by decide)
  let computation := IntegrationLayers.Observation.initial safe ⟨0, by decide⟩ resolution rfl
  let recorded := computation.run (IntegrationLayers.Observation.initialAnswer safe ⟨0, by decide⟩ resolution)
  match recorded.value with
  | .error _ => throw (IO.userError "initial layer rejected its original mesh or cell replies")
  | .ok retained =>
      let layer := retained.val
      let cached := IntegrationProgram.cachedFrom layer
      let stage := cached.stage 0
      unless decide (stage.sample = layer.model.integralSample) &&
          decide (stage.allowance = layer.model.aggregateAllowance) do
        throw (IO.userError "cached program lost the actual retained initial model's sample or allowance")
      unless layer.cells.length == 2 ^ layer.depth && layer.model.cells.length == layer.cells.length &&
          recorded.trace.length == 2 + 3 * layer.cells.length && decide (layer.allowance ≤ 1) do
        throw (IO.userError "initial layer lost its original geometry, model, allowance or source calls")
      match computation.replayExact recorded.trace with
      | .ok (.ok replayed) =>
          unless replayed.val.depth == layer.depth && decide (replayed.val.allowance = layer.allowance) &&
              decide (replayed.val.cells.map (fun (cell : OwnedCells.Cell safe) => cell.model.center) =
                layer.cells.map (fun (cell : OwnedCells.Cell safe) => cell.model.center)) do
            throw (IO.userError "initial layer replay changed its retained mesh, allowance or model caches")
      | _ => throw (IO.userError "initial layer failed replay from its actual preparation and cell replies")
      checkSynchronization layer.cells

/-- Check whole preparation and ordered cell compilation on the actual safe path, including exact cached replay. -/
private def checkPreparedRun {polynomial : SquareFactor.GaussianPolynomial}
    {request : SquareFactor.Request}
    {prepared : SquareFactor.Prepared polynomial request}
    {segment : PathInput.Segment} {data : PathInput.Data prepared segment} (safe : data.Safe) : IO Unit := do
  let computation := OwnedCells.Preparation.compile safe ⟨0, by decide⟩ (1 / 2) (by decide) 0
  let oracle := OwnedCells.Preparation.answer safe ⟨0, by decide⟩ (1 / 2) (by decide) 0
  let recorded := computation.run oracle
  match recorded.value with
  | .error _ => throw (IO.userError "whole prepared run rejected an original preparation or cell reply")
  | .ok retained =>
      unless recorded.trace.length == 2 + 3 * retained.val.cells.length do
        throw (IO.userError "whole prepared run omitted initial isolation, mesh preparation or a cell callback")
      match recorded.trace with
      | _ :: _ :: firstCell :: _ =>
          match firstCell.query with
          | .cell cached _ =>
              unless cached.val.depth == retained.val.depth do
                throw (IO.userError "cell request lost the exact returned prepared mesh")
          | _ => throw (IO.userError "whole prepared run did not compile the retained mesh after preparation")
      | _ => throw (IO.userError "whole prepared run has an incomplete callback trace")
      match computation.replayExact recorded.trace with
      | .ok (.ok replayed) =>
          unless replayed.val.depth == retained.val.depth &&
              decide (replayed.val.cells.map (fun (cell : OwnedCells.Cell safe) => cell.model.center) =
                retained.val.cells.map (fun (cell : OwnedCells.Cell safe) => cell.model.center)) do
            throw (IO.userError "whole prepared replay changed the actual mesh or cached cell models")
      | _ => throw (IO.userError "whole prepared replay rejected its original cached construction")
  let rejected := computation.run (fun _ => oracle (.prepare .isolate))
  match rejected.value with
  | .error (.preparation .expectedMesh) =>
      unless rejected.trace.length == 2 do
        throw (IO.userError "failed mesh preparation executed a later cell callback")
  | _ => throw (IO.userError "whole prepared run accepted an isolation reply at its mesh-preparation boundary")

/-- Check exact cached track replay and rejection of a receipt for another radius. -/
private def checkTrack {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) : IO Unit := do
  let question := Question.ofCurrent track.initial (1 / 16) (by decide)
  let refine := RootIsolation.Track.Observation.request track track.initial question
  let refinement := refine.run (RootIsolation.Track.Observation.answer track track.initial)
  match refinement.value with
  | .error _ => throw (IO.userError "track refinement rejected its actual original callback")
  | .ok state =>
      unless decide (state.val.box.diagonalSq ≤ (1 / 16) ^ 2) && refinement.trace.length == 1 do
        throw (IO.userError "track callback lost its requested accuracy or actual refinement receipt")
      match refine.replayExact refinement.trace with
      | .ok (.ok replayed) =>
          unless decide (replayed.val.box.diagonalSq = state.val.box.diagonalSq) do
            throw (IO.userError "track replay changed the original cached refinement")
      | _ => throw (IO.userError "track replay rejected its actual refinement receipt")
  let different := Question.ofCurrent track.initial (1 / 8) (by decide)
  let mismatch := refine.run
    (fun _ => RootIsolation.Track.Observation.answer track track.initial different)
  match mismatch.value with
  | .ok _ => throw (IO.userError "track refinement accepted a receipt for another radius")
  | .error invalid =>
      unless decide (invalid.expected.epsilon = 1 / 16) &&
          decide (invalid.reported.epsilon = 1 / 8) do
        throw (IO.userError "track invalidity lost its actual expected and reported radii")

/-- Check complete terminal point refinement and exact cached replay at the same state. -/
private def checkPoint {p : CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : RootIsolation.CCL.Persistent.State p ambient) : IO Unit := do
  let terminal := Observation.Refinement.resolvePoint
    degreePositive track current 0
  let terminalOracle :=
    Observation.Refinement.answer track current
  let resolved := terminal.run terminalOracle
  match resolved.value with
  | .error _ => throw (IO.userError "terminal point rejected its actual evaluator or track receipt")
  | .ok retained => match retained.val with
    | .exact _ => throw (IO.userError "zero was falsely returned as the nonzero radicand's root")
    | .excluded next _ _ _ =>
      unless decide (next.word = current.word) &&
          decide (¬next.numerical.box.Contains 0) && resolved.trace.length == 2 do
        throw (IO.userError "terminal point lost its prefix, exclusion or displayed refinement")
      match terminal.replayExact resolved.trace with
      | .ok (.ok retained) => match retained.val with
        | .excluded replayed _ _ _ =>
          unless decide (replayed.word = next.word) &&
              decide (replayed.numerical.box.diagonalSq = next.numerical.box.diagonalSq) do
            throw (IO.userError "terminal replay lost its same cached winding state")
        | _ => throw (IO.userError "terminal replay changed its original exclusion outcome")
      | _ => throw (IO.userError "terminal replay rejected its evaluator/refinement trace")
  let differentReceipt := terminal.run fun question =>
    match question with
    | .evaluate _ => terminalOracle question
    | .refine wanted =>
        let other := Question.ofRetained wanted.current
          (wanted.epsilon / 2)
          (Data.Rat.Fraction.Order.Field.div_pos_direct wanted.positive (by decide))
        .refined (RootIsolation.Track.Observation.answer track current.numerical other)
  match differentReceipt.value with
  | .error (.request _) => pure ()
  | _ => throw (IO.userError "terminal point accepted a cached refinement for a different radius")

/-- Check chronological pair refinement and callback-free preparation for the empty word. -/
private def checkPair {p : CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : RootIsolation.CCL.Persistent.State p ambient) : IO Unit := do
  let pair := Observation.Pair.resolvePair
    degreePositive track current 0 0
  let pairOracle := Observation.Pair.answer
    degreePositive track current 0
  let paired := pair.run pairOracle
  match paired.value with
  | .ok (.excluded next _ _ _ _) =>
      unless decide (next.word = current.word) && paired.trace.length == 4 do
        throw (IO.userError "joint terminal resolution lost its prefix or either conditional callback")
      match paired.trace with
      | [_, firstRefinement, _, secondRefinement] =>
          match firstRefinement.reply, secondRefinement.reply with
          | .first (.refined first), .second (.refined second) =>
              unless decide
                  (second.question.current.val.box.diagonalSq = first.state.box.diagonalSq) do
                throw (IO.userError "second terminal callback restarted instead of using the retained state")
          | _, _ => throw (IO.userError "joint terminal trace lost its staged winding-state receipts")
      | _ => throw (IO.userError "joint terminal trace has the wrong evaluator/refinement ordering")
      match pair.replayExact paired.trace with
      | .ok (.ok (.excluded replayed _ _ _ _)) =>
          unless decide (replayed.word = next.word) &&
              decide (replayed.numerical.box.diagonalSq = next.numerical.box.diagonalSq) do
            throw (IO.userError "joint terminal replay changed the final retained winding state")
      | _ => throw (IO.userError "joint terminal replay rejected its retained callback trace")
  | _ => throw (IO.userError "joint terminal resolution failed its actual nonroot inputs")
  let preparation := Observation.Pair.prepare
    degreePositive track current
  let empty := preparation.run (Observation.Pair.answer
    degreePositive track current (Observation.Pair.leftCandidate
      current (Data.CCL.Encoding.Parser.State.parse current.word).phase))
  unless empty.trace.isEmpty do
    throw (IO.userError "nonterminal empty prefix invoked a polynomial or winding callback")

/-- Run actual isolation/preparation and the original owner's track refinement, then replay their cached replies. -/
public def run : IO Unit := do
  checkNextFixture
  match PathInput.prepare ⟨[1]⟩ (.original 0) ⟨0, 1⟩ with
  | .error _ => throw (IO.userError "preparation observation fixture failed coefficient preparation")
  | .ok prepared =>
      match prepared.outcome with
      | .endpointObstruction _ _ => throw (IO.userError "preparation observation fixture has an endpoint obstruction")
      | .inconclusive _ => throw (IO.userError "preparation observation fixture lacks certified path margins")
      | .accepted safe =>
          checkInitialLayer safe
          checkPreparedRun safe
          let computation := PathContinuation.Observation.prepare safe ⟨0, by decide⟩ (1 / 2) (by decide) 0
          let oracle := PathContinuation.Observation.answer safe ⟨0, by decide⟩ (1 / 2) (by decide) 0
          let recorded := computation.run oracle
          match recorded.value, recorded.trace with
          | .ok selected, [ownerEntry, meshEntry] =>
              match ownerEntry.reply, meshEntry.reply with
              | .owner cached, .mesh mesh _ =>
                  unless selected.depth == mesh.depth && selected.run.stepCount == 2 ^ selected.depth do
                    throw (IO.userError "mesh preparation lost its original retained subdivision or request depth")
                  match computation.replayExact recorded.trace with
                  | .ok (.ok replayed) =>
                      unless replayed.depth == selected.depth && replayed.run.stepCount == selected.run.stepCount do
                        throw (IO.userError "mesh replay lost its exact prepared subdivision")
                  | _ => throw (IO.userError "mesh replay rejected its original owner and prepared mesh")
                  let wrong := computation.run (fun _ => meshEntry.reply)
                  match wrong.value with
                  | .error .expectedOwner =>
                      unless wrong.trace.length == 1 do
                        throw (IO.userError "wrong initial-isolation reply did not stop before preparation")
                  | _ => throw (IO.userError "mesh preparation accepted a wrong-operation reply")
                  let track := cached.val.track
                  checkTrack track
                  let current := RootIsolation.CCL.Persistent.State.initial track.initial
                  have degreePositive : 0 <
                      (Polynomial.Power.Gaussian.rootPolynomial _
                        Riemann.RootContinuation.SquareRootDegree.degreeTwo).natDegree := by
                    rewrite [Polynomial.Power.Gaussian.rootPolynomial_degree]
                    exact Riemann.RootContinuation.SquareRootDegree.degreeTwo.positive
                  checkPoint degreePositive track current
                  checkPair degreePositive track current
              | _, _ => throw (IO.userError "prepared mesh trace lost its original isolation/preparation tags")
          | _, _ => throw (IO.userError "mesh observation failed or omitted a root/preparation callback")
  IO.print "owned preparation: isolated owner, actual mesh, cached track refinement, replay and invalidity passed\n"

end TestPurelib.Integration.Algebraic.SquareFactor.PreparationObservation
