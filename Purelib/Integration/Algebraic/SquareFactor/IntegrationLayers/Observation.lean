module

public import Purelib.Integration.Algebraic.SquareFactor.IntegrationLayers
public import Purelib.Integration.Algebraic.SquareFactor.OwnedCells.Preparation
public import Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.Observation
import Purelib.Integration.Algebraic.SquareFactor.Accuracy

open Purelib.Approximation.Rational.Geometric

/-!
# Initial integration layers from recorded original preparation

The supplied unit-accuracy resolution is the original retained request.
Its whole-run construction displays initial isolation, mesh preparation and
every cell root and polynomial evaluation. Layer assembly consumes that
same returned run through the original named constructor, preserving its
cached cells, model, geometry, depth and allowance.
-/

public section

namespace Purelib.Integration.Algebraic.SquareFactor.IntegrationLayers

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Computation.Query

namespace Observation

variable {polynomial : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request}
  {prepared : SquareFactor.Prepared polynomial request} {segment : PathInput.Segment}
  {data : PathInput.Data prepared segment}

/-- The original unit-accuracy layer together with identity of its complete retained cell and model caches. -/
abbrev InitialRealization (safe : data.Safe) (sheet : Fin 2) :=
  {layer : Layer safe 0 // layer = initial safe sheet}

/-- The whole-run source questions at the exact supplied original unit-accuracy resolution. -/
abbrev InitialQuestion (safe : data.Safe) (sheet : Fin 2) (resolution : Accuracy.Resolution data 1 1) :=
  OwnedCells.Preparation.Question safe sheet resolution.rootDiameter
    resolution.rootDiameterPositive resolution.minimumDepth

/-- Original owner, mesh and cell replies at the same retained unit-accuracy request. -/
abbrev InitialReply (safe : data.Safe) (sheet : Fin 2) (resolution : Accuracy.Resolution data 1 1) :=
  OwnedCells.Preparation.Reply safe sheet resolution.rootDiameter
    resolution.rootDiameterPositive resolution.minimumDepth

/-- Execute the displayed source request using the supplied retained resolution, without computing another request. -/
def initialAnswer (safe : data.Safe) (sheet : Fin 2) (resolution : Accuracy.Resolution data 1 1) :
    InitialQuestion safe sheet resolution → InitialReply safe sheet resolution :=
  OwnedCells.Preparation.answer safe sheet resolution.rootDiameter
    resolution.rootDiameterPositive resolution.minimumDepth

/-- Assemble the same original initial layer from the returned whole run and its retained construction certificate. -/
private def assemble (safe : data.Safe) (sheet : Fin 2) (resolution : Accuracy.Resolution data 1 1)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) 1 (by decide))
    (retained : OwnedCells.Preparation.Realization safe sheet resolution.rootDiameter
      resolution.rootDiameterPositive resolution.minimumDepth) : InitialRealization safe sheet :=
  ⟨Layer.ofInitialRun safe sheet resolution retained.val,
    Layer.ofInitialRun_eq_initial safe sheet resolution resolutionEq retained.val retained.property⟩

/-- Construct the original initial layer from its same retained accuracy request and all displayed source replies. -/
def initialProgram (safe : data.Safe) (sheet : Fin 2) (resolution : Accuracy.Resolution data 1 1)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) 1 (by decide)) :
    Program (InitialQuestion safe sheet resolution) (InitialReply safe sheet resolution)
      (Except OwnedCells.Preparation.Invalidity (InitialRealization safe sheet)) :=
  (OwnedCells.Preparation.program safe sheet resolution.rootDiameter
    resolution.rootDiameterPositive resolution.minimumDepth).map
      (Except.map (assemble safe sheet resolution resolutionEq))

/-- Record the original unit-accuracy initial layer and every preparation and cell request needed to construct it. -/
def initial (safe : data.Safe) (sheet : Fin 2) (resolution : Accuracy.Resolution data 1 1)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) 1 (by decide)) :
    Protocol (InitialQuestion safe sheet resolution) (InitialReply safe sheet resolution)
      (Except OwnedCells.Preparation.Invalidity (InitialRealization safe sheet)) :=
  (initialProgram safe sheet resolution resolutionEq).protocol

/-- A successful realization retains the exact original complete initial layer. -/
private theorem realization_eq {safe : data.Safe} {sheet : Fin 2} (actual : InitialRealization safe sheet) :
    actual = ⟨IntegrationLayers.initial safe sheet, rfl⟩ := by
  cases actual with
  | mk layer same =>
      cases same
      rfl

/-- The original unit request and source replies retain the original initial layer and all its cached data. -/
private theorem initialProgram_value_spec (safe : data.Safe) (sheet : Fin 2)
    (resolution : Accuracy.Resolution data 1 1)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) 1 (by decide)) :
    ((initialProgram safe sheet resolution resolutionEq).protocol.run (initialAnswer safe sheet resolution)).value =
      .ok ⟨IntegrationLayers.initial safe sheet, rfl⟩ := by
  rewrite [initialProgram, Program.map_execution, Protocol.map_run_value]
  change Except.map (assemble safe sheet resolution resolutionEq)
    ((OwnedCells.Preparation.program safe sheet resolution.rootDiameter
      resolution.rootDiameterPositive resolution.minimumDepth).protocol.run
      (OwnedCells.Preparation.answer safe sheet resolution.rootDiameter
        resolution.rootDiameterPositive resolution.minimumDepth)).value = _
  rewrite [OwnedCells.Preparation.program_value]
  exact congrArg Except.ok (realization_eq _)

/-- The expandable initial-layer construction returns exactly its original retained layer for every safe path. -/
theorem initialProgram_value (safe : data.Safe) (sheet : Fin 2) (resolution : Accuracy.Resolution data 1 1)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) 1 (by decide)) :
    ((initialProgram safe sheet resolution resolutionEq).protocol.run (initialAnswer safe sheet resolution)).value =
      .ok ⟨IntegrationLayers.initial safe sheet, rfl⟩ :=
  initialProgram_value_spec safe sheet resolution resolutionEq

/-- Complete initial-layer execution preserves the original layer and all reached mesh and cell callbacks in order. -/
theorem initial_execution (safe : data.Safe) (sheet : Fin 2) (resolution : Accuracy.Resolution data 1 1)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) 1 (by decide)) :
    let computation := initial safe sheet resolution resolutionEq
    let oracle := initialAnswer safe sheet resolution
    computation.run oracle =
      ⟨.ok ⟨IntegrationLayers.initial safe sheet, rfl⟩, (computation.run oracle).trace⟩ :=
  Basic.Execution.ext (initialProgram_value safe sheet resolution resolutionEq) rfl

/-- Replay retains the original initial layer using only the saved original mesh and cell replies. -/
theorem initial_replay (safe : data.Safe) (sheet : Fin 2) (resolution : Accuracy.Resolution data 1 1)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) 1 (by decide)) :
    let computation := initial safe sheet resolution resolutionEq
    let oracle := initialAnswer safe sheet resolution
    computation.replayExact (computation.run oracle).trace =
      .ok (.ok ⟨IntegrationLayers.initial safe sheet, rfl⟩) :=
  ((initial safe sheet resolution resolutionEq).replayExact_run _).trans
    (congrArg Except.ok (initialProgram_value safe sheet resolution resolutionEq))

/-- Changes outside reached initial-layer requests preserve its whole original model, geometry and callback log. -/
theorem initial_payload_erasure {Payload : Type} (safe : data.Safe) (sheet : Fin 2)
    (resolution : Accuracy.Resolution data 1 1)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) 1 (by decide)) (payload : Payload)
    (outside : Payload → InitialQuestion safe sheet resolution → InitialReply safe sheet resolution) :
    let computation := initial safe sheet resolution resolutionEq
    let oracle := initialAnswer safe sheet resolution
    computation.run (Boundary.Trace.overlay (computation.run oracle).trace (outside payload)) =
      computation.run oracle :=
  Protocol.annotation_erasure (initial safe sheet resolution resolutionEq)
    (initialAnswer safe sheet resolution) payload outside

/-- The actual next construction with identity to the same original parent's next quarter-radius refinement. -/
abbrev NextRealization {safe : data.Safe} {index : Nat} (parent : Layer safe index) :=
  {next : Next parent // next = Next.make parent}

/-- Questions for the supplied next-target resolution on the exact retained parent's depth and cell list. -/
abbrev NextQuestion {safe : data.Safe} {index : Nat} (parent : Layer safe index)
    (resolution : Accuracy.Resolution data 1 (Basic.quarterRadius 1 (index + 1))) :=
  UniformRefinement.Observation.RefinementQuestion parent.depth parent.cells resolution

/-- Original selection and cell receipts for the exact retained parent's next-target request. -/
abbrev NextReply {safe : data.Safe} {index : Nat} (parent : Layer safe index)
    (resolution : Accuracy.Resolution data 1 (Basic.quarterRadius 1 (index + 1))) :=
  UniformRefinement.Observation.RefinementReply parent.depth parent.cells resolution

/-- Execute the next-target source request using the actual retained parent and supplied original resolution. -/
def nextAnswer {safe : data.Safe} {index : Nat} (parent : Layer safe index)
    (resolution : Accuracy.Resolution data 1 (Basic.quarterRadius 1 (index + 1))) :
    NextQuestion parent resolution → NextReply parent resolution :=
  UniformRefinement.Observation.refineAnswer parent.depth parent.cells resolution

/-- Assemble the original next construction from its actual returned target-refinement cache. -/
private def assembleNext {safe : data.Safe} {index : Nat} (parent : Layer safe index)
    (cached : UniformRefinement.Observation.RefinementRealization parent.depth parent.cells parent.width_sq
      (Basic.quarterRadius 1 (index + 1))
      (Basic.quarterRadius_pos (by decide) _)) : NextRealization parent :=
  ⟨Next.ofRefined parent cached.val, Next.ofRefined_eq_make parent cached.val cached.property⟩

/-- Construct the retained parent's original next refinement with all selected-bank and cell requests displayed. -/
def nextProgram {safe : data.Safe} {index : Nat} (parent : Layer safe index)
    (resolution : Accuracy.Resolution data 1 (Basic.quarterRadius 1 (index + 1)))
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide)
      (Basic.quarterRadius 1 (index + 1))
      (Basic.quarterRadius_pos (by decide) _)) :
    Program (NextQuestion parent resolution) (NextReply parent resolution)
      (Except UniformRefinement.Observation.Invalidity (NextRealization parent)) :=
  (UniformRefinement.Observation.refineProgram parent.depth parent.cells parent.width_sq
    (Basic.quarterRadius 1 (index + 1))
    (Basic.quarterRadius_pos (by decide) _) resolution resolutionEq).map
      (Except.map (assembleNext parent))

/-- Record the original next-layer construction and all actual selected-bank and cell source requests. -/
def next {safe : data.Safe} {index : Nat} (parent : Layer safe index)
    (resolution : Accuracy.Resolution data 1 (Basic.quarterRadius 1 (index + 1)))
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide)
      (Basic.quarterRadius 1 (index + 1))
      (Basic.quarterRadius_pos (by decide) _)) :
    Protocol (NextQuestion parent resolution) (NextReply parent resolution)
      (Except UniformRefinement.Observation.Invalidity (NextRealization parent)) :=
  (nextProgram parent resolution resolutionEq).protocol

/-- A successful next realization retains exactly the original parent's complete next construction. -/
private theorem nextRealization_eq {safe : data.Safe} {index : Nat} {parent : Layer safe index}
    (actual : NextRealization parent) : actual = ⟨Next.make parent, rfl⟩ := by
  cases actual with
  | mk next same =>
      cases same
      rfl

/-- The original next-target source replies retain the same original next construction and every cached field. -/
private theorem nextProgram_value_spec {safe : data.Safe} {index : Nat} (parent : Layer safe index)
    (resolution : Accuracy.Resolution data 1 (Basic.quarterRadius 1 (index + 1)))
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide)
      (Basic.quarterRadius 1 (index + 1))
      (Basic.quarterRadius_pos (by decide) _)) :
    ((nextProgram parent resolution resolutionEq).protocol.run (nextAnswer parent resolution)).value =
      .ok ⟨Next.make parent, rfl⟩ := by
  rewrite [nextProgram, Program.map_execution, Protocol.map_run_value]
  change Except.map (assembleNext parent)
    ((UniformRefinement.Observation.refineProgram parent.depth parent.cells parent.width_sq
      (Basic.quarterRadius 1 (index + 1))
      (Basic.quarterRadius_pos (by decide) _) resolution resolutionEq).protocol.run
        (UniformRefinement.Observation.refineAnswer parent.depth parent.cells resolution)).value = _
  rewrite [UniformRefinement.Observation.refineProgram_value]
  exact congrArg Except.ok (nextRealization_eq _)

/-- The expandable next construction retains its original next result with the same parent and accuracy target. -/
theorem nextProgram_value {safe : data.Safe} {index : Nat} (parent : Layer safe index)
    (resolution : Accuracy.Resolution data 1 (Basic.quarterRadius 1 (index + 1)))
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide)
      (Basic.quarterRadius 1 (index + 1))
      (Basic.quarterRadius_pos (by decide) _)) :
    ((nextProgram parent resolution resolutionEq).protocol.run (nextAnswer parent resolution)).value =
      .ok ⟨Next.make parent, rfl⟩ := nextProgram_value_spec parent resolution resolutionEq

/-- Complete next construction preserves the original cached refinement and every actual chronological source call. -/
theorem next_execution {safe : data.Safe} {index : Nat} (parent : Layer safe index)
    (resolution : Accuracy.Resolution data 1 (Basic.quarterRadius 1 (index + 1)))
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide)
      (Basic.quarterRadius 1 (index + 1))
      (Basic.quarterRadius_pos (by decide) _)) :
    let computation := next parent resolution resolutionEq
    let oracle := nextAnswer parent resolution
    computation.run oracle = ⟨.ok ⟨Next.make parent, rfl⟩, (computation.run oracle).trace⟩ :=
  Basic.Execution.ext (nextProgram_value parent resolution resolutionEq) rfl

/-- Replay reconstructs the exact original next construction from retained selection and cell replies only. -/
theorem next_replay {safe : data.Safe} {index : Nat} (parent : Layer safe index)
    (resolution : Accuracy.Resolution data 1 (Basic.quarterRadius 1 (index + 1)))
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide)
      (Basic.quarterRadius 1 (index + 1))
      (Basic.quarterRadius_pos (by decide) _)) :
    let computation := next parent resolution resolutionEq
    let oracle := nextAnswer parent resolution
    computation.replayExact (computation.run oracle).trace = .ok (.ok ⟨Next.make parent, rfl⟩) :=
  ((next parent resolution resolutionEq).replayExact_run _).trans
    (congrArg Except.ok (nextProgram_value parent resolution resolutionEq))

/-- Changes outside reached next-construction requests preserve its original result and entire ordered source log. -/
theorem next_payload_erasure {Payload : Type} {safe : data.Safe} {index : Nat} (parent : Layer safe index)
    (resolution : Accuracy.Resolution data 1 (Basic.quarterRadius 1 (index + 1)))
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide)
      (Basic.quarterRadius 1 (index + 1))
      (Basic.quarterRadius_pos (by decide) _)) (payload : Payload)
    (outside : Payload → NextQuestion parent resolution → NextReply parent resolution) :
    let computation := next parent resolution resolutionEq
    let oracle := nextAnswer parent resolution
    computation.run (Boundary.Trace.overlay (computation.run oracle).trace (outside payload)) =
      computation.run oracle :=
  Protocol.annotation_erasure (next parent resolution resolutionEq) (nextAnswer parent resolution) payload outside

end Observation

end Purelib.Integration.Algebraic.SquareFactor.IntegrationLayers
