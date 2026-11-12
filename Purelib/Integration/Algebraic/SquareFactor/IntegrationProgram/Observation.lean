module

public import Purelib.Integration.Algebraic.SquareFactor.IntegrationProgram
public import Purelib.Integration.Algebraic.SquareFactor.IntegrationLayers.Observation
import Purelib.Approximation.Rational.Geometric.Basic

/-!
# Chronological integration layers from the retained original initial layer

The initial layer is supplied once. Each successor construction receives
the actual returned parent and computes its next accuracy request once.
Questions retain that same parent and resolution; source execution uses
their actual caches. The original layer identity certifies every step and
allows complete replay without reconstruction of any earlier source call.
-/

public section

namespace Purelib.Integration.Algebraic.SquareFactor.IntegrationProgram

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Computation.Query
open Purelib.Approximation.Rational

namespace Observation

variable {polynomial : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request}
  {prepared : SquareFactor.Prepared polynomial request} {segment : PathInput.Segment}
  {data : PathInput.Data prepared segment} {safe : data.Safe}

/-- The actual retained layer with identity to its chronological construction from the same original initial layer. -/
abbrev Realization (start : IntegrationLayers.Layer safe 0) (index : Nat) :=
  {layer : IntegrationLayers.Layer safe index // layer = layerFrom start index}

set_option genInjectivity false in
/-- A next-layer request retaining the actual returned parent and its one computed original accuracy resolution. -/
structure Request (start : IntegrationLayers.Layer safe 0) (index : Nat) where
  /-- The actual chronological parent with its original construction identity. -/ parent : Realization start index
  /-- The supplied next quarter-radius resolution on the same original path. -/ resolution :
      Accuracy.Resolution data 1 (Geometric.Basic.quarterRadius 1 (index + 1))
  /-- The request is the exact original next-target resolution. -/ resolution_eq : resolution =
      Accuracy.resolve safe 1 (by decide) (Geometric.Basic.quarterRadius 1 (index + 1))
        (Geometric.Basic.quarterRadius_pos (by decide) _)

namespace Request

/-- Compute the original next accuracy request once while retaining the actual returned chronological parent. -/
def ofParent {start : IntegrationLayers.Layer safe 0} {index : Nat} (parent : Realization start index) :
    Request start index :=
  ⟨parent, Accuracy.resolve safe 1 (by decide) (Geometric.Basic.quarterRadius 1 (index + 1))
    (Geometric.Basic.quarterRadius_pos (by decide) _), rfl⟩

/-- Requests at the same original chronological position have the same retained parent and resolution. -/
theorem eq {start : IntegrationLayers.Layer safe 0} {index : Nat} (first second : Request start index) :
    first = second := by
  cases first with
  | mk firstParent firstResolution firstResolutionEq =>
      cases second with
      | mk secondParent secondResolution secondResolutionEq =>
          cases firstParent with
          | mk firstLayer firstEq =>
              cases secondParent with
              | mk secondLayer secondEq =>
                  cases firstEq
                  cases secondEq
                  cases firstResolutionEq
                  cases secondResolutionEq
                  rfl

end Request

set_option genInjectivity false in
/-- A displayed source request on the actual retained parent and resolution at its original chronological index. -/
inductive Question (start : IntegrationLayers.Layer safe 0) where
  /-- Request one original next-layer source operation at this same retained chronological position. -/ | next
      (index : Nat) (request : Request start index)
      (question : IntegrationLayers.Observation.NextQuestion request.parent.val request.resolution)

/-- Compare chronological indices and original source requests without comparing any parent callbacks. -/
instance {start : IntegrationLayers.Layer safe 0} : DecidableEq (Question start) := fun left right =>
  match left, right with
  | .next index first question, .next otherIndex second otherQuestion =>
      if same : index = otherIndex then by
        cases same
        cases Request.eq second first
        exact if equal : question = otherQuestion then
          .isTrue (congrArg (Question.next index first) equal)
        else .isFalse (fun same => by cases same; exact equal rfl)
      else .isFalse (fun equal => by cases equal; exact same rfl)

set_option genInjectivity false in
/-- The original next-layer source reply with its actual parent, request and chronological position. -/
inductive Reply (start : IntegrationLayers.Layer safe 0) where
  /-- Retain the complete original selected-bank or cell reply at the same original parent and index. -/ | next
      (index : Nat) (request : Request start index)
      (reply : IntegrationLayers.Observation.NextReply request.parent.val request.resolution)

set_option genInjectivity false in
/-- A reply belongs to a different chronological index or violates the original next-refinement checking boundary. -/
inductive Invalidity where
  /-- Retain the exact requested and reported chronological indices with their proved disagreement. -/ | index
      (expected reported : Nat) (different : reported ≠ expected)
  /-- Retain the original next-refinement invalidity at the exact requested chronological position. -/ | refinement
      (index : Nat) (invalid : UniformRefinement.Observation.Invalidity)

/-- Execute the original source operation from the actual parent and resolution carried by its displayed request. -/
def answer {start : IntegrationLayers.Layer safe 0} : Question start → Reply start
  | .next index request question =>
      .next index request (IntegrationLayers.Observation.nextAnswer request.parent.val request.resolution question)

/-- Check the actual chronological index and transport only the retained original request's ownership. -/
private def receive {start : IntegrationLayers.Layer safe 0} {index : Nat} (request : Request start index)
    (reply : Reply start) : Except Invalidity
      (IntegrationLayers.Observation.NextReply request.parent.val request.resolution) :=
  match reply with
  | .next reported retained actual =>
      if same : reported = index then by
        cases same
        exact .ok (Request.eq retained request ▸ actual)
      else .error (.index index reported same)

/-- Forward the actual next-layer request and reject a reply from another chronological position. -/
private def handler {start : IntegrationLayers.Layer safe 0} {index : Nat} (request : Request start index)
    (question : IntegrationLayers.Observation.NextQuestion request.parent.val request.resolution) :
    Program (Question start) (Reply start) (Except Invalidity
      (IntegrationLayers.Observation.NextReply request.parent.val request.resolution)) :=
  (Program.query (.next index request question)).map (receive request)

/-- Assemble the next chronological layer from the exact returned next construction and original parent identity. -/
private def ofNext {start : IntegrationLayers.Layer safe 0} {index : Nat} (request : Request start index)
    (next : IntegrationLayers.Observation.NextRealization request.parent.val) : Realization start (index + 1) :=
  ⟨next.val.layer,
    (congrArg (fun next : IntegrationLayers.Next request.parent.val => next.layer) next.property).trans
      (congrArg (fun parent : IntegrationLayers.Layer safe index => (IntegrationLayers.Next.make parent).layer)
        request.parent.property)⟩

/-- Construct the actual returned parent's successor using the same computed request and displayed source calls. -/
private def successor {start : IntegrationLayers.Layer safe 0} {index : Nat} (parent : Realization start index) :
    Program (Question start) (Reply start) (Except Invalidity (Realization start (index + 1))) :=
  let request := Request.ofParent parent
  let construction := IntegrationLayers.Observation.nextProgram
    request.parent.val request.resolution request.resolution_eq
  (construction.substituteChecked (handler request)).map fun result =>
      match result with
      | .error invalid => .error invalid
      | .ok executed =>
          match executed.value with
          | .error invalid => .error (.refinement index invalid)
          | .ok next => .ok (ofNext request next)

/-- Construct a requested chronological layer from the supplied retained initial layer, reusing each returned parent. -/
def program (start : IntegrationLayers.Layer safe 0) : (index : Nat) →
    Program (Question start) (Reply start) (Except Invalidity (Realization start index))
  | 0 => .pure (.ok ⟨start, rfl⟩)
  | index + 1 => (program start index).bind fun result =>
      match result with
      | .error invalid => .pure (.error invalid)
      | .ok parent => successor parent

/-- Transport an already constructed chronological program along equality of its retained initial-layer owner. -/
@[expose] def castStart {start other : IntegrationLayers.Layer safe 0} (same : start = other) {index : Nat}
    (construction : Program (Question start) (Reply start) (Except Invalidity (Realization start index))) :
    Program (Question other) (Reply other) (Except Invalidity (Realization other index)) := by
  cases same
  exact construction

/-- Record the original finite layer sequence and all reached next-refinement source requests. -/
def layerFrom (start : IntegrationLayers.Layer safe 0) (index : Nat) :
    Protocol (Question start) (Reply start) (Except Invalidity (Realization start index)) :=
  (program start index).protocol

/-- Original replies to a retained request pass chronological checking unchanged. -/
private theorem handler_value {start : IntegrationLayers.Layer safe 0} {index : Nat} (request : Request start index)
    (question : IntegrationLayers.Observation.NextQuestion request.parent.val request.resolution) :
    ((handler request question).protocol.run answer).value =
      .ok (IntegrationLayers.Observation.nextAnswer request.parent.val request.resolution question) := by
  rewrite [handler, Program.map_execution, Protocol.map_run_value]
  change receive request (.next index request
    (IntegrationLayers.Observation.nextAnswer request.parent.val request.resolution question)) = _
  unfold receive
  dsimp only
  rewrite [dif_pos rfl]
  rfl

/-- Every successful realization retains precisely its original chronological layer. -/
private theorem realization_eq {start : IntegrationLayers.Layer safe 0} {index : Nat}
    (actual : Realization start index) : actual = ⟨IntegrationProgram.layerFrom start index, rfl⟩ := by
  cases actual with
  | mk layer same =>
      cases same
      rfl

/-- Original next-layer replies preserve the exact successor of the retained chronological parent. -/
private theorem successor_value {start : IntegrationLayers.Layer safe 0} {index : Nat}
    (parent : Realization start index) : ((successor parent).protocol.run answer).value =
      .ok ⟨IntegrationProgram.layerFrom start (index + 1), rfl⟩ := by
  rewrite [successor, Program.map_execution, Protocol.map_run_value,
    Program.substituteChecked_value _ _ _
      (IntegrationLayers.Observation.nextAnswer (Request.ofParent parent).parent.val
        (Request.ofParent parent).resolution) (handler_value (Request.ofParent parent))]
  dsimp only
  rewrite [IntegrationLayers.Observation.nextProgram_value]
  exact congrArg Except.ok (realization_eq _)

/-- Every finite chronological sequence returns its exact original layer under the original displayed source replies. -/
private theorem program_value_spec (start : IntegrationLayers.Layer safe 0) (index : Nat) :
    ((program start index).protocol.run answer).value = .ok ⟨IntegrationProgram.layerFrom start index, rfl⟩ := by
  induction index with
  | zero => rfl
  | succ index induction =>
      rewrite [program, Program.bind_execution, Protocol.bind_run_value, induction]
      dsimp only
      exact successor_value _

/-- The expandable chronological construction retains the exact original layer and its defining identity. -/
theorem program_value (start : IntegrationLayers.Layer safe 0) (index : Nat) :
    ((program start index).protocol.run answer).value = .ok ⟨IntegrationProgram.layerFrom start index, rfl⟩ :=
  program_value_spec start index

/-- Complete layer-sequence execution preserves the original layer and every chronological callback in order. -/
theorem layerFrom_execution (start : IntegrationLayers.Layer safe 0) (index : Nat) :
    (layerFrom start index).run answer =
      ⟨.ok ⟨IntegrationProgram.layerFrom start index, rfl⟩, ((layerFrom start index).run answer).trace⟩ :=
  Basic.Execution.ext (program_value start index) rfl

/-- Replay reconstructs the same finite original layer sequence from its saved source replies without callbacks. -/
theorem layerFrom_replay (start : IntegrationLayers.Layer safe 0) (index : Nat) :
    (layerFrom start index).replayExact ((layerFrom start index).run answer).trace =
      .ok (.ok ⟨IntegrationProgram.layerFrom start index, rfl⟩) :=
  ((layerFrom start index).replayExact_run answer).trans (congrArg Except.ok (program_value start index))

/-- Outside-request changes preserve the entire original chronological layer and ordered source trace. -/
theorem payload_erasure {Payload : Type} (start : IntegrationLayers.Layer safe 0) (index : Nat) (payload : Payload)
    (outside : Payload → Question start → Reply start) :
    let computation := layerFrom start index
    computation.run (Boundary.Trace.overlay (computation.run answer).trace (outside payload)) =
      computation.run answer :=
  Protocol.annotation_erasure (layerFrom start index) answer payload outside

/-- The original cached stage with identity to the same retained initial layer's complete model source. -/
abbrev ModelRealization (start : IntegrationLayers.Layer safe 0) (index : Nat) :=
  {model : Integration.Program.Gaussian.Cached.Basic.CachedModel // model = (cachedFrom start).stage index}

/-- Cache the returned layer's exact model readbacks without reconstructing that layer or invoking its source. -/
def ModelRealization.ofLayer {start : IntegrationLayers.Layer safe 0} {index : Nat}
    (actual : Realization start index) : ModelRealization start index :=
  let model := Integration.CertifiedProgram.CachedModel.canonical
    (operations := Integration.Program.Gaussian.Cached.Basic.modelOperations) actual.val.model
  have same : model = (cachedFrom start).stage index :=
    (congrArg (fun layer : IntegrationLayers.Layer safe index =>
      Integration.CertifiedProgram.CachedModel.canonical
        (operations := Integration.Program.Gaussian.Cached.Basic.modelOperations) layer.model)
      actual.property).trans (cachedFrom_stage start index).symm
  ⟨model, same⟩

/-- Construct the complete original cached stage from the actual returned chronological layer and its same model. -/
def modelProgram (start : IntegrationLayers.Layer safe 0) (index : Nat) :
    Program (Question start) (Reply start) (Except Invalidity (ModelRealization start index)) :=
  (program start index).map (Except.map ModelRealization.ofLayer)

/-- A successful model realization retains exactly the original stage and all its cached readbacks. -/
private theorem modelRealization_eq {start : IntegrationLayers.Layer safe 0} {index : Nat}
    (actual : ModelRealization start index) : actual = ⟨(cachedFrom start).stage index, rfl⟩ := by
  cases actual with
  | mk model same =>
      cases same
      rfl

/-- Original chronological source replies preserve the complete original cached stage, including model and readbacks. -/
theorem modelProgram_value (start : IntegrationLayers.Layer safe 0) (index : Nat) :
    ((modelProgram start index).protocol.run answer).value = .ok ⟨(cachedFrom start).stage index, rfl⟩ := by
  rewrite [modelProgram, Program.map_execution, Protocol.map_run_value, program_value]
  exact congrArg Except.ok (modelRealization_eq _)

end Observation

end Purelib.Integration.Algebraic.SquareFactor.IntegrationProgram
