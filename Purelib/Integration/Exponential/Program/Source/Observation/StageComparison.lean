module

public import Purelib.Integration.Exponential.Program.Source.Observation
public import Purelib.Integration.Exponential.Program.Source.Comparison
public import Purelib.Integration.Cell.Source.Comparison.Observation
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Comparing retained exponential stages through their source requests

Each input keeps the actual selection and model caches of one original
policy-controlled exponential program. Stage construction consumes the
returned exact Taylor readings, and comparison consumes the returned
owner-specific readings on the actual common refinement. No completed
exponential value is selected.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source.Observation.StageComparison

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Computation.Query
open Purelib.Data.Nat.Schedule
open Purelib.Data.Rat
open Purelib.Integration.Exponential
open Purelib.Integration.Program.Gaussian
open Purelib.Integration.SourceFrontier.Continuous
open Purelib.Integration.SourceFrontier

set_option genInjectivity false in
/-- One original exponential stage request with its actual shared selection and model caches. -/
structure Request (policy : Geometry.Policy) (schedule : PositiveStride) (extraDepth : Nat) where
  /-- The original policy-controlled selection and model prefixes. -/ retained :
    Program.Retained policy schedule extraDepth
  /-- The original stage index. -/ index : Nat
  /-- The actual original selection and geometry at that index. -/ selection : Selection index
  /-- The selection belongs to the same retained program. -/ selection_eq : selection = retained.selection index
  /-- The original cached model already selected at that index. -/ stage : Cached.Basic.CachedModel
  /-- The cached model is the requested stage of the same retained program. -/ stage_eq :
    stage = retained.program.stage index
  /-- The positive source-enclosure request at that stage. -/ accuracy : AccuracyRequest

namespace Request

/-- Retain an original cached program with the requested stage and source accuracy. -/
@[expose] def make {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat) (accuracy : AccuracyRequest) :
    Request policy schedule extraDepth :=
  let chosen := retained.selectedStage index
  ⟨retained, index, chosen.selection, chosen.selection_eq, chosen.model, chosen.model_eq, accuracy⟩

/-- Retain a previously returned stage cache with its original program, index and source request. -/
@[expose] def withStage {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat) (stage : Cached.Basic.CachedModel)
    (stage_eq : stage = retained.program.stage index) (accuracy : AccuracyRequest) :
    Request policy schedule extraDepth := ⟨retained, index, retained.selection index, rfl, stage, stage_eq, accuracy⟩

/-- Retain the actual selected stage and model returned by an original stage acquisition. -/
@[expose] def withSelected {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat)
    (selected : Selection index) (selected_eq : selected = retained.selection index)
    (stage : Cached.Basic.CachedModel) (stage_eq : stage = retained.program.stage index) (accuracy : AccuracyRequest) :
    Request policy schedule extraDepth := ⟨retained, index, selected, selected_eq, stage, stage_eq, accuracy⟩

/-- The original finite Taylor source at the actual retained selected depth. -/
abbrev source {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (request : Request policy schedule extraDepth) : Fraction.Rational → Fraction.Rational :=
  Horner.Real.finiteSource request.selection.depth

/-- The finite source preparation for the actual retained stage request. -/
abbrev preparation {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (request : Request policy schedule extraDepth) :=
  selectedPreparation request.selection request.accuracy

/-- Observe the actual retained stage and its source construction. -/
abbrev computation {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (request : Request policy schedule extraDepth) :=
  selectedComputation request.retained request.index request.selection request.selection_eq request.stage
    request.stage_eq request.accuracy

end Request

/-- The retained source has the original canonical selection's exact finite Taylor depth. -/
theorem Request.source_eq {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (request : Request policy schedule extraDepth) :
    Horner.Real.finiteSource (Selection.selection policy schedule request.index).depth = request.source := by
  change Horner.Real.finiteSource (Selection.selection policy schedule request.index).depth =
    Horner.Real.finiteSource request.selection.depth
  exact congrArg Horner.Real.finiteSource
    (congrArg Selection.depth (request.selection_eq.trans (request.retained.selection_eq request.index))).symm

variable {leftPolicy rightPolicy : Geometry.Policy} {leftSchedule rightSchedule : PositiveStride}
  {leftExtra rightExtra : Nat}
variable (left : Request leftPolicy leftSchedule leftExtra) (right : Request rightPolicy rightSchedule rightExtra)

set_option genInjectivity false in
/-- A source request for an original left stage, right stage or common comparison. -/
inductive Question where
  /-- A source point of the original retained left stage. -/ | left
      (entry : Continuous.Observation.Entry left.preparation)
  /-- A source point of the original retained right stage. -/ | right
      (entry : Continuous.Observation.Entry right.preparation)
  /-- An owner-specific common-refinement point. -/ | common (question : Comparison.Observation.Query)
  deriving @[expose] DecidableEq

set_option genInjectivity false in
/-- A reply retains the original stage or common-comparison source owner. -/
inductive Reply where
  /-- An exact reading of the retained left Taylor source. -/ | left (point : SourcePoint left.source)
  /-- An exact reading of the retained right Taylor source. -/ | right (point : SourcePoint right.source)
  /-- An owner-specific reading for the common comparison. -/ | common
      (reply : Comparison.Observation.Reply left.source right.source)

set_option genInjectivity false in
/-- An invalid operation or original source-point tag at one of the three boundaries. -/
inductive Failure where
  /-- A reply belongs to a different source operation. -/ | operation (requested : Question left right)
  /-- The original left stage rejected a point tag. -/ | left
      (invalid : Continuous.Observation.InvalidTag left.preparation)
  /-- The original right stage rejected a point tag. -/ | right
      (invalid : Continuous.Observation.InvalidTag right.preparation)
  /-- The common comparison rejected a source owner or point tag. -/ | common (invalid : Comparison.Observation.Failure)

/-- Answer each displayed question from its exact original retained source owner. -/
@[expose] def originalReply : Question left right → Reply left right
  | .left entry => .left (Continuous.Observation.originalReply left.preparation entry)
  | .right entry => .right (Continuous.Observation.originalReply right.preparation entry)
  | .common question => .common (Comparison.Observation.originalReply left.source right.source question)

theorem transport_contains {source target : Fraction.Rational → Fraction.Rational} (same : source = target)
    (frontier : SourceFrontier source) (value : Fraction.Rational)
    (inside : (integralBound frontier.cells).Contains value) :
    (integralBound (same ▸ frontier).cells).Contains value := by
  cases same
  exact inside

/-- View a returned original stage frontier at the same retained selection-cache depth. -/
@[expose] def retainedFrontier {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (request : Request policy schedule extraDepth)
    (result : Result policy schedule extraDepth request.index request.accuracy) : SourceFrontier request.source :=
  (Request.source_eq request) ▸ result.sourceResult.frontier

/-- The actual stage sample remains admitted after viewing its frontier at the retained depth. -/
theorem retainedFrontier_contains {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (request : Request policy schedule extraDepth)
    (result : Result policy schedule extraDepth request.index request.accuracy) :
    (integralBound (retainedFrontier request result).cells).Contains result.stage.sample.re :=
  transport_contains (Request.source_eq request) result.sourceResult.frontier result.stage.sample.re
    result.sample_inside

set_option genInjectivity false in
/-- Two returned original stages and their actual certified common-point comparison. -/
structure Compared where
  /-- The returned stage of the original retained left program. -/ leftStage :
    Result leftPolicy leftSchedule leftExtra left.index left.accuracy
  /-- The returned stage of the original retained right program. -/ rightStage :
    Result rightPolicy rightSchedule rightExtra right.index right.accuracy
  /-- The returned original common refinement at both retained selected depths. -/ common :
    Comparison.Observation.Certified (retainedFrontier left leftStage) (retainedFrontier right rightStage)

/-- The actually returned common readings pay for the two retained stage samples. -/
theorem Compared.samples_difference_le (compared : Compared left right) :
    Fraction.abs (compared.leftStage.stage.sample.re - compared.rightStage.stage.sample.re) ≤
      (integralBound (retainedFrontier left compared.leftStage).cells).width +
        (integralBound (retainedFrontier right compared.rightStage).cells).width + compared.common.val.pointBudget :=
  compared.common.val.answers_difference_le compared.leftStage.stage.sample.re compared.rightStage.stage.sample.re
    (retainedFrontier_contains left compared.leftStage) (retainedFrontier_contains right compared.rightStage)

/-- The retained selected depths pay for the actual returned common-point discrepancy. -/
theorem Compared.pointBudget_le (compared : Compared left right) :
    compared.common.val.pointBudget ≤ Horner.Real.tailRadius left.selection.depth +
      Horner.Real.tailRadius right.selection.depth := by
  rw [compared.common.property]
  exact Source.finitePointBudget _ _ (retainedFrontier left compared.leftStage)
    (retainedFrontier right compared.rightStage)

/-- The retained stage samples differ by their actual enclosure widths and selected-depth radii. -/
theorem Compared.samples_difference_le_radii (compared : Compared left right) :
    Fraction.abs (compared.leftStage.stage.sample.re - compared.rightStage.stage.sample.re) ≤
      (integralBound (retainedFrontier left compared.leftStage).cells).width +
        (integralBound (retainedFrontier right compared.rightStage).cells).width +
          (Horner.Real.tailRadius left.selection.depth +
            Horner.Real.tailRadius right.selection.depth) :=
  (Compared.samples_difference_le left right compared).trans
    (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
      (Compared.pointBudget_le left right compared))

/-- The returned left stage keeps its own original retained program. -/
theorem Compared.left_program (compared : Compared left right) :
    compared.leftStage.program = left.retained.program :=
  compared.leftStage.program_eq.trans left.retained.program_eq.symm

/-- The returned right stage keeps its own original retained program. -/
theorem Compared.right_program (compared : Compared left right) :
    compared.rightStage.program = right.retained.program :=
  compared.rightStage.program_eq.trans right.retained.program_eq.symm

/-- The returned left stage equals the cache supplied by its original request. -/
theorem Compared.left_stage (compared : Compared left right) : compared.leftStage.stage = left.stage :=
  compared.leftStage.stage_eq.trans ((congrArg (fun program : Cached.Basic.CachedProgram => program.stage left.index)
    (Compared.left_program left right compared)).trans left.stage_eq.symm)

/-- The returned right stage equals the cache supplied by its original request. -/
theorem Compared.right_stage (compared : Compared left right) : compared.rightStage.stage = right.stage :=
  compared.rightStage.stage_eq.trans ((congrArg (fun program : Cached.Basic.CachedProgram => program.stage right.index)
    (Compared.right_program left right compared)).trans right.stage_eq.symm)

/-- Forward one original left-stage source request and reject another operation's reply. -/
private def leftHandler (entry : Continuous.Observation.Entry left.preparation) :
    Program (Question left right) (Reply left right) (Except (Failure left right) (SourcePoint left.source)) :=
  .request (.left entry) fun response => match response with
    | .left point => .pure (.ok point)
    | .right _ | .common _ => .pure (.error (.operation (.left entry)))

/-- Forward one original right-stage source request and reject another operation's reply. -/
private def rightHandler (entry : Continuous.Observation.Entry right.preparation) :
    Program (Question left right) (Reply left right) (Except (Failure left right) (SourcePoint right.source)) :=
  .request (.right entry) fun response => match response with
    | .right point => .pure (.ok point)
    | .left _ | .common _ => .pure (.error (.operation (.right entry)))

/-- Forward one original common-source request and reject another operation's reply. -/
private def commonHandler (question : Comparison.Observation.Query) :
    Program (Question left right) (Reply left right)
      (Except (Failure left right) (Comparison.Observation.Reply left.source right.source)) :=
  .request (.common question) fun response => match response with
    | .common reply => .pure (.ok reply)
    | .left _ | .right _ => .pure (.error (.operation (.common question)))

/-- Construct the original retained left stage from its displayed source requests. -/
def leftProgram : Program (Question left right) (Reply left right)
    (Except (Failure left right) (Result leftPolicy leftSchedule leftExtra left.index left.accuracy)) :=
  (left.computation.substituteChecked (leftHandler left right)).map fun result =>
    match result with
    | .error invalid => .error invalid
    | .ok execution => execution.value.mapError Failure.left

/-- Construct the original retained right stage from its displayed source requests. -/
def rightProgram : Program (Question left right) (Reply left right)
    (Except (Failure left right) (Result rightPolicy rightSchedule rightExtra right.index right.accuracy)) :=
  (right.computation.substituteChecked (rightHandler left right)).map fun result =>
    match result with
    | .error invalid => .error invalid
    | .ok execution => execution.value.mapError Failure.right

/-- Original left-source replies return the complete original retained left stage. -/
theorem leftProgram_original :
    ((leftProgram left right).protocol.run (originalReply left right)).value =
      .ok (Source.build leftPolicy leftSchedule leftExtra left.index left.accuracy) := by
  unfold leftProgram
  rw [Program.map_execution, Protocol.map_run_value]
  rw [Program.substituteChecked_value _ _ _ (Continuous.Observation.originalReply left.preparation) (fun _ => rfl)]
  dsimp only [Request.computation, Request.preparation]
  rw [selectedComputation_original]
  rfl

/-- Original right-source replies return the complete original retained right stage. -/
private theorem rightProgram_original :
    ((rightProgram left right).protocol.run (originalReply left right)).value =
      .ok (Source.build rightPolicy rightSchedule rightExtra right.index right.accuracy) := by
  unfold rightProgram
  rw [Program.map_execution, Protocol.map_run_value]
  rw [Program.substituteChecked_value _ _ _ (Continuous.Observation.originalReply right.preparation) (fun _ => rfl)]
  dsimp only [Request.computation, Request.preparation]
  rw [selectedComputation_original]
  rfl

/-- Construct the original certified common comparison from the two returned stage frontiers. -/
def commonProgram (leftStage : Result leftPolicy leftSchedule leftExtra left.index left.accuracy)
    (rightStage : Result rightPolicy rightSchedule rightExtra right.index right.accuracy) :
    Program (Question left right) (Reply left right) (Except (Failure left right)
      (Comparison.Observation.Certified (retainedFrontier left leftStage) (retainedFrontier right rightStage))) :=
  (Program.substituteChecked (commonHandler left right)
    (Comparison.Observation.certifiedComputation (retainedFrontier left leftStage)
      (retainedFrontier right rightStage))).map fun result =>
      match result with
      | .error invalid => .error invalid
      | .ok execution => execution.value.mapError Failure.common

/-- Original owner-specific replies return the complete original common comparison. -/
private theorem commonProgram_original
    (leftStage : Result leftPolicy leftSchedule leftExtra left.index left.accuracy)
    (rightStage : Result rightPolicy rightSchedule rightExtra right.index right.accuracy) :
    ((commonProgram left right leftStage rightStage).protocol.run (originalReply left right)).value =
      .ok ⟨SourceFrontier.commonReadings (retainedFrontier left leftStage)
        (retainedFrontier right rightStage), rfl⟩ := by
  unfold commonProgram
  rw [Program.map_execution, Protocol.map_run_value]
  rw [Program.substituteChecked_value _ _ _ (Comparison.Observation.originalReply left.source right.source)
    (fun _ => rfl)]
  dsimp only
  rw [Comparison.Observation.certified_original]
  rfl

/-- The original two retained stage results with their original common-source comparison. -/
@[expose] def canonical : Compared left right :=
  let leftStage := Source.build leftPolicy leftSchedule leftExtra left.index left.accuracy
  let rightStage := Source.build rightPolicy rightSchedule rightExtra right.index right.accuracy
  ⟨leftStage, rightStage,
    ⟨SourceFrontier.commonReadings (retainedFrontier left leftStage) (retainedFrontier right rightStage), rfl⟩⟩

/-- Construct both retained stages and their common comparison from their actual ordered source replies.

Each successful stage feeds its returned frontier to the common comparison.
A wrong operation, source owner or point tag stops before later requests;
no returned stage, point or common reading is reconstructed by a second run. -/
@[expose] def computation : Program (Question left right) (Reply left right)
    (Except (Failure left right) (Compared left right)) :=
  (leftProgram left right).bind fun first =>
    match first with
    | .error invalid => .pure (.error invalid)
    | .ok leftStage => (rightProgram left right).bind fun second =>
        match second with
        | .error invalid => .pure (.error invalid)
        | .ok rightStage => (commonProgram left right leftStage rightStage).map fun common =>
            common.map fun readings => ⟨leftStage, rightStage, readings⟩

/-- Successful stages expose the actual left, right and common source traces in their execution order. -/
theorem computation_trace (oracle : Question left right → Reply left right)
    (leftStage : Result leftPolicy leftSchedule leftExtra left.index left.accuracy)
    (rightStage : Result rightPolicy rightSchedule rightExtra right.index right.accuracy)
    (leftRun : ((leftProgram left right).protocol.run oracle).value = .ok leftStage)
    (rightRun : ((rightProgram left right).protocol.run oracle).value = .ok rightStage) :
    ((computation left right).protocol.run oracle).trace =
      ((leftProgram left right).protocol.run oracle).trace ++
        (((rightProgram left right).protocol.run oracle).trace ++
          ((commonProgram left right leftStage rightStage).protocol.run oracle).trace) := by
  unfold computation
  rw [Program.bind_execution, Protocol.bind_run_trace, leftRun]
  dsimp only
  rw [Program.bind_execution, Protocol.bind_run_trace, rightRun]
  dsimp only
  rw [Program.map_execution, Protocol.map_run_trace]

/-- Original source replies return the complete original stages and their actual common comparison. -/
theorem computation_original :
    ((computation left right).protocol.run (originalReply left right)).value = .ok (canonical left right) := by
  unfold computation canonical
  rw [Program.bind_execution, Protocol.bind_run_value, leftProgram_original]
  rw [Program.bind_execution, Protocol.bind_run_value, rightProgram_original]
  rw [Program.map_execution, Protocol.map_run_value, commonProgram_original]
  rfl

/-- Exact replay returns both original stages and their comparison without repeating source requests. -/
theorem computation_replay :
    (computation left right).protocol.replayExact
      ((computation left right).protocol.run (originalReply left right)).trace = .ok (.ok (canonical left right)) := by
  rw [(computation left right).protocol.replayExact_run, computation_original]

/-- Replies outside the actual stage-and-comparison trace preserve its complete result and ordered trace. -/
theorem payload_erasure {Payload : Type} (payload : Payload)
    (outside : Payload → Question left right → Reply left right) :
    (computation left right).protocol.run (Boundary.Trace.overlay
      ((computation left right).protocol.run (originalReply left right)).trace (outside payload)) =
      (computation left right).protocol.run (originalReply left right) :=
  (computation left right).protocol.annotation_erasure (originalReply left right) payload outside

end Purelib.Integration.Exponential.Program.Source.Observation.StageComparison

end
