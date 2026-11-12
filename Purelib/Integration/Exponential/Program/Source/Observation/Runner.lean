module

public import Purelib.Integration.Exponential.Program.Source.Observation.StageComparison
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record

/-!
# Source comparison of an original exponential integration observation

The original integration runner executes once against the retained cached
program and keeps its complete model-query transcript. Its actual selected
exchange supplies the cached stage for a source comparison; the comparison
records the Taylor and common-point replies it consumes. The numerical bound
uses the runner's returned sample and those same common readings.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source.Observation.Runner

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential
open Purelib.CCL.Progressive.IntegrationReplay
open Purelib.Computation.Query
open Purelib.Data.Nat.Schedule
open Purelib.Data.Rat
open Purelib.Integration.Exponential
open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation

/-- The original integration record indexed by the same retained exponential program. -/
abbrev Prepared {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth)
    (request : CertifiedProgram.Request) (count : Nat) := Record.Recorded retained.program request count

/-- Execute the original integration observation once on the retained cached program. -/
@[expose] def prepare {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (request : CertifiedProgram.Request) (count : Nat) :
    Prepared retained request count :=
  Record.record retained.program request count

/-- Construct the source request from the exact prepared cache already returned by the runner.

The original observation's prepared-request projection reads the selected
index and complete model directly from its retained transcript. Its stage
identity proof is reused without another executable model request. -/
@[expose] def stageRequest {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    {retained : Program.Retained policy schedule extraDepth} {request : CertifiedProgram.Request} {count : Nat}
    (prepared : Prepared retained request count) (accuracy : AccuracyRequest) :
    StageComparison.Request policy schedule extraDepth :=
  let selected := prepared.preparedRequest
  StageComparison.Request.withStage retained selected.index selected.cache selected.cache_eq accuracy

/-- The source request uses the exact selected model retained by the runner's transcript. -/
theorem stageRequest_stage {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    {retained : Program.Retained policy schedule extraDepth} {request : CertifiedProgram.Request} {count : Nat}
    (prepared : Prepared retained request count) (accuracy : AccuracyRequest) :
    (stageRequest prepared accuracy).stage = prepared.selectedExchange.reply := rfl

/-- The runner's selected sample is the sample of its same retained selected exchange. -/
theorem selected_sample {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    {retained : Program.Retained policy schedule extraDepth} {request : CertifiedProgram.Request} {count : Nat}
    (prepared : Prepared retained request count) :
    prepared.observation.selected.sample = prepared.selectedExchange.reply.sample := by
  have same := congrArg (fun reading : Reading => reading.sample) prepared.preparedRequest_reading
  change prepared.selectedExchange.reply.sample = prepared.observation.selected.sample at same
  exact same.symm

variable {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride}
  {extraDepth rightExtra : Nat} {retained : Program.Retained policy schedule extraDepth}
  {request : CertifiedProgram.Request} {count : Nat}
variable (prepared : Prepared retained request count) (accuracy : AccuracyRequest)
  (right : StageComparison.Request rightPolicy rightSchedule rightExtra)

/-- Source questions belonging to the actual selected runner stage and the independent right stage. -/
abbrev Query := StageComparison.Question (stageRequest prepared accuracy) right

/-- Source replies retain their selected-runner or independent-stage owner. -/
abbrev Reply := StageComparison.Reply (stageRequest prepared accuracy) right

/-- Compare the original selected runner stage through the actual Taylor and common-point observations. -/
abbrev computation := StageComparison.computation (stageRequest prepared accuracy) right

/-- Answer the comparison questions using the original selected and independent finite Taylor sources. -/
abbrev originalReply := StageComparison.originalReply (stageRequest prepared accuracy) right

/-- Original source replies return the actual selected-stage and independent-stage comparison. -/
theorem computation_original :
    ((computation prepared accuracy right).protocol.run (originalReply prepared accuracy right)).value =
      .ok (StageComparison.canonical (stageRequest prepared accuracy) right) :=
  StageComparison.computation_original (stageRequest prepared accuracy) right

/-- Exact source replay returns the same comparison without invoking any displayed Taylor source. -/
theorem computation_replay :
    (computation prepared accuracy right).protocol.replayExact
      ((computation prepared accuracy right).protocol.run (originalReply prepared accuracy right)).trace =
        .ok (.ok (StageComparison.canonical (stageRequest prepared accuracy) right)) :=
  StageComparison.computation_replay (stageRequest prepared accuracy) right

/-- Replies outside the actual source trace preserve the complete comparison and ordered trace. -/
theorem payload_erasure {Payload : Type} (payload : Payload)
    (outside : Payload → Query prepared accuracy right → Reply prepared accuracy right) :
    (computation prepared accuracy right).protocol.run (Boundary.Trace.overlay
      ((computation prepared accuracy right).protocol.run (originalReply prepared accuracy right)).trace
      (outside payload)) = (computation prepared accuracy right).protocol.run (originalReply prepared accuracy right) :=
  StageComparison.payload_erasure (stageRequest prepared accuracy) right payload outside

/-- The returned left stage uses the exact model sample already observed by the runner. -/
theorem selected_stage_sample
    (compared : StageComparison.Compared (stageRequest prepared accuracy) right) :
    prepared.observation.selected.sample = compared.leftStage.stage.sample := by
  have stage_eq := StageComparison.Compared.left_stage (stageRequest prepared accuracy) right compared
  exact (selected_sample prepared).trans (congrArg (fun stage => stage.sample) stage_eq).symm

/-- The actual returned common-point budget pays for the difference from the runner's selected sample. -/
theorem selected_difference_le_actual
    (compared : StageComparison.Compared (stageRequest prepared accuracy) right) :
    Fraction.abs (prepared.observation.selected.sample.re - compared.rightStage.stage.sample.re) ≤
      (integralBound (StageComparison.retainedFrontier (stageRequest prepared accuracy)
        compared.leftStage).cells).width +
        (integralBound (StageComparison.retainedFrontier right compared.rightStage).cells).width +
          compared.common.val.pointBudget := by
  rw [selected_stage_sample prepared accuracy right compared]
  exact StageComparison.Compared.samples_difference_le (stageRequest prepared accuracy) right compared

/-- Both retained selected depths pay for the runner's actual selected-sample comparison. -/
theorem selected_difference_le
    (compared : StageComparison.Compared (stageRequest prepared accuracy) right) :
    Fraction.abs (prepared.observation.selected.sample.re - compared.rightStage.stage.sample.re) ≤
      (integralBound (StageComparison.retainedFrontier (stageRequest prepared accuracy)
        compared.leftStage).cells).width +
        (integralBound (StageComparison.retainedFrontier right compared.rightStage).cells).width +
          (Horner.Real.tailRadius ((stageRequest prepared accuracy).retained.selection
              (stageRequest prepared accuracy).index).depth +
            Horner.Real.tailRadius right.selection.depth) := by
  rw [selected_stage_sample prepared accuracy right compared]
  exact StageComparison.Compared.samples_difference_le_radii (stageRequest prepared accuracy) right compared

end Purelib.Integration.Exponential.Program.Source.Observation.Runner

end
