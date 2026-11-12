module
public import Purelib.Integration.Step.Reciprocal.Integration.Observation
public import Purelib.Integration.Cell.Source.Observation.Continuation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing persistent reciprocal-step integration

The original request selects its finite truncation and tail, whose source
observations are followed by the actual common-refinement reads. The returned
result supplies the same saved frontier and history as the public producer.
-/

public section

namespace Purelib.Integration.Step.Reciprocal.Observation.Continuation

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Integration.SourceFrontier.Observation
open Purelib.Integration.SourceFrontier.Observation.Continuation

/-- One original common-refinement source question at the reciprocal request. -/
abbrev CommonQuery (request : AccuracyRequest) :=
  SourceFrontier.Observation.Continuation.Query (preparation request).partition

/-- An original reciprocal-construction question or one common-refinement source question. -/
abbrev Query (request : AccuracyRequest) :=
  Sum (Observation.Query request) (CommonQuery request)

/-- A reply identifies the original reciprocal construction or common-source operation. -/
abbrev Reply (request : AccuracyRequest) := Sum (Observation.Reply request) (SourcePoint value)

set_option genInjectivity false in
/-- An invalid original operation or source reply during a reciprocal continuation. -/
inductive Failure (request : AccuracyRequest) where
  /-- A response belongs to a different displayed operation. -/ | operation (requested : Query request)
  /-- The original finite reciprocal construction rejected its reply. -/ | fresh (invalid : Observation.Failure request)
  /-- The original common source construction rejected its reply. -/ | common
      (invalid : SourceFrontier.Observation.Continuation.Failure (preparation request).partition)

constructive_injectivity Failure

/-- The original source operations answer the questions they actually own. -/
@[expose] def originalReply (request : AccuracyRequest) : Query request → Reply request :=
  let fresh := Observation.originalReply request
  fun
  | .inl question => .inl (fresh question)
  | .inr question => .inr (originalReplyAll (preparation request).partition question)

/-- Display a question from the original finite reciprocal construction. -/
@[expose] def freshHandler (request : AccuracyRequest) (question : Observation.Query request) :
    Program (Query request) (Reply request) (Except (Failure request) (Observation.Reply request)) :=
  .request (.inl question) fun reply => match reply with
    | .inl response => .pure (.ok response)
    | .inr _ => .pure (.error (.operation (.inl question)))

/-- Compose the actual finite reciprocal construction with its source questions. -/
@[expose] def freshProgram (cached : List (SourcePoint value)) (request : AccuracyRequest) :
    Program (Query request) (Reply request) (Except (Failure request)
      (Basic.Execution (Observation.Query request) (Observation.Reply request)
        (Except (Observation.Failure request) (Observation.CertifiedResult cached request)))) :=
  (Observation.computation cached request).substituteChecked (freshHandler request)

/-- Original execution retains the complete original finite reciprocal construction. -/
theorem freshProgram_original (cached : List (SourcePoint value)) (request : AccuracyRequest) :
    ((freshProgram cached request).protocol.run (originalReply request)).value =
      .ok ((Observation.computation cached request).protocol.run (Observation.originalReply request)) := by
  unfold freshProgram
  apply Program.substituteChecked_value
  intro question
  rfl

/-- Display an actual common-refinement source question. -/
@[expose] def commonHandler (request : AccuracyRequest)
    (question : CommonQuery request) :
    Program (Query request) (Reply request) (Except (Failure request) (SourcePoint value)) :=
  .request (.inr question) fun reply => match reply with
    | .inl _ => .pure (.error (.operation (.inr question)))
    | .inr response => .pure (.ok response)

/-- Compose the actual common refinement with the original shared source requests. -/
@[expose] def commonProgram (request : AccuracyRequest) (cached : List (SourcePoint value))
    (left right : SourceFrontier value) :
    Program (Query request) (Reply request) (Except (Failure request)
      (Basic.Execution (CommonQuery request)
        (SourcePoint value)
        (Except (SourceFrontier.Observation.Continuation.Failure (preparation request).partition)
          (CertifiedCommon left right)))) :=
  (certifiedCommon
    (preparation request).partition cached left right).substituteChecked (commonHandler request)

/-- Original execution retains the complete original common-point construction. -/
theorem commonProgram_original (request : AccuracyRequest) (cached : List (SourcePoint value))
    (left right : SourceFrontier value) :
    ((commonProgram request cached left right).protocol.run (originalReply request)).value =
      .ok ((certifiedCommon
        (preparation request).partition cached left right).protocol.run
          (originalReplyAll (preparation request).partition)) := by
  unfold commonProgram
  apply Program.substituteChecked_value
  intro question
  rfl

/-- Continue the actual saved reciprocal frontier through the original construction and common source reads. -/
@[expose] def computation (previous : SourceFrontier value) (cached : List (SourcePoint value))
    (request : AccuracyRequest) :
    Program (Query request) (Reply request)
      (Except (Failure request) (SourceFrontier.Producer.Continuation producer previous)) := by
  if accurate : (integralBound previous.cells).width < request.tolerance then
    exact .pure (.ok (.reused request accurate))
  else
    let bank := SourceFrontier.Producer.effectiveBank previous cached
    exact (freshProgram bank request).bind fun result =>
      match result with
      | .error invalid => .pure (.error invalid)
      | .ok execution =>
          match execution.value with
          | .error invalid => .pure (.error (.fresh invalid))
          | .ok fresh =>
              let available := fresh.val.frontier.cells.map (fun cell => cell.item) ++
                previous.cells.map (fun cell => cell.item) ++ bank
              (commonProgram request available previous fresh.val.frontier).map fun result =>
                match result with
                | .error invalid => .error invalid
                | .ok execution =>
                    match execution.value with
                    | .error invalid => .error (.common invalid)
                    | .ok common => .ok (fromCertified
                        producer previous cached request fresh common)

/-- An adequate saved reciprocal frontier returns with no displayed source calls. -/
theorem computation_reused (previous : SourceFrontier value) (cached : List (SourcePoint value))
    (request : AccuracyRequest) (accurate : (integralBound previous.cells).width < request.tolerance)
    (oracle : Query request → Reply request) :
    ((computation previous cached request).protocol.run oracle).value = .ok (.reused request accurate) ∧
      ((computation previous cached request).protocol.run oracle).trace = [] := by
  unfold computation
  rw [dif_pos accurate]
  exact ⟨rfl, rfl⟩

/-- Original execution returns the complete cache-aware reciprocal producer continuation. -/
theorem computation_original (previous : SourceFrontier value) (cached : List (SourcePoint value))
    (request : AccuracyRequest) :
    ((computation previous cached request).protocol.run (originalReply request)).value =
      .ok (producer.advanceCached cached previous request) := by
  unfold computation
  by_cases accurate : (integralBound previous.cells).width < request.tolerance
  · rw [dif_pos accurate]
    unfold SourceFrontier.Producer.advanceCached SourceFrontier.Producer.advanceWithBank
    rw [dif_pos accurate]
    rfl
  · rw [dif_neg accurate]
    dsimp only
    rw [Program.bind_execution, Protocol.bind_run_value, freshProgram_original]
    dsimp only
    rw [Observation.computation_original]
    rw [Program.map_execution, Protocol.map_run_value, commonProgram_original]
    dsimp only
    rw [certifiedCommon_original]
    apply congrArg Except.ok
    exact fromCertified_eq producer previous cached request _ _ accurate

/-- Exact replay recovers the complete reciprocal continuation without repeating displayed source calls. -/
theorem computation_replay (previous : SourceFrontier value) (cached : List (SourcePoint value))
    (request : AccuracyRequest) :
    (computation previous cached request).protocol.replayExact
      ((computation previous cached request).protocol.run (originalReply request)).trace =
        .ok (.ok (producer.advanceCached cached previous request)) := by
  rw [(computation previous cached request).protocol.replayExact_run, computation_original]

/-- Replies outside the executed continuation trace preserve the complete result and ordered trace. -/
theorem payload_erasure (previous : SourceFrontier value) (cached : List (SourcePoint value))
    (request : AccuracyRequest) {Payload : Type} (payload : Payload)
    (outside : Payload → Query request → Reply request) :
    (computation previous cached request).protocol.run (Boundary.Trace.overlay
      ((computation previous cached request).protocol.run (originalReply request)).trace (outside payload)) =
      (computation previous cached request).protocol.run (originalReply request) :=
  (computation previous cached request).protocol.annotation_erasure (originalReply request) payload outside

/-- Observe one public persistent reciprocal request from its actual retained history. -/
@[expose] def historyComputation (state : producer.integrationProcess.State) (request : AccuracyRequest) :
    Program (Query request) (Reply request) (Except (Failure request) producer.integrationProcess.State) := by
  if accurate : (integralBound state.1.cells).width < request.tolerance then
    exact .pure (.ok ⟨state.1, RefiningController.History.next state.2 (.reused request accurate)⟩)
  else
    let cached := producer.retainedReadings state.2
    exact (computation state.1 cached request).map fun returned =>
      returned.map fun step => ⟨step.frontier, RefiningController.History.next state.2 step⟩

/-- The accuracy-first history agrees with the original composed continuation. -/
theorem historyComputation_eq (state : producer.integrationProcess.State) (request : AccuracyRequest) :
    historyComputation state request =
      (computation state.1 (producer.retainedReadings state.2) request).map
        (fun returned => returned.map fun step => ⟨step.frontier, RefiningController.History.next state.2 step⟩) := by
  unfold historyComputation
  by_cases accurate : (integralBound state.1.cells).width < request.tolerance
  · rw [dif_pos accurate]
    unfold computation
    rw [dif_pos accurate]
    rfl
  · rw [dif_neg accurate]
    rfl

/-- Original execution returns the complete next public reciprocal integration state. -/
theorem historyComputation_original (state : producer.integrationProcess.State) (request : AccuracyRequest) :
    ((historyComputation state request).protocol.run (originalReply request)).value =
      .ok (producer.integrationProcess.request state request.tolerance request.positive) := by
  rw [historyComputation_eq]
  let cached := producer.retainedReadings state.2
  change (((computation state.1 cached request).map fun returned =>
    returned.map fun step => (⟨step.frontier, RefiningController.History.next state.2 step⟩ :
      producer.integrationProcess.State)).protocol.run (originalReply request)).value = _
  rw [Program.map_execution, Protocol.map_run_value, computation_original]
  rfl

/-- Exact replay recovers the complete public reciprocal integration history. -/
theorem historyComputation_replay (state : producer.integrationProcess.State) (request : AccuracyRequest) :
    (historyComputation state request).protocol.replayExact
      ((historyComputation state request).protocol.run (originalReply request)).trace =
        .ok (.ok (producer.integrationProcess.request state request.tolerance request.positive)) := by
  rw [(historyComputation state request).protocol.replayExact_run, historyComputation_original]

/-- Replies outside the public reciprocal request trace preserve its complete state and ordered trace. -/
theorem historyComputation_payload_erasure (state : producer.integrationProcess.State) (request : AccuracyRequest)
    {Payload : Type} (payload : Payload) (outside : Payload → Query request → Reply request) :
    (historyComputation state request).protocol.run (Boundary.Trace.overlay
      ((historyComputation state request).protocol.run (originalReply request)).trace (outside payload)) =
      (historyComputation state request).protocol.run (originalReply request) :=
  (historyComputation state request).protocol.annotation_erasure (originalReply request) payload outside

end Purelib.Integration.Step.Reciprocal.Observation.Continuation

end
