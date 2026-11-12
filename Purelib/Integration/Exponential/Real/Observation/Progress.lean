module

public import Purelib.Integration.Exponential.Real.Observation
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Retained partial Gaussian work for numerical history requests -/

public section

namespace Purelib.Integration.Exponential.Real.Observation.Progress

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Approximation.Gaussian.Process
open Purelib.Computation.Query
open Purelib.Data.Gaussian
open Purelib.Integration.NumericalFrontier
open Purelib.Integration.NumericalFrontier.Continuous
open Purelib.Integration.NumericalFrontier.Continuous.Observation

/-- The exact original point decision belonging to one numerical query. -/
@[expose] def queryPoint (prepared : Preparation Horner.Real.modulus)
    (_cached : List (NumericalPoint Horner.Real.source)) (request : AccuracyRequest)
    (query : Continuation.Query prepared) : Point × AccuracyRequest :=
  match query with
  | .inl entry => (preparedPoint prepared entry, prepared.pointRequest)
  | .inr (_, child) => (commonPoint child, request)

/-- The original bank-selected branch belonging to one numerical query. -/
@[expose] def queryChoice (prepared : Preparation Horner.Real.modulus)
    (cached : List (NumericalPoint Horner.Real.source)) (request : AccuracyRequest)
    (query : Continuation.Query prepared) :
    NumericalPoint.Selection Horner.Real.source (queryPoint prepared cached request query).1.val
      (queryPoint prepared cached request query).2 :=
  match query with
  | .inl entry => NumericalPoint.selectBank Horner.Real.source cached (preparedPoint prepared entry).val
      prepared.pointRequest
  | .inr (bank, child) => NumericalPoint.selectBank Horner.Real.source bank (commonPoint child).val request

/-- Failure of the selected original fresh or common point, indexed by its actual numerical query. -/
abbrev HandlerFailure (prepared : Preparation Horner.Real.modulus)
    (cached : List (NumericalPoint Horner.Real.source)) (request : AccuracyRequest) (Error : Type)
    (query : Continuation.Query prepared) :=
  SelectionFailure (queryPoint prepared cached request query).1 (queryPoint prepared cached request query).2
    (queryChoice prepared cached request query) Error

/-- Lower the actual numerical query while retaining its selected partial Gaussian state. -/
@[expose] def handlerWith {OuterQuestion OuterReply Error : Type}
    (outerHandler : Query → Program OuterQuestion OuterReply (Except Error Reply)) (invalid : Failure → Error)
    (prepared : Preparation Horner.Real.modulus)
    (cached : List (NumericalPoint Horner.Real.source)) (request : AccuracyRequest)
    (query : Continuation.Query prepared) :
    Program OuterQuestion OuterReply (Except (HandlerFailure prepared cached request Error query)
      (Continuation.Reply prepared cached request)) := by
  cases query with
  | inl entry =>
      exact (selectionWith (preparedPoint prepared entry) outerHandler invalid prepared.pointRequest
        (NumericalPoint.selectBank Horner.Real.source cached (preparedPoint prepared entry).val
          prepared.pointRequest)).map fun result => result.map fun reply =>
            .inl (freshPointReply prepared cached entry reply)
  | inr occurrence =>
      rcases occurrence with ⟨bank, child⟩
      exact (selectionWith (commonPoint child) outerHandler invalid request
        (NumericalPoint.selectBank Horner.Real.source bank (commonPoint child).val request)).map fun result =>
          result.map fun reply => .inr ⟨bank, commonPointReply bank request child reply⟩

/-- Resume an interrupted numerical query from its exact selected point and returned refinement. -/
@[expose] def resumeHandlerWith {OuterQuestion OuterReply Error : Type}
    (outerHandler : Query → Program OuterQuestion OuterReply (Except Error Reply)) (invalid : Failure → Error)
    (prepared : Preparation Horner.Real.modulus)
    (cached : List (NumericalPoint Horner.Real.source)) (request : AccuracyRequest)
    (query : Continuation.Query prepared)
    (pending : Pending (queryPoint prepared cached request query).1 (queryPoint prepared cached request query).2
      (queryChoice prepared cached request query) Error) :
    Program OuterQuestion OuterReply (Except (HandlerFailure prepared cached request Error query)
      (Continuation.Reply prepared cached request)) := by
  cases query with
  | inl entry =>
      exact (resumeWith (preparedPoint prepared entry) outerHandler invalid prepared.pointRequest
        (NumericalPoint.selectBank Horner.Real.source cached (preparedPoint prepared entry).val
          prepared.pointRequest) pending).map fun result => (result.mapError SelectionFailure.pending).map fun reply =>
            .inl (freshPointReply prepared cached entry reply)
  | inr occurrence =>
      rcases occurrence with ⟨bank, child⟩
      exact (resumeWith (commonPoint child) outerHandler invalid request
        (NumericalPoint.selectBank Horner.Real.source bank (commonPoint child).val request) pending).map fun result =>
          (result.mapError SelectionFailure.pending).map fun reply =>
            .inr ⟨bank, commonPointReply bank request child reply⟩

/-- Retrying a pending outer query reads the ball of that query's returned refinement. -/
theorem resumeHandlerWith_trace {OuterQuestion OuterReply Error : Type} [DecidableEq OuterQuestion]
    (outerHandler : Query → Program OuterQuestion OuterReply (Except Error Reply)) (invalid : Failure → Error)
    (prepared : Preparation Horner.Real.modulus)
    (cached : List (NumericalPoint Horner.Real.source)) (request : AccuracyRequest)
    (query : Continuation.Query prepared)
    (pending : Pending (queryPoint prepared cached request query).1 (queryPoint prepared cached request query).2
      (queryChoice prepared cached request query) Error) (oracle : OuterQuestion → OuterReply) :
    ((resumeHandlerWith outerHandler invalid prepared cached request query pending).protocol.run oracle).trace =
      ((outerHandler ((queryPoint prepared cached request query).1, .ball pending.refined.val)).protocol.run
        oracle).trace := by
  cases query with
  | inl entry =>
      unfold resumeHandlerWith
      rw [Program.map_execution, Protocol.map_run_trace]
      exact resumeWith_trace _ _ _ _ _ pending oracle
  | inr occurrence =>
      rcases occurrence with ⟨bank, child⟩
      unfold resumeHandlerWith
      rw [Program.map_execution, Protocol.map_run_trace]
      exact resumeWith_trace _ _ _ _ _ pending oracle

/-- The exact prepared numerical operation and effective bank of a saved real history. -/
@[expose] def prepared (_state : Real.integrationProcess.State) (request : AccuracyRequest) :=
  Preparation.prepare Horner.Real.modulus request

/-- The original history request, before lowering its actual selected point operations. -/
@[expose] def outer (state : Real.integrationProcess.State) (request : AccuracyRequest) :=
  Continuation.historyComputation Horner.Real.modulus state request

/-- The actual point bank supplied by the original saved history. -/
@[expose] def bank (state : Real.integrationProcess.State) :=
  let producer := NumericalFrontier.Continuous.producer Horner.Real.modulus
  Producer.effectiveBank state.1 (producer.retainedReadings state.2)

/-- An interrupted original history request, its exact continuation and point-owned partial work. -/
abbrev HistoryStop (state : Real.integrationProcess.State) (request : AccuracyRequest) (Error : Type) :=
  Program.CheckedStop (outer state request) (HandlerFailure (prepared state request) (bank state) request Error)

/-- Transport a checked substitution along equality of its exact original program. -/
private theorem checkedProgress_transport {Question Reply Value OuterQuestion OuterReply : Type}
    {Error : Question → Type} (handler : (question : Question) →
      Program OuterQuestion OuterReply (Except (Error question) Reply))
    (first second : Program Question Reply Value) (same : first = second) :
    cast (congrArg (fun program : Program Question Reply Value =>
      Program OuterQuestion OuterReply (Except (Program.CheckedStop program Error)
        (Basic.Execution Question Reply Value))) same) (first.substituteCheckedProgress handler) =
      second.substituteCheckedProgress handler := by
  cases same
  rfl

/-- Execute the original saved history through the supplied tagged Gaussian handler. -/
@[expose] def historyWith {OuterQuestion OuterReply Error : Type}
    (outerHandler : Query → Program OuterQuestion OuterReply (Except Error Reply)) (invalid : Failure → Error)
    (state : Real.integrationProcess.State) (request : AccuracyRequest) :
    Program OuterQuestion OuterReply (Except (HistoryStop state request Error)
      (Basic.Execution (Continuation.Query (prepared state request))
        (Continuation.Reply (prepared state request) (bank state) request)
        (Except (Continuation.Failure (prepared state request)) Real.integrationProcess.State))) := by
  if adequate : (integralBound state.1.cells).width < request.tolerance then
    let result : Except (Continuation.Failure (prepared state request)) Real.integrationProcess.State :=
      .ok ⟨state.1, RefiningController.History.next state.2 (.reused request adequate)⟩
    have sameOuter : outer state request = .pure result := by
      unfold outer Continuation.historyComputation Continuation.computationWithBank
        Continuation.certifiedComputationWithBank
      rw [dif_pos adequate]
      rfl
    exact cast (congrArg (fun program : Program (Continuation.Query (prepared state request))
        (Continuation.Reply (prepared state request) (bank state) request)
        (Except (Continuation.Failure (prepared state request)) Real.integrationProcess.State) =>
      Program OuterQuestion OuterReply (Except
        (Program.CheckedStop program (HandlerFailure (prepared state request) (bank state) request Error))
        (Basic.Execution (Continuation.Query (prepared state request))
          (Continuation.Reply (prepared state request) (bank state) request)
          (Except (Continuation.Failure (prepared state request)) Real.integrationProcess.State)))) sameOuter.symm)
      (.pure (.ok ⟨result, []⟩))
  else
    let sharedPrepared := prepared state request
    let producer := NumericalFrontier.Continuous.producer Horner.Real.modulus
    let cached := producer.retainedReadings state.2
    let sharedBank := Producer.effectiveBank state.1 cached
    let realized := Continuation.historyRefiningPrepared Horner.Real.modulus state request
      sharedPrepared rfl cached rfl sharedBank rfl adequate
    have sameOuter : outer state request = realized := by
      unfold outer Continuation.historyComputation Continuation.computationWithBank
        Continuation.certifiedComputationWithBank
      rw [dif_neg adequate]
      rfl
    exact cast (congrArg (fun program : Program (Continuation.Query (prepared state request))
        (Continuation.Reply (prepared state request) (bank state) request)
        (Except (Continuation.Failure (prepared state request)) Real.integrationProcess.State) =>
      Program OuterQuestion OuterReply (Except
        (Program.CheckedStop program (HandlerFailure (prepared state request) (bank state) request Error))
        (Basic.Execution (Continuation.Query (prepared state request))
          (Continuation.Reply (prepared state request) (bank state) request)
          (Except (Continuation.Failure (prepared state request)) Real.integrationProcess.State)))) sameOuter.symm)
      (realized.substituteCheckedProgress (handlerWith outerHandler invalid sharedPrepared sharedBank request))

/-- The shared realization retains the original stopped program and its checked handler. -/
theorem historyWith_eq {OuterQuestion OuterReply Error : Type}
    (outerHandler : Query → Program OuterQuestion OuterReply (Except Error Reply)) (invalid : Failure → Error)
    (state : Real.integrationProcess.State) (request : AccuracyRequest) :
    historyWith outerHandler invalid state request =
      (outer state request).substituteCheckedProgress
        (handlerWith outerHandler invalid (prepared state request) (bank state) request) := by
  unfold historyWith
  by_cases adequate : (integralBound state.1.cells).width < request.tolerance
  · rw [dif_pos adequate]
    refine checkedProgress_transport
      (handlerWith outerHandler invalid (prepared state request) (bank state) request)
      (.pure _) (outer state request) ?_
    unfold outer Continuation.historyComputation Continuation.computationWithBank
      Continuation.certifiedComputationWithBank
    rw [dif_pos adequate]
    rfl
  · rw [dif_neg adequate]
    refine checkedProgress_transport _ _ _ ?_
    unfold outer Continuation.historyComputation Continuation.computationWithBank
      Continuation.certifiedComputationWithBank
    rw [dif_neg adequate]
    rfl

/-- Execute the original saved history on its direct tagged Gaussian surface. -/
@[expose] def history (state : Real.integrationProcess.State) (request : AccuracyRequest) :=
  historyWith forward id state request

/-- Resume the exact stopped point through its original tagged Gaussian handler.

An initial failure retries its saved point decision. A returned refinement
reuses that state and reads only its ball before resuming the captured
numerical continuation. -/
@[expose] def resumeHistoryWith {OuterQuestion OuterReply Error : Type}
    (outerHandler : Query → Program OuterQuestion OuterReply (Except Error Reply)) (invalid : Failure → Error)
    (state : Real.integrationProcess.State) (request : AccuracyRequest) (stopped : HistoryStop state request Error) :
    Program OuterQuestion OuterReply (Except (HistoryStop state request Error)
      (Basic.Execution (Continuation.Query (prepared state request))
        (Continuation.Reply (prepared state request) (bank state) request)
        (Except (Continuation.Failure (prepared state request)) Real.integrationProcess.State))) :=
  let sharedPrepared := prepared state request
  let sharedBank := bank state
  let retry : Program OuterQuestion OuterReply
      (Except (HandlerFailure (prepared state request) (bank state) request Error stopped.question)
        (Continuation.Reply (prepared state request) (bank state) request)) :=
    match stopped.reason with
    | .initial _ => handlerWith outerHandler invalid sharedPrepared sharedBank request stopped.question
    | .pending pending =>
        resumeHandlerWith outerHandler invalid sharedPrepared sharedBank request stopped.question pending
  retry.bind fun returned => match returned with
    | .error error => .pure (.error { stopped with reason := error })
    | .ok reply => stopped.resume (handlerWith outerHandler invalid sharedPrepared sharedBank request)
        reply

/-- Resume a stopped history on the same direct tagged Gaussian surface. -/
@[expose] def resumeHistory (state : Real.integrationProcess.State) (request : AccuracyRequest)
    (stopped : HistoryStop state request Failure) :=
  resumeHistoryWith forward id state request stopped

/-- A pending history resumes at the retained ball, then only its captured continuation. -/
theorem resumeHistoryWith_pending_trace {OuterQuestion OuterReply Error : Type} [DecidableEq OuterQuestion]
    (outerHandler : Query → Program OuterQuestion OuterReply (Except Error Reply)) (invalid : Failure → Error)
    (state : Real.integrationProcess.State) (request : AccuracyRequest) (stopped : HistoryStop state request Error)
    (pending : Pending (queryPoint (prepared state request) (bank state) request stopped.question).1
      (queryPoint (prepared state request) (bank state) request stopped.question).2
      (queryChoice (prepared state request) (bank state) request stopped.question) Error)
    (isPending : stopped.reason = .pending pending) (oracle : OuterQuestion → OuterReply) :
    ((resumeHistoryWith outerHandler invalid state request stopped).protocol.run oracle).trace =
      ((outerHandler ((queryPoint (prepared state request) (bank state) request stopped.question).1,
        .ball pending.refined.val)).protocol.run oracle).trace ++
      match ((resumeHandlerWith outerHandler invalid (prepared state request) (bank state) request
        stopped.question pending).protocol.run oracle).value with
      | .error _ => []
      | .ok reply => ((Program.substituteCheckedProgress
          (handlerWith outerHandler invalid (prepared state request) (bank state) request)
          (stopped.next reply)).protocol.run oracle).trace := by
  unfold resumeHistoryWith
  rw [isPending, Program.bind_execution, Protocol.bind_run_trace]
  rw [resumeHandlerWith_trace]
  cases returned : ((resumeHandlerWith outerHandler invalid (prepared state request) (bank state) request
      stopped.question pending).protocol.run oracle).value with
  | error error => rfl
  | ok reply =>
      dsimp only
      apply congrArg (List.append (((outerHandler
        ((queryPoint (prepared state request) (bank state) request stopped.question).1,
          .ball pending.refined.val)).protocol.run oracle).trace))
      exact Program.CheckedStop.resume_trace
        (handlerWith outerHandler invalid (prepared state request) (bank state) request) stopped reply oracle

/-- Exact replay preserves a resumed history's returned state or later stop. -/
theorem resumeHistoryWith_replay {OuterQuestion OuterReply Error : Type} [DecidableEq OuterQuestion]
    (outerHandler : Query → Program OuterQuestion OuterReply (Except Error Reply)) (invalid : Failure → Error)
    (state : Real.integrationProcess.State) (request : AccuracyRequest) (stopped : HistoryStop state request Error)
    (oracle : OuterQuestion → OuterReply) :
    (resumeHistoryWith outerHandler invalid state request stopped).protocol.replayExact
        ((resumeHistoryWith outerHandler invalid state request stopped).protocol.run oracle).trace =
      .ok ((resumeHistoryWith outerHandler invalid state request stopped).protocol.run oracle).value :=
  (resumeHistoryWith outerHandler invalid state request stopped).protocol.replayExact_run oracle

/-- Changing replies outside a resumed history's actual trace preserves its complete execution. -/
theorem resumeHistoryWith_payload_erasure {OuterQuestion OuterReply Error : Type} [DecidableEq OuterQuestion]
    (outerHandler : Query → Program OuterQuestion OuterReply (Except Error Reply)) (invalid : Failure → Error)
    (state : Real.integrationProcess.State) (request : AccuracyRequest) (stopped : HistoryStop state request Error)
    (oracle : OuterQuestion → OuterReply) {Payload : Type} (payload : Payload)
    (outside : Payload → OuterQuestion → OuterReply) :
    (resumeHistoryWith outerHandler invalid state request stopped).protocol.run (Boundary.Trace.overlay
      ((resumeHistoryWith outerHandler invalid state request stopped).protocol.run oracle).trace (outside payload)) =
        (resumeHistoryWith outerHandler invalid state request stopped).protocol.run oracle :=
  (resumeHistoryWith outerHandler invalid state request stopped).protocol.annotation_erasure oracle payload outside

/-- Error projection commutes with mapping a successful point reply. -/
private theorem map_error_reply {Alpha Beta Error NewError : Type} (result : Except Error Alpha)
    (build : Alpha → Beta) (erase : Error → NewError) :
    (result.map build).mapError erase = (result.mapError erase).map build := by
  cases result <;> rfl

/-- On the direct tagged surface, progress and existing numerical handlers have the same values and traces. -/
theorem handler_compatibility (prepared : Preparation Horner.Real.modulus)
    (cached : List (NumericalPoint Horner.Real.source)) (request : AccuracyRequest)
    (query : Continuation.Query prepared) (oracle : Query → Reply) :
    let progress := (handlerWith forward id prepared cached request query).protocol.run oracle
    let direct := (numericalHandler prepared cached request query).protocol.run oracle
    progress.value.mapError SelectionFailure.failure = direct.value ∧ progress.trace = direct.trace := by
  cases query with
  | inl entry =>
      constructor
      · unfold handlerWith numericalHandler Real.Observation.selection selection
        rw [Program.map_execution, Protocol.map_run_value, Program.map_execution, Protocol.map_run_value,
          Program.map_execution, Protocol.map_run_value]
        exact map_error_reply _ _ _
      · unfold handlerWith numericalHandler Real.Observation.selection selection
        rw [Program.map_execution, Protocol.map_run_trace, Program.map_execution, Protocol.map_run_trace,
          Program.map_execution, Protocol.map_run_trace]
  | inr occurrence =>
      rcases occurrence with ⟨bank, child⟩
      constructor
      · unfold handlerWith numericalHandler Real.Observation.selection selection
        rw [Program.map_execution, Protocol.map_run_value, Program.map_execution, Protocol.map_run_value,
          Program.map_execution, Protocol.map_run_value]
        exact map_error_reply _ _ _
      · unfold handlerWith numericalHandler Real.Observation.selection selection
        rw [Program.map_execution, Protocol.map_run_trace, Program.map_execution, Protocol.map_run_trace,
          Program.map_execution, Protocol.map_run_trace]

/-- Original tagged replies answer each actual fresh or common numerical query. -/
theorem handlerWith_original {OuterQuestion OuterReply Error : Type} [DecidableEq OuterQuestion]
    (outerHandler : Query → Program OuterQuestion OuterReply (Except Error Reply)) (invalid : Failure → Error)
    (prepared : Preparation Horner.Real.modulus) (cached : List (NumericalPoint Horner.Real.source))
    (request : AccuracyRequest) (query : Continuation.Query prepared) (oracle : OuterQuestion → OuterReply)
    (answers : ∀ question, ((outerHandler question).protocol.run oracle).value = .ok (original question)) :
    ((handlerWith outerHandler invalid prepared cached request query).protocol.run oracle).value =
      .ok (Continuation.originalReplyAll prepared cached request query) := by
  cases query with
  | inl entry =>
      unfold handlerWith
      rw [Program.map_execution, Protocol.map_run_value, selectionWith_original _ _ _ _ _ _ answers]
      apply congrArg Except.ok
      apply congrArg Sum.inl
      exact freshPointReply_eq prepared cached entry _
  | inr occurrence =>
      rcases occurrence with ⟨bank, child⟩
      unfold handlerWith
      rw [Program.map_execution, Protocol.map_run_value, selectionWith_original _ _ _ _ _ _ answers]
      apply congrArg Except.ok
      change (Sum.inr ⟨bank, commonPointReply bank request child _⟩ : Continuation.Reply prepared cached request) =
        (Sum.inr ⟨bank, Common.Observation.originalReply bank request child⟩ :
          Continuation.Reply prepared cached request)
      exact congrArg (fun point : Common.Observation.Reply bank request =>
        (Sum.inr ⟨bank, point⟩ : Continuation.Reply prepared cached request))
        (commonPointReply_eq bank request child _)

/-- Original tagged replies finish the exact pending fresh or common point request. -/
theorem resumeHandlerWith_original {OuterQuestion OuterReply Error : Type} [DecidableEq OuterQuestion]
    (outerHandler : Query → Program OuterQuestion OuterReply (Except Error Reply)) (invalid : Failure → Error)
    (prepared : Preparation Horner.Real.modulus) (cached : List (NumericalPoint Horner.Real.source))
    (request : AccuracyRequest) (query : Continuation.Query prepared)
    (pending : Pending (queryPoint prepared cached request query).1 (queryPoint prepared cached request query).2
      (queryChoice prepared cached request query) Error) (oracle : OuterQuestion → OuterReply)
    (answers : ∀ question, ((outerHandler question).protocol.run oracle).value = .ok (original question)) :
    ((resumeHandlerWith outerHandler invalid prepared cached request query pending).protocol.run oracle).value =
      .ok (Continuation.originalReplyAll prepared cached request query) := by
  cases query with
  | inl entry =>
      unfold resumeHandlerWith
      rw [Program.map_execution, Protocol.map_run_value, resumeWith_original _ _ _ _ _ _ _ answers]
      apply congrArg Except.ok
      apply congrArg Sum.inl
      exact freshPointReply_eq prepared cached entry _
  | inr occurrence =>
      rcases occurrence with ⟨bank, child⟩
      unfold resumeHandlerWith
      rw [Program.map_execution, Protocol.map_run_value, resumeWith_original _ _ _ _ _ _ _ answers]
      apply congrArg Except.ok
      change (Sum.inr ⟨bank, commonPointReply bank request child _⟩ : Continuation.Reply prepared cached request) =
        (Sum.inr ⟨bank, Common.Observation.originalReply bank request child⟩ :
          Continuation.Reply prepared cached request)
      exact congrArg (fun point : Common.Observation.Reply bank request =>
        (Sum.inr ⟨bank, point⟩ : Continuation.Reply prepared cached request))
        (commonPointReply_eq bank request child _)

/-- Original tagged replies return the complete original numerical execution and its ordered outer log. -/
theorem historyWith_original {OuterQuestion OuterReply Error : Type} [DecidableEq OuterQuestion]
    (outerHandler : Query → Program OuterQuestion OuterReply (Except Error Reply)) (invalid : Failure → Error)
    (state : Real.integrationProcess.State) (request : AccuracyRequest) (oracle : OuterQuestion → OuterReply)
    (answers : ∀ question, ((outerHandler question).protocol.run oracle).value = .ok (original question)) :
    ((historyWith outerHandler invalid state request).protocol.run oracle).value =
      .ok ((outer state request).protocol.run
        (Continuation.originalReplyAll (prepared state request) (bank state) request)) := by
  rw [historyWith_eq]
  apply Program.substituteCheckedProgress_original
  intro question
  exact handlerWith_original outerHandler invalid (prepared state request) (bank state) request question oracle answers

/-- Original replies resume the retained question and the exact original continuation. -/
theorem resumeHistoryWith_original {OuterQuestion OuterReply Error : Type} [DecidableEq OuterQuestion]
    (outerHandler : Query → Program OuterQuestion OuterReply (Except Error Reply)) (invalid : Failure → Error)
    (state : Real.integrationProcess.State) (request : AccuracyRequest) (stopped : HistoryStop state request Error)
    (oracle : OuterQuestion → OuterReply)
    (answers : ∀ question, ((outerHandler question).protocol.run oracle).value = .ok (original question)) :
    let answer := Continuation.originalReplyAll (prepared state request) (bank state) request
    let reply := answer stopped.question
    ((resumeHistoryWith outerHandler invalid state request stopped).protocol.run oracle).value =
      .ok ⟨((stopped.next reply).protocol.run answer).value,
        stopped.before ++ ⟨stopped.question, reply⟩ :: ((stopped.next reply).protocol.run answer).trace⟩ := by
  unfold resumeHistoryWith
  cases stopped.reason with
  | initial error =>
      rw [Program.bind_execution, Protocol.bind_run_value, handlerWith_original _ _ _ _ _ _ _ answers]
      exact Program.CheckedStop.resume_original _ stopped _ oracle _
        (handlerWith_original outerHandler invalid (prepared state request) (bank state) request · oracle answers)
  | pending pending =>
      rw [Program.bind_execution, Protocol.bind_run_value, resumeHandlerWith_original _ _ _ _ _ _ _ _ answers]
      exact Program.CheckedStop.resume_original _ stopped _ oracle _
        (handlerWith_original outerHandler invalid (prepared state request) (bank state) request · oracle answers)

/-- Progress and existing real history have the same projected values and traces for every oracle. -/
theorem history_compatibility (state : Real.integrationProcess.State) (request : AccuracyRequest)
    (oracle : Query → Reply) :
    let progressed := (history state request).protocol.run oracle
    let direct := (Real.Observation.history state request).protocol.run oracle
    progressed.value.mapError (fun stopped => SelectionFailure.failure stopped.reason) = direct.value ∧
      progressed.trace = direct.trace := by
  unfold history
  rw [historyWith_eq, Real.Observation.history_eq]
  exact Program.substituteCheckedProgress_compatible
    (handlerWith forward id (prepared state request) (bank state) request)
    (numericalHandler (prepared state request) (bank state) request)
    (fun _ => SelectionFailure.failure) (outer state request) oracle
    (handler_compatibility (prepared state request) (bank state) request · oracle)

/-- Exact replay preserves the stopped original history, completed prefix and partial point state. -/
theorem history_replay (state : Real.integrationProcess.State) (request : AccuracyRequest) (oracle : Query → Reply) :
    (history state request).protocol.replayExact ((history state request).protocol.run oracle).trace =
      .ok ((history state request).protocol.run oracle).value :=
  (history state request).protocol.replayExact_run oracle

/-- Replies outside the actual tagged history trace preserve its complete progress. -/
theorem history_payload_erasure (state : Real.integrationProcess.State) (request : AccuracyRequest)
    (oracle : Query → Reply) {Payload : Type} (payload : Payload) (outside : Payload → Query → Reply) :
    let program := history state request
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run oracle).trace (outside payload)) =
      program.protocol.run oracle :=
  (history state request).protocol.annotation_erasure oracle payload outside

end Purelib.Integration.Exponential.Real.Observation.Progress

end
