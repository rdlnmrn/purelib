module

public import Purelib.Integration.Exponential.Real.Paired.Frontier
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Paired observations through saved exponential integration

The original real numerical integration executes first and retains its complete
ordered execution. The actual returned frontier is then observed with a retained
paired bank. The resulting Gaussian trace records both stages in execution order.
-/

public section

namespace Purelib.Integration.Exponential.Real.Paired.History

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Computation.Query
open Purelib.Integration.Exponential.Real.Observation
open Purelib.Integration.NumericalFrontier
open Purelib.Integration.NumericalFrontier.Continuous
open Purelib.Integration.NumericalFrontier.Continuous.Observation

/-- The exact original numerical execution of a saved exponential integration request. -/
abbrev Execution (state : Real.integrationProcess.State) (request : AccuracyRequest) :=
  let prepared := Preparation.prepare Horner.Real.modulus request
  let producer := NumericalFrontier.Continuous.producer Horner.Real.modulus
  let bank := Producer.effectiveBank state.1 (producer.retainedReadings state.2)
  Basic.Execution (Continuation.Query prepared) (Continuation.Reply prepared bank request)
    (Except (Continuation.Failure prepared) Real.integrationProcess.State)

set_option genInjectivity false in
/-- The original real numerical execution and its paired frontier observation or typed failure. -/
inductive Result (state : Real.integrationProcess.State) (request : AccuracyRequest) where
  /-- The original numerical integration failed before producing a frontier. -/
  | numerical (execution : Execution state request)
      (invalid : Continuation.Failure (Preparation.prepare Horner.Real.modulus request))
      (same : execution.value = .error invalid)
  /-- The paired observation retains the actual returned integration state and all finite progress. -/
  | paired (execution : Execution state request) (next : Real.integrationProcess.State)
      (same : execution.value = .ok next) (progress : Frontier.Progress next.1)

constructive_injectivity Result

/-- Continue the original numerical integration and pair its actual returned frontier.

The returned numerical execution contains its original ordered point replies.
The paired progress retains the same frontier's original occurrences, saved
states and bank, including a typed failure and pending work when interrupted. -/
@[expose] def observe (state : Real.integrationProcess.State) (request imaginary : AccuracyRequest)
    (bank : List Frontier.Saved) : Program Query Reply (Except Failure (Result state request)) :=
  (history state request).bind fun result => match result with
    | .error invalid => .pure (.error invalid)
    | .ok execution => match same : execution.value with
      | .error invalid => .pure (.ok (.numerical execution invalid same))
      | .ok next => (Frontier.observeFrontier next.1 imaginary bank).map fun progress =>
          .ok (.paired execution next same progress)

/-- Exact replay returns the same original integration execution and paired progress. -/
theorem replay (state : Real.integrationProcess.State) (request imaginary : AccuracyRequest)
    (bank : List Frontier.Saved) (oracle : Query → Reply) :
    let program := observe state request imaginary bank
    program.protocol.replayExact (program.protocol.run oracle).trace = .ok (program.protocol.run oracle).value :=
  (observe state request imaginary bank).protocol.replayExact_run oracle

/-- Original tagged Gaussian replies return the original saved numerical state and a completed paired frontier. -/
theorem observe_original_finished (state : Real.integrationProcess.State) (request imaginary : AccuracyRequest)
    (bank : List Frontier.Saved) :
    let prepared := Preparation.prepare Horner.Real.modulus request
    let producer := NumericalFrontier.Continuous.producer Horner.Real.modulus
    let effective := Producer.effectiveBank state.1 (producer.retainedReadings state.2)
    let canonical := (Continuation.historyComputation Horner.Real.modulus state request).protocol.run
      (Continuation.originalReplyAll prepared effective request)
    ∃ execution next same progress,
      ((observe state request imaginary bank).protocol.run original).value =
        .ok (.paired execution next same progress) ∧
      execution = canonical ∧
      next = Real.integrationProcess.request state request.tolerance request.positive ∧
      progress.pending = [] ∧ progress.failure = none ∧
      progress.completed.map (fun entry => entry.occurrence) = Frontier.occurrences next.1 ∧
      (∀ entry ∈ progress.completed, entry.state.paired.imaginary.interval.width < imaginary.tolerance) := by
  let producer := NumericalFrontier.Continuous.producer Horner.Real.modulus
  let prepared := Preparation.prepare Horner.Real.modulus request
  let cached := producer.retainedReadings state.2
  let effective := Producer.effectiveBank state.1 cached
  let execution : Execution state request :=
    (Continuation.historyComputation Horner.Real.modulus state request).protocol.run
      (Continuation.originalReplyAll prepared effective request)
  let next := Real.integrationProcess.request state request.tolerance request.positive
  have same : execution.value = .ok next :=
    Continuation.historyComputation_original Horner.Real.modulus state request
  let progress := ((Frontier.observeFrontier next.1 imaginary bank).protocol.run original).value
  have finished := Frontier.observeFrontier_original_finished next.1 imaginary bank
  have ordered := Frontier.observeFrontier_original_order next.1 imaginary bank
  have accurate := Frontier.observeFrontier_original_accurate next.1 imaginary bank
  refine ⟨execution, next, same, progress, ?_, rfl, rfl, finished.1, finished.2, ordered, accurate⟩
  unfold observe
  rw [Program.bind_execution, Protocol.bind_run_value, Real.Observation.history_original]
  change (((match same : execution.value with
    | .error invalid => (Program.pure (.ok (.numerical execution invalid same)) :
        Program Query Reply (Except Failure (Result state request)))
    | .ok returned => (Frontier.observeFrontier returned.1 imaginary bank).map fun progress =>
        .ok (.paired execution returned same progress)).protocol.run original).value) = _
  revert same
  cases execution with
  | mk value trace =>
      cases value with
      | error invalid =>
          intro same
          cases same
      | ok returned =>
          intro same
          cases same
          rw [Program.map_execution, Protocol.map_run_value]

end Purelib.Integration.Exponential.Real.Paired.History

end
