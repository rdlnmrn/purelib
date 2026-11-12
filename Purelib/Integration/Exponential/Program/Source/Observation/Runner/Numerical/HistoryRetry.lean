module

public import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical
public import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical.Retry

/-! # Continue an interrupted original production and numerical history -/

public section

namespace Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical.HistoryRetry

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Nat.Schedule
open Purelib.Integration.Exponential
open Purelib.Integration.Exponential.Program.Source.Observation.Numerical
open Purelib.Integration.Exponential.Real.Observation
open Purelib.Integration.NumericalFrontier.Continuous.Observation

variable {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride} {extraDepth rightExtra : Nat}
variable (input : Numerical.Input policy rightPolicy schedule rightSchedule extraDepth rightExtra)

set_option genInjectivity false in
/-- The actual returned production owner and its stopped numerical-history execution. -/
structure Request where
  /-- The actual completed original production runner. -/ production : Full.Result input.production
  /-- The actual tagged history execution, including its failed operation. -/ execution :
    NumericalProgressExecution input
  /-- The original numerical continuation and its retained partial point work. -/ stopped : NumericalStop input
  /-- The actual tagged execution returned this exact stop. -/ returned : execution.value = .error stopped
  /-- Earlier tagged history attempts, in the order in which they were returned. -/
  earlier : List (NumericalProgressExecution input)

/-- Extract the original retry owner from a stopped mixed numerical history. -/
@[expose] def ofFailure (failure : Numerical.Failure input) : Option (Request input) :=
  match failure with
  | .numericalStop actualProduction execution stopped returned =>
      some ⟨actualProduction, execution, stopped, returned, []⟩
  | _ => none

set_option genInjectivity false in
/-- A resumed history retains its prior owner, actual new execution and typed outcome. -/
structure Outcome where
  /-- The original stopped request, including earlier tagged attempts. -/ previous : Request input
  /-- The actual newly returned tagged history execution. -/ execution : NumericalProgressExecution input
  /-- The result after this history and any subsequent common-point work. -/
  result : Except (Numerical.Failure input) (Numerical.Result input)

/-- Continue a later actual stop while retaining both previous and newly returned attempts. -/
def Outcome.next (outcome : Outcome input) : Option (Request input) :=
  match returned : outcome.execution.value with
  | .error stopped => some ⟨outcome.previous.production, outcome.execution, stopped, returned,
      outcome.previous.earlier ++ [outcome.previous.execution]⟩
  | .ok _ => none

/-- Resume the actual stopped history through the same original tagged Gaussian handler. -/
def history (retry : Request input) :=
  Progress.resumeHistoryWith (Numerical.numericalHandler input) NumericalSourceFailure.gaussian
    input.numerical input.numericalRequest retry.stopped

/-- Original replies resume the retained prefix and exact original numerical continuation. -/
theorem history_original (retry : Request input) :
    let answer := Continuation.originalReplyAll
      (Progress.prepared input.numerical input.numericalRequest)
      (Progress.bank input.numerical) input.numericalRequest
    let reply := answer retry.stopped.question
    ((history input retry).protocol.run (Numerical.originalReply input)).value =
      .ok ⟨((retry.stopped.next reply).protocol.run answer).value,
        retry.stopped.before ++ ⟨retry.stopped.question, reply⟩ ::
          ((retry.stopped.next reply).protocol.run answer).trace⟩ := by
  unfold history
  exact Progress.resumeHistoryWith_original (Numerical.numericalHandler input)
    NumericalSourceFailure.gaussian input.numerical input.numericalRequest retry.stopped
    (Numerical.originalReply input) (Numerical.numericalHandler_original input)

/-- Record the exact tagged retry execution without repeating any request. -/
def recording (retry : Request input) :=
  (history input retry).substituteChecked (Program.forward id (fun _ reply => reply))

/-- Recording returns the complete actual tagged retry execution for every oracle. -/
theorem recording_value (retry : Request input) (oracle : Numerical.Question input → Numerical.Reply input) :
    ((recording input retry).protocol.run oracle).value = .ok ((history input retry).protocol.run oracle) := by
  unfold recording
  apply Program.substituteChecked_value
  intro question
  rfl

/-- Recording emits the actual ordered tagged retry requests and their returned replies. -/
theorem recording_trace (retry : Request input) (oracle : Numerical.Question input → Numerical.Reply input) :
    ((recording input retry).protocol.run oracle).trace =
      ((history input retry).protocol.run oracle).trace.map
        (fun exchange => ⟨exchange.query, oracle exchange.query⟩) :=
  Program.substituteChecked_forward_trace id (fun _ reply => reply) (history input retry) oracle

/-- Resume the stopped history while retaining the actual tagged attempt across every outcome. -/
def computationProgress (retry : Request input) :
    Program (Numerical.Question input) (Numerical.Reply input) (Outcome input) :=
  (recording input retry).bind fun result => match result with
    | .error impossible => nomatch impossible
    | .ok execution => match returned : execution.value with
      | .error stopped => .pure ⟨retry, execution, .error (.numericalStop retry.production execution stopped returned)⟩
      | .ok history => match success : history.value with
        | .error failure =>
            .pure ⟨retry, execution, .error (.numericalHistory retry.production history failure success)⟩
        | .ok state => (Numerical.commonFinish input retry.production ⟨history, state, success⟩).map
            fun result => ⟨retry, execution, result⟩

/-- Resume the stopped history and continue the original common comparison without rerunning production. -/
def computation (retry : Request input) : Program (Numerical.Question input) (Numerical.Reply input)
    (Except (Numerical.Failure input) (Numerical.Result input)) :=
  (computationProgress input retry).map Outcome.result

/-- The ordinary retry returns the actual typed result of the progress-bearing retry. -/
theorem computation_value (retry : Request input) (oracle : Numerical.Question input → Numerical.Reply input) :
    ((computation input retry).protocol.run oracle).value =
      ((computationProgress input retry).protocol.run oracle).value.result := by
  unfold computation
  rw [Program.map_execution, Protocol.map_run_value]

/-- Projecting the retry result preserves every displayed query and reply. -/
theorem computation_trace (retry : Request input) (oracle : Numerical.Question input → Numerical.Reply input) :
    ((computation input retry).protocol.run oracle).trace =
      ((computationProgress input retry).protocol.run oracle).trace := by
  unfold computation
  rw [Program.map_execution, Protocol.map_run_trace]

/-- A continued stop keeps the earlier attempts in order and the exact newly returned execution. -/
theorem Outcome.next_owner (outcome : Outcome input) (next : Request input)
    (returned : Outcome.next input outcome = some next) :
    next.production = outcome.previous.production ∧ next.execution = outcome.execution ∧
      next.earlier = outcome.previous.earlier ++ [outcome.previous.execution] := by
  rcases outcome with ⟨previous, ⟨value, trace⟩, result⟩
  cases value with
  | error stopped =>
      change some ⟨previous.production, ⟨.error stopped, trace⟩, stopped, rfl,
        previous.earlier ++ [previous.execution]⟩ = some next at returned
      cases returned
      exact ⟨rfl, rfl, rfl⟩
  | ok completed =>
      change none = some next at returned
      cases returned

/-- Every retry outcome retains its exact input owner and actual tagged history execution. -/
theorem computationProgress_owner (retry : Request input)
    (oracle : Numerical.Question input → Numerical.Reply input) :
    let outcome := ((computationProgress input retry).protocol.run oracle).value
    outcome.previous = retry ∧ outcome.execution = ((history input retry).protocol.run oracle) := by
  unfold computationProgress
  rw [Program.bind_execution, Protocol.bind_run_value, recording_value]
  dsimp only
  split
  next stopped returned => exact ⟨rfl, rfl⟩
  next history returned =>
      split
      next failure success => exact ⟨rfl, rfl⟩
      next state success =>
          rw [Program.map_execution, Protocol.map_run_value]
          exact ⟨rfl, rfl⟩

/-- A completed resumed history continues through the actual common comparison.

The production owner and numerical state are the ones retained by this retry;
the returned execution may contain an earlier prefix with arbitrary valid replies.
-/
theorem computationProgress_common (retry : Request input)
    (oracle : Numerical.Question input → Numerical.Reply input)
    (completed : Numerical.HistoryExecution input) (state : Real.integrationProcess.State)
    (returned : ((history input retry).protocol.run oracle).value = .ok completed)
    (success : completed.value = .ok state) :
    ((computationProgress input retry).protocol.run oracle).value.result =
      ((Numerical.commonFinish input retry.production ⟨completed, state, success⟩).protocol.run oracle).value := by
  unfold computationProgress
  rw [Program.bind_execution, Protocol.bind_run_value, recording_value]
  dsimp only
  split
  next stopped failed =>
    have impossible : Except.error stopped = Except.ok completed := failed.symm.trans returned
    cases impossible
  next actual recorded =>
    have same : actual = completed := Except.ok.inj (recorded.symm.trans returned)
    cases same
    split
    next failure failed =>
      have impossible : Except.error failure = Except.ok state := failed.symm.trans success
      cases impossible
    next actual successful =>
      have same : actual = state := Except.ok.inj (successful.symm.trans success)
      cases same
      rw [Program.map_execution, Protocol.map_run_value]

/-- Original common replies compare the actual successfully resumed history.

The original production owner and returned numerical execution are retained;
the preceding history may have been acquired using different valid replies.
-/
theorem computationProgress_common_original (retry : Request input)
    (completed : Numerical.HistoryExecution input) (state : Real.integrationProcess.State)
    (returned : ((history input retry).protocol.run (Numerical.originalReply input)).value = .ok completed)
    (success : completed.value = .ok state) :
    ∃ result : Numerical.Result input,
      ((computationProgress input retry).protocol.run (Numerical.originalReply input)).value.result = .ok result ∧
      result.production = retry.production ∧ result.numerical = ⟨completed, state, success⟩ := by
  obtain ⟨result, finished, production, numerical, _, _⟩ :=
    Numerical.commonFinish_original input retry.production ⟨completed, state, success⟩
  refine ⟨result, ?_, production, numerical⟩
  rw [computationProgress_common input retry (Numerical.originalReply input) completed state returned success]
  exact finished

/-- Original replies retain the actual retry owner and complete resumed original numerical execution. -/
theorem computationProgress_original (retry : Request input) :
    let answer := Continuation.originalReplyAll
      (Progress.prepared input.numerical input.numericalRequest)
      (Progress.bank input.numerical) input.numericalRequest
    let reply := answer retry.stopped.question
    let outcome := ((computationProgress input retry).protocol.run (Numerical.originalReply input)).value
    outcome.previous = retry ∧ outcome.execution.value =
      .ok ⟨((retry.stopped.next reply).protocol.run answer).value,
        retry.stopped.before ++ ⟨retry.stopped.question, reply⟩ ::
          ((retry.stopped.next reply).protocol.run answer).trace⟩ := by
  have owner := computationProgress_owner input retry (Numerical.originalReply input)
  refine ⟨owner.1, ?_⟩
  rw [owner.2]
  exact history_original input retry

/-- The actual outer execution of one interrupted common-point retry. -/
@[expose] def CommonExecution (retry : Retry.Request input) :=
  Basic.Execution (Numerical.Question input) (Numerical.Reply input)
    (Except Empty (Basic.Execution Points.Query (Option (Points.Reply (Retry.depth input retry.production)))
      (Points.Resume.Result (Retry.depth input retry.production) (Retry.left input retry.production)
        retry.numerical.state.1 (Retry.effectiveLeft input retry.production)
        (Retry.effectiveRight input retry.numerical) input.pointRequest retry.savedLeft retry.savedRight
        retry.stopped)))

set_option genInjectivity false in
/-- An actual common retry together with the history attempt that reached it.

The original common failure remains linked to the history outcome. Later
common attempts retain the same production and numerical owners, while their
complete displayed executions remain ordered in `earlier`.
-/
structure CommonRequest where
  /-- The complete tagged history attempt and all its earlier numerical attempts. -/ history :
    Basic.Execution (Numerical.Question input) (Numerical.Reply input) (Outcome input)
  /-- The common failure returned by that actual history attempt. -/ failure : Numerical.Failure input
  /-- The history attempt returned this failure. -/ failure_eq : history.value.result = .error failure
  /-- The original common retry extracted from that failure. -/ original : Retry.Request input
  /-- Extraction preserves the original failure owner. -/ original_eq : Retry.ofFailure input failure = some original
  /-- The current common retry and its exact stopped batch. -/ current : Retry.Request input
  /-- Later common retries retain the original production owner. -/ production_eq :
    current.production = original.production
  /-- Later common retries retain the original completed numerical owner. -/ numerical_eq :
    current.numerical = original.numerical
  /-- Earlier common retries and their complete actual displayed executions, in order. -/
  earlier : List (Σ retry : Retry.Request input, CommonExecution input retry)

/-- Extract the common retry directly from the complete tagged history execution. -/
def CommonRequest.ofExecution
    (history : Basic.Execution (Numerical.Question input) (Numerical.Reply input) (Outcome input)) :
    Option (CommonRequest input) :=
  match returned : history.value.result with
  | .ok _ => none
  | .error failure => match extracted : Retry.ofFailure input failure with
    | none => none
    | some original => some ⟨history, failure, returned, original, extracted, original, rfl, rfl, []⟩

set_option genInjectivity false in
/-- A common retry retains its complete input owner and actual displayed execution. -/
structure CommonOutcome where
  /-- The original history and current common retry. -/ previous : CommonRequest input
  /-- The complete newly returned tagged common execution. -/ execution : CommonExecution input previous.current

/-- Record the actual common retry once without repeating its source calls. -/
def commonRecording (request : CommonRequest input) :=
  (Retry.computation input request.current).substituteChecked (Program.forward id (fun _ reply => reply))

/-- Original combined replies record the exact underlying common retry. -/
theorem commonRecording_value (request : CommonRequest input)
    (oracle : Numerical.Question input → Numerical.Reply input) :
    ((commonRecording input request).protocol.run oracle).value =
      .ok ((Retry.computation input request.current).protocol.run oracle) := by
  unfold commonRecording
  apply Program.substituteChecked_value
  intro question
  rfl

/-- Run the original common retry, retaining its preceding history and exact tagged execution. -/
def commonComputation (request : CommonRequest input) :
    Program (Numerical.Question input) (Numerical.Reply input) (CommonOutcome input) :=
  (commonRecording input request).map fun result => match result with
    | .error impossible => nomatch impossible
    | .ok execution => ⟨request, execution⟩

/-- Every common outcome retains the exact input owner and newly returned execution. -/
theorem commonComputation_owner (request : CommonRequest input)
    (oracle : Numerical.Question input → Numerical.Reply input) :
    ((commonComputation input request).protocol.run oracle).value =
      ⟨request, ((Retry.computation input request.current).protocol.run oracle)⟩ := by
  unfold commonComputation
  rw [Program.map_execution, Protocol.map_run_value, commonRecording_value]

/-- Continue a later stopped common batch while retaining all earlier actual executions. -/
def CommonOutcome.next (outcome : CommonOutcome input) : Option (CommonRequest input) :=
  match outcome.execution.value with
  | .error impossible => nomatch impossible
  | .ok execution => match execution.value with
    | .invalid _ => none
    | .completed _ _ _ _ => none
    | .pending next =>
        let current := Retry.Request.withPending input outcome.previous.current next
        some { outcome.previous with
          current := current
          production_eq := outcome.previous.production_eq
          numerical_eq := outcome.previous.numerical_eq
          earlier := outcome.previous.earlier ++ [⟨outcome.previous.current, outcome.execution⟩] }
    | .later point next =>
        let current := Retry.Request.withLater input outcome.previous.current point next
        some { outcome.previous with
          current := current
          production_eq := outcome.previous.production_eq
          numerical_eq := outcome.previous.numerical_eq
          earlier := outcome.previous.earlier ++ [⟨outcome.previous.current, outcome.execution⟩] }

/-- A later common stop retains its original history and appends the actual tagged attempt. -/
theorem CommonOutcome.next_owner (outcome : CommonOutcome input) (next : CommonRequest input)
    (returned : CommonOutcome.next input outcome = some next) :
    next.history = outcome.previous.history ∧
      next.current.production = outcome.previous.current.production ∧
      next.current.numerical = outcome.previous.current.numerical ∧
      next.earlier = outcome.previous.earlier ++ [⟨outcome.previous.current, outcome.execution⟩] := by
  rcases outcome with ⟨previous, ⟨value, trace⟩⟩
  cases value with
  | error impossible => cases impossible
  | ok execution =>
      rcases execution with ⟨value, sourceTrace⟩
      cases value with
      | invalid invalid => cases returned
      | completed point suffix common same => cases returned
      | pending stopped => cases returned; exact ⟨rfl, rfl, rfl, rfl⟩
      | later point stopped => cases returned; exact ⟨rfl, rfl, rfl, rfl⟩

/-- Exact replay retains the earlier history and the actual completed common retry. -/
theorem common_replay (request : CommonRequest input) (oracle : Numerical.Question input → Numerical.Reply input) :
    (commonComputation input request).protocol.replayExact
        ((commonComputation input request).protocol.run oracle).trace =
      .ok ((commonComputation input request).protocol.run oracle).value :=
  (commonComputation input request).protocol.replayExact_run oracle

/-- Changing replies outside the actual common retry trace preserves its retained owners and work. -/
theorem common_payload_erasure (request : CommonRequest input)
    (oracle : Numerical.Question input → Numerical.Reply input) {Payload : Type}
    (payload : Payload) (outside : Payload → Numerical.Question input → Numerical.Reply input) :
    (commonComputation input request).protocol.run (Boundary.Trace.overlay
      ((commonComputation input request).protocol.run oracle).trace (outside payload)) =
        (commonComputation input request).protocol.run oracle :=
  (commonComputation input request).protocol.annotation_erasure oracle payload outside

/-- Exact replay preserves the retained earlier owner, new execution and outcome. -/
theorem progress_replay (retry : Request input) (oracle : Numerical.Question input → Numerical.Reply input) :
    (computationProgress input retry).protocol.replayExact
      ((computationProgress input retry).protocol.run oracle).trace =
      .ok ((computationProgress input retry).protocol.run oracle).value :=
  (computationProgress input retry).protocol.replayExact_run oracle

/-- Replies outside the actual progress trace preserve every retained attempt. -/
theorem progress_payload_erasure (retry : Request input) (oracle : Numerical.Question input → Numerical.Reply input)
    {Payload : Type} (payload : Payload) (outside : Payload → Numerical.Question input → Numerical.Reply input) :
    (computationProgress input retry).protocol.run (Boundary.Trace.overlay
      ((computationProgress input retry).protocol.run oracle).trace (outside payload)) =
        (computationProgress input retry).protocol.run oracle :=
  (computationProgress input retry).protocol.annotation_erasure oracle payload outside

/-- Exact replay preserves every completed retry or later typed failure. -/
theorem replay (retry : Request input) (oracle : Numerical.Question input → Numerical.Reply input) :
    (computation input retry).protocol.replayExact ((computation input retry).protocol.run oracle).trace =
      .ok ((computation input retry).protocol.run oracle).value :=
  (computation input retry).protocol.replayExact_run oracle

/-- Outside replies cannot affect the actual resumed history and common comparison. -/
theorem payload_erasure (retry : Request input) (oracle : Numerical.Question input → Numerical.Reply input)
    {Payload : Type} (payload : Payload) (outside : Payload → Numerical.Question input → Numerical.Reply input) :
    (computation input retry).protocol.run (Boundary.Trace.overlay
      ((computation input retry).protocol.run oracle).trace (outside payload)) =
        (computation input retry).protocol.run oracle :=
  (computation input retry).protocol.annotation_erasure oracle payload outside

end Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical.HistoryRetry

end
