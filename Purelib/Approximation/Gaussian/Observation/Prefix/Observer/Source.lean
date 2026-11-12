module

public import Purelib.Approximation.Gaussian.Observation.Prefix.Observer
public import Purelib.Computation.Machine.Numerical.Cached
import Purelib.Computation.Machine.Numerical.Simulation
import Purelib.Computation.Query.Path
public import Purelib.Approximation.Gaussian.Observation.Prefix.Source
public import Purelib.Approximation.Gaussian.Observation.Prefix.Continuation
import Purelib.Approximation.Gaussian.Observation.Cursor.Observer
import Purelib.Data.List.GetD
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Map

/-!
# Cached execution of canonical numerical observers

The original canonical snapshot is consumed once per new mixed request.
Recalls reuse the exact cached occurrence. The complete ordered execution
agrees with the same finite observer's pure path interpretation, and its
actual final proper box constructs unconditional joint rational admission.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Prefix.Observer.Source

open Purelib
open Purelib.Computation.Machine
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Observation
open Purelib.Approximation.Gaussian.Observation.Observer hiding Instruction Frame
open Purelib.Approximation.Gaussian.Observation.Cursor.Observer (Instruction Frame)
open Purelib.Computation.Query

set_option genInjectivity false in
/-- An actual cached canonical recording is indexed by the same mixed observer path and saved trace. -/
structure Context (origin : Prefix.Source.Snapshot) (state : Observer.State) where
  /-- The actual original cursor history, cached replies and ordered occurrences. -/ recording :
    Prefix.Source.Recording origin
  /-- The actual newly issued request path is the observer's exact numerical path. -/ pathEq :
    recording.path = state.path
  /-- The actual ordered numerical trace is the observer's exact saved trace. -/ pastEq :
    recording.trace = state.past

namespace Context

/-- Start the original mixed source and finite observer with the same empty path and trace. -/
def initial (origin : Prefix.Source.Snapshot) (registers : List Value) :
    Context origin (Observer.State.initial registers) :=
  ⟨Prefix.Source.Recording.start origin, Prefix.Source.Recording.start_path origin,
    Prefix.Source.Recording.start_trace origin⟩

/-- Transport the same cached recording through a pure numerical transition. -/
@[expose] def transport {origin : Prefix.Source.Snapshot}
    {state next : Observer.State} (context : Context origin state)
    (pathEq : next.path = state.path) (pastEq : next.past = state.past) : Context origin next :=
  ⟨context.recording, context.pathEq.trans pathEq.symm, context.pastEq.trans pastEq.symm⟩

end Context

/-- One actual cached reply and the next context retain this same original context and displayed query. -/
abbrev QueryResult {origin : Prefix.Source.Snapshot} {state : Observer.State}
    (context : Context origin state) (query : Observer.Query) :=
  Numerical.Cached.Answer (Context origin) Observer.replyRegisters
    (Prefix.Source.answer origin) context query

namespace QueryResult

/-- The actual next recording appends this same complete numerical reply at the original displayed question. -/
theorem traceEq {origin : Prefix.Source.Snapshot} {state : Observer.State}
    {context : Context origin state} {query : Observer.Query} (result : QueryResult context query) :
    result.next.recording.trace = context.recording.trace ++ [⟨query.question state, result.reply⟩] :=
  result.next.pastEq.trans
    (congrArg (fun (trace : Basic.Trace Cursor.Question Reply) => trace ++ [⟨query.question state, result.reply⟩])
      context.pastEq.symm)

end QueryResult

/-- Answer one legal mixed query from its actual current canonical cache or exact retained old occurrence. -/
def answer {origin : Prefix.Source.Snapshot} {state : Observer.State}
    (context : Context origin state) (query : Observer.Query) (legal : query.Legal state) :
    QueryResult context query := by
  cases query with
  | request nextRequest =>
      let recording := context.recording.request nextRequest
      let reply := recording.current.reply
      have questionEq : (⟨context.recording.path, nextRequest⟩ : Cursor.Question) =
          (Numerical.Query.request nextRequest).question state :=
        congrArg (fun path => Path.Question.mk path nextRequest) context.pathEq
      exact
        { reply := reply
          next :=
            { recording := recording
              pathEq := (context.recording.request_path nextRequest).trans
                (congrArg (fun path => path ++ [nextRequest]) context.pathEq)
              pastEq := (context.recording.request_trace nextRequest).trans
                (congrArg₂ List.append context.pastEq
                  (congrArg (fun question => [(⟨question, reply⟩ : Basic.Exchange Cursor.Question Reply)])
                    questionEq)) }
          replyEq := (context.recording.request_reply nextRequest).trans
            (congrArg (Prefix.Source.answer origin) questionEq) }
  | recall index entry =>
      have projected : (Data.List.getElem? context.recording.occurrences index).map
          Prefix.Source.Occurrence.exchange = some entry := by
        rewrite [← Data.List.getElem?_map, ← context.recording.traceEq, context.pastEq]
        exact legal
      cases found : Data.List.getElem? context.recording.occurrences index with
      | none => rewrite [found] at projected; nomatch projected
      | some occurrence =>
          have exchangeEq : occurrence.exchange = entry := by
            rewrite [found] at projected
            exact congrArg (fun selected : Option (Basic.Exchange Cursor.Question Reply) => selected.getD entry)
              projected
          have member := Data.List.mem_of_getElem? context.recording.occurrences index occurrence found
          let recording := context.recording.recall occurrence member
          let reply := occurrence.reply
          have questionEq : occurrence.question = entry.query := congrArg Basic.Exchange.query exchangeEq
          have appended : occurrence.exchange = (⟨entry.query, reply⟩ : Basic.Exchange Cursor.Question Reply) :=
            congrArg (fun question => (⟨question, reply⟩ : Basic.Exchange Cursor.Question Reply)) questionEq
          exact
            { reply := reply
              next :=
                { recording := recording
                  pathEq := (context.recording.recall_path occurrence member).trans context.pathEq
                  pastEq := (context.recording.recall_trace occurrence member).trans
                    (congrArg₂ List.append context.pastEq (congrArg (fun exchange => [exchange]) appended)) }
              replyEq := occurrence.answerEq.trans (congrArg (Prefix.Source.answer origin) questionEq) }

/-- A cached mixed source execution retains its final numerical state, actual recording and finite outcome. -/
abbrev Execution (origin : Prefix.Source.Snapshot) :=
  Numerical.Cached.Execution Instruction (Context origin)

namespace Execution

/-- Read the actual new geometric-handler calls from this same retained source recording, excluding recalls. -/
@[expose] def requestCount {origin : Prefix.Source.Snapshot} (execution : Execution origin) : Nat :=
  execution.context.recording.requestCount

/-- Read the original retained geometric bit constructions independently of numerical transition fuel. -/
@[expose] def bitSteps {origin : Prefix.Source.Snapshot} (execution : Execution origin) : Nat :=
  execution.context.recording.bitSteps

/-- Read the actual direct inner-box accuracy constructions from the same retained source recording. -/
@[expose] def enclosureSteps {origin : Prefix.Source.Snapshot} (execution : Execution origin) : Nat :=
  execution.context.recording.enclosureSteps

/-- Read the candidate polynomial evaluations cached by those original geometric constructions. -/
@[expose] def evaluationCount {origin : Prefix.Source.Snapshot} (execution : Execution origin) : Nat :=
  execution.context.recording.evaluationCount

/-- Read the sum of the original finite candidate bounds from those same cached constructions. -/
@[expose] def evaluationBound {origin : Prefix.Source.Snapshot} (execution : Execution origin) : Nat :=
  execution.context.recording.evaluationBound

/-- The counted new handler calls are exactly this actual numerical state's original request path. -/
theorem requestCount_eq_state_path {origin : Prefix.Source.Snapshot} (execution : Execution origin) :
    execution.requestCount = execution.state.path.length :=
  execution.context.recording.requestCount_eq.trans (congrArg List.length execution.context.pathEq)

/-- Every actual candidate evaluation is paid by its same retained original finite search bound. -/
theorem evaluationCount_le {origin : Prefix.Source.Snapshot} (execution : Execution origin) :
    execution.evaluationCount ≤ execution.evaluationBound := execution.context.recording.evaluationCount_le

/-- Read the exact cached numerical outcome and complete ordered mixed trace. -/
@[expose] def numerical {origin : Prefix.Source.Snapshot}
    (execution : Execution origin) : Basic.Execution Cursor.Question Reply Outcome :=
  ⟨execution.outcome, execution.context.recording.trace⟩

/-- Every actual canonical observer execution produces one joint proper-box rational admission. -/
def admitted {origin : Prefix.Source.Snapshot} (execution : Execution origin) :
    Admitted execution.numerical.trace := execution.context.recording.admission

end Execution

/-- Execute finite control using each actual cached source state once and retaining exact recalls. -/
@[expose] def run {origin : Prefix.Source.Snapshot} :
    Nat → List Frame → {state : Observer.State} → Context origin state → Execution origin :=
  Numerical.Cached.run Observer.step Observer.replyRegisters (Context origin)
    (fun context pathEq pastEq => context.transport pathEq pastEq)
    (Prefix.Source.answer origin) answer

/-- Cached source execution agrees with the complete numerical interpreter at every finite fuel. -/
theorem run_correct {origin : Prefix.Source.Snapshot}
    (fuel : Nat) (control : List Frame) {state : Observer.State} (context : Context origin state) :
    (run fuel control context).outcome = (Observer.run fuel control state (Prefix.Source.answer origin)).value ∧
      (run fuel control context).context.recording.trace = context.recording.trace ++
        (Observer.run fuel control state (Prefix.Source.answer origin)).trace := by
  have correct := Numerical.Cached.run_correct Observer.step Observer.replyRegisters (Context origin)
    (fun context pathEq pastEq => context.transport pathEq pastEq)
    (Prefix.Source.answer origin) answer fuel control context
  exact ⟨correct.1, (run fuel control context).context.pastEq.trans
    (correct.2.trans (congrArg (fun past => past ++
      (Observer.run fuel control state (Prefix.Source.answer origin)).trace) context.pastEq.symm))⟩

/-- Run fixed finite mixed control, numerical registers and fuel against the retained original cursor. -/
def execute (origin : Prefix.Source.Snapshot)
    (control : List Frame) (registers : List Value) (fuel : Nat) : Execution origin :=
  run fuel control (Context.initial origin registers)

/-- Actual canonical execution retains exactly its original numerical transition budget. -/
theorem execute_budget (origin : Prefix.Source.Snapshot)
    (control : List Frame) (registers : List Value) (fuel : Nat) :
    (execute origin control registers fuel).budget = fuel :=
  Numerical.Cached.run_budget Observer.step Observer.replyRegisters (Context origin)
    (fun context pathEq pastEq => context.transport pathEq pastEq)
    (Prefix.Source.answer origin) answer fuel control (Context.initial origin registers)

/-- Consumed and unused numerical transitions account for the exact supplied canonical execution budget.

Geometric handler calls, bit constructions and candidate polynomial evaluations
have their separate retained readbacks; none is identified with transition fuel.
-/
theorem execute_accounted (origin : Prefix.Source.Snapshot)
    (control : List Frame) (registers : List Value) (fuel : Nat) :
    (execute origin control registers fuel).simulation.usedFuel +
      (execute origin control registers fuel).simulation.remainingFuel = fuel :=
  Numerical.Cached.run_accounted Observer.step Observer.replyRegisters (Context origin)
    (fun context pathEq pastEq => context.transport pathEq pastEq)
    (Prefix.Source.answer origin) answer fuel control (Context.initial origin registers)

/-- Actual cached execution equals the whole numerical execution of the same finite mixed machine. -/
theorem execute_correct (origin : Prefix.Source.Snapshot)
    (control : List Frame) (registers : List Value) (fuel : Nat) :
    (execute origin control registers fuel).numerical =
      Observer.execute control registers fuel (Prefix.Source.answer origin) := by
  have correct := run_correct fuel control (Context.initial origin registers)
  apply Basic.Execution.ext
  · exact correct.1
  · exact correct.2.trans
      (congrArg (fun trace => trace ++
        (Observer.run fuel control (Observer.State.initial registers)
          (Prefix.Source.answer origin)).trace)
        (Prefix.Source.Recording.start_trace origin))

/-- Execute and admit an actual canonical observer without assuming a common rational reading. -/
def admission (origin : Prefix.Source.Snapshot) (control : List Frame)
    (registers : List Value) (fuel : Nat) :
    (execution : Execution origin) × Admitted execution.numerical.trace :=
  let execution := execute origin control registers fuel
  ⟨execution, execution.admitted⟩

set_option genInjectivity false in
/-- Retain one actual mixed observer execution and its valid whole-history finite rational continuation. -/
structure RationalExecution (origin : Prefix.Source.Snapshot)
    (control : List Frame) (registers : List Value) (fuel : Nat) where
  /-- The actual original cached mixed source execution. -/ execution : Execution origin
  /-- The execution uses exactly this fixed finite control, registers and fuel. -/ executionEq :
    execution = execute origin control registers fuel
  /-- The finite rational continuation belongs to that same complete numerical trace. -/ continuation :
    Prefix.Continuation.Result execution.numerical.trace

/-- Execute one canonical observer and construct its same finite rational history from the retained recording. -/
def continueExecution (origin : Prefix.Source.Snapshot)
    (control : List Frame) (registers : List Value) (fuel : Nat) :
    RationalExecution origin control registers fuel :=
  let execution := execute origin control registers fuel
  ⟨execution, rfl, Prefix.Continuation.ofAdmitted execution.admitted⟩

namespace RationalExecution

/-- The finite-code rational replacement preserves the entire actual mixed observer execution, including repetitions. -/
theorem same_execution {origin : Prefix.Source.Snapshot}
    {control : List Frame} {registers : List Value} {fuel : Nat}
    (result : RationalExecution origin control registers fuel) :
    Observer.execute control registers fuel (result.continuation.history.interpret result.continuation.valid) =
      result.execution.numerical := by
  let protocol := Observer.protocol control registers fuel
  let oracle := Prefix.Source.answer origin
  have original : protocol.run oracle = result.execution.numerical :=
    (Observer.protocol_run control registers fuel oracle).trans
      ((execute_correct origin control registers fuel).symm.trans
        (congrArg Execution.numerical result.executionEq.symm))
  exact (Observer.protocol_run control registers fuel
    (result.continuation.history.interpret result.continuation.valid)).symm.trans
      ((result.continuation.same_execution protocol oracle (congrArg Basic.Execution.trace original)).trans original)

/-- A witnessed completed observer preserves its exact rational execution at every larger finite bound.

The witness excludes only this attempt's exhaustion. It can retain a returned
value or numerical failure; no globally fixed fuel cap or termination oracle
is assumed. The continuation was already constructed from its actual source
recording, and every ordered numerical exchange remains identical.
-/
theorem same_execution_after_completion {origin : Prefix.Source.Snapshot}
    {control : List Frame} {registers : List Value} {fuel later : Nat}
    (result : RationalExecution origin control registers fuel)
    (completed : result.execution.outcome ≠ .exhausted) (order : fuel ≤ later) :
    Observer.execute control registers later (result.continuation.history.interpret result.continuation.valid) =
      result.execution.numerical := by
  have observed :
      (Observer.execute control registers fuel
        (result.continuation.history.interpret result.continuation.valid)).value =
        result.execution.outcome :=
    congrArg Basic.Execution.value result.same_execution
  have persists := Numerical.Simulation.completed_persists Observer.step Observer.replyRegisters
    (result.continuation.history.interpret result.continuation.valid) order control (Observer.State.initial registers)
    result.execution.outcome completed observed
  exact persists.trans result.same_execution

/-- The same witnessed complete source execution persists with its whole ordered trace at every larger finite bound. -/
theorem source_execution_after_completion {origin : Prefix.Source.Snapshot}
    {control : List Frame} {registers : List Value} {fuel later : Nat}
    (result : RationalExecution origin control registers fuel)
    (completed : result.execution.outcome ≠ .exhausted) (order : fuel ≤ later) :
    (execute origin control registers later).numerical = result.execution.numerical := by
  have original : Observer.execute control registers fuel (Prefix.Source.answer origin) =
      result.execution.numerical :=
    (execute_correct origin control registers fuel).symm.trans
      (congrArg Execution.numerical result.executionEq.symm)
  have observed :
      (Observer.execute control registers fuel (Prefix.Source.answer origin)).value =
        result.execution.outcome :=
    congrArg Basic.Execution.value original
  have persists := Numerical.Simulation.completed_persists Observer.step Observer.replyRegisters
    (Prefix.Source.answer origin) order control (Observer.State.initial registers)
    result.execution.outcome completed observed
  exact (execute_correct origin control registers later).trans (persists.trans original)

/-- Numerical acceptance of a completed run holds for its rational continuation at every later finite bound. -/
theorem accepts_after_completion {origin : Prefix.Source.Snapshot}
    {control : List Frame} {registers : List Value} {fuel later : Nat}
    (result : RationalExecution origin control registers fuel)
    (completed : result.execution.outcome ≠ .exhausted) (order : fuel ≤ later)
    (accept : Basic.Execution Cursor.Question Reply Outcome → Prop) (accepted : accept result.execution.numerical) :
    accept (Observer.execute control registers later
      (result.continuation.history.interpret result.continuation.valid)) :=
  (result.same_execution_after_completion completed order).symm ▸ accepted

/-- Numerical acceptance is preserved by the same whole-history rational execution. -/
theorem accepts {origin : Prefix.Source.Snapshot}
    {control : List Frame} {registers : List Value} {fuel : Nat}
    (result : RationalExecution origin control registers fuel)
    (accept : Basic.Execution Cursor.Question Reply Outcome → Prop) (accepted : accept result.execution.numerical) :
    accept (Observer.execute control registers fuel
      (result.continuation.history.interpret result.continuation.valid)) := result.same_execution.symm ▸ accepted

/-- A numerical acceptance rule excluding every valid finite rational history cannot accept an admitted mixed run. -/
theorem cannot_certify_no_rational_execution {origin : Prefix.Source.Snapshot}
    {control : List Frame} {registers : List Value} {fuel : Nat}
    (result : RationalExecution origin control registers fuel)
    (accept : Basic.Execution Cursor.Question Reply Outcome → Prop)
    (sound : ∀ (history : Prefix.Continuation.History) (valid : history.Valid),
      ¬ accept (Observer.execute control registers fuel (history.interpret valid))) :
    ¬ accept result.execution.numerical :=
  fun accepted => sound result.continuation.history result.continuation.valid (result.accepts accept accepted)

/-- No numerical acceptance excluding every valid rational code can certify a witnessed complete run at later fuel.

The larger finite bound is arbitrary. The actual constructed continuation
preserves the completed outcome and ordered trace there, so exclusion of every
valid finite rational continuation also excludes this actual numerical run.
-/
theorem cannot_certify_no_rational_execution_after_completion {origin : Prefix.Source.Snapshot}
    {control : List Frame} {registers : List Value} {fuel later : Nat}
    (result : RationalExecution origin control registers fuel)
    (completed : result.execution.outcome ≠ .exhausted) (order : fuel ≤ later)
    (accept : Basic.Execution Cursor.Question Reply Outcome → Prop)
    (sound : ∀ (history : Prefix.Continuation.History) (valid : history.Valid),
      ¬ accept (Observer.execute control registers later (history.interpret valid))) :
    ¬ accept result.execution.numerical :=
  fun accepted => sound result.continuation.history result.continuation.valid
    (result.accepts_after_completion completed order accept accepted)

end RationalExecution

end Purelib.Approximation.Gaussian.Observation.Prefix.Observer.Source

end
