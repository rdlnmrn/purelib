module

public import Purelib.Approximation.Gaussian.Observation.Observer
public import Purelib.Computation.Machine.Numerical.Cached
import Purelib.Computation.Machine.Numerical.Simulation
import Purelib.Computation.Query.Path
import Purelib.Data.List.GetD
import Purelib.Data.List.Membership
import Purelib.Data.List.Append

/-!
# Cached source execution for first-order numerical observers

An execution context retains the original enclosure recording and identifies
its request path and ordered exchanges with the numerical observer state.
Source requests consume the actual cached current state once. Recall reads
the original retained occurrence at its coordinate, preserving its cached
reply and both original state owners.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Observer.Source

open Purelib
open Purelib.Computation.Machine
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Computation.Query

set_option genInjectivity false in
/-- Retain an original source recording corresponding to this exact numerical observer state. -/
structure Context (process : Gaussian.Process) (initial : process.State) (state : Observer.State) where
  /-- The actual original source states, refinement history and cached replies. -/ recording :
    Observation.Source.Recording process initial
  /-- The source's actual current request path is this observer's numerical path. -/ pathEq :
    recording.current.path = state.path
  /-- The source's exact ordered trace is this observer's saved numerical trace. -/ pastEq :
    recording.trace = state.past

namespace Context

/-- Start an original source and numerical observer with the same empty request history. -/
def initial (process : Gaussian.Process) (initial : process.State) (registers : List Value) :
    Context process initial (Observer.State.initial registers) :=
  ⟨Observation.Source.Recording.initial process initial, rfl, rfl⟩

/-- Transport the same cached source context through a certified pure numerical state transition. -/
@[expose] def transport {process : Gaussian.Process} {initial : process.State} {state next : Observer.State}
    (context : Context process initial state) (pathEq : next.path = state.path)
    (pastEq : next.past = state.past) : Context process initial next :=
  ⟨context.recording, context.pathEq.trans pathEq.symm, context.pastEq.trans pastEq.symm⟩

end Context

/-- One actual cached reply and the next context retain this same original context and displayed query. -/
abbrev QueryResult {process : Gaussian.Process} {initial : process.State} {state : Observer.State}
    (context : Context process initial state) (query : Observer.Query) :=
  Numerical.Cached.Answer (Context process initial) Observer.replyRegisters
    (Observation.Source.answer process initial) context query

namespace QueryResult

/-- The new recording appends this same cached reply at the actual question. -/
theorem traceEq {process : Gaussian.Process} {initial : process.State} {state : Observer.State}
    {context : Context process initial state} {query : Observer.Query}
    (result : QueryResult context query) :
    result.next.recording.trace = context.recording.trace ++ [⟨query.question state, result.reply⟩] := by
  have after : result.next.recording.trace =
      state.past ++ [(⟨query.question state, result.reply⟩ : Basic.Exchange Question Enclosure.Ball)] :=
    result.next.pastEq
  exact after.trans
    (congrArg (fun (trace : Basic.Trace Question Enclosure.Ball) =>
      trace ++ [(⟨query.question state, result.reply⟩ : Basic.Exchange Question Enclosure.Ball)]) context.pastEq.symm)

end QueryResult

/-- Answer a legal observer query from the same original cached source recording.

Refinement uses the actual request receipt and its cached reply. Recall
selects the original occurrence by the certified finite coordinate and
never invokes the source refinement or ball-reading procedure again.
-/
def answer {process : Gaussian.Process} {initial : process.State} {state : Observer.State}
    (context : Context process initial state) (query : Observer.Query) (legal : query.Legal state) :
    QueryResult context query := by
  cases query with
  | request target =>
      let result := context.recording.prepareRequest target
      let reply := result.occurrence.reply
      have questionEq : result.occurrence.question =
          (Numerical.Query.request target).question state :=
        result.questionEq.trans (congrArg (fun path => (Path.Question.mk path target)) context.pathEq)
      have exchangeEq : result.occurrence.exchange =
          (⟨(Numerical.Query.request target).question state, reply⟩ : Basic.Exchange Question Enclosure.Ball) :=
        congrArg (fun question => (⟨question, reply⟩ : Basic.Exchange Question Enclosure.Ball)) questionEq
      exact
        { reply := reply
          next :=
            { recording := result.next
              pathEq := result.pathEq.trans (congrArg (fun path => path ++ [target]) context.pathEq)
              pastEq := result.traceEq.trans
                (congrArg₂ List.append context.pastEq (congrArg (fun entry => [entry]) exchangeEq)) }
          replyEq := result.occurrence.answerEq.symm.trans
            (congrArg (Observation.Source.answer process initial) questionEq) }
  | recall index entry =>
      have projected :
          (Data.List.getElem? context.recording.occurrences index).map Observation.Source.Occurrence.exchange =
            some entry := by
        rewrite [← Data.List.getElem?_map, ← context.recording.traceEq, context.pastEq]
        exact legal
      cases found : Data.List.getElem? context.recording.occurrences index with
      | none =>
          rewrite [found] at projected
          nomatch projected
      | some occurrence =>
          have exchangeEq : occurrence.exchange = entry := by
            rewrite [found] at projected
            exact congrArg (fun selected : Option (Basic.Exchange Question Enclosure.Ball) =>
              selected.getD entry) projected
          have member := Data.List.mem_of_getElem? context.recording.occurrences index occurrence found
          let recording := context.recording.recall occurrence member
          let reply := occurrence.reply
          have questionEq : occurrence.question = entry.query := congrArg Basic.Exchange.query exchangeEq
          have appended : occurrence.exchange =
              (⟨entry.query, reply⟩ : Basic.Exchange Question Enclosure.Ball) :=
            congrArg (fun question => (⟨question, reply⟩ : Basic.Exchange Question Enclosure.Ball)) questionEq
          exact
            { reply := reply
              next :=
                { recording := recording
                  pathEq := (congrArg Observation.Source.Snapshot.path
                    (context.recording.recall_current occurrence member)).trans context.pathEq
                  pastEq := (context.recording.recall_trace occurrence member).trans
                    (congrArg₂ List.append context.pastEq (congrArg (fun exchange => [exchange]) appended)) }
              replyEq := occurrence.answerEq.symm.trans
                (congrArg (Observation.Source.answer process initial) questionEq) }

/-- An actual finite source execution with its final numerical state, retained recording and outcome. -/
abbrev Execution (process : Gaussian.Process) (initial : process.State) :=
  Numerical.Cached.Execution Instruction (Context process initial)

namespace Execution

/-- Read the cached number of fresh original source refinements, excluding numerical recalls. -/
@[expose] def requestCount {process : Gaussian.Process} {initial : process.State}
    (execution : Execution process initial) : Nat := execution.context.recording.current.requestCount

/-- Read the displayed original source-interface calls separately from numerical transitions.

The original setup reads one ball and one witness. Fresh requests refine once
and retain their next ball and witness; recalls and admission reuse those caches.
Work hidden inside the supplied process implementation is outside this count.
-/
@[expose] def sourceCalls {process : Gaussian.Process} {initial : process.State}
    (execution : Execution process initial) : Nat := execution.context.recording.sourceCalls

/-- The counted source refinements are exactly the actual numerical state's new-request path. -/
theorem requestCount_eq_state_path {process : Gaussian.Process} {initial : process.State}
    (execution : Execution process initial) : execution.requestCount = execution.state.path.length :=
  execution.context.recording.current.requestCountEq.trans (congrArg List.length execution.context.pathEq)

/-- Each fresh request pays three displayed calls in addition to the two original setup calls. -/
theorem sourceCalls_eq_requests {process : Gaussian.Process} {initial : process.State}
    (execution : Execution process initial) : execution.sourceCalls = 2 + 3 * execution.requestCount :=
  execution.context.recording.current.sourceCalls_eq_requests

/-- Project the cached source execution into its exact numerical outcome and complete ordered trace. -/
@[expose] def numerical {process : Gaussian.Process} {initial : process.State}
    (execution : Execution process initial) : Basic.Execution Question Enclosure.Ball Outcome :=
  ⟨execution.outcome, execution.context.recording.trace⟩

/-- Construct admission for the actual entire source-generated execution trace. -/
def admitted {process : Gaussian.Process} {initial : process.State}
    (execution : Execution process initial) : Admitted execution.numerical.trace :=
  execution.context.recording.admission

end Execution

/-- Execute finite control using each actual cached source state once and retaining exact recalls. -/
@[expose] def run {process : Gaussian.Process} {initial : process.State} :
    (fuel : Nat) → List Frame → {state : Observer.State} → Context process initial state → Execution process initial :=
  Numerical.Cached.run Observer.step Observer.replyRegisters (Context process initial)
    (fun context pathEq pastEq => context.transport pathEq pastEq)
    (Observation.Source.answer process initial) answer

/-- Cached source execution agrees with the complete numerical interpreter at every finite fuel. -/
theorem run_correct {process : Gaussian.Process} {initial : process.State}
    (fuel : Nat) (control : List Frame) {state : Observer.State} (context : Context process initial state) :
    (run fuel control context).outcome =
        (Observer.run fuel control state (Observation.Source.answer process initial)).value ∧
      (run fuel control context).context.recording.trace = context.recording.trace ++
        (Observer.run fuel control state (Observation.Source.answer process initial)).trace := by
  have correct := Numerical.Cached.run_correct Observer.step Observer.replyRegisters (Context process initial)
    (fun context pathEq pastEq => context.transport pathEq pastEq)
    (Observation.Source.answer process initial) answer
    fuel control context
  exact ⟨correct.1, (run fuel control context).context.pastEq.trans
    (correct.2.trans (congrArg (fun past => past ++
      (Observer.run fuel control state (Observation.Source.answer process initial)).trace) context.pastEq.symm))⟩

/-- Run a finite observer from fixed numerical registers and one original source initial state. -/
def execute (process : Gaussian.Process) (initial : process.State)
    (control : List Frame) (registers : List Value) (fuel : Nat) : Execution process initial :=
  run fuel control (Context.initial process initial registers)

/-- Actual enclosure execution retains its exact originally supplied numerical transition budget. -/
theorem execute_budget (process : Gaussian.Process) (initial : process.State)
    (control : List Frame) (registers : List Value) (fuel : Nat) :
    (execute process initial control registers fuel).budget = fuel :=
  Numerical.Cached.run_budget Observer.step Observer.replyRegisters (Context process initial)
    (fun context pathEq pastEq => context.transport pathEq pastEq)
    (Observation.Source.answer process initial) answer fuel control (Context.initial process initial registers)

/-- Consumed and unused numerical transitions account for the exact supplied enclosure execution budget.

The retained source-interface calls have their own readback and certified
count; they are not identified with numerical transition fuel.
-/
theorem execute_accounted (process : Gaussian.Process) (initial : process.State)
    (control : List Frame) (registers : List Value) (fuel : Nat) :
    (execute process initial control registers fuel).simulation.usedFuel +
      (execute process initial control registers fuel).simulation.remainingFuel = fuel :=
  Numerical.Cached.run_accounted Observer.step Observer.replyRegisters (Context process initial)
    (fun context pathEq pastEq => context.transport pathEq pastEq)
    (Observation.Source.answer process initial) answer fuel control (Context.initial process initial registers)

/-- Every actual source execution equals the full numerical execution of the same coded numerical observer. -/
theorem execute_correct (process : Gaussian.Process) (initial : process.State)
    (control : List Frame) (registers : List Value) (fuel : Nat) :
    (execute process initial control registers fuel).numerical =
      Observer.execute control registers fuel (Observation.Source.answer process initial) := by
  have correct := run_correct fuel control (Context.initial process initial registers)
  apply Basic.Execution.ext
  · exact correct.1
  · exact correct.2

/-- Every finite coded numerical source execution produces an admitted exact ordered numerical trace. -/
def admission (process : Gaussian.Process) (initial : process.State)
    (control : List Frame) (registers : List Value) (fuel : Nat) :
    (execution : Execution process initial) × Admitted execution.numerical.trace :=
  let execution := execute process initial control registers fuel
  ⟨execution, execution.admitted⟩

set_option genInjectivity false in
/-- Retain an actual coded numerical source execution and its valid finite-code rational continuation. -/
structure RationalExecution (process : Gaussian.Process) (initial : process.State)
    (control : List Frame) (registers : List Value) (fuel : Nat) where
  /-- The original actual cached source execution. -/ execution : Execution process initial
  /-- The execution uses these same fixed control, numerical registers and fuel. -/ executionEq :
    execution = execute process initial control registers fuel
  /-- The new finite-code continuation for this exact ordered numerical trace. -/ continuation :
    Continuation.Result execution.numerical.trace

/-- Run the actual source once and construct its valid rational replacement from that same retained execution. -/
def continueExecution (process : Gaussian.Process) (initial : process.State)
    (control : List Frame) (registers : List Value) (fuel : Nat) :
    RationalExecution process initial control registers fuel :=
  let execution := execute process initial control registers fuel
  ⟨execution, rfl, Continuation.ofAdmitted execution.admitted⟩

namespace RationalExecution

/-- The finite-code rational replacement reproduces this actual entire coded numerical observer execution.

The source and continuation remain separate retained owners. Fixed control
and initial registers are finite numerical data, and the admission producer
is the actual executed refinement spine rather than an assumed realizer.
-/
theorem same_execution {process : Gaussian.Process} {initial : process.State}
    {control : List Frame} {registers : List Value} {fuel : Nat}
    (result : RationalExecution process initial control registers fuel) :
    Observer.execute control registers fuel result.continuation.code.interpret = result.execution.numerical := by
  let protocol := Observer.protocol control registers fuel
  let oracle := Observation.Source.answer process initial
  have original : protocol.run oracle = result.execution.numerical :=
    (Observer.protocol_run control registers fuel oracle).trans
      ((execute_correct process initial control registers fuel).symm.trans
        (congrArg Execution.numerical result.executionEq.symm))
  have answers : Basic.Answers result.continuation.code.interpret (protocol.run oracle).trace := by
    intro entry member
    have recorded : entry ∈ result.execution.numerical.trace :=
      congrArg Basic.Execution.trace original ▸ member
    exact result.continuation.answers entry recorded
  exact (Observer.protocol_run control registers fuel result.continuation.code.interpret).symm.trans
    ((protocol.run_of_answers oracle result.continuation.code.interpret answers).trans original)

/-- The rational continuation preserves the actual returned numerical outcome, including failure or exhaustion. -/
theorem same_outcome {process : Gaussian.Process} {initial : process.State}
    {control : List Frame} {registers : List Value} {fuel : Nat}
    (result : RationalExecution process initial control registers fuel) :
    (Observer.execute control registers fuel result.continuation.code.interpret).value =
      result.execution.numerical.value :=
  congrArg Basic.Execution.value result.same_execution

/-- The rational continuation preserves the complete ordered numerical trace and every repeated occurrence. -/
theorem same_trace {process : Gaussian.Process} {initial : process.State}
    {control : List Frame} {registers : List Value} {fuel : Nat}
    (result : RationalExecution process initial control registers fuel) :
    (Observer.execute control registers fuel result.continuation.code.interpret).trace =
      result.execution.numerical.trace :=
  congrArg Basic.Execution.trace result.same_execution

/-- A witnessed completed observer preserves its exact rational execution at every larger finite bound.

The witness excludes only this attempt's exhaustion. It can retain a returned
value or numerical failure; no globally fixed fuel cap or termination oracle
is assumed. The continuation was already constructed from its actual source
recording, and every ordered numerical exchange remains identical.
-/
theorem same_execution_after_completion {process : Gaussian.Process} {initial : process.State}
    {control : List Frame} {registers : List Value} {fuel later : Nat}
    (result : RationalExecution process initial control registers fuel)
    (completed : result.execution.outcome ≠ .exhausted) (order : fuel ≤ later) :
    Observer.execute control registers later result.continuation.code.interpret =
      result.execution.numerical := by
  have observed :
      (Observer.execute control registers fuel result.continuation.code.interpret).value =
        result.execution.outcome :=
    congrArg Basic.Execution.value result.same_execution
  have persists := Numerical.Simulation.completed_persists Observer.step Observer.replyRegisters
    result.continuation.code.interpret order control (Observer.State.initial registers)
    result.execution.outcome completed observed
  exact persists.trans result.same_execution

/-- The same witnessed complete source execution persists with its whole ordered trace at every larger finite bound. -/
theorem source_execution_after_completion {process : Gaussian.Process} {initial : process.State}
    {control : List Frame} {registers : List Value} {fuel later : Nat}
    (result : RationalExecution process initial control registers fuel)
    (completed : result.execution.outcome ≠ .exhausted) (order : fuel ≤ later) :
    (execute process initial control registers later).numerical = result.execution.numerical := by
  have original : Observer.execute control registers fuel (Observation.Source.answer process initial) =
      result.execution.numerical :=
    (execute_correct process initial control registers fuel).symm.trans
      (congrArg Execution.numerical result.executionEq.symm)
  have observed :
      (Observer.execute control registers fuel (Observation.Source.answer process initial)).value =
        result.execution.outcome :=
    congrArg Basic.Execution.value original
  have persists := Numerical.Simulation.completed_persists Observer.step Observer.replyRegisters
    (Observation.Source.answer process initial) order control (Observer.State.initial registers)
    result.execution.outcome completed observed
  exact (execute_correct process initial control registers later).trans (persists.trans original)

/-- Numerical acceptance of a completed run holds for its rational continuation at every later finite bound. -/
theorem accepts_after_completion {process : Gaussian.Process} {initial : process.State}
    {control : List Frame} {registers : List Value} {fuel later : Nat}
    (result : RationalExecution process initial control registers fuel)
    (completed : result.execution.outcome ≠ .exhausted) (order : fuel ≤ later)
    (accept : Basic.Execution Question Enclosure.Ball Outcome → Prop) (accepted : accept result.execution.numerical) :
    accept (Observer.execute control registers later result.continuation.code.interpret) :=
  (result.same_execution_after_completion completed order).symm ▸ accepted

/-- Acceptance depending only on the numerical outcome and trace also accepts the finite rational continuation. -/
theorem accepts {process : Gaussian.Process} {initial : process.State}
    {control : List Frame} {registers : List Value} {fuel : Nat}
    (result : RationalExecution process initial control registers fuel)
    (acceptance : Basic.Execution Question Enclosure.Ball Outcome → Prop)
    (accepted : acceptance result.execution.numerical) :
    acceptance (Observer.execute control registers fuel result.continuation.code.interpret) :=
  result.same_execution.symm ▸ accepted

/-- A numerical acceptance rule excluding every valid finite rational code cannot accept this admitted run.

The continuation is a finite description with the named total interpreter
and validity for all future positive requests. The conclusion concerns this
coded numerical observer's fixed control, parameters and finite execution; it
does not classify the original source or identify its source code.
-/
theorem cannot_certify_no_rational_execution {process : Gaussian.Process} {initial : process.State}
    {control : List Frame} {registers : List Value} {fuel : Nat}
    (result : RationalExecution process initial control registers fuel)
    (acceptance : Basic.Execution Question Enclosure.Ball Outcome → Prop)
    (sound : acceptance result.execution.numerical →
      ∀ code : Continuation.Code, Continuation.Valid code →
        Observer.execute control registers fuel code.interpret ≠ result.execution.numerical) :
    ¬ acceptance result.execution.numerical := by
  intro accepted
  exact sound accepted result.continuation.code result.continuation.valid result.same_execution

/-- No numerical acceptance excluding every valid rational code can certify a witnessed complete run at later fuel.

The larger finite bound is arbitrary. The actual constructed continuation
preserves the completed outcome and ordered trace there, so exclusion of every
valid finite rational continuation also excludes this actual numerical run.
-/
theorem cannot_certify_no_rational_execution_after_completion {process : Gaussian.Process} {initial : process.State}
    {control : List Frame} {registers : List Value} {fuel later : Nat}
    (result : RationalExecution process initial control registers fuel)
    (completed : result.execution.outcome ≠ .exhausted) (order : fuel ≤ later)
    (accept : Basic.Execution Question Enclosure.Ball Outcome → Prop)
    (sound : ∀ (code : Continuation.Code) (_valid : Continuation.Valid code),
      ¬ accept (Observer.execute control registers later code.interpret)) :
    ¬ accept result.execution.numerical :=
  fun accepted => sound result.continuation.code result.continuation.valid
    (result.accepts_after_completion completed order accept accepted)

end RationalExecution

end Purelib.Approximation.Gaussian.Observation.Observer.Source

end
