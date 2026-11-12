module

public import Purelib.Computation.Machine.Numerical.Simulation
import Purelib.Data.List.Append

/-!
# Finite control over retained source contexts

A source-specific context keeps the actual original recording and cached work.
The shared traversal transports that context across pure control steps and
consumes its actual legal-query result once. Agreement concerns the complete
numerical outcome and ordered saved exchanges at every finite fuel.
-/

public section

namespace Purelib.Computation.Machine.Numerical.Cached

open Purelib
open Purelib.Approximation.Gaussian.Observation.Observer
open Purelib.Computation.Query

universe u v w x

variable {Instruction : Type u} {Request : Type v} {Reply : Type w}

set_option genInjectivity false in
/-- An actual retained reply and its correctly indexed next source context.

The context family retains its original source owner. The supplied original
oracle identifies the returned reply, while the next context belongs to the
same numerical state after consuming that exact cached reply. -/
structure Answer (Context : State Request Reply → Type x) (registers : Reply → List Value)
    (oracle : Path.Question Request → Reply) {state : State Request Reply}
    (context : Context state) (query : Query Request Reply) where
  /-- The actual cached reply returned by the original legal-query handler. -/ reply : Reply
  /-- The retained next context consumes this exact reply in the original numerical state. -/ next :
    Context (query.receive registers state reply)
  /-- The cached reply agrees with the original pure answer at this exact path question. -/ replyEq :
    reply = oracle (query.question state)

set_option genInjectivity false in
/-- A retained finite source execution with every actual configuration and its original context.

The same numerical simulation payload retains counters, callers, original
registers, ordered exchanges and exact consumed/unused fuel. The source context
belongs to that exact retained final state, without another source traversal.
-/
structure Execution (Instruction : Type u) (Context : State Request Reply → Type x) where
  /-- Every actual chronological numerical configuration and exact transition accounting. -/ simulation :
    Simulation.Execution Instruction Request Reply
  /-- The actual retained source context for that same final numerical state. -/ context :
    Context simulation.current.state
  /-- The exact original finite numerical transition budget. -/ budget : Nat
  /-- The actual stopped transition or certified exhausted unresolved configuration. -/ stopping :
    Simulation.Stopping simulation budget

namespace Execution

/-- Read the original final numerical state from its retained complete simulation. -/
@[expose] def state {Instruction : Type u} {Context : State Request Reply → Type x}
    (execution : Execution Instruction Context) : State Request Reply := execution.simulation.current.state

/-- Read the actual finite outcome or budget exhaustion from the retained final configuration. -/
@[expose] def outcome {Instruction : Type u} {Context : State Request Reply → Type x}
    (execution : Execution Instruction Context) : Outcome := execution.simulation.current.outcome

/-- Prepend one original numerical predecessor while retaining the same completed source work. -/
@[expose] def prepend {Instruction : Type u} {Context : State Request Reply → Type x}
    (configuration : Configuration Instruction Request Reply) (execution : Execution Instruction Context) :
    Execution Instruction Context :=
  { simulation := execution.simulation.prepend configuration
    context := execution.context
    budget := execution.budget + 1
    stopping := match execution.stopping with
      | .stopped outcome observed => .stopped outcome observed
      | .exhausted pending spent unused =>
          .exhausted pending (congrArg (fun count => count + 1) spent) unused }

end Execution

variable (step : List (Frame Instruction) → (state : State Request Reply) → Action Instruction state)
    (registers : Reply → List Value) (Context : State Request Reply → Type x)
    (transport : {state next : State Request Reply} → Context state →
      next.path = state.path → next.past = state.past → Context next)
    (oracle : Path.Question Request → Reply)
    (answer : {state : State Request Reply} → (context : Context state) → (query : Query Request Reply) →
      query.Legal state → Answer Context registers oracle context query)

/-- Execute finite control using each actual legal-query result and retained source context once.

Pure steps transport the original context. Each query uses the actual source
handler's reply and next context without evaluating the oracle or replaying the
preceding path. The same fuel counts every numerical control transition. -/
@[expose] def run : Nat → List (Frame Instruction) → {state : State Request Reply} → Context state →
    Execution Instruction Context
  | 0, control, state, context =>
      ⟨Simulation.Execution.initial (Configuration.initial control state) 0, context, 0, .exhausted rfl rfl rfl⟩
  | fuel + 1, control, state, context =>
      let configuration := Configuration.initial control state
      match step control state with
      | .stop outcome =>
          ⟨(Simulation.Execution.initial (configuration.stop outcome) fuel).prepend configuration,
            context, fuel + 1, .stopped outcome rfl⟩
      | .next next _nextState pathEq pastEq =>
          (run fuel next (transport context pathEq pastEq)).prepend configuration
      | .ask query next legal =>
          let result := answer context query legal
          (run fuel next result.next).prepend configuration

/-- Cached source traversal retains the complete same-machine configuration sequence and fuel accounting.

The equality includes every chronological configuration, original counter and
caller, final state, actual stop and consumed/unused transitions. Each source
reply is consumed from its existing answer receipt once; the oracle appears
only in the correctness comparison.
-/
theorem run_simulation (fuel : Nat) (control : List (Frame Instruction)) {state : State Request Reply}
    (context : Context state) :
    (run step registers Context transport oracle answer fuel control context).simulation =
      Simulation.scan step registers oracle fuel (Configuration.initial control state) := by
  induction fuel generalizing control state with
  | zero => rfl
  | succ fuel induction =>
      rewrite [run, Simulation.scan]
      change (match step control state with
        | .stop outcome =>
            (⟨(Simulation.Execution.initial ((Configuration.initial control state).stop outcome) fuel).prepend
                (Configuration.initial control state), context, fuel + 1, .stopped outcome rfl⟩ :
                  Execution Instruction Context)
        | .next next nextState pathEq pastEq =>
            (run step registers Context transport oracle answer fuel next
              (transport context pathEq pastEq)).prepend (Configuration.initial control state)
        | .ask query next legal =>
            let result := answer context query legal
            (run step registers Context transport oracle answer fuel next result.next).prepend
              (Configuration.initial control state)).simulation =
        (Simulation.scan step registers oracle fuel
          (Simulation.advance step registers oracle (Configuration.initial control state))).prepend
            (Configuration.initial control state)
      cases action : step control state with
      | stop outcome =>
          change (Simulation.Execution.initial ((Configuration.initial control state).stop outcome) fuel).prepend
              (Configuration.initial control state) =
            (Simulation.scan step registers oracle fuel
              (Simulation.advance step registers oracle (Configuration.initial control state))).prepend
                (Configuration.initial control state)
          unfold Simulation.advance
          dsimp only [Configuration.initial]
          rewrite [action]
          exact congrArg (fun result => result.prepend (Configuration.initial control state))
            (Simulation.scan_stopped step registers oracle
              ((Configuration.initial control state).stop outcome) outcome rfl fuel).symm
      | next next nextState pathEq pastEq =>
          unfold Simulation.advance
          dsimp only [Configuration.initial]
          rewrite [action]
          exact congrArg (fun result => result.prepend (Configuration.initial control state))
            (induction next (transport context pathEq pastEq))
      | ask query next legal =>
          unfold Simulation.advance
          dsimp only [Configuration.initial]
          rewrite [action]
          let result := answer context query legal
          have tail := induction next result.next
          have actual : Simulation.scan step registers oracle fuel
              (Configuration.initial next (query.receive registers state result.reply)) =
            Simulation.scan step registers oracle fuel
              (Configuration.initial next (query.receive registers state (oracle (query.question state)))) :=
            congrArg (fun reply => Simulation.scan step registers oracle fuel
              (Configuration.initial next (query.receive registers state reply))) result.replyEq
          exact congrArg (fun result => result.prepend (Configuration.initial control state)) (tail.trans actual)

/-- The retained source execution carries the exact originally supplied transition budget. -/
theorem run_budget (fuel : Nat) (control : List (Frame Instruction)) {state : State Request Reply}
    (context : Context state) :
    (run step registers Context transport oracle answer fuel control context).budget = fuel := by
  induction fuel generalizing control state with
  | zero => rfl
  | succ fuel induction =>
      rewrite [run]
      cases action : step control state with
      | stop outcome => rfl
      | next next nextState pathEq pastEq =>
          exact congrArg (fun budget => budget + 1) (induction next (transport context pathEq pastEq))
      | ask query next legal =>
          exact congrArg (fun budget => budget + 1) (induction next (answer context query legal).next)

/-- Source traversal's cached consumed and unused transitions exactly account for its actual original budget. -/
theorem run_accounted (fuel : Nat) (control : List (Frame Instruction)) {state : State Request Reply}
    (context : Context state) :
    (run step registers Context transport oracle answer fuel control context).simulation.usedFuel +
      (run step registers Context transport oracle answer fuel control context).simulation.remainingFuel = fuel := by
  have actual := run_simulation step registers Context transport oracle answer fuel control context
  exact (congrArg (fun execution => execution.usedFuel + execution.remainingFuel) actual).trans
    (Simulation.scan_accounted step registers oracle fuel (Configuration.initial control state))

/-- Cached traversal preserves the complete numerical outcome and ordered saved exchanges.

The claim holds for every finite fuel, original state and retained context.
Only the executed branch contributes exchanges; legal recalls preserve their
actual original questions and cached replies as repeated occurrences. -/
theorem run_correct (fuel : Nat) (control : List (Frame Instruction)) {state : State Request Reply}
    (context : Context state) :
    (run step registers Context transport oracle answer fuel control context).outcome =
        (Numerical.run step registers fuel control state oracle).value ∧
      (run step registers Context transport oracle answer fuel control context).state.past = state.past ++
        (Numerical.run step registers fuel control state oracle).trace := by
  induction fuel generalizing control state with
  | zero => exact ⟨rfl, (Data.List.Append.append_nil _).symm⟩
  | succ fuel induction =>
      rewrite [run, Numerical.run]
      cases action : step control state with
      | stop outcome => exact ⟨rfl, (Data.List.Append.append_nil _).symm⟩
      | next next nextState pathEq pastEq =>
          have tail := induction next (transport context pathEq pastEq)
          exact ⟨tail.1, tail.2.trans
            (congrArg (fun past => past ++ (Numerical.run step registers fuel next nextState oracle).trace) pastEq)⟩
      | ask query next legal =>
          let result := answer context query legal
          let question := query.question state
          change (run step registers Context transport oracle answer fuel next result.next).outcome =
              (Numerical.run step registers fuel next (query.receive registers state (oracle question)) oracle).value ∧
            (run step registers Context transport oracle answer fuel next result.next).state.past = state.past ++
              (⟨question, oracle question⟩ ::
                (Numerical.run step registers fuel next (query.receive registers state (oracle question)) oracle).trace)
          have tail := induction next result.next
          have tailEq : Numerical.run step registers fuel next (query.receive registers state result.reply) oracle =
              Numerical.run step registers fuel next (query.receive registers state (oracle question)) oracle :=
            congrArg (fun reply => Numerical.run step registers fuel next (query.receive registers state reply) oracle)
              result.replyEq
          refine ⟨tail.1.trans (congrArg Basic.Execution.value tailEq), ?_⟩
          have entryEq : (⟨question, result.reply⟩ : Basic.Exchange (Path.Question Request) Reply) =
              ⟨question, oracle question⟩ := congrArg (Basic.Exchange.mk question) result.replyEq
          calc
            (run step registers Context transport oracle answer fuel next result.next).state.past =
                (state.past ++ [⟨question, result.reply⟩]) ++
                  (Numerical.run step registers fuel next (query.receive registers state result.reply) oracle).trace :=
              tail.2
            _ = (state.past ++ [⟨question, result.reply⟩]) ++
                  (Numerical.run step registers fuel next
                    (query.receive registers state (oracle question)) oracle).trace :=
              congrArg (List.append (state.past ++ [⟨question, result.reply⟩])) (congrArg Basic.Execution.trace tailEq)
            _ = state.past ++ (⟨question, oracle question⟩ ::
                  (Numerical.run step registers fuel next
                    (query.receive registers state (oracle question)) oracle).trace) := by
              rewrite [Data.List.Append.append_assoc]
              exact congrArg (List.append state.past)
                (congrArg (fun entry => entry ::
                  (Numerical.run step registers fuel next
                    (query.receive registers state (oracle question)) oracle).trace) entryEq)

end Purelib.Computation.Machine.Numerical.Cached

end
