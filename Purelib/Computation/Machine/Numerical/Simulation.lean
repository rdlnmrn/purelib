module

public import Purelib.Computation.Machine.Numerical
import Purelib.Data.List.Append

/-!
# Retained numerical-machine configurations and finite simulation

A configuration retains the same original control frames and numerical state.
Each deterministic transition is the original numerical step, with at most one
displayed query; stopped configurations are absorbing. Finite simulation can
be extended from its exact saved configuration without a global fuel cap.
-/

public section

namespace Purelib.Computation.Machine.Numerical

open Purelib.Approximation.Gaussian.Observation.Observer
open Purelib.Computation.Query
open Purelib.Data.List

universe u v w

set_option genInjectivity false in
/-- The original finite numerical control, state and any witnessed stopping outcome.

The state retains its actual ordered exchanges and numerical registers. A
terminal outcome records the actual stopped-step tag; `none` retains
unresolved control rather than asserting nontermination.
-/
structure Configuration (Instruction : Type u) (Request : Type v) (Reply : Type w) where
  /-- The exact original control frames, including counters and callers. -/ control : List (Frame Instruction)
  /-- The original numerical registers, request path and ordered exchanges. -/ state : State Request Reply
  /-- A witnessed stop, or unresolved finite control. -/ terminal : Option Outcome

namespace Configuration

variable {Instruction : Type u} {Request : Type v} {Reply : Type w}

/-- Retain original control and state as a running numerical configuration. -/
@[expose] def initial (control : List (Frame Instruction)) (state : State Request Reply) :
    Configuration Instruction Request Reply := ⟨control, state, none⟩

/-- Retain an actual stopped outcome with the same original control and state. -/
@[expose] def stop (configuration : Configuration Instruction Request Reply) (outcome : Outcome) :
    Configuration Instruction Request Reply := { configuration with terminal := some outcome }

/-- Read a witnessed stopping outcome, reporting finite exhaustion for unresolved control. -/
@[expose] def outcome (configuration : Configuration Instruction Request Reply) : Outcome :=
  configuration.terminal.getD .exhausted

end Configuration

namespace Simulation

variable {Instruction : Type u} {Request : Type v} {Reply : Type w}

variable (step : List (Frame Instruction) → (state : State Request Reply) → Action Instruction state)
    (registers : Reply → List Value) (oracle : Path.Question Request → Reply)

/-- Advance one original numerical transition, querying only its actual displayed request.

Stopped configurations remain unchanged. A running query consumes one actual
reply and updates the same original numerical state and continuation frames.
-/
@[expose] def advance (configuration : Configuration Instruction Request Reply) :
    Configuration Instruction Request Reply :=
  match configuration.terminal with
  | some _ => configuration
  | none =>
      match step configuration.control configuration.state with
      | .stop outcome => configuration.stop outcome
      | .next next nextState _pathEq _pastEq => Configuration.initial next nextState
      | .ask query next _legal =>
          let reply := oracle (query.question configuration.state)
          Configuration.initial next (query.receive registers configuration.state reply)

/-- Execute exactly the displayed finite number of deterministic numerical transitions. -/
@[expose] def run (initial : Configuration Instruction Request Reply) : Nat →
    Configuration Instruction Request Reply
  | 0 => initial
  | steps + 1 => advance step registers oracle (run initial steps)

/-- Further finite simulation starts from the exact original previously reached configuration. -/
theorem run_add (initial : Configuration Instruction Request Reply) (earlier later : Nat) :
    run step registers oracle initial (earlier + later) =
      run step registers oracle (run step registers oracle initial earlier) later := by
  induction later with
  | zero => rfl
  | succ later induction => exact congrArg (advance step registers oracle) induction

/-- A witnessed stopped configuration remains the exact same configuration at every later finite bound. -/
theorem run_stopped (configuration : Configuration Instruction Request Reply) (outcome : Outcome)
    (observed : configuration.terminal = some outcome) (steps : Nat) :
    run step registers oracle configuration steps = configuration := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
      change advance step registers oracle (run step registers oracle configuration steps) = configuration
      rewrite [induction]
      unfold advance
      rewrite [observed]
      rfl

/-- An actual stop at a witnessed finite stage persists with its complete state and ordered trace.

There is no fixed global cap. Every larger finite simulation retains that same
terminal configuration, including counters, callers and original exchanges.
-/
theorem stopped_persists (initial : Configuration Instruction Request Reply) {earlier later : Nat}
    (order : earlier ≤ later) (outcome : Outcome)
    (observed : (run step registers oracle initial earlier).terminal = some outcome) :
    run step registers oracle initial later = run step registers oracle initial earlier := by
  have remainder := Nat.add_sub_of_le order
  calc
    run step registers oracle initial later =
        run step registers oracle initial (earlier + (later - earlier)) :=
      congrArg (run step registers oracle initial) remainder.symm
    _ = run step registers oracle (run step registers oracle initial earlier) (later - earlier) :=
      run_add step registers oracle initial earlier _
    _ = run step registers oracle initial earlier :=
      run_stopped step registers oracle _ outcome observed _

set_option genInjectivity false in
/-- A finite attempt retains the exact final configuration, all configurations and consumed fuel.

The configuration sequence contains its original start and every actual
transition through the stop or budget boundary. Remaining fuel is retained
separately from consumed transitions; no completed prefix is recomputed.
-/
structure Execution (Instruction : Type u) (Request : Type v) (Reply : Type w) where
  /-- The actual last retained configuration. -/ current : Configuration Instruction Request Reply
  /-- The original chronological configurations, including the initial and final configurations. -/ configurations :
    List (Configuration Instruction Request Reply)
  /-- The exact number of consumed original numerical transitions. -/ usedFuel : Nat
  /-- The original unused finite budget after an actual stop. -/ remainingFuel : Nat

namespace Execution

variable {Instruction : Type u} {Request : Type v} {Reply : Type w}

/-- Retain one actual configuration with zero consumed transitions. -/
@[expose] def initial (configuration : Configuration Instruction Request Reply) (remaining : Nat) :
    Execution Instruction Request Reply := ⟨configuration, [configuration], 0, remaining⟩

/-- Prepend one actual predecessor while retaining all completed subsequent work. -/
@[expose] def prepend (configuration : Configuration Instruction Request Reply)
    (execution : Execution Instruction Request Reply) : Execution Instruction Request Reply :=
  { execution with configurations := configuration :: execution.configurations
                   usedFuel := execution.usedFuel + 1 }

end Execution

/-- Continue finite simulation from one actual saved configuration, caching each transition once. -/
@[expose] def scan : Nat → Configuration Instruction Request Reply → Execution Instruction Request Reply
  | 0, configuration => Execution.initial configuration 0
  | fuel + 1, configuration =>
      match configuration.terminal with
      | some _ => Execution.initial configuration (fuel + 1)
      | none =>
          let next := advance step registers oracle configuration
          (scan fuel next).prepend configuration

/-- An already witnessed stopped configuration retains zero additional transitions and the exact unused budget. -/
theorem scan_stopped (configuration : Configuration Instruction Request Reply) (outcome : Outcome)
    (observed : configuration.terminal = some outcome) (fuel : Nat) :
    scan step registers oracle fuel configuration = Execution.initial configuration fuel := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      unfold scan
      rewrite [observed]
      rfl

/-- Forward continuation has the same actual configurations as finite sequential simulation. -/
theorem run_succ_start (initial : Configuration Instruction Request Reply) (steps : Nat) :
    run step registers oracle initial (steps + 1) =
      run step registers oracle (advance step registers oracle initial) steps := by
  induction steps with
  | zero => rfl
  | succ steps induction => exact congrArg (advance step registers oracle) induction

/-- The retained final configuration is exactly the original simulation at the supplied finite budget. -/
theorem scan_current (fuel : Nat) (configuration : Configuration Instruction Request Reply) :
    (scan step registers oracle fuel configuration).current = run step registers oracle configuration fuel := by
  induction fuel generalizing configuration with
  | zero => rfl
  | succ fuel induction =>
      unfold scan
      cases observed : configuration.terminal with
      | some outcome => exact (run_stopped step registers oracle configuration outcome observed (fuel + 1)).symm
      | none =>
          exact (induction (advance step registers oracle configuration)).trans
            (run_succ_start step registers oracle configuration fuel).symm

/-- Consumed transitions and the retained unused budget account for the exact original finite budget. -/
theorem scan_accounted (fuel : Nat) (configuration : Configuration Instruction Request Reply) :
    (scan step registers oracle fuel configuration).usedFuel +
      (scan step registers oracle fuel configuration).remainingFuel = fuel := by
  induction fuel generalizing configuration with
  | zero => rfl
  | succ fuel induction =>
      unfold scan
      cases configuration.terminal with
      | some outcome => exact Nat.zero_add (fuel + 1)
      | none =>
          change ((scan step registers oracle fuel _).usedFuel + 1) +
            (scan step registers oracle fuel _).remainingFuel = fuel + 1
          calc
            ((scan step registers oracle fuel _).usedFuel + 1) +
                (scan step registers oracle fuel _).remainingFuel =
              ((scan step registers oracle fuel _).usedFuel +
                (scan step registers oracle fuel _).remainingFuel) + 1 :=
              Nat.add_right_comm _ 1 _
            _ = fuel + 1 := congrArg (fun count => count + 1) (induction _)

/-- A finite attempt consumes no more than its exact original transition budget. -/
theorem scan_within (fuel : Nat) (configuration : Configuration Instruction Request Reply) :
    (scan step registers oracle fuel configuration).usedFuel ≤ fuel := by
  have accounted := scan_accounted step registers oracle fuel configuration
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq accounted)

/-- A configuration sequence records only consecutive actual transitions of the same numerical machine. -/
inductive Chain : Configuration Instruction Request Reply →
    List (Configuration Instruction Request Reply) → Configuration Instruction Request Reply → Prop where
  /-- A zero-transition sequence retains its original configuration once. -/ | initial (configuration) :
      Chain configuration [configuration] configuration
  /-- Prepend the actual original predecessor to an already checked transition sequence. -/ | next
      (configuration next : Configuration Instruction Request Reply)
      (actual : next = advance step registers oracle configuration)
      {configurations : List (Configuration Instruction Request Reply)} {current}
      (tail : Chain next configurations current) : Chain configuration (configuration :: configurations) current

/-- Every retained configuration in an attempt belongs to its actual chronological transition sequence. -/
theorem scan_chain (fuel : Nat) (configuration : Configuration Instruction Request Reply) :
    Chain step registers oracle configuration (scan step registers oracle fuel configuration).configurations
      (scan step registers oracle fuel configuration).current := by
  induction fuel generalizing configuration with
  | zero => exact .initial configuration
  | succ fuel induction =>
      unfold scan
      cases configuration.terminal with
      | some outcome => exact .initial configuration
      | none => exact .next configuration _ rfl (induction _)

/-- The retained chronological sequence contains one more configuration than consumed transitions. -/
theorem scan_length (fuel : Nat) (configuration : Configuration Instruction Request Reply) :
    (scan step registers oracle fuel configuration).configurations.length =
      (scan step registers oracle fuel configuration).usedFuel + 1 := by
  induction fuel generalizing configuration with
  | zero => rfl
  | succ fuel induction =>
      unfold scan
      cases configuration.terminal with
      | some outcome => rfl
      | none => exact congrArg (fun count => count + 1) (induction _)

/-- An unresolved finite attempt used its whole exact budget and retained no unused transitions. -/
theorem scan_pending (fuel : Nat) (configuration : Configuration Instruction Request Reply)
    (pending : (scan step registers oracle fuel configuration).current.terminal = none) :
    (scan step registers oracle fuel configuration).usedFuel = fuel ∧
      (scan step registers oracle fuel configuration).remainingFuel = 0 := by
  induction fuel generalizing configuration with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel induction =>
      unfold scan at pending ⊢
      cases observed : configuration.terminal with
      | some outcome =>
          rewrite [observed] at pending
          change configuration.terminal = none at pending
          have impossible := observed.symm.trans pending
          nomatch impossible
      | none =>
          rewrite [observed] at pending
          have tail := induction (advance step registers oracle configuration) pending
          exact ⟨congrArg (fun count => count + 1) tail.1, tail.2⟩

/-- Retained configuration simulation preserves the original outcome and exact ordered exchange suffix.

The equality uses the same numerical step, reply projection and original fuel.
It includes numerical failures and finite exhaustion, not only acceptance.
-/
theorem scan_numerical (fuel : Nat) (control : List (Frame Instruction)) (state : State Request Reply) :
    (scan step registers oracle fuel (Configuration.initial control state)).current.outcome =
        (Numerical.run step registers fuel control state oracle).value ∧
      (scan step registers oracle fuel (Configuration.initial control state)).current.state.past =
        state.past ++ (Numerical.run step registers fuel control state oracle).trace := by
  induction fuel generalizing control state with
  | zero => exact ⟨rfl, (Append.append_nil _).symm⟩
  | succ fuel induction =>
      rewrite [scan, Numerical.run]
      dsimp only [Configuration.initial]
      unfold advance
      dsimp only [Configuration.initial]
      cases action : step control state with
      | stop outcome =>
          change (scan step registers oracle fuel
              ((Configuration.initial control state).stop outcome)).current.outcome = outcome ∧
            (scan step registers oracle fuel ((Configuration.initial control state).stop outcome)).current.state.past =
              state.past ++ []
          rewrite [scan_stopped step registers oracle
            ((Configuration.initial control state).stop outcome) outcome rfl fuel]
          exact ⟨rfl, (Append.append_nil _).symm⟩
      | next next nextState pathEq pastEq =>
          have tail := induction next nextState
          exact ⟨tail.1, tail.2.trans
            (congrArg (fun past => past ++ (Numerical.run step registers fuel next nextState oracle).trace) pastEq)⟩
      | ask query next legal =>
          have tail := induction next (query.receive registers state (oracle (query.question state)))
          refine ⟨tail.1, ?_⟩
          exact tail.2.trans (Append.append_assoc _ _ _)

/-- Original numerical execution is the scalar readback of the same retained bounded configuration run. -/
theorem run_numerical (fuel : Nat) (control : List (Frame Instruction)) (state : State Request Reply) :
    (run step registers oracle (Configuration.initial control state) fuel).outcome =
        (Numerical.run step registers fuel control state oracle).value ∧
      (run step registers oracle (Configuration.initial control state) fuel).state.past =
        state.past ++ (Numerical.run step registers fuel control state oracle).trace := by
  have current := scan_current step registers oracle fuel (Configuration.initial control state)
  have numerical := scan_numerical step registers oracle fuel control state
  exact ⟨(congrArg Configuration.outcome current).symm.trans numerical.1,
    (congrArg (fun configuration => configuration.state.past) current).symm.trans numerical.2⟩

/-- Every witnessed returned value or numerical failure preserves its complete execution at further finite fuel.

The additional fuel has no global cap. A pending exhausted attempt is excluded;
its current control can still issue later queries or reach a later return.
-/
theorem completed_add (earlier extra : Nat) (control : List (Frame Instruction)) (state : State Request Reply)
    (outcome : Outcome) (completed : outcome ≠ .exhausted)
    (observed : (Numerical.run step registers earlier control state oracle).value = outcome) :
    Numerical.run step registers (earlier + extra) control state oracle =
      Numerical.run step registers earlier control state oracle := by
  induction earlier generalizing control state with
  | zero => exact (completed observed.symm).elim
  | succ earlier induction =>
      rewrite [Nat.succ_add, Numerical.run, Numerical.run]
      rewrite [Numerical.run] at observed
      cases action : step control state with
      | stop actual => rfl
      | next next nextState pathEq pastEq =>
          rewrite [action] at observed
          exact induction next nextState observed
      | ask query next legal =>
          rewrite [action] at observed
          let question := query.question state
          let reply := oracle question
          have tail := induction next (query.receive registers state reply) observed
          exact congrArg (fun execution : Basic.Execution (Path.Question Request) Reply Outcome =>
            (⟨execution.value, ⟨question, reply⟩ :: execution.trace⟩ :
              Basic.Execution (Path.Question Request) Reply Outcome)) tail

/-- A witnessed complete execution persists at every larger finite transition bound. -/
theorem completed_persists {earlier later : Nat} (order : earlier ≤ later)
    (control : List (Frame Instruction)) (state : State Request Reply)
    (outcome : Outcome) (completed : outcome ≠ .exhausted)
    (observed : (Numerical.run step registers earlier control state oracle).value = outcome) :
    Numerical.run step registers later control state oracle =
      Numerical.run step registers earlier control state oracle := by
  have remainder := Nat.add_sub_of_le order
  exact (congrArg (fun bound => Numerical.run step registers bound control state oracle) remainder.symm).trans
    (completed_add step registers oracle earlier (later - earlier) control state outcome completed observed)

/-- An actual returned numerical value preserves the complete ordered execution at every larger finite bound. -/
theorem returned_persists {earlier later : Nat} (order : earlier ≤ later)
    (control : List (Frame Instruction)) (state : State Request Reply) (value : Value)
    (observed : (Numerical.run step registers earlier control state oracle).value = .returned value) :
    Numerical.run step registers later control state oracle =
      Numerical.run step registers earlier control state oracle :=
  completed_persists step registers oracle order control state (.returned value) (fun impossible => nomatch impossible)
    observed

/-- An actual numerical failure preserves its offending data and complete trace at every larger finite bound. -/
theorem failed_persists {earlier later : Nat} (order : earlier ≤ later)
    (control : List (Frame Instruction)) (state : State Request Reply) (error : Error)
    (observed : (Numerical.run step registers earlier control state oracle).value = .failed error) :
    Numerical.run step registers later control state oracle =
      Numerical.run step registers earlier control state oracle :=
  completed_persists step registers oracle order control state (.failed error) (fun impossible => nomatch impossible)
    observed

set_option genInjectivity false in
/-- A finite attempt stops with its actual outcome or retains the exhausted unresolved control.

Exhaustion certifies only that this attempt consumed its finite transition
budget. It retains the actual nonterminal configuration and asserts no global
nontermination or impossibility of a later successful observation.
-/
inductive Stopping (execution : Execution Instruction Request Reply) (fuel : Nat) where
  /-- This exact final configuration has the displayed witnessed stopping outcome. -/ | stopped
      (outcome : Outcome) (observed : execution.current.terminal = some outcome)
  /-- This actual unresolved attempt consumed its whole budget without unused transitions. -/ | exhausted
      (pending : execution.current.terminal = none) (spent : execution.usedFuel = fuel)
      (unused : execution.remainingFuel = 0)

set_option genInjectivity false in
/-- A certified finite simulation retains its actual cached execution and exact procedure certificates. -/
structure Attempt (initial : Configuration Instruction Request Reply) (fuel : Nat) where
  /-- The original cached attempt, including every actual chronological configuration. -/ execution :
    Execution Instruction Request Reply
  /-- The retained attempt is produced by the exact original bounded procedure. -/ executionEq :
    execution = scan step registers oracle fuel initial
  /-- The final configuration agrees with original finite simulation. -/ currentEq :
    execution.current = run step registers oracle initial fuel
  /-- The retained configurations are consecutive transitions of the actual original procedure. -/ chain :
    Chain step registers oracle initial execution.configurations execution.current
  /-- Consumed and unused transitions account for the exact original budget. -/ accounted :
    execution.usedFuel + execution.remainingFuel = fuel
  /-- Consumed transitions lie within that original budget. -/ within : execution.usedFuel ≤ fuel
  /-- The actual stop or certified exhaustion boundary of this finite attempt. -/ stopping : Stopping execution fuel

/-- Construct a complete evidence-bearing finite attempt from the actual cached simulation once. -/
@[expose] def attempt (initial : Configuration Instruction Request Reply) (fuel : Nat) :
    Attempt step registers oracle initial fuel :=
  let execution := scan step registers oracle fuel initial
  { execution := execution
    executionEq := rfl
    currentEq := scan_current step registers oracle fuel initial
    chain := scan_chain step registers oracle fuel initial
    accounted := scan_accounted step registers oracle fuel initial
    within := scan_within step registers oracle fuel initial
    stopping := match observed : execution.current.terminal with
      | some outcome => .stopped outcome observed
      | none => .exhausted observed
          (scan_pending step registers oracle fuel initial observed).1
          (scan_pending step registers oracle fuel initial observed).2 }

end Simulation

end Purelib.Computation.Machine.Numerical

end
