module

public import Purelib.Computation.Machine.Halting.Decision
public import Purelib.Computation.Machine.Invocation
import Purelib.Data.Nat.Order

/-!
# Constructive diagonal contradiction for finite coded machines

The diagonal program receives actual program code as input, pairs that
same code with itself, invokes the retained alleged decider, then returns
on a zero prediction and jumps forever on a one prediction. Its encoded
self-input is a finite value; it embeds the alleged decider once and no
recursive program object or halting oracle is introduced.
-/

public section

namespace Purelib.Computation.Machine.Halting.Diagonal

open Purelib.Data.Nat

/-- Construct the actual finite diagonal program around the supplied original alleged decider code. -/
@[expose] def program (decider : Program) : Program :=
  [ .pair 0 0 0, .constant 1 (Value.encode decider), .call 1 0, .jumpZero 0 5 4, .jump 4, .halt ]

/-- Retain the exact encoded self-input for this same actual finite diagonal program. -/
@[expose] def self (decider : Program) : Value := Value.encode (program decider)

/-- The original diagonal computation begins on its exact finite encoded self-input. -/
@[expose] def initial (decider : Program) : Configuration := Configuration.initial (program decider) (self decider)

/-- Retain the original caller at its prediction branch with the same decider input and code. -/
@[expose] def caller (decider : Program) : Frame :=
  ⟨program decider, 3, [Halting.input (program decider) (self decider), Value.encode decider]⟩

/-- The first three steps invoke the alleged decider on the diagonal's exact encoded self-input pair. -/
theorem invokes (decider : Program) : Simulation.run (initial decider) 3 =
    (Configuration.initial decider (Halting.input (program decider) (self decider))).withCaller
      (caller decider) [] := by
  change Configuration.invoke (caller decider) [] (Value.encode decider)
    (Halting.input (program decider) (self decider)) = _
  exact Configuration.invoke_withCaller _ _ _ _

/-- The actual diagonal branch returns after a zero prediction at the retained original caller. -/
theorem branch_zero (decider : Program) :
    Simulation.run (.running ((caller decider).receive (.number 0)) []) 2 = .halted (.number 0) := rfl

/-- The actual diagonal branch enters its same self-jump after a one prediction. -/
theorem branch_one (decider : Program) :
    (.running ((caller decider).receive (.number 1)) [] : Configuration).step =
      .running ⟨program decider, 4, [.number 1, Value.encode decider]⟩ [] := rfl

/-- Every future finite step after a one prediction retains the original self-jump configuration. -/
theorem loop_one (decider : Program) (steps : Nat) :
    Simulation.run (.running ⟨program decider, 4, [.number 1, Value.encode decider]⟩ []) steps =
      .running ⟨program decider, 4, [.number 1, Value.encode decider]⟩ [] :=
  Simulation.run_selfLoop _ _ rfl steps

/-- Retain restoration of the actual diagonal caller at the alleged decider's same first successful halt. -/
theorem returned (decider : Program) {bound : Nat}
    (first : First (Configuration.initial decider (Halting.input (program decider) (self decider))) bound) :
    Simulation.run (initial decider) (3 + first.stage) = .running ((caller decider).receive first.value) [] :=
  (Simulation.run_add (initial decider) 3 first.stage).trans
    ((congrArg (fun state => Simulation.run state first.stage) (invokes decider)).trans
      (Simulation.invocation_returns first (caller decider) []))

/-- A witnessed zero prediction forces this actual diagonal computation to halt. -/
theorem halts_on_zero (decider : Program) {bound : Nat}
    (first : First (Configuration.initial decider (Halting.input (program decider) (self decider))) bound)
    (predicted : first.value = .number 0) : Halts (initial decider) := by
  refine ⟨3 + first.stage + 2, .number 0, ?_⟩
  have atReturn := returned decider first
  have exactReturn : Simulation.run (initial decider) (3 + first.stage) =
      .running ((caller decider).receive (.number 0)) [] :=
    atReturn.trans (congrArg (fun value => Configuration.running ((caller decider).receive value) []) predicted)
  exact (Simulation.run_add (initial decider) (3 + first.stage) 2).trans
    ((congrArg (fun state => Simulation.run state 2) exactReturn).trans (branch_zero decider))

/-- A witnessed one prediction forces every actual future diagonal configuration to remain running. -/
theorem noHalt_on_one (decider : Program) {bound : Nat}
    (first : First (Configuration.initial decider (Halting.input (program decider) (self decider))) bound)
    (predicted : first.value = .number 1) : ¬ Halts (initial decider) := by
  intro halted
  rcases halted with ⟨haltBound, value, atHalt⟩
  let loopStart := 3 + first.stage + 1
  let loopState : Configuration := .running ⟨program decider, 4, [.number 1, Value.encode decider]⟩ []
  have atReturn := returned decider first
  have atLoop : Simulation.run (initial decider) loopStart = loopState := by
    change (Simulation.run (initial decider) (3 + first.stage)).step = _
    rewrite [atReturn, predicted]
    exact branch_one decider
  let later := Nat.max haltBound loopStart
  have loopLe : loopStart ≤ later := Order.le_max_right _ _
  have haltLe : haltBound ≤ later := Order.le_max_left _ _
  have reconstruction := Nat.add_sub_of_le loopLe
  have stillRunning : Simulation.run (initial decider) later = loopState :=
    (congrArg (Simulation.run (initial decider)) reconstruction.symm).trans
      ((Simulation.run_add (initial decider) loopStart (later - loopStart)).trans
        ((congrArg (fun state => Simulation.run state (later - loopStart)) atLoop).trans
          (loop_one decider (later - loopStart))))
  have stillHalted := Simulation.halted_persists (initial decider) haltLe value atHalt
  have impossible := stillRunning.symm.trans stillHalted
  nomatch impossible

/-- No finite coded machine program soundly and totally decides halting of every encoded program and input. -/
theorem no_decider (decider : Decider) : False := by
  rcases decider.correct (program decider.program) (self decider.program) with ⟨bound, decision, halted⟩
  rcases firstHalt_of_halted halted with ⟨stage, observed⟩
  rcases firstHalt_some observed with ⟨first, _⟩
  have last := Simulation.halted_persists _ first.within first.value first.reaches
  have sameValue : first.value = decision.value :=
    Option.some.inj ((congrArg Configuration.output last).symm.trans (congrArg Configuration.output halted))
  cases decision with
  | noHalt absent => exact absent (halts_on_zero decider.program first sameValue)
  | halts witness => exact noHalt_on_one decider.program first sameValue witness

end Purelib.Computation.Machine.Halting.Diagonal

end
