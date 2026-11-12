module

public import Purelib.Computation.Machine.Halting

/-!
# Represented total halting decisions

The decision concerns one original finite machine configuration. A represented
decider retains finite instruction-list code and a termination/correctness
certificate for every encoded program and input. No arbitrary Lean function
is treated as the executable representation of a halting classifier.
-/

public section

namespace Purelib.Computation.Machine.Halting

/-- Encode the original finite program and its exact input as one ordered machine value. -/
@[expose] def input (program : Program) (value : Value) : Value := .pair (Value.encode program) value

set_option genInjectivity false in
/-- A sound halting decision either excludes every finite halt or retains an actual finite halting witness. -/
inductive Decision (initial : Configuration) where
  /-- No original finite simulation reaches an outermost halt. -/ | noHalt (absent : ¬ Halts initial)
  /-- The same original configuration has a finite halting witness. -/ | halts (witness : Halts initial)

namespace Decision

/-- The finite decision result is zero for no halt and one for a witnessed halt. -/
@[expose] def value {initial : Configuration} : Decision initial → Value
  | .noHalt _ => .number 0
  | .halts _ => .number 1

end Decision

set_option genInjectivity false in
/-- A represented total decider retains actual finite program code and its sound terminating result for every input. -/
structure Decider where
  /-- The exact finite instruction list implementing the classifier. -/ program : Program
  /-- Every encoded program/input has an actual bounded successful execution with its sound decision. -/ correct :
    ∀ task : Program, ∀ value : Value, ∃ bound, ∃ decision : Decision (Configuration.initial task value),
      Simulation.run (Configuration.initial program (input task value)) bound = .halted decision.value

end Purelib.Computation.Machine.Halting

end
