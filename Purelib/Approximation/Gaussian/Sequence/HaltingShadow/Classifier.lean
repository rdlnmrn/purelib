module

public import Purelib.Approximation.Gaussian.Sequence.HaltingShadow
public import Purelib.Computation.Machine.Invocation
public import Purelib.Computation.Machine.Halting.Decision
import Purelib.Computation.Machine.Halting.Diagonal

/-!
# Effective reduction from represented shadow classifiers

An actual finite instruction wrapper constructs the original shadow description
from encoded program/input data and invokes the supplied classifier code.
Invocation preserves its exact result. Sound operational-zero and reached-
apartness certificates then produce a represented total halting decider.
-/

public section

namespace Purelib.Approximation.Gaussian.Sequence.HaltingShadow

open Purelib
open Purelib.Computation

set_option genInjectivity false in
/-- A shadow decision carries operational-zero evidence or apartness at its actual retained reached state. -/
inductive Decision (code : Code) where
  /-- The original shadow is operationally equivalent to exact zero. -/ | zero
      (equivalent : Gaussian.Equivalence.NamedEquivalent code.named.name (Gaussian.Name.Basic.Named.exact 0))
  /-- This shadow has an actual reached state with a positive candidate bound. -/ | apart (reached : code.ReachedApart)

namespace Decision

/-- Encode the two exhaustive shadow outcomes as their actual zero/one machine result. -/
@[expose] def value {code : Code} : Decision code → Machine.Value
  | .zero _ => .number 0
  | .apart _ => .number 1

/-- Transport the same original shadow decision to the original machine's sound halting decision. -/
@[expose] def halting {code : Code} : Decision code → Machine.Halting.Decision code.initial
  | .zero equivalent => .noHalt (code.noHalt_of_zero equivalent)
  | .apart reached => .halts (code.halts_of_apart reached)

/-- Shadow-to-halting transport preserves the exact represented machine result. -/
theorem halting_value {code : Code} (decision : Decision code) : decision.halting.value = decision.value := by
  cases decision <;> rfl

end Decision

set_option genInjectivity false in
/-- A represented total shadow classifier retains finite program code and sound termination on each description. -/
structure Classifier where
  /-- The exact original finite classifier instruction list. -/ program : Machine.Program
  /-- Each finite shadow description has an actual bounded successful execution carrying its sound original decision. -/
  correct : ∀ code : Code, ∃ bound, ∃ decision : Decision code,
    Machine.Simulation.run (Machine.Configuration.initial program code.description) bound = .halted decision.value

namespace Classifier

/-- Compile the actual finite wrapper that forms the original shadow description and invokes its retained classifier. -/
@[expose] def wrapper (program : Machine.Program) : Machine.Program :=
  [ .constant 1 (.number 0), .pair 0 1 0, .constant 1 (Machine.Value.encode program), .call 1 0, .halt ]

/-- Retain the wrapper caller at its return instruction with the original supplied description and code. -/
@[expose] def caller (program : Machine.Program) (description : Machine.Value) : Machine.Frame :=
  ⟨wrapper program, 4, [description, Machine.Value.encode program]⟩

/-- The wrapper's first four steps install its same original caller around the classifier's exact initial state. -/
theorem wrapper_invokes (program task : Machine.Program) (input : Machine.Value) :
    Machine.Simulation.run (Machine.Configuration.initial (wrapper program) (Machine.Halting.input task input)) 4 =
      (Machine.Configuration.initial program (Code.ofProgram task input).description).withCaller
        (caller program (Code.ofProgram task input).description) [] := by
  change Machine.Configuration.invoke (caller program (Code.ofProgram task input).description) []
      (Machine.Value.encode program) (Code.ofProgram task input).description = _
  exact Machine.Configuration.invoke_withCaller _ _ _ _

/-- The original wrapper caller returns the exact received classifier result. -/
theorem caller_returns (program : Machine.Program) (description value : Machine.Value) :
    (Machine.Configuration.running ((caller program description).receive value) []).step = .halted value := rfl

/-- A retained first classifier halt yields an actual bounded wrapper halt with its same exact result. -/
theorem wrapper_returns (program task : Machine.Program) (input : Machine.Value) {bound : Nat}
    (first : Machine.Halting.First
      (Machine.Configuration.initial program (Code.ofProgram task input).description) bound) :
    Machine.Simulation.run (Machine.Configuration.initial (wrapper program) (Machine.Halting.input task input))
      (4 + first.stage + 1) = .halted first.value := by
  let initial := Machine.Configuration.initial (wrapper program) (Machine.Halting.input task input)
  let description := (Code.ofProgram task input).description
  have invoked := wrapper_invokes program task input
  have returned := Machine.Simulation.invocation_returns first (caller program description) []
  have atReturn : Machine.Simulation.run initial (4 + first.stage) =
      .running ((caller program description).receive first.value) [] :=
    (Machine.Simulation.run_add initial 4 first.stage).trans
      ((congrArg (fun state => Machine.Simulation.run state first.stage) invoked).trans returned)
  change (Machine.Simulation.run initial (4 + first.stage)).step = _
  rewrite [atReturn]
  exact caller_returns program description first.value

/-- Compile an actual represented total halting decider from the supplied finite shadow-classifier program. -/
def toHalting (classifier : Classifier) : Machine.Halting.Decider where
  program := wrapper classifier.program
  correct := by
    intro task input
    let code := Code.ofProgram task input
    rcases classifier.correct code with ⟨bound, decision, halted⟩
    rcases Machine.Halting.firstHalt_of_halted halted with ⟨stage, observed⟩
    rcases Machine.Halting.firstHalt_some observed with ⟨first, stageEq⟩
    have last := Machine.Simulation.halted_persists _ first.within first.value first.reaches
    have sameValue : first.value = decision.value :=
      Option.some.inj ((congrArg Machine.Configuration.output last).symm.trans
        (congrArg Machine.Configuration.output halted))
    refine ⟨4 + first.stage + 1, decision.halting, ?_⟩
    have result := wrapper_returns classifier.program task input first
    exact result.trans (congrArg Machine.Configuration.halted (sameValue.trans decision.halting_value.symm))

/-- No represented total classifier soundly returns operational zero or reached apartness for every coded shadow. -/
theorem no_classifier (classifier : Classifier) : False := Machine.Halting.Diagonal.no_decider classifier.toHalting

end Classifier

end Purelib.Approximation.Gaussian.Sequence.HaltingShadow

end
