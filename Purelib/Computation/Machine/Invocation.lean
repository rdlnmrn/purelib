module

public import Purelib.Computation.Machine.Halting
import Purelib.Data.List.Append

/-!
# Invocation of original finite machine computations

A caller suffix is appended to the actual retained callee stack. The same
instruction steps run until the callee's retained first halt, which restores
that original caller with the exact returned value. No program, register
array or caller position is independently reconstructed by clients.
-/

public section

namespace Purelib.Computation.Machine.Configuration

/-- Append the same original caller suffix to a retained computation, restoring it immediately for an existing halt. -/
@[expose] def withCaller (configuration : Configuration) (caller : Frame) (outer : List Frame) : Configuration :=
  match configuration with
  | .running frame nested => .running frame (nested ++ caller :: outer)
  | .halted value => .running (caller.receive value) outer
  | .invalid value failed => .invalid value failed

/-- Actual encoded invocation installs the same original caller around the callee's own initial configuration. -/
theorem invoke_withCaller (program : Program) (input : Value) (caller : Frame) (outer : List Frame) :
    invoke caller outer (Value.encode program) input = (initial program input).withCaller caller outer := by
  cases program <;> rfl

/-- Before an outermost halt, installing an original caller commutes with the same actual instruction step. -/
theorem step_withCaller (configuration : Configuration) (caller : Frame) (outer : List Frame)
    (notHalted : configuration.output = none) :
    (configuration.withCaller caller outer).step = configuration.step.withCaller caller outer := by
  cases configuration with
  | halted value => cases notHalted
  | invalid value failed => rfl
  | running frame nested =>
      unfold withCaller step
      dsimp only
      cases instruction : frame.program.instruction frame.counter with
      | halt => cases nested <;> rfl
      | tick => rfl
      | constant target value => rfl
      | copy target source => rfl
      | successor target source => rfl
      | predecessor target source => rfl
      | jump target => rfl
      | jumpZero source zeroTarget nonzeroTarget => rfl
      | pair target left right => rfl
      | first target source => rfl
      | second target source => rfl
      | call code input =>
          dsimp only
          unfold invoke
          cases value : Registers.get frame.registers code with
          | number value => rfl
          | pair left right => rfl
          | program program => cases program <;> rfl

end Purelib.Computation.Machine.Configuration

namespace Purelib.Computation.Machine.Simulation

/-- Through the original first halt, the installed caller retains the exact same bounded callee configurations. -/
theorem run_withCaller {initial : Configuration} {bound : Nat} (first : Halting.First initial bound)
    (caller : Frame) (outer : List Frame) {steps : Nat} (within : steps ≤ first.stage) :
    run (initial.withCaller caller outer) steps = (run initial steps).withCaller caller outer := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
      have before : steps < first.stage := Nat.lt_of_succ_le within
      have current := induction (Nat.le_of_lt before)
      change (run (initial.withCaller caller outer) steps).step = _
      rewrite [current]
      exact Configuration.step_withCaller (run initial steps) caller outer (first.before steps before)

/-- At the original retained first halt, invocation restores its same original caller and exact returned value. -/
theorem invocation_returns {initial : Configuration} {bound : Nat} (first : Halting.First initial bound)
    (caller : Frame) (outer : List Frame) :
    run (initial.withCaller caller outer) first.stage = .running (caller.receive first.value) outer :=
  (run_withCaller first caller outer (Nat.le_refl first.stage)).trans
    (congrArg (fun configuration => configuration.withCaller caller outer) first.reaches)

end Purelib.Computation.Machine.Simulation

end
