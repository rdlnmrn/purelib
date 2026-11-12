module

public import Purelib.Computation.Machine.Syntax

/-!
# Deterministic finite register execution

A configuration retains its actual program, register values, instruction
counter and finite caller stack. Calls consume an encoded original program;
a return restores its actual caller and writes only register zero. Invalid
call data retain the supplied value and a proved decoding failure. Every
bounded simulation performs finitely many deterministic instruction steps.
-/

public section

namespace Purelib.Computation.Machine

set_option genInjectivity false in
/-- An actual machine frame retains its original program, next instruction counter and finite register contents. -/
structure Frame where
  /-- The exact original instruction list executed by this frame. -/ program : Program
  /-- The actual next instruction counter. -/ counter : Nat
  /-- The finite retained register values. -/ registers : List Value

namespace Frame

/-- Advance the same original frame without changing its program or registers. -/
@[expose] def advance (frame : Frame) : Frame := ⟨frame.program, frame.counter + 1, frame.registers⟩

/-- Store one value and advance the same original program counter. -/
@[expose] def store (frame : Frame) (target : Nat) (value : Value) : Frame :=
  ⟨frame.program, frame.counter + 1, Registers.put frame.registers target value⟩

/-- Jump within the same original program while retaining every register value. -/
@[expose] def jump (frame : Frame) (target : Nat) : Frame := ⟨frame.program, target, frame.registers⟩

/-- Receive a returned value in register zero, retaining the actual caller program, counter and all other registers. -/
@[expose] def receive (frame : Frame) (value : Value) : Frame :=
  ⟨frame.program, frame.counter, Registers.put frame.registers 0 value⟩

end Frame

namespace Program

/-- Read one exact instruction; reaching a counter beyond the retained list returns normally. -/
@[expose] def instruction : Program → Nat → Instruction
  | [], _ => .halt
  | first :: _, 0 => first
  | _ :: remaining, index + 1 => instruction remaining index

/-- Construct a finite program that executes the requested number of ticks before returning its original input. -/
@[expose] def delay : Nat → Program
  | 0 => [.halt]
  | ticks + 1 => .tick :: delay ticks

/-- Every instruction strictly before a delayed return is its original tick. -/
theorem instruction_delay_before {ticks index : Nat} (before : index < ticks) :
    (delay ticks).instruction index = .tick := by
  induction ticks generalizing index with
  | zero => exact (Nat.not_lt_zero index before).elim
  | succ ticks induction =>
      cases index with
      | zero => rfl
      | succ index => exact induction (Nat.lt_of_succ_lt_succ before)

/-- The instruction at the retained delayed program's final tick count is its return. -/
theorem instruction_delay_end (ticks : Nat) : (delay ticks).instruction ticks = .halt := by
  induction ticks with
  | zero => rfl
  | succ ticks induction => exact induction

/-- An explicit never-returning instruction repeats the same original program and input. -/
@[expose] def loop : Program := [.jump 0]

end Program

set_option genInjectivity false in
/-- A finite configuration is running, has returned a final value, or retains an identified invalid call input. -/
inductive Configuration where
  /-- The actual active frame and its original finite caller stack. -/ | running (frame : Frame) (stack : List Frame)
  /-- The retained outermost returned value. -/ | halted (value : Value)
  /-- A supplied call value is not an encoded program. -/ | invalid (value : Value) (failed : value.decode = none)

namespace Configuration

/-- Begin at counter zero with the original input in register zero; the empty program returns at once. -/
@[expose] def initial : Program → Value → Configuration
  | [], input => .halted input
  | first :: remaining, input => .running ⟨first :: remaining, 0, [input]⟩ []

/-- A delayed program starts with its same actual finite program and original input register. -/
theorem initial_delay (ticks : Nat) (input : Value) :
    initial (Program.delay ticks) input = .running ⟨Program.delay ticks, 0, [input]⟩ [] := by
  cases ticks <;> rfl

/-- Return to the actual preceding caller, updating only its register zero, or finish the outermost invocation. -/
@[expose] def returnValue (value : Value) : List Frame → Configuration
  | [] => .halted value
  | caller :: earlier => .running (caller.receive value) earlier

/-- Decode and invoke the actual supplied finite program, preserving the same original caller and input. -/
@[expose] def invoke (caller : Frame) (stack : List Frame) : Value → Value → Configuration
  | .program program, input =>
      match initial program input with
      | .halted result => .running (caller.receive result) stack
      | .running frame _ => .running frame (caller :: stack)
      | .invalid value failed => .invalid value failed
  | .number value, _ => .invalid (.number value) rfl
  | .pair left right, _ => .invalid (.pair left right) rfl

/-- Execute one deterministic instruction, retaining all original program and caller owners. -/
@[expose] def step : Configuration → Configuration
  | .halted value => .halted value
  | .invalid value failed => .invalid value failed
  | .running frame stack =>
      match frame.program.instruction frame.counter with
      | .halt => returnValue (Registers.get frame.registers 0) stack
      | .tick => .running frame.advance stack
      | .constant target value => .running (frame.store target value) stack
      | .copy target source => .running (frame.store target (Registers.get frame.registers source)) stack
      | .successor target source =>
          .running (frame.store target (.number ((Registers.get frame.registers source).natural + 1))) stack
      | .predecessor target source =>
          .running (frame.store target (.number (Registers.get frame.registers source).natural.pred)) stack
      | .jump target => .running (frame.jump target) stack
      | .jumpZero source zeroTarget nonzeroTarget =>
          let target := if (Registers.get frame.registers source).natural = 0 then zeroTarget else nonzeroTarget
          .running (frame.jump target) stack
      | .pair target left right =>
          let value := Value.pair (Registers.get frame.registers left) (Registers.get frame.registers right)
          .running (frame.store target value) stack
      | .first target source =>
          let value := match Registers.get frame.registers source with | .pair left _ => left | _ => .number 0
          .running (frame.store target value) stack
      | .second target source =>
          let value := match Registers.get frame.registers source with | .pair _ right => right | _ => .number 0
          .running (frame.store target value) stack
      | .call code input =>
          invoke frame.advance stack (Registers.get frame.registers code) (Registers.get frame.registers input)

/-- A retained outermost halt remains the same exact halt after a further instruction step. -/
theorem step_halted (value : Value) : step (.halted value) = .halted value := rfl

/-- Read an outermost halt value, distinguishing an invalid invocation from successful termination. -/
@[expose] def output : Configuration → Option Value
  | .halted value => some value
  | .running _ _ | .invalid _ _ => none

/-- A successful output readback identifies that same original configuration as an outermost halt. -/
theorem output_some {configuration : Configuration} {value : Value} (equal : configuration.output = some value) :
    configuration = .halted value := by
  cases configuration with
  | running _ _ => cases equal
  | halted actual => cases equal; rfl
  | invalid _ _ => cases equal

/-- An actual jump to the same retained counter preserves the complete original running frame and stack. -/
theorem step_selfLoop (frame : Frame) (stack : List Frame)
    (instruction : frame.program.instruction frame.counter = .jump frame.counter) :
    (.running frame stack : Configuration).step = .running frame stack := by
  unfold step
  dsimp only
  rewrite [instruction]
  cases frame
  rfl

end Configuration

namespace Simulation

/-- Execute exactly the displayed finite number of instruction steps from the same original configuration. -/
@[expose] def run (initial : Configuration) : Nat → Configuration
  | 0 => initial
  | steps + 1 => (run initial steps).step

/-- Further bounded execution continues from the exact previously reached configuration. -/
theorem run_add (initial : Configuration) (earlier later : Nat) :
    run initial (earlier + later) = run (run initial earlier) later := by
  induction later with
  | zero => rfl
  | succ later induction => exact congrArg Configuration.step induction

/-- Every finite bounded execution after a retained halt returns the same original value. -/
theorem run_halted (value : Value) (steps : Nat) : run (.halted value) steps = .halted value := by
  induction steps with
  | zero => rfl
  | succ steps induction => exact (congrArg Configuration.step induction).trans (Configuration.step_halted value)

/-- Every finite bound of an actual self-jump retains the same original complete running configuration. -/
theorem run_selfLoop (frame : Frame) (stack : List Frame)
    (instruction : frame.program.instruction frame.counter = .jump frame.counter) (steps : Nat) :
    run (.running frame stack) steps = .running frame stack := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
      exact (congrArg Configuration.step induction).trans (Configuration.step_selfLoop frame stack instruction)

/-- An outermost halt observed at one bound persists at every displayed later bound. -/
theorem halted_persists (initial : Configuration) {earlier later : Nat} (order : earlier ≤ later) (value : Value)
    (observed : run initial earlier = .halted value) : run initial later = .halted value := by
  have remainder := Nat.add_sub_of_le order
  calc
    run initial later = run initial (earlier + (later - earlier)) := congrArg (run initial) remainder.symm
    _ = run (run initial earlier) (later - earlier) := run_add initial earlier _
    _ = run (.halted value) (later - earlier) := congrArg (fun state => run state (later - earlier)) observed
    _ = .halted value := run_halted value _

/-- Every bounded prefix through the tick count of a delayed program retains its original running frame and input. -/
theorem delay_running (ticks : Nat) (input : Value) {steps : Nat} (within : steps ≤ ticks) :
    run (Configuration.initial (Program.delay ticks) input) steps =
      .running ⟨Program.delay ticks, steps, [input]⟩ [] := by
  induction steps with
  | zero => exact Configuration.initial_delay ticks input
  | succ steps induction =>
      have before : steps < ticks := Nat.lt_of_succ_le within
      have current := induction (Nat.le_of_lt before)
      change (run (Configuration.initial (Program.delay ticks) input) steps).step = _
      rewrite [current]
      unfold Configuration.step
      dsimp only
      rewrite [Program.instruction_delay_before before]
      rfl

/-- A delayed program returns its exact original input after its tick count and one actual return step. -/
theorem delay_halted (ticks : Nat) (input : Value) :
    run (Configuration.initial (Program.delay ticks) input) (ticks + 1) = .halted input := by
  change (run (Configuration.initial (Program.delay ticks) input) ticks).step = _
  rewrite [delay_running ticks input (Nat.le_refl ticks)]
  unfold Configuration.step
  dsimp only
  rewrite [Program.instruction_delay_end]
  rfl

/-- Every finite bound of the explicit loop reaches its same original running configuration. -/
theorem loop_run (input : Value) (steps : Nat) :
    Simulation.run (Configuration.initial Program.loop input) steps = Configuration.initial Program.loop input := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
      exact congrArg Configuration.step induction

end Simulation

end Purelib.Computation.Machine

end
