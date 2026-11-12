module

public import Purelib.Computation.Machine.Simulation

/-! # Encoded calls, self-input data, invalid invocations and finite execution boundaries -/

namespace TestPurelib.Computation.Machine.Simulation

open Purelib.Computation.Machine

/-- A finite callee increments its original natural input and returns it. -/
@[expose] public def increment : Program := [.successor 0 0, .halt]

/-- A finite caller invokes the actual encoded increment program with its original input. -/
@[expose] public def caller : Program := [.constant 1 (Value.encode increment), .call 1 0, .halt]

/-- The actual encoded invocation returns to its original caller with the incremented input. -/
public theorem encoded_call (input : Nat) :
    (Simulation.run (Configuration.initial caller (.number input)) 5).output = some (.number (input + 1)) := rfl

/-- A finite program pairs its original input with that same retained input. -/
@[expose] public def duplicate : Program := [.copy 1 0, .pair 0 0 1, .halt]

/-- The finite program preserves both exact original input occurrences, including encoded self-input. -/
public theorem duplicate_input (input : Value) :
    (Simulation.run (Configuration.initial duplicate input) 3).output = some (.pair input input) := rfl

/-- Check a retained finite simulation's natural result or bounded absence of successful termination. -/
private def check (program : Program) (input : Value) (steps : Nat) (expected : Option Nat) : IO Unit := do
  let actual := match (Simulation.run (Configuration.initial program input) steps).output with
    | some (.number value) => some value
    | _ => none
  unless actual == expected do
    throw (IO.userError "finite machine simulation changed its retained expected result")

/-- Exercise initial halt, delayed halt, a never-returning run, encoded invocation, self-input and invalid call data. -/
public def run : IO Unit := do
  check [] (.number 7) 0 (some 7)
  check [.tick, .tick, .halt] (.number 7) 2 none
  check [.tick, .tick, .halt] (.number 7) 3 (some 7)
  check Program.loop (.number 7) 100 none
  check caller (.number 7) 5 (some 8)
  let input := Value.encode duplicate
  match (Purelib.Computation.Machine.Simulation.run (Configuration.initial duplicate input) 3).output with
  | some (.pair (.program first) (.program second)) =>
      unless first.length == duplicate.length && second.length == duplicate.length do
        throw (IO.userError "encoded self-input lost its retained program occurrences")
  | _ => throw (IO.userError "encoded self-input changed its finite value constructors")
  match Purelib.Computation.Machine.Simulation.run (Configuration.initial [.call 0 0] (.number 7)) 1 with
  | .invalid (.number 7) _ => pure ()
  | _ => throw (IO.userError "invalid invocation lost its original supplied value and typed failure")
  IO.print "finite machine: initial and delayed halt, bounded loop, encoded call, self-input and invalid call passed\n"

end TestPurelib.Computation.Machine.Simulation
