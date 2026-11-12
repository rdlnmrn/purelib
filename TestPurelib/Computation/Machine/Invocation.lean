module

import Purelib.Computation.Machine.Invocation
import TestPurelib.Computation.Machine.Simulation

/-! # Retained call frames, original register preservation, nested calls and initially halted invocation -/

namespace TestPurelib.Computation.Machine.Invocation

open Purelib.Computation.Machine

/-- Inspect the retained first halt and verify restoration of the same actual caller and untouched second register. -/
private def check (program : Program) (input : Value) (bound : Nat) (expected : Nat) : IO Unit := do
  let initial := Configuration.initial program input
  let caller : Frame := ⟨Program.delay 0, 0, [.number 10, .number 99]⟩
  match Halting.inspect initial bound with
  | .pending _ _ _ => throw (IO.userError "invocation fixture failed to observe its expected actual first halt")
  | .found first =>
      let restored := Purelib.Computation.Machine.Simulation.run (initial.withCaller caller []) first.stage
      match restored with
      | .running frame [] =>
          unless frame.counter == caller.counter do
            throw (IO.userError "invocation changed the original retained caller counter")
          match Registers.get frame.registers 0, Registers.get frame.registers 1 with
          | .number actual, .number other =>
              unless actual == expected && other == 99 do
                throw (IO.userError "invocation lost its returned value or untouched original register")
          | _, _ => throw (IO.userError "invocation changed original register value constructors")
      | _ => throw (IO.userError "invocation failed to restore its same original caller frame")
      match Purelib.Computation.Machine.Simulation.run (initial.withCaller caller []) (first.stage + 1) with
      | .halted (.number actual) =>
          unless actual == expected do throw (IO.userError "restored caller changed the original callee result")
      | _ => throw (IO.userError "restored caller failed its original return instruction")

/-- Check direct, nested, initially halted and delayed invocation against original retained caller registers. -/
public def run : IO Unit := do
  check [] (.number 7) 0 7
  check Simulation.increment (.number 7) 10 8
  check Simulation.caller (.number 7) 10 8
  check (Program.delay 3) (.number 7) 10 7
  IO.print "invocation: initial halt, direct and nested calls preserve original caller frames and other registers\n"

end TestPurelib.Computation.Machine.Invocation
