module

public import Purelib.Computation.Machine.Halting
public import TestPurelib.Computation.Machine.Simulation

/-! # First-stage zero, delayed detection, bounded absence and persistence -/

namespace TestPurelib.Computation.Machine.Halting

open Purelib.Computation.Machine

/-- Compare one actual first-stage readback against its expected bounded outcome. -/
private def check (program : Program) (input : Value) (bound : Nat) (expected : Option Nat) : IO Unit := do
  let actual := Halting.firstHalt (Configuration.initial program input) bound
  unless actual == expected do
    throw (IO.userError "first-stage scan changed its inclusive-bound or stage-zero convention")
  match Halting.inspect (Configuration.initial program input) bound with
  | .found first =>
      unless first.stage ≤ bound && actual == some first.stage do
        throw (IO.userError "first-stage readback lost its original bounded certificate")
  | .pending current _ _ =>
      match current with
      | .halted _ => throw (IO.userError "bounded absence retained an already halted current configuration")
      | .running _ _ | .invalid _ _ => pure ()

/-- Run initially halted, delayed, never-returning, encoded-call and invalid-call first-stage boundaries. -/
public def run : IO Unit := do
  check [] (.number 7) 0 (some 0)
  check [] (.number 7) 100 (some 0)
  check [.tick, .tick, .halt] (.number 7) 0 none
  check [.tick, .tick, .halt] (.number 7) 2 none
  check [.tick, .tick, .halt] (.number 7) 3 (some 3)
  check [.tick, .tick, .halt] (.number 7) 100 (some 3)
  check Program.loop (.number 7) 100 none
  check Simulation.caller (.number 7) 4 none
  check Simulation.caller (.number 7) 5 (some 5)
  check Simulation.caller (.number 7) 100 (some 5)
  check [.call 0 0] (.number 7) 100 none
  IO.print "first halt: stage zero, delayed detection, bounded loop, encoded invocation and persistence passed\n"

end TestPurelib.Computation.Machine.Halting
