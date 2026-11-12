module

import Purelib.Approximation.Gaussian.Sequence.HaltingShadow.Classifier

/-! # Actual finite shadow-description construction and represented classifier invocation -/

namespace TestPurelib.Approximation.Gaussian.Sequence.HaltingShadow.Classifier

open Purelib
open Purelib.Computation
open Purelib.Approximation.Gaussian.Sequence.HaltingShadow

/-- Check actual wrapper execution of both represented decision values for arbitrary retained task inputs. -/
private def checkTag (tag : Nat) (task : Machine.Program) (input : Machine.Value) : IO Unit := do
  let program : Machine.Program := [.constant 0 (.number tag), .halt]
  let original := Machine.Configuration.initial program (Code.ofProgram task input).description
  match Machine.Halting.inspect original 10 with
  | .pending _ _ _ => throw (IO.userError "classifier fixture failed to return its actual decision tag")
  | .found first =>
      let wrapped := Machine.Simulation.run
        (Machine.Configuration.initial (Classifier.wrapper program) (Machine.Halting.input task input))
        (4 + first.stage + 1)
      match wrapped with
      | .halted (.number actual) =>
          unless actual == tag do throw (IO.userError "represented wrapper changed its classifier's original result")
      | _ => throw (IO.userError "represented wrapper changed the actual returned value constructor")

/-- Check descriptor fields after invoking an initially halted or a direct-return original classifier program. -/
private def checkDescription (program : Machine.Program) (steps : Nat) : IO Unit := do
  let task := Machine.Program.delay 3
  let input := Machine.Value.number 7
  let initial := Machine.Configuration.initial (Classifier.wrapper program) (Machine.Halting.input task input)
  match Machine.Simulation.run initial steps with
  | .halted (.pair (.number 0) (.pair (.program retained) (.number 7))) =>
      unless retained.length == task.length do
        throw (IO.userError "shadow description lost its original retained instruction list")
  | _ => throw (IO.userError "shadow wrapper changed the actual algorithm tag or encoded program/input fields")

/-- Run both result tags, different task codes, exact encoded fields and initially halted classifier invocation. -/
public def run : IO Unit := do
  for tag in [0, 1] do
    checkTag tag Machine.Program.loop (.number 7)
    checkTag tag (Machine.Program.delay 3) (.pair (.number 7) (.program Machine.Program.loop))
  checkDescription [] 5
  checkDescription [.halt] 6
  IO.print "represented reduction: original shadow descriptions and classifier tags survive actual finite invocation\n"

end TestPurelib.Approximation.Gaussian.Sequence.HaltingShadow.Classifier
