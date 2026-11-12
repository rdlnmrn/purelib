module

import Purelib.Computation.Machine.Halting.Diagonal

/-! # Actual encoded self-input and the two opposite finite diagonal execution branches -/

namespace TestPurelib.Computation.Machine.Halting.Diagonal

open Purelib.Computation.Machine

/-- Check that the diagonal actually presents both original encoded self-input occurrences to its predictor. -/
private def checkInput : IO Unit := do
  let predictor : Program := [.halt]
  let initial := Halting.Diagonal.initial predictor
  match Simulation.run initial 3 with
  | .running frame [_] =>
      match Registers.get frame.registers 0 with
      | .pair (.program first) (.program second) =>
          unless first.length == (Halting.Diagonal.program predictor).length && first.length == second.length do
            throw (IO.userError "diagonal invocation lost either original encoded self-input occurrence")
      | _ => throw (IO.userError "diagonal predictor did not receive its actual encoded self-input pair")
  | _ => throw (IO.userError "diagonal did not install its original predictor invocation and caller")

/-- Check the actual diagonal return on zero and retained self-jump on one, using finite predictor programs. -/
public def run : IO Unit := do
  checkInput
  let predictsZero : Program := [.constant 0 (.number 0), .halt]
  let predictsOne : Program := [.constant 0 (.number 1), .halt]
  let zeroRun := Halting.Diagonal.initial predictsZero
  let oneRun := Halting.Diagonal.initial predictsOne
  unless Halting.firstHalt zeroRun 100 == some 7 && Halting.firstHalt oneRun 100 == none do
    throw (IO.userError "diagonal changed its actual zero-return or one-loop execution branch")
  match Simulation.run zeroRun 7 with
  | .halted (.number 0) => pure ()
  | _ => throw (IO.userError "zero prediction did not produce the original opposite halting behavior")
  for bound in [6, 7, 20, 100] do
    match Simulation.run oneRun bound with
    | .running frame [] =>
        unless frame.counter == 4 do throw (IO.userError "one prediction left its retained original self-jump")
        match Registers.get frame.registers 0 with
        | .number 1 => pure ()
        | _ => throw (IO.userError "one prediction lost its original retained decision value")
    | _ => throw (IO.userError "one prediction produced an unexpected finite halt or failed invocation")
  IO.print "coded diagonal: exact self-input, opposite zero-return and one-loop branches passed\n"

end TestPurelib.Computation.Machine.Halting.Diagonal
