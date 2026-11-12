module

import Purelib.Approximation.Gaussian.Observation.Check
import Purelib.Approximation.Gaussian.Observation.Observer.Source

/-! # Imported-transcript success, invalidity and candidate-failure boundaries -/

namespace TestPurelib.Approximation.Gaussian.Observation.Imported

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Observation
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Computation.Query

/-- Every original cached source execution succeeds when its actual admitted reading is checked. -/
theorem source_success (process : Process) (initial : process.State)
    (instructions : List Observer.Instruction) (registers : List Observer.Value) (fuel : Nat) :
    let execution := Observer.Source.execute process initial [.block instructions] registers fuel
    (Observation.Imported.check execution.numerical.trace execution.admitted.point).succeeded :=
  Observation.Imported.Check.of_admitted _

/-- A positive target for the exact imported numerical fixtures. -/
private def target : Request := Request.ofPositive 1 (by decide)

/-- An accurate positive-radius reply distinct from the zero-radius reply at the same question. -/
private def wide : Enclosure.Ball := ⟨0, 1 / 2, by decide⟩

/-- Execute exact acceptance, inaccurate reply, repeated conflict and retryable candidate-failure boundaries. -/
public def run : IO Unit := do
  match Observation.Imported.check [] 0 with
  | .admitted _ _ => pure ()
  | _ => throw (IO.userError "empty imported trace did not admit its rational reading")
  let exactZero : Basic.Exchange Question Enclosure.Ball := ⟨Question.initial target, Enclosure.Ball.point 0⟩
  let inaccurate : Basic.Exchange Question Enclosure.Ball := ⟨Question.initial target, ⟨0, 1, by decide⟩⟩
  match Observation.Imported.check [inaccurate] 0 with
  | .invalid (.inaccurate _ _ _) => pure ()
  | _ => throw (IO.userError "strict target violation was not reported as numerical invalidity")
  let conflicting : Basic.Exchange Question Enclosure.Ball := ⟨Question.initial target, wide⟩
  match Observation.Imported.check [exactZero, conflicting] 0 with
  | .invalid (.repeated _ _ _ _ _ _) => pure ()
  | _ => throw (IO.userError "different complete replies to one exact question were accepted")
  match Observation.Imported.check [exactZero, exactZero] 0 with
  | .admitted result _ =>
      unless result.code.trace.length == 2 do
        throw (IO.userError "checking removed a repeated original occurrence")
  | _ => throw (IO.userError "consistent repeated exact replies were rejected")
  let one : Gaussian.Basic.Canonical := ⟨1, 0⟩
  let atOne : Basic.Exchange Question Enclosure.Ball := ⟨Question.initial target, Enclosure.Ball.point one⟩
  match Observation.Imported.check [atOne] 0 with
  | .inconclusive attempt =>
      unless attempt.unresolved.length == 1 && attempt.inspected == 1 && attempt.candidateBudget == 1 do
        throw (IO.userError "candidate failure lost its unresolved constraint or finite budget")
  | _ => throw (IO.userError "a failed candidate was confused with transcript invalidity")
  match Observation.Imported.check [atOne] one with
  | .admitted _ _ => pure ()
  | _ => throw (IO.userError "retry with the actual exact reading did not succeed")
  IO.print "imported enclosure transcript: six checking boundaries passed\n"

end TestPurelib.Approximation.Gaussian.Observation.Imported
