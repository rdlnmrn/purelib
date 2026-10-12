module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Division.Partial.Ready
public import Purelib.Approximation.Gaussian.Division.Partial.Step
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Init.Prelude

open Purelib.Approximation.Gaussian.Division.Partial (Ready)

open Purelib

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

section
@[expose] public section

/-!
# Retryable finite preflight for constructive division

An ordinary progressive division is total only after its denominator carries
uniform whole-ball apartness.  This module searches for that certificate one
explicit finite refinement at a time.  It keeps the existing total `Process`
and productive transducer unchanged: a caller receives an ordinary
`CoherentNamed` only in the `ready` case.

Failure of the current rational separation test is represented solely by a
certified progress step.  It is neither evidence that the denominator is zero
nor evidence that zero lies in the current ball.  Manual resumption accepts an
apartness witness indexed by the exact retained denominator state.
-/

namespace Purelib.Approximation.Gaussian.Division.Partial.Run

set_option genInjectivity false in
/-- Terminal result of a caller-bounded automatic run. `exhausted` means only that the supplied natural fuel was
consumed. -/
inductive RunResult (numerator denominator :
  Coherent.CoherentNamed)
    (start : Approximation.Gaussian.Name.Coherent.Refinement.State denominator) : Nat → Type 2
  /-- Retain the successful denominator state, its finite reachability, the actual quotient and its indexed readiness
    certificate. -/ | ready {fuel : Nat} (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator)
      (reachable : State.Reachable start state) (output : Coherent.CoherentNamed)
      (valid : Ready numerator denominator state output) :
      RunResult numerator denominator start fuel
  /-- Retain the final denominator state and finite reachability when the supplied fuel is exhausted. -/ | exhausted
    {fuel : Nat} (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator)
      (reachable : State.Reachable start state) :
      RunResult numerator denominator start fuel

constructive_injectivity RunResult

/-- Structurally recursive finite runner. Fuel is consumed only after a real `progressed` transition. At zero fuel the
retained state is returned unchanged. -/
def attempt (numerator denominator :
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed)
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator) :
    (fuel : Nat) → RunResult numerator denominator state fuel
  | 0 => .exhausted state (.refl state)
  | fuel + 1 =>
      match Purelib.Approximation.Gaussian.Division.Partial.Step.step numerator denominator state with
      | .ready output valid => .ready state (.refl state) output valid
      | .progressed next progress =>
          match attempt numerator denominator next fuel with
          | .ready final reachable output valid =>
              .ready final (.tail progress reachable) output valid
          | .exhausted final reachable =>
              .exhausted final (.tail progress reachable)

/-- A zero-fuel division attempt returns the unchanged source state with reflexive reachability. -/
@[simp] theorem attempt_zero (numerator denominator :
  Coherent.CoherentNamed)
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator) :
    attempt numerator denominator state 0 =
      .exhausted state (.refl state) := rfl

/-- A ready one-step result terminates every positive-fuel run immediately; unused fuel is irrelevant finite budget. -/
theorem attempt_succ_eq_ready_of_step_ready
    (numerator denominator : Coherent.CoherentNamed) (state : Approximation.Gaussian.Name.Coherent.Refinement.State
        denominator)
    (fuel : Nat) (output : Coherent.CoherentNamed)
    (valid : Ready numerator denominator state output)
    (stepReady : Step.step numerator denominator state = .ready output valid) :
    attempt numerator denominator state (fuel + 1) =
      .ready state (.refl state) output valid := by
  rw [attempt, stepReady]

/-- A progressed step prefixes its reachability certificate to a recursively ready finite run. -/
theorem attempt_succ_eq_ready_of_step_progressed
    (numerator denominator : Coherent.CoherentNamed)
    (state next final : Approximation.Gaussian.Name.Coherent.Refinement.State denominator) (fuel : Nat)
    (progress : State.Progress state next) (reachable : State.Reachable next final)
    (output : Coherent.CoherentNamed) (valid : Ready numerator denominator final
        output)
    (stepProgressed : Step.step numerator denominator state =
      .progressed next progress)
    (laterReady : attempt numerator denominator next fuel =
      .ready final reachable output valid) :
    attempt numerator denominator state (fuel + 1) =
      .ready final (.tail progress reachable) output valid := by
  rw [attempt, stepProgressed]
  simp only
  rw [laterReady]

/-- A progressed step likewise retains its transition when the recursive run exhausts its remaining fuel. -/
theorem attempt_succ_eq_exhausted_of_step_progressed
    (numerator denominator : Coherent.CoherentNamed)
    (state next final : Approximation.Gaussian.Name.Coherent.Refinement.State denominator) (fuel : Nat)
    (progress : State.Progress state next) (reachable : State.Reachable next final)
    (stepProgressed : Step.step numerator denominator state =
      .progressed next progress)
    (laterExhausted : attempt numerator denominator next fuel =
      .exhausted final reachable) :
    attempt numerator denominator state (fuel + 1) =
      .exhausted final (.tail progress reachable) := by
  rw [attempt, stepProgressed]
  simp only
  rw [laterExhausted]
end Purelib.Approximation.Gaussian.Division.Partial.Run

end
