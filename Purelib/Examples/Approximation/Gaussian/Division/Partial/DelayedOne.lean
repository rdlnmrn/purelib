module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Division.Partial.Ready
public import Purelib.Approximation.Gaussian.Division.Partial.Run
import Purelib.Approximation.Gaussian.Division.Partial.Step
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Executable examples for retryable division preflight

The delayed-one process intentionally begins with a ball too coarse for the
automatic apartness test.  Its first finite refinement changes to an exact
ball at one.  This witnesses the semantic distinction between progress,
budget exhaustion, and readiness without using a completed value or an
unbounded search.
-/

namespace Purelib.Examples.Approximation.Gaussian.Division.Partial.DelayedOne

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

open Purelib.Approximation.Gaussian.Process
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

/-- A two-state Gaussian process representing one.

The initial state has a unit squared-radius ball centered at zero; refinement stores the exact ball at one while
preserving its unique possible value. -/
def delayedOneProcess :
    Approximation.Gaussian.Process where
  State := Bool
  ball state :=
    if state = true then
      { center := 1
        radiusSq := 0
        radiusSq_nonneg := le_rfl }
    else
      { center := 0
        radiusSq := 1
        radiusSq_nonneg := by decide }
  Possible _ candidate := candidate = 1
  witness _ := ⟨1, rfl⟩
  possible_inside := by
    intro state candidate equal
    subst candidate
    cases state <;> decide
  refine _ _ _ := true
  refine_persists := by
    intro state target positive candidate possible
    exact possible
  accurate := by
    intro state target positive
    exact positive
  centerBound := 1
  centerBound_nonneg := by decide
  center_bounded := by
    intro state
    cases state <;> decide

/-- Coherence allowance one before refinement and zero afterwards. -/
def delayedOneAllowance : Bool →
  Fraction.Rational
  | false => 1
  | true => 0

/-- Coherence data for the two-state process representing one.

Keeps the original Boolean states and allowances; every possible value is exactly one and every refinement reaches the
exact state. -/
def delayedOneCoherent :
  Coherence.Basic.Coherent delayedOneProcess where
  allowance := delayedOneAllowance
  allowance_nonneg := by
    intro state
    cases state <;> decide
  ball_radius_le := by
    intro state
    cases state <;> decide
  possible_close := by
    intro leftState rightState leftValue rightValue leftEqual rightEqual
    subst leftValue
    subst rightValue
    cases leftState <;> cases rightState <;> decide
  accuracyRequest target := target
  accuracyRequest_pos positive := positive
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    exact positive

/-- The coherent name for one initialized with its nonexact ball. -/
def delayedOne : CoherentNamed where
  name := { process := delayedOneProcess, state := false }
  coherent := delayedOneCoherent

/-- The first division step refines the delayed denominator.

The initial ball has no certified separation from zero, so the original step retains its refinement transition. -/
theorem delayedOne_first_step_progresses
  (numerator : CoherentNamed) :
    Partial.Step.step numerator delayedOne
        (Refinement.State.initial
      delayedOne) =
      .progressed (Refinement.State.initial
          delayedOne).advance
        (.refined (Refinement.State.initial
            delayedOne)) := by
  apply Partial.Step.step_eq_progressed_of_not_separated
  decide

/-- The next division step accepts the refined delayed denominator.

At the retained advanced state, separation yields an actual quotient name and its original readiness certificate. -/
theorem delayedOne_second_step_ready
  (numerator : CoherentNamed) :
    ∃ output : CoherentNamed, ∃ valid :
        Approximation.Gaussian.Division.Partial.Ready numerator
            delayedOne
            (Refinement.State.initial
          delayedOne).advance output,
      Partial.Step.step numerator delayedOne
          (Refinement.State.initial
        delayedOne).advance =
        .ready output valid := by
  apply Partial.Step.step_is_ready_of_separated
  decide

/-- A zero-step division attempt retains the initial state as exhausted. -/
theorem delayedOne_zero_fuel_exhausted
  (numerator : CoherentNamed) :
    Partial.Run.attempt numerator delayedOne
        (Refinement.State.initial
      delayedOne) 0 =
      .exhausted (Refinement.State.initial
          delayedOne)
        (.refl (Refinement.State.initial
            delayedOne)) := rfl

/-- A one-step division attempt exhausts after its retained refinement. -/
theorem delayedOne_one_fuel_exhausted
  (numerator : CoherentNamed) :
    Partial.Run.attempt numerator delayedOne
        (Refinement.State.initial
      delayedOne) 1 =
      .exhausted (Refinement.State.initial
          delayedOne).advance
        (.tail (.refined (Refinement.State.initial
            delayedOne))
          (.refl (Refinement.State.initial
              delayedOne).advance)) := by
  rw [Partial.Run.attempt, delayedOne_first_step_progresses]
  rfl

/-- Two division steps suffice for the delayed name of one.

Returns the original quotient, readiness evidence and explicit reachability chain at the advanced denominator state. -/
theorem delayedOne_two_fuel_ready (numerator
  : CoherentNamed) :
    ∃ output : CoherentNamed, ∃ valid :
        Approximation.Gaussian.Division.Partial.Ready numerator
            delayedOne
            (Refinement.State.initial
          delayedOne).advance output,
      ∃ reachable : State.Reachable (Refinement.State.initial
          delayedOne)
          (Refinement.State.initial
              delayedOne).advance,
        Partial.Run.attempt numerator delayedOne
            (Refinement.State.initial
          delayedOne) 2 =
          .ready (Refinement.State.initial
              delayedOne).advance reachable
            output valid := by
  rcases delayedOne_second_step_ready numerator with ⟨output, valid,
    ready⟩
  let reachable : State.Reachable (Refinement.State.initial
      delayedOne)
      (Refinement.State.initial
          delayedOne).advance :=
    .tail (.refined (Refinement.State.initial
        delayedOne))
      (.refl (Refinement.State.initial
          delayedOne).advance)
  have laterReady :
      Partial.Run.attempt numerator delayedOne
          (Refinement.State.initial
        delayedOne).advance 1 =
        .ready (Refinement.State.initial
            delayedOne).advance
          (.refl (Refinement.State.initial
              delayedOne).advance) output
            valid :=
    Partial.Run.attempt_succ_eq_ready_of_step_ready numerator
      delayedOne
      (Refinement.State.initial
          delayedOne).advance 0 output valid ready
  have result := Partial.Run.attempt_succ_eq_ready_of_step_progressed
    numerator delayedOne
        (Refinement.State.initial
      delayedOne)
    (Refinement.State.initial
        delayedOne).advance
        (Refinement.State.initial
      delayedOne).advance
    1 (.refined (Refinement.State.initial
        delayedOne))
    (.refl (Refinement.State.initial
        delayedOne).advance) output valid
    (delayedOne_first_step_progresses numerator) laterReady
  exact ⟨output, valid, reachable, result⟩

end Purelib.Examples.Approximation.Gaussian.Division.Partial.DelayedOne

end
