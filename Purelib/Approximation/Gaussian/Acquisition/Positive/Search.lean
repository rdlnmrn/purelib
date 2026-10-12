module
public import Purelib.Approximation.Gaussian.Acquisition.Positive.Enclosure
import Purelib.Approximation.Gaussian.Acquisition.State
public import Purelib.Approximation.Gaussian.Acquisition.State.Schedule
import Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary.Positive
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
public import Purelib.Control.FiniteRunner.Basic
import Init.Core
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic

open Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic (PositiveEnclosure)

open Purelib

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Positive

open Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.Control

open Purelib.Control.FiniteRunner

section
@[expose] public section

/-!
# Automatic discovery of the initial positive enclosure

A cached rational ball passes when its centre is above the real axis and its
squared radius is below the squared half-height. The soundness proof gives a
positive imaginary lower bound for every point in that ball. Failed tests
perform one canonical finite refinement; bounded runs retain their exact
state on exhaustion and never infer a negative positivity verdict.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Positive.Search

/-- One finite inspection either discovers the reusable positive enclosure or refines the retained source once. No
exclusion case is manufactured. -/
def inspect (tau : Coherent.CoherentNamed) (state :
  Approximation.Gaussian.Acquisition.State tau) :
    Sum (PositiveEnclosure tau) (Approximation.Gaussian.Acquisition.State tau) :=
  if test : Positive.PositiveTest state.ball then .inl (Enclosure.enclosure state test)
  else .inr (State.advance state)

/-- A successful cached-ball positivity test makes inspection return the enclosure at that exact retained state. -/
theorem inspect_of_positive {tau :
  Coherent.CoherentNamed} (state : Approximation.Gaussian.Acquisition.State tau)
    (test : Positive.PositiveTest state.ball) :
    inspect tau state = .inl (Enclosure.enclosure state test) := by
  rw [inspect, dif_pos test]

/-- An unresolved cached-ball positivity test makes inspection return exactly one canonical refinement. -/
theorem inspect_of_unresolved {tau :
  Coherent.CoherentNamed} (state : Approximation.Gaussian.Acquisition.State tau)
    (unresolved : ¬ Positive.PositiveTest state.ball) :
    inspect tau state = .inr (State.advance state) := by
  rw [inspect, dif_neg unresolved]

/-- A bounded positivity-search result retaining either a positive enclosure or the exact exhausted acquisition state.
-/
def Result (tau : Coherent.CoherentNamed) : Type :=
  LegendreTransport.ResultPayload.{0, 0}
    (PositiveEnclosure tau) (Approximation.Gaussian.Acquisition.State tau)

/-- Bounded discovery reuses the same finite runner as single-matrix acquisition. A caller can resume an exhausted
result at exactly its state. -/
def attempt (tau : Coherent.CoherentNamed) (state :
  Approximation.Gaussian.Acquisition.State tau) (fuel : Nat) : Result
      tau :=
  FiniteRunner.Basic.runPayload (inspect tau) state fuel

/-- A zero-budget positivity search retains its starting acquisition state as exhausted. -/
@[simp] theorem attempt_zero (tau :
  Coherent.CoherentNamed) (state : Approximation.Gaussian.Acquisition.State tau) :
    attempt tau state 0 = .exhausted state := rfl

/-- Splitting a finite search budget is equivalent to resuming its exhausted state with the remaining budget. -/
theorem attempt_add (tau : Coherent.CoherentNamed)
  (state : Approximation.Gaussian.Acquisition.State tau) (first second : Nat) :
    attempt tau state (first + second) =
      match attempt tau state first with
      | .ready certificate => .ready certificate
      | .exhausted retained => attempt tau retained second := by
  unfold Result
  have law := FiniteRunner.Basic.runPayload_add
    (inspect tau) state first second
  cases firstRun : FiniteRunner.Basic.runPayload (inspect tau) state
    first <;>
    simpa only [attempt, firstRun] using law

/-- A displayed passing state needs exactly one inspection to finish. -/
theorem attempt_one_of_positive {tau :
  Coherent.CoherentNamed} (state : Approximation.Gaussian.Acquisition.State tau)
    (test : Positive.PositiveTest state.ball) :
    attempt tau state 1 = .ready (Enclosure.enclosure state
      test) := by
  unfold attempt
  rw [FiniteRunner.Basic.runPayload, inspect_of_positive state test]

/-- Any positive search budget returns the enclosure immediately when the current cached ball passes. -/
theorem attempt_succ_of_positive {tau :
  Coherent.CoherentNamed} (state : Approximation.Gaussian.Acquisition.State tau)
    (test : Positive.PositiveTest state.ball) (fuel : Nat) :
    attempt tau state (fuel + 1) = .ready
      (Enclosure.enclosure state test) := by
  unfold attempt
  rw [FiniteRunner.Basic.runPayload, inspect_of_positive state test]

/-- An unresolved first inspection consumes one step and continues from the canonical refined state. -/
theorem attempt_succ_of_unresolved {tau :
  Coherent.CoherentNamed} (state : Approximation.Gaussian.Acquisition.State tau)
    (unresolved : ¬ Positive.PositiveTest state.ball) (fuel : Nat) :
    attempt tau state (fuel + 1) =
      attempt tau (State.advance state) fuel := by
  unfold attempt
  rw [FiniteRunner.Basic.runPayload, inspect_of_unresolved state
    unresolved]

/-- A finite passing-state witness gives a certified sufficient budget. The algorithm may stop earlier; no infinitary
fairness assumption is used. -/
def finishBy {tau :
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed} (state :
  Approximation.Gaussian.Acquisition.State tau) :
    (count : Nat) → Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary.Positive.PositiveTest
      (Purelib.Approximation.Gaussian.Acquisition.State.Schedule.advanceN state count).ball →
      { certificate : PositiveEnclosure tau //
        attempt tau state (count + 1) = .ready certificate }
  | 0, test => ⟨Purelib.Approximation.Gaussian.Acquisition.Positive.Enclosure.enclosure state test,
    attempt_one_of_positive state test⟩
  | count + 1, test => by
      by_cases now : Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary.Positive.PositiveTest state.ball
      · exact ⟨Purelib.Approximation.Gaussian.Acquisition.Positive.Enclosure.enclosure state now,
          attempt_succ_of_positive state now (count + 1)⟩
      · let later := finishBy
          (Purelib.Approximation.Gaussian.Acquisition.State.advance state) count test
        exact ⟨later.val,
          (attempt_succ_of_unresolved state now (count +
            1)).trans later.property⟩
end Purelib.Approximation.Gaussian.Acquisition.Positive.Search

end
