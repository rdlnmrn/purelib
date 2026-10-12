module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
import Purelib.Approximation.Gaussian.Acquisition.State
public import Purelib.Approximation.Gaussian.Acquisition.State.Schedule
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Sampling

import Purelib.Data.Rat.Fraction.Order
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Signed

open Purelib.Approximation.Gaussian.Acquisition.State

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Quantitative signed completeness from an unsigned candidate gap

A persistent rational gap removes the near-boundary alternative without
supplying the sign. Both direct requested precision and a coefficient-bounded
canonical refinement schedule construct signed evidence. The canonical
positive result supplies a budget for the original positivity `attempt`.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Signed

/-- Every candidate at the retained coherent state lies outside the displayed open imaginary-coordinate gap.

The predicate retains both possible signs and makes no sign selection or operational zero claim. -/
def Gap (tau : Coherent.CoherentNamed) (state :
  State tau) (delta : Fraction.Rational) : Prop :=
  ∀ {value : Data.Gaussian.Basic.Canonical}, tau.name.process.Possible state.retained.source value →
    value.im ≤ -delta ∨ delta ≤ value.im

namespace Gap

/-- Transport the candidate gap along an explicit persistence certificate between original source states. -/
theorem after {tau : Coherent.CoherentNamed}
  {first last : State tau} {delta : Fraction.Rational}
    (gap : Gap tau first delta)
    (persists : ∀ {value : Data.Gaussian.Basic.Canonical}, tau.name.process.Possible last.retained.source value →
      tau.name.process.Possible first.retained.source value) : Gap
        tau last delta :=
  fun possible => gap (persists possible)

/-- One canonical refinement preserves the retained candidate gap. -/
theorem advance {tau : Coherent.CoherentNamed}
  {state : State tau} {delta : Fraction.Rational}
    (gap : Gap tau state delta) :
      Gap tau (State.advance state) delta :=
  gap.after (fun possible => tau.name.process.refine_persists state.retained.source
    (Gaussian.Process.Sampling.refinementTarget state.retained.nextIndex)
    (Gaussian.Process.Sampling.refinementTarget_pos state.retained.nextIndex) possible)

/-- Every finite canonical refinement schedule preserves the retained candidate gap. -/
theorem advanceN {tau : Coherent.CoherentNamed}
  (state : State tau) {delta : Fraction.Rational}
    (gap : Gap tau state delta) (count : Nat) :
    Gap tau (Schedule.advanceN state count) delta := by
  induction count generalizing state with
  | zero => exact gap
  | succ count inductionHypothesis =>
      exact inductionHypothesis _ gap.advance

/-- A retained candidate gap contradicts strict near-boundary evidence at the same state and threshold. -/
theorem incompatible_near {tau :
  Coherent.CoherentNamed} {state : State tau} {delta : Fraction.Rational}
    (gap : Gap tau state delta)
    (near : Certificate.Near tau state delta) : False := by
  let witness := tau.name.process.witness state.retained.source
  have bounds := near.bounds witness.property
  exact (gap witness.property).elim
    (not_le_of_gt bounds.1) (not_le_of_gt bounds.2)

end Gap
end Purelib.Approximation.Gaussian.Acquisition.Signed

end
