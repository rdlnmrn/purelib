module

public import Purelib.Approximation.Gaussian.Name.Coherent.Power
public import Purelib.Data.Gaussian.Norm.Power
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Bounds for independently refined factors of original coherent powers

A finite power retains one process state for each occurrence of its original
input. The state constructor below places every occurrence at one retained
input state, while later arithmetic refinements can select distinct readings
for those occurrences. Bounds concern their actual product rather than an
asserted repeated value of a single chosen witness.
-/

public section

namespace Purelib.Approximation.Gaussian.Name.Coherent.Power

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Initialize every occurrence of an original coherent power at the same retained input process state. -/
@[expose] def stateFrom (value : CoherentNamed) (state : value.name.process.State) :
    (exponent : Nat) → (namedPower value exponent).name.process.State
  | 0 => ()
  | exponent + 1 => (stateFrom value state exponent, state)

/-- Independently possible finite factors satisfy the computed product-displacement bound.

The original initialized input state supplies each factor's magnitude and
distance from the displayed anchor. The claim allows different possible
readings for every retained occurrence in the original power process.
-/
theorem possible_difference_le (value : CoherentNamed) (state : value.name.process.State)
    (anchor : Canonical) (bound distance : Fraction.Rational)
    (boundNonnegative : 0 ≤ bound) (distanceNonnegative : 0 ≤ distance)
    (anchorBound : Norm.Basic.normSq anchor ≤ bound)
    (candidateBound : ∀ {candidate : Canonical}, value.name.process.Possible state candidate →
      Norm.Basic.normSq candidate ≤ bound)
    (candidateDistance : ∀ {candidate : Canonical}, value.name.process.Possible state candidate →
      Norm.Basic.normSq (candidate - anchor) ≤ distance)
    (exponent : Nat) {candidate : Canonical}
    (possible : (namedPower value exponent).name.process.Possible (stateFrom value state exponent) candidate) :
    Norm.Basic.normSq (candidate - anchor ^ exponent) ≤ Norm.Power.differenceFactor bound exponent * distance := by
  induction exponent generalizing candidate with
  | zero =>
      change candidate = 1 at possible
      rewrite [possible, pow_zero, Gaussian.Basic.sub_self, Norm.Basic.normSq_zero]
      change (0 : Fraction.Rational) ≤ 0 * distance
      rewrite [Fraction.Field.zero_mul_direct]
      exact Fraction.Order.Basic.le_refl _
  | succ exponent inductionHypothesis =>
      rcases possible with ⟨left, right, leftPossible, rightPossible, rfl⟩
      have leftDistance := inductionHypothesis leftPossible
      have rightBound := candidateBound rightPossible
      have rightDistance := candidateDistance rightPossible
      have anchorPowerBound : Norm.Basic.normSq (anchor ^ exponent) ≤ bound ^ exponent := by
        rewrite [Norm.Power.normSq_pow]
        exact Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg _) anchorBound exponent
      have firstTerm : Norm.Basic.normSq ((left - anchor ^ exponent) * right) ≤
          (Norm.Power.differenceFactor bound exponent * distance) * bound := by
        rewrite [Norm.Basic.normSq_mul]
        exact Arithmetic.mul_le_mul_direct leftDistance rightBound (Norm.Basic.normSq_nonneg _)
          (Arithmetic.mul_nonneg_direct
            (Norm.Power.differenceFactor_nonnegative boundNonnegative exponent) distanceNonnegative)
      have secondTerm : Norm.Basic.normSq (anchor ^ exponent * (right - anchor)) ≤
          bound ^ exponent * distance := by
        rewrite [Norm.Basic.normSq_mul]
        exact Arithmetic.mul_le_mul_direct anchorPowerBound rightDistance (Norm.Basic.normSq_nonneg _)
          (Arithmetic.pow_nonneg_direct boundNonnegative exponent)
      have identity : left * right - anchor ^ (exponent + 1) =
          (left - anchor ^ exponent) * right + anchor ^ exponent * (right - anchor) := by
        rewrite [pow_succ]
        ring1
      rewrite [identity]
      calc
        _ ≤ 2 * (Norm.Basic.normSq ((left - anchor ^ exponent) * right) +
            Norm.Basic.normSq (anchor ^ exponent * (right - anchor))) := Norm.Bounds.normSq_add_le_two _ _
        _ ≤ 2 * ((Norm.Power.differenceFactor bound exponent * distance) * bound + bound ^ exponent * distance) :=
          Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Arithmetic.add_le_add_direct firstTerm secondTerm) (by decide +kernel)
        _ = Norm.Power.differenceFactor bound (exponent + 1) * distance := by
          rewrite [Norm.Power.differenceFactor_succ]
          ring1

end Purelib.Approximation.Gaussian.Name.Coherent.Power
