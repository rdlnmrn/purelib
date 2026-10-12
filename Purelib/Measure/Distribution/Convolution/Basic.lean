module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Field
public import Purelib.Measure.Distribution.Equivalence
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Finite rational convolution

Convolution is the finite pushforward of an explicit product distribution by
rational addition.  Its event, expectation, and variance identities are
finite Fubini and independent-moment calculations.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat
/-- Push the exact product of two finite rational distributions forward by addition.

The construction retains the original product occurrences and weights; repeated rational sums remain separate
occurrences. -/
def convolve (left right : Distribution Fraction.Rational) :
    Distribution Fraction.Rational :=
  (left.product right).map fun pair => pair.1 + pair.2

/-- A convolution event's probability is the original left expectation of its translated right-event probabilities. -/
theorem convolve_probability (left right : Distribution Fraction.Rational)
    (event : Fraction.Rational → Bool) :
    (left.convolve right).probability event =
      left.expectation (fun leftValue =>
        right.probability (fun rightValue =>
          event (leftValue + rightValue))) := by
  rw [convolve, map_probability, product_probability_iterated]

/-- Expectation under convolution equals the iterated original expectations of the observable at the coordinate sum. -/
theorem convolve_expectation_value
    (left right : Distribution Fraction.Rational)
    (value : Fraction.Rational → Fraction.Rational) :
    (left.convolve right).expectation value =
      left.expectation (fun leftValue =>
        right.expectation (fun rightValue =>
          value (leftValue + rightValue))) := by
  rw [convolve, map_expectation, product_expectation_iterated]

/-- Exchanging the original convolution factors preserves all event probabilities and rational expectations. -/
theorem convolve_comm_evaluationEquivalent
    (left right : Distribution Fraction.Rational) :
    EvaluationEquivalent (left.convolve right) (right.convolve left) := by
  apply EvaluationEquivalent.of_expectation_eq
  intro value
  rw [left.convolve_expectation_value right value,
    right.convolve_expectation_value left value]
  calc
    left.expectation (fun leftValue =>
          right.expectation (fun rightValue =>
            value (leftValue + rightValue))) =
        right.expectation (fun rightValue =>
          left.expectation (fun leftValue =>
            value (leftValue + rightValue))) :=
      left.expectation_exchange right
        (fun leftValue rightValue => value (leftValue + rightValue))
    _ = right.expectation (fun rightValue =>
          left.expectation (fun leftValue =>
            value (rightValue + leftValue))) := by
      exact right.expectation_congr _ _ (fun rightValue =>
        left.expectation_congr _ _ (fun leftValue => by rw [add_comm]))
end Distribution

end Purelib.Measure

end
