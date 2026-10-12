module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
/-!
# Conditional expectation over displayed finite partitions

This module proves the finite rational form of the law of total expectation.
Every partition cell is an executable Boolean event, every sum is a displayed
list sum, and positivity of conditioning cells is carried explicitly.  No
sigma-algebra, completion, or limiting conditional expectation is formed.
-/

@[expose] public section

namespace Purelib.Measure
namespace Distribution

open Purelib.Data.Rat
/-- Take the conditional mean of squared deviation from the original event's conditional mean. -/
def conditionalVariance {α : Type} (distribution : Distribution α)
    (event : α → Bool) (value : α → Fraction.Rational) : Fraction.Rational :=
  distribution.conditionalMean event fun item =>
    (value item - distribution.conditionalMean event value) ^ 2

/-- Conditional variance on a positive-probability event is nonnegative. -/
theorem conditionalVariance_nonneg {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Fraction.Rational) :
    0 ≤ distribution.conditionalVariance event value := by
  unfold conditionalVariance
  apply distribution.conditionalMean_nonneg event positive
  intro atom member
  exact Fraction.Order.Arithmetic.sq_nonneg_direct _

/-- On a positive-probability event, conditional variance is the conditional second moment minus squared conditional
mean. -/
theorem conditionalVariance_eq_secondMoment_sub_sq {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Fraction.Rational) :
    distribution.conditionalVariance event value =
      distribution.conditionalMean event (fun item => value item ^ 2) -
        distribution.conditionalMean event value ^ 2 := by
  unfold conditionalVariance
  calc
    distribution.conditionalMean event (fun item =>
        (value item - distribution.conditionalMean event value) ^ 2) =
        distribution.conditionalMean event (fun item =>
          (value item ^ 2 -
            (2 * distribution.conditionalMean event value) * value item) +
            distribution.conditionalMean event value ^ 2) :=
      distribution.conditionalMean_congr event _ _ (fun item => by ring1)
    _ = distribution.conditionalMean event (fun item => value item ^ 2) -
          distribution.conditionalMean event value ^ 2 := by
      rw [distribution.conditionalMean_add,
        distribution.conditionalMean_sub, distribution.conditionalMean_scale,
        distribution.conditionalMean_constant event positive]
      ring1

/-- On a positive-probability event, conditional squared deviation around a center equals conditional variance plus
squared displacement of the conditional mean. -/
theorem conditionalMean_sq_sub_center {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Fraction.Rational) (center : Fraction.Rational) :
    distribution.conditionalMean event
        (fun item => (value item - center) ^ 2) =
      distribution.conditionalVariance event value +
        (distribution.conditionalMean event value - center) ^ 2 := by
  calc
    distribution.conditionalMean event (fun item =>
        (value item - center) ^ 2) =
        distribution.conditionalMean event (fun item =>
          (value item ^ 2 - (2 * center) * value item) + center ^ 2) :=
      distribution.conditionalMean_congr event _ _ (fun item => by ring1)
    _ = distribution.conditionalVariance event value +
          (distribution.conditionalMean event value - center) ^ 2 := by
      rw [distribution.conditionalMean_add,
        distribution.conditionalMean_sub, distribution.conditionalMean_scale,
        distribution.conditionalMean_constant event positive,
        distribution.conditionalVariance_eq_secondMoment_sub_sq event positive]
      ring1

end Distribution

end Purelib.Measure

end
