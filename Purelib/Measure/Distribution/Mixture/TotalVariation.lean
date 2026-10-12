module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Mixture.Basic
public import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Total variation distance between finite rational laws

The duplicate-free union of two displayed atom catalogues supports their
signed difference.  A decidable comparison of the two singleton masses gives
an executable Hahn event.  For probability distributions this event attains
the largest possible event-probability discrepancy, because the positive and
negative Jordan masses agree.

Thus total variation is an exact rational computation here.  The development
proves its sharp event bound, half-L1 formula, metric laws modulo evaluation
equivalence, contraction under pushforward, and the coupling inequality.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat in
/-- Mixtures with the same retained weight have total variation bounded by the weighted corresponding component
distances. -/
theorem totalVariationDistance_mixture_le
    {α : Type} [DecidableEq α]
    (leftFirst leftSecond rightFirst rightSecond : Distribution α)
    (weight : MixingWeight) :
    (leftFirst.mixture rightFirst weight).totalVariationDistance
        (leftSecond.mixture rightSecond weight) ≤
      weight.coefficient *
          leftFirst.totalVariationDistance leftSecond +
        weight.complement *
          rightFirst.totalVariationDistance rightSecond := by
  let event := (leftFirst.mixture rightFirst weight).totalVariationEvent
    (leftSecond.mixture rightSecond weight)
  have leftBound : leftFirst.probability event -
        leftSecond.probability event ≤
      leftFirst.totalVariationDistance leftSecond :=
    (Fraction.Order.Basic.le_max_left _ _).trans
      (leftFirst.probability_separation_le_totalVariationDistance
        leftSecond event)
  have rightBound : rightFirst.probability event -
        rightSecond.probability event ≤
      rightFirst.totalVariationDistance rightSecond :=
    (Fraction.Order.Basic.le_max_left _ _).trans
      (rightFirst.probability_separation_le_totalVariationDistance
        rightSecond event)
  calc
    (leftFirst.mixture rightFirst weight).totalVariationDistance
          (leftSecond.mixture rightSecond weight) =
        (leftFirst.mixture rightFirst weight).probability event -
          (leftSecond.mixture rightSecond weight).probability event :=
      ((leftFirst.mixture rightFirst weight).probability_sub_at_totalVariationEvent
          (leftSecond.mixture rightSecond weight)).symm
    _ = weight.coefficient *
          (leftFirst.probability event - leftSecond.probability event) +
        weight.complement *
          (rightFirst.probability event - rightSecond.probability event) := by
      rw [leftFirst.mixture_probability rightFirst weight,
        leftSecond.mixture_probability rightSecond weight]
      ring1
    _ ≤ weight.coefficient *
          leftFirst.totalVariationDistance leftSecond +
        weight.complement *
          rightFirst.totalVariationDistance rightSecond :=
      add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          leftBound weight.nonnegative)
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rightBound
          weight.complement_nonnegative)
end Distribution

end Purelib.Measure

end
