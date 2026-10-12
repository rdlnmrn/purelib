module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Mixture.Basic
import Purelib.Measure.Distribution.Cumulative.Basic
public import Purelib.Measure.Distribution.Kolmogorov.Basic
import Purelib.Measure.Distribution.Mixture.Cumulative
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Exact finite Kolmogorov distance

For two finite rational laws, cumulative probabilities can change only at
payloads displayed by one of the two atom tables.  A terminating search finds
the greatest displayed payload below any supplied rational cut.  Consequently
the maximum CDF discrepancy on the finite union of the two support tables
controls every rational cut; no supremum over the rational or real line is
formed.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib in
open Purelib.Data.Rat in
/-- Mixtures with the same retained weight have Kolmogorov distance bounded by the weighted corresponding component
distances. -/
theorem kolmogorovDistance_mixture_le
    (leftFirst leftSecond rightFirst rightSecond :
      Distribution Fraction.Rational)
    (weight : Measure.MixingWeight) :
    (leftFirst.mixture rightFirst weight).kolmogorovDistance
        (leftSecond.mixture rightSecond weight) ≤
      weight.coefficient *
          leftFirst.kolmogorovDistance leftSecond +
        weight.complement *
          rightFirst.kolmogorovDistance rightSecond := by
  apply (leftFirst.mixture rightFirst weight).kolmogorovDistance_le
    (leftSecond.mixture rightSecond weight)
  · exact add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct weight.nonnegative
        (leftFirst.kolmogorovDistance_nonnegative leftSecond))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        weight.complement_nonnegative
        (rightFirst.kolmogorovDistance_nonnegative rightSecond))
  · intro cut
    rw [leftFirst.cumulative_mixture rightFirst weight,
      leftSecond.cumulative_mixture rightSecond weight]
    calc
      Distance.rationalSeparation
          (weight.coefficient * leftFirst.cumulative cut +
            weight.complement * rightFirst.cumulative cut)
          (weight.coefficient * leftSecond.cumulative cut +
            weight.complement * rightSecond.cumulative cut) ≤
        Distance.rationalSeparation
            (weight.coefficient * leftFirst.cumulative cut)
            (weight.coefficient * leftSecond.cumulative cut) +
          Distance.rationalSeparation
            (weight.complement * rightFirst.cumulative cut)
            (weight.complement * rightSecond.cumulative cut) :=
        Distance.rationalSeparation_add_le _ _ _ _
      _ = weight.coefficient * Distance.rationalSeparation
            (leftFirst.cumulative cut) (leftSecond.cumulative cut) +
          weight.complement * Distance.rationalSeparation
            (rightFirst.cumulative cut) (rightSecond.cumulative cut) := by
        rw [Distance.rationalSeparation_scale, Distance.rationalSeparation_scale,
          Distance.rationalSeparation_zero_of_nonneg weight.nonnegative,
          Distance.rationalSeparation_zero_of_nonneg weight.complement_nonnegative]
      _ ≤ weight.coefficient *
            leftFirst.kolmogorovDistance leftSecond +
          weight.complement *
            rightFirst.kolmogorovDistance rightSecond :=
        add_le_add
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (leftFirst.cumulative_separation_leKolmogorovDistance
              leftSecond cut) weight.nonnegative)
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (rightFirst.cumulative_separation_leKolmogorovDistance
              rightSecond cut) weight.complement_nonnegative)
end Distribution

end Purelib.Measure

end
