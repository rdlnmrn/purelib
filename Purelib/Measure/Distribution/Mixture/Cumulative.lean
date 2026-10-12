module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Distribution.Cumulative.Grid
public import Purelib.Measure.Distribution.Mixture.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Finite rational cumulative contents

For a rational-valued finite distribution, cumulative probabilities are
exact evaluations of executable order tests.  Monotonicity and interval-mass
identities are finite Boolean-event calculations.  No continuity, supremum,
or real-valued distribution function is introduced.
-/

namespace Purelib.Measure
namespace Distribution

open Purelib.Data.Rat in
/-- A mixture's cumulative probability is the same weighted combination of the original cumulative probabilities. -/
theorem cumulative_mixture
    (left right : Distribution Fraction.Rational) (weight : MixingWeight)
    (threshold : Fraction.Rational) :
    (left.mixture right weight).cumulative threshold =
      weight.coefficient * left.cumulative threshold +
        weight.complement * right.cumulative threshold :=
  left.mixture_probability right weight (atMostEvent threshold)
end Distribution

end Purelib.Measure

end

section
section
@[expose] public section

/-!
# Stability of finite cumulative laws

Total variation controls every executable lower-ray event, hence every exact
rational cumulative probability.  A displayed finite threshold grid packages
these pointwise bounds as the constructive finite replacement for a uniform
CDF comparison.  No supremum over all thresholds or limiting law is formed.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat in
/-- Mixtures with the same retained mixing weight have grid distance bounded by the weighted corresponding component
distances. -/
theorem cumulativeGridDistance_mixture_le
    (leftFirst leftSecond rightFirst rightSecond :
      Distribution Fraction.Rational)
    (weight : MixingWeight) (thresholds : List Fraction.Rational) :
    (leftFirst.mixture leftSecond weight).cumulativeGridDistance
        (rightFirst.mixture rightSecond weight) thresholds ≤
      weight.coefficient *
          leftFirst.cumulativeGridDistance rightFirst thresholds +
        weight.complement *
          leftSecond.cumulativeGridDistance rightSecond thresholds := by
  apply (leftFirst.mixture leftSecond weight).cumulativeGridDistance_le
    (rightFirst.mixture rightSecond weight) thresholds
  · exact add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct weight.nonnegative
        (leftFirst.cumulativeGridDistance_nonnegative rightFirst thresholds))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        weight.complement_nonnegative
        (leftSecond.cumulativeGridDistance_nonnegative rightSecond
          thresholds))
  · intro threshold member
    rw [leftFirst.cumulative_mixture leftSecond weight,
      rightFirst.cumulative_mixture rightSecond weight]
    calc
      Distance.rationalSeparation
          (weight.coefficient * leftFirst.cumulative threshold +
            weight.complement * leftSecond.cumulative threshold)
          (weight.coefficient * rightFirst.cumulative threshold +
            weight.complement * rightSecond.cumulative threshold) ≤
        Distance.rationalSeparation
            (weight.coefficient * leftFirst.cumulative threshold)
            (weight.coefficient * rightFirst.cumulative threshold) +
          Distance.rationalSeparation
            (weight.complement * leftSecond.cumulative threshold)
            (weight.complement * rightSecond.cumulative threshold) :=
        Distance.rationalSeparation_add_le _ _ _ _
      _ = weight.coefficient * Distance.rationalSeparation
            (leftFirst.cumulative threshold) (rightFirst.cumulative threshold) +
          weight.complement * Distance.rationalSeparation
            (leftSecond.cumulative threshold)
            (rightSecond.cumulative threshold) := by
        rw [Distance.rationalSeparation_scale, Distance.rationalSeparation_scale,
          Distance.rationalSeparation_zero_of_nonneg weight.nonnegative,
          Distance.rationalSeparation_zero_of_nonneg weight.complement_nonnegative]
      _ ≤ weight.coefficient *
            leftFirst.cumulativeGridDistance rightFirst thresholds +
          weight.complement *
            leftSecond.cumulativeGridDistance rightSecond thresholds :=
        add_le_add
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (leftFirst.cumulative_separation_le_cumulativeGridDistance
              rightFirst threshold member) weight.nonnegative)
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (leftSecond.cumulative_separation_le_cumulativeGridDistance
              rightSecond threshold member) weight.complement_nonnegative)
end Distribution

end Purelib.Measure

end

end
