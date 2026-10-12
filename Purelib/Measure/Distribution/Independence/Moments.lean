module

import Purelib.Tactic.Ring
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Independence.Basic
import Purelib.Measure.Weighted.Integral
public import Purelib.Measure.Distribution.Moments.Covariance
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Independence of finite rational events

Independence is an exact rational multiplication identity between three
finite event evaluations.  Event families remain displayed lists.
-/

namespace Purelib.Measure

/-- Independent Boolean events have zero covariance between their indicators. -/
theorem Distribution.covariance_indicators_eq_zero_of_independent
    {α : Type} (distribution : Distribution α)
    {left right : α → Bool}
    (independent : distribution.IndependentEvents left right) :
    distribution.covariance (indicator left) (indicator right) = 0 := by
  rw [distribution.covariance_eq_productMoment_sub_means,
    distribution.expectation_indicator_mul_indicator,
    distribution.expectation_indicator,
    distribution.expectation_indicator,
    independent, sub_self]

/-- Zero covariance between two Boolean indicators implies independence of their original events. -/
theorem Distribution.independentEvents_of_covariance_indicators_eq_zero
    {α : Type} (distribution : Distribution α)
    {left right : α → Bool}
    (zero : distribution.covariance (indicator left) (indicator right) = 0) :
    distribution.IndependentEvents left right := by
  rw [distribution.covariance_eq_productMoment_sub_means,
    distribution.expectation_indicator_mul_indicator,
    distribution.expectation_indicator,
    distribution.expectation_indicator] at zero
  change distribution.probability (intersectionEvent left right) =
    distribution.probability left * distribution.probability right
  calc
    distribution.probability (intersectionEvent left right) =
        (distribution.probability (intersectionEvent left right) -
          distribution.probability left * distribution.probability right) +
            distribution.probability left * distribution.probability right := by ring1
    _ = 0 + distribution.probability left * distribution.probability right :=
      congrArg (fun amount => amount +
        distribution.probability left * distribution.probability right) zero
    _ = distribution.probability left * distribution.probability right := by ring1
end Purelib.Measure

end
