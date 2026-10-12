module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Cumulative.Basic
public import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Measure.Event.RationalOrder
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Distribution.Cumulative.Grid
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

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

open Purelib.Data.Rat
/-- Cumulative-probability separation at any exact threshold is bounded by the original total variation distance. -/
theorem cumulative_separation_le_totalVariationDistance
    (left right : Distribution Fraction.Rational) (threshold : Fraction.Rational) :
    Distance.rationalSeparation (left.cumulative threshold)
        (right.cumulative threshold) ≤
      left.totalVariationDistance right :=
  left.probability_separation_le_totalVariationDistance right
    (atMostEvent threshold)

/-- A strict total-variation bound gives the same strict cumulative tolerance at every threshold in the retained finite
grid. -/
theorem cumulativeGridClose_of_totalVariationDistance_lt
    (left right : Distribution Fraction.Rational)
    (thresholds : List Fraction.Rational) (tolerance : Fraction.Rational)
    (small : left.totalVariationDistance right < tolerance) :
    CumulativeGridClose left right thresholds tolerance := by
  intro threshold member
  exact (left.cumulative_separation_le_totalVariationDistance
    right threshold).trans_lt small

/-- The exact finite-grid cumulative distance is at most the original total variation distance. -/
theorem cumulativeGridDistance_le_totalVariationDistance
    (left right : Distribution Fraction.Rational)
    (thresholds : List Fraction.Rational) :
    left.cumulativeGridDistance right thresholds ≤
      left.totalVariationDistance right := by
  apply left.cumulativeGridDistance_le right thresholds
  · exact left.totalVariationDistance_nonnegative right
  · intro threshold member
    exact left.cumulative_separation_le_totalVariationDistance right threshold

end Distribution

end Purelib.Measure

end
