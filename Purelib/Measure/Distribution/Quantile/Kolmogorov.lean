module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Quantile.Basic
import Purelib.Measure.Distribution.Quantile.Margin
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
public import Purelib.Measure.Distribution.Kolmogorov.Basic
public import Purelib.Measure.Distribution.Median.Basic
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
/-!
# Quantile stability under finite law perturbations

Quantiles need not be Lipschitz under small changes of law: an atom near the
quantile level can move the selected cut discontinuously.  The constructive
finite replacement is an explicit CDF-margin theorem.  Total variation is
computed exactly, and a displayed lower/upper pair brackets the perturbed
quantile whenever the reference cumulative law crosses the requested level
with that margin.
-/

@[expose] public section

namespace Purelib.Measure

namespace Distribution

open Purelib
open Purelib.Data.Rat
/-- A strict Kolmogorov-distance bound and original cumulative margins bracket the perturbed lower quantile.

The bracket has a strict lower endpoint and weak upper endpoint, at the same retained positive level no greater than
one. -/
theorem lowerQuantile_mem_bracket_ofKolmogorovDistance_lt
    (perturbed reference : Measure.Distribution Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1)
    (lower upper tolerance : Fraction.Rational)
    (distanceSmall : perturbed.kolmogorovDistance reference < tolerance)
    (lowerMargin : reference.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ reference.cumulative upper) :
    lower < perturbed.lowerQuantile level positive atMostOne ∧
      perturbed.lowerQuantile level positive atMostOne ≤ upper := by
  apply perturbed.lowerQuantile_mem_bracket_of_cumulative_separations_lt
    reference level positive atMostOne lower upper tolerance
  · exact (perturbed.cumulative_separation_leKolmogorovDistance
      reference lower).trans_lt distanceSmall
  · exact (perturbed.cumulative_separation_leKolmogorovDistance
      reference upper).trans_lt distanceSmall
  · exact lowerMargin
  · exact upperMargin

/-- Zero finite Kolmogorov distance gives equal exact lower quantiles at the same admissible level. -/
theorem lowerQuantile_eq_ofKolmogorovDistance_eq_zero
    (left right : Measure.Distribution Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1)
    (distanceZero : left.kolmogorovDistance right = 0) :
    left.lowerQuantile level positive atMostOne =
      right.lowerQuantile level positive atMostOne := by
  have cumulativeEqual :=
    (left.kolmogorovDistance_eq_zero_iff right).1 distanceZero
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · apply (left.lowerQuantile_le_iff_level_le_cumulative
      level positive atMostOne
      (right.lowerQuantile level positive atMostOne)).2
    rw [cumulativeEqual]
    exact right.level_le_cumulative_lowerQuantile level positive atMostOne
  · apply (right.lowerQuantile_le_iff_level_le_cumulative
      level positive atMostOne
      (left.lowerQuantile level positive atMostOne)).2
    rw [← cumulativeEqual]
    exact left.level_le_cumulative_lowerQuantile level positive atMostOne

/-- Zero finite Kolmogorov distance gives equal computed lower medians. -/
theorem median_eq_ofKolmogorovDistance_eq_zero
    (left right : Measure.Distribution Fraction.Rational)
    (distanceZero : left.kolmogorovDistance right = 0) :
    left.median = right.median :=
  left.lowerQuantile_eq_ofKolmogorovDistance_eq_zero right
    (1 / 2) (by decide) (by decide) distanceZero
end Distribution

end Purelib.Measure

end
