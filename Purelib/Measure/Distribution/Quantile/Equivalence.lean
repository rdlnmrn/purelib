module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Cumulative.Equivalence
public import Purelib.Measure.Distribution.Equivalence
public import Purelib.Measure.Distribution.Quantile.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Uniform stability of constructive finite quantiles

Finite lower quantiles are stable under a displayed uniform rational
perturbation of the source observable.  The proof compares the two executable
cumulative events atom by atom and applies the exact finite generalized-inverse
law.  No infimum, limiting distribution, or completed metric space occurs.
-/

namespace Purelib.Measure

namespace Distribution
namespace EvaluationEquivalent

open Purelib.Data.Rat in
/-- Evaluation-equivalent original rational laws have equal computed lower quantiles at the same admissible level. -/
theorem lowerQuantile_eq
    {left right : Distribution Fraction.Rational}
    (equivalent : EvaluationEquivalent left right)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1) :
    left.lowerQuantile level positive atMostOne =
      right.lowerQuantile level positive atMostOne := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · apply (left.lowerQuantile_le_iff_level_le_cumulative
      level positive atMostOne
      (right.lowerQuantile level positive atMostOne)).2
    rw [equivalent.cumulative_eq]
    exact right.level_le_cumulative_lowerQuantile level positive atMostOne
  · apply (right.lowerQuantile_le_iff_level_le_cumulative
      level positive atMostOne
      (left.lowerQuantile level positive atMostOne)).2
    rw [← equivalent.cumulative_eq]
    exact left.level_le_cumulative_lowerQuantile level positive atMostOne
end EvaluationEquivalent
end Distribution

end Purelib.Measure

end
