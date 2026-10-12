module
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Pushforward.Cumulative
public import Purelib.Measure.Distribution.Quantile.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

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
end EvaluationEquivalent

open Purelib.Data.Rat in
/-- Occurrence-wise closeness of two observables bounds separation of their exact pushforward lower quantiles by the
same radius.

Both pushforwards retain the same original source law and the same positive quantile level no greater than one. -/
theorem map_lowerQuantile_rationalSeparation_le {α : Type}
    (source : Distribution α) (left right : α → Fraction.Rational)
    (radius : Fraction.Rational)
    (close : ∀ atom, atom ∈ source.atoms →
      Distance.rationalSeparation (left atom.item) (right atom.item) ≤ radius)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1) :
    Distance.rationalSeparation
        ((source.map left).lowerQuantile level positive atMostOne)
        ((source.map right).lowerQuantile level positive atMostOne) ≤
      radius := by
  let leftQuantile :=
    (source.map left).lowerQuantile level positive atMostOne
  let rightQuantile :=
    (source.map right).lowerQuantile level positive atMostOne
  have rightLe : rightQuantile ≤ leftQuantile + radius := by
    apply ((source.map right).lowerQuantile_le_iff_level_le_cumulative
      level positive atMostOne (leftQuantile + radius)).2
    exact ((source.map left).level_le_cumulative_lowerQuantile
      level positive atMostOne).trans
        (source.map_cumulative_le_add_of_rationalSeparation_le
          left right radius leftQuantile close)
  have reverseClose : ∀ atom, atom ∈ source.atoms →
      Distance.rationalSeparation (right atom.item) (left atom.item) ≤ radius := by
    intro atom member
    rw [Distance.rationalSeparation_symm]
    exact close atom member
  have leftLe : leftQuantile ≤ rightQuantile + radius := by
    apply ((source.map left).lowerQuantile_le_iff_level_le_cumulative
      level positive atMostOne (rightQuantile + radius)).2
    exact ((source.map right).level_le_cumulative_lowerQuantile
      level positive atMostOne).trans
        (source.map_cumulative_le_add_of_rationalSeparation_le
          right left radius rightQuantile reverseClose)
  unfold Distance.rationalSeparation
  apply Fraction.Order.Basic.max_le
  · apply (Fraction.Order.Arithmetic.sub_le_iff_le_add_direct).2
    calc
      leftQuantile ≤ rightQuantile + radius := leftLe
      _ = radius + rightQuantile := by ring1
  · apply (Fraction.Order.Arithmetic.sub_le_iff_le_add_direct).2
    calc
      rightQuantile ≤ leftQuantile + radius := rightLe
      _ = radius + leftQuantile := by ring1
end Distribution

end Purelib.Measure

end
