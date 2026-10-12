module
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Cumulative.Basic
public import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Cumulative.TotalVariation
public import Purelib.Measure.Distribution.Quantile.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
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

open Purelib.Data.Rat
/-- A strict reference cumulative margin including exact total variation places the perturbed lower quantile above the
cut. -/
theorem cut_lt_lowerQuantile_of_cumulative_add_totalVariation_lt_level
    (perturbed reference : Distribution Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1)
    (cut : Fraction.Rational)
    (margin : reference.cumulative cut +
      perturbed.totalVariationDistance reference < level) :
    cut < perturbed.lowerQuantile level positive atMostOne := by
  apply Fraction.Order.Arithmetic.lt_of_not_ge_direct
  intro quantileLeCut
  have levelLePerturbed : level ≤ perturbed.cumulative cut :=
    ((perturbed.lowerQuantile_le_iff_level_le_cumulative
      level positive atMostOne cut).1 quantileLeCut)
  have cumulativeDifference :
      perturbed.cumulative cut - reference.cumulative cut ≤
        perturbed.totalVariationDistance reference :=
    (Fraction.Order.Basic.le_max_left
      (perturbed.cumulative cut - reference.cumulative cut)
      (reference.cumulative cut - perturbed.cumulative cut)).trans
      (perturbed.cumulative_separation_le_totalVariationDistance
        reference cut)
  have perturbedLe : perturbed.cumulative cut ≤
      reference.cumulative cut +
        perturbed.totalVariationDistance reference := by
    have shifted := (Fraction.Order.Arithmetic.sub_le_iff_le_add_direct).mp cumulativeDifference
    simpa only [-eq_self, -iff_self, add_comm] using shifted
  exact (not_le_of_gt margin) (levelLePerturbed.trans perturbedLe)

/-- A reference cumulative upper margin including exact total variation places the perturbed lower quantile at or below
the cut. -/
theorem lowerQuantile_le_cut_of_level_add_totalVariation_le_cumulative
    (perturbed reference : Distribution Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1)
    (cut : Fraction.Rational)
    (margin : level + perturbed.totalVariationDistance reference ≤
      reference.cumulative cut) :
    perturbed.lowerQuantile level positive atMostOne ≤ cut := by
  apply (perturbed.lowerQuantile_le_iff_level_le_cumulative
    level positive atMostOne cut).2
  have cumulativeDifference :
      reference.cumulative cut - perturbed.cumulative cut ≤
        perturbed.totalVariationDistance reference :=
    (Fraction.Order.Basic.le_max_right
      (perturbed.cumulative cut - reference.cumulative cut)
      (reference.cumulative cut - perturbed.cumulative cut)).trans
      (perturbed.cumulative_separation_le_totalVariationDistance
        reference cut)
  have referenceLe : reference.cumulative cut ≤
      perturbed.totalVariationDistance reference +
        perturbed.cumulative cut :=
    (Fraction.Order.Arithmetic.sub_le_iff_le_add_direct).mp cumulativeDifference
  have translated : level + perturbed.totalVariationDistance reference ≤
      perturbed.cumulative cut +
        perturbed.totalVariationDistance reference := by
    calc
      level + perturbed.totalVariationDistance reference ≤
          reference.cumulative cut := margin
      _ ≤ perturbed.totalVariationDistance reference +
          perturbed.cumulative cut := referenceLe
      _ = perturbed.cumulative cut +
          perturbed.totalVariationDistance reference := by
        rw [add_comm]
  exact Fraction.Order.Arithmetic.le_of_add_le_add_right_direct translated

/-- Exact total-variation margins bracket the perturbed lower quantile with a strict lower and weak upper endpoint. -/
theorem lowerQuantile_mem_bracket_of_totalVariation_margins
    (perturbed reference : Distribution Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1)
    (lower upper : Fraction.Rational)
    (lowerMargin : reference.cumulative lower +
      perturbed.totalVariationDistance reference < level)
    (upperMargin : level + perturbed.totalVariationDistance reference ≤
      reference.cumulative upper) :
    lower < perturbed.lowerQuantile level positive atMostOne ∧
      perturbed.lowerQuantile level positive atMostOne ≤ upper :=
  ⟨perturbed.cut_lt_lowerQuantile_of_cumulative_add_totalVariation_lt_level
      reference level positive atMostOne lower lowerMargin,
    perturbed.lowerQuantile_le_cut_of_level_add_totalVariation_le_cumulative
      reference level positive atMostOne upper upperMargin⟩

end Distribution

end Purelib.Measure

end
