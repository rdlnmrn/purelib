module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Distribution.Cumulative.Grid
public import Purelib.Measure.Distribution.Quantile.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Cumulative.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

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
/-- A strict lower cumulative margin places the perturbed law's exact lower quantile strictly above the supplied cut. -/
theorem cut_lt_lowerQuantile_of_cumulative_separation_lt
    (perturbed reference : Distribution Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1)
    (cut tolerance : Fraction.Rational)
    (close : Distance.rationalSeparation (perturbed.cumulative cut)
      (reference.cumulative cut) < tolerance)
    (margin : reference.cumulative cut + tolerance < level) :
    cut < perturbed.lowerQuantile level positive atMostOne := by
  apply Fraction.Order.Arithmetic.lt_of_not_ge_direct
  intro quantileLeCut
  have levelLePerturbed : level ≤ perturbed.cumulative cut :=
    (perturbed.lowerQuantile_le_iff_level_le_cumulative
      level positive atMostOne cut).1 quantileLeCut
  have differenceSmall :
      perturbed.cumulative cut - reference.cumulative cut < tolerance :=
    (Fraction.Order.Basic.le_max_left
      (perturbed.cumulative cut - reference.cumulative cut)
      (reference.cumulative cut - perturbed.cumulative cut)).trans_lt close
  have perturbedSmall : perturbed.cumulative cut <
      reference.cumulative cut + tolerance := by
    calc
      perturbed.cumulative cut =
          (perturbed.cumulative cut - reference.cumulative cut) +
            reference.cumulative cut := by ring1
      _ < tolerance + reference.cumulative cut :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct differenceSmall _
      _ = reference.cumulative cut + tolerance := by ring1
  exact (not_lt_of_ge levelLePerturbed) (perturbedSmall.trans margin)

/-- An upper cumulative margin places the perturbed law's exact lower quantile at or below the supplied cut. -/
theorem lowerQuantile_le_cut_of_cumulative_separation_lt
    (perturbed reference : Distribution Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1)
    (cut tolerance : Fraction.Rational)
    (close : Distance.rationalSeparation (perturbed.cumulative cut)
      (reference.cumulative cut) < tolerance)
    (margin : level + tolerance ≤ reference.cumulative cut) :
    perturbed.lowerQuantile level positive atMostOne ≤ cut := by
  apply (perturbed.lowerQuantile_le_iff_level_le_cumulative
    level positive atMostOne cut).2
  have differenceSmall :
      reference.cumulative cut - perturbed.cumulative cut < tolerance :=
    (Fraction.Order.Basic.le_max_right
      (perturbed.cumulative cut - reference.cumulative cut)
      (reference.cumulative cut - perturbed.cumulative cut)).trans_lt close
  have referenceSmall : reference.cumulative cut <
      perturbed.cumulative cut + tolerance := by
    calc
      reference.cumulative cut =
          (reference.cumulative cut - perturbed.cumulative cut) +
            perturbed.cumulative cut := by ring1
      _ < tolerance + perturbed.cumulative cut :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct differenceSmall _
      _ = perturbed.cumulative cut + tolerance := by ring1
  have shifted : level + tolerance <
      perturbed.cumulative cut + tolerance :=
    margin.trans_lt referenceSmall
  exact (Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct shifted).le

/-- Cumulative closeness and retained endpoint margins bracket the perturbed quantile with strict lower and weak upper
inequalities. -/
theorem lowerQuantile_mem_bracket_of_cumulative_separations_lt
    (perturbed reference : Distribution Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1)
    (lower upper tolerance : Fraction.Rational)
    (lowerClose : Distance.rationalSeparation (perturbed.cumulative lower)
      (reference.cumulative lower) < tolerance)
    (upperClose : Distance.rationalSeparation (perturbed.cumulative upper)
      (reference.cumulative upper) < tolerance)
    (lowerMargin : reference.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ reference.cumulative upper) :
    lower < perturbed.lowerQuantile level positive atMostOne ∧
      perturbed.lowerQuantile level positive atMostOne ≤ upper :=
  ⟨perturbed.cut_lt_lowerQuantile_of_cumulative_separation_lt reference
      level positive atMostOne lower tolerance lowerClose lowerMargin,
    perturbed.lowerQuantile_le_cut_of_cumulative_separation_lt reference
      level positive atMostOne upper tolerance upperClose upperMargin⟩

/-- A grid-distance bound and endpoint membership transfer the retained cumulative margins to the exact perturbed
quantile bracket. -/
theorem lowerQuantile_mem_bracket_of_cumulativeGridDistance_lt
    (perturbed reference : Distribution Fraction.Rational)
    (thresholds : List Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1)
    (lower upper tolerance : Fraction.Rational)
    (lowerMember : lower ∈ thresholds) (upperMember : upper ∈ thresholds)
    (gridClose : perturbed.cumulativeGridDistance reference thresholds <
      tolerance)
    (lowerMargin : reference.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ reference.cumulative upper) :
    lower < perturbed.lowerQuantile level positive atMostOne ∧
      perturbed.lowerQuantile level positive atMostOne ≤ upper := by
  apply perturbed.lowerQuantile_mem_bracket_of_cumulative_separations_lt
    reference level positive atMostOne lower upper tolerance
  · exact (perturbed.cumulative_separation_le_cumulativeGridDistance reference
      lower lowerMember).trans_lt gridClose
  · exact (perturbed.cumulative_separation_le_cumulativeGridDistance reference
      upper upperMember).trans_lt gridClose
  · exact lowerMargin
  · exact upperMargin

/-- Zero grid distance gives equal exact lower quantiles when both original quantile values belong to the retained grid.
-/
theorem lowerQuantile_eq_of_cumulativeGridDistance_eq_zero
    (left right : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (level : Fraction.Rational) (positive : 0 < level) (atMostOne : level ≤ 1)
    (leftMember : left.lowerQuantile level positive atMostOne ∈ thresholds)
    (rightMember : right.lowerQuantile level positive atMostOne ∈ thresholds)
    (distanceZero : left.cumulativeGridDistance right thresholds = 0) :
    left.lowerQuantile level positive atMostOne =
      right.lowerQuantile level positive atMostOne := by
  have cumulativeEqual :=
    (left.cumulativeGridDistance_eq_zero_iff right thresholds).1 distanceZero
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · apply (left.lowerQuantile_le_iff_level_le_cumulative
      level positive atMostOne
      (right.lowerQuantile level positive atMostOne)).2
    rw [cumulativeEqual _ rightMember]
    exact right.level_le_cumulative_lowerQuantile level positive atMostOne
  · apply (right.lowerQuantile_le_iff_level_le_cumulative
      level positive atMostOne
      (left.lowerQuantile level positive atMostOne)).2
    rw [← cumulativeEqual _ leftMember]
    exact left.level_le_cumulative_lowerQuantile level positive atMostOne
end Distribution

end Purelib.Measure

end
