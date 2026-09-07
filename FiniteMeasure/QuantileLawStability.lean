import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.FiniteKolmogorov
import FiniteMeasure.QuantileStability

/-!
# Quantile stability under finite law perturbations

Quantiles need not be Lipschitz under small changes of law: an atom near the
quantile level can move the selected cut discontinuously.  The constructive
finite replacement is an explicit CDF-margin theorem.  Total variation is
computed exactly, and a displayed lower/upper pair brackets the perturbed
quantile whenever the reference cumulative law crosses the requested level
with that margin.
-/

namespace FiniteMeasure

namespace Distribution

/-- A strict cumulative comparison at one lower cut is enough to place a
perturbed lower quantile above that cut.  The comparison budget need not be
global total variation; it may come from any finite computation of this one
cumulative probability. -/
theorem cut_lt_lowerQuantile_of_cumulative_separation_lt
    (perturbed reference : Distribution Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1)
    (cut tolerance : Coordinate)
    (close : rationalSeparation (perturbed.cumulative cut)
      (reference.cumulative cut) < tolerance)
    (margin : reference.cumulative cut + tolerance < level) :
    cut < perturbed.lowerQuantile level positive atMostOne := by
  apply RFAP.ConstructiveFraction.lt_of_not_ge_direct
  intro quantileLeCut
  have levelLePerturbed : level ≤ perturbed.cumulative cut :=
    (perturbed.lowerQuantile_le_iff_level_le_cumulative
      level positive atMostOne cut).1 quantileLeCut
  have differenceSmall :
      perturbed.cumulative cut - reference.cumulative cut < tolerance :=
    (le_max_left
      (perturbed.cumulative cut - reference.cumulative cut)
      (reference.cumulative cut - perturbed.cumulative cut)).trans_lt close
  have perturbedSmall : perturbed.cumulative cut <
      reference.cumulative cut + tolerance := by
    calc
      perturbed.cumulative cut =
          (perturbed.cumulative cut - reference.cumulative cut) +
            reference.cumulative cut := by ring1
      _ < tolerance + reference.cumulative cut :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct differenceSmall _
      _ = reference.cumulative cut + tolerance := by ring1
  exact (not_lt_of_ge levelLePerturbed) (perturbedSmall.trans margin)

/-- A strict cumulative comparison at one upper cut is enough to place a
perturbed lower quantile at or below that cut. -/
theorem lowerQuantile_le_cut_of_cumulative_separation_lt
    (perturbed reference : Distribution Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1)
    (cut tolerance : Coordinate)
    (close : rationalSeparation (perturbed.cumulative cut)
      (reference.cumulative cut) < tolerance)
    (margin : level + tolerance ≤ reference.cumulative cut) :
    perturbed.lowerQuantile level positive atMostOne ≤ cut := by
  apply (perturbed.lowerQuantile_le_iff_level_le_cumulative
    level positive atMostOne cut).2
  have differenceSmall :
      reference.cumulative cut - perturbed.cumulative cut < tolerance :=
    (le_max_right
      (perturbed.cumulative cut - reference.cumulative cut)
      (reference.cumulative cut - perturbed.cumulative cut)).trans_lt close
  have referenceSmall : reference.cumulative cut <
      perturbed.cumulative cut + tolerance := by
    calc
      reference.cumulative cut =
          (reference.cumulative cut - perturbed.cumulative cut) +
            perturbed.cumulative cut := by ring1
      _ < tolerance + perturbed.cumulative cut :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct differenceSmall _
      _ = perturbed.cumulative cut + tolerance := by ring1
  have shifted : level + tolerance <
      perturbed.cumulative cut + tolerance :=
    margin.trans_lt referenceSmall
  exact (RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct shifted).le

/-- Two displayed pointwise cumulative comparisons and two reference-law
margins give a fully finite confidence bracket for a lower quantile. -/
theorem lowerQuantile_mem_bracket_of_cumulative_separations_lt
    (perturbed reference : Distribution Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1)
    (lower upper tolerance : Coordinate)
    (lowerClose : rationalSeparation (perturbed.cumulative lower)
      (reference.cumulative lower) < tolerance)
    (upperClose : rationalSeparation (perturbed.cumulative upper)
      (reference.cumulative upper) < tolerance)
    (lowerMargin : reference.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ reference.cumulative upper) :
    lower < perturbed.lowerQuantile level positive atMostOne ∧
      perturbed.lowerQuantile level positive atMostOne ≤ upper :=
  ⟨perturbed.cut_lt_lowerQuantile_of_cumulative_separation_lt reference
      level positive atMostOne lower tolerance lowerClose lowerMargin,
    perturbed.lowerQuantile_le_cut_of_cumulative_separation_lt reference
      level positive atMostOne upper tolerance upperClose upperMargin⟩

/-- A strict bound on the computed displayed-grid CDF distance supplies both
pointwise comparisons needed for a robust lower-quantile bracket. -/
theorem lowerQuantile_mem_bracket_of_cumulativeGridDistance_lt
    (perturbed reference : Distribution Coordinate)
    (thresholds : List Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1)
    (lower upper tolerance : Coordinate)
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

/-- A strict global finite Kolmogorov bound supplies the two CDF comparisons
needed for a robust lower-quantile bracket.  No threshold grid has to be
carried by the caller because the distance already computes the finite union
of both support tables. -/
theorem lowerQuantile_mem_bracket_of_finiteKolmogorovDistance_lt
    (perturbed reference : Distribution Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1)
    (lower upper tolerance : Coordinate)
    (distanceSmall : perturbed.finiteKolmogorovDistance reference < tolerance)
    (lowerMargin : reference.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ reference.cumulative upper) :
    lower < perturbed.lowerQuantile level positive atMostOne ∧
      perturbed.lowerQuantile level positive atMostOne ≤ upper := by
  apply perturbed.lowerQuantile_mem_bracket_of_cumulative_separations_lt
    reference level positive atMostOne lower upper tolerance
  · exact (perturbed.cumulative_separation_le_finiteKolmogorovDistance
      reference lower).trans_lt distanceSmall
  · exact (perturbed.cumulative_separation_le_finiteKolmogorovDistance
      reference upper).trans_lt distanceSmall
  · exact lowerMargin
  · exact upperMargin

/-- Zero global finite Kolmogorov distance forces equality of every
executable lower quantile. -/
theorem lowerQuantile_eq_of_finiteKolmogorovDistance_eq_zero
    (left right : Distribution Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1)
    (distanceZero : left.finiteKolmogorovDistance right = 0) :
    left.lowerQuantile level positive atMostOne =
      right.lowerQuantile level positive atMostOne := by
  have cumulativeEqual :=
    (left.finiteKolmogorovDistance_eq_zero_iff right).1 distanceZero
  apply RFAP.ConstructiveFraction.le_antisymm
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

/-- In particular, zero global finite Kolmogorov distance forces equality of
the two executable lower medians. -/
theorem median_eq_of_finiteKolmogorovDistance_eq_zero
    (left right : Distribution Coordinate)
    (distanceZero : left.finiteKolmogorovDistance right = 0) :
    left.median = right.median :=
  left.lowerQuantile_eq_of_finiteKolmogorovDistance_eq_zero right
    (1 / 2) (by decide) (by decide) distanceZero

/-- If a displayed grid contains both selected lower-quantile values and the
two finite laws have zero CDF distance on that grid, then those executable
quantiles are equal. -/
theorem lowerQuantile_eq_of_cumulativeGridDistance_eq_zero
    (left right : Distribution Coordinate) (thresholds : List Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1)
    (leftMember : left.lowerQuantile level positive atMostOne ∈ thresholds)
    (rightMember : right.lowerQuantile level positive atMostOne ∈ thresholds)
    (distanceZero : left.cumulativeGridDistance right thresholds = 0) :
    left.lowerQuantile level positive atMostOne =
      right.lowerQuantile level positive atMostOne := by
  have cumulativeEqual :=
    (left.cumulativeGridDistance_eq_zero_iff right thresholds).1 distanceZero
  apply RFAP.ConstructiveFraction.le_antisymm
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

/-- If the reference cumulative mass at a lower cut remains below the level
after adding the total-variation budget, then the perturbed lower quantile is
strictly above that cut. -/
theorem cut_lt_lowerQuantile_of_cumulative_add_totalVariation_lt_level
    (perturbed reference : Distribution Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1)
    (cut : Coordinate)
    (margin : reference.cumulative cut +
      perturbed.totalVariationDistance reference < level) :
    cut < perturbed.lowerQuantile level positive atMostOne := by
  apply RFAP.ConstructiveFraction.lt_of_not_ge_direct
  intro quantileLeCut
  have levelLePerturbed : level ≤ perturbed.cumulative cut :=
    ((perturbed.lowerQuantile_le_iff_level_le_cumulative
      level positive atMostOne cut).1 quantileLeCut)
  have cumulativeDifference :
      perturbed.cumulative cut - reference.cumulative cut ≤
        perturbed.totalVariationDistance reference :=
    (le_max_left
      (perturbed.cumulative cut - reference.cumulative cut)
      (reference.cumulative cut - perturbed.cumulative cut)).trans
      (perturbed.cumulative_separation_le_totalVariationDistance
        reference cut)
  have perturbedLe : perturbed.cumulative cut ≤
      reference.cumulative cut +
        perturbed.totalVariationDistance reference := by
    have shifted := (sub_le_iff_le_add).1 cumulativeDifference
    simpa only [add_comm] using shifted
  exact (not_le_of_gt margin) (levelLePerturbed.trans perturbedLe)

/-- If the reference cumulative mass at an upper cut exceeds the level by
the total-variation budget, then the perturbed lower quantile is at most that
cut. -/
theorem lowerQuantile_le_cut_of_level_add_totalVariation_le_cumulative
    (perturbed reference : Distribution Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1)
    (cut : Coordinate)
    (margin : level + perturbed.totalVariationDistance reference ≤
      reference.cumulative cut) :
    perturbed.lowerQuantile level positive atMostOne ≤ cut := by
  apply (perturbed.lowerQuantile_le_iff_level_le_cumulative
    level positive atMostOne cut).2
  have cumulativeDifference :
      reference.cumulative cut - perturbed.cumulative cut ≤
        perturbed.totalVariationDistance reference :=
    (le_max_right
      (perturbed.cumulative cut - reference.cumulative cut)
      (reference.cumulative cut - perturbed.cumulative cut)).trans
      (perturbed.cumulative_separation_le_totalVariationDistance
        reference cut)
  have referenceLe : reference.cumulative cut ≤
      perturbed.totalVariationDistance reference +
        perturbed.cumulative cut :=
    (sub_le_iff_le_add).1 cumulativeDifference
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
  exact RFAP.ConstructiveFraction.le_of_add_le_add_right_direct translated

/-- A displayed reference-CDF margin gives a two-sided bracket for the lower
quantile of a perturbed finite rational law. -/
theorem lowerQuantile_mem_bracket_of_totalVariation_margins
    (perturbed reference : Distribution Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1)
    (lower upper : Coordinate)
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

end FiniteMeasure
