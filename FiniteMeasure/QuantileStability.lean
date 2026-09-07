import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.EnclosureObservation
import FiniteMeasure.DistributionEquivalence
import FiniteMeasure.Quantile

/-!
# Uniform stability of constructive finite quantiles

Finite lower quantiles are stable under a displayed uniform rational
perturbation of the source observable.  The proof compares the two executable
cumulative events atom by atom and applies the exact finite generalized-inverse
law.  No infimum, limiting distribution, or completed metric space occurs.
-/

namespace FiniteMeasure

namespace Distribution

/-- Uniform pointwise rational separation shifts the cumulative probability
of a finite pushforward by at most the same rational radius. -/
theorem map_cumulative_le_add_of_rationalSeparation_le {α : Type}
    (source : Distribution α) (left right : α → Coordinate)
    (radius cut : Coordinate)
    (close : ∀ atom, atom ∈ source.atoms →
      rationalSeparation (left atom.item) (right atom.item) ≤ radius) :
    (source.map left).cumulative cut ≤
      (source.map right).cumulative (cut + radius) := by
  unfold cumulative
  rw [source.map_probability, source.map_probability]
  apply eventWeight_mono
  intro atom member selected
  have leftLeCut : left atom.item ≤ cut := of_decide_eq_true selected
  have rightMinusLeft : right atom.item - left atom.item ≤ radius :=
    (le_max_right (left atom.item - right atom.item)
      (right atom.item - left atom.item)).trans (close atom member)
  have rightLeRadiusAddLeft :
      right atom.item ≤ radius + left atom.item :=
    (sub_le_iff_le_add).1 rightMinusLeft
  apply decide_eq_true_eq.mpr
  calc
    right atom.item ≤ radius + left atom.item := rightLeRadiusAddLeft
    _ ≤ radius + cut :=
      RFAP.ConstructiveFraction.add_le_add_direct le_rfl leftLeCut
    _ = cut + radius := by ring1

/-- Generalized-inverse characterization stated directly for the executable
lower-quantile value. -/
theorem lowerQuantile_le_iff_level_le_cumulative
    (distribution : Distribution Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1)
    (cut : Coordinate) :
    distribution.lowerQuantile level positive atMostOne ≤ cut ↔
      level ≤ distribution.cumulative cut :=
  (distribution.quantileCertificate level positive atMostOne)
    |>.threshold_le_iff_level_le_cumulative cut

/-- A finite rational support gap turns a displayed CDF crossing into an
exact lower-quantile value.  No infimum or order completeness is used: the
selected quantile has an explicit positive-weight atom witness. -/
theorem lowerQuantile_eq_of_atom_gap_crossing
    (distribution : Distribution Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1)
    (lower value : Coordinate)
    (gap : ∀ atom, atom ∈ distribution.atoms →
      atom.item ≤ lower ∨ value ≤ atom.item)
    (belowLevel : distribution.cumulative lower < level)
    (levelAtValue : level ≤ distribution.cumulative value) :
    distribution.lowerQuantile level positive atMostOne = value := by
  have quantileLeValue :
      distribution.lowerQuantile level positive atMostOne ≤ value :=
    (distribution.lowerQuantile_le_iff_level_le_cumulative
      level positive atMostOne value).2 levelAtValue
  have lowerLtQuantile : lower <
      distribution.lowerQuantile level positive atMostOne := by
    apply RFAP.ConstructiveFraction.lt_of_not_ge_direct
    intro quantileLeLower
    have levelLeLower :=
      (distribution.lowerQuantile_le_iff_level_le_cumulative
        level positive atMostOne lower).1 quantileLeLower
    exact (not_le_of_gt belowLevel) levelLeLower
  rcases distribution.lowerQuantile_eq_positiveAtom_of_mem
      level positive atMostOne with
    ⟨atom, member, _weightPositive, valueEqual⟩
  have valueLeQuantile : value ≤
      distribution.lowerQuantile level positive atMostOne := by
    rcases gap atom member with atomLow | atomHigh
    · rw [valueEqual] at atomLow
      exact (not_le_of_gt lowerLtQuantile atomLow).elim
    · simpa only [valueEqual] using atomHigh
  exact RFAP.ConstructiveFraction.le_antisymm _ _ quantileLeValue
    valueLeQuantile

namespace EvaluationEquivalent

/-- Evaluation-equivalent rational laws have identical exact cumulative
probabilities at every supplied rational cut. -/
theorem cumulative_eq
    {left right : Distribution Coordinate}
    (equivalent : EvaluationEquivalent left right)
    (cut : Coordinate) :
    left.cumulative cut = right.cumulative cut :=
  equivalent.probability_eq (atMostEvent cut)

/-- Constructive lower quantiles depend only on the exact finite law, not on
the ordering, duplication, or layout of its displayed atom table. -/
theorem lowerQuantile_eq
    {left right : Distribution Coordinate}
    (equivalent : EvaluationEquivalent left right)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1) :
    left.lowerQuantile level positive atMostOne =
      right.lowerQuantile level positive atMostOne := by
  apply RFAP.ConstructiveFraction.le_antisymm
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

/-- Executable lower medians are invariant under evaluation equivalence. -/
theorem median_eq
    {left right : Distribution Coordinate}
    (equivalent : EvaluationEquivalent left right) :
    left.median = right.median := by
  simpa only [median] using
    equivalent.lowerQuantile_eq (1 / 2) (by decide) (by decide)

end EvaluationEquivalent

/-- The same finite weighted source evaluated by two uniformly close rational
observables has lower quantiles separated by at most that uniform radius. -/
theorem map_lowerQuantile_rationalSeparation_le {α : Type}
    (source : Distribution α) (left right : α → Coordinate)
    (radius : Coordinate)
    (close : ∀ atom, atom ∈ source.atoms →
      rationalSeparation (left atom.item) (right atom.item) ≤ radius)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1) :
    rationalSeparation
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
      rationalSeparation (right atom.item) (left atom.item) ≤ radius := by
    intro atom member
    rw [rationalSeparation_symm]
    exact close atom member
  have leftLe : leftQuantile ≤ rightQuantile + radius := by
    apply ((source.map left).lowerQuantile_le_iff_level_le_cumulative
      level positive atMostOne (rightQuantile + radius)).2
    exact ((source.map right).level_le_cumulative_lowerQuantile
      level positive atMostOne).trans
        (source.map_cumulative_le_add_of_rationalSeparation_le
          right left radius rightQuantile reverseClose)
  unfold rationalSeparation
  apply max_le
  · apply (sub_le_iff_le_add).2
    calc
      leftQuantile ≤ rightQuantile + radius := leftLe
      _ = radius + rightQuantile := by ring1
  · apply (sub_le_iff_le_add).2
    calc
      rightQuantile ≤ leftQuantile + radius := rightLe
      _ = radius + leftQuantile := by ring1

/-- Uniformly close rational observables on one finite weighted source have
executable lower medians within the same rational radius. -/
theorem map_median_rationalSeparation_le {α : Type}
    (source : Distribution α) (left right : α → Coordinate)
    (radius : Coordinate)
    (close : ∀ atom, atom ∈ source.atoms →
      rationalSeparation (left atom.item) (right atom.item) ≤ radius) :
    rationalSeparation (source.map left).median (source.map right).median ≤
      radius := by
  simpa only [median] using
    source.map_lowerQuantile_rationalSeparation_le left right radius close
      (1 / 2) (by decide) (by decide)

end Distribution

end FiniteMeasure
