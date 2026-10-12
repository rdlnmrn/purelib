module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Distribution.Cumulative.Support
import Purelib.Measure.SignedContent.Basic
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Distribution.TotalVariation.Support
public import Purelib.Measure.Distribution.Kolmogorov.Basic
import Purelib.Measure.Distribution.Kolmogorov.Atomic
public import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Measure.Distribution.Kolmogorov.Equivalence
import Purelib.Measure.Distribution.Consolidation
import Purelib.Measure.Distribution.Cumulative.TotalVariation
import Purelib.Data.List.Event
import Purelib.Measure.SignedContent.Variation.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Exact finite Kolmogorov distance

For two finite rational laws, cumulative probabilities can change only at
payloads displayed by one of the two atom tables.  A terminating search finds
the greatest displayed payload below any supplied rational cut.  Consequently
the maximum CDF discrepancy on the finite union of the two support tables
controls every rational cut; no supremum over the rational or real line is
formed.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib in
open Purelib.Data.List in
open Purelib.Data.Rat in
/-- Atomic L1 distance is bounded by the retained comparison-key count times twice the exact Kolmogorov distance. -/
theorem atomMassL1Distance_le_two_mul_supportCardinality_mulKolmogorovDistance
    (left right : Measure.Distribution Fraction.Rational) :
    left.atomMassL1Distance right ≤
      (left.comparisonSupportCardinality right : Fraction.Rational) *
        (2 * left.kolmogorovDistance right) := by
  have lengthEqual : (left.signedDifference right).atoms.length =
      left.comparisonSupportCardinality right := by
    unfold Distribution.signedDifference Content.signedDifference
      comparisonSupportCardinality
    exact Map.length_map _ _
  unfold atomMassL1Distance SignedContent.variationContent Content.total
  rw [← lengthEqual]
  change totalWeight ((left.signedDifference right).atoms.map
      SignedContent.variationAtom) ≤
    ((left.signedDifference right).atoms.length : Fraction.Rational) *
      (2 * left.kolmogorovDistance right)
  apply Measure.SignedContent.variationTotalWeight_le_length_mul_of_bounded
  intro atom member
  unfold Distribution.signedDifference Content.signedDifference at member
  rcases Map.mem_map.mp member with ⟨key, keyMember, equal⟩
  subst atom
  change Distance.rationalSeparation
      (left.atomMass key.item - right.atomMass key.item) 0 ≤
    2 * left.kolmogorovDistance right
  rw [← Distance.rationalSeparation_eq_sub_zero]
  exact left.atomMass_separation_le_two_mulKolmogorovDistance
    right key.item

open Purelib
open Purelib.Data.Rat
/-- Total variation distance is bounded by the retained comparison-key count times the exact Kolmogorov distance. -/
theorem totalVariationDistance_le_supportCardinality_mulKolmogorovDistance
    (left right : Measure.Distribution Fraction.Rational) :
    left.totalVariationDistance right ≤
      (left.comparisonSupportCardinality right : Fraction.Rational) *
        left.kolmogorovDistance right := by
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
  · calc
      left.totalVariationDistance right * 2 =
          2 * left.totalVariationDistance right := by ring1
      _ = left.atomMassL1Distance right :=
        (left.atomMassL1Distance_eq_two_mul_totalVariationDistance right).symm
      _ ≤ (left.comparisonSupportCardinality right : Fraction.Rational) *
          (2 * left.kolmogorovDistance right) :=
        left.atomMassL1Distance_le_two_mul_supportCardinality_mulKolmogorovDistance
          right
      _ = ((left.comparisonSupportCardinality right : Fraction.Rational) *
          left.kolmogorovDistance right) * 2 := by ring1
  · decide

/-- Exact finite Kolmogorov distance vanishes exactly when total variation distance vanishes. -/
theorem kolmogorovDistance_eq_zero_iff_totalVariationDistance_eq_zero
    (left right : Measure.Distribution Fraction.Rational) :
    left.kolmogorovDistance right = 0 ↔
      left.totalVariationDistance right = 0 := by
  exact (left.kolmogorovDistance_eq_zero_iff_evaluationEquivalent right).trans
    (left.totalVariationDistance_eq_zero_iff_evaluationEquivalent right).symm

/-- Exact finite Kolmogorov distance is at most total variation distance between the same original laws. -/
theorem kolmogorovDistance_le_totalVariationDistance
    (left right : Measure.Distribution Fraction.Rational) :
    left.kolmogorovDistance right ≤
      left.totalVariationDistance right :=
  left.cumulativeGridDistance_le_totalVariationDistance right
    (cumulativeSupportGrid left right)

/-- Exact finite Kolmogorov distance between two normalized rational laws is at most one. -/
theorem kolmogorovDistance_le_one
    (left right : Measure.Distribution Fraction.Rational) :
    left.kolmogorovDistance right ≤ 1 :=
  (left.kolmogorovDistance_le_totalVariationDistance right).trans
    (left.totalVariationDistance_le_one right)

end Distribution

end Purelib.Measure

end
