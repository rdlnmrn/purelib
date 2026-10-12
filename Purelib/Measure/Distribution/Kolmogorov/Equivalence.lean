module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Distribution.Content
import Purelib.Measure.Weighted.Consolidation
public import Purelib.Measure.Distribution.Kolmogorov.Basic
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Distribution.Kolmogorov.Atomic
import Purelib.Measure.Content.Histogram
import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Measure.Distribution.Consolidation
import Purelib.Measure.Content.Density.Witness
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Equivalence
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

section
open Purelib.Data.Rat
/-- Equality of all cumulative probabilities gives equal masses to every exact rational atom. -/
private theorem atomMass_eq_of_cumulative_eq
    (left right : Distribution Fraction.Rational)
    (cumulativeEqual : ∀ cut,
      left.cumulative cut = right.cumulative cut)
    (item : Fraction.Rational) :
    left.probability (atomEvent item) =
      right.probability (atomEvent item) := by
  have distanceZero : left.kolmogorovDistance right = 0 :=
    (left.kolmogorovDistance_eq_zero_iff right).2 cumulativeEqual
  apply (Distance.rationalSeparation_eq_zero_iff _ _).mp
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · calc
      Distance.rationalSeparation (left.probability (atomEvent item))
          (right.probability (atomEvent item)) =
        Distance.rationalSeparation (left.atomMass item) (right.atomMass item) := rfl
      _ ≤ 2 * left.kolmogorovDistance right :=
        left.atomMass_separation_le_two_mulKolmogorovDistance right item
      _ = 0 := by rw [distanceZero]; ring1
  · exact Distance.rationalSeparation_nonneg _ _

/-- Distributions with equal cumulative probabilities at every rational cut are evaluation-equivalent. -/
theorem evaluationEquivalent_of_cumulative_eq
    (left right : Distribution Fraction.Rational)
    (cumulativeEqual : ∀ cut,
      left.cumulative cut = right.cumulative cut) :
    EvaluationEquivalent left right := by
  have contentEquivalent : Content.EvaluationEquivalent
      left.toContent right.toContent :=
    Content.EvaluationEquivalent.of_atom_measure_eq fun item =>
      atomMass_eq_of_cumulative_eq left right cumulativeEqual item
  exact
    { probability_eq := contentEquivalent.measure_eq
      expectation_eq := contentEquivalent.integral_eq }

/-- Evaluation equivalence is exactly equality of all rational-cut cumulative probabilities. -/
theorem evaluationEquivalent_iff_cumulative_eq
    (left right : Distribution Fraction.Rational) :
    EvaluationEquivalent left right ↔
      ∀ cut, left.cumulative cut = right.cumulative cut := by
  constructor
  · intro equivalent cut
    exact equivalent.probability_eq (atMostEvent cut)
  · exact left.evaluationEquivalent_of_cumulative_eq right

/-- The exact finite Kolmogorov distance vanishes exactly when the two original distributions are evaluation-equivalent.
-/
theorem kolmogorovDistance_eq_zero_iff_evaluationEquivalent
    (left right : Distribution Fraction.Rational) :
    left.kolmogorovDistance right = 0 ↔
      EvaluationEquivalent left right := by
  exact (left.kolmogorovDistance_eq_zero_iff right).trans
    (left.evaluationEquivalent_iff_cumulative_eq right).symm

end

open Purelib.Data.Rat in
/-- Replacing each original distribution by an evaluation-equivalent law preserves their exact Kolmogorov distance. -/
theorem EvaluationEquivalent.kolmogorovDistance_eq
    {leftFirst leftSecond rightFirst rightSecond : Distribution Fraction.Rational}
    (leftEquivalent : EvaluationEquivalent leftFirst leftSecond)
    (rightEquivalent : EvaluationEquivalent rightFirst rightSecond) :
    leftFirst.kolmogorovDistance rightFirst =
      leftSecond.kolmogorovDistance rightSecond := by
  have leftCumulative : ∀ cut,
      leftFirst.cumulative cut = leftSecond.cumulative cut := fun cut =>
    leftEquivalent.probability_eq (atMostEvent cut)
  have rightCumulative : ∀ cut,
      rightFirst.cumulative cut = rightSecond.cumulative cut := fun cut =>
    rightEquivalent.probability_eq (atMostEvent cut)
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · apply leftFirst.kolmogorovDistance_le rightFirst
      (leftSecond.kolmogorovDistance rightSecond)
      (leftSecond.kolmogorovDistance_nonnegative rightSecond)
    intro cut
    rw [leftCumulative cut, rightCumulative cut]
    exact leftSecond.cumulative_separation_leKolmogorovDistance
      rightSecond cut
  · apply leftSecond.kolmogorovDistance_le rightSecond
      (leftFirst.kolmogorovDistance rightFirst)
      (leftFirst.kolmogorovDistance_nonnegative rightFirst)
    intro cut
    rw [← leftCumulative cut, ← rightCumulative cut]
    exact leftFirst.cumulative_separation_leKolmogorovDistance
      rightFirst cut
end Distribution

end Purelib.Measure

end
