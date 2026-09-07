import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.ConvergenceModes

/-!
# A finite bounded-convergence/Vitali bridge

Convergence in measure alone does not control L1 error.  If one finite
in-measure certificate is accompanied by a displayed uniform error ceiling,
the exceptional mass can be charged explicitly.  The resulting rational
bound is the finite quantitative content of the bounded Vitali argument:

`L1 error ≤ threshold + (ceiling - threshold) * failure`.

No sequence, limiting assertion, or uniform-integrability quantifier is
introduced.
-/

namespace FiniteMeasure

namespace Distribution

/-- One in-measure certificate together with an explicit uniform ceiling on
the pointwise error over the displayed atom table. -/
structure BoundedInMeasureBudget {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) where
  inMeasure : InMeasureBudget distribution left right
  ceiling : Coordinate
  threshold_le_ceiling : inMeasure.threshold ≤ ceiling
  error_le : ∀ atom, atom ∈ distribution.atoms →
    rationalSeparation (left atom.item) (right atom.item) ≤ ceiling

namespace BoundedInMeasureBudget

/-- Explicit finite L1 budget obtained by charging the unresolved event. -/
def l1Bound {α : Type} {distribution : Distribution α}
    {left right : α → Coordinate}
    (budget : BoundedInMeasureBudget distribution left right) : Coordinate :=
  budget.inMeasure.threshold +
    (budget.ceiling - budget.inMeasure.threshold) * budget.inMeasure.failure

theorem l1Bound_nonnegative {α : Type}
    {distribution : Distribution α} {left right : α → Coordinate}
    (budget : BoundedInMeasureBudget distribution left right) :
    0 ≤ budget.l1Bound := by
  apply add_nonneg budget.inMeasure.threshold_positive.le
  exact RFAP.ConstructiveFraction.mul_nonneg_direct
    (RFAP.ConstructiveFraction.sub_nonneg_direct
      budget.threshold_le_ceiling)
    budget.inMeasure.failure_nonnegative

/-- Quantitative finite Vitali estimate. -/
theorem l1Distance_le {α : Type}
    {distribution : Distribution α} {left right : α → Coordinate}
    (budget : BoundedInMeasureBudget distribution left right) :
    distribution.l1Distance left right ≤ budget.l1Bound := by
  let event := separationAtLeast budget.inMeasure.threshold left right
  let extra := budget.ceiling - budget.inMeasure.threshold
  let allowance : α → Coordinate := fun item =>
    budget.inMeasure.threshold + extra * indicator event item
  have extraNonnegative : 0 ≤ extra :=
    RFAP.ConstructiveFraction.sub_nonneg_direct
      budget.threshold_le_ceiling
  have pointwise : ∀ atom, atom ∈ distribution.atoms →
      rationalSeparation (left atom.item) (right atom.item) ≤
        allowance atom.item := by
    intro atom atomMember
    cases selected : event atom.item
    · have notThreshold : ¬budget.inMeasure.threshold ≤
          rationalSeparation (left atom.item) (right atom.item) := by
        unfold event separationAtLeast at selected
        exact decide_eq_false_iff_not.mp selected
      have below :=
        RFAP.ConstructiveFraction.lt_of_not_ge_direct notThreshold
      simp only [allowance, indicator, selected, mul_zero, add_zero]
      exact RFAP.ConstructiveFraction.le_of_lt_direct below
    · simp only [allowance, indicator, selected, mul_one]
      calc
        rationalSeparation (left atom.item) (right atom.item) ≤
            budget.ceiling := budget.error_le atom atomMember
        _ = budget.inMeasure.threshold + extra := by
          dsimp only [extra]
          ring1
  have averaged := distribution.expectation_mono
    (fun item => rationalSeparation (left item) (right item))
    allowance pointwise
  have allowanceExpectation : distribution.expectation allowance =
      budget.inMeasure.threshold + extra * distribution.probability event := by
    calc
      distribution.expectation allowance =
          distribution.expectation
              (fun _ => budget.inMeasure.threshold) +
            distribution.expectation
              (fun item => extra * indicator event item) :=
        distribution.expectation_add _ _
      _ = budget.inMeasure.threshold +
          extra * distribution.probability event := by
        rw [distribution.expectation_constant,
          distribution.expectation_scale,
          distribution.expectation_indicator]
  calc
    distribution.l1Distance left right ≤
        distribution.expectation allowance := averaged
    _ = budget.inMeasure.threshold +
        extra * distribution.probability event := allowanceExpectation
    _ ≤ budget.inMeasure.threshold +
        extra * budget.inMeasure.failure :=
      RFAP.ConstructiveFraction.add_le_add_direct le_rfl
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          budget.inMeasure.probability_le extraNonnegative)
    _ = budget.l1Bound := rfl

/-- A displayed L1 budget below a requested tolerance supplies the finite
bounded-convergence conclusion. -/
theorem accurate {α : Type} {distribution : Distribution α}
    {left right : α → Coordinate}
    (budget : BoundedInMeasureBudget distribution left right)
    (epsilon : Coordinate) (small : budget.l1Bound < epsilon) :
    distribution.l1Distance left right < epsilon :=
  budget.l1Distance_le.trans_lt small

end BoundedInMeasureBudget

end Distribution

end FiniteMeasure
