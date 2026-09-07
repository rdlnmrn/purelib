import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Vitali
import FiniteMeasure.UniformIntegrability

/-!
# An L2 finite Vitali bridge

An in-measure certificate controls the probability of one threshold-error
event.  Cauchy--Schwarz controls the error integral on that event by its
powered-L2 size.  To remain rational and executable, the conclusion squares
the nonnegative L1 excess instead of introducing a square root.
-/

namespace FiniteMeasure

theorem rationalSeparation_sq_eq_sub_sq (left right : Coordinate) :
    rationalSeparation left right ^ 2 = (left - right) ^ 2 := by
  have same : rationalSeparation left right =
      rationalSeparation (left - right) 0 := by
    unfold rationalSeparation
    congr 1 <;> ring1
  rw [same, rationalSeparation_zero_sq]

namespace Distribution

namespace InMeasureBudget

/-- Nonnegative part of the exact L1 error above the budget's pointwise
threshold. -/
def l1Excess {α : Type} {distribution : Distribution α}
    {left right : α → Coordinate}
    (budget : InMeasureBudget distribution left right) : Coordinate :=
  max (distribution.l1Distance left right - budget.threshold) 0

theorem l1Excess_nonnegative {α : Type}
    {distribution : Distribution α} {left right : α → Coordinate}
    (budget : InMeasureBudget distribution left right) :
    0 ≤ budget.l1Excess :=
  le_max_right _ _

/-- Rational L2-Vitali estimate. -/
theorem l1Excess_sq_le_poweredL2Distance_mul_failure {α : Type}
    {distribution : Distribution α} {left right : α → Coordinate}
    (budget : InMeasureBudget distribution left right) :
    budget.l1Excess ^ 2 ≤
      distribution.poweredL2Distance left right * budget.failure := by
  let bad := separationAtLeast budget.threshold left right
  let tailError : α → Coordinate := fun item =>
    rationalSeparation (left item) (right item) * indicator bad item
  have tailErrorNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ tailError atom.item := by
    intro atom atomMember
    apply RFAP.ConstructiveFraction.mul_nonneg_direct
    · exact rationalSeparation_nonneg _ _
    · cases selected : bad atom.item <;>
        simp only [indicator, selected] <;> decide
  have pointwiseSplit : ∀ atom, atom ∈ distribution.atoms →
      rationalSeparation (left atom.item) (right atom.item) ≤
        budget.threshold + tailError atom.item := by
    intro atom atomMember
    cases selected : bad atom.item
    · have notThreshold : ¬budget.threshold ≤
          rationalSeparation (left atom.item) (right atom.item) := by
        unfold bad separationAtLeast at selected
        exact decide_eq_false_iff_not.mp selected
      have below := RFAP.ConstructiveFraction.lt_of_not_ge_direct notThreshold
      simp only [tailError, indicator, selected, mul_zero, add_zero]
      exact RFAP.ConstructiveFraction.le_of_lt_direct below
    · simp only [tailError, indicator, selected, mul_one]
      exact le_add_of_nonneg_left budget.threshold_positive.le
  have splitAveraged := distribution.expectation_mono
    (fun item => rationalSeparation (left item) (right item))
    (fun item => budget.threshold + tailError item) pointwiseSplit
  rw [distribution.expectation_add, distribution.expectation_constant]
    at splitAveraged
  have differenceLeTail :
      distribution.l1Distance left right - budget.threshold ≤
        distribution.expectation tailError := by
    change distribution.expectation (fun item =>
      rationalSeparation (left item) (right item)) - budget.threshold ≤
        distribution.expectation tailError
    have shifted := RFAP.ConstructiveFraction.sub_le_sub_right_direct
      splitAveraged budget.threshold
    simpa only [add_sub_cancel_left] using shifted
  have tailExpectationNonnegative :
      0 ≤ distribution.expectation tailError :=
    distribution.expectation_nonneg tailError tailErrorNonnegative
  have excessLeTail : budget.l1Excess ≤
      distribution.expectation tailError := by
    unfold l1Excess
    exact max_le differenceLeTail tailExpectationNonnegative
  have excessSqLeTailSq : budget.l1Excess ^ 2 ≤
      distribution.expectation tailError ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      budget.l1Excess_nonnegative excessLeTail 2
  have cauchy := distribution.productExpectation_sq_le_poweredL2_mul
    (fun item => rationalSeparation (left item) (right item))
    (indicator bad)
  have productSame : (fun item =>
      rationalSeparation (left item) (right item) * indicator bad item) =
      tailError := rfl
  rw [productSame] at cauchy
  have errorL2 : distribution.poweredL2
      (fun item => rationalSeparation (left item) (right item)) =
      distribution.poweredL2Distance left right := by
    unfold poweredL2 poweredL2Distance FiniteContent.poweredL2Distance
      FiniteContent.poweredL2
    exact distribution.toFiniteContent.integral_congr _ _ (fun item =>
      rationalSeparation_sq_eq_sub_sq (left item) (right item))
  have indicatorL2 : distribution.poweredL2 (indicator bad) =
      distribution.probability bad := by
    calc
      distribution.poweredL2 (indicator bad) =
          distribution.expectation (fun item => indicator bad item ^ 2) :=
        rfl
      _ = distribution.expectation (indicator bad) := by
        exact distribution.expectation_congr _ _ (fun item => by
          cases selected : bad item <;>
            simp only [indicator, selected] <;> ring1)
      _ = distribution.probability bad :=
        distribution.expectation_indicator bad
  rw [errorL2, indicatorL2] at cauchy
  have distanceNonnegative :=
    distribution.toFiniteContent.poweredL2Distance_nonnegative left right
  calc
    budget.l1Excess ^ 2 ≤ distribution.expectation tailError ^ 2 :=
      excessSqLeTailSq
    _ ≤ distribution.poweredL2Distance left right *
        distribution.probability bad := cauchy
    _ ≤ distribution.poweredL2Distance left right * budget.failure :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        budget.probability_le distanceNonnegative

end InMeasureBudget

/-- An in-measure certificate plus a displayed powered-L2 error ceiling. -/
structure L2InMeasureBudget {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) where
  inMeasure : InMeasureBudget distribution left right
  ceiling : Coordinate
  ceiling_nonnegative : 0 ≤ ceiling
  poweredL2Distance_le : distribution.poweredL2Distance left right ≤ ceiling

namespace L2InMeasureBudget

/-- Ceiling form of the rational L2-Vitali estimate. -/
theorem l1Excess_sq_le {α : Type} {distribution : Distribution α}
    {left right : α → Coordinate}
    (budget : L2InMeasureBudget distribution left right) :
    budget.inMeasure.l1Excess ^ 2 ≤
      budget.ceiling * budget.inMeasure.failure := by
  calc
    budget.inMeasure.l1Excess ^ 2 ≤
        distribution.poweredL2Distance left right *
          budget.inMeasure.failure :=
      budget.inMeasure.l1Excess_sq_le_poweredL2Distance_mul_failure
    _ ≤ budget.ceiling * budget.inMeasure.failure :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        budget.poweredL2Distance_le budget.inMeasure.failure_nonnegative

end L2InMeasureBudget

end Distribution

end FiniteMeasure
