import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.PoweredLp

/-!
# Finite uniform-integrability tail budgets

The absolute tail of one rational observable is an executable threshold event
and an exact rational integral.  A second-moment bound controls this tail by
`poweredL2 / threshold`.  A displayed finite family with one common
second-moment ceiling therefore has one uniform rational tail budget.

This retains the quantitative finite content used in uniform-integrability
arguments without quantifying over an infinite family or taking a limit as
the threshold tends to infinity.
-/

namespace FiniteMeasure

theorem rationalSeparation_zero_sq (value : Coordinate) :
    rationalSeparation value 0 ^ 2 = value ^ 2 := by
  have multiplicative := rationalSeparation_mul_zero value value
  have squareNonnegative : 0 ≤ value * value := by
    simpa only [pow_two] using
      RFAP.ConstructiveFraction.sq_nonneg_direct value
  rw [rationalSeparation_zero_of_nonneg squareNonnegative] at multiplicative
  simpa only [pow_two] using multiplicative.symm

namespace Distribution

/-- Executable event on which the absolute rational value reaches a displayed
positive threshold. -/
def absoluteTailEvent {α : Type} (threshold : Coordinate)
    (value : α → Coordinate) : α → Bool :=
  fun item => decide (threshold ≤ rationalSeparation (value item) 0)

/-- Exact L1 mass retained on the displayed absolute tail. -/
def absoluteTailIntegral {α : Type} (distribution : Distribution α)
    (threshold : Coordinate) (value : α → Coordinate) : Coordinate :=
  distribution.expectation fun item =>
    rationalSeparation (value item) 0 *
      indicator (absoluteTailEvent threshold value) item

theorem absoluteTailIntegral_nonnegative {α : Type}
    (distribution : Distribution α) (threshold : Coordinate)
    (value : α → Coordinate) :
    0 ≤ distribution.absoluteTailIntegral threshold value := by
  apply distribution.expectation_nonneg
  intro atom atomMember
  apply RFAP.ConstructiveFraction.mul_nonneg_direct
  · exact rationalSeparation_nonneg _ _
  · cases selected : absoluteTailEvent threshold value atom.item <;>
      simp only [indicator, selected] <;> decide

/-- Multiplicative L2 tail estimate. -/
theorem threshold_mul_absoluteTailIntegral_le_poweredL2 {α : Type}
    (distribution : Distribution α) (threshold : Coordinate)
    (value : α → Coordinate) :
    threshold * distribution.absoluteTailIntegral threshold value ≤
      distribution.poweredL2 value := by
  let tailValue : α → Coordinate := fun item =>
    rationalSeparation (value item) 0 *
      indicator (absoluteTailEvent threshold value) item
  have pointwise : ∀ atom, atom ∈ distribution.atoms →
      threshold * tailValue atom.item ≤ value atom.item ^ 2 := by
    intro atom atomMember
    cases selected : absoluteTailEvent threshold value atom.item
    · simp only [tailValue, indicator, selected, mul_zero, mul_zero]
      exact RFAP.ConstructiveFraction.sq_nonneg_direct (value atom.item)
    · have thresholdLe : threshold ≤
          rationalSeparation (value atom.item) 0 := by
        unfold absoluteTailEvent at selected
        exact of_decide_eq_true selected
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          thresholdLe (rationalSeparation_nonneg (value atom.item) 0)
      simp only [tailValue, indicator, selected, mul_one]
      calc
        threshold * rationalSeparation (value atom.item) 0 ≤
            rationalSeparation (value atom.item) 0 *
              rationalSeparation (value atom.item) 0 := scaled
        _ = value atom.item ^ 2 := by
          rw [← pow_two, rationalSeparation_zero_sq]
  have averaged := distribution.expectation_mono
    (fun item => threshold * tailValue item)
    (fun item => value item ^ 2) pointwise
  rw [distribution.expectation_scale] at averaged
  change threshold * distribution.absoluteTailIntegral threshold value ≤
    distribution.poweredL2 value at averaged
  exact averaged

/-- Divided L2 tail estimate. -/
theorem absoluteTailIntegral_le_poweredL2_div {α : Type}
    (distribution : Distribution α) (threshold : Coordinate)
    (positive : 0 < threshold) (value : α → Coordinate) :
    distribution.absoluteTailIntegral threshold value ≤
      distribution.poweredL2 value / threshold := by
  apply (RFAP.ConstructiveFraction.le_div_iff_pos positive).2
  calc
    distribution.absoluteTailIntegral threshold value * threshold =
        threshold * distribution.absoluteTailIntegral threshold value := by
      ring1
    _ ≤ distribution.poweredL2 value :=
      distribution.threshold_mul_absoluteTailIntegral_le_poweredL2
        threshold value

/-- A displayed finite observable family with one common second-moment
ceiling. -/
structure L2FamilyBudget {α : Type} (distribution : Distribution α)
    (values : List (α → Coordinate)) where
  ceiling : Coordinate
  ceiling_nonnegative : 0 ≤ ceiling
  poweredL2_le : ∀ value, value ∈ values →
    distribution.poweredL2 value ≤ ceiling

namespace L2FamilyBudget

/-- One rational tail bound works uniformly for every member of the displayed
finite family. -/
theorem absoluteTailIntegral_le {α : Type}
    {distribution : Distribution α} {values : List (α → Coordinate)}
    (budget : L2FamilyBudget distribution values)
    (value : α → Coordinate) (member : value ∈ values)
    (threshold : Coordinate) (positive : 0 < threshold) :
    distribution.absoluteTailIntegral threshold value ≤
      budget.ceiling / threshold :=
  (distribution.absoluteTailIntegral_le_poweredL2_div
    threshold positive value).trans (by
      apply (RFAP.ConstructiveFraction.le_div_iff_pos positive).2
      calc
        distribution.poweredL2 value / threshold * threshold =
            distribution.poweredL2 value :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ threshold
            positive.ne'
        _ ≤ budget.ceiling := budget.poweredL2_le value member)

/-- A common tail budget below a requested tolerance certifies uniform tail
accuracy for every displayed family member. -/
theorem accurate {α : Type}
    {distribution : Distribution α} {values : List (α → Coordinate)}
    (budget : L2FamilyBudget distribution values)
    (threshold epsilon : Coordinate) (positive : 0 < threshold)
    (small : budget.ceiling / threshold < epsilon) :
    ∀ value, value ∈ values →
      distribution.absoluteTailIntegral threshold value < epsilon := by
  intro value member
  exact (budget.absoluteTailIntegral_le value member threshold positive)
    |>.trans_lt small

end L2FamilyBudget

end Distribution

end FiniteMeasure
