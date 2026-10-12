module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Measure.Distribution.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Lp.L2
public import Purelib.Measure.Event.RationalDistance
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

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

namespace Purelib.Measure
namespace Distribution

section
open Purelib
open Purelib.Data.Rat
/-- Average the observable's magnitude restricted to its absolute threshold event. -/
def absoluteTailIntegral {α : Type} (distribution : Measure.Distribution α)
    (threshold : Fraction.Rational) (value : α → Fraction.Rational) : Fraction.Rational :=
  distribution.expectation fun item =>
    Distance.rationalSeparation (value item) 0 *
      indicator (absoluteTailEvent threshold value) item

/-- The original absolute-tail integral is nonnegative for every threshold. -/
theorem absoluteTailIntegral_nonnegative {α : Type}
    (distribution : Measure.Distribution α) (threshold : Fraction.Rational)
    (value : α → Fraction.Rational) :
    0 ≤ distribution.absoluteTailIntegral threshold value := by
  apply distribution.expectation_nonneg
  intro atom atomMember
  apply Fraction.Order.Arithmetic.mul_nonneg_direct
  · exact Distance.rationalSeparation_nonneg _ _
  · cases selected : absoluteTailEvent threshold value atom.item <;>
      simp only [indicator, selected] <;> decide

/-- The threshold times its absolute-tail integral is at most the original second moment. -/
theorem threshold_mul_absoluteTailIntegral_le_poweredL2 {α : Type}
    (distribution : Measure.Distribution α) (threshold : Fraction.Rational)
    (value : α → Fraction.Rational) :
    threshold * distribution.absoluteTailIntegral threshold value ≤
      distribution.poweredL2 value := by
  let tailValue : α → Fraction.Rational := fun item =>
    Distance.rationalSeparation (value item) 0 *
      indicator (absoluteTailEvent threshold value) item
  have pointwise : ∀ atom, atom ∈ distribution.atoms →
      threshold * tailValue atom.item ≤ value atom.item ^ 2 := by
    intro atom atomMember
    cases selected : absoluteTailEvent threshold value atom.item
    · simp only [tailValue, indicator, selected, mul_zero, mul_zero]
      exact Fraction.Order.Arithmetic.sq_nonneg_direct (value atom.item)
    · have thresholdLe : threshold ≤
          Distance.rationalSeparation (value atom.item) 0 := by
        unfold absoluteTailEvent at selected
        exact of_decide_eq_true selected
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          thresholdLe (Distance.rationalSeparation_nonneg (value atom.item) 0)
      simp only [tailValue, indicator, selected, mul_one]
      calc
        threshold * Distance.rationalSeparation (value atom.item) 0 ≤
            Distance.rationalSeparation (value atom.item) 0 *
              Distance.rationalSeparation (value atom.item) 0 := scaled
        _ = value atom.item ^ 2 := by
          rw [← pow_two, Distance.rationalSeparation_zero_sq]
  have averaged := distribution.expectation_mono
    (fun item => threshold * tailValue item)
    (fun item => value item ^ 2) pointwise
  rw [distribution.expectation_scale] at averaged
  change threshold * distribution.absoluteTailIntegral threshold value ≤
    distribution.poweredL2 value at averaged
  exact averaged

/-- At a positive threshold, the original absolute-tail integral is at most second moment divided by threshold. -/
theorem absoluteTailIntegral_le_poweredL2_div {α : Type}
    (distribution : Measure.Distribution α) (threshold : Fraction.Rational)
    (positive : 0 < threshold) (value : α → Fraction.Rational) :
    distribution.absoluteTailIntegral threshold value ≤
      distribution.poweredL2 value / threshold := by
  apply (Fraction.Order.Field.le_div_iff_pos positive).2
  calc
    distribution.absoluteTailIntegral threshold value * threshold =
        threshold * distribution.absoluteTailIntegral threshold value := by
      ring1
    _ ≤ distribution.poweredL2 value :=
      distribution.threshold_mul_absoluteTailIntegral_le_poweredL2
        threshold value

end

open Purelib in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retain one nonnegative second-moment ceiling for every observable in an exact finite list.

Each membership-indexed bound uses the same original distribution and the retained common rational ceiling. -/
structure L2FamilyBudget {α : Type} (distribution : Measure.Distribution α)
    (values : List (α → Fraction.Rational)) where
  /-- The common rational second-moment ceiling for the original finite family. -/ ceiling : Fraction.Rational
  /-- The retained common ceiling is nonnegative. -/ ceiling_nonnegative : 0 ≤ ceiling
  /-- Every member of the exact observable list has second moment at most the common ceiling. -/ poweredL2_le : ∀ value,
    value ∈ values →
    distribution.poweredL2 value ≤ ceiling

constructive_injectivity L2FamilyBudget

namespace L2FamilyBudget

open Purelib
open Purelib.Data.Rat
/-- Every retained family member's absolute-tail integral is at most the common ceiling divided by a positive threshold.
-/
theorem absoluteTailIntegral_le {α : Type}
    {distribution : Measure.Distribution α} {values : List (α → Fraction.Rational)}
    (budget : L2FamilyBudget distribution values)
    (value : α → Fraction.Rational) (member : value ∈ values)
    (threshold : Fraction.Rational) (positive : 0 < threshold) :
    distribution.absoluteTailIntegral threshold value ≤
      budget.ceiling / threshold :=
  (distribution.absoluteTailIntegral_le_poweredL2_div
    threshold positive value).trans (by
      apply (Fraction.Order.Field.le_div_iff_pos positive).2
      calc
        distribution.poweredL2 value / threshold * threshold =
            distribution.poweredL2 value :=
          Fraction.Field.div_mul_cancel_of_ne _ threshold
            positive.ne'
        _ ≤ budget.ceiling := budget.poweredL2_le value member)

/-- If the common ceiling divided by a positive threshold is below epsilon, every retained family member's tail integral
is below epsilon. -/
theorem accurate {α : Type}
    {distribution : Measure.Distribution α} {values : List (α → Fraction.Rational)}
    (budget : L2FamilyBudget distribution values)
    (threshold epsilon : Fraction.Rational) (positive : 0 < threshold)
    (small : budget.ceiling / threshold < epsilon) :
    ∀ value, value ∈ values →
      distribution.absoluteTailIntegral threshold value < epsilon := by
  intro value member
  exact (budget.absoluteTailIntegral_le value member threshold positive)
    |>.trans_lt small

end L2FamilyBudget

end Distribution

end Purelib.Measure

end
