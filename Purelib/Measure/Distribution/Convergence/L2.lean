module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Content.Lp.L2
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Convergence.InMeasure
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Event.RationalDistance
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# An L2 finite Vitali bridge

An in-measure certificate controls the probability of one threshold-error
event.  Cauchy--Schwarz controls the error integral on that event by its
powered-L2 size.  To remain rational and executable, the conclusion squares
the nonnegative L1 excess instead of introducing a square root.
-/

namespace Purelib.Measure
namespace Distribution

namespace InMeasureBudget

open Purelib.Data.Rat
/-- Take the nonnegative part of L1 distance minus the retained positive in-measure threshold. -/
def l1Excess {α : Type} {distribution : Distribution α}
    {left right : α → Fraction.Rational}
    (budget : InMeasureBudget distribution left right) : Fraction.Rational :=
  max (distribution.l1Distance left right - budget.threshold) 0

/-- The retained in-measure budget's L1 excess is nonnegative. -/
theorem l1Excess_nonnegative {α : Type}
    {distribution : Distribution α} {left right : α → Fraction.Rational}
    (budget : InMeasureBudget distribution left right) :
    0 ≤ budget.l1Excess :=
  Fraction.Order.Basic.le_max_right _ _

/-- Squared L1 excess is bounded by the exact squared-L2 distance times the retained failure budget. -/
theorem l1Excess_sq_le_poweredL2Distance_mul_failure {α : Type}
    {distribution : Distribution α} {left right : α → Fraction.Rational}
    (budget : InMeasureBudget distribution left right) :
    budget.l1Excess ^ 2 ≤
      distribution.poweredL2Distance left right * budget.failure := by
  let bad := separationAtLeast budget.threshold left right
  let tailError : α → Fraction.Rational := fun item =>
    Distance.rationalSeparation (left item) (right item) * indicator bad item
  have tailErrorNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ tailError atom.item := by
    intro atom atomMember
    apply Fraction.Order.Arithmetic.mul_nonneg_direct
    · exact Distance.rationalSeparation_nonneg _ _
    · cases selected : bad atom.item <;>
        simp only [indicator, selected] <;> decide
  have pointwiseSplit : ∀ atom, atom ∈ distribution.atoms →
      Distance.rationalSeparation (left atom.item) (right atom.item) ≤
        budget.threshold + tailError atom.item := by
    intro atom atomMember
    cases selected : bad atom.item
    · have notThreshold : ¬budget.threshold ≤
          Distance.rationalSeparation (left atom.item) (right atom.item) := by
        unfold bad separationAtLeast at selected
        exact decide_eq_false_iff_not.mp selected
      have below := Fraction.Order.Arithmetic.lt_of_not_ge_direct notThreshold
      simp only [tailError, indicator, selected, mul_zero, add_zero]
      exact Fraction.Order.Arithmetic.le_of_lt_direct below
    · simp only [tailError, indicator, selected, mul_one]
      exact le_add_of_nonneg_left budget.threshold_positive.le
  have splitAveraged := distribution.expectation_mono
    (fun item => Distance.rationalSeparation (left item) (right item))
    (fun item => budget.threshold + tailError item) pointwiseSplit
  rw [distribution.expectation_add, distribution.expectation_constant]
    at splitAveraged
  have differenceLeTail :
      distribution.l1Distance left right - budget.threshold ≤
        distribution.expectation tailError := by
    change distribution.expectation (fun item =>
      Distance.rationalSeparation (left item) (right item)) - budget.threshold ≤
        distribution.expectation tailError
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct
      splitAveraged budget.threshold
    have canceled :
        (budget.threshold + distribution.expectation tailError) - budget.threshold =
          distribution.expectation tailError := by ring1
    rw [canceled] at shifted
    exact shifted
  have tailExpectationNonnegative :
      0 ≤ distribution.expectation tailError :=
    distribution.expectation_nonneg tailError tailErrorNonnegative
  have excessLeTail : budget.l1Excess ≤
      distribution.expectation tailError := by
    unfold l1Excess
    exact Fraction.Order.Basic.max_le differenceLeTail tailExpectationNonnegative
  have excessSqLeTailSq : budget.l1Excess ^ 2 ≤
      distribution.expectation tailError ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      budget.l1Excess_nonnegative excessLeTail 2
  have cauchy := distribution.productExpectation_sq_le_poweredL2_mul
    (fun item => Distance.rationalSeparation (left item) (right item))
    (indicator bad)
  have productSame : (fun item =>
      Distance.rationalSeparation (left item) (right item) * indicator bad item) =
      tailError := rfl
  rw [productSame] at cauchy
  have errorL2 : distribution.poweredL2
      (fun item => Distance.rationalSeparation (left item) (right item)) =
      distribution.poweredL2Distance left right := by
    unfold poweredL2 poweredL2Distance Content.poweredL2Distance
      Content.poweredL2
    exact distribution.toContent.integral_congr _ _ (fun item =>
      Distance.VitaliL2.rationalSeparation_sq_eq_sub_sq (left item) (right item))
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
    distribution.toContent.poweredL2Distance_nonnegative left right
  calc
    budget.l1Excess ^ 2 ≤ distribution.expectation tailError ^ 2 :=
      excessSqLeTailSq
    _ ≤ distribution.poweredL2Distance left right *
        distribution.probability bad := cauchy
    _ ≤ distribution.poweredL2Distance left right * budget.failure :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        budget.probability_le distanceNonnegative

end InMeasureBudget

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain an in-measure certificate and a nonnegative ceiling on the exact squared-L2 distance.

The threshold, failure probability and second-moment bound all refer to the same original distribution and pair of
observables. -/
structure L2InMeasureBudget {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) where
  /-- The retained threshold and failure-probability certificate for the exact two observables. -/ inMeasure :
    InMeasureBudget distribution left right
  /-- The retained rational ceiling on their squared-L2 distance. -/ ceiling : Fraction.Rational
  /-- The retained squared-L2 ceiling is nonnegative. -/ ceiling_nonnegative : 0 ≤ ceiling
  /-- The exact original squared-L2 distance is at most the retained ceiling. -/ poweredL2Distance_le :
    distribution.poweredL2Distance left right ≤ ceiling

constructive_injectivity L2InMeasureBudget

namespace L2InMeasureBudget

open Purelib.Data.Rat in
/-- Squared L1 excess is at most the retained squared-L2 ceiling times the retained in-measure failure budget. -/
theorem l1Excess_sq_le {α : Type} {distribution : Distribution α}
    {left right : α → Fraction.Rational}
    (budget : L2InMeasureBudget distribution left right) :
    budget.inMeasure.l1Excess ^ 2 ≤
      budget.ceiling * budget.inMeasure.failure := by
  calc
    budget.inMeasure.l1Excess ^ 2 ≤
        distribution.poweredL2Distance left right *
          budget.inMeasure.failure :=
      budget.inMeasure.l1Excess_sq_le_poweredL2Distance_mul_failure
    _ ≤ budget.ceiling * budget.inMeasure.failure :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        budget.poweredL2Distance_le budget.inMeasure.failure_nonnegative

end L2InMeasureBudget

end Distribution

end Purelib.Measure

end
