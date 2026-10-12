module

import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Measure.Event.RationalDistance
import Purelib.Data.Rat.Distance.Basic
public import Purelib.Measure.Distribution.Convergence.InMeasure
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section

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

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retain an exceedance budget and a uniform separation ceiling on the exact original distribution atoms.

The ceiling is at least the same retained positive threshold. It bounds every original occurrence, while the inner
budget bounds probability of exceeding that threshold. -/
structure BoundedInMeasureBudget {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) where
  /-- The exact retained threshold and exceedance-probability certificate for these observables. -/ inMeasure :
    InMeasureBudget distribution left right
  /-- The uniform rational separation ceiling on original retained occurrences. -/ ceiling : Fraction.Rational
  /-- The ceiling is no smaller than the exact retained exceedance threshold. -/ threshold_le_ceiling :
    inMeasure.threshold ≤ ceiling
  /-- Every original distribution occurrence has separation at most the retained ceiling. -/ error_le : ∀ atom, atom ∈
    distribution.atoms →
    Distance.rationalSeparation (left atom.item) (right atom.item) ≤ ceiling

constructive_injectivity BoundedInMeasureBudget

namespace BoundedInMeasureBudget

open Purelib.Data.Rat
/-- Compute threshold plus ceiling-minus-threshold times the exact retained failure allowance. -/
def l1Bound {α : Type} {distribution : Distribution α}
    {left right : α → Fraction.Rational}
    (budget : BoundedInMeasureBudget distribution left right) : Fraction.Rational :=
  budget.inMeasure.threshold +
    (budget.ceiling - budget.inMeasure.threshold) * budget.inMeasure.failure

/-- The retained threshold-ceiling probability expression is nonnegative. -/
theorem l1Bound_nonnegative {α : Type}
    {distribution : Distribution α} {left right : α → Fraction.Rational}
    (budget : BoundedInMeasureBudget distribution left right) :
    0 ≤ budget.l1Bound := by
  apply add_nonneg budget.inMeasure.threshold_positive.le
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.sub_nonneg_direct
      budget.threshold_le_ceiling)
    budget.inMeasure.failure_nonnegative

/-- The retained bounded exceedance budget bounds expected separation by its computed threshold-ceiling expression.

Below the threshold use its ordinary allowance; on the exact exceedance event use the larger ceiling and its retained
probability bound. -/
theorem l1Distance_le {α : Type}
    {distribution : Distribution α} {left right : α → Fraction.Rational}
    (budget : BoundedInMeasureBudget distribution left right) :
    distribution.l1Distance left right ≤ budget.l1Bound := by
  let event := separationAtLeast budget.inMeasure.threshold left right
  let extra := budget.ceiling - budget.inMeasure.threshold
  let allowance : α → Fraction.Rational := fun item =>
    budget.inMeasure.threshold + extra * indicator event item
  have extraNonnegative : 0 ≤ extra :=
    Fraction.Order.Arithmetic.sub_nonneg_direct
      budget.threshold_le_ceiling
  have pointwise : ∀ atom, atom ∈ distribution.atoms →
      Distance.rationalSeparation (left atom.item) (right atom.item) ≤
        allowance atom.item := by
    intro atom atomMember
    cases selected : event atom.item
    · have notThreshold : ¬budget.inMeasure.threshold ≤
          Distance.rationalSeparation (left atom.item) (right atom.item) := by
        unfold event separationAtLeast at selected
        exact decide_eq_false_iff_not.mp selected
      have below :=
        Fraction.Order.Arithmetic.lt_of_not_ge_direct notThreshold
      simp only [allowance, indicator, selected, mul_zero, add_zero]
      exact Fraction.Order.Arithmetic.le_of_lt_direct below
    · simp only [allowance, indicator, selected, mul_one]
      calc
        Distance.rationalSeparation (left atom.item) (right atom.item) ≤
            budget.ceiling := budget.error_le atom atomMember
        _ = budget.inMeasure.threshold + extra := by
          dsimp only [extra]
          ring1
  have averaged := distribution.expectation_mono
    (fun item => Distance.rationalSeparation (left item) (right item))
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
      Fraction.Order.Arithmetic.add_le_add_direct le_rfl
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          budget.inMeasure.probability_le extraNonnegative)
    _ = budget.l1Bound := rfl

/-- A computed bounded-exceedance allowance below a tolerance gives expected separation strictly below that tolerance.
-/
theorem accurate {α : Type} {distribution : Distribution α}
    {left right : α → Fraction.Rational}
    (budget : BoundedInMeasureBudget distribution left right)
    (epsilon : Fraction.Rational) (small : budget.l1Bound < epsilon) :
    distribution.l1Distance left right < epsilon :=
  budget.l1Distance_le.trans_lt small

end BoundedInMeasureBudget

end Distribution

end Purelib.Measure
