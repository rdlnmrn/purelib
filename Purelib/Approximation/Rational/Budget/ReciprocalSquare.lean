module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Rounding.Floor

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Field
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Data.Rat.Rounding

section
@[expose] public section

/-!
# Executable finite sample-count requests

The one-shot finite Chebyshev estimate can be inverted constructively.  A
rational variance budget, deviation threshold, and failure budget determine
an explicit positive natural sample count using the constructive rational
ceiling.  The returned finite iid table then has deviation probability
strictly below the requested failure budget.

The construction is intentionally one-shot: it creates no infinite sample
sequence and states no asymptotic law.
-/

namespace Purelib.Measure

namespace Distribution

/-- A positive finite sample count sufficient for a Chebyshev failure request under a displayed rational variance upper
bound. -/
def requiredChebyshevSampleCount
    (varianceBudget threshold failure : Fraction.Rational) : Nat :=
  Nat.succ (Floor.ceilNat
    (varianceBudget / (failure * threshold ^ 2)))

/-- The computed Chebyshev sample count has strictly positive rational cast. -/
theorem requiredChebyshevSampleCount_positive
    (varianceBudget threshold failure : Fraction.Rational) :
    0 < ((requiredChebyshevSampleCount
      varianceBudget threshold failure : Nat) : Fraction.Rational) := by
  apply Fraction.Cast.Order.natCast_pos_direct
  unfold requiredChebyshevSampleCount
  exact Nat.zero_lt_succ _

/-- The variance-to-budget ratio is strictly below the computed sample count for nonnegative variance and positive
threshold and failure budgets. -/
private theorem requiredChebyshev_ratio_lt_count
    (varianceBudget threshold failure : Fraction.Rational)
    (varianceBudgetNonnegative : 0 ≤ varianceBudget)
    (thresholdPositive : 0 < threshold)
    (failurePositive : 0 < failure) :
    varianceBudget / (failure * threshold ^ 2) <
      ((requiredChebyshevSampleCount
        varianceBudget threshold failure : Nat) : Fraction.Rational) := by
  have squarePositive : 0 < threshold ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct thresholdPositive 2
  have denominatorPositive : 0 < failure * threshold ^ 2 :=
    Fraction.Order.Arithmetic.mul_pos_direct failurePositive squarePositive
  let ratio := varianceBudget / (failure * threshold ^ 2)
  have ratioNonnegative : 0 ≤ ratio :=
    Fraction.Order.Field.div_nonneg_direct varianceBudgetNonnegative
      denominatorPositive.le
  have ratioLeCeiling : ratio ≤
      (Floor.ceilNat ratio : Fraction.Rational) :=
    Floor.le_natCast_ceilNat_of_nonneg ratioNonnegative
  have ceilingLtSuccessor :
      (Floor.ceilNat ratio : Fraction.Rational) <
        (Nat.succ (Floor.ceilNat ratio) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_lt_direct (Nat.lt_succ_self _)
  exact ratioLeCeiling.trans_lt ceilingLtSuccessor

/-- The computed finite sample count makes the rational Chebyshev expression strictly smaller than the requested
positive failure budget. -/
theorem requiredChebyshevSampleCount_accurate
    (varianceBudget threshold failure : Fraction.Rational)
    (varianceBudgetNonnegative : 0 ≤ varianceBudget)
    (thresholdPositive : 0 < threshold)
    (failurePositive : 0 < failure) :
    (varianceBudget /
        (requiredChebyshevSampleCount
          varianceBudget threshold failure : Fraction.Rational)) /
      threshold ^ 2 < failure := by
  have squarePositive : 0 < threshold ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct thresholdPositive 2
  have failureTimesSquarePositive : 0 < failure * threshold ^ 2 :=
    Fraction.Order.Arithmetic.mul_pos_direct failurePositive squarePositive
  have countPositive := requiredChebyshevSampleCount_positive
    varianceBudget threshold failure
  have ratioSmall := requiredChebyshev_ratio_lt_count
    varianceBudget threshold failure varianceBudgetNonnegative
    thresholdPositive failurePositive
  have numeratorSmall : varianceBudget <
      (failure * threshold ^ 2) *
        (requiredChebyshevSampleCount
          varianceBudget threshold failure : Fraction.Rational) := by
    have crossed := (Fraction.Order.Field.div_lt_iff_pos
      failureTimesSquarePositive).1 ratioSmall
    calc
      varianceBudget <
          (requiredChebyshevSampleCount
            varianceBudget threshold failure : Fraction.Rational) *
            (failure * threshold ^ 2) := crossed
      _ = (failure * threshold ^ 2) *
          (requiredChebyshevSampleCount
            varianceBudget threshold failure : Fraction.Rational) := by ring1
  apply (Fraction.Order.Field.div_lt_iff_pos squarePositive).2
  apply (Fraction.Order.Field.div_lt_iff_pos countPositive).2
  exact numeratorSmall

/-- Every larger finite sample count preserves the strict Chebyshev request. -/
theorem requiredChebyshevSampleCount_accurate_of_le
    (varianceBudget threshold failure : Fraction.Rational)
    (varianceBudgetNonnegative : 0 ≤ varianceBudget)
    (thresholdPositive : 0 < threshold)
    (failurePositive : 0 < failure)
    (count : Nat)
    (enough : requiredChebyshevSampleCount
      varianceBudget threshold failure ≤ count) :
    (varianceBudget / (count : Fraction.Rational)) / threshold ^ 2 < failure := by
  have requestedPositive := requiredChebyshevSampleCount_positive
    varianceBudget threshold failure
  have countOrder :
      ((requiredChebyshevSampleCount
        varianceBudget threshold failure : Nat) : Fraction.Rational) ≤
        (count : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct enough
  have squarePositive : 0 < threshold ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct thresholdPositive 2
  have firstDivisionLe : varianceBudget / (count : Fraction.Rational) ≤
      varianceBudget /
        (requiredChebyshevSampleCount
          varianceBudget threshold failure : Fraction.Rational) :=
    Fraction.Order.Field.div_le_div_of_nonneg_left_direct
      varianceBudgetNonnegative requestedPositive countOrder
  have bothDivisionsLe :
      (varianceBudget / (count : Fraction.Rational)) / threshold ^ 2 ≤
        (varianceBudget /
          (requiredChebyshevSampleCount
            varianceBudget threshold failure : Fraction.Rational)) /
          threshold ^ 2 := by
    change (varianceBudget / (count : Fraction.Rational)) *
        (threshold ^ 2)⁻¹ ≤
      (varianceBudget /
        (requiredChebyshevSampleCount
          varianceBudget threshold failure : Fraction.Rational)) *
        (threshold ^ 2)⁻¹
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      firstDivisionLe
      (Fraction.Order.Field.inv_pos_direct squarePositive).le
  exact bothDivisionsLe.trans_lt
    (requiredChebyshevSampleCount_accurate varianceBudget threshold failure
      varianceBudgetNonnegative thresholdPositive failurePositive)
end Distribution

end Purelib.Measure

end

section
@[expose] public section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

namespace Purelib.Approximation.Rational.Budget

/-- Executable sample count assigning half of the desired estimator error to sampling fluctuation, using the global
variance budget `1`. -/
def encodedChordalOmegaEstimatorSampleCount
    (epsilon failure : Fraction.Rational) : Nat :=
  Measure.Distribution.requiredChebyshevSampleCount
    1 (epsilon / 2) failure
end Purelib.Approximation.Rational.Budget

end
