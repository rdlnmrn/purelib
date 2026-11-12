module
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Requested error budgets for finite sums

The local squared-error request pays both factors of the actual term count.
The positive `count + 1` denominator also handles an empty sum without a
nonemptiness premise.  Nothing here holds the term count fixed across requests.
-/

namespace Purelib.Approximation.Gaussian.Budget.Aggregate

open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)

/-- The finite Gaussian sum meets a positive squared-norm target when each original term receives the count-adjusted
allowance.

The allowance uses the actual list length and pays both finite count factors in the sum estimate. -/
theorem normSq_sum_lt (values : List
  Data.Gaussian.Basic.Canonical) {target : Fraction.Rational} (positive : 0 < target)
    (bounded : ∀ value ∈ values, Data.Gaussian.Norm.Basic.normSq value ≤ Aggregate.perTerm target
      values.length) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum values) < target :=
  (Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le values _ bounded).trans_lt (Aggregate.count_mul_perTerm_lt positive
    values.length)
end Purelib.Approximation.Gaussian.Budget.Aggregate

end

public section

namespace Purelib.Approximation.Gaussian.Budget.Aggregate

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Indexed (normSq_add_add_le)
open Purelib.Data.Rat.Fraction

/-- Three actual Gaussian remainders meet their whole target when each uses the original three-term allowance. -/
theorem normSq_add_add_lt (first second third : Canonical) {target : Rational} (positive : 0 < target)
    (firstBound : normSq first ≤ Aggregate.perTerm target 3)
    (secondBound : normSq second ≤ Aggregate.perTerm target 3)
    (thirdBound : normSq third ≤ Aggregate.perTerm target 3) :
    normSq (first + second + third) < target := by
  have combined := Order.Arithmetic.add_le_add_direct
    (Order.Arithmetic.add_le_add_direct firstBound secondBound) thirdBound
  have bounded := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct combined
    (by decide +kernel : (0 : Rational) ≤ 3)
  have grouped : (3 : Rational) *
      (Aggregate.perTerm target 3 + Aggregate.perTerm target 3 + Aggregate.perTerm target 3) =
      3 * (3 * Aggregate.perTerm target 3) := by ring1
  exact (normSq_add_add_le first second third).trans_lt
    ((bounded.trans_eq grouped).trans_lt (Aggregate.count_mul_perTerm_lt positive 3))

end Purelib.Approximation.Gaussian.Budget.Aggregate
