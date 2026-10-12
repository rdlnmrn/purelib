module
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
public section

/-!
# Requested error budgets for finite sums

The local squared-error request pays both factors of the actual term count.
The positive `count + 1` denominator also handles an empty sum without a
nonemptiness premise.  Nothing here holds the term count fixed across requests.
-/

namespace Purelib.Approximation.Rational.Budget.Aggregate

open Purelib.Data.Rat
open Purelib.Algebra

/-- Convert the binary natural directly, avoiding unary ring-cast execution when a large mesh count is used without
enumerating its cells. -/
@[expose] def countCoordinate (count : Nat) : Fraction.Rational := Fraction.Cast.fromInt (Int.ofNat count)

/-- The binary count coordinate equals the ordinary rational natural-number cast. -/
theorem countCoordinate_eq (count : Nat) : countCoordinate count = (count : Fraction.Rational) :=
  (Fraction.Cast.natCast_eq_fromInt count).symm

/-- Divide the target by twice the square of the incremented term count.

The extra one keeps the denominator positive even for an empty aggregate, while two count factors are available for the
finite error estimate. -/
@[expose] def perTerm (target : Fraction.Rational) (count : Nat) : Fraction.Rational :=
  target / (2 * (countCoordinate count + 1) ^ 2)

/-- Twice the square of a rational natural-number count plus one is strictly positive.

The original count is nonnegative. Adding one gives a positive denominator base,
whose square remains positive under multiplication by two. -/
private theorem denominator_positive (count : Nat) :
    0 < (2 : Fraction.Rational) * ((count : Fraction.Rational) + 1) ^ 2 :=
  Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Fraction.Order.Arithmetic.pow_pos_direct
      (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) (by decide)) 2)

/-- A positive aggregate target gives a positive per-term allowance for every finite count. -/
theorem perTerm_positive {target : Fraction.Rational} (positive : 0 < target) (count : Nat) :
    0 < perTerm target count := by
  rw [perTerm, countCoordinate_eq]
  exact Fraction.Order.Field.div_pos_direct positive (denominator_positive count)

/-- The two count factors consume at most half of the requested error. -/
theorem count_mul_perTerm_lt {target : Fraction.Rational} (positive : 0 < target) (count : Nat) :
    (count : Fraction.Rational) * ((count : Fraction.Rational) * perTerm target count) < target := by
  have countNonnegative : (0 : Fraction.Rational) ≤ count := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)
  have squares : (count : Fraction.Rational) * count ≤ ((count : Fraction.Rational) + 1) ^ 2 := by
    have extra : (0 : Fraction.Rational) ≤ 2 * count + 1 :=
      add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) countNonnegative) (by decide)
    calc
      _ ≤ (count : Fraction.Rational) * count + (2 * count + 1) := le_add_of_nonneg_right extra
      _ = _ := by ring1
  have paid : (2 * ((count : Fraction.Rational) + 1) ^ 2) * perTerm target count = target := by
    rw [perTerm, countCoordinate_eq]
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (denominator_positive count).ne'
  have half : ((count : Fraction.Rational) + 1) ^ 2 * perTerm target count = target / 2 := by
    apply Fraction.Field.mul_right_cancel_of_ne (by decide : (2 : Fraction.Rational) ≠ 0)
    rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
    calc
      _ = (2 * ((count : Fraction.Rational) + 1) ^ 2) * perTerm target count := by ring1
      _ = target := paid
  have halfLt : target / 2 < target := by
    apply (Fraction.Order.Field.div_lt_iff_pos (by decide)).mpr
    have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct positive (by
        decide : (1 : Fraction.Rational) < 2)
    simpa only [Fraction.Field.mul_one_direct] using scaled
  calc
    _ = ((count : Fraction.Rational) * count) * perTerm target count := by ring1
    _ ≤ ((count : Fraction.Rational) + 1) ^ 2 * perTerm target count :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct squares (perTerm_positive positive count).le
    _ = target / 2 := half
    _ < target := halfLt

/-- For a nonnegative target, its per-term allowance is at most the target. -/
theorem perTerm_le {target : Fraction.Rational} (nonnegative : 0 ≤ target) (count : Nat) :
    perTerm target count ≤ target := by
  have countNonnegative : (0 : Fraction.Rational) ≤ countCoordinate count := by
    rw [countCoordinate_eq]
    exact Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)
  have extra : (0 : Fraction.Rational) ≤ 2 * countCoordinate count ^ 2 + 4 * countCoordinate count + 1 :=
    add_nonneg (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) countNonnegative)) (by decide)
  apply Fraction.Order.Field.divide_le_self nonnegative
  calc
    1 ≤ 1 + (2 * countCoordinate count ^ 2 + 4 * countCoordinate count + 1) := le_add_of_nonneg_right extra
    _ = 2 * (countCoordinate count + 1) ^ 2 := by ring1

/-- A shorter retained occurrence count is paid by the longer count's local aggregate allowance.

A positive budget and the supplied local bound pay both factors of the
original shorter count. The comparison retains the original binary count
coordinates and the exact allowance selected by `perTerm`. -/
theorem count_mul_allowance_lt {first last : Nat} (countBound : first ≤ last) {allowance budget : Fraction.Rational}
    (positive : 0 < budget) (localBound : allowance ≤ perTerm budget last) :
    countCoordinate first * (countCoordinate first * allowance) < budget := by
  have nonnegative : 0 ≤ countCoordinate first := by
    rw [countCoordinate_eq]
    exact Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have firstBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct localBound nonnegative) nonnegative
  have countSquare := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.mul_le_mul countBound countBound))
    (perTerm_positive positive last).le
  have regroup : countCoordinate first * (countCoordinate first * perTerm budget last) ≤
      countCoordinate last * (countCoordinate last * perTerm budget last) := by
    simpa only [countCoordinate_eq, NatCast.mul, Fraction.Field.mul_assoc, -eq_self, -iff_self] using countSquare
  exact (firstBound.trans regroup).trans_lt (by
    rw [countCoordinate_eq]
    exact count_mul_perTerm_lt positive last)

end Purelib.Approximation.Rational.Budget.Aggregate

end

public section

namespace Purelib.Approximation.Rational.Budget.Aggregate

open Purelib.Data.Rat
/-- The count-squared factor times a quarter and nested quarter stays below the target.

Both shares come from the same positive per-term allowance. Their doubled sum
is at most that allowance, whose retained count-squared payment is strict. -/
public theorem count_square_mul_quarters_lt {target : Fraction.Rational} (positive : 0 < target) (count : Nat) :
    (count : Fraction.Rational) ^ 2 * (2 * (perTerm target count / 4 +
      (perTerm target count / 4) / 4)) < target := by
  let term := perTerm target count
  have termPositive := perTerm_positive positive count
  have quarterNonnegative : 0 ≤ term / 4 := Fraction.Order.Field.div_nonneg_direct termPositive.le (by decide)
  have quarterScale : term / 4 ≤ term / 4 * 4 := by
    simpa only [Fraction.Field.mul_one_direct, -eq_self, -iff_self] using
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide : (1 : Fraction.Rational) ≤ 4)
        quarterNonnegative
  have quarterSmall : (term / 4) / 4 ≤ term / 4 :=
    (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : Fraction.Rational) < 4)).mpr quarterScale
  have small : 2 * (term / 4 + (term / 4) / 4) ≤ term := by
    calc
      _ ≤ 2 * (term / 4 + term / 4) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl (term / 4)) quarterSmall) (by decide)
      _ = term / 4 * 4 := by ring1
      _ = term := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  have bounded := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small
    (Fraction.Order.Arithmetic.sq_nonneg_direct (count : Fraction.Rational))
  have paid : (count : Fraction.Rational) ^ 2 * term < target := by
    simpa only [pow_two, Fraction.Field.mul_assoc, -eq_self, -iff_self] using count_mul_perTerm_lt positive count
  exact bounded.trans_lt paid

-- Preserve the original ChartReplacementRequest.ChartReplacementRequest nominal path.

end Purelib.Approximation.Rational.Budget.Aggregate

end

public section
namespace Purelib.Approximation.Rational.Budget.Aggregate

open Purelib.Data.Rat

/-- The original finite count times its positive weighted allowance is below the target.

The count is retained as its binary rational coordinate. Increasing it by one
gives a strictly larger positive denominator, so the same allowance pays every
retained occurrence and leaves a strict margin below the positive target. -/
theorem count_mul_weighted_allowance_lt {target : Fraction.Rational}
    (positive : 0 < target) (count : Nat) :
    (count : Fraction.Rational) * Weighted.allowance target (countCoordinate count) < target := by
  have denominator : 0 < (count : Fraction.Rational) + 1 :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) (by decide)
  have allowancePositive : 0 < Weighted.allowance target (countCoordinate count) :=
    Weighted.allowance_positive positive (by
      rewrite [countCoordinate_eq]
      exact Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count))
  calc
    _ < ((count : Fraction.Rational) + 1) * Weighted.allowance target (countCoordinate count) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        (by
          have translated := Fraction.Order.Arithmetic.add_lt_add_right_direct
            (show (0 : Fraction.Rational) < 1 by decide) (count : Fraction.Rational)
          rewrite [Fraction.Field.zero_add, Fraction.Field.add_comm 1] at translated
          exact translated) allowancePositive
    _ = Weighted.allowance target (countCoordinate count) * ((count : Fraction.Rational) + 1) :=
      Fraction.Field.mul_comm _ _
    _ = target := by
      unfold Weighted.allowance
      rewrite [countCoordinate_eq]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ denominator.ne'

end Purelib.Approximation.Rational.Budget.Aggregate
end
