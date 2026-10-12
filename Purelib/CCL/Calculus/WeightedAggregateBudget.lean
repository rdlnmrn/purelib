module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Budget.Aggregate
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

public section

/-!
# Weighted finite-sum allowances

Pay a fixed nonnegative weight before the existing full count-dependent
sum budget. The two scalar divisions commute exactly, including zero weights
and empty term lists. No second term-count penalty is introduced.
-/

namespace Purelib.CCL.Calculus.WeightedAggregateBudget

open Purelib.Data.Rat
open Purelib.Approximation.Rational.Budget
/-- Weight allocation commutes with the count-dependent per-term allocation.

Both orders divide by the same two scalar factors. The identity includes zero weights and zero term counts. -/
theorem perTerm_allowance (target weight : Fraction.Rational) (count : Nat) :
    Aggregate.perTerm (Weighted.allowance target weight) count =
      Weighted.allowance (Aggregate.perTerm target count) weight := by
  simp only [Aggregate.perTerm, Weighted.allowance, Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- A nonnegative weight times its allocated per-term allowance stays within the unweighted allowance.

The target must be positive; the finite count may be zero. -/
theorem weighted_perTerm_le {target weight : Fraction.Rational} (positive : 0 < target) (nonnegative : 0 ≤ weight)
  (count : Nat) :
    weight * Aggregate.perTerm (Weighted.allowance target weight) count ≤ Aggregate.perTerm target count := by
  rw [perTerm_allowance]
  exact Weighted.mul_allowance_le (Aggregate.perTerm_positive positive count).le nonnegative

/-- The count-allocation denominator is positive for every natural count. -/
theorem countScale_positive (count : Nat) : 0 < (2 : Fraction.Rational) * (Aggregate.countCoordinate count + 1) ^ 2 :=
  by
  have countNonnegative : (0 : Fraction.Rational) ≤ Aggregate.countCoordinate count := by
    rw [Aggregate.countCoordinate_eq]
    exact Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have translated := Fraction.Order.Arithmetic.add_lt_add_right_direct (by decide : (0 : Fraction.Rational) < 1)
    (Aggregate.countCoordinate count)
  rw [zero_add, add_comm 1] at translated
  exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Fraction.Order.Arithmetic.pow_pos_direct (countNonnegative.trans_lt translated) 2)

/-- Multiplying by the count scale exactly reverses per-term allocation.

The denominator is twice the square of one plus the rational count, so it is nonzero even at count zero. The identity
holds for any rational amount. -/
theorem perTerm_rescale (amount : Fraction.Rational) (count : Nat) :
    Aggregate.perTerm ((2 * (Aggregate.countCoordinate count + 1) ^ 2) * amount) count = amount := by
  unfold Aggregate.perTerm
  apply Fraction.Field.mul_right_cancel_of_ne (countScale_positive count).ne'
  rw [Fraction.Field.div_mul_cancel_of_ne _ _ (countScale_positive count).ne']
  ring1

end Purelib.CCL.Calculus.WeightedAggregateBudget
