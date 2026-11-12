module

public import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-!
# Squared-norm separation through a retained product

A reading close to a fixed point keeps a quarter of that point's squared
norm. A positive upper bound on one factor converts product separation into
separation of the other factor using exact rational division.
-/

public section

namespace Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction

/-- A quarter-norm discrepancy retains a quarter of the original point's squared norm. -/
theorem quarter_normSq_le_of_close (point value : Canonical)
    (close : Norm.Basic.normSq (point - value) ≤ Norm.Basic.normSq point / 4) :
    Norm.Basic.normSq point / 4 ≤ Norm.Basic.normSq value := by
  have bound := half_normSq_sub_le_normSq_sub point (point - value)
  have cancel : point - (point - value) = value := by ring1
  rewrite [cancel] at bound
  calc
    Norm.Basic.normSq point / 4 = Norm.Basic.normSq point / 2 - Norm.Basic.normSq point / 4 := by
      rewrite [Purelib.Data.Rat.Bounds.Quarter.half_eq_two_quarters]
      ring1
    _ ≤ Norm.Basic.normSq point / 2 - Norm.Basic.normSq (point - value) :=
      Order.Arithmetic.sub_le_sub_left_direct close _
    _ ≤ Norm.Basic.normSq value := bound

/-- A sufficiently large sum and a small first summand bound the original second summand from below. -/
theorem other_normSq_lower_of_sum (left right : Canonical) (lower : Rational)
    (sumLower : 4 * lower ≤ Norm.Basic.normSq (left + right))
    (firstUpper : Norm.Basic.normSq left ≤ lower) : lower ≤ Norm.Basic.normSq right := by
  have bound := sumLower.trans (normSq_add_le_two left right)
  have twice : 2 * lower ≤ Norm.Basic.normSq left + Norm.Basic.normSq right := by
    apply Order.Arithmetic.le_of_mul_le_mul_right_direct (c := (2 : Rational)) _ (by decide)
    have same : (2 * lower) * 2 = 4 * lower := by ring1
    have commute : (Norm.Basic.normSq left + Norm.Basic.normSq right) * 2 =
        2 * (Norm.Basic.normSq left + Norm.Basic.normSq right) := by ring1
    rewrite [same, commute]
    exact bound
  have remainder : 2 * lower - Norm.Basic.normSq left ≤ Norm.Basic.normSq right :=
    Order.Arithmetic.sub_le_iff_le_add_direct.mpr (by
      have same : Norm.Basic.normSq right + Norm.Basic.normSq left =
          Norm.Basic.normSq left + Norm.Basic.normSq right := by ring1
      rewrite [same]
      exact twice)
  calc
    lower = 2 * lower - lower := by ring1
    _ ≤ 2 * lower - Norm.Basic.normSq left := Order.Arithmetic.sub_le_sub_left_direct firstUpper _
    _ ≤ Norm.Basic.normSq right := remainder

/-- A positive bound on the second factor transports a product lower norm to its original first factor. -/
theorem factor_normSq_lower {left right : Canonical} {lower upper : Rational}
    (upperPositive : 0 < upper) (rightBound : Norm.Basic.normSq right ≤ upper)
    (productLower : lower ≤ Norm.Basic.normSq (left * right)) : lower / upper ≤ Norm.Basic.normSq left := by
  apply (Order.Field.div_le_iff_pos upperPositive).mpr
  calc
    lower ≤ Norm.Basic.normSq (left * right) := productLower
    _ = Norm.Basic.normSq left * Norm.Basic.normSq right := Norm.Basic.normSq_mul left right
    _ ≤ Norm.Basic.normSq left * upper :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rightBound (Norm.Basic.normSq_nonneg left)

end Purelib.Data.Gaussian.Norm.Bounds

end
