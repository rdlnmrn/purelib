module

public import Purelib.Data.Gaussian.Norm.Reciprocal.Variation
import Purelib.Data.Gaussian.Norm.Power.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Finite reciprocal-sensitivity comparison on original positive floors

The original floor inequality reverses the retained reciprocal comparison.
The original power-difference recurrence and product monotonicity then give
the exact sensitivity comparison, with the same actual finite exponent.
-/

public section

namespace Purelib.Data.Gaussian.Norm.Reciprocal

open Purelib.Data.Rat

/-- Raising a positive actual denominator floor decreases its original reciprocal-power sensitivity. -/
theorem powerSensitivity_antitone {first last : Fraction.Rational} (positive : 0 < first) (order : first ≤ last)
    (exponent : Nat) : powerSensitivity last exponent ≤ powerSensitivity first exponent := by
  have inverse := Fraction.Order.Field.inv_le_inv_of_pos_direct positive order
  have firstInverse := (Fraction.Order.Field.inv_pos_direct positive).1
  have lastPositive : 0 < last :=
    ⟨Fraction.Order.Basic.le_trans 0 first last positive.1 order,
      fun reverse => positive.2 (Fraction.Order.Basic.le_trans first last 0 order reverse)⟩
  have lastInverse := (Fraction.Order.Field.inv_pos_direct lastPositive).1
  have factors := Norm.Power.differenceFactor_mono lastInverse inverse exponent
  have square := Fraction.Order.Arithmetic.mul_le_mul_direct inverse inverse lastInverse firstInverse
  exact Fraction.Order.Arithmetic.mul_le_mul_direct factors square
    (Fraction.Order.Arithmetic.mul_nonneg_direct lastInverse lastInverse)
    (Norm.Power.differenceFactor_nonnegative firstInverse exponent)

end Purelib.Data.Gaussian.Norm.Reciprocal

end
