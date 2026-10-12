module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

namespace Purelib.Data.Rat.Fraction.ScaledProduct

/-- Rewrite the three inverse factors into two explicit fractions. -/
theorem inverse_product_as_fractions_direct (a b c : Fraction.Rational) :
    (2 * a)⁻¹ * (2 * b) * (2 * c)⁻¹ =
      ((2 * b) / (2 * a)) * (1 / (2 * c)) := by
  rw [Field.ExplicitField.div_eq_mul_inv,
    Field.ExplicitField.div_eq_mul_inv,
    Fraction.Field.one_mul]
  rw [Fraction.Field.mul_comm (2 * a)⁻¹ (2 * b)]

/-- Combine the two explicit fractions without a generic field instance. -/
theorem combine_scaled_fractions_direct (a b c : Fraction.Rational) :
    ((2 * b) / (2 * a)) * (1 / (2 * c)) =
      (2 * b) / (2 * (2 * a * c)) := by
  calc
    ((2 * b) / (2 * a)) * (1 / (2 * c)) =
        ((2 * b) * 1) / ((2 * a) * (2 * c)) :=
      Fraction.Field.div_mul_div_direct _ _ _ _
    _ = (2 * b) / (2 * (2 * a * c)) := by
      rw [Fraction.Field.mul_one_direct]
      have denominatorIdentity :
          (2 * a) * (2 * c) = 2 * (2 * a * c) := by ring1
      rw [denominatorIdentity]

/-- The rational cancellation at the end of the inverse-error calculation, kept explicit so it cannot select Mathlib's
generic division lemmas. -/
theorem inverse_error_fraction_direct (a b c : Fraction.Rational) :
    (2 * a)⁻¹ * (2 * b) * (2 * c)⁻¹ = b / (2 * a * c) := by
  rw [inverse_product_as_fractions_direct,
    combine_scaled_fractions_direct]
  have twoNonzero : (2 : Fraction.Rational) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 2) (by decide)).ne'
  exact Fraction.Field.mul_div_mul_left_direct
    2 b (2 * a * c) twoNonzero
end Purelib.Data.Rat.Fraction.ScaledProduct

end
