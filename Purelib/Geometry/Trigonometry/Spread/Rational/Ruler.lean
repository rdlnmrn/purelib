module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Rational.Ruler

section

/-- The squared height ratio used to mark a spread ruler. -/
def spreadRulerRatio (spread : Fraction.Rational) :
  Fraction.Rational :=
  spread / (1 - spread)

/-- Complementary spread marks have reciprocal squared height ratios away from the two endpoints. -/
theorem spreadRulerRatio_complementary
    (spread : Fraction.Rational) (spreadNonzero : spread ≠ 0)
    (complementNonzero : 1 - spread ≠ 0) :
    spreadRulerRatio spread *
      spreadRulerRatio (1 - spread) = 1 := by
  have spreadCancel : spread * spread⁻¹ = (1 : Fraction.Rational) :=
    ExplicitField.mul_inv_cancel spread spreadNonzero
  have complementCancel :
      (1 - spread) * (1 - spread)⁻¹ = (1 : Fraction.Rational) :=
    ExplicitField.mul_inv_cancel (1 - spread) complementNonzero
  unfold spreadRulerRatio
  simp only [ExplicitField.div_eq_mul_inv]
  rw [show 1 - (1 - spread) = spread by ring1]
  calc
    spread * (1 - spread)⁻¹ * ((1 - spread) * spread⁻¹) =
        (spread * (1 - spread)⁻¹) *
          (spread⁻¹ * (1 - spread)) := by
            rw [mul_comm (1 - spread) spread⁻¹]
    _ = (spread * spread⁻¹) *
        ((1 - spread)⁻¹ * (1 - spread)) :=
      Fraction.Field.mul_pair_swap _ _ _ _
    _ = (spread * spread⁻¹) *
        ((1 - spread) * (1 - spread)⁻¹) := by
          rw [mul_comm (1 - spread)⁻¹ (1 - spread)]
    _ = 1 := by rw [spreadCancel, complementCancel, one_mul]
end
end Purelib.Geometry.Trigonometry.Spread.Rational.Ruler

end
