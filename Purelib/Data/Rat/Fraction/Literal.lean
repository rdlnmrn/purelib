module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Int.Order
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Cast
import Purelib.Data.Rat.SignedFraction.Arithmetic
public import Purelib.Data.Rat.SignedFraction.Normalization
import Purelib.Data.Rat.Fraction.Cast.Order

open Purelib.Algebra

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Normalized finite rational literals

Normalize an integer numerator over a supplied positive natural denominator,
retaining the original signed-fraction representation and its reduction laws.
-/

namespace Purelib.Data.Rat.Fraction.Literal

open Purelib.Data

/-! Closed rational literals are kept in their finite numerator/denominator
representation while the certificates below are checked.  This prevents the
kernel from repeatedly reducing nested quotient decision procedures. -/

/-- Normalize an integer numerator over its supplied positive natural denominator.

The positive denominator is cast to the signed display type, then the original executable gcd normalization produces the
canonical reduced record. -/
def rationalLiteral (numerator : Int) (denominator : Nat)
    (denominatorPositive : 0 < denominator) : Fraction.Rational :=
  SignedFraction.Normalization.ofFraction
    ⟨numerator, Int.ofNat denominator,
      Int.Order.natCast_pos denominatorPositive⟩

/-- Multiplying a normalized literal fraction by its original positive denominator recovers the numerator cast. -/
theorem rationalLiteral_mul_denominator
    (numerator : Int) (denominator : Nat)
    (denominatorPositive : 0 < denominator) :
    Fraction.Literal.rationalLiteral numerator denominator denominatorPositive * denominator =
      (numerator : Fraction.Rational) := by
  exact SignedFraction.Arithmetic.ofFraction_mul_den
    ⟨numerator, Int.ofNat denominator,
      Int.Order.natCast_pos denominatorPositive⟩

/-- A normalized literal fraction equals the quotient of its original integer numerator and positive natural
denominator. -/
theorem rationalLiteral_eq_div
    (numerator : Int) (denominator : Nat)
    (denominatorPositive : 0 < denominator) :
    Fraction.Literal.rationalLiteral numerator denominator denominatorPositive =
      (numerator : Fraction.Rational) / denominator := by
  apply Fraction.Field.mul_right_cancel_of_ne
    (Fraction.Cast.Order.rationalNatCastNonzero denominatorPositive)
  calc
    Fraction.Literal.rationalLiteral numerator denominator denominatorPositive * denominator =
        (numerator : Fraction.Rational) :=
      Fraction.Literal.rationalLiteral_mul_denominator numerator denominator
        denominatorPositive
    _ = ((numerator : Fraction.Rational) / denominator) * denominator :=
      (Field.ExplicitField.div_mul_cancel _
        (Fraction.Cast.Order.rationalNatCastNonzero denominatorPositive)).symm

/-- A normalized literal with denominator one is its integer numerator cast. -/
theorem rationalLiteral_denominator_one (numerator : Int) :
    Fraction.Literal.rationalLiteral numerator 1 (by decide) = (numerator : Fraction.Rational) := by
  calc
    Fraction.Literal.rationalLiteral numerator 1 (by decide) =
        Fraction.Literal.rationalLiteral numerator 1 (by decide) * 1 :=
      (Fraction.Field.mul_one_direct _).symm
    _ = (numerator : Fraction.Rational) :=
      Fraction.Literal.rationalLiteral_mul_denominator numerator 1 (by decide)

end Purelib.Data.Rat.Fraction.Literal

end

section
/-!
# A closed rational literal product

The exact product of three canonical rational halves is one eighth.
-/

@[expose] public section

namespace Purelib.Data.Rat.Fraction.Literal

/-- The product of three canonical rational halves is one eighth. -/
theorem half_cube_eq_eighth :
    ((1 : Fraction.Rational) / 2) * ((1 : Fraction.Rational) / 2) * ((1 : Fraction.Rational) / 2) =
      (1 : Fraction.Rational) / 8 := by
  calc
    ((1 : Fraction.Rational) / 2) * ((1 : Fraction.Rational) / 2) * ((1 : Fraction.Rational) / 2) =
        ((1 * 1 : Fraction.Rational) / (2 * 2)) * ((1 : Fraction.Rational) / 2) := by
          exact congrArg (fun value : Fraction.Rational => value * ((1 : Fraction.Rational) / 2))
            (Fraction.Field.div_mul_div_direct 1 2 1 2)
    _ = ((1 * 1) * 1 : Fraction.Rational) / ((2 * 2) * 2) :=
      Fraction.Field.div_mul_div_direct _ _ _ _
    _ = (1 : Fraction.Rational) / 8 := by decide

end Purelib.Data.Rat.Fraction.Literal

end

end
