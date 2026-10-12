module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.NatCast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat

/-!
# Rational records with retained Bézout coefficients

The supplied numerator, positive denominator and exact integer coefficients
certify coprimality. Construction retains that data without gcd normalization;
the quotient and cross-product laws read the same original coordinates.
-/

@[expose] public section

namespace Purelib.Data.Rat.Fraction.Construction.Bezout

/-- Build a canonical rational directly from coordinates and an explicit Bézout identity.

The supplied positive denominator and integer coefficients certify that the numerator magnitude and denominator are
coprime. The constructor stores those exact coordinates without running a new gcd normalization. -/
def ofCoefficients (num : Int) (den : Nat) (denPositive :
  0 < den)
    (left right : Int)
    (bezout : left * (num.natAbs : Int) + right * (den : Int) = 1) : Fraction.Rational where
  num := num
  den := den
  den_pos := denPositive
  reduced := ⟨⟨left, right, bezout⟩⟩

/-- A rational built with retained Bézout coefficients equals the quotient of its displayed coordinates. -/
theorem ofCoefficients_eq_div (num : Int) (den : Nat)
    (denPositive : 0 < den) (left right : Int)
    (bezout : left * (num.natAbs : Int) + right * (den : Int) = 1) :
    Bezout.ofCoefficients num den denPositive left right bezout =
      (num : Fraction.Rational) / (den : Fraction.Rational) := by
  let value := Bezout.ofCoefficients num den denPositive left right bezout
  have denominatorPositive : (0 : Fraction.Rational) < den := Fraction.Cast.Order.natCast_pos_direct (n := den)
    denPositive
  apply Fraction.Field.mul_right_cancel_of_ne
    denominatorPositive.ne'
  calc
    value * (den : Fraction.Rational) = (num : Fraction.Rational) := by
      exact Fraction.Cast.representative_mul_den value
    _ = ((num : Fraction.Rational) / (den : Fraction.Rational)) * (den : Fraction.Rational) :=
      (Fraction.Field.div_mul_cancel_of_ne _ _
        denominatorPositive.ne').symm

/-- A rational quotient equals the retained Bézout fraction when both denominators are positive and the cross-products
agree.

The stated nonzero or positive denominator evidence justifies cancellation of the cleared denominator products. The
equality identifies the original canonical rational records. -/
theorem over_eq_ofCoefficients
    (left denominator : Fraction.Rational) (num : Int) (den : Nat)
    (denPositive : 0 < den) (bezoutLeft bezoutRight : Int)
    (bezout : bezoutLeft * (num.natAbs : Int) +
      bezoutRight * (den : Int) = 1)
    (denominatorPositive : 0 < denominator)
    (cross : left * (den : Fraction.Rational) = (num : Fraction.Rational) * denominator) :
    left / denominator =
      Bezout.ofCoefficients num den denPositive bezoutLeft
        bezoutRight bezout := by
  rw [Bezout.ofCoefficients_eq_div]
  exact Fraction.Field.div_eq_div_of_cross_mul
    denominatorPositive.ne' (Fraction.Order.NatCast.natCast_pos_direct den denPositive).ne' cross

end Purelib.Data.Rat.Fraction.Construction.Bezout
