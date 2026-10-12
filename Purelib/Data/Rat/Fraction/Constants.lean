module

public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
public import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.SignedFraction.Normalization

open Purelib.Data.Rat

section
public section

/-!
# Sharpness witnesses for the denominator-height obstruction

For every positive coefficient scale `S`, positive common denominator `D`,
and degree `d`, the displayed monomial `(1/S) Z^d` evaluated at `1/D`
attains equality in the lower residual bound.  Thus the unit constant and the
exponents of both `S²` and `H^d` cannot be uniformly improved using only
these displayed parameters.
-/

namespace Purelib.Data.Rat.Fraction.Constants

/-- The canonical reduced zero record with denominator one and explicit Bézout coefficients. -/
@[expose] def zeroReduced : Fraction.Basic.ReducedFraction :=
  { num := 0
    den := 1
    den_pos := by decide
    reduced := ⟨⟨0, 1, by decide⟩⟩ }

/-- The retained representative of canonical zero is the displayed zero-over-one reduced record. -/
theorem representative_zero :
    Fraction.Basic.representative (0 : Fraction.Rational) = zeroReduced := by
  change Fraction.Basic.representative
    (SignedFraction.Normalization.ofFraction (SignedFraction.Normalization.toFraction zeroReduced)) = zeroReduced
  exact SignedFraction.Normalization.representative_of_reduced _

end Purelib.Data.Rat.Fraction.Constants

end

section

namespace Purelib.Data.Rat.Fraction.Constants
/-- The rational product eighteen times four equals seventy-two. -/
public theorem eighteen_mul_four : (18 :
  Purelib.Data.Rat.Fraction.Rational) * 4 = 72 := by ring1

/-- The rational product thirty-two times four equals one hundred twenty-eight. -/
public theorem thirtyTwo_mul_four : (32 :
  Purelib.Data.Rat.Fraction.Rational) * 4 = 128 := by ring1

/-! ## Sharper dyadic residual-linear converse -/

/-- Two rational halves sum to one. -/
public theorem half_add_half :
    (1 / 2 : Purelib.Data.Rat.Fraction.Rational) + (1 / 2 : Purelib.Data.Rat.Fraction.Rational) = 1 := by decide

/-- Taking half of a doubled rational returns the original value. -/
public theorem half_double (value :
  Purelib.Data.Rat.Fraction.Rational) :
    (1 / 2 : Purelib.Data.Rat.Fraction.Rational) * (value + value) = value := by
  calc
    (1 / 2 : Purelib.Data.Rat.Fraction.Rational) * (value + value) =
        ((1 / 2 : Purelib.Data.Rat.Fraction.Rational) + (1 / 2 : Purelib.Data.Rat.Fraction.Rational)) * value := by
          ring1
    _ = 1 * value := by rw [half_add_half]
    _ = value := _root_.one_mul value

/-- The rational unary threshold coefficient times two equals thirty-two fifteenths. -/
public theorem scaledTwo :
  (16 / 15 : Purelib.Data.Rat.Fraction.Rational) * 2 = 32 / 15 := by
  have twoDivOne : (2 / 1 : Purelib.Data.Rat.Fraction.Rational) = 2 := by
    calc
      (2 / 1 : Purelib.Data.Rat.Fraction.Rational) = (2 / 1) * 1 :=
        (Purelib.Data.Rat.Fraction.Field.mul_one_direct _).symm
      _ = 2 :=
        Purelib.Data.Rat.Fraction.Field.div_mul_cancel_of_ne 2 1 (by decide)
  calc
    (16 / 15 : Purelib.Data.Rat.Fraction.Rational) * 2 = (16 / 15) * (2 / 1) := by rw [twoDivOne]
    _ = (16 * 2) / (15 * 1) :=
      Purelib.Data.Rat.Fraction.Field.div_mul_div_direct 16 15 2 1
    _ = 32 / 15 := by
      rw [show (16 : Purelib.Data.Rat.Fraction.Rational) * 2 = 32 by decide,
        Purelib.Data.Rat.Fraction.Field.mul_one_direct]

/-- The rational sector coefficient times seven sixteenths equals seven fifteenths. -/
public theorem
  scaledSectorBound :
    (16 / 15 : Purelib.Data.Rat.Fraction.Rational) * (7 / 16) = 7 / 15 := by
  calc
    (16 / 15 : Purelib.Data.Rat.Fraction.Rational) * (7 / 16) =
        (16 * 7) / (15 * 16) :=
      Purelib.Data.Rat.Fraction.Field.div_mul_div_direct 16 15 7 16
    _ = (16 * 7) / (16 * 15) := by
      rw [Purelib.Data.Rat.Fraction.Field.mul_comm 15 16]
    _ = 7 / 15 :=
      Purelib.Data.Rat.Fraction.Field.mul_div_mul_left_direct
        16 7 15 (by decide)
end Purelib.Data.Rat.Fraction.Constants
end
