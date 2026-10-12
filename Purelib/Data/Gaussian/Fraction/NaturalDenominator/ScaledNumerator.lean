module
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Data.Rat.Fraction.ScaledNumerator
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.GaussianInt.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Finite denominator-height lower bounds for polynomial residuals

The finite coefficient list is cleared to Gaussian integers by a structural
product of the canonical coordinate denominators.  Homogeneous evaluation at
a displayed common-denominator Gaussian fraction then gives an integral
numerator.  If the residual is nonzero, its integral norm is at least one.
-/

namespace Purelib.Data.Gaussian.Fraction.NaturalDenominator.ScaledNumerator

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Compute the Gaussian-integer coefficient obtained by scaling both original rational coordinate numerators.

Compute each integer coordinate with the original scaledCoordinateNumerator operation. Its embedding theorem requires
both reduced denominators to divide the same supplied natural scale. -/
def scaledGaussianCoefficient
    (scale : Nat) (coefficient : Basic.Canonical) : Data.GaussianInt :=
  ⟨Fraction.ScaledNumerator.scaledCoordinateNumerator scale coefficient.re,
    Fraction.ScaledNumerator.scaledCoordinateNumerator scale coefficient.im⟩

open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- When both reduced coordinate denominators divide the scale, the integer coefficient embeds as that scale times the
original Gaussian. -/
theorem toGaussian_scaledGaussianCoefficient
    (scale : Nat) (coefficient : Basic.Canonical)
    (realDivides :
      (Fraction.Basic.representative coefficient.re).den ∣ scale)
    (imaginaryDivides :
      (Fraction.Basic.representative coefficient.im).den ∣ scale) :
    GaussianInt.toGaussian
        (scaledGaussianCoefficient scale coefficient) =
      ⟨(scale : Fraction.Rational), 0⟩ * coefficient := by
  apply Basic.ext
  · simp only [-eq_self, -iff_self, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    change
      (Fraction.ScaledNumerator.scaledCoordinateNumerator scale coefficient.re : Fraction.Rational) =
        (scale : Fraction.Rational) * coefficient.re - 0 * coefficient.im
    rw [Fraction.ScaledNumerator.scaledCoordinateNumerator_spec scale coefficient.re realDivides]
    ring1
  · simp only [-eq_self, -iff_self, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    change
      (Fraction.ScaledNumerator.scaledCoordinateNumerator scale coefficient.im : Fraction.Rational) =
        (scale : Fraction.Rational) * coefficient.im + 0 * coefficient.re
    rw [Fraction.ScaledNumerator.scaledCoordinateNumerator_spec scale coefficient.im imaginaryDivides]
    ring1
end Purelib.Data.Gaussian.Fraction.NaturalDenominator.ScaledNumerator

end
