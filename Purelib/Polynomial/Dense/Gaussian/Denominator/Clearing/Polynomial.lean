module
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.LCM
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Basic

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite denominator-height lower bounds for polynomial residuals

The finite coefficient list is cleared to Gaussian integers by a structural
product of the canonical coordinate denominators.  Homogeneous evaluation at
a displayed common-denominator Gaussian fraction then gives an integral
numerator.  If the residual is nonzero, its integral norm is at least one.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing

/-- Coefficient scale used by the lower residual theorem. -/
def coefficientScale (p :
  Basic.CanonicalCoefficients.CoefficientPolynomial) : Nat :=
  (Dense.Gaussian.Denominator.Clearing.LCM.lcmClear p.normalize.coeffs).scale

/-- The least common denominator scale of the normalized polynomial coefficients is positive. -/
theorem coefficientScale_pos (p :
  Basic.CanonicalCoefficients.CoefficientPolynomial) :
    0 < coefficientScale p := by
  exact (Dense.Gaussian.Denominator.Clearing.LCM.lcmClear p.normalize.coeffs).scalePositive

/-- The polynomial coefficient scale divides every natural number that clears
all reduced real and imaginary coefficient-coordinate denominators. -/
theorem coefficientScale_dvd_of_clears (p :
  Basic.CanonicalCoefficients.CoefficientPolynomial) {scale : Nat}
    (clears : Dense.Gaussian.Denominator.Clearing.LCM.ClearsCoefficientDenominators p.normalize.coeffs scale) :
    coefficientScale p ∣ scale := by
  exact Dense.Gaussian.Denominator.Clearing.LCM.lcmScale_dvd_of_clears clears
end Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing

end
