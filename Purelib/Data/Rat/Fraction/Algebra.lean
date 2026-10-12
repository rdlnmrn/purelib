module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite rational geometry of CCL comparisons

Every radial or coordinate comparison made after a finite decoder homography
pulls back to a four-coefficient Hermitian form

`a * (x² + y²) + b * x + c * y + d`.

The coefficients and the evaluated point are constructive rationals.  These
identities are the algebraic input for the finite x--y curve classifier used
by the persistent next-bit controller.
-/

namespace Purelib.Data.Rat.Fraction.BoundaryClearing

/-- Reorder rational factors so a displayed scale multiplies its inverse factor. -/
theorem norm_clear_algebra (factor value inverseFactor :
  Fraction.Rational) :
    factor * (value * inverseFactor) =
      value * (factor * inverseFactor) := by
  ring1

/-- Factor a common rational scale and inverse from the real-coordinate cross-product formula. -/
theorem real_clear_algebra
    (factor inverseFactor numeratorReal numeratorImag
      denominatorReal denominatorImag : Fraction.Rational) :
    factor *
        (numeratorReal * (denominatorReal * inverseFactor) -
          numeratorImag * (-denominatorImag * inverseFactor)) =
      (factor * inverseFactor) *
        (numeratorReal * denominatorReal +
          numeratorImag * denominatorImag) := by
  ring1

/-- Factor a common rational scale and inverse from the imaginary-coordinate cross-product formula. -/
theorem imag_clear_algebra
    (factor inverseFactor numeratorReal numeratorImag
      denominatorReal denominatorImag : Fraction.Rational) :
    factor *
        (numeratorReal * (-denominatorImag * inverseFactor) +
          numeratorImag * (denominatorReal * inverseFactor)) =
      (factor * inverseFactor) *
        (numeratorImag * denominatorReal -
          numeratorReal * denominatorImag) := by
  ring1
end Purelib.Data.Rat.Fraction.BoundaryClearing

end
