module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Algebra
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

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

namespace Purelib.Data.Gaussian.NormSq

open Purelib.Algebra
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Multiplying the real inverse-product coordinate by denominator norm gives the corresponding conjugate-product
coordinate. -/
theorem normSq_mul_inv_real
    (numeratorValue denominatorValue : Basic.Canonical)
    (denominatorNonzero : denominatorValue ≠ 0) :
    Norm.Basic.normSq denominatorValue *
        (numeratorValue * Field.inv denominatorValue).re =
      (numeratorValue * Basic.conj denominatorValue).re := by
  have normNonzero : Norm.Basic.normSq denominatorValue ≠ 0 :=
    fun zero => denominatorNonzero (Norm.Basic.normSq_eq_zero.mp zero)
  let inverseNorm := (Norm.Basic.normSq denominatorValue)⁻¹
  have cancel : Norm.Basic.normSq denominatorValue * inverseNorm = 1 :=
    Fraction.Field.mul_inv_cancel _ normNonzero
  simp only [Basic.mul_re, Field.inv, Field.ExplicitField.div_eq_mul_inv]
  change Norm.Basic.normSq denominatorValue *
      (numeratorValue.re * (denominatorValue.re * inverseNorm) -
        numeratorValue.im * (-denominatorValue.im * inverseNorm)) =
    numeratorValue.re * denominatorValue.re -
      numeratorValue.im * -denominatorValue.im
  calc
    Norm.Basic.normSq denominatorValue *
        (numeratorValue.re * (denominatorValue.re * inverseNorm) -
          numeratorValue.im * (-denominatorValue.im * inverseNorm)) =
        (Norm.Basic.normSq denominatorValue * inverseNorm) *
          (numeratorValue.re * denominatorValue.re +
            numeratorValue.im * denominatorValue.im) :=
      Fraction.BoundaryClearing.real_clear_algebra _ _ _ _ _ _
    _ = numeratorValue.re * denominatorValue.re -
        numeratorValue.im * -denominatorValue.im := by
      rw [cancel]
      ring1

/-- Multiplying the imaginary inverse-product coordinate by denominator norm gives the corresponding conjugate-product
coordinate. -/
theorem normSq_mul_inv_imag
    (numeratorValue denominatorValue : Basic.Canonical)
    (denominatorNonzero : denominatorValue ≠ 0) :
    Norm.Basic.normSq denominatorValue *
        (numeratorValue * Field.inv denominatorValue).im =
      (numeratorValue * Basic.conj denominatorValue).im := by
  have normNonzero : Norm.Basic.normSq denominatorValue ≠ 0 :=
    fun zero => denominatorNonzero (Norm.Basic.normSq_eq_zero.mp zero)
  let inverseNorm := (Norm.Basic.normSq denominatorValue)⁻¹
  have cancel : Norm.Basic.normSq denominatorValue * inverseNorm = 1 :=
    Fraction.Field.mul_inv_cancel _ normNonzero
  simp only [Basic.mul_im, Field.inv, Field.ExplicitField.div_eq_mul_inv]
  change Norm.Basic.normSq denominatorValue *
      (numeratorValue.re * (-denominatorValue.im * inverseNorm) +
        numeratorValue.im * (denominatorValue.re * inverseNorm)) =
    numeratorValue.re * -denominatorValue.im +
      numeratorValue.im * denominatorValue.re
  calc
    Norm.Basic.normSq denominatorValue *
        (numeratorValue.re * (-denominatorValue.im * inverseNorm) +
          numeratorValue.im * (denominatorValue.re * inverseNorm)) =
        (Norm.Basic.normSq denominatorValue * inverseNorm) *
          (numeratorValue.im * denominatorValue.re -
            numeratorValue.re * denominatorValue.im) :=
      Fraction.BoundaryClearing.imag_clear_algebra _ _ _ _ _ _
    _ = numeratorValue.re * -denominatorValue.im +
        numeratorValue.im * denominatorValue.re := by
      rw [cancel]
      ring1
end Purelib.Data.Gaussian.NormSq

end
