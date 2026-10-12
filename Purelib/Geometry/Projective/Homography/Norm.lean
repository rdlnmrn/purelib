module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Algebra
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.LinearAlgebra.Coordinates2.Matrix

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

namespace Purelib.Geometry.Projective.Homography

/-- Exact squared-norm quotient for the affine decoder chart. -/
theorem normSq_homographic (matrix : GaussianMatrix)
  (value : Data.Gaussian.Basic.Canonical)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix value) =
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix value) *
        (Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value))⁻¹ := by
  rw [Homography.Basic.homographic, Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Field.inv_eq,
    Data.Gaussian.Field.normSq_inv _ denominatorNonzero]

/-- Clear the squared-norm denominator of a homography.

At a point with nonzero affine denominator, its squared norm times the squared norm of the homographic value equals the
numerator squared norm. -/
theorem normSq_mul_homographic
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
        Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix value) =
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix value) := by
  rw [normSq_homographic matrix value denominatorNonzero]
  have normNonzero : Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) ≠ 0 :=
    fun zero => denominatorNonzero (Data.Gaussian.Norm.Basic.normSq_eq_zero.mp zero)
  let inverseNorm := (Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value))⁻¹
  have cancel :
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) * inverseNorm = 1 :=
    Fraction.Field.mul_inv_cancel _ normNonzero
  change Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
      (Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix value) * inverseNorm) =
    Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix value)
  calc
    Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
        (Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix value) * inverseNorm) =
        Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix value) *
          (Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) * inverseNorm) :=
      Fraction.BoundaryClearing.norm_clear_algebra _ _ _
    _ = Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix value) := by
      rw [cancel]
      ring1
end Purelib.Geometry.Projective.Homography

end
