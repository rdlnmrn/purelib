module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.NormSq.Division
import Purelib.Data.Rat.Order.PositiveScale
import Purelib.Geometry.Projective.Hermitian.Affine
import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Projective.Hermitian.Radial
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.Homography.Norm
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
public section

/-!
# Finite rational geometry of CCL comparisons

Every radial or coordinate comparison made after a finite decoder homography
pulls back to a four-coefficient Hermitian form

`a * (x² + y²) + b * x + c * y + d`.

The coefficients and the evaluated point are constructive rationals.  These
identities are the algebraic input for the finite x--y curve classifier used
by the persistent next-bit controller.
-/

namespace Purelib.Geometry.Projective.Hermitian

open Purelib

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates2.Matrix

/-- Pull back a squared-norm comparison to a Hermitian form.

The numerator affine norm form and threshold-scaled denominator affine norm
form retain the displayed matrix coefficients and rational squared radius. -/
@[expose] def normComparisonForm (matrix : GaussianMatrix) (radiusSq : Fraction.Rational) :
    Hermitian.HermitianForm :=
  (Hermitian.affineNormForm matrix.a matrix.b).sub
    ((Hermitian.affineNormForm matrix.c matrix.d).scale radiusSq)

/-- Pull back a real-coordinate comparison to a Hermitian form.

The cross-product form retains the matrix numerator and denominator, while
the supplied threshold scales the same denominator norm form. -/
@[expose] def realComparisonForm (matrix : GaussianMatrix) (threshold : Fraction.Rational) :
    Hermitian.HermitianForm :=
  (Hermitian.realCrossForm matrix.a matrix.b matrix.c matrix.d).sub
    ((Hermitian.affineNormForm matrix.c matrix.d).scale threshold)

/-- Pull back an imaginary-coordinate comparison to a Hermitian form.

The imaginary cross-product form and threshold-scaled denominator norm form
retain the same matrix entries and coordinate threshold. -/
@[expose] def imagComparisonForm (matrix : GaussianMatrix) (threshold : Fraction.Rational) :
    Hermitian.HermitianForm :=
  (Hermitian.imagCrossForm matrix.a matrix.b matrix.c matrix.d).sub
    ((Hermitian.affineNormForm matrix.c matrix.d).scale threshold)

/-- Evaluate a norm comparison as the difference of retained affine quadrances.

The numerator and denominator use the supplied matrix and point; the same
squared radius multiplies the denominator quadrance. -/
theorem eval_normComparisonForm
    (matrix : GaussianMatrix) (radiusSq : Fraction.Rational) (value :
      Data.Gaussian.Basic.Canonical) :
    (Geometry.Projective.Hermitian.normComparisonForm matrix radiusSq).eval value =
      Data.Gaussian.Norm.Basic.normSq (matrix.a * value + matrix.b) -
        radiusSq * Data.Gaussian.Norm.Basic.normSq (matrix.c * value + matrix.d) := by
  simp only [Geometry.Projective.Hermitian.normComparisonForm, HermitianForm.eval_sub,
    HermitianForm.eval_scale, Hermitian.eval_affineNormForm, -eq_self]
  rfl

/-- Evaluate a real-coordinate comparison through the conjugate affine product.

The real part of the retained numerator times conjugate denominator is
adjusted by the same threshold-scaled denominator quadrance. -/
theorem eval_realComparisonForm
    (matrix : GaussianMatrix) (threshold : Fraction.Rational) (value :
      Data.Gaussian.Basic.Canonical) :
    (Geometry.Projective.Hermitian.realComparisonForm matrix threshold).eval value =
      ((matrix.a * value + matrix.b) *
          Data.Gaussian.Basic.conj (matrix.c * value + matrix.d)).re -
        threshold * Data.Gaussian.Norm.Basic.normSq (matrix.c * value + matrix.d) := by
  simp only [Geometry.Projective.Hermitian.realComparisonForm, HermitianForm.eval_sub,
    HermitianForm.eval_scale, Hermitian.eval_realCrossForm, Hermitian.eval_affineNormForm, -eq_self]
  rfl

/-- Evaluate an imaginary-coordinate comparison through the conjugate affine product.

The imaginary part of the retained numerator times conjugate denominator is
adjusted by the same threshold-scaled denominator quadrance. -/
theorem eval_imagComparisonForm
    (matrix : GaussianMatrix) (threshold : Fraction.Rational) (value :
      Data.Gaussian.Basic.Canonical) :
    (Geometry.Projective.Hermitian.imagComparisonForm matrix threshold).eval value =
      ((matrix.a * value + matrix.b) *
          Data.Gaussian.Basic.conj (matrix.c * value + matrix.d)).im -
        threshold * Data.Gaussian.Norm.Basic.normSq (matrix.c * value + matrix.d) := by
  simp only [Geometry.Projective.Hermitian.imagComparisonForm, HermitianForm.eval_sub,
    HermitianForm.eval_scale, Hermitian.eval_imagCrossForm, Hermitian.eval_affineNormForm, -eq_self]
  rfl

/-- Clearing the denominator norm gives the norm comparison form.

The denominator is nonzero, so its retained quadrance scales the squared
homographic norm difference by the same matrix and radius. -/
theorem cleared_norm_identity
    (matrix : GaussianMatrix) (radiusSq : Fraction.Rational) (value :
      Data.Gaussian.Basic.Canonical)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    (Geometry.Projective.Hermitian.normComparisonForm matrix radiusSq).eval value =
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
        (Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix value) - radiusSq) := by
  rw [Geometry.Projective.Hermitian.eval_normComparisonForm]
  change Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix value) -
      radiusSq * Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) = _
  rw [← Homography.normSq_mul_homographic matrix value denominatorNonzero]
  ring1

/-- Clearing the denominator gives the real-coordinate comparison form.

The supplied nonzero denominator identifies the rational real-coordinate
difference after scaling by that denominator quadrance. -/
theorem cleared_real_identity
    (matrix : GaussianMatrix) (threshold : Fraction.Rational) (value :
      Data.Gaussian.Basic.Canonical)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    (Geometry.Projective.Hermitian.realComparisonForm matrix threshold).eval value =
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
        ((Homography.Basic.homographic matrix value).re - threshold) := by
  rw [Geometry.Projective.Hermitian.eval_realComparisonForm]
  change ((Homography.Basic.numerator matrix value) *
      Data.Gaussian.Basic.conj (Homography.Basic.denominator matrix value)).re -
        threshold * Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) = _
  rw [← NormSq.normSq_mul_inv_real (Homography.Basic.numerator matrix value)
    (Homography.Basic.denominator matrix value) denominatorNonzero]
  unfold Homography.Basic.homographic
  rw [Data.Gaussian.Field.inv_eq]
  ring1

/-- Clearing the denominator gives the imaginary-coordinate comparison form.

The supplied nonzero denominator identifies the rational imaginary-coordinate
difference after scaling by that denominator quadrance. -/
theorem cleared_imag_identity
    (matrix : GaussianMatrix) (threshold : Fraction.Rational) (value :
      Data.Gaussian.Basic.Canonical)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    (Geometry.Projective.Hermitian.imagComparisonForm matrix threshold).eval value =
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
        ((Homography.Basic.homographic matrix value).im - threshold) := by
  rw [Geometry.Projective.Hermitian.eval_imagComparisonForm]
  change ((Homography.Basic.numerator matrix value) *
      Data.Gaussian.Basic.conj (Homography.Basic.denominator matrix value)).im -
        threshold * Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) = _
  rw [← NormSq.normSq_mul_inv_imag (Homography.Basic.numerator matrix value)
    (Homography.Basic.denominator matrix value) denominatorNonzero]
  unfold Homography.Basic.homographic
  rw [Data.Gaussian.Field.inv_eq]
  ring1

/-- The homographic squared norm is strictly below its threshold exactly when its comparison form is negative.

The homographic denominator must be nonzero; its positive squared norm preserves the comparison when clearing the
denominator. -/
theorem norm_homographic_lt_iff
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) (radiusSq :
      Fraction.Rational)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix value) < radiusSq ↔
      (Geometry.Projective.Hermitian.normComparisonForm matrix radiusSq).eval value < 0 :=
  Order.PositiveScale.compare_lt_iff (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
    (Geometry.Projective.Hermitian.cleared_norm_identity matrix radiusSq value denominatorNonzero)

/-- The homographic squared norm is at most its threshold exactly when its comparison form is nonpositive.

The homographic denominator must be nonzero; its positive squared norm preserves the comparison when clearing the
denominator. -/
theorem norm_homographic_le_iff
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) (radiusSq :
      Fraction.Rational)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix value) ≤ radiusSq ↔
      (Geometry.Projective.Hermitian.normComparisonForm matrix radiusSq).eval value ≤ 0 :=
  Order.PositiveScale.compare_le_iff (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
    (Geometry.Projective.Hermitian.cleared_norm_identity matrix radiusSq value denominatorNonzero)

/-- The homographic squared norm is equal to its threshold exactly when its comparison form is zero.

The homographic denominator must be nonzero; its positive squared norm preserves the comparison when clearing the
denominator. -/
theorem norm_homographic_eq_iff
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) (radiusSq :
      Fraction.Rational)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix value) = radiusSq ↔
      (Geometry.Projective.Hermitian.normComparisonForm matrix radiusSq).eval value = 0 :=
  Order.PositiveScale.compare_eq_iff (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
    (Geometry.Projective.Hermitian.cleared_norm_identity matrix radiusSq value denominatorNonzero)

/-- The homographic squared norm is strictly above its threshold exactly when its comparison form is positive.

The homographic denominator must be nonzero; its positive squared norm preserves the comparison when clearing the
denominator. -/
theorem norm_homographic_gt_iff
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) (radiusSq :
      Fraction.Rational)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    radiusSq < Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix value) ↔
      0 < (Geometry.Projective.Hermitian.normComparisonForm matrix radiusSq).eval value :=
  Order.PositiveScale.compare_gt_iff (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
    (Geometry.Projective.Hermitian.cleared_norm_identity matrix radiusSq value denominatorNonzero)

/-- The homographic squared norm is at least its threshold exactly when its comparison form is nonnegative.

The homographic denominator must be nonzero; its positive squared norm preserves the comparison when clearing the
denominator. -/
theorem norm_homographic_ge_iff
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) (radiusSq :
      Fraction.Rational)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    radiusSq ≤ Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix value) ↔
      0 ≤ (Geometry.Projective.Hermitian.normComparisonForm matrix radiusSq).eval value :=
  Order.PositiveScale.compare_ge_iff (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
    (Geometry.Projective.Hermitian.cleared_norm_identity matrix radiusSq value denominatorNonzero)

/-- The homographic real coordinate is strictly below its threshold exactly when its comparison form is negative.

The homographic denominator must be nonzero; its positive squared norm preserves the comparison when clearing the
denominator. -/
theorem real_homographic_lt_iff
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) (threshold :
      Fraction.Rational)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    (Homography.Basic.homographic matrix value).re < threshold ↔
      (Geometry.Projective.Hermitian.realComparisonForm matrix threshold).eval value < 0 :=
  Order.PositiveScale.compare_lt_iff (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
    (Geometry.Projective.Hermitian.cleared_real_identity matrix threshold value denominatorNonzero)

/-- The homographic real coordinate is at most its threshold exactly when its comparison form is nonpositive.

The homographic denominator must be nonzero; its positive squared norm preserves the comparison when clearing the
denominator. -/
theorem real_homographic_le_iff
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) (threshold :
      Fraction.Rational)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    (Homography.Basic.homographic matrix value).re ≤ threshold ↔
      (Geometry.Projective.Hermitian.realComparisonForm matrix threshold).eval value ≤ 0 :=
  Order.PositiveScale.compare_le_iff (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
    (Geometry.Projective.Hermitian.cleared_real_identity matrix threshold value denominatorNonzero)

/-- The homographic real coordinate is equal to its threshold exactly when its comparison form is zero.

The homographic denominator must be nonzero; its positive squared norm preserves the comparison when clearing the
denominator. -/
theorem real_homographic_eq_iff
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) (threshold :
      Fraction.Rational)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    (Homography.Basic.homographic matrix value).re = threshold ↔
      (Geometry.Projective.Hermitian.realComparisonForm matrix threshold).eval value = 0 :=
  Order.PositiveScale.compare_eq_iff (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
    (Geometry.Projective.Hermitian.cleared_real_identity matrix threshold value denominatorNonzero)

/-- The homographic real coordinate is strictly above its threshold exactly when its comparison form is positive.

The homographic denominator must be nonzero; its positive squared norm preserves the comparison when clearing the
denominator. -/
theorem real_homographic_gt_iff
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) (threshold :
      Fraction.Rational)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    threshold < (Homography.Basic.homographic matrix value).re ↔
      0 < (Geometry.Projective.Hermitian.realComparisonForm matrix threshold).eval value :=
  Order.PositiveScale.compare_gt_iff (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
    (Geometry.Projective.Hermitian.cleared_real_identity matrix threshold value denominatorNonzero)

/-- The homographic real coordinate is at least its threshold exactly when its comparison form is nonnegative.

The homographic denominator must be nonzero; its positive squared norm preserves the comparison when clearing the
denominator. -/
theorem real_homographic_ge_iff
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) (threshold :
      Fraction.Rational)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    threshold ≤ (Homography.Basic.homographic matrix value).re ↔
      0 ≤ (Geometry.Projective.Hermitian.realComparisonForm matrix threshold).eval value :=
  Order.PositiveScale.compare_ge_iff (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
    (Geometry.Projective.Hermitian.cleared_real_identity matrix threshold value denominatorNonzero)

/-- The homographic imaginary coordinate is strictly below its threshold exactly when its comparison form is negative.

The homographic denominator must be nonzero; its positive squared norm preserves the comparison when clearing the
denominator. -/
theorem imag_homographic_lt_iff
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) (threshold :
      Fraction.Rational)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    (Homography.Basic.homographic matrix value).im < threshold ↔
      (Geometry.Projective.Hermitian.imagComparisonForm matrix threshold).eval value < 0 :=
  Order.PositiveScale.compare_lt_iff (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
    (Geometry.Projective.Hermitian.cleared_imag_identity matrix threshold value denominatorNonzero)

/-- The homographic imaginary coordinate is at most its threshold exactly when its comparison form is nonpositive.

The homographic denominator must be nonzero; its positive squared norm preserves the comparison when clearing the
denominator. -/
theorem imag_homographic_le_iff
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) (threshold :
      Fraction.Rational)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    (Homography.Basic.homographic matrix value).im ≤ threshold ↔
      (Geometry.Projective.Hermitian.imagComparisonForm matrix threshold).eval value ≤ 0 :=
  Order.PositiveScale.compare_le_iff (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
    (Geometry.Projective.Hermitian.cleared_imag_identity matrix threshold value denominatorNonzero)

/-- The homographic imaginary coordinate is equal to its threshold exactly when its comparison form is zero.

The homographic denominator must be nonzero; its positive squared norm preserves the comparison when clearing the
denominator. -/
theorem imag_homographic_eq_iff
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) (threshold :
      Fraction.Rational)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    (Homography.Basic.homographic matrix value).im = threshold ↔
      (Geometry.Projective.Hermitian.imagComparisonForm matrix threshold).eval value = 0 :=
  Order.PositiveScale.compare_eq_iff (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
    (Geometry.Projective.Hermitian.cleared_imag_identity matrix threshold value denominatorNonzero)

/-- The homographic imaginary coordinate is strictly above its threshold exactly when its comparison form is positive.

The homographic denominator must be nonzero; its positive squared norm preserves the comparison when clearing the
denominator. -/
theorem imag_homographic_gt_iff
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) (threshold :
      Fraction.Rational)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    threshold < (Homography.Basic.homographic matrix value).im ↔
      0 < (Geometry.Projective.Hermitian.imagComparisonForm matrix threshold).eval value :=
  Order.PositiveScale.compare_gt_iff (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
    (Geometry.Projective.Hermitian.cleared_imag_identity matrix threshold value denominatorNonzero)

/-- The homographic imaginary coordinate is at least its threshold exactly when its comparison form is nonnegative.

The homographic denominator must be nonzero; its positive squared norm preserves the comparison when clearing the
denominator. -/
theorem imag_homographic_ge_iff
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) (threshold :
      Fraction.Rational)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    threshold ≤ (Homography.Basic.homographic matrix value).im ↔
      0 ≤ (Geometry.Projective.Hermitian.imagComparisonForm matrix threshold).eval value :=
  Order.PositiveScale.compare_ge_iff (Data.Gaussian.Norm.Basic.normSq_pos denominatorNonzero)
    (Geometry.Projective.Hermitian.cleared_imag_identity matrix threshold value denominatorNonzero)

end Purelib.Geometry.Projective.Hermitian

end

section
public section

/-!
# Finite descriptions of CCL atom boundaries

An unresolved Hermitian atom is useful to the equality-owner layer only when
its zero boundary retains constructive provenance.  The boundary is either a
rationally parameterized generalized circle/line, a finite explicit zero set,
or the identically-zero form.  This avoids recovering geometry from bare
coefficients by an unbounded search.
-/

namespace Purelib.Geometry.Projective.Hermitian

open Purelib

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates2.Matrix

/-- At zero threshold the norm comparison is the affine numerator norm form.

The denominator form has zero coefficient in every retained component, so
coefficient equality identifies the displayed affine norm form. -/
private theorem normComparison_zero_eq_affineNorm (matrix : GaussianMatrix) :
    Geometry.Projective.Hermitian.normComparisonForm matrix 0 = Hermitian.affineNormForm matrix.a matrix.b := by
  apply HermitianForm.ext <;>
    simp only [Geometry.Projective.Hermitian.normComparisonForm, HermitianForm.sub, Hermitian.HermitianForm.add,
      Hermitian.HermitianForm.neg, HermitianForm.scale, Hermitian.affineNormForm] <;>
    ring1

/-- The affine norm comparison agrees with the identity-matrix comparison.

The identity numerator and unit denominator retain the same squared norm
and rational threshold in all four Hermitian coefficients. -/
private theorem affineNormComparison_eq
    (threshold : Fraction.Rational) :
    Hermitian.affineNormComparisonForm threshold =
      Geometry.Projective.Hermitian.normComparisonForm Coordinates2.Matrix.identityMatrix threshold := by
  apply HermitianForm.ext <;>
    simp only [Hermitian.affineNormComparisonForm,
      Hermitian.constantForm, Geometry.Projective.Hermitian.normComparisonForm,
      HermitianForm.sub, Hermitian.HermitianForm.add, Hermitian.HermitianForm.neg,
      HermitianForm.scale, Hermitian.affineNormForm,
      Coordinates2.Matrix.identityMatrix, Data.Gaussian.Norm.Basic.normSq,
      Basic.one_re,
      Basic.one_im,
      Basic.zero_re,
      Basic.zero_im] <;>
    ring1
end Purelib.Geometry.Projective.Hermitian

end
