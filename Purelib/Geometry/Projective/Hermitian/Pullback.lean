module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Projective.Hermitian.Affine
import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Projective.Hermitian.Comparison
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Pulling finite CCL comparisons back to the original coordinate

Raw-parser predicates are stated at the current affine tail, whereas the
winding boxes live in the original polynomial coordinate.  This module
precomposes every Hermitian comparison with a finite decoder homography and
clears its denominator by a positive squared norm.  It also supplies the
explicit adjugate chart used to recover the unique parser tail.
-/

namespace Purelib.Geometry.Projective.Hermitian

/-- Clear the denominator after substituting one homography into a Hermitian form. -/
def pullbackForm (matrix : GaussianMatrix) (form :
  HermitianForm) : HermitianForm :=
  HermitianForm.add
    (HermitianForm.scale form.radial
      (affineNormForm matrix.a matrix.b))
    (HermitianForm.add
      (HermitianForm.scale form.realLinear
        (realCrossForm matrix.a matrix.b matrix.c matrix.d))
      (HermitianForm.add
        (HermitianForm.scale form.imagLinear
          (imagCrossForm matrix.a matrix.b matrix.c matrix.d))
        (HermitianForm.scale form.constant
          (affineNormForm matrix.c matrix.d))))

/-- Pulling back a Hermitian form commutes with negation. -/
@[simp] theorem pullbackForm_neg (matrix :
  GaussianMatrix) (form : HermitianForm) :
    pullbackForm matrix form.neg = (pullbackForm matrix
      form).neg := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, HermitianForm.neg, HermitianForm.add,
      HermitianForm.scale] <;>
    ring1

/-- Pulling back a squared affine norm composes its affine numerator with the homogeneous numerator and denominator of
the homography. -/
theorem pullbackForm_affineNorm (matrix :
  GaussianMatrix) (u v : Data.Gaussian.Basic.Canonical) :
    pullbackForm matrix (affineNormForm u v) =
      affineNormForm (u * matrix.a + v * matrix.c)
        (u * matrix.b + v * matrix.d) := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, HermitianForm.add, HermitianForm.scale,
      affineNormForm, realCrossForm, imagCrossForm,
        Basic.normSq, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
      Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im] <;>
    ring1

/-- Exact positive-factor pullback identity. -/
theorem eval_pullbackForm
    (matrix : GaussianMatrix) (form : HermitianForm) (value :
      Data.Gaussian.Basic.Canonical)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    (pullbackForm matrix form).eval value =
      Basic.normSq (Homography.Basic.denominator matrix value) *
        form.eval (Homography.Basic.homographic matrix value) := by
  have normIdentity :
      Basic.normSq (Homography.Basic.numerator matrix value) =
        Basic.normSq (Homography.Basic.denominator matrix value) *
          Basic.normSq (Homography.Basic.homographic matrix value) := by
    calc
      Basic.normSq (Homography.Basic.numerator matrix value) =
          (normComparisonForm matrix 0).eval value := by
        rw [eval_normComparisonForm]
        change Basic.normSq (Homography.Basic.numerator matrix value) =
          Basic.normSq (Homography.Basic.numerator matrix value) -
            0 * Basic.normSq (Homography.Basic.denominator matrix value)
        ring1
      _ = Basic.normSq (Homography.Basic.denominator matrix value) *
          (Basic.normSq (Homography.Basic.homographic matrix value) - 0) :=
        cleared_norm_identity matrix 0 value denominatorNonzero
      _ = Basic.normSq (Homography.Basic.denominator matrix value) *
          Basic.normSq (Homography.Basic.homographic matrix value) := by ring1
  have realIdentity :
      ((Homography.Basic.numerator matrix value) * Data.Gaussian.Basic.conj (Homography.Basic.denominator
        matrix value)).re =
        Basic.normSq (Homography.Basic.denominator matrix value) *
          (Homography.Basic.homographic matrix value).re := by
    change ((matrix.a * value + matrix.b) *
        Data.Gaussian.Basic.conj (matrix.c * value + matrix.d)).re =
      Basic.normSq (Homography.Basic.denominator matrix value) *
        (Homography.Basic.homographic matrix value).re
    calc
      ((matrix.a * value + matrix.b) *
          Data.Gaussian.Basic.conj (matrix.c * value + matrix.d)).re =
          (realComparisonForm matrix 0).eval value := by
        rw [eval_realComparisonForm]
        change _ = _ - 0 * Basic.normSq (Homography.Basic.denominator matrix value)
        ring1
      _ = Basic.normSq (Homography.Basic.denominator matrix value) *
          ((Homography.Basic.homographic matrix value).re - 0) :=
        cleared_real_identity matrix 0 value denominatorNonzero
      _ = Basic.normSq (Homography.Basic.denominator matrix value) *
          (Homography.Basic.homographic matrix value).re := by ring1
  have imagIdentity :
      ((Homography.Basic.numerator matrix value) * Data.Gaussian.Basic.conj (Homography.Basic.denominator
        matrix value)).im =
        Basic.normSq (Homography.Basic.denominator matrix value) *
          (Homography.Basic.homographic matrix value).im := by
    change ((matrix.a * value + matrix.b) *
        Data.Gaussian.Basic.conj (matrix.c * value + matrix.d)).im =
      Basic.normSq (Homography.Basic.denominator matrix value) *
        (Homography.Basic.homographic matrix value).im
    calc
      ((matrix.a * value + matrix.b) *
          Data.Gaussian.Basic.conj (matrix.c * value + matrix.d)).im =
          (imagComparisonForm matrix 0).eval value := by
        rw [eval_imagComparisonForm]
        change _ = _ - 0 * Basic.normSq (Homography.Basic.denominator matrix value)
        ring1
      _ = Basic.normSq (Homography.Basic.denominator matrix value) *
          ((Homography.Basic.homographic matrix value).im - 0) :=
        cleared_imag_identity matrix 0 value denominatorNonzero
      _ = Basic.normSq (Homography.Basic.denominator matrix value) *
          (Homography.Basic.homographic matrix value).im := by ring1
  simp only [pullbackForm, HermitianForm.eval_add,
    HermitianForm.eval_scale, eval_affineNormForm, eval_realCrossForm,
    eval_imagCrossForm]
  change form.radial * Basic.normSq (Homography.Basic.numerator matrix value) +
      (form.realLinear *
        ((Homography.Basic.numerator matrix value) * Data.Gaussian.Basic.conj (Homography.Basic.denominator
          matrix value)).re +
      (form.imagLinear *
        ((Homography.Basic.numerator matrix value) * Data.Gaussian.Basic.conj (Homography.Basic.denominator
          matrix value)).im +
      form.constant * Basic.normSq (Homography.Basic.denominator matrix value))) = _
  rw [normIdentity, realIdentity, imagIdentity]
  simp only [HermitianForm.eval]
  ring1

/-- Pulling back a norm comparison composes its decoder matrices. -/
theorem pullbackForm_normComparison
    (outer inner : GaussianMatrix) (radiusSq : Fraction.Rational) :
    pullbackForm inner (normComparisonForm outer radiusSq) =
      normComparisonForm (Coordinates2.Matrix.mul outer inner) radiusSq := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, normComparisonForm, HermitianForm.sub,
      HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
      affineNormForm, realCrossForm, imagCrossForm, Coordinates2.Matrix.mul,
        Basic.normSq,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im]
        <;>
    ring1

/-- Pulling back a real-coordinate comparison composes its matrices. -/
theorem pullbackForm_realComparison
    (outer inner : GaussianMatrix) (threshold : Fraction.Rational) :
    pullbackForm inner (realComparisonForm outer threshold) =
      realComparisonForm (Coordinates2.Matrix.mul outer inner) threshold := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, realComparisonForm, HermitianForm.sub,
      HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
      affineNormForm, realCrossForm, imagCrossForm, Coordinates2.Matrix.mul,
        Basic.normSq,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im]
        <;>
    ring1

/-- Pulling back an imaginary-coordinate comparison composes its matrices. -/
theorem pullbackForm_imagComparison
    (outer inner : GaussianMatrix) (threshold : Fraction.Rational) :
    pullbackForm inner (imagComparisonForm outer threshold) =
      imagComparisonForm (Coordinates2.Matrix.mul outer inner) threshold := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, imagComparisonForm, HermitianForm.sub,
      HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
      affineNormForm, realCrossForm, imagCrossForm, Coordinates2.Matrix.mul,
        Basic.normSq,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im]
        <;>
    ring1
end Purelib.Geometry.Projective.Hermitian

end

section
@[expose] public section

/-!
# Boundary provenance for finite CCL formulas

This module follows the syntax tree of each next-bit formula.  Every atom is
paired with a constructive description of its exact zero boundary.  Formula
inspection can therefore hand an unresolved atom directly to the finite
curve-event layer without guessing its geometric origin from coefficients.
-/

namespace Purelib.Geometry.Projective.Hermitian

/-- Pullback along the identity matrix preserves every Hermitian coefficient. -/
@[simp] public theorem pullbackForm_identity (form :
  HermitianForm) :
    pullbackForm Coordinates2.Matrix.identityMatrix form = form := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm,
      Coordinates2.Matrix.identityMatrix, HermitianForm.add, HermitianForm.scale,
      affineNormForm, realCrossForm, imagCrossForm,
        Basic.normSq,
      Data.Gaussian.Basic.one_re,
      Data.Gaussian.Basic.one_im,
      Data.Gaussian.Basic.zero_re,
      Data.Gaussian.Basic.zero_im] <;>
    ring1

end Purelib.Geometry.Projective.Hermitian

end
