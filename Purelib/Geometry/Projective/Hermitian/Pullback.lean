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
  Hermitian.HermitianForm) : Hermitian.HermitianForm :=
  HermitianForm.add
    (HermitianForm.scale form.radial
      (Hermitian.affineNormForm matrix.a matrix.b))
    (HermitianForm.add
      (HermitianForm.scale form.realLinear
        (Hermitian.realCrossForm matrix.a matrix.b matrix.c matrix.d))
      (HermitianForm.add
        (HermitianForm.scale form.imagLinear
          (Hermitian.imagCrossForm matrix.a matrix.b matrix.c matrix.d))
        (HermitianForm.scale form.constant
          (Hermitian.affineNormForm matrix.c matrix.d))))

/-- Pulling back a Hermitian form commutes with negation. -/
@[simp] theorem pullbackForm_neg (matrix :
  GaussianMatrix) (form : Hermitian.HermitianForm) :
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
    pullbackForm matrix (Hermitian.affineNormForm u v) =
      Hermitian.affineNormForm (u * matrix.a + v * matrix.c)
        (u * matrix.b + v * matrix.d) := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, HermitianForm.add, HermitianForm.scale,
      Hermitian.affineNormForm, Hermitian.realCrossForm, Hermitian.imagCrossForm,
        Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
      Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im] <;>
    ring1

/-- Exact positive-factor pullback identity. -/
theorem eval_pullbackForm
    (matrix : GaussianMatrix) (form : Hermitian.HermitianForm) (value :
      Data.Gaussian.Basic.Canonical)
    (denominatorNonzero : Homography.Basic.denominator matrix value ≠ 0) :
    (pullbackForm matrix form).eval value =
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
        form.eval (Homography.Basic.homographic matrix value) := by
  have normIdentity :
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix value) =
        Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
          Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix value) := by
    calc
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix value) =
          (Hermitian.normComparisonForm matrix 0).eval value := by
        rw [Hermitian.eval_normComparisonForm]
        change Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix value) =
          Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix value) -
            0 * Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value)
        ring1
      _ = Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
          (Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix value) - 0) :=
        Hermitian.cleared_norm_identity matrix 0 value denominatorNonzero
      _ = Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
          Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix value) := by ring1
  have realIdentity :
      ((Homography.Basic.numerator matrix value) * Data.Gaussian.Basic.conj (Homography.Basic.denominator
        matrix value)).re =
        Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
          (Homography.Basic.homographic matrix value).re := by
    change ((matrix.a * value + matrix.b) *
        Data.Gaussian.Basic.conj (matrix.c * value + matrix.d)).re =
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
        (Homography.Basic.homographic matrix value).re
    calc
      ((matrix.a * value + matrix.b) *
          Data.Gaussian.Basic.conj (matrix.c * value + matrix.d)).re =
          (Hermitian.realComparisonForm matrix 0).eval value := by
        rw [Hermitian.eval_realComparisonForm]
        change _ = _ - 0 * Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value)
        ring1
      _ = Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
          ((Homography.Basic.homographic matrix value).re - 0) :=
        Hermitian.cleared_real_identity matrix 0 value denominatorNonzero
      _ = Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
          (Homography.Basic.homographic matrix value).re := by ring1
  have imagIdentity :
      ((Homography.Basic.numerator matrix value) * Data.Gaussian.Basic.conj (Homography.Basic.denominator
        matrix value)).im =
        Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
          (Homography.Basic.homographic matrix value).im := by
    change ((matrix.a * value + matrix.b) *
        Data.Gaussian.Basic.conj (matrix.c * value + matrix.d)).im =
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
        (Homography.Basic.homographic matrix value).im
    calc
      ((matrix.a * value + matrix.b) *
          Data.Gaussian.Basic.conj (matrix.c * value + matrix.d)).im =
          (Hermitian.imagComparisonForm matrix 0).eval value := by
        rw [Hermitian.eval_imagComparisonForm]
        change _ = _ - 0 * Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value)
        ring1
      _ = Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
          ((Homography.Basic.homographic matrix value).im - 0) :=
        Hermitian.cleared_imag_identity matrix 0 value denominatorNonzero
      _ = Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value) *
          (Homography.Basic.homographic matrix value).im := by ring1
  simp only [pullbackForm, HermitianForm.eval_add,
    HermitianForm.eval_scale, Hermitian.eval_affineNormForm, Hermitian.eval_realCrossForm,
    Hermitian.eval_imagCrossForm]
  change form.radial * Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix value) +
      (form.realLinear *
        ((Homography.Basic.numerator matrix value) * Data.Gaussian.Basic.conj (Homography.Basic.denominator
          matrix value)).re +
      (form.imagLinear *
        ((Homography.Basic.numerator matrix value) * Data.Gaussian.Basic.conj (Homography.Basic.denominator
          matrix value)).im +
      form.constant * Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value))) = _
  rw [normIdentity, realIdentity, imagIdentity]
  simp only [HermitianForm.eval]
  ring1

/-- Pulling back a norm comparison composes its decoder matrices. -/
theorem pullbackForm_normComparison
    (outer inner : GaussianMatrix) (radiusSq : Fraction.Rational) :
    pullbackForm inner (Hermitian.normComparisonForm outer radiusSq) =
      Hermitian.normComparisonForm (Coordinates2.Matrix.mul outer inner) radiusSq := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, Hermitian.normComparisonForm, Hermitian.HermitianForm.sub,
      HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
      Hermitian.affineNormForm, Hermitian.realCrossForm, Hermitian.imagCrossForm, Coordinates2.Matrix.mul,
        Data.Gaussian.Norm.Basic.normSq,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im]
        <;>
    ring1

/-- Pulling back a real-coordinate comparison composes its matrices. -/
theorem pullbackForm_realComparison
    (outer inner : GaussianMatrix) (threshold : Fraction.Rational) :
    pullbackForm inner (Hermitian.realComparisonForm outer threshold) =
      Hermitian.realComparisonForm (Coordinates2.Matrix.mul outer inner) threshold := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, Hermitian.realComparisonForm, Hermitian.HermitianForm.sub,
      HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
      Hermitian.affineNormForm, Hermitian.realCrossForm, Hermitian.imagCrossForm, Coordinates2.Matrix.mul,
        Data.Gaussian.Norm.Basic.normSq,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im]
        <;>
    ring1

/-- Pulling back an imaginary-coordinate comparison composes its matrices. -/
theorem pullbackForm_imagComparison
    (outer inner : GaussianMatrix) (threshold : Fraction.Rational) :
    pullbackForm inner (Hermitian.imagComparisonForm outer threshold) =
      Hermitian.imagComparisonForm (Coordinates2.Matrix.mul outer inner) threshold := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, Hermitian.imagComparisonForm, Hermitian.HermitianForm.sub,
      HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
      Hermitian.affineNormForm, Hermitian.realCrossForm, Hermitian.imagCrossForm, Coordinates2.Matrix.mul,
        Data.Gaussian.Norm.Basic.normSq,
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
  Hermitian.HermitianForm) :
    pullbackForm Coordinates2.Matrix.identityMatrix form = form := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm,
      Coordinates2.Matrix.identityMatrix, HermitianForm.add, HermitianForm.scale,
      Hermitian.affineNormForm, Hermitian.realCrossForm, Hermitian.imagCrossForm,
        Data.Gaussian.Norm.Basic.normSq,
      Data.Gaussian.Basic.one_re,
      Data.Gaussian.Basic.one_im,
      Data.Gaussian.Basic.zero_re,
      Data.Gaussian.Basic.zero_im] <;>
    ring1

end Purelib.Geometry.Projective.Hermitian

end
