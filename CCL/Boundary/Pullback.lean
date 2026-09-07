import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.Geometry

/-!
# Pulling finite CCL comparisons back to the original coordinate

Raw-parser predicates are stated at the current affine tail, whereas the
winding boxes live in the original polynomial coordinate.  This module
precomposes every Hermitian comparison with a finite decoder homography and
clears its denominator by a positive squared norm.  It also supplies the
explicit adjugate chart used to recover the unique parser tail.
-/

namespace CCL.CCLPullback

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm

open RFAP.ConstructiveGaussian.Gaussian
open CCL.RawParser
open CCL.RawParserSemantics
open CCL.CCLGeometry

def determinant (matrix : Mat2) : Gaussian :=
  CCL.Chordal.Mat2.det matrix

/-- Explicit adjugate of a two-by-two constructive Gaussian matrix. -/
def adjugate (matrix : Mat2) : Mat2 :=
  ⟨matrix.d, -matrix.b, -matrix.c, matrix.a⟩

@[simp] theorem determinant_adjugate (matrix : Mat2) :
    determinant (adjugate matrix) = determinant matrix := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [determinant, adjugate, CCL.Chordal.Mat2.det,
      mul_re, mul_im, sub_re, sub_im, neg_re, neg_im] <;>
    ring1

/-- Clear the denominator after substituting one homography into a
Hermitian form. -/
def pullbackForm (matrix : Mat2) (form : HermitianForm) : HermitianForm :=
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

@[simp] theorem pullbackForm_neg (matrix : Mat2) (form : HermitianForm) :
    pullbackForm matrix form.neg = (pullbackForm matrix form).neg := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, HermitianForm.neg, HermitianForm.add,
      HermitianForm.scale] <;>
    ring1

/-- Pulling back a squared affine norm composes its affine numerator with
the homogeneous numerator and denominator of the homography. -/
theorem pullbackForm_affineNorm (matrix : Mat2) (u v : Gaussian) :
    pullbackForm matrix (affineNormForm u v) =
      affineNormForm (u * matrix.a + v * matrix.c)
        (u * matrix.b + v * matrix.d) := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, HermitianForm.add, HermitianForm.scale,
      affineNormForm, realCrossForm, imagCrossForm, normSq, mul_re, mul_im,
      add_re, add_im] <;>
    ring1

/-- Exact positive-factor pullback identity. -/
theorem eval_pullbackForm
    (matrix : Mat2) (form : HermitianForm) (value : Gaussian)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    (pullbackForm matrix form).eval value =
      normSq (denominator matrix value) *
        form.eval (homographic matrix value) := by
  have normIdentity :
      normSq (numerator matrix value) =
        normSq (denominator matrix value) *
          normSq (homographic matrix value) := by
    calc
      normSq (numerator matrix value) =
          (normComparisonForm matrix 0).eval value := by
        rw [eval_normComparisonForm]
        change normSq (numerator matrix value) =
          normSq (numerator matrix value) -
            0 * normSq (denominator matrix value)
        ring1
      _ = normSq (denominator matrix value) *
          (normSq (homographic matrix value) - 0) :=
        cleared_norm_identity matrix 0 value denominatorNonzero
      _ = normSq (denominator matrix value) *
          normSq (homographic matrix value) := by ring1
  have realIdentity :
      ((numerator matrix value) * conj (denominator matrix value)).re =
        normSq (denominator matrix value) *
          (homographic matrix value).re := by
    change ((matrix.a * value + matrix.b) *
        conj (matrix.c * value + matrix.d)).re =
      normSq (denominator matrix value) *
        (homographic matrix value).re
    calc
      ((matrix.a * value + matrix.b) *
          conj (matrix.c * value + matrix.d)).re =
          (realComparisonForm matrix 0).eval value := by
        rw [eval_realComparisonForm]
        change _ = _ - 0 * normSq (denominator matrix value)
        ring1
      _ = normSq (denominator matrix value) *
          ((homographic matrix value).re - 0) :=
        cleared_real_identity matrix 0 value denominatorNonzero
      _ = normSq (denominator matrix value) *
          (homographic matrix value).re := by ring1
  have imagIdentity :
      ((numerator matrix value) * conj (denominator matrix value)).im =
        normSq (denominator matrix value) *
          (homographic matrix value).im := by
    change ((matrix.a * value + matrix.b) *
        conj (matrix.c * value + matrix.d)).im =
      normSq (denominator matrix value) *
        (homographic matrix value).im
    calc
      ((matrix.a * value + matrix.b) *
          conj (matrix.c * value + matrix.d)).im =
          (imagComparisonForm matrix 0).eval value := by
        rw [eval_imagComparisonForm]
        change _ = _ - 0 * normSq (denominator matrix value)
        ring1
      _ = normSq (denominator matrix value) *
          ((homographic matrix value).im - 0) :=
        cleared_imag_identity matrix 0 value denominatorNonzero
      _ = normSq (denominator matrix value) *
          (homographic matrix value).im := by ring1
  simp only [pullbackForm, HermitianForm.eval_add,
    HermitianForm.eval_scale, eval_affineNormForm, eval_realCrossForm,
    eval_imagCrossForm]
  change form.radial * normSq (numerator matrix value) +
      (form.realLinear *
        ((numerator matrix value) * conj (denominator matrix value)).re +
      (form.imagLinear *
        ((numerator matrix value) * conj (denominator matrix value)).im +
      form.constant * normSq (denominator matrix value))) = _
  rw [normIdentity, realIdentity, imagIdentity]
  simp only [HermitianForm.eval]
  ring1

/-- Pulling back a norm comparison composes its decoder matrices. -/
theorem pullbackForm_normComparison
    (outer inner : Mat2) (radiusSq : Coordinate) :
    pullbackForm inner (normComparisonForm outer radiusSq) =
      normComparisonForm (CCL.Mat2.mul outer inner) radiusSq := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, normComparisonForm, HermitianForm.sub,
      HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
      affineNormForm, realCrossForm, imagCrossForm, CCL.Mat2.mul, normSq,
      mul_re, mul_im, add_re, add_im] <;>
    ring1

/-- Pulling back a real-coordinate comparison composes its matrices. -/
theorem pullbackForm_realComparison
    (outer inner : Mat2) (threshold : Coordinate) :
    pullbackForm inner (realComparisonForm outer threshold) =
      realComparisonForm (CCL.Mat2.mul outer inner) threshold := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, realComparisonForm, HermitianForm.sub,
      HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
      affineNormForm, realCrossForm, imagCrossForm, CCL.Mat2.mul, normSq,
      mul_re, mul_im, add_re, add_im] <;>
    ring1

/-- Pulling back an imaginary-coordinate comparison composes its matrices. -/
theorem pullbackForm_imagComparison
    (outer inner : Mat2) (threshold : Coordinate) :
    pullbackForm inner (imagComparisonForm outer threshold) =
      imagComparisonForm (CCL.Mat2.mul outer inner) threshold := by
  apply HermitianForm.ext <;>
    simp only [pullbackForm, imagComparisonForm, HermitianForm.sub,
      HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
      affineNormForm, realCrossForm, imagCrossForm, CCL.Mat2.mul, normSq,
      mul_re, mul_im, add_re, add_im] <;>
    ring1

/-- Multiplying a decoder by its adjugate gives its determinant scalar. -/
theorem mul_adjugate (matrix : Mat2) :
    CCL.Mat2.mul matrix (adjugate matrix) =
      ⟨determinant matrix, 0, 0, determinant matrix⟩ := by
  apply CCL.Mat2.ext <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [CCL.Mat2.mul, adjugate, determinant,
        CCL.Chordal.Mat2.det, mul_re, mul_im, add_re, add_im,
        sub_re, sub_im, neg_re, neg_im, zero_re, zero_im] <;>
      ring1

/-- The reverse product gives the same determinant scalar. -/
theorem adjugate_mul (matrix : Mat2) :
    CCL.Mat2.mul (adjugate matrix) matrix =
      ⟨determinant matrix, 0, 0, determinant matrix⟩ := by
  apply CCL.Mat2.ext <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [CCL.Mat2.mul, adjugate, determinant,
        CCL.Chordal.Mat2.det, mul_re, mul_im, add_re, add_im,
        sub_re, sub_im, neg_re, neg_im, zero_re, zero_im] <;>
      ring1

/-- An invertible forward homography has a nonzero adjugate denominator at
every affine image in its domain. -/
theorem adjugate_denominator_homographic_ne
    (matrix : Mat2) (input : Gaussian)
    (determinantNonzero : determinant matrix ≠ 0)
    (denominatorNonzero : denominator matrix input ≠ 0) :
    denominator (adjugate matrix) (homographic matrix input) ≠ 0 := by
  have productDenominator :
      denominator (CCL.Mat2.mul (adjugate matrix) matrix) input ≠ 0 := by
    rw [adjugate_mul]
    simpa only [denominator,
      RFAP.ConstructiveGaussian.Gaussian.zero_mul,
      RFAP.ConstructiveGaussian.Gaussian.zero_add,
      RFAP.ConstructiveGaussian.Gaussian.add_zero] using determinantNonzero
  exact (denominator_mul_ne_iff (adjugate matrix) matrix input
    denominatorNonzero).1 productDenominator

/-- Applying a decoder and then its adjugate recovers the affine input. -/
theorem homographic_adjugate_forward_inverse
    (matrix : Mat2) (input : Gaussian)
    (determinantNonzero : determinant matrix ≠ 0)
    (denominatorNonzero : denominator matrix input ≠ 0) :
    homographic (adjugate matrix) (homographic matrix input) = input := by
  have inverseDenominator := adjugate_denominator_homographic_ne matrix input
    determinantNonzero denominatorNonzero
  calc
    homographic (adjugate matrix) (homographic matrix input) =
        homographic (CCL.Mat2.mul (adjugate matrix) matrix) input :=
      (homographic_mul (adjugate matrix) matrix input denominatorNonzero
        inverseDenominator).symm
    _ = input := by
      rw [adjugate_mul]
      unfold homographic numerator denominator
      rw [RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.zero_add,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
      calc
        determinant matrix * input * (determinant matrix)⁻¹ =
            input * (determinant matrix * (determinant matrix)⁻¹) := by
          rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm
              (determinant matrix) input,
            RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
        _ = input := by
          rw [inv_eq,
            RFAP.ConstructiveGaussian.Gaussian.mul_inv _ determinantNonzero,
            RFAP.ConstructiveGaussian.Gaussian.mul_one]

/-- The inverse chart's nonzero denominator forces the recovered forward
denominator to be nonzero. -/
theorem denominator_inverse_tail_ne
    (matrix : Mat2) (input : Gaussian)
    (determinantNonzero : determinant matrix ≠ 0)
    (inverseDenominator : denominator (adjugate matrix) input ≠ 0) :
    denominator matrix (homographic (adjugate matrix) input) ≠ 0 := by
  have productDenominator :
      denominator (CCL.Mat2.mul matrix (adjugate matrix)) input ≠ 0 := by
    rw [mul_adjugate]
    simpa only [denominator,
      RFAP.ConstructiveGaussian.Gaussian.zero_mul,
      RFAP.ConstructiveGaussian.Gaussian.zero_add,
      RFAP.ConstructiveGaussian.Gaussian.add_zero] using determinantNonzero
  exact (denominator_mul_ne_iff matrix (adjugate matrix) input
    inverseDenominator).1 productDenominator

/-- Decoding the adjugate tail returns the original affine input. -/
theorem homographic_adjugate_inverse
    (matrix : Mat2) (input : Gaussian)
    (determinantNonzero : determinant matrix ≠ 0)
    (inverseDenominator : denominator (adjugate matrix) input ≠ 0) :
    homographic matrix (homographic (adjugate matrix) input) = input := by
  have forwardDenominator := denominator_inverse_tail_ne matrix input
    determinantNonzero inverseDenominator
  calc
    homographic matrix (homographic (adjugate matrix) input) =
        homographic (CCL.Mat2.mul matrix (adjugate matrix)) input :=
      (homographic_mul matrix (adjugate matrix) input inverseDenominator
        forwardDenominator).symm
    _ = input := by
      rw [mul_adjugate]
      unfold homographic numerator denominator
      rw [RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.zero_add,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
      calc
        determinant matrix * input * (determinant matrix)⁻¹ =
            input * (determinant matrix * (determinant matrix)⁻¹) := by
          rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm
              (determinant matrix) input,
            RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
        _ = input := by
          rw [inv_eq,
            RFAP.ConstructiveGaussian.Gaussian.mul_inv _ determinantNonzero,
            RFAP.ConstructiveGaussian.Gaussian.mul_one]

/-- Build a parser representation directly from a point satisfying the state
predicate in inverse-decoder coordinates. -/
theorem represents_of_inverse_tail
    (state : State) (input : Gaussian)
    (determinantNonzero : determinant state.matrix ≠ 0)
    (inverseDenominator : denominator (adjugate state.matrix) input ≠ 0)
    (holds : state.Holds (homographic (adjugate state.matrix) input)) :
    Represents state input (homographic (adjugate state.matrix) input) := by
  refine ⟨denominator_inverse_tail_ne state.matrix input
      determinantNonzero inverseDenominator, ?_, holds⟩
  exact (homographic_adjugate_inverse state.matrix input determinantNonzero
    inverseDenominator).symm

end CCL.CCLPullback
