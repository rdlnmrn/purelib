import FTA.CCLPathIntersection
import FTA.CCLOwnerDirection
import FTA.CCLParserGeometry
import FTA.CCLBoundaryPath

/-!
# Parser formulas along projective branch paths

To assign a CCL equality owner on one parameter cell, every Hermitian atom
must be evaluated along the cell's projective circle or line.  This module
clears the positive projective denominator and produces an exact rational
polynomial for each atom.  The resulting Boolean evaluator is proved equal to
the original parser formula at every affine path parameter.
-/

namespace FTA
namespace CCLFormulaPath

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.ProjectivePath
open FTA.CCLGeometry
open FTA.CCLOwnerDirection
open FTA.CCLParserGeometry
open FTA.CCLPathIntersection
open FTA.RationalPolynomialBounds
open FTA.SturmTransducer

abbrev QI := CCL.GaussianRat
abbrev RatPolynomial := DensePolynomial ℚ
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

/-- Squared norm of the homogeneous numerator. -/
def numeratorNorm (path : Path) : RatPolynomial :=
  numeratorReal path * numeratorReal path +
    numeratorImag path * numeratorImag path

@[simp] theorem eval_numeratorNorm (path : Path) (t : ℚ) :
    (numeratorNorm path).eval t =
      normSq (path.numerator.eval (PathPolynomial.ofRat t)) := by
  simp [numeratorNorm, normSq]
  ring

/-- Denominator-cleared substitution of a Hermitian form along a projective
path.  It is a rational polynomial in the path parameter. -/
def clearedForm (form : HermitianForm) (path : Path) : RatPolynomial :=
  DensePolynomial.scale form.radial (numeratorNorm path) +
    DensePolynomial.scale form.realLinear (affineRealNumerator path) +
    DensePolynomial.scale form.imagLinear (affineImagNumerator path) +
    DensePolynomial.scale form.constant (denominatorNorm path)

/-- Exact denominator-clearing identity. -/
theorem eval_clearedForm
    (form : HermitianForm) (path : Path) (t : ℚ)
    (denominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    (clearedForm form path).eval t =
      (denominatorNorm path).eval t * form.eval (path.value t) := by
  let numerator := path.numerator.eval (PathPolynomial.ofRat t)
  let denominatorValue := path.denominator.eval (PathPolynomial.ofRat t)
  have denominatorNormPositive := eval_denominatorNorm_pos path t denominator
  have denominatorNormNonzero :
      (denominatorNorm path).eval t ≠ 0 := denominatorNormPositive.ne'
  have normIdentity :
      (denominatorNorm path).eval t * normSq (path.value t) =
        (numeratorNorm path).eval t := by
    rw [eval_denominatorNorm, eval_numeratorNorm]
    change normSq denominatorValue * normSq (numerator * inv denominatorValue) =
      normSq numerator
    rw [normSq_mul, normSq_inv denominatorValue denominator]
    have denominatorValueNormNonzero : normSq denominatorValue ≠ 0 :=
      (normSq_pos denominator).ne'
    field_simp [denominatorValueNormNonzero]
  have realIdentity :
      (denominatorNorm path).eval t * (path.value t).re =
        (affineRealNumerator path).eval t := by
    rw [path_value_re path t denominator]
    field_simp [denominatorNormNonzero]
  have imagIdentity :
      (denominatorNorm path).eval t * (path.value t).im =
        (affineImagNumerator path).eval t := by
    rw [path_value_im path t denominator]
    field_simp [denominatorNormNonzero]
  simp only [clearedForm, eval_add, eval_scale, HermitianForm.eval]
  rw [← normIdentity, ← realIdentity, ← imagIdentity]
  ring

/-- Cleared norm comparison as a difference of its numerator and denominator
norm forms. -/
theorem toPolynomial_clearedForm_normComparison
    (matrix : Mat2 QI) (radius : ℚ) (path : Path) :
    (clearedForm (normComparisonForm matrix radius) path).toPolynomial =
      (clearedForm (affineNormForm matrix.a matrix.b) path).toPolynomial -
        Polynomial.C radius *
          (clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial := by
  simp only [clearedForm, normComparisonForm, HermitianForm.sub,
    HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
    toPolynomial_add, toPolynomial_scale, Polynomial.C_add,
    Polynomial.C_neg, Polynomial.C_mul]
  ring

/-- Cleared real comparison as its cross form minus the threshold-scaled
homography denominator. -/
theorem toPolynomial_clearedForm_realComparison
    (matrix : Mat2 QI) (threshold : ℚ) (path : Path) :
    (clearedForm (realComparisonForm matrix threshold) path).toPolynomial =
      (clearedForm (realCrossForm matrix.a matrix.b matrix.c matrix.d)
          path).toPolynomial -
        Polynomial.C threshold *
          (clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial := by
  simp only [clearedForm, realComparisonForm, HermitianForm.sub,
    HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
    toPolynomial_add, toPolynomial_scale, Polynomial.C_add,
    Polynomial.C_neg, Polynomial.C_mul]
  ring

/-- Imaginary-coordinate counterpart of the preceding decomposition. -/
theorem toPolynomial_clearedForm_imagComparison
    (matrix : Mat2 QI) (threshold : ℚ) (path : Path) :
    (clearedForm (imagComparisonForm matrix threshold) path).toPolynomial =
      (clearedForm (imagCrossForm matrix.a matrix.b matrix.c matrix.d)
          path).toPolynomial -
        Polynomial.C threshold *
          (clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial := by
  simp only [clearedForm, imagComparisonForm, HermitianForm.sub,
    HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
    toPolynomial_add, toPolynomial_scale, Polynomial.C_add,
    Polynomial.C_neg, Polynomial.C_mul]
  ring

/-- Clearing is linear under rational scaling of a Hermitian form. -/
theorem toPolynomial_clearedForm_scale
    (scaleValue : ℚ) (form : HermitianForm) (path : Path) :
    (clearedForm (HermitianForm.scale scaleValue form) path).toPolynomial =
      Polynomial.C scaleValue * (clearedForm form path).toPolynomial := by
  simp only [clearedForm, HermitianForm.scale, toPolynomial_add,
    toPolynomial_scale, Polynomial.C_mul]
  ring

/-- A nonzero rational form scaling is a polynomial unit, so divisibility of
the scaled cleared form is equivalent to divisibility of the original one. -/
theorem dvd_clearedForm_of_dvd_scale
    {factor : Polynomial ℚ} (scaleValue : ℚ) (form : HermitianForm)
    (path : Path) (scaleNonzero : scaleValue ≠ 0)
    (divides : factor ∣
      (clearedForm (HermitianForm.scale scaleValue form) path).toPolynomial) :
    factor ∣ (clearedForm form path).toPolynomial := by
  rw [toPolynomial_clearedForm_scale] at divides
  rcases divides with ⟨quotient, quotientIdentity⟩
  refine ⟨Polynomial.C scaleValue⁻¹ * quotient, ?_⟩
  calc
    (clearedForm form path).toPolynomial =
        Polynomial.C scaleValue⁻¹ *
          (Polynomial.C scaleValue *
            (clearedForm form path).toPolynomial) := by
      calc
        (clearedForm form path).toPolynomial =
            1 * (clearedForm form path).toPolynomial := by simp
        _ = (Polynomial.C scaleValue⁻¹ * Polynomial.C scaleValue) *
            (clearedForm form path).toPolynomial := by
          rw [← Polynomial.C_mul]
          simp [scaleNonzero]
        _ = Polynomial.C scaleValue⁻¹ *
            (Polynomial.C scaleValue *
              (clearedForm form path).toPolynomial) := by
          ring
    _ = Polynomial.C scaleValue⁻¹ * (factor * quotient) := by
      rw [quotientIdentity]
    _ = factor * (Polynomial.C scaleValue⁻¹ * quotient) := by ring

/-- Clearing an affine norm along a projective path is exactly the norm of
the corresponding homogeneous affine numerator. -/
theorem eval_clearedForm_affineNorm
    (u v : QI) (path : Path) (parameter : ℚ) :
    (clearedForm (affineNormForm u v) path).eval parameter =
      normSq
        (u * path.numerator.eval (PathPolynomial.ofRat parameter) +
          v * path.denominator.eval (PathPolynomial.ofRat parameter)) := by
  simp only [clearedForm, eval_add, eval_scale, affineNormForm,
    eval_numeratorNorm, eval_affineRealNumerator,
    eval_affineImagNumerator, eval_denominatorNorm, normSq, mul_re, mul_im,
    add_re, add_im, conj]
  ring

/-- A constant affine numerator clears to its squared norm times the
projective denominator norm. -/
theorem toPolynomial_clearedForm_affineNorm_zero_linear
    (v : QI) (path : Path) :
    (clearedForm (affineNormForm 0 v) path).toPolynomial =
      Polynomial.C (normSq v) * (denominatorNorm path).toPolynomial := by
  simp only [clearedForm, affineNormForm, normSq, zero_re, zero_im,
    toPolynomial_add, toPolynomial_scale]
  simp

/-- Pointwise homogeneous interpretation of a cleared real cross form. -/
theorem eval_clearedForm_realCross
    (u v s t : QI) (path : Path) (parameter : ℚ) :
    (clearedForm (realCrossForm u v s t) path).eval parameter =
      ((u * path.numerator.eval (PathPolynomial.ofRat parameter) +
          v * path.denominator.eval (PathPolynomial.ofRat parameter)) *
        conj
          (s * path.numerator.eval (PathPolynomial.ofRat parameter) +
            t * path.denominator.eval
              (PathPolynomial.ofRat parameter))).re := by
  simp only [clearedForm, eval_add, eval_scale, realCrossForm,
    eval_numeratorNorm, eval_affineRealNumerator,
    eval_affineImagNumerator, eval_denominatorNorm, normSq, mul_re, mul_im,
    add_re, add_im, conj]
  ring

/-- Pointwise homogeneous interpretation of a cleared imaginary cross form. -/
theorem eval_clearedForm_imagCross
    (u v s t : QI) (path : Path) (parameter : ℚ) :
    (clearedForm (imagCrossForm u v s t) path).eval parameter =
      ((u * path.numerator.eval (PathPolynomial.ofRat parameter) +
          v * path.denominator.eval (PathPolynomial.ofRat parameter)) *
        conj
          (s * path.numerator.eval (PathPolynomial.ofRat parameter) +
            t * path.denominator.eval
              (PathPolynomial.ofRat parameter))).im := by
  simp only [clearedForm, eval_add, eval_scale, imagCrossForm,
    eval_numeratorNorm, eval_affineRealNumerator,
    eval_affineImagNumerator, eval_denominatorNorm, normSq, mul_re, mul_im,
    add_re, add_im, conj]
  ring

/-- Applying a matrix lower row after its adjugate homogeneous action cancels
to the determinant times the original denominator coordinate. -/
theorem lowerRow_adjugate_homogeneous
    (matrix : Mat2 QI) (numerator denominator : QI) :
    matrix.c *
          ((adjugate matrix).a * numerator +
            (adjugate matrix).b * denominator) +
        matrix.d *
          ((adjugate matrix).c * numerator +
            (adjugate matrix).d * denominator) =
      determinant matrix * denominator := by
  apply GaussianRat.ext <;>
    simp only [adjugate, determinant, mul_re, mul_im, add_re, add_im,
      sub_re, sub_im, neg_re, neg_im] <;>
    ring

/-- The upper row of a matrix composed with its adjugate similarly recovers
the determinant times the original homogeneous numerator coordinate. -/
theorem upperRow_adjugate_homogeneous
    (matrix : Mat2 QI) (numerator denominator : QI) :
    matrix.a *
          ((adjugate matrix).a * numerator +
            (adjugate matrix).b * denominator) +
        matrix.b *
          ((adjugate matrix).c * numerator +
            (adjugate matrix).d * denominator) =
      determinant matrix * numerator := by
  apply GaussianRat.ext <;>
    simp only [adjugate, determinant, mul_re, mul_im, add_re, add_im,
      sub_re, sub_im, neg_re, neg_im] <;>
    ring

private theorem eval_clearedForm_realComparison
    (matrix : Mat2 QI) (threshold : ℚ) (path : Path) (parameter : ℚ) :
    (clearedForm (realComparisonForm matrix threshold) path).eval parameter =
      (clearedForm (realCrossForm matrix.a matrix.b matrix.c matrix.d)
          path).eval parameter -
        threshold *
          (clearedForm (affineNormForm matrix.c matrix.d) path).eval
            parameter := by
  have identity := congrArg (Polynomial.eval parameter)
    (toPolynomial_clearedForm_realComparison matrix threshold path)
  simpa only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    eval_toPolynomial] using identity

private theorem eval_clearedForm_imagComparison
    (matrix : Mat2 QI) (threshold : ℚ) (path : Path) (parameter : ℚ) :
    (clearedForm (imagComparisonForm matrix threshold) path).eval parameter =
      (clearedForm (imagCrossForm matrix.a matrix.b matrix.c matrix.d)
          path).eval parameter -
        threshold *
          (clearedForm (affineNormForm matrix.c matrix.d) path).eval
            parameter := by
  have identity := congrArg (Polynomial.eval parameter)
    (toPolynomial_clearedForm_imagComparison matrix threshold path)
  simpa only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    eval_toPolynomial] using identity

/-- A real-coordinate comparison pulled back along its own inverse decoder
reduces, after clearing, to the corresponding standard homogeneous line
comparison times the squared determinant. -/
theorem eval_clearedForm_realComparison_actPath_adjugate
    (matrix : Mat2 QI) (threshold : ℚ) (path : Path) (parameter : ℚ) :
    (clearedForm (realComparisonForm matrix threshold)
        (CCLBoundaryPath.actPath (adjugate matrix) path)).eval parameter =
      normSq (determinant matrix) *
        (((path.numerator.eval (PathPolynomial.ofRat parameter) *
            conj (path.denominator.eval
              (PathPolynomial.ofRat parameter)))).re -
          threshold * normSq (path.denominator.eval
            (PathPolynomial.ofRat parameter))) := by
  rw [eval_clearedForm_realComparison, eval_clearedForm_realCross,
    eval_clearedForm_affineNorm]
  simp only [CCLBoundaryPath.actPath, eval_add, eval_scale]
  rw [upperRow_adjugate_homogeneous, lowerRow_adjugate_homogeneous,
    normSq_mul]
  simp only [normSq, mul_re, mul_im, conj]
  ring

/-- Imaginary-coordinate counterpart of the same inverse-decoder
cancellation. -/
theorem eval_clearedForm_imagComparison_actPath_adjugate
    (matrix : Mat2 QI) (threshold : ℚ) (path : Path) (parameter : ℚ) :
    (clearedForm (imagComparisonForm matrix threshold)
        (CCLBoundaryPath.actPath (adjugate matrix) path)).eval parameter =
      normSq (determinant matrix) *
        (((path.numerator.eval (PathPolynomial.ofRat parameter) *
            conj (path.denominator.eval
              (PathPolynomial.ofRat parameter)))).im -
          threshold * normSq (path.denominator.eval
            (PathPolynomial.ofRat parameter))) := by
  rw [eval_clearedForm_imagComparison, eval_clearedForm_imagCross,
    eval_clearedForm_affineNorm]
  simp only [CCLBoundaryPath.actPath, eval_add, eval_scale]
  rw [upperRow_adjugate_homogeneous, lowerRow_adjugate_homogeneous,
    normSq_mul]
  simp only [normSq, mul_re, mul_im, conj]
  ring

private theorem natDegree_le_one_of_eval_eq_linear
    (polynomial : RatPolynomial) (nonzero : polynomial.isZero = false)
    (a b : ℚ) (evaluation : ∀ parameter : ℚ,
      polynomial.eval parameter = a * parameter + b) :
    polynomial.natDegree ≤ 1 := by
  have sparseEquality : polynomial.toPolynomial =
      Polynomial.C a * Polynomial.X + Polynomial.C b := by
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    rw [eval_toPolynomial, evaluation]
    simp
  rw [← natDegree_toPolynomial nonzero, sparseEquality]
  exact Polynomial.natDegree_linear_le

/-- Every nonzero coordinate comparison restricted to either same-decoder
real-line chart is at most affine in the rational chart parameter. -/
theorem clearedForm_realComparison_inverseReal_natDegree_le_one
    (matrix : Mat2 QI) (comparisonThreshold sourceThreshold : ℚ)
    (nonzero : (clearedForm (realComparisonForm matrix comparisonThreshold)
      (CCLBoundaryPath.inverseRealBoundaryPath matrix sourceThreshold)).isZero =
        false) :
    (clearedForm (realComparisonForm matrix comparisonThreshold)
      (CCLBoundaryPath.inverseRealBoundaryPath matrix sourceThreshold)).natDegree ≤
        1 := by
  apply natDegree_le_one_of_eval_eq_linear _ nonzero 0
    (normSq (determinant matrix) * (sourceThreshold - comparisonThreshold))
  intro parameter
  rw [CCLBoundaryPath.inverseRealBoundaryPath,
    CCLBoundaryPath.inverseLinePath,
    eval_clearedForm_realComparison_actPath_adjugate,
    CCLBoundaryPath.linePath_numerator,
    CCLBoundaryPath.linePath_denominator]
  simp only [CCLGeometry.ofRat, normSq, conj, mul_re, mul_im, add_re,
    add_im, one_re, one_im]
  ring

theorem clearedForm_imagComparison_inverseReal_natDegree_le_one
    (matrix : Mat2 QI) (comparisonThreshold sourceThreshold : ℚ)
    (nonzero : (clearedForm (imagComparisonForm matrix comparisonThreshold)
      (CCLBoundaryPath.inverseRealBoundaryPath matrix sourceThreshold)).isZero =
        false) :
    (clearedForm (imagComparisonForm matrix comparisonThreshold)
      (CCLBoundaryPath.inverseRealBoundaryPath matrix sourceThreshold)).natDegree ≤
        1 := by
  apply natDegree_le_one_of_eval_eq_linear _ nonzero
    (normSq (determinant matrix))
    (-normSq (determinant matrix) * comparisonThreshold)
  intro parameter
  rw [CCLBoundaryPath.inverseRealBoundaryPath,
    CCLBoundaryPath.inverseLinePath,
    eval_clearedForm_imagComparison_actPath_adjugate,
    CCLBoundaryPath.linePath_numerator,
    CCLBoundaryPath.linePath_denominator]
  simp only [CCLGeometry.ofRat, normSq, conj, mul_re, mul_im, add_re,
    add_im, one_re, one_im]
  ring

theorem clearedForm_realComparison_inverseImag_natDegree_le_one
    (matrix : Mat2 QI) (comparisonThreshold sourceThreshold : ℚ)
    (nonzero : (clearedForm (realComparisonForm matrix comparisonThreshold)
      (CCLBoundaryPath.inverseImagBoundaryPath matrix sourceThreshold)).isZero =
        false) :
    (clearedForm (realComparisonForm matrix comparisonThreshold)
      (CCLBoundaryPath.inverseImagBoundaryPath matrix sourceThreshold)).natDegree ≤
        1 := by
  apply natDegree_le_one_of_eval_eq_linear _ nonzero
    (normSq (determinant matrix))
    (-normSq (determinant matrix) * comparisonThreshold)
  intro parameter
  rw [CCLBoundaryPath.inverseImagBoundaryPath,
    CCLBoundaryPath.inverseLinePath,
    eval_clearedForm_realComparison_actPath_adjugate,
    CCLBoundaryPath.linePath_numerator,
    CCLBoundaryPath.linePath_denominator]
  simp only [CCLGeometry.ofRat, normSq, conj, mul_re, mul_im, add_re,
    add_im, one_re, one_im]
  ring

theorem clearedForm_imagComparison_inverseImag_natDegree_le_one
    (matrix : Mat2 QI) (comparisonThreshold sourceThreshold : ℚ)
    (nonzero : (clearedForm (imagComparisonForm matrix comparisonThreshold)
      (CCLBoundaryPath.inverseImagBoundaryPath matrix sourceThreshold)).isZero =
        false) :
    (clearedForm (imagComparisonForm matrix comparisonThreshold)
      (CCLBoundaryPath.inverseImagBoundaryPath matrix sourceThreshold)).natDegree ≤
        1 := by
  apply natDegree_le_one_of_eval_eq_linear _ nonzero 0
    (normSq (determinant matrix) * (sourceThreshold - comparisonThreshold))
  intro parameter
  rw [CCLBoundaryPath.inverseImagBoundaryPath,
    CCLBoundaryPath.inverseLinePath,
    eval_clearedForm_imagComparison_actPath_adjugate,
    CCLBoundaryPath.linePath_numerator,
    CCLBoundaryPath.linePath_denominator]
  simp only [CCLGeometry.ofRat, normSq, conj, mul_re, mul_im, add_re,
    add_im, one_re, one_im]
  ring

/-- Along an adjugate-transformed projective path, the cleared forward
homography denominator is the determinant norm times the original projective
denominator norm. -/
theorem eval_clearedForm_lowerRow_actPath_adjugate
    (matrix : Mat2 QI) (path : Path) (parameter : ℚ) :
    (clearedForm (affineNormForm matrix.c matrix.d)
        (CCLBoundaryPath.actPath (adjugate matrix) path)).eval parameter =
      normSq (determinant matrix) * (denominatorNorm path).eval parameter := by
  rw [eval_clearedForm_affineNorm]
  simp only [CCLBoundaryPath.actPath, eval_add, eval_scale]
  rw [lowerRow_adjugate_homogeneous, normSq_mul, eval_denominatorNorm]

/-- The numerator/denominator norm product is the sum of the squared real and
imaginary cross forms, after any projective-path clearing. -/
theorem cleared_affineNorm_cross_identity
    (matrix : Mat2 QI) (path : Path) :
    (clearedForm (affineNormForm matrix.a matrix.b) path *
        clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial =
      (clearedForm (realCrossForm matrix.a matrix.b matrix.c matrix.d) path *
          clearedForm (realCrossForm matrix.a matrix.b matrix.c matrix.d) path +
        clearedForm (imagCrossForm matrix.a matrix.b matrix.c matrix.d) path *
          clearedForm (imagCrossForm matrix.a matrix.b matrix.c matrix.d)
            path).toPolynomial := by
  apply rationalPolynomial_eq_of_eval_eq_on_fin
  intro i
  simp only [eval_toPolynomial, eval_mul, eval_add,
    eval_clearedForm_affineNorm, eval_clearedForm_realCross,
    eval_clearedForm_imagCross]
  simp only [normSq, mul_re, mul_im, conj]
  ring

/-- Homogeneous coordinate identity for a norm boundary and two coordinate
boundaries through the same homography.  It is stated after projective-path
clearing so common event factors can be eliminated without realizing an
algebraic root. -/
theorem cleared_normComparison_coordinate_identity
    (matrix : Mat2 QI) (radius realThreshold imagThreshold : ℚ)
    (path : Path) :
    (clearedForm (normComparisonForm matrix radius) path *
        clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial =
      (clearedForm (realComparisonForm matrix realThreshold) path *
          clearedForm (realComparisonForm matrix realThreshold) path +
        clearedForm (imagComparisonForm matrix imagThreshold) path *
          clearedForm (imagComparisonForm matrix imagThreshold) path +
        DensePolynomial.scale (2 * realThreshold)
          (clearedForm (affineNormForm matrix.c matrix.d) path *
            clearedForm (realComparisonForm matrix realThreshold) path) +
        DensePolynomial.scale (2 * imagThreshold)
          (clearedForm (affineNormForm matrix.c matrix.d) path *
            clearedForm (imagComparisonForm matrix imagThreshold) path) +
        DensePolynomial.scale
          (realThreshold ^ 2 + imagThreshold ^ 2 - radius)
          (clearedForm (affineNormForm matrix.c matrix.d) path *
            clearedForm (affineNormForm matrix.c matrix.d) path)).toPolynomial := by
  simp only [toPolynomial_mul, toPolynomial_add, toPolynomial_scale]
  rw [toPolynomial_clearedForm_normComparison,
    toPolynomial_clearedForm_realComparison,
    toPolynomial_clearedForm_imagComparison]
  let numerator :=
    (clearedForm (affineNormForm matrix.a matrix.b) path).toPolynomial
  let denominator :=
    (clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial
  let realCross :=
    (clearedForm (realCrossForm matrix.a matrix.b matrix.c matrix.d)
      path).toPolynomial
  let imagCross :=
    (clearedForm (imagCrossForm matrix.a matrix.b matrix.c matrix.d)
      path).toPolynomial
  change (numerator - Polynomial.C radius * denominator) * denominator =
    (realCross - Polynomial.C realThreshold * denominator) *
        (realCross - Polynomial.C realThreshold * denominator) +
      (imagCross - Polynomial.C imagThreshold * denominator) *
        (imagCross - Polynomial.C imagThreshold * denominator) +
      Polynomial.C (2 * realThreshold) *
        (denominator *
          (realCross - Polynomial.C realThreshold * denominator)) +
      Polynomial.C (2 * imagThreshold) *
        (denominator *
          (imagCross - Polynomial.C imagThreshold * denominator)) +
      Polynomial.C (realThreshold ^ 2 + imagThreshold ^ 2 - radius) *
        (denominator * denominator)
  have crossIdentity : numerator * denominator =
      realCross * realCross + imagCross * imagCross := by
    simpa only [numerator, denominator, realCross, imagCross,
      toPolynomial_mul, toPolynomial_add] using
        cleared_affineNorm_cross_identity matrix path
  calc
    (numerator - Polynomial.C radius * denominator) * denominator =
        numerator * denominator -
          Polynomial.C radius * (denominator * denominator) := by ring
    _ = realCross * realCross + imagCross * imagCross -
          Polynomial.C radius * (denominator * denominator) := by
      rw [crossIdentity]
    _ = (realCross - Polynomial.C realThreshold * denominator) *
          (realCross - Polynomial.C realThreshold * denominator) +
        (imagCross - Polynomial.C imagThreshold * denominator) *
          (imagCross - Polynomial.C imagThreshold * denominator) +
        Polynomial.C (2 * realThreshold) *
          (denominator *
            (realCross - Polynomial.C realThreshold * denominator)) +
        Polynomial.C (2 * imagThreshold) *
          (denominator *
            (imagCross - Polynomial.C imagThreshold * denominator)) +
        Polynomial.C (realThreshold ^ 2 + imagThreshold ^ 2 - radius) *
          (denominator * denominator) := by
      simp only [Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul,
        Polynomial.C_pow, Polynomial.C_ofNat]
      ring

/-- A nonzero rational constant polynomial can be cancelled from the right
side of a divisibility target. -/
theorem dvd_of_dvd_C_mul
    {factor polynomial : Polynomial ℚ} (constant : ℚ)
    (constantNonzero : constant ≠ 0)
    (divides : factor ∣ Polynomial.C constant * polynomial) :
    factor ∣ polynomial := by
  rcases divides with ⟨quotient, quotientIdentity⟩
  refine ⟨Polynomial.C constant⁻¹ * quotient, ?_⟩
  calc
    polynomial = 1 * polynomial := by simp
    _ = (Polynomial.C constant⁻¹ * Polynomial.C constant) *
        polynomial := by
      rw [← Polynomial.C_mul]
      simp [constantNonzero]
    _ = Polynomial.C constant⁻¹ *
        (Polynomial.C constant * polynomial) := by ring
    _ = Polynomial.C constant⁻¹ * (factor * quotient) := by
      rw [quotientIdentity]
    _ = factor * (Polynomial.C constant⁻¹ * quotient) := by ring

/-- Polynomial cancellation form of the homogeneous radial/coordinate
identity: a common divisor of the norm comparison and both coordinate
comparisons divides the squared homography denominator whenever the corner
radius differs from the radial radius. -/
theorem dvd_clearedDenominator_square_of_norm_real_imag
    (factor : Polynomial ℚ) (matrix : Mat2 QI)
    (radius realThreshold imagThreshold : ℚ) (path : Path)
    (radiusGapNonzero :
      realThreshold ^ 2 + imagThreshold ^ 2 - radius ≠ 0)
    (normDivides : factor ∣
      (clearedForm (normComparisonForm matrix radius) path).toPolynomial)
    (realDivides : factor ∣
      (clearedForm
        (realComparisonForm matrix realThreshold) path).toPolynomial)
    (imagDivides : factor ∣
      (clearedForm
        (imagComparisonForm matrix imagThreshold) path).toPolynomial) :
    factor ∣
      (clearedForm (affineNormForm matrix.c matrix.d) path *
        clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial := by
  let normPolynomial :=
    (clearedForm (normComparisonForm matrix radius) path).toPolynomial
  let realPolynomial :=
    (clearedForm (realComparisonForm matrix realThreshold) path).toPolynomial
  let imagPolynomial :=
    (clearedForm (imagComparisonForm matrix imagThreshold) path).toPolynomial
  let denominatorPolynomial :=
    (clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial
  have identity :
      normPolynomial * denominatorPolynomial =
        realPolynomial * realPolynomial + imagPolynomial * imagPolynomial +
          Polynomial.C (2 * realThreshold) *
            (denominatorPolynomial * realPolynomial) +
          Polynomial.C (2 * imagThreshold) *
            (denominatorPolynomial * imagPolynomial) +
          Polynomial.C
              (realThreshold ^ 2 + imagThreshold ^ 2 - radius) *
            (denominatorPolynomial * denominatorPolynomial) := by
    simpa only [normPolynomial, realPolynomial, imagPolynomial,
      denominatorPolynomial, toPolynomial_mul, toPolynomial_add,
      toPolynomial_scale] using
        cleared_normComparison_coordinate_identity matrix radius
          realThreshold imagThreshold path
  have fullDivides : factor ∣
      realPolynomial * realPolynomial + imagPolynomial * imagPolynomial +
        Polynomial.C (2 * realThreshold) *
          (denominatorPolynomial * realPolynomial) +
        Polynomial.C (2 * imagThreshold) *
          (denominatorPolynomial * imagPolynomial) +
        Polynomial.C
            (realThreshold ^ 2 + imagThreshold ^ 2 - radius) *
          (denominatorPolynomial * denominatorPolynomial) := by
    rw [← identity]
    exact dvd_mul_of_dvd_left normDivides denominatorPolynomial
  have baseDivides : factor ∣
      realPolynomial * realPolynomial + imagPolynomial * imagPolynomial +
        Polynomial.C (2 * realThreshold) *
          (denominatorPolynomial * realPolynomial) +
        Polynomial.C (2 * imagThreshold) *
          (denominatorPolynomial * imagPolynomial) := by
    apply dvd_add
    · apply dvd_add
      · apply dvd_add
        · exact dvd_mul_of_dvd_left realDivides realPolynomial
        · exact dvd_mul_of_dvd_left imagDivides imagPolynomial
      · exact dvd_mul_of_dvd_right
          (dvd_mul_of_dvd_right realDivides denominatorPolynomial) _
    · exact dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_right imagDivides denominatorPolynomial) _
  have gapProductDivides : factor ∣
      Polynomial.C (realThreshold ^ 2 + imagThreshold ^ 2 - radius) *
        (denominatorPolynomial * denominatorPolynomial) := by
    have difference := dvd_sub fullDivides baseDivides
    simpa only [add_sub_cancel_left] using difference
  have denominatorSquareDivides : factor ∣
      denominatorPolynomial * denominatorPolynomial :=
    dvd_of_dvd_C_mul
      (realThreshold ^ 2 + imagThreshold ^ 2 - radius)
      radiusGapNonzero gapProductDivides
  simpa only [denominatorPolynomial, toPolynomial_mul] using
    denominatorSquareDivides

/-! ## Cleared owner slopes -/

/-- Projective-denominator-cleared first coordinate of a Hermitian gradient
along a branch path. -/
def clearedGradientX (form : HermitianForm) (path : Path) : RatPolynomial :=
  DensePolynomial.scale (2 * form.radial) (affineRealNumerator path) +
    DensePolynomial.scale form.realLinear (denominatorNorm path)

/-- Projective-denominator-cleared second coordinate of a Hermitian gradient
along a branch path. -/
def clearedGradientY (form : HermitianForm) (path : Path) : RatPolynomial :=
  DensePolynomial.scale (2 * form.radial) (affineImagNumerator path) +
    DensePolynomial.scale form.imagLinear (denominatorNorm path)

/-- Projectively cleared form of the bilinear gradient-pairing identity. -/
theorem clearedGradient_pairing_identity
    (left right : HermitianForm) (path : Path) :
    (clearedGradientX left path * clearedGradientX right path +
        clearedGradientY left path * clearedGradientY right path).toPolynomial =
      (DensePolynomial.scale (2 * right.radial)
          (clearedForm left path * denominatorNorm path) +
        DensePolynomial.scale (2 * left.radial)
          (clearedForm right path * denominatorNorm path) +
        DensePolynomial.scale (gradientPairingConstant left right)
          (denominatorNorm path * denominatorNorm path)).toPolynomial := by
  simp only [clearedForm, clearedGradientX, clearedGradientY,
    numeratorNorm, affineRealNumerator, affineImagNumerator, denominatorNorm,
    gradientPairingConstant, toPolynomial_add, toPolynomial_sub,
    toPolynomial_mul, toPolynomial_scale, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_add, Polynomial.C_ofNat]
  ring

/-- Projectively cleared squared-gradient identity for one Hermitian form. -/
theorem clearedGradient_norm_identity
    (form : HermitianForm) (path : Path) :
    (clearedGradientX form path * clearedGradientX form path +
        clearedGradientY form path * clearedGradientY form path).toPolynomial =
      (DensePolynomial.scale (4 * form.radial)
          (clearedForm form path * denominatorNorm path) -
        DensePolynomial.scale (boundaryDiscriminant form)
          (denominatorNorm path * denominatorNorm path)).toPolynomial := by
  simp only [clearedForm, clearedGradientX, clearedGradientY,
    numeratorNorm, affineRealNumerator, affineImagNumerator, denominatorNorm,
    boundaryDiscriminant, toPolynomial_add, toPolynomial_sub,
    toPolynomial_mul, toPolynomial_scale, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_ofNat, map_pow]
  ring

/-- If the pairing obstruction vanishes and an event factor divides both
cleared boundary forms, it also divides their cleared gradient dot product. -/
theorem dvd_clearedGradient_pairing_of_constant_zero
    (left right : HermitianForm) (path : Path) (factor : Polynomial ℚ)
    (constantZero : gradientPairingConstant left right = 0)
    (leftDivides : factor ∣ (clearedForm left path).toPolynomial)
    (rightDivides : factor ∣ (clearedForm right path).toPolynomial) :
    factor ∣
      (clearedGradientX left path * clearedGradientX right path +
        clearedGradientY left path * clearedGradientY right path).toPolynomial := by
  rw [clearedGradient_pairing_identity, constantZero]
  simp only [toPolynomial_add, toPolynomial_mul, toPolynomial_scale,
    Polynomial.C_0, MulZeroClass.zero_mul, _root_.add_zero]
  apply dvd_add
  · exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left leftDivides
        (denominatorNorm path).toPolynomial) _
  · exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left rightDivides
        (denominatorNorm path).toPolynomial) _

/-- Exact clearing identity for the first gradient coordinate. -/
theorem eval_clearedGradientX
    (form : HermitianForm) (path : Path) (t : ℚ)
    (denominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    (clearedGradientX form path).eval t =
      (denominatorNorm path).eval t * gradientX form (path.value t) := by
  have denominatorNormPositive := eval_denominatorNorm_pos path t denominator
  have denominatorNormNonzero :
      (denominatorNorm path).eval t ≠ 0 := denominatorNormPositive.ne'
  have realIdentity :
      (denominatorNorm path).eval t * (path.value t).re =
        (affineRealNumerator path).eval t := by
    rw [path_value_re path t denominator]
    field_simp [denominatorNormNonzero]
  simp only [clearedGradientX, eval_add, eval_scale, gradientX]
  rw [← realIdentity]
  ring

/-- Exact clearing identity for the second gradient coordinate. -/
theorem eval_clearedGradientY
    (form : HermitianForm) (path : Path) (t : ℚ)
    (denominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    (clearedGradientY form path).eval t =
      (denominatorNorm path).eval t * gradientY form (path.value t) := by
  have denominatorNormPositive := eval_denominatorNorm_pos path t denominator
  have denominatorNormNonzero :
      (denominatorNorm path).eval t ≠ 0 := denominatorNormPositive.ne'
  have imagIdentity :
      (denominatorNorm path).eval t * (path.value t).im =
        (affineImagNumerator path).eval t := by
    rw [path_value_im path t denominator]
    field_simp [denominatorNormNonzero]
  simp only [clearedGradientY, eval_add, eval_scale, gradientY]
  rw [← imagIdentity]
  ring

/-- Cleared directional slope for one of the finite rational grid directions. -/
def clearedDirectionalSlope
    (form : HermitianForm) (path : Path) (direction : QI) : RatPolynomial :=
  DensePolynomial.scale direction.re (clearedGradientX form path) +
    DensePolynomial.scale direction.im (clearedGradientY form path)

@[simp] theorem toPolynomial_clearedDirectionalSlope_neg
    (form : HermitianForm) (path : Path) (direction : QI) :
    (clearedDirectionalSlope form path (-direction)).toPolynomial =
      -(clearedDirectionalSlope form path direction).toPolynomial := by
  simp [clearedDirectionalSlope, toPolynomial_add, toPolynomial_scale,
    toPolynomial_neg]
  ring

/-- The cleared slope has the sign of the genuine planar directional
derivative because the projective denominator norm is strictly positive. -/
theorem eval_clearedDirectionalSlope
    (form : HermitianForm) (path : Path) (direction : QI) (t : ℚ)
    (denominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    (clearedDirectionalSlope form path direction).eval t =
      (denominatorNorm path).eval t *
        directionalSlope form (path.value t) direction := by
  simp only [clearedDirectionalSlope, eval_add, eval_scale, directionalSlope]
  rw [eval_clearedGradientX form path t denominator,
    eval_clearedGradientY form path t denominator]
  ring

/-- Polynomial form of the Hermitian gradient-discriminant identity after
projective denominator clearing.  Unlike the pointwise affine statement,
this identity remains valid at projective denominator zeros as an exact
coefficient equality. -/
theorem clearedGradient_discriminant_identity
    (form : HermitianForm) (path : Path) :
    (DensePolynomial.scale (4 * form.radial)
        (clearedForm form path * denominatorNorm path)).toPolynomial =
      (clearedGradientX form path * clearedGradientX form path +
        clearedGradientY form path * clearedGradientY form path +
          DensePolynomial.scale (boundaryDiscriminant form)
            (denominatorNorm path * denominatorNorm path)).toPolynomial := by
  simp only [clearedForm, clearedGradientX, clearedGradientY,
    numeratorNorm, affineRealNumerator, affineImagNumerator, denominatorNorm,
    boundaryDiscriminant, toPolynomial_add, toPolynomial_sub,
    toPolynomial_mul, toPolynomial_scale, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_ofNat]
  ring

@[simp] theorem toPolynomial_clearedDirectionalSlope_east
    (form : HermitianForm) (path : Path) :
    (clearedDirectionalSlope form path ⟨1, 0⟩).toPolynomial =
      (clearedGradientX form path).toPolynomial := by
  simp [clearedDirectionalSlope, toPolynomial_add, toPolynomial_normalize]

@[simp] theorem toPolynomial_clearedDirectionalSlope_west
    (form : HermitianForm) (path : Path) :
    (clearedDirectionalSlope form path ⟨-1, 0⟩).toPolynomial =
      -(clearedGradientX form path).toPolynomial := by
  simp [clearedDirectionalSlope, toPolynomial_add, toPolynomial_neg]

@[simp] theorem toPolynomial_clearedDirectionalSlope_north
    (form : HermitianForm) (path : Path) :
    (clearedDirectionalSlope form path ⟨0, 1⟩).toPolynomial =
      (clearedGradientY form path).toPolynomial := by
  simp [clearedDirectionalSlope, toPolynomial_add, toPolynomial_normalize]

@[simp] theorem toPolynomial_clearedDirectionalSlope_south
    (form : HermitianForm) (path : Path) :
    (clearedDirectionalSlope form path ⟨0, -1⟩).toPolynomial =
      -(clearedGradientY form path).toPolynomial := by
  simp [clearedDirectionalSlope, toPolynomial_add, toPolynomial_neg]

@[simp] theorem toPolynomial_clearedDirectionalSlope_northEast
    (form : HermitianForm) (path : Path) :
    (clearedDirectionalSlope form path ⟨1 / 2, 1 / 2⟩).toPolynomial =
      Polynomial.C (1 / 2 : ℚ) *
        ((clearedGradientX form path).toPolynomial +
          (clearedGradientY form path).toPolynomial) := by
  simp only [clearedDirectionalSlope, toPolynomial_add, toPolynomial_scale]
  norm_num
  ring

@[simp] theorem toPolynomial_clearedDirectionalSlope_southEast
    (form : HermitianForm) (path : Path) :
    (clearedDirectionalSlope form path ⟨1 / 2, -1 / 2⟩).toPolynomial =
      Polynomial.C (1 / 2 : ℚ) *
        ((clearedGradientX form path).toPolynomial -
          (clearedGradientY form path).toPolynomial) := by
  simp only [clearedDirectionalSlope, toPolynomial_add, toPolynomial_scale]
  norm_num
  ring

/-- If an event factor lies on two Hermitian boundaries, it divides the
exact compass-table obstruction obtained by adding the invariant angle-gap
term to the four failed axis/diagonal product terms. -/
theorem dvd_compass_angleGap_identity
    (left right : HermitianForm) (path : Path) (factor : Polynomial ℚ)
    (leftDivides : factor ∣ (clearedForm left path).toPolynomial)
    (rightDivides : factor ∣ (clearedForm right path).toPolynomial) :
    factor ∣
      (DensePolynomial.scale
          (boundaryDiscriminant left * boundaryDiscriminant right -
            2 * gradientPairingConstant left right ^ 2)
          ((denominatorNorm path * denominatorNorm path) *
            (denominatorNorm path * denominatorNorm path)) +
        (DensePolynomial.scale 4
            ((clearedDirectionalSlope left path ⟨1, 0⟩ *
                clearedDirectionalSlope right path ⟨1, 0⟩) *
              (clearedDirectionalSlope left path ⟨0, 1⟩ *
                clearedDirectionalSlope right path ⟨0, 1⟩)) +
          DensePolynomial.scale 16
            ((clearedDirectionalSlope left path ⟨1 / 2, 1 / 2⟩ *
                clearedDirectionalSlope right path ⟨1 / 2, 1 / 2⟩) *
              (clearedDirectionalSlope left path ⟨1 / 2, -1 / 2⟩ *
                clearedDirectionalSlope right path ⟨1 / 2, -1 / 2⟩)))).toPolynomial := by
  have leftScaledDivides : factor ∣
      (DensePolynomial.scale (4 * left.radial)
        (clearedForm left path * denominatorNorm path)).toPolynomial := by
    simp only [toPolynomial_scale, toPolynomial_mul]
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left leftDivides
        (denominatorNorm path).toPolynomial) _
  have rightScaledDivides : factor ∣
      (DensePolynomial.scale (4 * right.radial)
        (clearedForm right path * denominatorNorm path)).toPolynomial := by
    simp only [toPolynomial_scale, toPolynomial_mul]
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left rightDivides
        (denominatorNorm path).toPolynomial) _
  have leftSumDivides : factor ∣
      (clearedGradientX left path * clearedGradientX left path +
        clearedGradientY left path * clearedGradientY left path +
        DensePolynomial.scale (boundaryDiscriminant left)
          (denominatorNorm path * denominatorNorm path)).toPolynomial := by
    rw [← clearedGradient_discriminant_identity]
    exact leftScaledDivides
  have rightSumDivides : factor ∣
      (clearedGradientX right path * clearedGradientX right path +
        clearedGradientY right path * clearedGradientY right path +
        DensePolynomial.scale (boundaryDiscriminant right)
          (denominatorNorm path * denominatorNorm path)).toPolynomial := by
    rw [← clearedGradient_discriminant_identity]
    exact rightScaledDivides
  have pairingDifferenceDivides : factor ∣
      (clearedGradientX left path * clearedGradientX right path +
          clearedGradientY left path * clearedGradientY right path -
        DensePolynomial.scale (gradientPairingConstant left right)
          (denominatorNorm path * denominatorNorm path)).toPolynomial := by
    have leftTerm : factor ∣
        (DensePolynomial.scale (2 * right.radial)
          (clearedForm left path * denominatorNorm path)).toPolynomial := by
      simp only [toPolynomial_scale, toPolynomial_mul]
      exact dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_left leftDivides
          (denominatorNorm path).toPolynomial) _
    have rightTerm : factor ∣
        (DensePolynomial.scale (2 * left.radial)
          (clearedForm right path * denominatorNorm path)).toPolynomial := by
      simp only [toPolynomial_scale, toPolynomial_mul]
      exact dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_left rightDivides
          (denominatorNorm path).toPolynomial) _
    have errorDivides := dvd_add leftTerm rightTerm
    simp only [toPolynomial_sub]
    rw [clearedGradient_pairing_identity]
    convert errorDivides using 1
    all_goals
      simp only [toPolynomial_add, toPolynomial_scale, toPolynomial_mul]
    all_goals ring
  simp only [toPolynomial_add, toPolynomial_mul, toPolynomial_scale] at leftSumDivides rightSumDivides
  simp only [toPolynomial_add, toPolynomial_sub, toPolynomial_mul,
    toPolynomial_scale] at pairingDifferenceDivides
  let denominator := (denominatorNorm path).toPolynomial
  let denominatorSq := denominator * denominator
  let leftX := (clearedGradientX left path).toPolynomial
  let leftY := (clearedGradientY left path).toPolynomial
  let rightX := (clearedGradientX right path).toPolynomial
  let rightY := (clearedGradientY right path).toPolynomial
  let leftNorm := leftX * leftX + leftY * leftY
  let rightNorm := rightX * rightX + rightY * rightY
  let pairing := leftX * rightX + leftY * rightY
  let leftDiscriminantTerm :=
    Polynomial.C (boundaryDiscriminant left) * denominatorSq
  let rightDiscriminantTerm :=
    Polynomial.C (boundaryDiscriminant right) * denominatorSq
  let leftBase := -leftDiscriminantTerm
  let rightBase := -rightDiscriminantTerm
  let pairingBase :=
    Polynomial.C (gradientPairingConstant left right) * denominatorSq
  change factor ∣ leftNorm + leftDiscriminantTerm at leftSumDivides
  change factor ∣ rightNorm + rightDiscriminantTerm at rightSumDivides
  change factor ∣ pairing - pairingBase at pairingDifferenceDivides
  have leftCongruence : factor ∣ leftNorm - leftBase := by
    convert leftSumDivides using 1
    all_goals dsimp only [leftBase]
    all_goals ring
  have rightCongruence : factor ∣ rightNorm - rightBase := by
    convert rightSumDivides using 1
    all_goals dsimp only [rightBase]
    all_goals ring
  have pairingCongruence : factor ∣ pairing - pairingBase :=
    pairingDifferenceDivides
  have mulCongruence (first firstBase second secondBase : Polynomial ℚ)
      (firstCongruence : factor ∣ first - firstBase)
      (secondCongruence : factor ∣ second - secondBase) :
      factor ∣ first * second - firstBase * secondBase := by
    have firstTerm := dvd_mul_of_dvd_left firstCongruence second
    have secondTerm := dvd_mul_of_dvd_right secondCongruence firstBase
    have sum := dvd_add firstTerm secondTerm
    convert sum using 1
    all_goals ring
  have normProductCongruence : factor ∣
      leftNorm * rightNorm - leftBase * rightBase :=
    mulCongruence leftNorm leftBase rightNorm rightBase leftCongruence
      rightCongruence
  have pairingSquareCongruence : factor ∣
      pairing * pairing - pairingBase * pairingBase :=
    mulCongruence pairing pairingBase pairing pairingBase pairingCongruence
      pairingCongruence
  have twicePairingCongruence : factor ∣
      2 * (pairing * pairing) - 2 * (pairingBase * pairingBase) := by
    have scaled := dvd_mul_of_dvd_right pairingSquareCongruence
      (Polynomial.C (2 : ℚ))
    simpa only [Polynomial.C_ofNat, mul_sub] using scaled
  have angleCongruence : factor ∣
      (leftNorm * rightNorm - 2 * (pairing * pairing)) -
        Polynomial.C
            (boundaryDiscriminant left * boundaryDiscriminant right -
              2 * gradientPairingConstant left right ^ 2) *
          (denominatorSq * denominatorSq) := by
    have difference := dvd_sub normProductCongruence twicePairingCongruence
    have coefficientIdentity :
        Polynomial.C
            (boundaryDiscriminant left * boundaryDiscriminant right -
              2 * gradientPairingConstant left right ^ 2) =
          Polynomial.C (boundaryDiscriminant left) *
              Polynomial.C (boundaryDiscriminant right) -
            2 * (Polynomial.C (gradientPairingConstant left right) ^ 2) := by
      simp only [Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow,
        Polynomial.C_ofNat]
    rw [coefficientIdentity]
    convert difference using 1
    all_goals
      dsimp only [leftBase, rightBase, leftDiscriminantTerm,
        rightDiscriminantTerm, pairingBase]
    all_goals ring
  have diagonalCoefficient :
      Polynomial.C (16 : ℚ) * Polynomial.C (1 / 2 : ℚ) ^ 4 =
        (1 : Polynomial ℚ) := by
    rw [← Polynomial.C_pow, ← Polynomial.C_mul]
    norm_num
  have diagonalScaling (a b c d : Polynomial ℚ) :
      Polynomial.C (16 : ℚ) *
          (((Polynomial.C (1 / 2 : ℚ) * a) *
              (Polynomial.C (1 / 2 : ℚ) * b)) *
            ((Polynomial.C (1 / 2 : ℚ) * c) *
              (Polynomial.C (1 / 2 : ℚ) * d))) =
        a * b * c * d := by
    calc
      _ = (Polynomial.C (16 : ℚ) *
            Polynomial.C (1 / 2 : ℚ) ^ 4) * (a * b * c * d) := by
          ring
      _ = a * b * c * d := by
          rw [diagonalCoefficient]
          ring
  have compassIdentity :
      (DensePolynomial.scale
          (boundaryDiscriminant left * boundaryDiscriminant right -
            2 * gradientPairingConstant left right ^ 2)
          ((denominatorNorm path * denominatorNorm path) *
            (denominatorNorm path * denominatorNorm path)) +
        (DensePolynomial.scale 4
            ((clearedDirectionalSlope left path ⟨1, 0⟩ *
                clearedDirectionalSlope right path ⟨1, 0⟩) *
              (clearedDirectionalSlope left path ⟨0, 1⟩ *
                clearedDirectionalSlope right path ⟨0, 1⟩)) +
          DensePolynomial.scale 16
            ((clearedDirectionalSlope left path ⟨1 / 2, 1 / 2⟩ *
                clearedDirectionalSlope right path ⟨1 / 2, 1 / 2⟩) *
              (clearedDirectionalSlope left path ⟨1 / 2, -1 / 2⟩ *
                clearedDirectionalSlope right path ⟨1 / 2, -1 / 2⟩)))).toPolynomial =
        -((leftNorm * rightNorm - 2 * (pairing * pairing)) -
          Polynomial.C
              (boundaryDiscriminant left * boundaryDiscriminant right -
                2 * gradientPairingConstant left right ^ 2) *
            (denominatorSq * denominatorSq)) := by
    simp only [toPolynomial_add, toPolynomial_scale, toPolynomial_mul]
    rw [toPolynomial_clearedDirectionalSlope_east,
      toPolynomial_clearedDirectionalSlope_east,
      toPolynomial_clearedDirectionalSlope_north,
      toPolynomial_clearedDirectionalSlope_north,
      toPolynomial_clearedDirectionalSlope_northEast,
      toPolynomial_clearedDirectionalSlope_northEast,
      toPolynomial_clearedDirectionalSlope_southEast,
      toPolynomial_clearedDirectionalSlope_southEast]
    rw [diagonalScaling]
    dsimp only [leftNorm, rightNorm, pairing, leftX, leftY, rightX, rightY,
      denominatorSq, denominator]
    simp only [Polynomial.C_ofNat]
    ring
  rw [compassIdentity]
  exact dvd_neg.mpr angleCongruence

private theorem SignTest.holds_mul_pos_iff
    (test : SignTest) (factor value : ℚ) (positive : 0 < factor) :
    test.Holds (factor * value) ↔ test.Holds value := by
  cases test <;> simp only [SignTest.Holds]
  · constructor <;> intro h <;> nlinarith
  · constructor <;> intro h <;> nlinarith
  · simp [positive.ne']
  · simp [positive.ne']
  · constructor <;> intro h <;> nlinarith
  · constructor <;> intro h <;> nlinarith

/-- Cleared univariate sign test corresponding to one Hermitian atom. -/
def atomPathHolds (atom : Atom) (path : Path) (t : ℚ) : Prop :=
  atom.sign.Holds ((clearedForm atom.form path).eval t)

instance (atom : Atom) (path : Path) (t : ℚ) :
    Decidable (atomPathHolds atom path t) := by
  unfold atomPathHolds
  infer_instance

theorem atomPathHolds_iff
    (atom : Atom) (path : Path) (t : ℚ)
    (denominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    atomPathHolds atom path t ↔ atom.Holds (path.value t) := by
  rw [atomPathHolds, Atom.Holds,
    eval_clearedForm atom.form path t denominator]
  exact SignTest.holds_mul_pos_iff atom.sign _ _
    (eval_denominatorNorm_pos path t denominator)

/-- Fully executable evaluation of a parser formula after projective
denominator clearing. -/
def pathEvalBool : Formula → Path → ℚ → Bool
  | .truth, _, _ => true
  | .falsity, _, _ => false
  | .atom atom, path, t => decide (atomPathHolds atom path t)
  | .and left right, path, t =>
      pathEvalBool left path t && pathEvalBool right path t
  | .or left right, path, t =>
      pathEvalBool left path t || pathEvalBool right path t

theorem pathEvalBool_eq_true_iff
    (formula : Formula) (path : Path) (t : ℚ)
    (denominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    pathEvalBool formula path t = true ↔
      formula.Holds (path.value t) := by
  induction formula with
  | truth => simp [pathEvalBool, Formula.Holds]
  | falsity => simp [pathEvalBool, Formula.Holds]
  | atom atom =>
      simp only [pathEvalBool, decide_eq_true_eq, Formula.Holds]
      exact atomPathHolds_iff atom path t denominator
  | and left right leftInduction rightInduction =>
      simp [pathEvalBool, Formula.Holds,
        leftInduction, rightInduction]
  | or left right leftInduction rightInduction =>
      simp [pathEvalBool, Formula.Holds,
        leftInduction, rightInduction]

/-- Finite list of every cleared atom polynomial needed to stabilize a
formula on a parameter cell. -/
def pathPolynomials : Formula → Path → List RatPolynomial
  | .truth, _ | .falsity, _ => []
  | .atom atom, path => [clearedForm atom.form path]
  | .and left right, path | .or left right, path =>
      pathPolynomials left path ++ pathPolynomials right path

/-! ## Whole parameter-cell formula stability -/

/-- Finite list of atoms, retaining both each form and its sign test. -/
def formulaAtoms : Formula → List Atom
  | .truth | .falsity => []
  | .atom atom => [atom]
  | .and left right | .or left right =>
      formulaAtoms left ++ formulaAtoms right

/-- A cleared atom polynomial is either identically zero or has one strict
sign throughout the parameter cell. -/
inductive PolynomialStatus
    (polynomial : RatPolynomial) (interval : RationalInterval) where
  | zero (isZero : polynomial.isZero = true)
  | strict
      (certificate : IntervalSignCertificate polynomial
        interval.lower interval.upper)

/-- Direct finite attempt to classify one polynomial on a cell.  Failure only
means that another finite subdivision is required. -/
def polynomialStatus?
    (polynomial : RatPolynomial) (interval : RationalInterval)
    (proper : interval.Proper) : Option (PolynomialStatus polynomial interval) := by
  if zero : polynomial.isZero = true then
    exact some (.zero zero)
  else
    match midpointSignCertificate? polynomial interval.lower interval.upper
        proper with
    | none => exact none
    | some certificate => exact some (.strict certificate)

private theorem SignTest.holds_iff_of_mul_pos
    (test : SignTest) {left right : ℚ}
    (sameSign : 0 < left * right) :
    test.Holds left ↔ test.Holds right := by
  rcases mul_pos_iff.mp sameSign with ⟨leftPos, rightPos⟩ |
      ⟨leftNeg, rightNeg⟩
  · have leftNe : left ≠ 0 := ne_of_gt leftPos
    have rightNe : right ≠ 0 := ne_of_gt rightPos
    cases test <;>
      simp [SignTest.Holds, leftPos, rightPos, leftNe, rightNe] <;>
      constructor <;> intro <;> linarith
  · have leftNe : left ≠ 0 := ne_of_lt leftNeg
    have rightNe : right ≠ 0 := ne_of_lt rightNeg
    cases test <;>
      simp [SignTest.Holds, leftNeg, rightNeg, leftNe, rightNe] <;>
      constructor <;> intro <;> linarith

theorem PolynomialStatus.holds_iff
    {polynomial : RatPolynomial} {interval : RationalInterval}
    (status : PolynomialStatus polynomial interval) (test : SignTest)
    {s t : ℚ}
    (sLower : interval.lower ≤ s) (sUpper : s ≤ interval.upper)
    (tLower : interval.lower ≤ t) (tUpper : t ≤ interval.upper) :
    test.Holds (polynomial.eval s) ↔ test.Holds (polynomial.eval t) := by
  cases status with
  | zero isZero =>
      rw [eval_eq_zero_of_isZero isZero,
        eval_eq_zero_of_isZero isZero]
  | strict certificate =>
      exact SignTest.holds_iff_of_mul_pos test
        (certificate.eval_mul_pos_between sLower sUpper tLower tUpper)

/-- Proof-relevant sign stability for every atom of one formula.  Event
partitioning supplies either an identically-zero proof or a strict-sign
certificate at every finite list position. -/
structure StableFormula
    (formula : Formula) (path : Path) (interval : RationalInterval) where
  status : ∀ atom ∈ formulaAtoms formula,
    PolynomialStatus (clearedForm atom.form path) interval

/-- A stable cleared formula has the same Boolean truth value at every two
parameters in the cell. -/
theorem StableFormula.pathEvalBool_iff
    {formula : Formula} {path : Path} {interval : RationalInterval}
    (stable : StableFormula formula path interval) {s t : ℚ}
    (sLower : interval.lower ≤ s) (sUpper : s ≤ interval.upper)
    (tLower : interval.lower ≤ t) (tUpper : t ≤ interval.upper) :
    pathEvalBool formula path s = true ↔
      pathEvalBool formula path t = true := by
  induction formula with
  | truth => simp [pathEvalBool]
  | falsity => simp [pathEvalBool]
  | atom value =>
      have status := stable.status value (by simp [formulaAtoms])
      simp only [pathEvalBool, decide_eq_true_eq]
      exact status.holds_iff value.sign sLower sUpper tLower tUpper
  | and left right leftInduction rightInduction =>
      let leftStable : StableFormula left path interval :=
        { status := by
            intro atom member
            exact stable.status atom
              (List.mem_append_left (formulaAtoms right) member) }
      let rightStable : StableFormula right path interval :=
        { status := by
            intro atom member
            exact stable.status atom
              (List.mem_append_right (formulaAtoms left) member) }
      simp only [pathEvalBool, Bool.and_eq_true]
      exact and_congr
        (leftInduction leftStable)
        (rightInduction rightStable)
  | or left right leftInduction rightInduction =>
      let leftStable : StableFormula left path interval :=
        { status := by
            intro atom member
            exact stable.status atom
              (List.mem_append_left (formulaAtoms right) member) }
      let rightStable : StableFormula right path interval :=
        { status := by
            intro atom member
            exact stable.status atom
              (List.mem_append_right (formulaAtoms left) member) }
      simp only [pathEvalBool, Bool.or_eq_true]
      exact or_congr
        (leftInduction leftStable)
        (rightInduction rightStable)

/-- With the path denominator certified nonzero, cleared-form stability is
exactly stability of the original Hermitian formula on affine path values. -/
theorem StableFormula.holds_iff
    {formula : Formula} {path : Path} {interval : RationalInterval}
    (stable : StableFormula formula path interval) {s t : ℚ}
    (sLower : interval.lower ≤ s) (sUpper : s ≤ interval.upper)
    (tLower : interval.lower ≤ t) (tUpper : t ≤ interval.upper)
    (sDenominator :
      path.denominator.eval (PathPolynomial.ofRat s) ≠ 0)
    (tDenominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    formula.Holds (path.value s) ↔ formula.Holds (path.value t) := by
  rw [← pathEvalBool_eq_true_iff formula path s sDenominator,
    ← pathEvalBool_eq_true_iff formula path t tDenominator]
  exact stable.pathEvalBool_iff sLower sUpper tLower tUpper

end CCLFormulaPath
end FTA
