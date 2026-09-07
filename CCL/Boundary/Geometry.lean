import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.RawParserSemantics

/-!
# Finite rational geometry of CCL comparisons

Every radial or coordinate comparison made after a finite decoder homography
pulls back to a four-coefficient Hermitian form

`a * (x² + y²) + b * x + c * y + d`.

The coefficients and the evaluated point are constructive rationals.  These
identities are the algebraic input for the finite x--y curve classifier used
by the persistent next-bit controller.
-/

namespace CCL.CCLGeometry

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Mat2 := CCL.GaussianProjective.Mat2

open RFAP.ConstructiveGaussian.Gaussian
open CCL.RawParser

/-- A generalized rational circle or line in Hermitian normal form. -/
@[ext]
structure HermitianForm where
  radial : Coordinate
  realLinear : Coordinate
  imagLinear : Coordinate
  constant : Coordinate
deriving DecidableEq

namespace HermitianForm

def eval (form : HermitianForm) (value : Gaussian) : Coordinate :=
  form.radial * normSq value + form.realLinear * value.re +
    form.imagLinear * value.im + form.constant

def add (left right : HermitianForm) : HermitianForm :=
  ⟨left.radial + right.radial,
    left.realLinear + right.realLinear,
    left.imagLinear + right.imagLinear,
    left.constant + right.constant⟩

def neg (form : HermitianForm) : HermitianForm :=
  ⟨-form.radial, -form.realLinear, -form.imagLinear, -form.constant⟩

def sub (left right : HermitianForm) : HermitianForm := left.add right.neg

def scale (factor : Coordinate) (form : HermitianForm) : HermitianForm :=
  ⟨factor * form.radial, factor * form.realLinear,
    factor * form.imagLinear, factor * form.constant⟩

@[simp] theorem eval_add (left right : HermitianForm) (value : Gaussian) :
    (left.add right).eval value = left.eval value + right.eval value := by
  simp only [eval, add]
  ring1

@[simp] theorem eval_neg (form : HermitianForm) (value : Gaussian) :
    form.neg.eval value = -form.eval value := by
  simp only [eval, neg]
  ring1

@[simp] theorem eval_sub (left right : HermitianForm) (value : Gaussian) :
    (left.sub right).eval value = left.eval value - right.eval value := by
  simp only [sub, eval_add, eval_neg]
  ring1

@[simp] theorem eval_scale
    (factor : Coordinate) (form : HermitianForm) (value : Gaussian) :
    (form.scale factor).eval value = factor * form.eval value := by
  simp only [eval, scale]
  ring1

end HermitianForm

/-- Form evaluating to the squared norm of `u * z + v`. -/
def affineNormForm (u v : Gaussian) : HermitianForm where
  radial := normSq u
  realLinear := 2 * (u.re * v.re + u.im * v.im)
  imagLinear := 2 * (u.re * v.im - u.im * v.re)
  constant := normSq v

theorem eval_affineNormForm (u v value : Gaussian) :
    (affineNormForm u v).eval value = normSq (u * value + v) := by
  simp only [HermitianForm.eval, affineNormForm, normSq, mul_re, mul_im,
    add_re, add_im]
  ring1

/-- Form evaluating to the real part of
`(u * z + v) * conj (s * z + t)`. -/
def realCrossForm (u v s t : Gaussian) : HermitianForm where
  radial := u.re * s.re + u.im * s.im
  realLinear :=
    u.re * t.re + u.im * t.im + v.re * s.re + v.im * s.im
  imagLinear :=
    u.re * t.im - u.im * t.re + v.im * s.re - v.re * s.im
  constant := v.re * t.re + v.im * t.im

/-- Form evaluating to the imaginary part of the same cross product. -/
def imagCrossForm (u v s t : Gaussian) : HermitianForm where
  radial := u.im * s.re - u.re * s.im
  realLinear :=
    u.im * t.re - u.re * t.im + v.im * s.re - v.re * s.im
  imagLinear :=
    u.re * t.re + u.im * t.im - v.re * s.re - v.im * s.im
  constant := v.im * t.re - v.re * t.im

theorem eval_realCrossForm (u v s t value : Gaussian) :
    (realCrossForm u v s t).eval value =
      ((u * value + v) * conj (s * value + t)).re := by
  simp only [HermitianForm.eval, realCrossForm, normSq, mul_re, mul_im,
    add_re, add_im, conj]
  ring1

theorem eval_imagCrossForm (u v s t value : Gaussian) :
    (imagCrossForm u v s t).eval value =
      ((u * value + v) * conj (s * value + t)).im := by
  simp only [HermitianForm.eval, imagCrossForm, normSq, mul_re, mul_im,
    add_re, add_im, conj]
  ring1

/-- Pullback of a squared-norm comparison after clearing the denominator. -/
def normComparisonForm (matrix : Mat2) (radiusSq : Coordinate) :
    HermitianForm :=
  (affineNormForm matrix.a matrix.b).sub
    ((affineNormForm matrix.c matrix.d).scale radiusSq)

/-- Pullback of a real-coordinate comparison after clearing the denominator. -/
def realComparisonForm (matrix : Mat2) (threshold : Coordinate) :
    HermitianForm :=
  (realCrossForm matrix.a matrix.b matrix.c matrix.d).sub
    ((affineNormForm matrix.c matrix.d).scale threshold)

/-- Pullback of an imaginary-coordinate comparison. -/
def imagComparisonForm (matrix : Mat2) (threshold : Coordinate) :
    HermitianForm :=
  (imagCrossForm matrix.a matrix.b matrix.c matrix.d).sub
    ((affineNormForm matrix.c matrix.d).scale threshold)

theorem eval_normComparisonForm
    (matrix : Mat2) (radiusSq : Coordinate) (value : Gaussian) :
    (normComparisonForm matrix radiusSq).eval value =
      normSq (matrix.a * value + matrix.b) -
        radiusSq * normSq (matrix.c * value + matrix.d) := by
  simp only [normComparisonForm, HermitianForm.eval_sub,
    HermitianForm.eval_scale, eval_affineNormForm]

theorem eval_realComparisonForm
    (matrix : Mat2) (threshold : Coordinate) (value : Gaussian) :
    (realComparisonForm matrix threshold).eval value =
      ((matrix.a * value + matrix.b) *
          conj (matrix.c * value + matrix.d)).re -
        threshold * normSq (matrix.c * value + matrix.d) := by
  simp only [realComparisonForm, HermitianForm.eval_sub,
    HermitianForm.eval_scale, eval_realCrossForm, eval_affineNormForm]

theorem eval_imagComparisonForm
    (matrix : Mat2) (threshold : Coordinate) (value : Gaussian) :
    (imagComparisonForm matrix threshold).eval value =
      ((matrix.a * value + matrix.b) *
          conj (matrix.c * value + matrix.d)).im -
        threshold * normSq (matrix.c * value + matrix.d) := by
  simp only [imagComparisonForm, HermitianForm.eval_sub,
    HermitianForm.eval_scale, eval_imagCrossForm, eval_affineNormForm]

/-- Exact squared-norm quotient for the affine decoder chart. -/
theorem normSq_homographic (matrix : Mat2) (value : Gaussian)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    normSq (homographic matrix value) =
      normSq (numerator matrix value) *
        (normSq (denominator matrix value))⁻¹ := by
  rw [homographic, normSq_mul, inv_eq,
    normSq_inv _ denominatorNonzero]

theorem norm_clear_algebra (factor value inverseFactor : Coordinate) :
    factor * (value * inverseFactor) =
      value * (factor * inverseFactor) := by
  ring1

theorem real_clear_algebra
    (factor inverseFactor numeratorReal numeratorImag
      denominatorReal denominatorImag : Coordinate) :
    factor *
        (numeratorReal * (denominatorReal * inverseFactor) -
          numeratorImag * (-denominatorImag * inverseFactor)) =
      (factor * inverseFactor) *
        (numeratorReal * denominatorReal +
          numeratorImag * denominatorImag) := by
  ring1

theorem imag_clear_algebra
    (factor inverseFactor numeratorReal numeratorImag
      denominatorReal denominatorImag : Coordinate) :
    factor *
        (numeratorReal * (-denominatorImag * inverseFactor) +
          numeratorImag * (denominatorReal * inverseFactor)) =
      (factor * inverseFactor) *
        (numeratorImag * denominatorReal -
          numeratorReal * denominatorImag) := by
  ring1

theorem normSq_mul_homographic
    (matrix : Mat2) (value : Gaussian)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    normSq (denominator matrix value) *
        normSq (homographic matrix value) =
      normSq (numerator matrix value) := by
  rw [normSq_homographic matrix value denominatorNonzero]
  have normNonzero : normSq (denominator matrix value) ≠ 0 :=
    fun zero => denominatorNonzero (normSq_eq_zero.mp zero)
  let inverseNorm := (normSq (denominator matrix value))⁻¹
  have cancel :
      normSq (denominator matrix value) * inverseNorm = 1 :=
    RFAP.ConstructiveFraction.mul_inv_cancel _ normNonzero
  change normSq (denominator matrix value) *
      (normSq (numerator matrix value) * inverseNorm) =
    normSq (numerator matrix value)
  calc
    normSq (denominator matrix value) *
        (normSq (numerator matrix value) * inverseNorm) =
        normSq (numerator matrix value) *
          (normSq (denominator matrix value) * inverseNorm) :=
      norm_clear_algebra _ _ _
    _ = normSq (numerator matrix value) := by
      rw [cancel]
      ring1

theorem normSq_mul_inv_real
    (numeratorValue denominatorValue : Gaussian)
    (denominatorNonzero : denominatorValue ≠ 0) :
    normSq denominatorValue *
        (numeratorValue * inv denominatorValue).re =
      (numeratorValue * conj denominatorValue).re := by
  have normNonzero : normSq denominatorValue ≠ 0 :=
    fun zero => denominatorNonzero (normSq_eq_zero.mp zero)
  let inverseNorm := (normSq denominatorValue)⁻¹
  have cancel : normSq denominatorValue * inverseNorm = 1 :=
    RFAP.ConstructiveFraction.mul_inv_cancel _ normNonzero
  simp only [mul_re, inv, RFAP.ExplicitField.div_eq_mul_inv]
  change normSq denominatorValue *
      (numeratorValue.re * (denominatorValue.re * inverseNorm) -
        numeratorValue.im * (-denominatorValue.im * inverseNorm)) =
    numeratorValue.re * denominatorValue.re -
      numeratorValue.im * -denominatorValue.im
  calc
    normSq denominatorValue *
        (numeratorValue.re * (denominatorValue.re * inverseNorm) -
          numeratorValue.im * (-denominatorValue.im * inverseNorm)) =
        (normSq denominatorValue * inverseNorm) *
          (numeratorValue.re * denominatorValue.re +
            numeratorValue.im * denominatorValue.im) :=
      real_clear_algebra _ _ _ _ _ _
    _ = numeratorValue.re * denominatorValue.re -
        numeratorValue.im * -denominatorValue.im := by
      rw [cancel]
      ring1

theorem normSq_mul_inv_imag
    (numeratorValue denominatorValue : Gaussian)
    (denominatorNonzero : denominatorValue ≠ 0) :
    normSq denominatorValue *
        (numeratorValue * inv denominatorValue).im =
      (numeratorValue * conj denominatorValue).im := by
  have normNonzero : normSq denominatorValue ≠ 0 :=
    fun zero => denominatorNonzero (normSq_eq_zero.mp zero)
  let inverseNorm := (normSq denominatorValue)⁻¹
  have cancel : normSq denominatorValue * inverseNorm = 1 :=
    RFAP.ConstructiveFraction.mul_inv_cancel _ normNonzero
  simp only [mul_im, inv, RFAP.ExplicitField.div_eq_mul_inv]
  change normSq denominatorValue *
      (numeratorValue.re * (-denominatorValue.im * inverseNorm) +
        numeratorValue.im * (denominatorValue.re * inverseNorm)) =
    numeratorValue.re * -denominatorValue.im +
      numeratorValue.im * denominatorValue.re
  calc
    normSq denominatorValue *
        (numeratorValue.re * (-denominatorValue.im * inverseNorm) +
          numeratorValue.im * (denominatorValue.re * inverseNorm)) =
        (normSq denominatorValue * inverseNorm) *
          (numeratorValue.im * denominatorValue.re -
            numeratorValue.re * denominatorValue.im) :=
      imag_clear_algebra _ _ _ _ _ _
    _ = numeratorValue.re * -denominatorValue.im +
        numeratorValue.im * denominatorValue.re := by
      rw [cancel]
      ring1

/-- Clearing the positive denominator norm gives the norm comparison form. -/
theorem cleared_norm_identity
    (matrix : Mat2) (radiusSq : Coordinate) (value : Gaussian)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    (normComparisonForm matrix radiusSq).eval value =
      normSq (denominator matrix value) *
        (normSq (homographic matrix value) - radiusSq) := by
  rw [eval_normComparisonForm]
  change normSq (numerator matrix value) -
      radiusSq * normSq (denominator matrix value) = _
  rw [← normSq_mul_homographic matrix value denominatorNonzero]
  ring1

/-- Clearing the denominator gives the real-coordinate comparison form. -/
theorem cleared_real_identity
    (matrix : Mat2) (threshold : Coordinate) (value : Gaussian)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    (realComparisonForm matrix threshold).eval value =
      normSq (denominator matrix value) *
        ((homographic matrix value).re - threshold) := by
  rw [eval_realComparisonForm]
  change ((numerator matrix value) *
      conj (denominator matrix value)).re -
        threshold * normSq (denominator matrix value) = _
  rw [← normSq_mul_inv_real (numerator matrix value)
    (denominator matrix value) denominatorNonzero]
  unfold homographic
  rw [inv_eq]
  ring1

/-- Clearing the denominator gives the imaginary-coordinate comparison. -/
theorem cleared_imag_identity
    (matrix : Mat2) (threshold : Coordinate) (value : Gaussian)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    (imagComparisonForm matrix threshold).eval value =
      normSq (denominator matrix value) *
        ((homographic matrix value).im - threshold) := by
  rw [eval_imagComparisonForm]
  change ((numerator matrix value) *
      conj (denominator matrix value)).im -
        threshold * normSq (denominator matrix value) = _
  rw [← normSq_mul_inv_imag (numerator matrix value)
    (denominator matrix value) denominatorNonzero]
  unfold homographic
  rw [inv_eq]
  ring1

theorem compare_lt_iff
    {value threshold cleared factor : Coordinate}
    (factorPositive : 0 < factor)
    (identity : cleared = factor * (value - threshold)) :
    value < threshold ↔ cleared < 0 := by
  constructor
  · intro less
    rw [identity]
    exact RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
      factorPositive (RFAP.ConstructiveFraction.sub_neg_direct less)
  · intro negative
    rw [identity] at negative
    have scaled :
        (value - threshold) * factor < (0 : Coordinate) * factor := by
      simpa only [RFAP.ConstructiveFraction.mul_comm,
        RFAP.ConstructiveFraction.zero_mul_direct,
        RFAP.ConstructiveFraction.mul_zero_direct] using negative
    exact RFAP.ConstructiveFraction.lt_of_sub_neg_direct
      (RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
        scaled factorPositive)

theorem compare_le_iff
    {value threshold cleared factor : Coordinate}
    (factorPositive : 0 < factor)
    (identity : cleared = factor * (value - threshold)) :
    value ≤ threshold ↔ cleared ≤ 0 := by
  constructor
  · intro less
    rw [identity]
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (sub_nonpos.mpr less) factorPositive.le
    simpa only [RFAP.ConstructiveFraction.mul_zero_direct] using scaled
  · intro nonpositive
    rw [identity] at nonpositive
    have scaled :
        (value - threshold) * factor ≤ (0 : Coordinate) * factor := by
      simpa only [RFAP.ConstructiveFraction.mul_comm,
        RFAP.ConstructiveFraction.zero_mul_direct,
        RFAP.ConstructiveFraction.mul_zero_direct] using nonpositive
    exact sub_nonpos.mp
      (RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
        scaled factorPositive)

theorem compare_eq_iff
    {value threshold cleared factor : Coordinate}
    (factorPositive : 0 < factor)
    (identity : cleared = factor * (value - threshold)) :
    value = threshold ↔ cleared = 0 := by
  constructor
  · intro equal
    rw [identity, equal]
    ring1
  · intro zero
    have differenceZero : value - threshold = 0 := by
      apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
        factorPositive.ne'
      calc
        (value - threshold) * factor =
            factor * (value - threshold) :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ = cleared := identity.symm
        _ = 0 := zero
        _ = 0 * factor := by
          rw [RFAP.ConstructiveFraction.zero_mul_direct]
    exact sub_eq_zero.mp differenceZero

theorem compare_gt_iff
    {value threshold cleared factor : Coordinate}
    (factorPositive : 0 < factor)
    (identity : cleared = factor * (value - threshold)) :
    threshold < value ↔ 0 < cleared := by
  constructor
  · intro greater
    rw [identity]
    exact RFAP.ConstructiveFraction.mul_pos_direct factorPositive
      (RFAP.ConstructiveFraction.sub_pos_direct greater)
  · intro positive
    rw [identity] at positive
    have scaled :
        (0 : Coordinate) * factor < (value - threshold) * factor := by
      simpa only [RFAP.ConstructiveFraction.mul_comm,
        RFAP.ConstructiveFraction.zero_mul_direct,
        RFAP.ConstructiveFraction.mul_zero_direct] using positive
    exact RFAP.ConstructiveFraction.lt_of_sub_pos_direct
      (RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
        scaled factorPositive)

theorem compare_ge_iff
    {value threshold cleared factor : Coordinate}
    (factorPositive : 0 < factor)
    (identity : cleared = factor * (value - threshold)) :
    threshold ≤ value ↔ 0 ≤ cleared := by
  constructor
  · intro greater
    rw [identity]
    exact RFAP.ConstructiveFraction.mul_nonneg_direct factorPositive.le
      (sub_nonneg.mpr greater)
  · intro nonnegative
    rw [identity] at nonnegative
    have scaled :
        (0 : Coordinate) * factor ≤ (value - threshold) * factor := by
      simpa only [RFAP.ConstructiveFraction.mul_comm,
        RFAP.ConstructiveFraction.zero_mul_direct,
        RFAP.ConstructiveFraction.mul_zero_direct] using nonnegative
    exact sub_nonneg.mp
      (RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
        scaled factorPositive)

theorem norm_homographic_lt_iff
    (matrix : Mat2) (value : Gaussian) (radiusSq : Coordinate)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    normSq (homographic matrix value) < radiusSq ↔
      (normComparisonForm matrix radiusSq).eval value < 0 :=
  compare_lt_iff (normSq_pos denominatorNonzero)
    (cleared_norm_identity matrix radiusSq value denominatorNonzero)

theorem norm_homographic_le_iff
    (matrix : Mat2) (value : Gaussian) (radiusSq : Coordinate)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    normSq (homographic matrix value) ≤ radiusSq ↔
      (normComparisonForm matrix radiusSq).eval value ≤ 0 :=
  compare_le_iff (normSq_pos denominatorNonzero)
    (cleared_norm_identity matrix radiusSq value denominatorNonzero)

theorem norm_homographic_eq_iff
    (matrix : Mat2) (value : Gaussian) (radiusSq : Coordinate)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    normSq (homographic matrix value) = radiusSq ↔
      (normComparisonForm matrix radiusSq).eval value = 0 :=
  compare_eq_iff (normSq_pos denominatorNonzero)
    (cleared_norm_identity matrix radiusSq value denominatorNonzero)

theorem norm_homographic_gt_iff
    (matrix : Mat2) (value : Gaussian) (radiusSq : Coordinate)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    radiusSq < normSq (homographic matrix value) ↔
      0 < (normComparisonForm matrix radiusSq).eval value :=
  compare_gt_iff (normSq_pos denominatorNonzero)
    (cleared_norm_identity matrix radiusSq value denominatorNonzero)

theorem norm_homographic_ge_iff
    (matrix : Mat2) (value : Gaussian) (radiusSq : Coordinate)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    radiusSq ≤ normSq (homographic matrix value) ↔
      0 ≤ (normComparisonForm matrix radiusSq).eval value :=
  compare_ge_iff (normSq_pos denominatorNonzero)
    (cleared_norm_identity matrix radiusSq value denominatorNonzero)

theorem real_homographic_lt_iff
    (matrix : Mat2) (value : Gaussian) (threshold : Coordinate)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    (homographic matrix value).re < threshold ↔
      (realComparisonForm matrix threshold).eval value < 0 :=
  compare_lt_iff (normSq_pos denominatorNonzero)
    (cleared_real_identity matrix threshold value denominatorNonzero)

theorem real_homographic_le_iff
    (matrix : Mat2) (value : Gaussian) (threshold : Coordinate)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    (homographic matrix value).re ≤ threshold ↔
      (realComparisonForm matrix threshold).eval value ≤ 0 :=
  compare_le_iff (normSq_pos denominatorNonzero)
    (cleared_real_identity matrix threshold value denominatorNonzero)

theorem real_homographic_eq_iff
    (matrix : Mat2) (value : Gaussian) (threshold : Coordinate)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    (homographic matrix value).re = threshold ↔
      (realComparisonForm matrix threshold).eval value = 0 :=
  compare_eq_iff (normSq_pos denominatorNonzero)
    (cleared_real_identity matrix threshold value denominatorNonzero)

theorem real_homographic_gt_iff
    (matrix : Mat2) (value : Gaussian) (threshold : Coordinate)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    threshold < (homographic matrix value).re ↔
      0 < (realComparisonForm matrix threshold).eval value :=
  compare_gt_iff (normSq_pos denominatorNonzero)
    (cleared_real_identity matrix threshold value denominatorNonzero)

theorem real_homographic_ge_iff
    (matrix : Mat2) (value : Gaussian) (threshold : Coordinate)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    threshold ≤ (homographic matrix value).re ↔
      0 ≤ (realComparisonForm matrix threshold).eval value :=
  compare_ge_iff (normSq_pos denominatorNonzero)
    (cleared_real_identity matrix threshold value denominatorNonzero)

theorem imag_homographic_lt_iff
    (matrix : Mat2) (value : Gaussian) (threshold : Coordinate)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    (homographic matrix value).im < threshold ↔
      (imagComparisonForm matrix threshold).eval value < 0 :=
  compare_lt_iff (normSq_pos denominatorNonzero)
    (cleared_imag_identity matrix threshold value denominatorNonzero)

theorem imag_homographic_le_iff
    (matrix : Mat2) (value : Gaussian) (threshold : Coordinate)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    (homographic matrix value).im ≤ threshold ↔
      (imagComparisonForm matrix threshold).eval value ≤ 0 :=
  compare_le_iff (normSq_pos denominatorNonzero)
    (cleared_imag_identity matrix threshold value denominatorNonzero)

theorem imag_homographic_eq_iff
    (matrix : Mat2) (value : Gaussian) (threshold : Coordinate)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    (homographic matrix value).im = threshold ↔
      (imagComparisonForm matrix threshold).eval value = 0 :=
  compare_eq_iff (normSq_pos denominatorNonzero)
    (cleared_imag_identity matrix threshold value denominatorNonzero)

theorem imag_homographic_gt_iff
    (matrix : Mat2) (value : Gaussian) (threshold : Coordinate)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    threshold < (homographic matrix value).im ↔
      0 < (imagComparisonForm matrix threshold).eval value :=
  compare_gt_iff (normSq_pos denominatorNonzero)
    (cleared_imag_identity matrix threshold value denominatorNonzero)

theorem imag_homographic_ge_iff
    (matrix : Mat2) (value : Gaussian) (threshold : Coordinate)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    threshold ≤ (homographic matrix value).im ↔
      0 ≤ (imagComparisonForm matrix threshold).eval value :=
  compare_ge_iff (normSq_pos denominatorNonzero)
    (cleared_imag_identity matrix threshold value denominatorNonzero)

end CCL.CCLGeometry
