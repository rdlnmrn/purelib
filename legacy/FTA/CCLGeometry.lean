import CCL.Boxes

/-!
# Rational geometry of CCL branch comparisons

This module formalizes the algebraic content of Section 10.1 of the finite
constructive FTA paper.  Every norm or coordinate comparison made after a
finite decoder homography pulls back to a four-coefficient rational Hermitian
form

`alpha * (x^2 + y^2) + beta * x + gamma * y + delta`.

It also gives the homogeneous rational parametrization of the unit circle,
including the missing affine parameter at the finite projective coordinate
`[1 : 0]`.  Everything is exact arithmetic over `Q(i)`.
-/

namespace FTA
namespace CCLGeometry

open CCL CCL.GaussianRat

abbrev QI := CCL.GaussianRat

/-- A rational generalized circle or line in the Hermitian normal form (16). -/
@[ext]
structure HermitianForm where
  radial : ℚ
  realLinear : ℚ
  imagLinear : ℚ
  constant : ℚ
deriving DecidableEq, Repr

namespace HermitianForm

/-- Exact evaluation of a rational generalized-circle form at `z = x + iy`. -/
def eval (h : HermitianForm) (z : QI) : ℚ :=
  h.radial * normSq z + h.realLinear * z.re +
    h.imagLinear * z.im + h.constant

/-- Coefficientwise addition. -/
def add (h k : HermitianForm) : HermitianForm :=
  ⟨h.radial + k.radial, h.realLinear + k.realLinear,
    h.imagLinear + k.imagLinear, h.constant + k.constant⟩

/-- Coefficientwise negation. -/
def neg (h : HermitianForm) : HermitianForm :=
  ⟨-h.radial, -h.realLinear, -h.imagLinear, -h.constant⟩

/-- Coefficientwise subtraction. -/
def sub (h k : HermitianForm) : HermitianForm := add h (neg k)

/-- Rational scaling of all four coefficients. -/
def scale (r : ℚ) (h : HermitianForm) : HermitianForm :=
  ⟨r * h.radial, r * h.realLinear, r * h.imagLinear, r * h.constant⟩

@[simp] theorem eval_add (h k : HermitianForm) (z : QI) :
    (add h k).eval z = h.eval z + k.eval z := by
  simp only [eval, add]
  ring

@[simp] theorem eval_neg (h : HermitianForm) (z : QI) :
    h.neg.eval z = -h.eval z := by
  simp only [eval, neg]
  ring

@[simp] theorem eval_sub (h k : HermitianForm) (z : QI) :
    (sub h k).eval z = h.eval z - k.eval z := by
  simp only [sub, eval_add, eval_neg]
  ring

@[simp] theorem eval_scale (r : ℚ) (h : HermitianForm) (z : QI) :
    (scale r h).eval z = r * h.eval z := by
  simp only [eval, scale]
  ring

end HermitianForm

/-- The Hermitian form evaluating exactly to `N(u*z + v)`. -/
def affineNormForm (u v : QI) : HermitianForm where
  radial := normSq u
  realLinear := 2 * (u.re * v.re + u.im * v.im)
  imagLinear := 2 * (u.re * v.im - u.im * v.re)
  constant := normSq v

theorem eval_affineNormForm (u v z : QI) :
    (affineNormForm u v).eval z = normSq (u * z + v) := by
  simp only [HermitianForm.eval, affineNormForm, normSq, mul_re, mul_im,
    add_re, add_im]
  ring

/-- The form evaluating to `Re ((u*z+v) * conj (s*z+t))`. -/
def realCrossForm (u v s t : QI) : HermitianForm where
  radial := u.re * s.re + u.im * s.im
  realLinear :=
    u.re * t.re + u.im * t.im + v.re * s.re + v.im * s.im
  imagLinear :=
    u.re * t.im - u.im * t.re + v.im * s.re - v.re * s.im
  constant := v.re * t.re + v.im * t.im

/-- The form evaluating to `Im ((u*z+v) * conj (s*z+t))`. -/
def imagCrossForm (u v s t : QI) : HermitianForm where
  radial := u.im * s.re - u.re * s.im
  realLinear :=
    u.im * t.re - u.re * t.im + v.im * s.re - v.re * s.im
  imagLinear :=
    u.re * t.re + u.im * t.im - v.re * s.re - v.im * s.im
  constant := v.im * t.re - v.re * t.im

theorem eval_realCrossForm (u v s t z : QI) :
    (realCrossForm u v s t).eval z =
      ((u * z + v) * conj (s * z + t)).re := by
  simp only [HermitianForm.eval, realCrossForm, normSq, mul_re, mul_im,
    add_re, add_im, conj]
  ring

theorem eval_imagCrossForm (u v s t z : QI) :
    (imagCrossForm u v s t).eval z =
      ((u * z + v) * conj (s * z + t)).im := by
  simp only [HermitianForm.eval, imagCrossForm, normSq, mul_re, mul_im,
    add_re, add_im, conj]
  ring

/-- Pullback of `N(H_M(z)) - radiusSq` after clearing the denominator norm. -/
def normComparisonForm (M : Mat2 QI) (radiusSq : ℚ) : HermitianForm :=
  HermitianForm.sub (affineNormForm M.a M.b)
    (HermitianForm.scale radiusSq (affineNormForm M.c M.d))

/-- Pullback of `Re(H_M(z)) - threshold` after clearing the denominator norm. -/
def realComparisonForm (M : Mat2 QI) (threshold : ℚ) : HermitianForm :=
  HermitianForm.sub (realCrossForm M.a M.b M.c M.d)
    (HermitianForm.scale threshold (affineNormForm M.c M.d))

/-- Pullback of `Im(H_M(z)) - threshold` after clearing the denominator norm. -/
def imagComparisonForm (M : Mat2 QI) (threshold : ℚ) : HermitianForm :=
  HermitianForm.sub (imagCrossForm M.a M.b M.c M.d)
    (HermitianForm.scale threshold (affineNormForm M.c M.d))

theorem eval_normComparisonForm (M : Mat2 QI) (radiusSq : ℚ) (z : QI) :
    (normComparisonForm M radiusSq).eval z =
      normSq (M.a * z + M.b) - radiusSq * normSq (M.c * z + M.d) := by
  simp only [normComparisonForm, HermitianForm.eval_sub, HermitianForm.eval_scale,
    eval_affineNormForm]

theorem eval_realComparisonForm (M : Mat2 QI) (threshold : ℚ) (z : QI) :
    (realComparisonForm M threshold).eval z =
      ((M.a * z + M.b) * conj (M.c * z + M.d)).re -
        threshold * normSq (M.c * z + M.d) := by
  simp only [realComparisonForm, HermitianForm.eval_sub, HermitianForm.eval_scale,
    eval_realCrossForm, eval_affineNormForm]

theorem eval_imagComparisonForm (M : Mat2 QI) (threshold : ℚ) (z : QI) :
    (imagComparisonForm M threshold).eval z =
      ((M.a * z + M.b) * conj (M.c * z + M.d)).im -
        threshold * normSq (M.c * z + M.d) := by
  simp only [imagComparisonForm, HermitianForm.eval_sub, HermitianForm.eval_scale,
    eval_imagCrossForm, eval_affineNormForm]

/-- Exact norm quotient for the finite decoder homography away from its pole. -/
theorem normSq_homographic (M : Mat2 QI) (z : QI)
    (hden : M.c * z + M.d ≠ 0) :
    normSq (CCL.RatBox.homographic M z) =
      normSq (M.a * z + M.b) / normSq (M.c * z + M.d) := by
  rw [CCL.RatBox.homographic, normSq_mul, normSq_inv _ hden]
  ring

private theorem normSq_mul_inv_real (numerator denominator : QI)
    (hden : denominator ≠ 0) :
    normSq denominator * (numerator * inv denominator).re =
      (numerator * conj denominator).re := by
  have hn : normSq denominator ≠ 0 :=
    fun h => hden (normSq_eq_zero.mp h)
  simp only [mul_re, inv, conj]
  field_simp [hn]

private theorem normSq_mul_inv_imag (numerator denominator : QI)
    (hden : denominator ≠ 0) :
    normSq denominator * (numerator * inv denominator).im =
      (numerator * conj denominator).im := by
  have hn : normSq denominator ≠ 0 :=
    fun h => hden (normSq_eq_zero.mp h)
  simp only [mul_im, inv, conj]
  field_simp [hn]

private theorem normSq_mul_homographic (M : Mat2 QI) (z : QI)
    (hden : M.c * z + M.d ≠ 0) :
    normSq (M.c * z + M.d) * normSq (CCL.RatBox.homographic M z) =
      normSq (M.a * z + M.b) := by
  rw [normSq_homographic M z hden]
  have hn : normSq (M.c * z + M.d) ≠ 0 :=
    fun h => hden (normSq_eq_zero.mp h)
  field_simp [hn]

/-- Clearing the positive denominator norm gives exactly the norm form. -/
theorem cleared_norm_identity (M : Mat2 QI) (radiusSq : ℚ) (z : QI)
    (hden : M.c * z + M.d ≠ 0) :
    (normComparisonForm M radiusSq).eval z =
      normSq (M.c * z + M.d) *
        (normSq (CCL.RatBox.homographic M z) - radiusSq) := by
  rw [eval_normComparisonForm]
  rw [← normSq_mul_homographic M z hden]
  ring

/-- Clearing the positive denominator norm gives exactly the real form. -/
theorem cleared_real_identity (M : Mat2 QI) (threshold : ℚ) (z : QI)
    (hden : M.c * z + M.d ≠ 0) :
    (realComparisonForm M threshold).eval z =
      normSq (M.c * z + M.d) *
        ((CCL.RatBox.homographic M z).re - threshold) := by
  rw [eval_realComparisonForm]
  have hclear := normSq_mul_inv_real
    (M.a * z + M.b) (M.c * z + M.d) hden
  rw [CCL.RatBox.homographic]
  rw [← hclear]
  ring

/-- Clearing the positive denominator norm gives exactly the imaginary form. -/
theorem cleared_imag_identity (M : Mat2 QI) (threshold : ℚ) (z : QI)
    (hden : M.c * z + M.d ≠ 0) :
    (imagComparisonForm M threshold).eval z =
      normSq (M.c * z + M.d) *
        ((CCL.RatBox.homographic M z).im - threshold) := by
  rw [eval_imagComparisonForm]
  have hclear := normSq_mul_inv_imag
    (M.a * z + M.b) (M.c * z + M.d) hden
  rw [CCL.RatBox.homographic]
  rw [← hclear]
  ring

/-- The unique affine pole of a decoder homography when `c` is nonzero. -/
def decoderPole (M : Mat2 QI) : QI := -M.d / M.c

theorem denominator_at_decoderPole (M : Mat2 QI) (hc : M.c ≠ 0) :
    M.c * decoderPole M + M.d = 0 := by
  dsimp [decoderPole]
  field_simp [hc]
  simp

theorem denominator_eq_zero_iff (M : Mat2 QI) (hc : M.c ≠ 0) (z : QI) :
    M.c * z + M.d = 0 ↔ z = decoderPole M := by
  constructor
  · intro h
    apply mul_right_cancel_of_ne hc
    rw [_root_.mul_comm z M.c]
    have hcz : M.c * z = -M.d := eq_neg_of_add_eq_zero_left h
    rw [hcz]
    dsimp [decoderPole]
    field_simp [hc]
  · rintro rfl
    exact denominator_at_decoderPole M hc

theorem denominator_of_c_eq_zero (M : Mat2 QI) (hc : M.c = 0) (z : QI) :
    M.c * z + M.d = M.d := by
  simp [hc]

private theorem compare_lt_iff {value threshold cleared factor : ℚ}
    (hfactor : 0 < factor) (hcleared : cleared = factor * (value - threshold)) :
    value < threshold ↔ cleared < 0 := by
  rw [hcleared]
  constructor
  · intro h
    exact mul_neg_of_pos_of_neg hfactor (sub_neg.mpr h)
  · intro h
    by_contra hnot
    exact (not_lt_of_ge (mul_nonneg hfactor.le (sub_nonneg.mpr (not_lt.mp hnot)))) h

private theorem compare_le_iff {value threshold cleared factor : ℚ}
    (hfactor : 0 < factor) (hcleared : cleared = factor * (value - threshold)) :
    value ≤ threshold ↔ cleared ≤ 0 := by
  rw [hcleared]
  constructor
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hfactor.le (sub_nonpos.mpr h)
  · intro h
    by_contra hnot
    exact (not_le_of_gt (mul_pos hfactor (sub_pos.mpr (not_le.mp hnot)))) h

private theorem compare_eq_iff {value threshold cleared factor : ℚ}
    (hfactor : 0 < factor) (hcleared : cleared = factor * (value - threshold)) :
    value = threshold ↔ cleared = 0 := by
  rw [hcleared, mul_eq_zero]
  simp only [ne_of_gt hfactor, false_or, sub_eq_zero]

private theorem compare_gt_iff {value threshold cleared factor : ℚ}
    (hfactor : 0 < factor) (hcleared : cleared = factor * (value - threshold)) :
    value > threshold ↔ cleared > 0 := by
  rw [hcleared]
  constructor
  · intro h
    exact mul_pos hfactor (sub_pos.mpr h)
  · intro h
    by_contra hnot
    exact (not_le_of_gt h)
      (mul_nonpos_of_nonneg_of_nonpos hfactor.le (sub_nonpos.mpr (not_lt.mp hnot)))

private theorem compare_ge_iff {value threshold cleared factor : ℚ}
    (hfactor : 0 < factor) (hcleared : cleared = factor * (value - threshold)) :
    value ≥ threshold ↔ cleared ≥ 0 := by
  rw [hcleared]
  constructor
  · intro h
    exact mul_nonneg hfactor.le (sub_nonneg.mpr h)
  · intro h
    by_contra hnot
    exact (not_lt_of_ge h)
      (mul_neg_of_pos_of_neg hfactor (sub_neg.mpr (not_le.mp hnot)))

theorem norm_homographic_lt_iff (M : Mat2 QI) (z : QI) (radiusSq : ℚ)
    (hden : M.c * z + M.d ≠ 0) :
    normSq (CCL.RatBox.homographic M z) < radiusSq ↔
      (normComparisonForm M radiusSq).eval z < 0 := by
  exact compare_lt_iff (normSq_pos hden)
    (cleared_norm_identity M radiusSq z hden)

theorem norm_homographic_le_iff (M : Mat2 QI) (z : QI) (radiusSq : ℚ)
    (hden : M.c * z + M.d ≠ 0) :
    normSq (CCL.RatBox.homographic M z) ≤ radiusSq ↔
      (normComparisonForm M radiusSq).eval z ≤ 0 := by
  exact compare_le_iff (normSq_pos hden)
    (cleared_norm_identity M radiusSq z hden)

theorem norm_homographic_eq_iff (M : Mat2 QI) (z : QI) (radiusSq : ℚ)
    (hden : M.c * z + M.d ≠ 0) :
    normSq (CCL.RatBox.homographic M z) = radiusSq ↔
      (normComparisonForm M radiusSq).eval z = 0 := by
  exact compare_eq_iff (normSq_pos hden)
    (cleared_norm_identity M radiusSq z hden)

theorem norm_homographic_gt_iff (M : Mat2 QI) (z : QI) (radiusSq : ℚ)
    (hden : M.c * z + M.d ≠ 0) :
    normSq (CCL.RatBox.homographic M z) > radiusSq ↔
      (normComparisonForm M radiusSq).eval z > 0 := by
  exact compare_gt_iff (normSq_pos hden)
    (cleared_norm_identity M radiusSq z hden)

theorem norm_homographic_ge_iff (M : Mat2 QI) (z : QI) (radiusSq : ℚ)
    (hden : M.c * z + M.d ≠ 0) :
    normSq (CCL.RatBox.homographic M z) ≥ radiusSq ↔
      (normComparisonForm M radiusSq).eval z ≥ 0 := by
  exact compare_ge_iff (normSq_pos hden)
    (cleared_norm_identity M radiusSq z hden)

theorem real_homographic_lt_iff (M : Mat2 QI) (z : QI) (threshold : ℚ)
    (hden : M.c * z + M.d ≠ 0) :
    (CCL.RatBox.homographic M z).re < threshold ↔
      (realComparisonForm M threshold).eval z < 0 := by
  exact compare_lt_iff (normSq_pos hden)
    (cleared_real_identity M threshold z hden)

theorem real_homographic_le_iff (M : Mat2 QI) (z : QI) (threshold : ℚ)
    (hden : M.c * z + M.d ≠ 0) :
    (CCL.RatBox.homographic M z).re ≤ threshold ↔
      (realComparisonForm M threshold).eval z ≤ 0 := by
  exact compare_le_iff (normSq_pos hden)
    (cleared_real_identity M threshold z hden)

theorem real_homographic_eq_iff (M : Mat2 QI) (z : QI) (threshold : ℚ)
    (hden : M.c * z + M.d ≠ 0) :
    (CCL.RatBox.homographic M z).re = threshold ↔
      (realComparisonForm M threshold).eval z = 0 := by
  exact compare_eq_iff (normSq_pos hden)
    (cleared_real_identity M threshold z hden)

theorem real_homographic_gt_iff (M : Mat2 QI) (z : QI) (threshold : ℚ)
    (hden : M.c * z + M.d ≠ 0) :
    (CCL.RatBox.homographic M z).re > threshold ↔
      (realComparisonForm M threshold).eval z > 0 := by
  exact compare_gt_iff (normSq_pos hden)
    (cleared_real_identity M threshold z hden)

theorem real_homographic_ge_iff (M : Mat2 QI) (z : QI) (threshold : ℚ)
    (hden : M.c * z + M.d ≠ 0) :
    (CCL.RatBox.homographic M z).re ≥ threshold ↔
      (realComparisonForm M threshold).eval z ≥ 0 := by
  exact compare_ge_iff (normSq_pos hden)
    (cleared_real_identity M threshold z hden)

theorem imag_homographic_lt_iff (M : Mat2 QI) (z : QI) (threshold : ℚ)
    (hden : M.c * z + M.d ≠ 0) :
    (CCL.RatBox.homographic M z).im < threshold ↔
      (imagComparisonForm M threshold).eval z < 0 := by
  exact compare_lt_iff (normSq_pos hden)
    (cleared_imag_identity M threshold z hden)

theorem imag_homographic_le_iff (M : Mat2 QI) (z : QI) (threshold : ℚ)
    (hden : M.c * z + M.d ≠ 0) :
    (CCL.RatBox.homographic M z).im ≤ threshold ↔
      (imagComparisonForm M threshold).eval z ≤ 0 := by
  exact compare_le_iff (normSq_pos hden)
    (cleared_imag_identity M threshold z hden)

theorem imag_homographic_eq_iff (M : Mat2 QI) (z : QI) (threshold : ℚ)
    (hden : M.c * z + M.d ≠ 0) :
    (CCL.RatBox.homographic M z).im = threshold ↔
      (imagComparisonForm M threshold).eval z = 0 := by
  exact compare_eq_iff (normSq_pos hden)
    (cleared_imag_identity M threshold z hden)

theorem imag_homographic_gt_iff (M : Mat2 QI) (z : QI) (threshold : ℚ)
    (hden : M.c * z + M.d ≠ 0) :
    (CCL.RatBox.homographic M z).im > threshold ↔
      (imagComparisonForm M threshold).eval z > 0 := by
  exact compare_gt_iff (normSq_pos hden)
    (cleared_imag_identity M threshold z hden)

theorem imag_homographic_ge_iff (M : Mat2 QI) (z : QI) (threshold : ℚ)
    (hden : M.c * z + M.d ≠ 0) :
    (CCL.RatBox.homographic M z).im ≥ threshold ↔
      (imagComparisonForm M threshold).eval z ≥ 0 := by
  exact compare_ge_iff (normSq_pos hden)
    (cleared_imag_identity M threshold z hden)

/-- The positive denominator in the affine unit-circle parametrization (17). -/
def unitCircleDenominator (t : ℚ) : ℚ := 1 + t ^ 2

theorem unitCircleDenominator_pos (t : ℚ) : 0 < unitCircleDenominator t := by
  dsimp [unitCircleDenominator]
  nlinarith [sq_nonneg t]

/-- The rational affine unit-circle parametrization (17). -/
def unitCircleParam (t : ℚ) : QI :=
  ⟨(1 - t ^ 2) / unitCircleDenominator t,
    (2 * t) / unitCircleDenominator t⟩

theorem normSq_unitCircleParam (t : ℚ) : normSq (unitCircleParam t) = 1 := by
  have hden := ne_of_gt (unitCircleDenominator_pos t)
  simp only [normSq, unitCircleParam]
  unfold unitCircleDenominator at hden ⊢
  field_simp [hden]
  ring

/-- Homogeneous rational parametrization of the whole unit circle.  The input
`[p:q]` represents the affine parameter `p/q`; `[1:0]` supplies the missing
point `-1`. -/
def unitCircleProjective (parameter : Proj ℚ) : Proj QI :=
  ⟨⟨parameter.q ^ 2 - parameter.p ^ 2, 2 * parameter.p * parameter.q⟩,
    ⟨parameter.q ^ 2 + parameter.p ^ 2, 0⟩⟩

/-- The homogeneous numerator and denominator satisfy the unit-circle equation. -/
theorem normSq_unitCircleProjective (parameter : Proj ℚ) :
    normSq (unitCircleProjective parameter).p =
      normSq (unitCircleProjective parameter).q := by
  simp only [unitCircleProjective, normSq]
  ring

/-- The missing projective parameter maps to the rational point `-1`. -/
theorem unitCircleProjective_omega :
    unitCircleProjective (Proj.omega : Proj ℚ) =
      Proj.affine (GaussianRat.mk (-1) 0) := by
  ext <;> norm_num [unitCircleProjective, Proj.omega, Proj.affine]

/-- On finite affine parameters, the homogeneous and displayed affine
parametrizations represent the same point. -/
theorem unitCircleProjective_affine (t : ℚ) :
    (unitCircleProjective (Proj.affine t)).Equivalent
      (Proj.affine (unitCircleParam t)) := by
  dsimp [unitCircleProjective, Proj.affine, Proj.Equivalent, unitCircleParam]
  have hden := ne_of_gt (unitCircleDenominator_pos t)
  unfold unitCircleDenominator at hden ⊢
  apply GaussianRat.ext
  · simp only [mul_re, one_re, one_im]
    field_simp [hden]
    ring
  · simp only [mul_im, one_re, one_im]
    field_simp [hden]
    ring

/-- The reciprocal affine chart `[1:t]` on the rational projective line. -/
def reciprocalAffine (t : ℚ) : Proj ℚ := ⟨1, t⟩

/-- Two closed rational unit intervals cover every nonzero rational
projective parameter: use `[t:1]` when `|p| ≤ |q|`, and `[1:t]` otherwise.
This is the finite two-chart cover used for complete circle traversal. -/
theorem projectiveUnitIntervalCover
    (parameter : Proj ℚ) (nonzero : parameter.p ≠ 0 ∨ parameter.q ≠ 0) :
    (∃ t : ℚ, -1 ≤ t ∧ t ≤ 1 ∧
      parameter.Equivalent (Proj.affine t)) ∨
    (∃ t : ℚ, -1 ≤ t ∧ t ≤ 1 ∧
      parameter.Equivalent (reciprocalAffine t)) := by
  by_cases qZero : parameter.q = 0
  · have pNonzero : parameter.p ≠ 0 := by
      rcases nonzero with pNonzero | qNonzero
      · exact pNonzero
      · exact (qNonzero qZero).elim
    right
    refine ⟨0, by norm_num, by norm_num, ?_⟩
    simp [Proj.Equivalent, reciprocalAffine, qZero]
  · by_cases primary : |parameter.p| ≤ |parameter.q|
    · left
      let t := parameter.p / parameter.q
      have qAbsPositive : 0 < |parameter.q| := abs_pos.mpr qZero
      have tAbs : |t| ≤ 1 := by
        dsimp [t]
        rw [abs_div]
        apply (div_le_iff₀ qAbsPositive).2
        simpa using primary
      rcases abs_le.mp tAbs with ⟨lower, upper⟩
      refine ⟨t, lower, upper, ?_⟩
      dsimp [Proj.Equivalent, Proj.affine, t]
      field_simp [qZero]
    · right
      have pAbsPositive : 0 < |parameter.p| := by
        have strict : |parameter.q| < |parameter.p| := lt_of_not_ge primary
        exact (abs_nonneg parameter.q).trans_lt strict
      have pNonzero : parameter.p ≠ 0 := abs_pos.mp pAbsPositive
      let t := parameter.q / parameter.p
      have tAbs : |t| ≤ 1 := by
        dsimp [t]
        rw [abs_div]
        apply (div_le_iff₀ pAbsPositive).2
        simpa using (le_of_lt (lt_of_not_ge primary))
      rcases abs_le.mp tAbs with ⟨lower, upper⟩
      refine ⟨t, lower, upper, ?_⟩
      dsimp [Proj.Equivalent, reciprocalAffine, t]
      field_simp [pNonzero]

/-- Multiplying the homogeneous numerator parametrizes the corresponding
scaled circle. -/
def scaledCircleProjective (scale : QI) (parameter : Proj ℚ) : Proj QI :=
  ⟨scale * (unitCircleProjective parameter).p,
    (unitCircleProjective parameter).q⟩

theorem normSq_scaledCircleProjective (scale : QI) (parameter : Proj ℚ) :
    normSq (scaledCircleProjective scale parameter).p =
      normSq scale * normSq (scaledCircleProjective scale parameter).q := by
  rw [scaledCircleProjective, normSq_mul, normSq_unitCircleProjective]

/-- Multiplication by `gamma = 1+i` parametrizes the norm-two circle. -/
theorem normSq_gammaCircleProjective (parameter : Proj ℚ) :
    normSq (scaledCircleProjective gamma parameter).p =
      2 * normSq (scaledCircleProjective gamma parameter).q := by
  rw [normSq_scaledCircleProjective, normSq_gamma]

/-- Embed a rational scalar as a Gaussian rational. -/
def ofRat (r : ℚ) : QI := ⟨r, 0⟩

/-- Homogeneous parametrization of the affine line `base + t*direction`.
At `[1:0]` it records the projective direction. -/
def projectiveLine (base direction : QI) (parameter : Proj ℚ) : Proj QI :=
  ⟨ofRat parameter.q * base + ofRat parameter.p * direction,
    ofRat parameter.q⟩

theorem projectiveLine_affine (base direction : QI) (t : ℚ) :
    projectiveLine base direction (Proj.affine t) =
      Proj.affine (base + ofRat t * direction) := by
  ext <;> simp [projectiveLine, ofRat, Proj.affine]

theorem projectiveLine_omega (base direction : QI) :
    projectiveLine base direction (Proj.omega : Proj ℚ) =
      ⟨direction, 0⟩ := by
  ext <;> simp [projectiveLine, ofRat, Proj.omega]

/-- Projective parametrization of the standard boundary `Re z = threshold`. -/
def realBoundaryProjective (threshold : ℚ) (parameter : Proj ℚ) : Proj QI :=
  projectiveLine ⟨threshold, 0⟩ ⟨0, 1⟩ parameter

/-- Projective parametrization of the standard boundary `Im z = threshold`. -/
def imagBoundaryProjective (threshold : ℚ) (parameter : Proj ℚ) : Proj QI :=
  projectiveLine ⟨0, threshold⟩ ⟨1, 0⟩ parameter

/-- Determinant of a finite decoder matrix. -/
def determinant (M : Mat2 QI) : QI := M.a * M.d - M.b * M.c

/-- The adjugate gives the inverse homography without introducing division. -/
def adjugate (M : Mat2 QI) : Mat2 QI := ⟨M.d, -M.b, -M.c, M.a⟩

theorem act_adjugate (M : Mat2 QI) (point : Proj QI) :
    Mat2.act M (Mat2.act (adjugate M) point) =
      ⟨determinant M * point.p, determinant M * point.q⟩ := by
  ext <;> simp only [Mat2.act, adjugate, determinant, mul_re, mul_im,
    add_re, add_im, sub_re, sub_im, neg_re, neg_im] <;> ring

/-- Apply the inverse decoder homography to the standard unit-circle
parametrization using only homogeneous rational arithmetic. -/
def inverseUnitCircleProjective (M : Mat2 QI) (parameter : Proj ℚ) : Proj QI :=
  Mat2.act (adjugate M) (unitCircleProjective parameter)

theorem decode_inverseUnitCircleProjective (M : Mat2 QI) (parameter : Proj ℚ) :
    Mat2.act M (inverseUnitCircleProjective M parameter) =
      ⟨determinant M * (unitCircleProjective parameter).p,
        determinant M * (unitCircleProjective parameter).q⟩ := by
  exact act_adjugate M (unitCircleProjective parameter)

/-- Apply the inverse decoder homography to any standard projective line. -/
def inverseLineProjective (M : Mat2 QI) (base direction : QI)
    (parameter : Proj ℚ) : Proj QI :=
  Mat2.act (adjugate M) (projectiveLine base direction parameter)

theorem decode_inverseLineProjective (M : Mat2 QI) (base direction : QI)
    (parameter : Proj ℚ) :
    Mat2.act M (inverseLineProjective M base direction parameter) =
      ⟨determinant M * (projectiveLine base direction parameter).p,
        determinant M * (projectiveLine base direction parameter).q⟩ := by
  exact act_adjugate M (projectiveLine base direction parameter)

end CCLGeometry
end FTA
