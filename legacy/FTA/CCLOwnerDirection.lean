import FTA.CCLGeometry

/-!
# Finite owner-side directions for Hermitian boundaries

At an equality point of a nondegenerate Hermitian boundary, exact rational
gradient signs select one of the four coordinate directions.  A displayed
rational step size then enters either requested strict owner side.  The proof
uses the exact quadratic expansion and supplies the squared displacement used
by the bounded grid sampler in Lemma 10.3.
-/

namespace FTA
namespace CCLOwnerDirection

open CCL CCL.GaussianRat
open FTA.CCLGeometry

abbrev QI := CCL.GaussianRat

def gradientX (form : HermitianForm) (z : QI) : ℚ :=
  2 * form.radial * z.re + form.realLinear

def gradientY (form : HermitianForm) (z : QI) : ℚ :=
  2 * form.radial * z.im + form.imagLinear

def directionalSlope (form : HermitianForm) (z direction : QI) : ℚ :=
  gradientX form z * direction.re + gradientY form z * direction.im

/-- Algebraic nondegeneracy invariant of a generalized circle or line. -/
def boundaryDiscriminant (form : HermitianForm) : ℚ :=
  4 * form.radial * form.constant - form.realLinear ^ 2 -
    form.imagLinear ^ 2

/-- Constant obstruction to expressing the dot product of two gradients as
a linear combination of the two defining Hermitian forms. -/
def gradientPairingConstant (left right : HermitianForm) : ℚ :=
  left.realLinear * right.realLinear +
      left.imagLinear * right.imagLinear -
    2 * right.radial * left.constant -
    2 * left.radial * right.constant

theorem gradient_pairing_identity
    (left right : HermitianForm) (z : QI) :
    gradientX left z * gradientX right z +
        gradientY left z * gradientY right z =
      2 * right.radial * left.eval z +
        2 * left.radial * right.eval z +
          gradientPairingConstant left right := by
  simp only [gradientX, gradientY, HermitianForm.eval,
    gradientPairingConstant, normSq]
  ring

@[simp] theorem gradientPairingConstant_neg_left
    (left right : HermitianForm) :
    gradientPairingConstant left.neg right =
      -gradientPairingConstant left right := by
  simp [gradientPairingConstant, HermitianForm.neg]
  ring

@[simp] theorem gradientPairingConstant_neg_right
    (left right : HermitianForm) :
    gradientPairingConstant left right.neg =
      -gradientPairingConstant left right := by
  simp [gradientPairingConstant, HermitianForm.neg]
  ring

/-- Real and imaginary coordinate comparisons through one decoder have zero
gradient-pairing obstruction, independently of their two thresholds. -/
theorem gradientPairingConstant_real_imag
    (M : Mat2 QI) (realThreshold imagThreshold : ℚ) :
    gradientPairingConstant (realComparisonForm M realThreshold)
      (imagComparisonForm M imagThreshold) = 0 := by
  simp only [gradientPairingConstant, realComparisonForm,
    imagComparisonForm, HermitianForm.sub, HermitianForm.add,
    HermitianForm.neg, HermitianForm.scale, realCrossForm, imagCrossForm,
    affineNormForm, normSq]
  ring

@[simp] theorem boundaryDiscriminant_neg (form : HermitianForm) :
    boundaryDiscriminant form.neg = boundaryDiscriminant form := by
  simp [boundaryDiscriminant, HermitianForm.neg]

theorem boundaryDiscriminant_scale (scale : ℚ) (form : HermitianForm) :
    boundaryDiscriminant (HermitianForm.scale scale form) =
      scale ^ 2 * boundaryDiscriminant form := by
  simp [boundaryDiscriminant, HermitianForm.scale]
  ring

theorem gradient_discriminant_identity (form : HermitianForm) (z : QI) :
    4 * form.radial * form.eval z =
      gradientX form z ^ 2 + gradientY form z ^ 2 +
        boundaryDiscriminant form := by
  simp only [HermitianForm.eval, gradientX, gradientY, boundaryDiscriminant,
    normSq]
  ring

theorem gradient_nonzero_of_boundaryDiscriminant
    (form : HermitianForm) (z : QI)
    (nondegenerate : boundaryDiscriminant form ≠ 0)
    (onBoundary : form.eval z = 0) :
    gradientX form z ≠ 0 ∨ gradientY form z ≠ 0 := by
  by_contra hgradient
  have hx : gradientX form z = 0 := by
    by_contra hx
    exact (not_or.mp hgradient).1 hx
  have hy : gradientY form z = 0 := by
    by_contra hy
    exact (not_or.mp hgradient).2 hy
  have hidentity := gradient_discriminant_identity form z
  rw [onBoundary, hx, hy] at hidentity
  norm_num at hidentity
  exact nondegenerate hidentity.symm

theorem boundaryDiscriminant_normComparisonForm
    (M : Mat2 QI) (radiusSq : ℚ) :
    boundaryDiscriminant (normComparisonForm M radiusSq) =
      -4 * radiusSq * normSq (determinant M) := by
  simp only [boundaryDiscriminant, normComparisonForm, HermitianForm.sub,
    HermitianForm.add, HermitianForm.neg, HermitianForm.scale, affineNormForm,
    determinant, normSq, mul_re, mul_im, sub_re, sub_im]
  ring

theorem boundaryDiscriminant_realComparisonForm
    (M : Mat2 QI) (threshold : ℚ) :
    boundaryDiscriminant (realComparisonForm M threshold) =
      -normSq (determinant M) := by
  simp only [boundaryDiscriminant, realComparisonForm, HermitianForm.sub,
    HermitianForm.add, HermitianForm.neg, HermitianForm.scale, realCrossForm,
    affineNormForm, determinant, normSq, mul_re, mul_im, sub_re, sub_im]
  ring

theorem boundaryDiscriminant_imagComparisonForm
    (M : Mat2 QI) (threshold : ℚ) :
    boundaryDiscriminant (imagComparisonForm M threshold) =
      -normSq (determinant M) := by
  simp only [boundaryDiscriminant, imagComparisonForm, HermitianForm.sub,
    HermitianForm.add, HermitianForm.neg, HermitianForm.scale, imagCrossForm,
    affineNormForm, determinant, normSq, mul_re, mul_im, sub_re, sub_im]
  ring

theorem boundaryDiscriminant_normComparisonForm_ne
    (M : Mat2 QI) (radiusSq : ℚ)
    (determinantNonzero : determinant M ≠ 0)
    (radiusNonzero : radiusSq ≠ 0) :
    boundaryDiscriminant (normComparisonForm M radiusSq) ≠ 0 := by
  rw [boundaryDiscriminant_normComparisonForm]
  exact mul_ne_zero (mul_ne_zero (by norm_num) radiusNonzero)
    (normSq_pos determinantNonzero).ne'

theorem boundaryDiscriminant_realComparisonForm_ne
    (M : Mat2 QI) (threshold : ℚ)
    (determinantNonzero : determinant M ≠ 0) :
    boundaryDiscriminant (realComparisonForm M threshold) ≠ 0 := by
  rw [boundaryDiscriminant_realComparisonForm]
  exact neg_ne_zero.mpr (normSq_pos determinantNonzero).ne'

theorem boundaryDiscriminant_imagComparisonForm_ne
    (M : Mat2 QI) (threshold : ℚ)
    (determinantNonzero : determinant M ≠ 0) :
    boundaryDiscriminant (imagComparisonForm M threshold) ≠ 0 := by
  rw [boundaryDiscriminant_imagComparisonForm]
  exact neg_ne_zero.mpr (normSq_pos determinantNonzero).ne'

theorem normComparison_gradient_nonzero
    (M : Mat2 QI) (radiusSq : ℚ) (z : QI)
    (determinantNonzero : determinant M ≠ 0) (radiusPositive : 0 < radiusSq)
    (onBoundary : (normComparisonForm M radiusSq).eval z = 0) :
    gradientX (normComparisonForm M radiusSq) z ≠ 0 ∨
      gradientY (normComparisonForm M radiusSq) z ≠ 0 := by
  apply gradient_nonzero_of_boundaryDiscriminant _ _ _ onBoundary
  rw [boundaryDiscriminant_normComparisonForm]
  exact mul_ne_zero (mul_ne_zero (by norm_num) radiusPositive.ne')
    (normSq_pos determinantNonzero).ne'

theorem realComparison_gradient_nonzero
    (M : Mat2 QI) (threshold : ℚ) (z : QI)
    (determinantNonzero : determinant M ≠ 0)
    (onBoundary : (realComparisonForm M threshold).eval z = 0) :
    gradientX (realComparisonForm M threshold) z ≠ 0 ∨
      gradientY (realComparisonForm M threshold) z ≠ 0 := by
  apply gradient_nonzero_of_boundaryDiscriminant _ _ _ onBoundary
  rw [boundaryDiscriminant_realComparisonForm]
  exact neg_ne_zero.mpr (normSq_pos determinantNonzero).ne'

theorem imagComparison_gradient_nonzero
    (M : Mat2 QI) (threshold : ℚ) (z : QI)
    (determinantNonzero : determinant M ≠ 0)
    (onBoundary : (imagComparisonForm M threshold).eval z = 0) :
    gradientX (imagComparisonForm M threshold) z ≠ 0 ∨
      gradientY (imagComparisonForm M threshold) z ≠ 0 := by
  apply gradient_nonzero_of_boundaryDiscriminant _ _ _ onBoundary
  rw [boundaryDiscriminant_imagComparisonForm]
  exact neg_ne_zero.mpr (normSq_pos determinantNonzero).ne'

/-- Rational coordinate perturbation by `epsilon * direction`. -/
def step (z : QI) (epsilon : ℚ) (direction : QI) : QI :=
  ⟨z.re + epsilon * direction.re, z.im + epsilon * direction.im⟩

@[simp] theorem step_re (z : QI) (epsilon : ℚ) (direction : QI) :
    (step z epsilon direction).re = z.re + epsilon * direction.re := rfl

@[simp] theorem step_im (z : QI) (epsilon : ℚ) (direction : QI) :
    (step z epsilon direction).im = z.im + epsilon * direction.im := rfl

theorem eval_step (form : HermitianForm) (z direction : QI) (epsilon : ℚ) :
    form.eval (step z epsilon direction) =
      form.eval z + epsilon * directionalSlope form z direction +
        form.radial * epsilon ^ 2 * normSq direction := by
  simp only [HermitianForm.eval, step, gradientX, gradientY, directionalSlope,
    normSq]
  ring

theorem normSq_step_sub (z direction : QI) (epsilon : ℚ) :
    normSq (step z epsilon direction - z) =
      epsilon ^ 2 * normSq direction := by
  simp only [normSq, step, sub_re, sub_im]
  ring

/-- Proof-bearing output of the four-direction rational sign table. -/
structure IncreasingDirection (form : HermitianForm) (z : QI) where
  vector : QI
  unitNorm : normSq vector = 1
  slopePositive : 0 < directionalSlope form z vector

/-- Exact finite selection of `±1` or `±i` from a nonzero gradient. -/
def increasingDirection (form : HermitianForm) (z : QI)
    (gradientNonzero : gradientX form z ≠ 0 ∨ gradientY form z ≠ 0) :
    IncreasingDirection form z := by
  by_cases hx : gradientX form z = 0
  · have hy : gradientY form z ≠ 0 := by
      rcases gradientNonzero with hxNonzero | hyNonzero
      · exact (hxNonzero hx).elim
      · exact hyNonzero
    if hyNeg : gradientY form z < 0 then
      exact
        { vector := ⟨0, -1⟩
          unitNorm := by norm_num [normSq]
          slopePositive := by
            simp only [directionalSlope]
            norm_num
            linarith }
    else if hyPos : 0 < gradientY form z then
      exact
        { vector := ⟨0, 1⟩
          unitNorm := by norm_num [normSq]
          slopePositive := by
            simp only [directionalSlope]
            norm_num
            exact hyPos }
    else
      have hyZero : gradientY form z = 0 :=
        le_antisymm (le_of_not_gt hyPos) (le_of_not_gt hyNeg)
      exact (hy hyZero).elim
  · if hxNeg : gradientX form z < 0 then
      exact
        { vector := ⟨-1, 0⟩
          unitNorm := by norm_num [normSq]
          slopePositive := by
            simp only [directionalSlope]
            norm_num
            linarith }
    else if hxPos : 0 < gradientX form z then
      exact
        { vector := ⟨1, 0⟩
          unitNorm := by norm_num [normSq]
          slopePositive := by
            simp only [directionalSlope]
            norm_num
            exact hxPos }
    else
      have hxZero : gradientX form z = 0 :=
        le_antisymm (le_of_not_gt hxPos) (le_of_not_gt hxNeg)
      exact (hx hxZero).elim

/-- Explicit perturbation scale, small enough that the selected linear term
strictly dominates either sign of the radial quadratic term. -/
def entryScale {form : HermitianForm} {z : QI}
    (direction : IncreasingDirection form z) : ℚ :=
  directionalSlope form z direction.vector /
    (2 * (|form.radial| + 1))

theorem entryScale_pos {form : HermitianForm} {z : QI}
    (direction : IncreasingDirection form z) : 0 < entryScale direction := by
  apply div_pos direction.slopePositive
  positivity

theorem entryScale_lt_linearRadius {form : HermitianForm} {z : QI}
    (direction : IncreasingDirection form z) :
    entryScale direction <
      directionalSlope form z direction.vector / (|form.radial| + 1) := by
  have hden : 0 < |form.radial| + 1 := by positivity
  apply (div_lt_div_iff₀ (mul_pos (by norm_num) hden) hden).2
  nlinarith [direction.slopePositive, hden]

private theorem radial_error_lt_slope
    {form : HermitianForm} {z : QI}
    (direction : IncreasingDirection form z) {epsilon : ℚ}
    (epsilonPos : 0 < epsilon)
    (epsilonSmall : epsilon <
      directionalSlope form z direction.vector / (|form.radial| + 1)) :
    epsilon * |form.radial| < directionalSlope form z direction.vector := by
  have hden : 0 < |form.radial| + 1 := by positivity
  have hscaled : epsilon * (|form.radial| + 1) <
      directionalSlope form z direction.vector :=
    (lt_div_iff₀ hden).mp epsilonSmall
  have hfirst : epsilon * |form.radial| <
      epsilon * (|form.radial| + 1) := by
    nlinarith
  exact hfirst.trans hscaled

theorem eval_step_pos
    {form : HermitianForm} {z : QI}
    (direction : IncreasingDirection form z) (onBoundary : form.eval z = 0)
    {epsilon : ℚ} (epsilonPos : 0 < epsilon)
    (epsilonSmall : epsilon <
      directionalSlope form z direction.vector / (|form.radial| + 1)) :
    0 < form.eval (step z epsilon direction.vector) := by
  rw [eval_step, onBoundary, direction.unitNorm]
  have herror := radial_error_lt_slope direction epsilonPos epsilonSmall
  have hradialLower : -|form.radial| ≤ form.radial := neg_abs_le _
  have hlinear : 0 <
      directionalSlope form z direction.vector + form.radial * epsilon := by
    have hmul := mul_le_mul_of_nonneg_right hradialLower epsilonPos.le
    nlinarith
  nlinarith [mul_pos epsilonPos hlinear]

theorem eval_step_neg
    {form : HermitianForm} {z : QI}
    (direction : IncreasingDirection form z) (onBoundary : form.eval z = 0)
    {epsilon : ℚ} (epsilonPos : 0 < epsilon)
    (epsilonSmall : epsilon <
      directionalSlope form z direction.vector / (|form.radial| + 1)) :
    form.eval (step z epsilon (-direction.vector)) < 0 := by
  rw [eval_step, onBoundary, normSq_neg, direction.unitNorm]
  have hslope : directionalSlope form z (-direction.vector) =
      -directionalSlope form z direction.vector := by
    simp only [directionalSlope, neg_re, neg_im]
    ring
  rw [hslope]
  have herror := radial_error_lt_slope direction epsilonPos epsilonSmall
  have hradialUpper : form.radial ≤ |form.radial| := le_abs_self _
  have hlinear : form.radial * epsilon <
      directionalSlope form z direction.vector := by
    have hmul := mul_le_mul_of_nonneg_right hradialUpper epsilonPos.le
    have herror' : |form.radial| * epsilon <
        directionalSlope form z direction.vector := by
      calc
        |form.radial| * epsilon = epsilon * |form.radial| :=
          _root_.mul_comm _ _
        _ < directionalSlope form z direction.vector := herror
    exact hmul.trans_lt herror'
  nlinarith [mul_pos epsilonPos
    (sub_pos.mpr hlinear)]

/-- The computed positive-owner perturbation enters the strict positive side. -/
theorem eval_positiveEntry_pos
    {form : HermitianForm} {z : QI}
    (direction : IncreasingDirection form z) (onBoundary : form.eval z = 0) :
    0 < form.eval (step z (entryScale direction) direction.vector) :=
  eval_step_pos direction onBoundary (entryScale_pos direction)
    (entryScale_lt_linearRadius direction)

/-- Negating the selected direction enters the strict negative owner side. -/
theorem eval_negativeEntry_neg
    {form : HermitianForm} {z : QI}
    (direction : IncreasingDirection form z) (onBoundary : form.eval z = 0) :
    form.eval (step z (entryScale direction) (-direction.vector)) < 0 :=
  eval_step_neg direction onBoundary (entryScale_pos direction)
    (entryScale_lt_linearRadius direction)

theorem normSq_positiveEntry_sub
    {form : HermitianForm} {z : QI}
    (direction : IncreasingDirection form z) :
    normSq (step z (entryScale direction) direction.vector - z) =
      entryScale direction ^ 2 := by
  rw [normSq_step_sub, direction.unitNorm]
  norm_num

theorem normSq_negativeEntry_sub
    {form : HermitianForm} {z : QI}
    (direction : IncreasingDirection form z) :
    normSq (step z (entryScale direction) (-direction.vector) - z) =
      entryScale direction ^ 2 := by
  rw [normSq_step_sub, normSq_neg, direction.unitNorm]
  norm_num

end CCLOwnerDirection
end FTA
