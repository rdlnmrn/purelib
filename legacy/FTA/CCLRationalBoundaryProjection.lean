import FTA.CCLBranchPlan

/-!
# Constructive rational projection onto CCL boundaries

A rational point whose Hermitian boundary residual is small must be close to
an exact rational point of that boundary.  The circle case uses two explicit
rational charts, choosing the chart whose homogeneous denominator is at least
one.  This avoids square roots and supplies the quantitative bridge from
boundary-neighbourhood exclusion to exact interval signs.
-/

namespace FTA
namespace CCLRationalBoundaryProjection

open CCL CCL.GaussianRat
open FTA.CCLBoundaryPath
open FTA.CCLBranchPlan
open FTA.CCLGeometry
open FTA.CCLOwnerDirection
open FTA.PathPolynomial
open FTA.ProjectivePath

abbrev QI := CCL.GaussianRat

def primaryDenominator (point : QI) : ℚ :=
  (1 + point.re) ^ 2 + point.im ^ 2

def reciprocalDenominator (point : QI) : ℚ :=
  (1 - point.re) ^ 2 + point.im ^ 2

/-- Homogeneous primary-chart retraction onto the rational unit circle. -/
def primaryUnitProjection (point : QI) : QI :=
  ⟨((1 + point.re) ^ 2 - point.im ^ 2) / primaryDenominator point,
    (2 * point.im * (1 + point.re)) / primaryDenominator point⟩

/-- Homogeneous reciprocal-chart retraction onto the rational unit circle. -/
def reciprocalUnitProjection (point : QI) : QI :=
  ⟨(point.im ^ 2 - (1 - point.re) ^ 2) / reciprocalDenominator point,
    (2 * point.im * (1 - point.re)) / reciprocalDenominator point⟩

theorem primaryDenominator_add_reciprocalDenominator (point : QI) :
    primaryDenominator point + reciprocalDenominator point =
      2 * (1 + normSq point) := by
  simp only [primaryDenominator, reciprocalDenominator, normSq]
  ring

theorem reciprocalDenominator_one_le_of_primary_lt
    {point : QI} (primarySmall : primaryDenominator point < 1) :
    1 ≤ reciprocalDenominator point := by
  have normNonnegative := normSq_nonneg point
  have sumIdentity := primaryDenominator_add_reciprocalDenominator point
  nlinarith

theorem normSq_primaryUnitProjection
    (point : QI) (denominatorNonzero : primaryDenominator point ≠ 0) :
    normSq (primaryUnitProjection point) = 1 := by
  simp only [normSq, primaryUnitProjection]
  unfold primaryDenominator at denominatorNonzero ⊢
  field_simp [denominatorNonzero]
  ring

theorem normSq_reciprocalUnitProjection
    (point : QI) (denominatorNonzero : reciprocalDenominator point ≠ 0) :
    normSq (reciprocalUnitProjection point) = 1 := by
  simp only [normSq, reciprocalUnitProjection]
  unfold reciprocalDenominator at denominatorNonzero ⊢
  field_simp [denominatorNonzero]
  ring

theorem normSq_primaryUnitProjection_sub
    (point : QI) (denominatorNonzero : primaryDenominator point ≠ 0) :
    normSq (primaryUnitProjection point - point) =
      (normSq point - 1) ^ 2 / primaryDenominator point := by
  simp only [normSq, primaryUnitProjection, sub_re, sub_im]
  unfold primaryDenominator at denominatorNonzero ⊢
  field_simp [denominatorNonzero]
  ring

theorem normSq_reciprocalUnitProjection_sub
    (point : QI) (denominatorNonzero : reciprocalDenominator point ≠ 0) :
    normSq (reciprocalUnitProjection point - point) =
      (normSq point - 1) ^ 2 / reciprocalDenominator point := by
  simp only [normSq, reciprocalUnitProjection, sub_re, sub_im]
  unfold reciprocalDenominator at denominatorNonzero ⊢
  field_simp [denominatorNonzero]
  ring

/-- Select the quantitatively safe chart of the rational unit-circle
retraction. -/
def rationalUnitProjection (point : QI) : QI :=
  if 1 ≤ primaryDenominator point then
    primaryUnitProjection point
  else
    reciprocalUnitProjection point

theorem normSq_rationalUnitProjection (point : QI) :
    normSq (rationalUnitProjection point) = 1 := by
  by_cases primaryLarge : 1 ≤ primaryDenominator point
  · have denominatorPositive : 0 < primaryDenominator point :=
      zero_lt_one.trans_le primaryLarge
    simp only [rationalUnitProjection, if_pos primaryLarge]
    exact normSq_primaryUnitProjection point denominatorPositive.ne'
  · have reciprocalLarge : 1 ≤ reciprocalDenominator point :=
      reciprocalDenominator_one_le_of_primary_lt (lt_of_not_ge primaryLarge)
    have denominatorPositive : 0 < reciprocalDenominator point :=
      zero_lt_one.trans_le reciprocalLarge
    simp only [rationalUnitProjection, if_neg primaryLarge]
    exact normSq_reciprocalUnitProjection point denominatorPositive.ne'

/-- The selected rational unit-circle retraction has a denominator at least
one, so its squared displacement is at most the squared norm residual. -/
theorem normSq_rationalUnitProjection_sub_le (point : QI) :
    normSq (rationalUnitProjection point - point) ≤
      (normSq point - 1) ^ 2 := by
  by_cases primaryLarge : 1 ≤ primaryDenominator point
  · have denominatorPositive : 0 < primaryDenominator point :=
      zero_lt_one.trans_le primaryLarge
    rw [rationalUnitProjection, if_pos primaryLarge,
      normSq_primaryUnitProjection_sub point denominatorPositive.ne']
    apply (div_le_iff₀ denominatorPositive).2
    have residualNonnegative : 0 ≤ (normSq point - 1) ^ 2 := sq_nonneg _
    have productNonnegative :
        0 ≤ (normSq point - 1) ^ 2 * (primaryDenominator point - 1) :=
      mul_nonneg residualNonnegative (sub_nonneg.mpr primaryLarge)
    nlinarith
  · have reciprocalLarge : 1 ≤ reciprocalDenominator point :=
      reciprocalDenominator_one_le_of_primary_lt (lt_of_not_ge primaryLarge)
    have denominatorPositive : 0 < reciprocalDenominator point :=
      zero_lt_one.trans_le reciprocalLarge
    rw [rationalUnitProjection, if_neg primaryLarge,
      normSq_reciprocalUnitProjection_sub point denominatorPositive.ne']
    apply (div_le_iff₀ denominatorPositive).2
    have residualNonnegative : 0 ≤ (normSq point - 1) ^ 2 := sq_nonneg _
    have productNonnegative :
        0 ≤ (normSq point - 1) ^ 2 *
          (reciprocalDenominator point - 1) :=
      mul_nonneg residualNonnegative (sub_nonneg.mpr reciprocalLarge)
    nlinarith

/-! ## Rational projection onto a nondegenerate Hermitian circle -/

def circleCenter (form : HermitianForm) : QI :=
  ⟨-form.realLinear / (2 * form.radial),
    -form.imagLinear / (2 * form.radial)⟩

theorem eval_sub_eval_eq_radial_mul_centered_normSq_sub
    (form : HermitianForm) (radialNonzero : form.radial ≠ 0)
    (point anchor : QI) :
    form.eval point - form.eval anchor =
      form.radial *
        (normSq (point - circleCenter form) -
          normSq (anchor - circleCenter form)) := by
  simp only [HermitianForm.eval, normSq, circleCenter, sub_re, sub_im]
  field_simp [radialNonzero]
  ring

theorem boundaryDiscriminant_eq_neg_four_mul_radius
    (form : HermitianForm) (radialNonzero : form.radial ≠ 0)
    (anchor : QI) (boundary : form.eval anchor = 0) :
    boundaryDiscriminant form =
      -4 * form.radial ^ 2 * normSq (anchor - circleCenter form) := by
  have identity := gradient_discriminant_identity form anchor
  rw [boundary] at identity
  norm_num at identity
  have gradientNorm :
      gradientX form anchor ^ 2 + gradientY form anchor ^ 2 =
        4 * form.radial ^ 2 * normSq (anchor - circleCenter form) := by
    simp only [gradientX, gradientY, normSq, circleCenter, sub_re, sub_im]
    field_simp [radialNonzero]
    ring
  rw [gradientNorm] at identity
  linarith

theorem circleRadiusVector_ne
    (form : HermitianForm) (radialNonzero : form.radial ≠ 0)
    (discriminantNegative : boundaryDiscriminant form < 0)
    (anchor : QI) (boundary : form.eval anchor = 0) :
    anchor - circleCenter form ≠ 0 := by
  intro radiusZero
  have discriminantIdentity :=
    boundaryDiscriminant_eq_neg_four_mul_radius form radialNonzero anchor
      boundary
  rw [radiusZero, normSq_zero] at discriminantIdentity
  linarith

def circleNormalized
    (form : HermitianForm) (anchor point : QI) : QI :=
  (point - circleCenter form) / (anchor - circleCenter form)

def circleProjection
    (form : HermitianForm) (anchor point : QI) : QI :=
  circleCenter form + (anchor - circleCenter form) *
    rationalUnitProjection (circleNormalized form anchor point)

theorem circleRadius_mul_normalized
    (form : HermitianForm) (anchor point : QI)
    (radiusNonzero : anchor - circleCenter form ≠ 0) :
    (anchor - circleCenter form) * circleNormalized form anchor point =
      point - circleCenter form := by
  simp only [circleNormalized, div_eq_mul_inv]
  calc
    (anchor - circleCenter form) *
          ((point - circleCenter form) * (anchor - circleCenter form)⁻¹) =
        (point - circleCenter form) *
          ((anchor - circleCenter form) * (anchor - circleCenter form)⁻¹) := by
      ring
    _ = point - circleCenter form := by
      simp only [inv_eq]
      rw [GaussianRat.mul_inv _ radiusNonzero, mul_one]

theorem circleProjection_sub_center
    (form : HermitianForm) (anchor point : QI) :
    circleProjection form anchor point - circleCenter form =
      (anchor - circleCenter form) *
        rationalUnitProjection (circleNormalized form anchor point) := by
  apply GaussianRat.ext <;>
    simp only [circleProjection, add_re, add_im, sub_re, sub_im] <;>
    ring

theorem circleProjection_onBoundary
    (form : HermitianForm) (radialNonzero : form.radial ≠ 0)
    (anchor point : QI) (boundary : form.eval anchor = 0) :
    form.eval (circleProjection form anchor point) = 0 := by
  have difference := eval_sub_eval_eq_radial_mul_centered_normSq_sub form
    radialNonzero (circleProjection form anchor point) anchor
  rw [circleProjection_sub_center, normSq_mul,
    normSq_rationalUnitProjection] at difference
  rw [boundary] at difference
  norm_num at difference
  exact difference

theorem normSq_circleNormalized
    (form : HermitianForm) (anchor point : QI)
    (radiusNonzero : anchor - circleCenter form ≠ 0) :
    normSq (circleNormalized form anchor point) =
      normSq (point - circleCenter form) /
        normSq (anchor - circleCenter form) := by
  exact normSq_div _ _ radiusNonzero

theorem circleProjection_sub
    (form : HermitianForm) (anchor point : QI)
    (radiusNonzero : anchor - circleCenter form ≠ 0) :
    circleProjection form anchor point - point =
      (anchor - circleCenter form) *
        (rationalUnitProjection (circleNormalized form anchor point) -
          circleNormalized form anchor point) := by
  have recovered := circleRadius_mul_normalized form anchor point radiusNonzero
  have recoveredRe := congrArg GaussianRat.re recovered
  have recoveredIm := congrArg GaussianRat.im recovered
  apply GaussianRat.ext
  · simp only [circleProjection, add_re, sub_re, sub_im, mul_re] at recoveredRe ⊢
    ring_nf at recoveredRe ⊢
    linarith
  · simp only [circleProjection, add_im, sub_re, sub_im, mul_im] at recoveredIm ⊢
    ring_nf at recoveredIm ⊢
    linarith

theorem normSq_circleProjection_sub_le
    (form : HermitianForm) (radialNonzero : form.radial ≠ 0)
    (anchor point : QI) (boundary : form.eval anchor = 0)
    (radiusNonzero : anchor - circleCenter form ≠ 0) :
    normSq (circleProjection form anchor point - point) ≤
      form.eval point ^ 2 /
        (form.radial ^ 2 * normSq (anchor - circleCenter form)) := by
  let radiusSq := normSq (anchor - circleCenter form)
  have radiusPositive : 0 < radiusSq := normSq_pos radiusNonzero
  have raw := normSq_rationalUnitProjection_sub_le
    (circleNormalized form anchor point)
  have projectionBound :
      normSq (circleProjection form anchor point - point) ≤
        radiusSq * (normSq (circleNormalized form anchor point) - 1) ^ 2 := by
    rw [circleProjection_sub form anchor point radiusNonzero, normSq_mul]
    exact mul_le_mul_of_nonneg_left raw radiusPositive.le
  have normalizedNorm := normSq_circleNormalized form anchor point radiusNonzero
  have evaluationDifference :=
    eval_sub_eval_eq_radial_mul_centered_normSq_sub form radialNonzero point
      anchor
  rw [boundary] at evaluationDifference
  norm_num at evaluationDifference
  rw [normalizedNorm] at projectionBound
  apply projectionBound.trans_eq
  dsimp only [radiusSq] at radiusPositive ⊢
  rw [evaluationDifference]
  field_simp [radiusPositive.ne', radialNonzero]

/-! ## Coordinate projection onto a Hermitian line -/

def realLineProjection (form : HermitianForm) (point : QI) : QI :=
  ⟨point.re - form.eval point / form.realLinear, point.im⟩

def imagLineProjection (form : HermitianForm) (point : QI) : QI :=
  ⟨point.re, point.im - form.eval point / form.imagLinear⟩

theorem realLineProjection_onBoundary
    (form : HermitianForm) (point : QI)
    (radialZero : form.radial = 0)
    (realNonzero : form.realLinear ≠ 0) :
    form.eval (realLineProjection form point) = 0 := by
  simp only [HermitianForm.eval, realLineProjection, normSq]
  rw [radialZero]
  field_simp [realNonzero]
  ring

theorem imagLineProjection_onBoundary
    (form : HermitianForm) (point : QI)
    (radialZero : form.radial = 0)
    (imagNonzero : form.imagLinear ≠ 0) :
    form.eval (imagLineProjection form point) = 0 := by
  simp only [HermitianForm.eval, imagLineProjection, normSq]
  rw [radialZero]
  field_simp [imagNonzero]
  ring

theorem normSq_realLineProjection_sub
    (form : HermitianForm) (point : QI) :
    normSq (realLineProjection form point - point) =
      form.eval point ^ 2 / form.realLinear ^ 2 := by
  simp only [normSq, realLineProjection, sub_re, sub_im]
  ring

theorem normSq_imagLineProjection_sub
    (form : HermitianForm) (point : QI) :
    normSq (imagLineProjection form point - point) =
      form.eval point ^ 2 / form.imagLinear ^ 2 := by
  simp only [normSq, imagLineProjection, sub_re, sub_im]
  ring

/-- An exact rational boundary point together with a positive residual-to-
distance coefficient. -/
structure ProjectionData (form : HermitianForm) (input : QI) where
  point : QI
  coefficient : ℚ
  coefficientPositive : 0 < coefficient
  boundary : form.eval point = 0
  distance : normSq (point - input) ≤ coefficient * form.eval input ^ 2

/-- Residual-to-distance coefficient chosen by the same constructive branch
as the projection itself.  It depends on the boundary, not on the input. -/
def projectionCoefficient (form : HermitianForm) (anchor : QI) : ℚ :=
  if form.radial = 0 then
    if form.realLinear ≠ 0 then 1 / form.realLinear ^ 2
    else 1 / form.imagLinear ^ 2
  else
    1 / (form.radial ^ 2 * normSq (anchor - circleCenter form))

theorem projectionCoefficient_pos
    (form : HermitianForm) (anchor : QI)
    (discriminantNegative : boundaryDiscriminant form < 0)
    (anchorBoundary : form.eval anchor = 0) :
    0 < projectionCoefficient form anchor := by
  by_cases radialZero : form.radial = 0
  · by_cases realNonzero : form.realLinear ≠ 0
    · simp only [projectionCoefficient, if_pos radialZero,
        if_pos realNonzero]
      exact div_pos (by norm_num) (sq_pos_of_ne_zero realNonzero)
    · have realZero : form.realLinear = 0 := not_ne_iff.mp realNonzero
      have imagNonzero : form.imagLinear ≠ 0 := by
        intro imagZero
        simp [boundaryDiscriminant, radialZero, realZero, imagZero] at discriminantNegative
      simp only [projectionCoefficient, if_pos radialZero,
        if_neg realNonzero]
      exact div_pos (by norm_num) (sq_pos_of_ne_zero imagNonzero)
  · have radiusNonzero := circleRadiusVector_ne form radialZero
      discriminantNegative anchor anchorBoundary
    simp only [projectionCoefficient, if_neg radialZero]
    exact div_pos (by norm_num)
      (mul_pos (sq_pos_of_ne_zero radialZero) (normSq_pos radiusNonzero))

/-- Project constructively onto any nondegenerate Hermitian circle or line
having one displayed rational boundary anchor. -/
def projectToHermitianBoundary
    (form : HermitianForm) (anchor input : QI)
    (discriminantNegative : boundaryDiscriminant form < 0)
    (anchorBoundary : form.eval anchor = 0) : ProjectionData form input := by
  by_cases radialZero : form.radial = 0
  · by_cases realNonzero : form.realLinear ≠ 0
    · have squarePositive : 0 < form.realLinear ^ 2 :=
        sq_pos_of_ne_zero realNonzero
      exact
        { point := realLineProjection form input
          coefficient := projectionCoefficient form anchor
          coefficientPositive := by
            simp only [projectionCoefficient, if_pos radialZero,
              if_pos realNonzero]
            exact div_pos (by norm_num) squarePositive
          boundary := realLineProjection_onBoundary form input radialZero
            realNonzero
          distance := by
            rw [normSq_realLineProjection_sub]
            simp only [projectionCoefficient, if_pos radialZero,
              if_pos realNonzero]
            ring_nf
            exact le_rfl }
    · have realZero : form.realLinear = 0 := not_ne_iff.mp realNonzero
      have imagNonzero : form.imagLinear ≠ 0 := by
        intro imagZero
        simp [boundaryDiscriminant, radialZero, realZero, imagZero] at discriminantNegative
      have squarePositive : 0 < form.imagLinear ^ 2 :=
        sq_pos_of_ne_zero imagNonzero
      exact
        { point := imagLineProjection form input
          coefficient := projectionCoefficient form anchor
          coefficientPositive := by
            simp only [projectionCoefficient, if_pos radialZero,
              if_neg realNonzero]
            exact div_pos (by norm_num) squarePositive
          boundary := imagLineProjection_onBoundary form input radialZero
            imagNonzero
          distance := by
            rw [normSq_imagLineProjection_sub]
            simp only [projectionCoefficient, if_pos radialZero,
              if_neg realNonzero]
            ring_nf
            exact le_rfl }
  · let radius := anchor - circleCenter form
    have radiusNonzero : radius ≠ 0 := by
      exact circleRadiusVector_ne form radialZero discriminantNegative anchor
        anchorBoundary
    have denominatorPositive :
        0 < form.radial ^ 2 * normSq radius :=
      mul_pos (sq_pos_of_ne_zero radialZero) (normSq_pos radiusNonzero)
    exact
      { point := circleProjection form anchor input
        coefficient := projectionCoefficient form anchor
        coefficientPositive := by
          simp only [projectionCoefficient, if_neg radialZero]
          exact div_pos (by norm_num) denominatorPositive
        boundary := circleProjection_onBoundary form radialZero anchor input
          anchorBoundary
        distance := by
          have bound := normSq_circleProjection_sub_le form radialZero anchor
            input anchorBoundary radiusNonzero
          apply bound.trans_eq
          simp only [projectionCoefficient, if_neg radialZero]
          ring }

/-! ## Planned CCL boundary sources -/

namespace PlannedBoundarySource

theorem path_denominator_ne_at_zero_or_one
    (source : CCLBranchPlan.BoundarySource)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (nondegenerate : source.ParametrizationNondegenerate) :
    source.path.denominator.eval (PathPolynomial.ofRat 0) ≠ 0 ∨
      source.path.denominator.eval (PathPolynomial.ofRat 1) ≠ 0 := by
  cases source with
  | norm matrix scaleValue =>
      have scaleNonzero : scaleValue ≠ 0 := by
        simpa [CCLBranchPlan.BoundarySource.ParametrizationNondegenerate] using
          nondegenerate
      simpa only [CCLBranchPlan.BoundarySource.path_norm] using
        inverseScaledCirclePath_denominator_ne_at_zero_or_one matrix scaleValue
          determinantNonzero scaleNonzero
  | real matrix threshold =>
      simpa only [CCLBranchPlan.BoundarySource.path_real] using
        inverseRealBoundaryPath_denominator_ne_at_zero_or_one matrix threshold
          determinantNonzero
  | imag matrix threshold =>
      simpa only [CCLBranchPlan.BoundarySource.path_imag] using
        inverseImagBoundaryPath_denominator_ne_at_zero_or_one matrix threshold
          determinantNonzero

/-- Select parameter zero when it is affine and parameter one otherwise. -/
def anchorParameter (source : CCLBranchPlan.BoundarySource) : ℚ :=
  if source.path.denominator.eval (PathPolynomial.ofRat 0) = 0 then 1 else 0

def anchor (source : CCLBranchPlan.BoundarySource) : QI :=
  source.path.value (anchorParameter source)

theorem anchor_denominator_ne
    (source : CCLBranchPlan.BoundarySource)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (nondegenerate : source.ParametrizationNondegenerate) :
    source.path.denominator.eval
      (PathPolynomial.ofRat (anchorParameter source)) ≠ 0 := by
  rcases path_denominator_ne_at_zero_or_one source determinantNonzero
      nondegenerate with atZero | atOne
  · simp [anchorParameter, atZero]
  · by_cases zero :
        source.path.denominator.eval (PathPolynomial.ofRat 0) = 0
    · simpa [anchorParameter, zero] using atOne
    · simp [anchorParameter, zero]

theorem anchor_onBoundary
    (source : CCLBranchPlan.BoundarySource)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (nondegenerate : source.ParametrizationNondegenerate) :
    source.form.eval (anchor source) = 0 := by
  exact source.onBoundary (anchorParameter source) determinantNonzero
    (anchor_denominator_ne source determinantNonzero nondegenerate)

theorem boundaryDiscriminant_neg
    (source : CCLBranchPlan.BoundarySource)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (nondegenerate : source.ParametrizationNondegenerate) :
    boundaryDiscriminant source.form < 0 := by
  cases source with
  | norm matrix scaleValue =>
      have scaleNonzero : scaleValue ≠ 0 := by
        simpa [CCLBranchPlan.BoundarySource.ParametrizationNondegenerate] using
          nondegenerate
      rw [CCLBranchPlan.BoundarySource.form,
        boundaryDiscriminant_normComparisonForm]
      have scalePositive : 0 < normSq scaleValue := normSq_pos scaleNonzero
      have determinantPositive : 0 < normSq (determinant matrix) :=
        normSq_pos determinantNonzero
      nlinarith [mul_pos scalePositive determinantPositive]
  | real matrix threshold =>
      rw [CCLBranchPlan.BoundarySource.form,
        boundaryDiscriminant_realComparisonForm]
      exact neg_neg_of_pos (normSq_pos determinantNonzero)
  | imag matrix threshold =>
      rw [CCLBranchPlan.BoundarySource.form,
        boundaryDiscriminant_imagComparisonForm]
      exact neg_neg_of_pos (normSq_pos determinantNonzero)

/-- Complete constructive projection data for a parser-planned source. -/
def projection
    (source : CCLBranchPlan.BoundarySource) (input : QI)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (nondegenerate : source.ParametrizationNondegenerate) :
    ProjectionData source.form input :=
  projectToHermitianBoundary source.form (anchor source) input
    (boundaryDiscriminant_neg source determinantNonzero nondegenerate)
    (anchor_onBoundary source determinantNonzero nondegenerate)

def coefficient
    (source : CCLBranchPlan.BoundarySource) : ℚ :=
  projectionCoefficient source.form (anchor source)

theorem projection_coefficient
    (source : CCLBranchPlan.BoundarySource) (input : QI)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (nondegenerate : source.ParametrizationNondegenerate) :
    (projection source input determinantNonzero nondegenerate).coefficient =
      coefficient source := by
  unfold projection coefficient projectToHermitianBoundary
  split
  · split <;> rfl
  · rfl

theorem coefficient_pos
    (source : CCLBranchPlan.BoundarySource)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (nondegenerate : source.ParametrizationNondegenerate) :
    0 < coefficient source := by
  exact projectionCoefficient_pos source.form (anchor source)
    (boundaryDiscriminant_neg source determinantNonzero nondegenerate)
    (anchor_onBoundary source determinantNonzero nondegenerate)

end PlannedBoundarySource

end CCLRationalBoundaryProjection
end FTA
