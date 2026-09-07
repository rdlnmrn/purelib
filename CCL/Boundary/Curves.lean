import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.Curve.Canonical
import CCL.Boundary.Formula

/-!
# Rational parameterizations of CCL comparison boundaries

Coordinate lines and centered circles are transported through an invertible
finite homography by its explicit adjugate.  The resulting rational curve is
proved to lie on the corresponding Hermitian comparison boundary at every
non-pole parameter.  This is the provenance-preserving bridge needed before
the cleared gcd/Sturm classifier can inspect parser-formula boundaries.
-/

namespace CCL.CCLBoundaryCurves

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev RationalCurve := CCL.RationalCurve.RationalCurve

open RFAP.ConstructiveGaussian.Gaussian
open CCL.RawParser
open CCL.CCLGeometry

/-- A rational curve proved to lie on one Hermitian zero boundary wherever
its own finite parameter denominator is nonzero. -/
structure Parametrization (form : HermitianForm) where
  curve : RationalCurve
  weightLower : Coordinate
  weightLowerPositive : 0 < weightLower
  weightLower_le : ∀ parameter, weightLower ≤
    CCL.Chordal.Proj.weight
      ⟨curve.numeratorAt parameter, curve.denominatorAt parameter⟩
  projectiveValid : ∀ parameter,
    CCL.Chordal.Proj.HasNonzeroCoordinate
      ⟨curve.numeratorAt parameter, curve.denominatorAt parameter⟩
  onBoundary : ∀ parameter,
    curve.denominatorAt parameter ≠ 0 →
      form.eval (curve.point parameter) = 0

namespace Parametrization

private def transformedWeightLower (matrix : Mat2)
    (sourceLower : Coordinate) : Coordinate :=
  normSq (CCL.CCLPullback.determinant matrix) * sourceLower /
    CCL.Chordal.Mat2.actionWeightCoefficient
      (CCL.CCLPullback.adjugate matrix)

private theorem transformedWeightLower_pos
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    {sourceLower : Coordinate} (sourceLowerPositive : 0 < sourceLower) :
    0 < transformedWeightLower matrix sourceLower := by
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct
      (normSq_pos determinantNonzero) sourceLowerPositive)
    (CCL.Chordal.Mat2.actionWeightCoefficient_pos
      (CCL.CCLPullback.adjugate matrix))

private theorem adjugate_act_act
    (matrix : Mat2) (point : CCL.Chordal.Proj) :
    CCL.Mat2.act (CCL.CCLPullback.adjugate matrix)
        (CCL.Mat2.act matrix point) =
      CCL.Chordal.Proj.scale
        (CCL.CCLPullback.determinant matrix) point := by
  apply CCL.Proj.ext
  · apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [CCL.Mat2.act, CCL.CCLPullback.adjugate,
        CCL.CCLPullback.determinant,
        CCL.Chordal.Mat2.det,
        CCL.Chordal.Proj.scale,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        RFAP.ConstructiveGaussian.Gaussian.neg_re,
        RFAP.ConstructiveGaussian.Gaussian.neg_im] <;>
      ring1
  · apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [CCL.Mat2.act, CCL.CCLPullback.adjugate,
        CCL.CCLPullback.determinant,
        CCL.Chordal.Mat2.det,
        CCL.Chordal.Proj.scale,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        RFAP.ConstructiveGaussian.Gaussian.neg_re,
        RFAP.ConstructiveGaussian.Gaussian.neg_im] <;>
      ring1

private theorem transformedWeightLower_le
    (matrix : Mat2)
    (sourceLower : Coordinate)
    (point : CCL.Chordal.Proj)
    (sourceLowerLe : sourceLower ≤
      CCL.Chordal.Proj.weight point) :
    transformedWeightLower matrix sourceLower ≤
      CCL.Chordal.Proj.weight (CCL.Mat2.act matrix point) := by
  let inverse := CCL.CCLPullback.adjugate matrix
  let coefficient :=
    CCL.Chordal.Mat2.actionWeightCoefficient inverse
  let image := CCL.Mat2.act matrix point
  have coefficientPositive : 0 < coefficient :=
    CCL.Chordal.Mat2.actionWeightCoefficient_pos inverse
  have scaledLower :
      normSq (CCL.CCLPullback.determinant matrix) * sourceLower ≤
        normSq (CCL.CCLPullback.determinant matrix) *
          CCL.Chordal.Proj.weight point :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct sourceLowerLe
      (normSq_nonneg (CCL.CCLPullback.determinant matrix))
  have inverseUpper :=
    CCL.Chordal.Mat2.act_weight_le inverse image
  have inverseIdentity : CCL.Mat2.act inverse image =
      CCL.Chordal.Proj.scale
        (CCL.CCLPullback.determinant matrix) point :=
    adjugate_act_act matrix point
  have scaledWeight :
      CCL.Chordal.Proj.weight
          (CCL.Chordal.Proj.scale
            (CCL.CCLPullback.determinant matrix) point) =
        normSq (CCL.CCLPullback.determinant matrix) *
          CCL.Chordal.Proj.weight point :=
    CCL.Chordal.Proj.weight_scale
      (CCL.CCLPullback.determinant matrix) point
  apply (RFAP.ConstructiveFraction.div_le_iff_pos coefficientPositive).2
  calc
    normSq (CCL.CCLPullback.determinant matrix) * sourceLower ≤
        normSq (CCL.CCLPullback.determinant matrix) *
          CCL.Chordal.Proj.weight point := scaledLower
    _ = CCL.Chordal.Proj.weight
        (CCL.Mat2.act inverse image) := by
      rw [inverseIdentity, scaledWeight]
    _ ≤ coefficient * CCL.Chordal.Proj.weight image := inverseUpper
    _ = CCL.Chordal.Proj.weight image * coefficient :=
      RFAP.ConstructiveFraction.mul_comm _ _

private theorem transformedCurveWeightLower_le
    (matrix : Mat2) (source : RationalCurve)
    (sourceLower : Coordinate)
    (sourceLowerLe : ∀ parameter, sourceLower ≤
      CCL.Chordal.Proj.weight
        ⟨source.numeratorAt parameter, source.denominatorAt parameter⟩)
    (parameter : Coordinate) :
    transformedWeightLower matrix sourceLower ≤
      CCL.Chordal.Proj.weight
        ⟨(source.transform matrix).numeratorAt parameter,
          (source.transform matrix).denominatorAt parameter⟩ := by
  have bound := transformedWeightLower_le matrix sourceLower
    ⟨source.numeratorAt parameter, source.denominatorAt parameter⟩
    (sourceLowerLe parameter)
  simpa only [
    CCL.RationalCurve.RationalCurve.numeratorAt_transform,
    CCL.RationalCurve.RationalCurve.denominatorAt_transform,
    CCL.Mat2.act] using bound

private theorem circleSourceWeightLower
    (curve : RationalCurve)
    (denominatorFormula : ∀ parameter,
      curve.denominatorAt parameter = ⟨parameter ^ 2 + 1, 0⟩)
    (parameter : Coordinate) :
    (1 : Coordinate) ≤ CCL.Chordal.Proj.weight
      ⟨curve.numeratorAt parameter, curve.denominatorAt parameter⟩ := by
  have oneLe : (1 : Coordinate) ≤ parameter ^ 2 + 1 := by
    have added := RFAP.ConstructiveFraction.add_le_add_right_direct
      (RFAP.ConstructiveFraction.sq_nonneg_direct parameter) 1
    simpa only [RFAP.ConstructiveFraction.zero_add] using added
  have squareLe : (1 : Coordinate) ≤ (parameter ^ 2 + 1) ^ 2 := by
    simpa only [one_pow] using
      RFAP.ConstructiveFraction.pow_le_pow_direct (by decide) oneLe 2
  rw [denominatorFormula parameter]
  change 1 ≤ normSq (curve.numeratorAt parameter) +
    ((parameter ^ 2 + 1) ^ 2 + 0 ^ 2)
  exact squareLe.trans (by
    calc
      (parameter ^ 2 + 1) ^ 2 ≤
          normSq (curve.numeratorAt parameter) +
            (parameter ^ 2 + 1) ^ 2 :=
        le_add_of_nonneg_left (normSq_nonneg (curve.numeratorAt parameter))
      _ = normSq (curve.numeratorAt parameter) +
          ((parameter ^ 2 + 1) ^ 2 + 0 ^ 2) := by ring1)

private theorem unitDenominatorSourceWeightLower
    (curve : RationalCurve)
    (denominatorFormula : ∀ parameter,
      curve.denominatorAt parameter = 1)
    (parameter : Coordinate) :
    (1 : Coordinate) ≤ CCL.Chordal.Proj.weight
      ⟨curve.numeratorAt parameter, curve.denominatorAt parameter⟩ := by
  rw [denominatorFormula parameter]
  simp only [CCL.Chordal.Proj.weight, normSq_one]
  have added := RFAP.ConstructiveFraction.add_le_add_right_direct
    (normSq_nonneg (curve.numeratorAt parameter)) 1
  simpa only [RFAP.ConstructiveFraction.zero_add] using added

private theorem transformedProjectiveValid
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    (source : RationalCurve)
    (sourceValid : ∀ parameter,
      CCL.Chordal.Proj.HasNonzeroCoordinate
        ⟨source.numeratorAt parameter, source.denominatorAt parameter⟩)
    (parameter : Coordinate) :
    CCL.Chordal.Proj.HasNonzeroCoordinate
      ⟨(source.transform matrix).numeratorAt parameter,
        (source.transform matrix).denominatorAt parameter⟩ := by
  have acted := CCL.Chordal.Mat2.act_hasNonzeroCoordinate
    (matrix := matrix)
    (point := ⟨source.numeratorAt parameter, source.denominatorAt parameter⟩)
    determinantNonzero (sourceValid parameter)
  simpa only [CCL.Mat2.act,
    CCL.RationalCurve.RationalCurve.numeratorAt_transform,
    CCL.RationalCurve.RationalCurve.denominatorAt_transform]
    using acted

/-- Transport a total source parameterization into the forward/input
coordinate.  The resulting Hermitian form is exactly the adjugate pullback
used by `inputIncrementalAdvanceFormula`. -/
def pushForward
    {form : HermitianForm} (source : Parametrization form)
    (sourceTotal : ∀ parameter, source.curve.denominatorAt parameter ≠ 0)
    (forward : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant forward ≠ 0) :
    Parametrization
      (CCL.CCLPullback.pullbackForm
        (CCL.CCLPullback.adjugate forward) form) := by
  refine
    { curve := source.curve.transform forward
      weightLower := transformedWeightLower forward source.weightLower
      weightLowerPositive := transformedWeightLower_pos forward
        determinantNonzero source.weightLowerPositive
      weightLower_le := transformedCurveWeightLower_le forward source.curve
        source.weightLower source.weightLower_le
      projectiveValid := transformedProjectiveValid forward
        determinantNonzero source.curve source.projectiveValid
      onBoundary := ?_ }
  intro parameter transformedDenominatorNonzero
  have sourceDenominatorNonzero := sourceTotal parameter
  have forwardDenominatorNonzero :
      denominator forward (source.curve.point parameter) ≠ 0 := by
    intro forwardZero
    apply transformedDenominatorNonzero
    rw [CCL.RationalCurve.RationalCurve.denominatorAt_transform_eq
      forward source.curve parameter sourceDenominatorNonzero,
      forwardZero, RFAP.ConstructiveGaussian.Gaussian.zero_mul]
  have pointIdentity :=
    CCL.RationalCurve.RationalCurve.point_transform
      forward source.curve parameter sourceDenominatorNonzero
        forwardDenominatorNonzero
  have inverseDenominatorNonzero :=
    CCL.CCLPullback.adjugate_denominator_homographic_ne
      forward (source.curve.point parameter) determinantNonzero
        forwardDenominatorNonzero
  have inverseIdentity :=
    CCL.CCLPullback.homographic_adjugate_forward_inverse
      forward (source.curve.point parameter) determinantNonzero
        forwardDenominatorNonzero
  rw [show (source.curve.transform forward).point parameter =
      homographic forward (source.curve.point parameter) by
        exact pointIdentity,
    CCL.CCLPullback.eval_pullbackForm
      (CCL.CCLPullback.adjugate forward) form _
        inverseDenominatorNonzero,
    inverseIdentity,
    source.onBoundary parameter sourceDenominatorNonzero,
    RFAP.ConstructiveFraction.mul_zero_direct]

end Parametrization

private theorem adjugateDeterminantNonzero
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0) :
    CCL.CCLPullback.determinant
      (CCL.CCLPullback.adjugate matrix) ≠ 0 := by
  rw [CCL.CCLPullback.determinant_adjugate]
  exact determinantNonzero

private theorem transformedCanonicalProjectiveValid
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    (source : RationalCurve)
    (sourceTotal : ∀ parameter, source.denominatorAt parameter ≠ 0)
    (parameter : Coordinate) :
    CCL.Chordal.Proj.HasNonzeroCoordinate
      ⟨(source.transform
          (CCL.CCLPullback.adjugate matrix)).numeratorAt parameter,
        (source.transform
          (CCL.CCLPullback.adjugate matrix)).denominatorAt
            parameter⟩ :=
  Parametrization.transformedProjectiveValid
    (CCL.CCLPullback.adjugate matrix)
    (adjugateDeterminantNonzero matrix determinantNonzero) source
    (fun point => Or.inr (sourceTotal point)) parameter

private theorem adjugate_denominator_ne_of_transform
    (matrix : Mat2) (source : RationalCurve) (parameter : Coordinate)
    (sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0)
    (transformedDenominatorNonzero :
      (source.transform
        (CCL.CCLPullback.adjugate matrix)).denominatorAt
          parameter ≠ 0) :
    denominator (CCL.CCLPullback.adjugate matrix)
      (source.point parameter) ≠ 0 := by
  intro inverseDenominatorZero
  apply transformedDenominatorNonzero
  rw [CCL.RationalCurve.RationalCurve.denominatorAt_transform_eq
    (CCL.CCLPullback.adjugate matrix) source parameter
      sourceDenominatorNonzero,
    inverseDenominatorZero,
    RFAP.ConstructiveGaussian.Gaussian.zero_mul]

private theorem transformed_point_eq_inverse
    (matrix : Mat2) (source : RationalCurve) (parameter : Coordinate)
    (sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0)
    (inverseDenominatorNonzero :
      denominator (CCL.CCLPullback.adjugate matrix)
        (source.point parameter) ≠ 0) :
    (source.transform
      (CCL.CCLPullback.adjugate matrix)).point parameter =
        homographic (CCL.CCLPullback.adjugate matrix)
          (source.point parameter) :=
  CCL.RationalCurve.RationalCurve.point_transform
    (CCL.CCLPullback.adjugate matrix) source parameter
      sourceDenominatorNonzero inverseDenominatorNonzero

/-- Pull the canonical vertical line back through an invertible homography. -/
def realComparison
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    (threshold : Coordinate) :
    Parametrization (realComparisonForm matrix threshold) := by
  let source := CCL.CanonicalCurves.realLine threshold
  refine
    { curve := source.transform
        (CCL.CCLPullback.adjugate matrix)
      weightLower := Parametrization.transformedWeightLower
        (CCL.CCLPullback.adjugate matrix) 1
      weightLowerPositive := Parametrization.transformedWeightLower_pos
        (CCL.CCLPullback.adjugate matrix)
          (adjugateDeterminantNonzero matrix determinantNonzero) (by decide)
      weightLower_le := Parametrization.transformedCurveWeightLower_le
        (CCL.CCLPullback.adjugate matrix) source 1
        (Parametrization.unitDenominatorSourceWeightLower source
          (CCL.CanonicalCurves.realLine_denominatorAt threshold))
      projectiveValid := transformedCanonicalProjectiveValid matrix
        determinantNonzero source
          (CCL.CanonicalCurves.realLine_denominator_ne threshold)
      onBoundary := ?_ }
  intro parameter transformedDenominatorNonzero
  have sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0 :=
    CCL.CanonicalCurves.realLine_denominator_ne
      threshold parameter
  have inverseDenominatorNonzero :=
    adjugate_denominator_ne_of_transform matrix source parameter
      sourceDenominatorNonzero transformedDenominatorNonzero
  have pointIdentity := transformed_point_eq_inverse matrix source parameter
    sourceDenominatorNonzero inverseDenominatorNonzero
  have forwardDenominatorNonzero :=
    CCL.CCLPullback.denominator_inverse_tail_ne matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  have inverseIdentity :=
    CCL.CCLPullback.homographic_adjugate_inverse matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  rw [show (source.transform
      (CCL.CCLPullback.adjugate matrix)).point parameter =
      homographic (CCL.CCLPullback.adjugate matrix)
        (source.point parameter) by exact pointIdentity]
  apply (real_homographic_eq_iff matrix _ threshold
    forwardDenominatorNonzero).1
  rw [inverseIdentity]
  exact congrArg RFAP.ConstructiveGaussian.Gaussian.re
    (CCL.CanonicalCurves.realLine_point threshold parameter)

/-- Pull the canonical horizontal line back through an invertible
homography. -/
def imaginaryComparison
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    (threshold : Coordinate) :
    Parametrization (imagComparisonForm matrix threshold) := by
  let source := CCL.CanonicalCurves.imaginaryLine threshold
  refine
    { curve := source.transform
        (CCL.CCLPullback.adjugate matrix)
      weightLower := Parametrization.transformedWeightLower
        (CCL.CCLPullback.adjugate matrix) 1
      weightLowerPositive := Parametrization.transformedWeightLower_pos
        (CCL.CCLPullback.adjugate matrix)
          (adjugateDeterminantNonzero matrix determinantNonzero) (by decide)
      weightLower_le := Parametrization.transformedCurveWeightLower_le
        (CCL.CCLPullback.adjugate matrix) source 1
        (Parametrization.unitDenominatorSourceWeightLower source
          (CCL.CanonicalCurves.imaginaryLine_denominatorAt
            threshold))
      projectiveValid := transformedCanonicalProjectiveValid matrix
        determinantNonzero source
          (CCL.CanonicalCurves.imaginaryLine_denominator_ne
            threshold)
      onBoundary := ?_ }
  intro parameter transformedDenominatorNonzero
  have sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0 :=
    CCL.CanonicalCurves.imaginaryLine_denominator_ne
      threshold parameter
  have inverseDenominatorNonzero :=
    adjugate_denominator_ne_of_transform matrix source parameter
      sourceDenominatorNonzero transformedDenominatorNonzero
  have pointIdentity := transformed_point_eq_inverse matrix source parameter
    sourceDenominatorNonzero inverseDenominatorNonzero
  have forwardDenominatorNonzero :=
    CCL.CCLPullback.denominator_inverse_tail_ne matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  have inverseIdentity :=
    CCL.CCLPullback.homographic_adjugate_inverse matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  rw [show (source.transform
      (CCL.CCLPullback.adjugate matrix)).point parameter =
      homographic (CCL.CCLPullback.adjugate matrix)
        (source.point parameter) by exact pointIdentity]
  apply (imag_homographic_eq_iff matrix _ threshold
    forwardDenominatorNonzero).1
  rw [inverseIdentity]
  exact congrArg RFAP.ConstructiveGaussian.Gaussian.im
    (CCL.CanonicalCurves.imaginaryLine_point threshold parameter)

/-- Pull a centered circle through an invertible homography.  The displayed
base point supplies the rational stereographic parameterization. -/
def normComparison
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    (base : Gaussian) :
    Parametrization (normComparisonForm matrix (normSq base)) := by
  let source := CCL.CanonicalCurves.circle base
  refine
    { curve := source.transform
        (CCL.CCLPullback.adjugate matrix)
      weightLower := Parametrization.transformedWeightLower
        (CCL.CCLPullback.adjugate matrix) 1
      weightLowerPositive := Parametrization.transformedWeightLower_pos
        (CCL.CCLPullback.adjugate matrix)
          (adjugateDeterminantNonzero matrix determinantNonzero) (by decide)
      weightLower_le := Parametrization.transformedCurveWeightLower_le
        (CCL.CCLPullback.adjugate matrix) source 1
        (Parametrization.circleSourceWeightLower source
          (CCL.CanonicalCurves.circle_denominatorAt base))
      projectiveValid := transformedCanonicalProjectiveValid matrix
        determinantNonzero source
          (CCL.CanonicalCurves.circle_denominator_ne base)
      onBoundary := ?_ }
  intro parameter transformedDenominatorNonzero
  have sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0 :=
    CCL.CanonicalCurves.circle_denominator_ne base parameter
  have inverseDenominatorNonzero :=
    adjugate_denominator_ne_of_transform matrix source parameter
      sourceDenominatorNonzero transformedDenominatorNonzero
  have pointIdentity := transformed_point_eq_inverse matrix source parameter
    sourceDenominatorNonzero inverseDenominatorNonzero
  have forwardDenominatorNonzero :=
    CCL.CCLPullback.denominator_inverse_tail_ne matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  have inverseIdentity :=
    CCL.CCLPullback.homographic_adjugate_inverse matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  rw [show (source.transform
      (CCL.CCLPullback.adjugate matrix)).point parameter =
      homographic (CCL.CCLPullback.adjugate matrix)
        (source.point parameter) by exact pointIdentity]
  apply (norm_homographic_eq_iff matrix _ (normSq base)
    forwardDenominatorNonzero).1
  rw [inverseIdentity]
  exact CCL.CanonicalCurves.normSq_circle_point base parameter

/-- Reciprocal chart of the same pulled-back centered norm boundary.  Its
zero parameter supplies the projective point missed by `normComparison`. -/
def normComparisonReciprocal
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    (base : Gaussian) :
    Parametrization (normComparisonForm matrix (normSq base)) := by
  let source := CCL.CanonicalCurves.reciprocalCircle base
  refine
    { curve := source.transform
        (CCL.CCLPullback.adjugate matrix)
      weightLower := Parametrization.transformedWeightLower
        (CCL.CCLPullback.adjugate matrix) 1
      weightLowerPositive := Parametrization.transformedWeightLower_pos
        (CCL.CCLPullback.adjugate matrix)
          (adjugateDeterminantNonzero matrix determinantNonzero) (by decide)
      weightLower_le := Parametrization.transformedCurveWeightLower_le
        (CCL.CCLPullback.adjugate matrix) source 1
        (Parametrization.circleSourceWeightLower source
          (CCL.CanonicalCurves.reciprocalCircle_denominatorAt
            base))
      projectiveValid := transformedCanonicalProjectiveValid matrix
        determinantNonzero source
          (CCL.CanonicalCurves.reciprocalCircle_denominator_ne base)
      onBoundary := ?_ }
  intro parameter transformedDenominatorNonzero
  have sourceDenominatorNonzero : source.denominatorAt parameter ≠ 0 :=
    CCL.CanonicalCurves.reciprocalCircle_denominator_ne
      base parameter
  have inverseDenominatorNonzero :=
    adjugate_denominator_ne_of_transform matrix source parameter
      sourceDenominatorNonzero transformedDenominatorNonzero
  have pointIdentity := transformed_point_eq_inverse matrix source parameter
    sourceDenominatorNonzero inverseDenominatorNonzero
  have forwardDenominatorNonzero :=
    CCL.CCLPullback.denominator_inverse_tail_ne matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  have inverseIdentity :=
    CCL.CCLPullback.homographic_adjugate_inverse matrix
      (source.point parameter) determinantNonzero inverseDenominatorNonzero
  rw [show (source.transform
      (CCL.CCLPullback.adjugate matrix)).point parameter =
      homographic (CCL.CCLPullback.adjugate matrix)
        (source.point parameter) by exact pointIdentity]
  apply (norm_homographic_eq_iff matrix _ (normSq base)
    forwardDenominatorNonzero).1
  rw [inverseIdentity]
  exact CCL.CanonicalCurves.normSq_reciprocalCircle_point
    base parameter

/-- Canonical centered norm boundary. -/
def affineNorm (base : Gaussian) :
    Parametrization
      (CCL.CCLFormula.affineNormComparisonForm (normSq base)) := by
  let curve := CCL.CanonicalCurves.circle base
  refine
    { curve := curve
      weightLower := 1
      weightLowerPositive := by decide
      weightLower_le := Parametrization.circleSourceWeightLower curve
        (CCL.CanonicalCurves.circle_denominatorAt base)
      projectiveValid := fun parameter => Or.inr
        (CCL.CanonicalCurves.circle_denominator_ne base parameter)
      onBoundary := ?_ }
  intro parameter _denominatorNonzero
  rw [CCL.CCLFormula.eval_affineNormComparisonForm,
    CCL.CanonicalCurves.normSq_circle_point]
  ring1

/-- Boundary `normSq z = 2^exponent`. -/
def affineNormDyadic (exponent : Nat) :
    Parametrization
      (CCL.CCLFormula.affineNormComparisonForm
        ((2 : Coordinate) ^ exponent)) := by
  let curve := CCL.CanonicalCurves.dyadicCircle exponent
  refine
    { curve := curve
      weightLower := 1
      weightLowerPositive := by decide
      weightLower_le := Parametrization.circleSourceWeightLower curve
        (by
          intro parameter
          exact CCL.CanonicalCurves.circle_denominatorAt
            (natPow gamma exponent) parameter)
      projectiveValid := fun parameter => Or.inr (by
        simpa [curve, CCL.CanonicalCurves.dyadicCircle] using
          CCL.CanonicalCurves.circle_denominator_ne
            (natPow gamma exponent) parameter)
      onBoundary := ?_ }
  intro parameter _denominatorNonzero
  rw [CCL.CCLFormula.eval_affineNormComparisonForm,
    CCL.CanonicalCurves.normSq_dyadicCircle_point]
  ring1

theorem affineNormDyadic_total (exponent : Nat) (parameter : Coordinate) :
    (affineNormDyadic exponent).curve.denominatorAt parameter ≠ 0 :=
  by
    simpa [affineNormDyadic, CCL.CanonicalCurves.dyadicCircle]
      using
      CCL.CanonicalCurves.circle_denominator_ne
        (natPow gamma exponent) parameter

/-- Boundary `2^exponent * normSq z = 1`. -/
def scaledNormOne (exponent : Nat) :
    Parametrization
      (CCL.CCLFormula.scaledNormComparisonForm exponent 1) := by
  let curve := CCL.CanonicalCurves.inverseDyadicCircle exponent
  refine
    { curve := curve
      weightLower := 1
      weightLowerPositive := by decide
      weightLower_le := Parametrization.circleSourceWeightLower curve
        (CCL.CanonicalCurves.circle_denominatorAt
          ((natPow gamma exponent)⁻¹))
      projectiveValid := fun parameter => Or.inr
        (CCL.CanonicalCurves.circle_denominator_ne
          ((natPow gamma exponent)⁻¹) parameter)
      onBoundary := ?_ }
  intro parameter _denominatorNonzero
  rw [CCL.CCLFormula.eval_scaledNormComparisonForm,
    CCL.CanonicalCurves.normSq_inverseDyadicCircle_point]
  have powerPositive : 0 < (2 : Coordinate) ^ exponent :=
    RFAP.ConstructiveFraction.pow_pos_direct (by decide) exponent
  rw [RFAP.ConstructiveFraction.mul_inv_cancel _ powerPositive.ne']
  ring1

theorem scaledNormOne_total (exponent : Nat) (parameter : Coordinate) :
    (scaledNormOne exponent).curve.denominatorAt parameter ≠ 0 :=
  CCL.CanonicalCurves.circle_denominator_ne
    ((natPow gamma exponent)⁻¹) parameter

/-- Boundary `2^exponent * normSq z = 2`. -/
def scaledNormTwo (exponent : Nat) :
    Parametrization
      (CCL.CCLFormula.scaledNormComparisonForm exponent 2) := by
  let curve := CCL.CanonicalCurves.lowUpperCircle exponent
  refine
    { curve := curve
      weightLower := 1
      weightLowerPositive := by decide
      weightLower_le := Parametrization.circleSourceWeightLower curve (by
        intro parameter
        cases exponent with
        | zero =>
            exact CCL.CanonicalCurves.circle_denominatorAt
              (natPow gamma 1) parameter
        | succ exponent =>
            exact CCL.CanonicalCurves.circle_denominatorAt
              ((natPow gamma exponent)⁻¹) parameter)
      projectiveValid := fun parameter => Or.inr (by
        cases exponent with
        | zero =>
            exact CCL.CanonicalCurves.circle_denominator_ne
              (natPow gamma 1) parameter
        | succ exponent =>
            exact CCL.CanonicalCurves.circle_denominator_ne
              ((natPow gamma exponent)⁻¹) parameter)
      onBoundary := ?_ }
  intro parameter _denominatorNonzero
  rw [CCL.CCLFormula.eval_scaledNormComparisonForm,
    CCL.CanonicalCurves.scaled_normSq_lowUpperCircle_point]
  ring1

theorem scaledNormTwo_total (exponent : Nat) (parameter : Coordinate) :
    (scaledNormTwo exponent).curve.denominatorAt parameter ≠ 0 := by
  cases exponent with
  | zero =>
      exact CCL.CanonicalCurves.circle_denominator_ne
        (natPow gamma 1) parameter
  | succ exponent =>
      exact CCL.CanonicalCurves.circle_denominator_ne
        ((natPow gamma exponent)⁻¹) parameter

end CCL.CCLBoundaryCurves
