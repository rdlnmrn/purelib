import CCL.Riemann.PreparedSheetContinuation
import CCL.Riemann.AlgebraicDifferentials
import CCL.Riemann.BranchCutLifts

/-!
# Uniform algebraic models on prepared continuation cells

This module connects the diameter-prepared square-root continuation with the
uniform integration semantics.  Every rational point query is answered from
the owner transported from the prepared left endpoint, so it cannot silently
choose the other square root by a fresh pointwise isolation.

The first constructor intentionally uses the zero polynomial.  It is a coarse
but honest local model: after one finite refinement of the differential CCL,
its displayed allowance pays for the complete enclosure and the zero-model
discrepancy.  Later constructors can replace this model by midpoint or Taylor
polynomials while reusing the owner-backed query machinery.
-/

namespace CCL.Riemann.PreparedDifferentialModels

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchCuts
open CCL.Riemann.BranchCutLifts
open CCL.Riemann.LiftedPaths

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner
abbrev Endpoint := CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint
abbrev StepRequest := CCL.Riemann.PreparedSheetContinuation.StepRequest
abbrev CellModel := CCL.ProgressiveGaussianIntegration.CellModel

/-- Residual-only denominator floor retained as one component of the
coordinate-line estimate. -/
def residualDenominatorLower {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  min 1 (segment.clearanceBound / 4) / 8

/-- Dyadic magnitude floor obtained from the same positive radicand
norm-square clearance, without extracting a completed square root. -/
def magnitudeDenominatorLower {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  (CCL.FiniteGeometric.dyadicSquareRadius (segment.clearanceBound / 2) / 2) / 8

/-- A single positive denominator lower bound valid at every rational point
of the certified coordinate line.  The residual component preserves the
original proof, while the dyadic component uses the dominant rational
coordinate exposed by `SquareRootSheets.sampleNormLower`. -/
def denominatorLower {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  max (residualDenominatorLower segment) (magnitudeDenominatorLower segment)

theorem denominatorLower_positive {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < denominatorLower segment :=
  (RFAP.ConstructiveFraction.div_pos_direct
      (lt_min (by decide)
        (RFAP.ConstructiveFraction.div_pos_direct
          segment.clearanceBound_positive (by decide)))
      (by decide)).trans_le (le_max_left _ _)

theorem denominatorLower_le_point {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish value : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (onLine : segment.OnCertifiedLine value) :
    denominatorLower segment <=
      CCL.Riemann.SquareRootSheets.sampleNormLower
        (polynomial.eval value) / 8 := by
  have evaluationLower := segment.clearanceBound_le_eval_normSq onLine
  apply max_le
  · have divided : segment.clearanceBound / 4 <=
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval value) / 4 := by
      rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        evaluationLower (by decide)
    have minimum := min_le_min (le_refl (1 : Coordinate)) divided
    have residualLower : residualDenominatorLower segment <=
        min 1 (RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval value) / 4) / 8 := by
      unfold residualDenominatorLower
      rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        minimum (by decide)
    exact residualLower.trans (by
      rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (le_max_left _ _) (by decide))
  · have dyadicLower :=
      CCL.Riemann.SquareRootSheets.dyadicSquareRadius_half_le_coordinateNormLower
        segment.clearanceBound_positive evaluationLower
    have halfLower :
        CCL.FiniteGeometric.dyadicSquareRadius
              (segment.clearanceBound / 2) / 2 <=
            CCL.Riemann.SquareRootSheets.coordinateNormLower
              (polynomial.eval value) / 2 := by
      rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        dyadicLower (by decide)
    have sampleLower :
        CCL.FiniteGeometric.dyadicSquareRadius
              (segment.clearanceBound / 2) / 2 <=
            CCL.Riemann.SquareRootSheets.sampleNormLower
              (polynomial.eval value) := by
      exact halfLower.trans (le_max_right _ _)
    unfold magnitudeDenominatorLower
    rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
      RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      sampleLower (by decide)

/-- A rational lower estimate for the radicand norm on one displayed clear
segment.  It is sampled at the segment's left endpoint and pays the complete
finite polynomial-variation budget across that segment.  Unlike the
coordinate-line clearance inherited from the ambient box, this estimate can
improve when a path is geometrically subdivided. -/
def segmentRadicandNormLower {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  RFAP.ConstructiveGaussian.Gaussian.normSq
      (polynomial.eval (segment.pointAt 0)) / 2 -
    CCL.Riemann.ClearSheetContinuation.variationBound segment 0 1

/-- Midpoint-sampled radicand lower estimate.  Every parameter of the unit
segment is at squared distance at most `1/4` from the midpoint, so this pays
only one quarter of the complete variation budget. -/
def segmentMidpointRadicandNormLower
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  RFAP.ConstructiveGaussian.Gaussian.normSq
      (polynomial.eval (segment.pointAt (1 / 2))) / 2 -
    CCL.Riemann.ClearSheetContinuation.variationBound segment 0 1 / 4

/-- Best of the left-endpoint and midpoint finite radicand estimates. -/
def segmentLocalRadicandNormLower
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  max (segmentRadicandNormLower segment)
    (segmentMidpointRadicandNormLower segment)

/-- Square-root-scaled denominator floor derived from the sampled local
radicand bound.  A nonpositive sampled bound contributes zero, leaving the
unconditional coordinate-line floor in control.  When it is positive, the
finite dyadic square radius has the correct magnitude for the norm-square of
the square root. -/
def segmentMagnitudeDenominatorLower
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  if _positive : 0 < segmentLocalRadicandNormLower segment then
    (CCL.FiniteGeometric.dyadicSquareRadius
      (segmentLocalRadicandNormLower segment / 2) / 2) / 8
  else
    0

/-- Denominator lower bound specialized to one geometrically refined clear
segment.  Taking the maximum with the coordinate-line bound preserves
unconditional positivity.  The two sampled terms retain the residual-only
estimate and add the stronger square-root-scaled estimate when the local
radicand bound is positive. -/
def segmentDenominatorLower {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  max
    (max (denominatorLower segment)
      (min 1 (segmentRadicandNormLower segment / 4) / 8))
    (segmentMagnitudeDenominatorLower segment)

theorem segmentDenominatorLower_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < segmentDenominatorLower segment :=
  (denominatorLower_positive segment).trans_le
    ((le_max_left _ _).trans (le_max_left _ _))

/-- The sampled local radicand estimate is valid at every point of the
displayed segment. -/
theorem segmentRadicandNormLower_le_point
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    segmentRadicandNormLower segment <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (polynomial.eval (segment.pointAt parameter)) := by
  have differenceBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval (segment.pointAt 0) -
            polynomial.eval (segment.pointAt parameter)) <=
        CCL.Riemann.ClearSheetContinuation.variationBound segment 0 1 :=
    (CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment
      within 0 parameter (by decide) inside).trans
        (CCL.Riemann.ClearSheetContinuation.variationBound_le_of_between
          segment inside.1 inside.2)
  have triangle :=
    RFAP.ConstructiveGaussian.Gaussian.half_normSq_sub_le_normSq_sub
      (polynomial.eval (segment.pointAt 0))
      (polynomial.eval (segment.pointAt parameter))
  unfold segmentRadicandNormLower
  apply (sub_le_iff_le_add).2
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval (segment.pointAt 0)) / 2 <=
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (polynomial.eval (segment.pointAt 0) -
              polynomial.eval (segment.pointAt parameter)) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (polynomial.eval (segment.pointAt parameter)) :=
      (sub_le_iff_le_add).1 triangle
    _ <= CCL.Riemann.ClearSheetContinuation.variationBound segment 0 1 +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (polynomial.eval (segment.pointAt parameter)) :=
      RFAP.ConstructiveFraction.add_le_add_right_direct differenceBound _
    _ = RFAP.ConstructiveGaussian.Gaussian.normSq
            (polynomial.eval (segment.pointAt parameter)) +
          CCL.Riemann.ClearSheetContinuation.variationBound segment 0 1 :=
      RFAP.ConstructiveFraction.add_comm _ _

/-- The midpoint-to-parameter polynomial variation is bounded by one quarter
of the complete unit-segment variation. -/
theorem variationBound_midpoint_le_quarter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    CCL.Riemann.ClearSheetContinuation.variationBound segment (1 / 2)
        parameter <=
      CCL.Riemann.ClearSheetContinuation.variationBound segment 0 1 / 4 := by
  have squareLe : ((1 / 2 : Coordinate) - parameter) ^ 2 <= 1 / 4 := by
    by_cases lowerHalf : parameter <= (1 / 2 : Coordinate)
    · have differenceNonnegative :
          (0 : Coordinate) <= 1 / 2 - parameter :=
        RFAP.ConstructiveFraction.sub_nonneg_direct lowerHalf
      have differenceLe : 1 / 2 - parameter <= (1 / 2 : Coordinate) :=
        sub_le_self _ inside.1
      exact (RFAP.ConstructiveFraction.pow_le_pow_direct
        differenceNonnegative differenceLe 2).trans_eq (by decide)
    · have halfLe : (1 / 2 : Coordinate) <= parameter :=
        le_of_not_ge lowerHalf
      have differenceNonnegative :
          (0 : Coordinate) <= parameter - 1 / 2 :=
        RFAP.ConstructiveFraction.sub_nonneg_direct halfLe
      have differenceLe : parameter - 1 / 2 <= (1 / 2 : Coordinate) := by
        calc
          parameter - 1 / 2 <= 1 - 1 / 2 :=
            sub_le_sub_right inside.2 _
          _ = 1 / 2 := by decide
      calc
        (1 / 2 - parameter) ^ 2 = (parameter - 1 / 2) ^ 2 := by ring1
        _ <= (1 / 2 : Coordinate) ^ 2 :=
          RFAP.ConstructiveFraction.pow_le_pow_direct
            differenceNonnegative differenceLe 2
        _ = 1 / 4 := by decide
  unfold CCL.Riemann.ClearSheetContinuation.variationBound
  calc
    RFAP.PolynomialBounds.denseLipschitzBound
          (CCL.Riemann.ClearSheetContinuation.segmentPolynomial segment)
          CCL.Riemann.ClearSheetContinuation.parameterAmbient *
        (1 / 2 - parameter) ^ 2 <=
      RFAP.PolynomialBounds.denseLipschitzBound
          (CCL.Riemann.ClearSheetContinuation.segmentPolynomial segment)
          CCL.Riemann.ClearSheetContinuation.parameterAmbient * (1 / 4) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareLe
        (RFAP.PolynomialBounds.denseLipschitzBound_pos
          (CCL.Riemann.ClearSheetContinuation.segmentPolynomial segment)
          CCL.Riemann.ClearSheetContinuation.parameterAmbient).le
    _ = RFAP.PolynomialBounds.denseLipschitzBound
          (CCL.Riemann.ClearSheetContinuation.segmentPolynomial segment)
          CCL.Riemann.ClearSheetContinuation.parameterAmbient *
            (0 - 1) ^ 2 / 4 := by
      rw [show ((0 : Coordinate) - 1) ^ 2 = 1 by decide]
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      ring1

/-- The midpoint sample supplies a valid radicand norm lower bound at every
rational parameter of the segment. -/
theorem segmentMidpointRadicandNormLower_le_point
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    segmentMidpointRadicandNormLower segment <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (polynomial.eval (segment.pointAt parameter)) := by
  have midpointInside :
      (0 : Coordinate) <= 1 / 2 ∧ (1 / 2 : Coordinate) <= 1 := by decide
  have differenceBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval (segment.pointAt (1 / 2)) -
            polynomial.eval (segment.pointAt parameter)) <=
        CCL.Riemann.ClearSheetContinuation.variationBound segment 0 1 / 4 :=
    (CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment
      within (1 / 2) parameter midpointInside inside).trans
        (variationBound_midpoint_le_quarter segment parameter inside)
  have triangle :=
    RFAP.ConstructiveGaussian.Gaussian.half_normSq_sub_le_normSq_sub
      (polynomial.eval (segment.pointAt (1 / 2)))
      (polynomial.eval (segment.pointAt parameter))
  unfold segmentMidpointRadicandNormLower
  apply (sub_le_iff_le_add).2
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval (segment.pointAt (1 / 2))) / 2 <=
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (polynomial.eval (segment.pointAt (1 / 2)) -
              polynomial.eval (segment.pointAt parameter)) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (polynomial.eval (segment.pointAt parameter)) :=
      (sub_le_iff_le_add).1 triangle
    _ <= CCL.Riemann.ClearSheetContinuation.variationBound segment 0 1 / 4 +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (polynomial.eval (segment.pointAt parameter)) :=
      RFAP.ConstructiveFraction.add_le_add_right_direct differenceBound _
    _ = RFAP.ConstructiveGaussian.Gaussian.normSq
            (polynomial.eval (segment.pointAt parameter)) +
          CCL.Riemann.ClearSheetContinuation.variationBound segment 0 1 / 4 :=
      RFAP.ConstructiveFraction.add_comm _ _

/-- The best local sample remains a valid lower bound throughout the segment. -/
theorem segmentLocalRadicandNormLower_le_point
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    segmentLocalRadicandNormLower segment <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (polynomial.eval (segment.pointAt parameter)) := by
  unfold segmentLocalRadicandNormLower
  exact max_le
    (segmentRadicandNormLower_le_point segment within parameter inside)
    (segmentMidpointRadicandNormLower_le_point segment within parameter inside)

/-- The locally sampled bound is a valid lower bound for every productive
square-root denominator queried on the segment. -/
theorem segmentDenominatorLower_le_point
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    segmentDenominatorLower segment <=
      CCL.Riemann.SquareRootSheets.sampleNormLower
        (polynomial.eval (segment.pointAt parameter)) / 8 := by
  apply max_le
  · apply max_le
    · exact denominatorLower_le_point segment
        (segment.pointAt_onCertifiedLine parameter inside)
    · have radicandLower := segmentRadicandNormLower_le_point segment within
        parameter inside
      have quarterLower : segmentRadicandNormLower segment / 4 <=
          RFAP.ConstructiveGaussian.Gaussian.normSq
              (polynomial.eval (segment.pointAt parameter)) / 4 := by
        rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
          RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          radicandLower (by decide)
      have sampledLower :
          min 1 (segmentRadicandNormLower segment / 4) <=
            CCL.Riemann.SquareRootSheets.sampleNormLower
              (polynomial.eval (segment.pointAt parameter)) := by
        unfold CCL.Riemann.SquareRootSheets.sampleNormLower
          CCL.Riemann.SquareRootSheets.residualTarget
        exact (min_le_min le_rfl quarterLower).trans (le_max_left _ _)
      rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        sampledLower (by decide)
  · have radicandLower := segmentLocalRadicandNormLower_le_point segment within
      parameter inside
    by_cases positive : 0 < segmentLocalRadicandNormLower segment
    · have dyadicLower :=
        CCL.Riemann.SquareRootSheets.dyadicSquareRadius_half_le_coordinateNormLower
          positive radicandLower
      have halfLower :
          CCL.FiniteGeometric.dyadicSquareRadius
                (segmentLocalRadicandNormLower segment / 2) / 2 <=
              CCL.Riemann.SquareRootSheets.coordinateNormLower
                (polynomial.eval (segment.pointAt parameter)) / 2 := by
        rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
          RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          dyadicLower (by decide)
      have sampleLower :
          CCL.FiniteGeometric.dyadicSquareRadius
                (segmentLocalRadicandNormLower segment / 2) / 2 <=
              CCL.Riemann.SquareRootSheets.sampleNormLower
                (polynomial.eval (segment.pointAt parameter)) :=
        halfLower.trans (le_max_right _ _)
      rw [segmentMagnitudeDenominatorLower, dif_pos positive,
        RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        sampleLower (by decide)
    · rw [segmentMagnitudeDenominatorLower, dif_neg positive]
      exact (denominatorLower_positive segment).le.trans
        (denominatorLower_le_point segment
          (segment.pointAt_onCertifiedLine parameter inside))

/-- The restricted geometric edge represented by one prepared move. -/
def edge {genus : Nat} (curve : HyperellipticCurve genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (request : StepRequest) :
    ClearSegment curve.polynomial ambient
      (segment.pointAt left.parameter)
      (segment.pointAt request.endpoint.parameter) :=
  segment.restrict within left.parameter request.endpoint.parameter
    left.inside request.endpoint.inside

/-- The division-ready square-root certificate returned by one inherited
point query.  Keeping this certificate separate from the algebraic-sheet
package makes operational transport proofs normalize only the root data they
actually compare. -/
def rootAt {genus : Nat} (curve : HyperellipticCurve genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    CCL.Riemann.CertifiedSquareRoot.Certificate
      (curve.polynomial.eval (segment.pointAt
        (CCL.Riemann.PreparedSheetContinuation.parameterAt left request
          fraction))) :=
  (CCL.Riemann.PreparedSheetContinuation.transportedAt segment within left
    owner request ordered small fraction inside).certificate
      (segment.pointAt_eval_ne_zero
        (CCL.Riemann.PreparedSheetContinuation.parameterAt left request
          fraction)
        (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside left request
          ordered fraction inside))

/-- The same inherited root query using the prepared source already cached in
the accepted subdivision node.  Its proof input remains the canonical
smallness theorem, while its executable owner is reused rather than rebuilt. -/
def rootAtCached {genus : Nat} (curve : HyperellipticCurve genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CCL.Riemann.PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    CCL.Riemann.CertifiedSquareRoot.Certificate
      (curve.polynomial.eval (segment.pointAt
        (CCL.Riemann.PreparedSheetContinuation.parameterAt left request
          fraction))) := by
  let parameter :=
    CCL.Riemann.PreparedSheetContinuation.parameterAt left request fraction
  let parameterNonzero := segment.pointAt_eval_ne_zero parameter
    (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside left request
      ordered fraction inside)
  have pointSmall : RFAP.ConstructiveGaussian.Gaussian.normSq
      (curve.polynomial.eval (segment.pointAt left.parameter) -
        curve.polynomial.eval (segment.pointAt parameter)) <
        cached.preparedOwner.track.initial.clearance.bound := by
    rw [cached.preparedOwner_eq]
    exact CCL.Riemann.PreparedSheetContinuation.pointNormSmall segment within
      left owner request ordered small fraction inside
  exact
    (CCL.Riemann.ExactQuadraticOwnerClearance.reservedTransport
      cached.preparedOwner parameterNonzero pointSmall
        (CCL.Riemann.PreparedSheetContinuation.transportReserve segment left
          request)).certificate parameterNonzero

/-- At the right endpoint, a query through the cached prepared owner has the
same productive root name as the accepted edge's transported endpoint owner. -/
theorem rootAtCached_one_name_eq_transportedRootName {genus : Nat}
    (curve : HyperellipticCurve genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CCL.Riemann.PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (inside : (0 : Coordinate) <= 1 ∧ (1 : Coordinate) <= 1) :
    (rootAtCached curve segment within left owner request cached ordered small
      1 inside).value.name =
      CCL.Riemann.PreparedSheetContinuation.transportedRootName segment within
        left owner request small := by
  rw [CCL.Riemann.PreparedSheetContinuation.CachedSource.eq_canonical cached]
  unfold rootAtCached
    CCL.Riemann.PreparedSheetContinuation.transportedRootName
    CCL.Riemann.PreparedSheetContinuation.transported
  apply
    CCL.Riemann.PreparedSheetContinuation.reservedTransportRootName_proof_irrel

/-- At the left endpoint, a query through the cached prepared owner has the
same productive root name as the canonical zero-displacement query. -/
theorem rootAtCached_zero_name_eq_zeroMoveRootName {genus : Nat}
    (curve : HyperellipticCurve genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CCL.Riemann.PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (inside : (0 : Coordinate) <= 0 ∧ (0 : Coordinate) <= 1) :
    (rootAtCached curve segment within left owner request cached ordered small
      0 inside).value.name =
      CCL.Riemann.PreparedSheetContinuation.zeroMoveRootName segment left owner
        request := by
  rw [CCL.Riemann.PreparedSheetContinuation.CachedSource.eq_canonical cached]
  unfold rootAtCached
    CCL.Riemann.PreparedSheetContinuation.zeroMoveRootName
  apply
    CCL.Riemann.PreparedSheetContinuation.reservedTransportRootName_proof_irrel

/-- The productive name of the inherited point-query root.  This
nondependent projection is the lightweight interface used by operational
boundary comparisons. -/
@[irreducible] def rootNameAt {genus : Nat} (curve : HyperellipticCurve genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    CCL.ProgressiveTransducer.Named :=
  (rootAt curve segment within left owner request ordered small fraction
    inside).value.name

/-- A local point-query name is exactly the owner root obtained by the direct
advance from the prepared left occurrence. -/
theorem rootNameAt_eq_directOwnerRootName {genus : Nat}
    (curve : HyperellipticCurve genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    rootNameAt curve segment within left owner request ordered small fraction
        inside =
      CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero
          (CCL.Riemann.PreparedSheetContinuation.parameterAt left request
            fraction)
          (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside left
            request ordered fraction inside))
        (CCL.Riemann.ExactQuadraticOwnerClearance.reservedTransport
          (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
            request)
          (segment.pointAt_eval_ne_zero
            (CCL.Riemann.PreparedSheetContinuation.parameterAt left request
              fraction)
            (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside left
              request ordered fraction inside))
          (CCL.Riemann.PreparedSheetContinuation.pointNormSmall segment within
            left owner request ordered small fraction inside)
          (CCL.Riemann.PreparedSheetContinuation.transportReserve segment left
            request)) := by
  unfold rootNameAt rootAt
  rw [CCL.Riemann.PreparedSheetContinuation.transportedAt_eq_directAdvance]
  rfl

/-- At the right endpoint, the generic point-query name is definitionally the
name of the transported endpoint owner; only the rational parameter
presentation differs. -/
theorem rootNameAt_one_eq_transportedRootName {genus : Nat}
    (curve : HyperellipticCurve genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (inside : (0 : Coordinate) <= 1 ∧ (1 : Coordinate) <= 1) :
    rootNameAt curve segment within left owner request ordered small 1 inside =
      CCL.Riemann.PreparedSheetContinuation.transportedRootName segment within
        left owner request small := by
  unfold rootNameAt rootAt
  unfold CCL.Riemann.PreparedSheetContinuation.transportedAt
    CCL.Riemann.PreparedSheetContinuation.transportedRootName
    CCL.Riemann.PreparedSheetContinuation.transported
  rfl

/-- At the left endpoint, the generic point-query name is the explicit
zero-displacement move from the prepared source owner. -/
theorem rootNameAt_zero_eq_zeroMoveRootName {genus : Nat}
    (curve : HyperellipticCurve genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (inside : (0 : Coordinate) <= 0 ∧ (0 : Coordinate) <= 1) :
    rootNameAt curve segment within left owner request ordered small 0 inside =
      CCL.Riemann.PreparedSheetContinuation.zeroMoveRootName segment left owner
        request := by
  unfold rootNameAt rootAt CCL.Riemann.PreparedSheetContinuation.transportedAt
    CCL.Riemann.PreparedSheetContinuation.transportedQuery
    CCL.Riemann.PreparedSheetContinuation.zeroMoveRootName
  rfl

/-- Algebraic sheet value at a queried local parameter, inherited from the
prepared source owner by one Rouché transport. -/
def sheetValueAt {genus : Nat} (curve : HyperellipticCurve genus)
    (_differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    AlgebraicSheetValue curve ((edge curve segment within left request).pointAt
      fraction) := by
  let originalParameter :=
    CCL.Riemann.PreparedSheetContinuation.parameterAt left request fraction
  let originalPoint := segment.pointAt originalParameter
  let point := (edge curve segment within left request).pointAt fraction
  have pointEqual : originalPoint = point :=
    CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
      segment within left request fraction
  let root := rootAt curve segment within left owner request ordered small
    fraction inside
  exact
    { value := root.value
      apart := root.apart
      sheet := sheet
      curveEquation :=
        CCL.OperationalEquivalence.NamedEquivalent.trans
          (by
            rw [← pointEqual]
            exact root.square)
          (CCL.OperationalEquivalence.NamedEquivalent.symm
            (CCL.ProjectiveRationalEvaluation.polynomialEval_exact
              curve.polynomial point)) }

/-- Algebraic sheet value backed by the prepared source cached in the
accepted subdivision node. -/
def sheetValueAtCached {genus : Nat} (curve : HyperellipticCurve genus)
    (_differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CCL.Riemann.PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    AlgebraicSheetValue curve ((edge curve segment within left request).pointAt
      fraction) := by
  let originalParameter :=
    CCL.Riemann.PreparedSheetContinuation.parameterAt left request fraction
  let originalPoint := segment.pointAt originalParameter
  let point := (edge curve segment within left request).pointAt fraction
  have pointEqual : originalPoint = point :=
    CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
      segment within left request fraction
  let root := rootAtCached curve segment within left owner request cached
    ordered small fraction inside
  exact
    { value := root.value
      apart := root.apart
      sheet := sheet
      curveEquation :=
        CCL.OperationalEquivalence.NamedEquivalent.trans
          (by
            rw [← pointEqual]
            exact root.square)
          (CCL.OperationalEquivalence.NamedEquivalent.symm
            (CCL.ProjectiveRationalEvaluation.polynomialEval_exact
              curve.polynomial point)) }

@[simp] theorem sheetValueAtCached_apart_lowerSq {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CCL.Riemann.PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (sheetValueAtCached curve differential segment within left owner request
      cached ordered small sheet fraction inside).apart.certificate.lowerSq =
      CCL.Riemann.SquareRootSheets.sampleNormLower
        (curve.polynomial.eval (segment.pointAt
          (CCL.Riemann.PreparedSheetContinuation.parameterAt left request
            fraction))) / 8 := by
  rfl

/-- Every candidate of a cached sheet query remains in the canonical
prepared source box specified by the accepted edge. -/
theorem sheetValueAtCached_candidate_in_prepared_box {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CCL.Riemann.PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (state : (sheetValueAtCached curve differential segment within left owner
      request cached ordered small sheet fraction inside).value.name.process.State)
    {candidate : Gaussian}
    (possible : (sheetValueAtCached curve differential segment within left
      owner request cached ordered small sheet fraction inside).value.name.process.Possible
        state candidate) :
    (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
      request).track.initial.box.Contains candidate := by
  let parameter :=
    CCL.Riemann.PreparedSheetContinuation.parameterAt left request fraction
  let parameterNonzero := segment.pointAt_eval_ne_zero parameter
    (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside left request
      ordered fraction inside)
  have pointSmall : RFAP.ConstructiveGaussian.Gaussian.normSq
      (curve.polynomial.eval (segment.pointAt left.parameter) -
        curve.polynomial.eval (segment.pointAt parameter)) <
        cached.preparedOwner.track.initial.clearance.bound := by
    rw [cached.preparedOwner_eq]
    exact CCL.Riemann.PreparedSheetContinuation.pointNormSmall segment within
      left owner request ordered small fraction inside
  let inherited := CCL.Riemann.ExactQuadraticOwnerClearance.reservedTransport
    cached.preparedOwner parameterNonzero pointSmall
      (CCL.Riemann.PreparedSheetContinuation.transportReserve segment left
        request)
  have candidateInside : inherited.track.initial.box.Contains candidate := by
    apply inherited.certificate_candidate_in_initial_box parameterNonzero state
    simpa only [sheetValueAtCached, rootAtCached, inherited, parameter,
      parameterNonzero, pointSmall] using possible
  have inheritedRefines : inherited.track.initial.box.Refines
      cached.preparedOwner.track.initial.box :=
    CCL.Riemann.ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines
      cached.preparedOwner parameterNonzero pointSmall
        (CCL.Riemann.PreparedSheetContinuation.transportReserve segment left
          request)
  have cachedContains := inheritedRefines.contains candidateInside
  rw [cached.preparedOwner_eq] at cachedContains
  exact cachedContains

@[simp] theorem sheetValueAt_value {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (sheetValueAt curve differential segment within left owner request ordered
      small sheet fraction inside).value =
        (rootAt curve segment within left owner request ordered small fraction
          inside).value := by
  rfl

@[simp] theorem sheetValueAt_apart_lowerSq {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (sheetValueAt curve differential segment within left owner request ordered
      small sheet fraction inside).apart.certificate.lowerSq =
      CCL.Riemann.SquareRootSheets.sampleNormLower
        (curve.polynomial.eval (segment.pointAt
          (CCL.Riemann.PreparedSheetContinuation.parameterAt left request
            fraction))) / 8 := by
  rfl

/-- Every finite denominator candidate returned at any rational point of an
accepted edge lies in the single prepared source root box.  This is stronger
than closeness of the displayed endpoint anchors: it controls all later CCL
refinements used by an integration query. -/
theorem sheetValueAt_candidate_in_prepared_box {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (state : (sheetValueAt curve differential segment within left owner
      request ordered small sheet fraction inside).value.name.process.State)
    {candidate : Gaussian}
    (possible : (sheetValueAt curve differential segment within left owner
      request ordered small sheet fraction inside).value.name.process.Possible
        state candidate) :
    (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
      request).track.initial.box.Contains
      candidate := by
  let parameter :=
    CCL.Riemann.PreparedSheetContinuation.parameterAt left request fraction
  let inherited := CCL.Riemann.PreparedSheetContinuation.transportedAt
    segment within left owner request ordered small fraction inside
  have parameterNonzero : curve.polynomial.eval
      (segment.pointAt parameter) ≠ 0 :=
    segment.pointAt_eval_ne_zero parameter
      (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside left request
        ordered fraction inside)
  have candidateInside : inherited.track.initial.box.Contains candidate :=
    inherited.certificate_candidate_in_initial_box parameterNonzero state
      possible
  have inheritedRefines : inherited.track.initial.box.Refines
      (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
        request).track.initial.box :=
    CCL.Riemann.PreparedSheetContinuation.transportedAt_initial_box_refines
      segment within left owner request ordered small fraction inside
  exact inheritedRefines.contains candidateInside

/-- The owner-backed coherent coefficient `x^k/y` at one queried point. -/
def coefficientAt {genus : Nat} (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (_sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    CCL.ProgressiveCoherence.CoherentNamed :=
  let point := (edge curve segment within left request).pointAt fraction
  let root := rootAt curve segment within left owner request ordered small
    fraction inside
  differentialValue differential point root.value root.apart

/-- Owner-backed coefficient using the already cached prepared source. -/
def coefficientAtCached {genus : Nat} (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CCL.Riemann.PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (_sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    CCL.ProgressiveCoherence.CoherentNamed :=
  let point := (edge curve segment within left request).pointAt fraction
  let root := rootAtCached curve segment within left owner request cached
    ordered small fraction inside
  differentialValue differential point root.value root.apart

/-- Local antisymmetric product of two standard differentials on one accepted
prepared edge.  The root owner and sheet continuation are shared before the
two differential exponents are evaluated. -/
def wedgeCoefficientAt {genus : Nat} (curve : HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    CCL.ProgressiveCoherence.CoherentNamed :=
  let point := (edge curve segment within left request).pointAt fraction
  let root := sheetValueAt curve leftDifferential segment within left owner
    request ordered small sheet fraction inside
  differentialWedgeCoefficient leftDifferential rightDifferential point
    root.value root.apart

/-- Every finite prepared chart computes zero for the wedge of two
hyperelliptic basis differentials.  This is the local holomorphic input for a
future cellwise Stokes assembly, now tied to the actual owner-backed root used
by the integration model. -/
def wedgeCoefficientAt_zero {genus : Nat}
    (curve : HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    CCL.OperationalEquivalence.NamedEquivalent
      (wedgeCoefficientAt curve leftDifferential rightDifferential segment
        within left owner request ordered small sheet fraction inside).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name := by
  unfold wedgeCoefficientAt
  exact differentialWedgeCoefficient_zero leftDifferential rightDifferential
    ((edge curve segment within left request).pointAt fraction)
    (sheetValueAt curve leftDifferential segment within left owner request
      ordered small sheet fraction inside).value
    (sheetValueAt curve leftDifferential segment within left owner request
      ordered small sheet fraction inside).apart

/-- A finite uniform upper bound for the centres of all owner-backed
differential processes on one edge. -/
structure CoefficientBound {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) where
  bound : Coordinate
  boundNonnegative : 0 <= bound
  centerBound_le : forall fraction : Coordinate,
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) ->
    (coefficientAt curve differential segment within left owner request
      ordered small sheet fraction inside).name.process.centerBound <= bound

/-- The coefficient bound computed solely from the fixed base ambient and
the line's positive polynomial clearance. -/
def automaticBoundValue {genus : Nat}
    (differential : Differential genus)
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  ambient.normSqBound ^ differential.exponent / denominatorLower segment

theorem automaticBoundValue_nonnegative {genus : Nat}
    (differential : Differential genus)
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 <= automaticBoundValue differential segment :=
  RFAP.ConstructiveFraction.div_nonneg_direct
    (RFAP.ConstructiveFraction.pow_nonneg_direct
      ambient.normSqBound_nonneg differential.exponent)
    (denominatorLower_positive segment).le

/-- Every prepared owner-backed differential cell has an automatic finite
uniform coefficient bound.  Its denominator estimate comes from the fixed
line clearance, not from a pointwise root choice or a completed minimum. -/
def automaticCoefficientBound {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) :
    CoefficientBound curve differential segment within left owner request
      ordered small sheet where
  bound := automaticBoundValue differential segment
  boundNonnegative := automaticBoundValue_nonnegative differential segment
  centerBound_le := by
    intro fraction inside
    let parameter :=
      CCL.Riemann.PreparedSheetContinuation.parameterAt left request fraction
    let originalPoint := segment.pointAt parameter
    let localPoint := (edge curve segment within left request).pointAt fraction
    let sheetValue := sheetValueAt curve differential segment within left owner
      request ordered small sheet fraction inside
    have parameterInside :=
      CCL.Riemann.PreparedSheetContinuation.parameterAt_inside left request
        ordered fraction inside
    have pointEqual : originalPoint = localPoint :=
      CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
        segment within left request fraction
    have localContains : ambient.Contains localPoint := by
      rw [← pointEqual]
      exact segment.pointAt_contains within parameter parameterInside
    have pointNormBound :
        RFAP.ConstructiveGaussian.Gaussian.normSq localPoint <=
          ambient.normSqBound :=
      ambient.normSq_le_normSqBound localContains
    have numeratorBound :
        RFAP.ConstructiveGaussian.Gaussian.normSq localPoint ^
            differential.exponent <=
          ambient.normSqBound ^ differential.exponent :=
      RFAP.ConstructiveFraction.pow_le_pow_direct
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg localPoint)
        pointNormBound differential.exponent
    have denominatorBound : denominatorLower segment <=
        sheetValue.apart.certificate.lowerSq := by
      rw [sheetValueAt_apart_lowerSq]
      exact denominatorLower_le_point segment
        (segment.pointAt_onCertifiedLine parameter parameterInside)
    have actualPositive : 0 < sheetValue.apart.certificate.lowerSq :=
      (denominatorLower_positive segment).trans_le denominatorBound
    change
      (differentialValue differential localPoint sheetValue.value
        sheetValue.apart).name.process.centerBound <=
          automaticBoundValue differential segment
    rw [differentialValue_centerBound]
    unfold automaticBoundValue
    change
      RFAP.ConstructiveGaussian.Gaussian.normSq localPoint ^
          differential.exponent /
          sheetValue.apart.certificate.lowerSq <=
        ambient.normSqBound ^ differential.exponent /
          denominatorLower segment
    calc
      RFAP.ConstructiveGaussian.Gaussian.normSq localPoint ^
            differential.exponent /
            sheetValue.apart.certificate.lowerSq <=
          ambient.normSqBound ^ differential.exponent /
            sheetValue.apart.certificate.lowerSq := by
        rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
          RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          numeratorBound
          (RFAP.ConstructiveFraction.inv_pos_direct actualPositive).le
      _ <= ambient.normSqBound ^ differential.exponent /
            denominatorLower segment :=
        RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
          (RFAP.ConstructiveFraction.pow_nonneg_direct
            ambient.normSqBound_nonneg differential.exponent)
          (denominatorLower_positive segment) denominatorBound

/-- Coarse fixed allowance used by the honest zero-polynomial model. -/
def zeroAllowance {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter))}
    {request : StepRequest}
    {ordered : left.parameter <= request.endpoint.parameter}
    {small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound}
    {sheet : Fin 2}
    (coefficientBound : CoefficientBound curve differential segment within
      left owner request ordered small sheet) : Coordinate :=
  12 + 4 * coefficientBound.bound

theorem zeroAllowance_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter))}
    {request : StepRequest}
    {ordered : left.parameter <= request.endpoint.parameter}
    {small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound}
    {sheet : Fin 2}
    (coefficientBound : CoefficientBound curve differential segment within
      left owner request ordered small sheet) :
    0 <= zeroAllowance coefficientBound :=
  add_nonneg (by decide)
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      coefficientBound.boundNonnegative)

/-- The displayed integration cell for the coarse uniform model. -/
def zeroModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter))}
    {request : StepRequest}
    {ordered : left.parameter <= request.endpoint.parameter}
    {small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound}
    {sheet : Fin 2}
    (coefficientBound : CoefficientBound curve differential segment within
      left owner request ordered small sheet) : CellModel :=
  { start := segment.pointAt left.parameter
    finish := segment.pointAt request.endpoint.parameter
    polynomial := CCL.FiniteGaussianPolynomial.zero
    localAllowance := zeroAllowance coefficientBound
    localAllowance_nonneg := zeroAllowance_nonnegative coefficientBound
    observations := [] }

def unitState (value : CCL.ProgressiveCoherence.CoherentNamed) :
    value.name.process.State :=
  value.name.process.refine value.name.state 1 (by decide)

def unitReading (value : CCL.ProgressiveCoherence.CoherentNamed) : Gaussian :=
  (value.name.process.witness (unitState value)).val

private theorem reading_norm_le
    (value : CCL.ProgressiveCoherence.CoherentNamed)
    (bound : Coordinate)
    (centerBound : value.name.process.centerBound <= bound) :
    RFAP.ConstructiveGaussian.Gaussian.normSq (unitReading value) <=
      2 * (1 + bound) := by
  let state := unitState value
  let reading := unitReading value
  let ball := value.name.process.ball state
  have possible : value.name.process.Possible state reading :=
    (value.name.process.witness state).property
  have inside : ball.Contains reading := value.name.process.possible_inside possible
  have radiusSmall : ball.radiusSq < 1 :=
    value.name.process.accurate value.name.state 1 (by decide)
  have identity : reading = (reading - ball.center) + ball.center := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  change RFAP.ConstructiveGaussian.Gaussian.normSq reading <= _
  rw [identity]
  exact (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (add_le_add (inside.trans radiusSmall.le)
        (value.name.process.center_bounded state |>.trans centerBound))
      (by decide))

/-- Automatic owner-backed uniform semantics for the coarse zero model. -/
def uniformZeroCertificate {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2)
    (coefficientBound : CoefficientBound curve differential segment within
      left owner request ordered small sheet) :
    UniformCellCertificate curve differential
      (ClearSegment.liftOnSheet sheet (edge curve segment within left request))
      (zeroModel coefficientBound) where
  query := by
    intro fraction lower upper
    let inside : (0 : Coordinate) <= fraction ∧ fraction <= 1 :=
      ⟨lower, upper⟩
    let point := (edge curve segment within left request).pointAt fraction
    let sheetValue := sheetValueAt curve differential segment within left owner
      request ordered small sheet fraction inside
    let coefficient := coefficientAt curve differential segment within left
      owner request ordered small sheet fraction inside
    let state := unitState coefficient
    let reading := unitReading coefficient
    let observation : CCL.ProgressiveGaussianIntegration.LocalObservation
        (zeroModel coefficientBound).polynomial
        (zeroModel coefficientBound).localAllowance :=
      { parameter := fraction
        integrandReading := reading
        error := reading
        decomposition := by
          change reading -
              CCL.FiniteGaussianPolynomial.eval
                CCL.FiniteGaussianPolynomial.zero ⟨fraction, 0⟩ = reading
          rw [CCL.FiniteGaussianPolynomial.eval_zero]
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.zero_re,
              RFAP.ConstructiveGaussian.Gaussian.zero_im] <;> ring1
        error_le := by
          have readingBound := reading_norm_le coefficient
            coefficientBound.bound
            (coefficientBound.centerBound_le fraction inside)
          change RFAP.ConstructiveGaussian.Gaussian.normSq reading <=
            zeroAllowance coefficientBound
          exact readingBound.trans (by
            unfold zeroAllowance
            apply sub_nonneg.mp
            have nonnegative := RFAP.ConstructiveFraction.mul_nonneg_direct
              (by decide : (0 : Coordinate) <= 2)
              coefficientBound.boundNonnegative
            have total := add_nonneg (by decide : (0 : Coordinate) <= 10)
              nonnegative
            convert total using 1
            ring1) }
    let algebraic : AlgebraicObservation curve differential
        (ClearSegment.liftOnSheet sheet (edge curve segment within left request))
        (zeroModel coefficientBound) observation :=
      { point := point
        point_eq := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [point, observationPoint, zeroModel,
              CCL.ProgressiveGaussianIntegration.CellModel.displacement,
              CCL.Riemann.BranchCuts.ClearSegment.pointAt,
              CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im,
              RFAP.ConstructiveGaussian.Gaussian.add_re,
              RFAP.ConstructiveGaussian.Gaussian.add_im,
              RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im] <;> ring1
        sheetValue := sheetValue
        chosenSheet_eq := rfl
        readingState := state
        readingPossible := by
          change coefficient.name.process.Possible state reading
          exact (coefficient.name.process.witness state).property }
    exact
      { observation := observation
        parameter_eq := rfl
        algebraic := algebraic
        semantic_error_le := by
          let ball := coefficient.name.process.ball state
          have radiusSmall : ball.radiusSq < 1 :=
            coefficient.name.process.accurate coefficient.name.state 1
              (by decide)
          have readingBound := reading_norm_le coefficient
            coefficientBound.bound
            (coefficientBound.centerBound_le fraction inside)
          change 2 * (4 * ball.radiusSq +
              RFAP.ConstructiveGaussian.Gaussian.normSq reading) <=
            zeroAllowance coefficientBound
          calc
            2 * (4 * ball.radiusSq +
                RFAP.ConstructiveGaussian.Gaussian.normSq reading) <=
                2 * (4 * 1 + 2 * (1 + coefficientBound.bound)) :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (add_le_add
                  (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                    radiusSmall.le (by decide)) readingBound) (by decide)
            _ = zeroAllowance coefficientBound := by
              unfold zeroAllowance
              ring1 }

end CCL.Riemann.PreparedDifferentialModels
