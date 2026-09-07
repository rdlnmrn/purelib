import CCL.Riemann.ClearSheetContinuation
import CCL.Riemann.SquareRootReconditioning

/-!
# Uniform finite square-root preparation along a clear segment

The generic global isolator may choose a different auxiliary radius at every
base parameter.  For the structured quadratic `Y^2 - f(x)` this is
unnecessary.  This file constructs one rational root ambient from a finite
variation bound for the whole clear segment and proves a parameter-uniform
boundary clearance on that ambient.  It is the finite replacement for a
compactness argument in the persistent refinement schedule.
-/

namespace CCL.Riemann.UniformSquareRootPreparation

open CCL.Riemann.BranchCuts

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner

/-! ## Finite path-range bounds -/

/-- A finite dyadic scan of exact affine substitutions.  At depth `n`, the
result is the maximum of the dense Horner bounds on the `2^n` displayed
subsegments.  This avoids enclosing a long segment in one unrelated square. -/
def dyadicLineNormMajorant (polynomial : GaussianPolynomial)
    (origin direction : Gaussian) : Nat -> Coordinate
  | 0 => RFAP.PolynomialBounds.denseEvalNormMajorant
      (RFAP.PathPolynomial.composeLine polynomial origin direction)
      CCL.Riemann.ClearSheetContinuation.parameterAmbient
  | depth + 1 =>
      let half := CCL.FiniteExp.scale (1 / 2) direction
      max (dyadicLineNormMajorant polynomial origin half depth)
        (dyadicLineNormMajorant polynomial (origin + half) half depth)

private theorem half_double_mul (left right : Coordinate) :
    (2 * left) * ((1 / 2 : Coordinate) * right) = left * right := by
  calc
    (2 * left) * ((1 / 2 : Coordinate) * right) =
        (2 * (1 / 2 : Coordinate)) * (left * right) := by ring1
    _ = left * right := by
      rw [show (2 : Coordinate) * (1 / 2) = 1 by decide]
      ring1

private theorem right_half_mul (left right : Coordinate) :
    (1 / 2 : Coordinate) * right +
        (2 * left - 1) * ((1 / 2 : Coordinate) * right) =
      left * right := by
  have coefficient : (1 / 2 : Coordinate) +
      (2 * left - 1) * (1 / 2) = left := by
    calc
      (1 / 2 : Coordinate) + (2 * left - 1) * (1 / 2) =
          left * (2 * (1 / 2 : Coordinate)) := by ring1
      _ = left := by
        rw [show (2 : Coordinate) * (1 / 2) = 1 by decide]
        ring1
  calc
    (1 / 2 : Coordinate) * right +
        (2 * left - 1) * ((1 / 2 : Coordinate) * right) =
      ((1 / 2 : Coordinate) + (2 * left - 1) * (1 / 2)) * right := by
        ring1
    _ = left * right := by rw [coefficient]

private theorem line_left_half (origin direction : Gaussian)
    (parameter : Coordinate) :
    RFAP.PathPolynomial.line origin
        (CCL.FiniteExp.scale (1 / 2) direction) (2 * parameter) =
      RFAP.PathPolynomial.line origin direction parameter := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.PathPolynomial.line,
      RFAP.PathPolynomial.ofCoordinate_re,
      RFAP.PathPolynomial.ofCoordinate_im,
      CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    rw [half_double_mul] <;>
    simp only [zero_mul, sub_zero, add_zero]

private theorem line_right_half (origin direction : Gaussian)
    (parameter : Coordinate) :
    RFAP.PathPolynomial.line
        (origin + CCL.FiniteExp.scale (1 / 2) direction)
        (CCL.FiniteExp.scale (1 / 2) direction) (2 * parameter - 1) =
      RFAP.PathPolynomial.line origin direction parameter := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.PathPolynomial.line,
      RFAP.PathPolynomial.ofCoordinate_re,
      RFAP.PathPolynomial.ofCoordinate_im,
      CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    simp only [zero_mul, sub_zero, add_zero] <;>
    rw [add_assoc, right_half_mul]

/-- Every rational point of the unit affine segment is covered by one leaf
of the finite dyadic range scan. -/
theorem normSq_eval_line_le_dyadicLineNormMajorant
    (polynomial : GaussianPolynomial) (origin direction : Gaussian)
    (depth : Nat) (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (polynomial.eval
          (RFAP.PathPolynomial.line origin direction parameter)) <=
      dyadicLineNormMajorant polynomial origin direction depth := by
  induction depth generalizing origin direction parameter with
  | zero =>
      have bound :=
        RFAP.PolynomialBounds.normSq_eval_le_denseEvalNormMajorant
          (RFAP.PathPolynomial.composeLine polynomial origin direction)
          (CCL.Riemann.ClearSheetContinuation.parameterAmbient_contains
            parameter inside)
      rw [RFAP.PathPolynomial.eval_composeLine] at bound
      exact bound
  | succ depth inductionHypothesis =>
      let half := CCL.FiniteExp.scale (1 / 2) direction
      by_cases left : parameter <= 1 / 2
      · have localInside : (0 : Coordinate) <= 2 * parameter ∧
            2 * parameter <= 1 := by
          constructor
          · exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
              inside.1
          · calc
              2 * parameter <= 2 * (1 / 2) :=
                RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                  left (by decide)
              _ = 1 := by decide
        have localBound := inductionHypothesis origin half
          (2 * parameter) localInside
        rw [line_left_half] at localBound
        exact localBound.trans (le_max_left _ _)
      · have halfLt : (1 / 2 : Coordinate) < parameter :=
          RFAP.ConstructiveFraction.lt_of_not_ge_direct left
        have localInside : (0 : Coordinate) <= 2 * parameter - 1 ∧
            2 * parameter - 1 <= 1 := by
          constructor
          · apply RFAP.ConstructiveFraction.sub_nonneg_direct
            calc
              1 = 2 * (1 / 2 : Coordinate) := by decide
              _ <= 2 * parameter :=
                RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                  halfLt.le (by decide)
          · calc
              2 * parameter - 1 <= 2 * 1 - 1 :=
                RFAP.ConstructiveFraction.sub_le_sub_right_direct
                  (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                    inside.2 (by decide)) 1
              _ = 1 := by ring1
        have localBound := inductionHypothesis (origin + half) half
          (2 * parameter - 1) localInside
        rw [line_right_half] at localBound
        exact localBound.trans (le_max_right _ _)

theorem dyadicLineNormMajorant_nonneg (polynomial : GaussianPolynomial)
    (origin direction : Gaussian) (depth : Nat) :
    0 <= dyadicLineNormMajorant polynomial origin direction depth := by
  induction depth generalizing origin direction with
  | zero =>
      exact (RFAP.PolynomialBounds.denseEvalNormMajorant_pos _ _).le
  | succ depth inductionHypothesis =>
      exact (inductionHypothesis origin
        (CCL.FiniteExp.scale (1 / 2) direction)).trans (le_max_left _ _)

/-- Four dyadic splits give sixteen exact range boxes.  The depth is a fixed
finite construction cost, not an elaborator or recursion-limit setting. -/
def radicandScanDepth : Nat := 4

private def rootPolynomialAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) : GaussianPolynomial :=
  CCL.Riemann.SquareRootReconditioning.rootPolynomial
    (polynomial.eval (segment.pointAt parameter))

/-- Squared-norm radius of a symmetric box containing the complete affine
segment.  It is computed solely from the two displayed endpoints. -/
def segmentPointRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (_segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  2 *
      (RFAP.ConstructiveGaussian.Gaussian.normSq (finish - start) +
        RFAP.ConstructiveGaussian.Gaussian.normSq start) +
    1

theorem one_le_segmentPointRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    (1 : Coordinate) <= segmentPointRadius segment := by
  unfold segmentPointRadius
  have doubledNonnegative :
      0 <= 2 *
        (RFAP.ConstructiveGaussian.Gaussian.normSq (finish - start) +
          RFAP.ConstructiveGaussian.Gaussian.normSq start) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _))
  exact le_add_of_nonneg_left doubledNonnegative

theorem segmentPointRadius_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < segmentPointRadius segment :=
  (show (0 : Coordinate) < 1 by decide).trans_le
    (one_le_segmentPointRadius segment)

/-- Explicit symmetric box containing every unit-interval point of the
segment, independent of the clear-line ambient. -/
def segmentPointAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Box :=
  RFAP.Boxes.Box.symmetric (segmentPointRadius segment)
    (segmentPointRadius_positive segment).le

theorem segmentPointAmbient_contains
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    (segmentPointAmbient segment).Contains (segment.pointAt parameter) := by
  let point := segment.pointAt parameter
  let radius := segmentPointRadius segment
  have differenceBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq (point - start) <=
        RFAP.ConstructiveGaussian.Gaussian.normSq (finish - start) := by
    simpa only [point, ClearSegment.pointAt_zero, ClearSegment.pointAt_one]
      using segment.normSq_pointAt_sub_zero_le_full parameter inside
  have decomposition : point = (point - start) + start := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  have pointLeBase : RFAP.ConstructiveGaussian.Gaussian.normSq point <=
      2 *
        (RFAP.ConstructiveGaussian.Gaussian.normSq (finish - start) +
          RFAP.ConstructiveGaussian.Gaussian.normSq start) := by
    rw [decomposition]
    exact (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add differenceBound le_rfl) (by decide))
  have pointLeRadius :
      RFAP.ConstructiveGaussian.Gaussian.normSq point <= radius := by
    exact pointLeBase.trans (by
      dsimp only [radius, segmentPointRadius]
      exact le_add_of_nonneg_right (by decide))
  have radiusLeSquare : radius <= radius ^ 2 := by
    rw [pow_two]
    calc
      radius = radius * 1 := by ring1
      _ <= radius * radius :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (one_le_segmentPointRadius segment)
          (segmentPointRadius_positive segment).le
  exact RFAP.AffineWinding.coordinate_bounds_of_normSq_le
    (segmentPointRadius_positive segment).le
    (pointLeRadius.trans radiusLeSquare)

/-- A finite coefficient-computed squared-norm majorant for every radicand on
the displayed segment.  Sixteen exact affine subsegments retain cancellation
that is lost in one large enclosing square; the final `+ 1` makes the result
strictly positive and at least one. -/
@[irreducible] def radicandNormBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (_segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  dyadicLineNormMajorant polynomial start (finish - start)
    radicandScanDepth + 1

theorem one_le_radicandNormBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (_segment : ClearSegment polynomial ambient start finish) :
    (1 : Coordinate) <= radicandNormBound _segment := by
  unfold radicandNormBound
  exact le_add_of_nonneg_left
    (dyadicLineNormMajorant_nonneg polynomial start (finish - start)
      radicandScanDepth)

theorem radicandNormBound_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < radicandNormBound segment :=
  (show (0 : Coordinate) < 1 by decide).trans_le
    (one_le_radicandNormBound segment)

/-- Every rational unit-interval parameter has radicand norm below the one
segment-wide majorant. -/
theorem eval_normSq_le_radicandNormBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (polynomial.eval (segment.pointAt parameter)) <=
      radicandNormBound segment := by
  have evaluated := normSq_eval_line_le_dyadicLineNormMajorant polynomial
    start (finish - start) radicandScanDepth parameter inside
  have lineEqual : RFAP.PathPolynomial.line start (finish - start) parameter =
      segment.pointAt parameter := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.PathPolynomial.line, ClearSegment.pointAt,
        RFAP.PathPolynomial.ofCoordinate_re,
        RFAP.PathPolynomial.ofCoordinate_im,
        CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
      ring1
  rw [lineEqual] at evaluated
  exact evaluated.trans (by
    unfold radicandNormBound
    exact le_add_of_nonneg_right (by decide))

/-- A coefficient-computed coordinate radius containing every sufficiently
accurate quadratic-root sample. -/
def rootSampleCoordinateRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  2 * radicandNormBound segment

/-- A direct norm-square bound for every sufficiently accurate quadratic-root
sample.  Unlike the coordinate radius, this grows only linearly with the
radicand majorant. -/
def rootSampleNormSqMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  2 * ((1 / 4 : Coordinate) + radicandNormBound segment)

theorem rootSampleNormSqMajorant_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < rootSampleNormSqMajorant segment :=
  RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (add_pos_of_pos_of_nonneg (by decide)
      (radicandNormBound_positive segment).le)

/-- Radius of one common symmetric root ambient for the complete segment.
The extra unit gives a direct geometric margin around every sample, avoiding
the much smaller residual-Lipschitz interior strip. -/
def rootAmbientRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  rootSampleCoordinateRadius segment + 1

/-- Every common quadratic root ambient contains the symmetric square of
radius three, without evaluating its finite radicand scan. -/
theorem three_le_rootAmbientRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    (3 : Coordinate) <= rootAmbientRadius segment := by
  unfold rootAmbientRadius rootSampleCoordinateRadius
  calc
    (3 : Coordinate) = 2 * 1 + 1 := by decide
    _ <= 2 * radicandNormBound segment + 1 := by
      exact add_le_add
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (one_le_radicandNormBound segment)
          (show (0 : Coordinate) <= 2 by decide)) le_rfl

theorem rootAmbientRadius_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < rootAmbientRadius segment :=
  add_pos_of_pos_of_nonneg
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (radicandNormBound_positive segment)) (by decide)

def rootAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Box :=
  RFAP.Boxes.Box.symmetric (rootAmbientRadius segment)
    (rootAmbientRadius_positive segment).le

private theorem two_one_add_le_sampleRadius_four
    {bound : Coordinate} (oneLe : (1 : Coordinate) <= bound) :
    2 * (1 + bound) <= (2 * bound) ^ 4 := by
  have boundNonnegative : (0 : Coordinate) <= bound :=
    (by decide : (0 : Coordinate) <= 1).trans oneLe
  have boundLeSquare : bound <= bound ^ 2 := by
    rw [pow_two]
    calc
      bound = bound * 1 := by ring1
      _ <= bound * bound :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct oneLe
          boundNonnegative
  have oneLeSquare : (1 : Coordinate) <= bound ^ 2 :=
    oneLe.trans boundLeSquare
  have squareLeFourth : bound ^ 2 <= bound ^ 4 := by
    rw [show bound ^ 4 = bound ^ 2 * bound ^ 2 by ring1]
    calc
      bound ^ 2 = bound ^ 2 * 1 := by ring1
      _ <= bound ^ 2 * bound ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct oneLeSquare
          (RFAP.ConstructiveFraction.sq_nonneg_direct bound)
  have boundLeFourth := boundLeSquare.trans squareLeFourth
  have oneLeFourth := oneLeSquare.trans squareLeFourth
  calc
    2 * (1 + bound) <= 2 * (bound ^ 4 + bound ^ 4) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add oneLeFourth boundLeFourth) (by decide)
    _ <= 16 * bound ^ 4 := by
      have fourthNonnegative : (0 : Coordinate) <= bound ^ 4 :=
        RFAP.ConstructiveFraction.pow_nonneg_direct boundNonnegative 4
      calc
        2 * (bound ^ 4 + bound ^ 4) = 4 * bound ^ 4 := by ring1
        _ <= 16 * bound ^ 4 :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (by decide) fourthNonnegative
    _ = (2 * bound) ^ 4 := by ring1

/-- The common root ambient has the same positive boundary-clearance bound
`1` for every parameter of the clear segment. -/
def rootAmbientClearance
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    RFAP.BoxClearance.BoundaryClearance
      (rootPolynomialAt segment parameter) (rootAmbient segment) where
  bound := 1
  positive := by decide
  lower := by
    intro z boundary
    let bound := radicandNormBound segment
    let radius := rootAmbientRadius segment
    let radicand := polynomial.eval (segment.pointAt parameter)
    have radicandBound :
        RFAP.ConstructiveGaussian.Gaussian.normSq radicand <= bound :=
      eval_normSq_le_radicandNormBound segment parameter inside
    have radial := RFAP.GlobalWinding.symmetric_boundary_norm_bounds
      (rootAmbientRadius_positive segment).le boundary
    have powerLower : radius ^ 4 <=
        RFAP.ConstructiveGaussian.Gaussian.normSq (z ^ 2) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.normSq_pow]
      calc
        radius ^ 4 = (radius ^ 2) ^ 2 := by ring1
        _ <= RFAP.ConstructiveGaussian.Gaussian.normSq z ^ 2 :=
          RFAP.ConstructiveFraction.pow_le_pow_direct
            (RFAP.ConstructiveFraction.sq_nonneg_direct radius) radial.1 2
    have split : z ^ 2 = (z ^ 2 - radicand) + radicand := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
    have upper :=
      RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two
        (z ^ 2 - radicand) radicand
    rw [← split] at upper
    have sampleRadiusLe : rootSampleCoordinateRadius segment <= radius := by
      dsimp only [radius, rootAmbientRadius]
      exact le_add_of_nonneg_right (by decide)
    have scalarLower : 2 * (1 + bound) <= radius ^ 4 := by
      have baseScalar : 2 * (1 + bound) <=
          rootSampleCoordinateRadius segment ^ 4 := by
        simpa only [rootSampleCoordinateRadius, bound] using
          two_one_add_le_sampleRadius_four
            (one_le_radicandNormBound segment)
      exact baseScalar.trans
        (RFAP.ConstructiveFraction.pow_le_pow_direct
          (by
            unfold rootSampleCoordinateRadius
            exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
              (radicandNormBound_positive segment).le)
          sampleRadiusLe 4)
    have combined :
        2 * (1 + bound) <=
          2 *
            (RFAP.ConstructiveGaussian.Gaussian.normSq
                (z ^ 2 - radicand) +
              RFAP.ConstructiveGaussian.Gaussian.normSq radicand) :=
      scalarLower.trans (powerLower.trans upper)
    have boundedRight :
        2 *
            (RFAP.ConstructiveGaussian.Gaussian.normSq
                (z ^ 2 - radicand) +
              RFAP.ConstructiveGaussian.Gaussian.normSq radicand) <=
          2 *
            (RFAP.ConstructiveGaussian.Gaussian.normSq
                (z ^ 2 - radicand) + bound) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add le_rfl radicandBound) (by decide)
    have reduced := combined.trans boundedRight
    have withoutTwo :
        1 + bound <=
          RFAP.ConstructiveGaussian.Gaussian.normSq
              (z ^ 2 - radicand) + bound := by
      apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
        (c := 2) ?_ (show (0 : Coordinate) < 2 by decide)
      simpa only [RFAP.ConstructiveFraction.mul_comm] using reduced
    have result : (1 : Coordinate) <=
        RFAP.ConstructiveGaussian.Gaussian.normSq (z ^ 2 - radicand) := by
      exact RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
        (c := bound) withoutTwo
    simpa only [rootPolynomialAt,
      CCL.Riemann.SquareRootReconditioning.rootPolynomial,
      CCL.PowerMonodromy.polynomial_eval,
      CCL.Riemann.SquareRootSheets.degreeTwo_value, radicand] using result

@[simp] theorem rootAmbientClearance_bound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    (rootAmbientClearance segment parameter inside).bound = 1 := rfl

/-- The dense first-variation scan of `Y^2-a` is independent of its constant
coefficient once the common root ambient is fixed. -/
theorem rootLipschitz_formula
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) :
    RFAP.PolynomialBounds.denseLipschitzBound
        (rootPolynomialAt segment parameter) (rootAmbient segment) =
      max 1 (16 * (rootAmbient segment).normSqBound) := by
  unfold RFAP.PolynomialBounds.denseLipschitzBound
    RFAP.PolynomialBounds.denseEvalNormLipschitzBound
    RFAP.PolynomialBounds.denseHornerNormBounds
    rootPolynomialAt CCL.Riemann.SquareRootReconditioning.rootPolynomial
    CCL.PowerMonodromy.polynomial CCL.RootPowers.rootPolynomial
  simp only [CCL.Riemann.SquareRootSheets.degreeTwo_value, Nat.reduceSub,
    List.replicate_succ, List.replicate_zero, List.nil_append,
    List.cons_append, RFAP.PolynomialBounds.HornerNormBounds.step,
    List.foldl_cons, List.foldl_nil,
    RFAP.ConstructiveGaussian.Gaussian.normSq_zero,
    RFAP.ConstructiveGaussian.Gaussian.normSq_one]
  congr 1
  ring1

/-- The quadratic Taylor-remainder scan is the exact constant `8`. -/
theorem rootTaylor_formula
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) :
    RFAP.PolynomialBounds.denseTaylorRemainderBound
        (rootPolynomialAt segment parameter) (rootAmbient segment) = 8 := by
  unfold RFAP.PolynomialBounds.denseTaylorRemainderBound
    RFAP.PolynomialBounds.denseEvalTaylorRemainderBound
    RFAP.PolynomialBounds.denseHornerTaylorNormBounds
    rootPolynomialAt CCL.Riemann.SquareRootReconditioning.rootPolynomial
    CCL.PowerMonodromy.polynomial CCL.RootPowers.rootPolynomial
  simp only [CCL.Riemann.SquareRootSheets.degreeTwo_value, Nat.reduceSub,
    List.replicate_succ, List.replicate_zero, List.nil_append,
    List.cons_append, RFAP.PolynomialBounds.HornerTaylorNormBounds.step,
    List.foldl_cons, List.foldl_nil,
    RFAP.ConstructiveGaussian.Gaussian.normSq_zero,
    RFAP.ConstructiveGaussian.Gaussian.normSq_one]
  calc
    max 1 _ = max 1 (8 : Coordinate) := by congr 1; ring1
    _ = 8 := by decide

/-- One coefficient-scanned bound for the derivative of every quadratic in
the segment family.  The derivative of `Y^2-a` is independent of `a`. -/
def rootDerivativeMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  RFAP.PolynomialBounds.denseEvalNormMajorant
    (RFAP.ConstructiveGCD.derivative (rootPolynomialAt segment 0))
    (rootAmbient segment)

theorem rootDerivativeMajorant_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < rootDerivativeMajorant segment :=
  RFAP.PolynomialBounds.denseEvalNormMajorant_pos _ _

theorem rootDerivativeMajorant_formula
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) :
    RFAP.PolynomialBounds.denseEvalNormMajorant
        (RFAP.ConstructiveGCD.derivative
          (rootPolynomialAt segment parameter))
        (rootAmbient segment) =
      rootDerivativeMajorant segment := by
  unfold rootDerivativeMajorant rootPolynomialAt
    CCL.Riemann.SquareRootReconditioning.rootPolynomial
  rw [CCL.PowerMonodromy.derivative_polynomial_eq
    (polynomial.eval (segment.pointAt parameter))
    (polynomial.eval (segment.pointAt 0))
    CCL.Riemann.SquareRootSheets.degreeTwo]

/-- The automatic derivative of the quadratic root polynomial has exact
norm square `4 * normSq point`. -/
theorem rootDerivative_normSq_formula
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) (point : Gaussian) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((RFAP.ConstructiveGCD.derivative
          (rootPolynomialAt segment parameter)).eval point) =
      4 * RFAP.ConstructiveGaussian.Gaussian.normSq point := by
  unfold rootPolynomialAt
    CCL.Riemann.SquareRootReconditioning.rootPolynomial
    CCL.PowerMonodromy.polynomial CCL.RootPowers.rootPolynomial
    RFAP.ConstructiveGCD.derivative RFAP.ComputableDerivative.derivative
    RFAP.ComputableDerivative.derivativeState
  simp only [CCL.Riemann.SquareRootSheets.degreeTwo_value, Nat.reduceSub,
    List.replicate_succ, List.replicate_zero, List.nil_append,
    List.cons_append, List.foldl_cons, List.foldl_nil,
    RFAP.ComputableDerivative.derivativeStep,
    RFAP.ComputablePolynomial.DensePolynomial.normalize_constant_of_ne
      (by decide : (1 : Gaussian) ≠ 0),
    RFAP.ComputablePolynomial.DensePolynomial.shift_zero,
    RFAP.ComputablePolynomial.DensePolynomial.zero_add_normalize,
    RFAP.ComputablePolynomial.DensePolynomial.normalize_zero,
    RFAP.ComputablePolynomial.DensePolynomial.eval_add,
    RFAP.ComputablePolynomial.DensePolynomial.eval_shift,
    RFAP.ComputablePolynomial.DensePolynomial.eval_constant, pow_one]
  simp only [one_mul, add_zero]
  unfold RFAP.ConstructiveGaussian.Gaussian.normSq
  simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.add_im]
  ring1

/-- The exact common dense first-variation majorant for every quadratic root
polynomial on the segment root ambient. -/
def rootLipschitz
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  max 1 (16 * (rootAmbient segment).normSqBound)

theorem rootLipschitz_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < rootLipschitz segment :=
  (show (0 : Coordinate) < 1 by decide).trans_le (le_max_left _ _)

/-- Uniform interior strip derived from the common boundary clearance and
the common quadratic Lipschitz scan. -/
def rootInteriorRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  min 1 (1 / (4 * rootLipschitz segment))

theorem rootInteriorRadius_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < rootInteriorRadius segment :=
  lt_min (by decide)
    (RFAP.ConstructiveFraction.div_pos_direct (by decide)
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (rootLipschitz_positive segment)))

theorem rootAmbient_residualInteriorRadius_eq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    (rootAmbientClearance segment parameter inside).residualInteriorRadius =
      rootInteriorRadius segment := by
  unfold RFAP.BoxClearance.BoundaryClearance.residualInteriorRadius
    rootInteriorRadius rootLipschitz
  rw [rootAmbientClearance_bound,
    rootLipschitz_formula segment parameter]

/-- One radius valid at every segment parameter.  Its three caps provide the
explicit root-ambient margin, quadratic Taylor dominance, and requested
output diameter.  Derivative admission is checked against the actual sampled
residual, so it no longer shrinks this geometric radius by an unrelated
ambient Lipschitz majorant. -/
def preparationRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) : Coordinate :=
  min (1 / 8 : Coordinate)
    (min
      (CCL.FiniteGeometric.dyadicSquareRadius
        (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
            segment / (72 * 8)))
      (CCL.FiniteGeometric.dyadicSquareRadius (rootDiameter / 8)))

theorem preparationRadius_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {rootDiameter : Coordinate} (_rootDiameterPositive : 0 < rootDiameter) :
    0 < preparationRadius segment rootDiameter := by
  unfold preparationRadius
  exact lt_min
    (by decide)
    (lt_min
      (CCL.FiniteGeometric.dyadicSquareRadius_positive _)
      (CCL.FiniteGeometric.dyadicSquareRadius_positive _))

/-- The exact derivative norm-square majorant obtained from the uniform
sample bound for the quadratic family. -/
def rootSampleDerivativeMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  4 * rootSampleNormSqMajorant segment

/-- The explicit positive offset in the radicand scan gives a uniform
numerical floor for the quadratic sample bound. -/
theorem ten_le_rootSampleDerivativeMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    (10 : Coordinate) <= rootSampleDerivativeMajorant segment := by
  unfold rootSampleDerivativeMajorant rootSampleNormSqMajorant
  calc
    (10 : Coordinate) = 4 * (2 * ((1 / 4 : Coordinate) + 1)) := by
      decide
    _ <= 4 * (2 * ((1 / 4 : Coordinate) + radicandNormBound segment)) := by
      apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      · apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        · exact add_le_add_right (one_le_radicandNormBound segment) (1 / 4)
        · decide
      · decide

theorem rootSampleDerivativeMajorant_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < rootSampleDerivativeMajorant segment :=
  RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (rootSampleNormSqMajorant_positive segment)

/-- Parameter-independent upper bound for the Newton affine term on the
uniform restart square, using the actual quadratic sample rather than a scan
over the much larger common ambient. -/
def linearizationMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) : Coordinate :=
  2 * rootSampleDerivativeMajorant segment *
    preparationRadius segment rootDiameter ^ 2

/-- A scan-free numerical lower bound for the Newton linearization
majorant.  It is sufficient for upper-bounding the predicted clearance in
explicit finite examples. -/
theorem twenty_mul_preparationRadius_sq_le_linearizationMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) :
    20 * preparationRadius segment rootDiameter ^ 2 <=
      linearizationMajorant segment rootDiameter := by
  unfold linearizationMajorant
  have doubled : (2 : Coordinate) * 10 <=
      2 * rootSampleDerivativeMajorant segment :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (ten_le_rootSampleDerivativeMajorant segment) (by decide)
  have twentyLe : (20 : Coordinate) <=
      2 * rootSampleDerivativeMajorant segment := by
    calc
      (20 : Coordinate) = 2 * 10 := by decide
      _ <= 2 * rootSampleDerivativeMajorant segment := doubled
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct twentyLe
    (RFAP.ConstructiveFraction.sq_nonneg_direct
      (preparationRadius segment rootDiameter))

theorem linearizationMajorant_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < linearizationMajorant segment rootDiameter :=
  RFAP.ConstructiveFraction.mul_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (rootSampleDerivativeMajorant_positive segment))
    (RFAP.ConstructiveFraction.pow_pos_direct
      (preparationRadius_positive segment rootDiameterPositive) 2)

theorem preparationRadius_le_oneEighth
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) :
    preparationRadius segment rootDiameter <= 1 / 8 :=
  min_le_left _ _

theorem preparationRadius_sq_lt_taylorRatio
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    preparationRadius segment rootDiameter ^ 2 <
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment /
        (72 * 8) := by
  let target :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment /
      (72 * 8)
  let selected := CCL.FiniteGeometric.dyadicSquareRadius target
  have radiusPositive :=
    preparationRadius_positive segment rootDiameterPositive
  have radiusLe : preparationRadius segment rootDiameter <= selected :=
    (min_le_right _ _).trans (min_le_left _ _)
  have squareLe : preparationRadius segment rootDiameter ^ 2 <=
      selected ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le radiusLe 2
  have denominatorPositive : (0 : Coordinate) < 72 * 8 :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct (n := 72) (by decide))
      (RFAP.ConstructiveFraction.natCast_pos_direct (n := 8) (by decide))
  have targetPositive : 0 < target :=
    RFAP.ConstructiveFraction.div_pos_direct
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
        segment) denominatorPositive
  exact squareLe.trans_lt
    (CCL.FiniteGeometric.dyadicSquareRadius_sq_lt targetPositive)

/-- Segment-wide squared root-diameter bound forced by the derivative
separation cap in uniform preparation.  It is independent of the caller's
coarser operational diameter request. -/
def derivativeDiameterBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  8 *
    (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment /
      (72 * 8))

theorem derivativeDiameterBound_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < derivativeDiameterBound segment :=
  RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (RFAP.ConstructiveFraction.div_pos_direct
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
        segment)
      (RFAP.ConstructiveFraction.mul_pos_direct
        (RFAP.ConstructiveFraction.natCast_pos_direct (n := 72) (by decide))
        (RFAP.ConstructiveFraction.natCast_pos_direct (n := 8) (by decide))))

theorem preparationRadius_le_diameterCap
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) :
    preparationRadius segment rootDiameter <=
      CCL.FiniteGeometric.dyadicSquareRadius (rootDiameter / 8) :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem preparationRadius_le_one
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) :
    preparationRadius segment rootDiameter <= 1 := by
  exact (preparationRadius_le_oneEighth segment rootDiameter).trans (by decide)

theorem preparation_taylorSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    2 *
        (36 *
          RFAP.PolynomialBounds.denseTaylorRemainderBound
            (rootPolynomialAt segment parameter) (rootAmbient segment) *
          preparationRadius segment rootDiameter ^ 2) <=
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
        segment := by
  let radius := preparationRadius segment rootDiameter
  let margin :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment
  have denominatorPositive : (0 : Coordinate) < 72 * 8 :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct (n := 72) (by decide))
      (RFAP.ConstructiveFraction.natCast_pos_direct (n := 8) (by decide))
  have scaled : radius ^ 2 * (72 * 8) <= margin :=
    (RFAP.ConstructiveFraction.le_div_iff_pos denominatorPositive).mp
      (preparationRadius_sq_lt_taylorRatio segment rootDiameterPositive).le
  rw [rootTaylor_formula segment parameter]
  calc
    2 * (36 * 8 * radius ^ 2) = (72 * 8) * radius ^ 2 := by ring1
    _ = radius ^ 2 * (72 * 8) := by ring1
    _ <= margin := scaled

theorem two_preparationRadius_lt_one
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {rootDiameter : Coordinate} (_rootDiameterPositive : 0 < rootDiameter) :
    2 * preparationRadius segment rootDiameter < 1 := by
  let radius := preparationRadius segment rootDiameter
  have radiusLe : radius <= 1 / 8 :=
    preparationRadius_le_oneEighth segment rootDiameter
  calc
    2 * radius <= 2 * (1 / 8 : Coordinate) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct radiusLe
        (by decide)
    _ < 1 := by decide

/-! ## A common inherited-occurrence bridge -/

/-- Radius of a same-sample bridge which fits both the inherited owner and
the uniform prepared square. -/
def bridgeRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Coordinate :=
  let p := rootPolynomialAt segment parameter
  let ownerBox := owner.track.initial.box
  min ((3 / 8 : Coordinate) *
      owner.track.initial.clearance.residualInteriorRadius)
    (min ((1 / 4 : Coordinate) * preparationRadius segment rootDiameter)
      (min
        (CCL.FiniteGeometric.dyadicSquareRadius
          (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeThreshold
              segment /
            (2 * RFAP.PolynomialBounds.denseLipschitzBound p ownerBox)))
        (CCL.FiniteGeometric.dyadicSquareRadius
          (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
              segment /
            (72 * RFAP.PolynomialBounds.denseTaylorRemainderBound
              p ownerBox)))))

theorem bridgeRadius_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < bridgeRadius segment owner rootDiameter :=
  lt_min
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      owner.track.initial.clearance.residualInteriorRadius_pos)
    (lt_min
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (preparationRadius_positive segment rootDiameterPositive))
      (lt_min
        (CCL.FiniteGeometric.dyadicSquareRadius_positive _)
        (CCL.FiniteGeometric.dyadicSquareRadius_positive _)))

theorem bridgeRadius_le_preparation
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    bridgeRadius segment owner rootDiameter <=
      preparationRadius segment rootDiameter := by
  have preparationNonnegative :=
    (preparationRadius_positive segment rootDiameterPositive).le
  exact ((min_le_right _ _).trans (min_le_left _ _)).trans
    (by
      calc
        (1 / 4 : Coordinate) * preparationRadius segment rootDiameter <=
            1 * preparationRadius segment rootDiameter :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (by decide) preparationNonnegative
        _ = preparationRadius segment rootDiameter := by ring1)

theorem bridgeRadius_le_ownerInteriorScale
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    bridgeRadius segment owner rootDiameter <=
      (3 / 8 : Coordinate) *
        owner.track.initial.clearance.residualInteriorRadius :=
  min_le_left _ _

theorem bridge_sourceThreshold
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.PolynomialBounds.denseLipschitzBound
        (rootPolynomialAt segment parameter) owner.track.initial.box *
        (2 * bridgeRadius segment owner rootDiameter ^ 2) <=
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeThreshold
        segment := by
  let p := rootPolynomialAt segment parameter
  let ownerBox := owner.track.initial.box
  let radius := bridgeRadius segment owner rootDiameter
  let lipschitz := RFAP.PolynomialBounds.denseLipschitzBound p ownerBox
  let threshold :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeThreshold segment
  have radiusPositive : 0 < radius :=
    bridgeRadius_positive segment owner rootDiameterPositive
  let selected := CCL.FiniteGeometric.dyadicSquareRadius
    (threshold / (2 * lipschitz))
  have radiusLeSelected : radius <= selected :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have denominatorPositive : 0 < 2 * lipschitz :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (RFAP.PolynomialBounds.denseLipschitzBound_pos p ownerBox)
  have targetPositive : 0 < threshold / (2 * lipschitz) :=
    RFAP.ConstructiveFraction.div_pos_direct
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeThreshold_positive
        segment) denominatorPositive
  have squareLeTarget : radius ^ 2 <= threshold / (2 * lipschitz) :=
    (RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le
      radiusLeSelected 2).trans
        (CCL.FiniteGeometric.dyadicSquareRadius_sq_lt targetPositive).le
  have scaled : radius ^ 2 * (2 * lipschitz) <= threshold :=
    (RFAP.ConstructiveFraction.le_div_iff_pos denominatorPositive).mp
      squareLeTarget
  change lipschitz * (2 * radius ^ 2) <= threshold
  calc
    lipschitz * (2 * radius ^ 2) = (2 * lipschitz) * radius ^ 2 := by ring1
    _ = radius ^ 2 * (2 * lipschitz) := by ring1
    _ <= threshold := scaled

theorem bridge_taylorSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    2 *
        (36 *
          RFAP.PolynomialBounds.denseTaylorRemainderBound
            (rootPolynomialAt segment parameter) owner.track.initial.box *
          bridgeRadius segment owner rootDiameter ^ 2) <=
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
        segment := by
  let p := rootPolynomialAt segment parameter
  let ownerBox := owner.track.initial.box
  let radius := bridgeRadius segment owner rootDiameter
  let taylor := RFAP.PolynomialBounds.denseTaylorRemainderBound p ownerBox
  let margin :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment
  have radiusPositive : 0 < radius :=
    bridgeRadius_positive segment owner rootDiameterPositive
  let selected := CCL.FiniteGeometric.dyadicSquareRadius
    (margin / (72 * taylor))
  have radiusLeSelected : radius <= selected :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  have denominatorPositive : 0 < 72 * taylor :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct (n := 72) (by decide))
      (RFAP.PolynomialBounds.denseTaylorRemainderBound_pos p ownerBox)
  have targetPositive : 0 < margin / (72 * taylor) :=
    RFAP.ConstructiveFraction.div_pos_direct
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
        segment) denominatorPositive
  have squareLeTarget : radius ^ 2 <= margin / (72 * taylor) :=
    (RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le
      radiusLeSelected 2).trans
        (CCL.FiniteGeometric.dyadicSquareRadius_sq_lt targetPositive).le
  have scaled : radius ^ 2 * (72 * taylor) <= margin :=
    (RFAP.ConstructiveFraction.le_div_iff_pos denominatorPositive).mp
      squareLeTarget
  change 2 * (36 * taylor * radius ^ 2) <= margin
  calc
    2 * (36 * taylor * radius ^ 2) = (72 * taylor) * radius ^ 2 := by ring1
    _ = radius ^ 2 * (72 * taylor) := by ring1
    _ <= margin := scaled

/-- One positive residual request simultaneously prepares the uniform square,
the smaller same-sample bridge, and strict containment in the inherited
owner. -/
def sampleResidualTarget
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Coordinate :=
  let radius := preparationRadius segment rootDiameter
  let bridge := bridgeRadius segment owner rootDiameter
  let p := rootPolynomialAt segment parameter
  let ownerLipschitz := RFAP.PolynomialBounds.denseLipschitzBound p
    owner.track.initial.box
  let margin :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment
  min
    (min (1 / 4 : Coordinate)
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeThreshold
        segment))
    (min (rootLipschitz segment * (2 * radius ^ 2))
      (min (margin * radius ^ 2)
        (min (ownerLipschitz * (2 * bridge ^ 2))
          (min (margin * bridge ^ 2)
            (owner.track.initial.clearance.bound / 4)))))

theorem sampleResidualTarget_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < sampleResidualTarget segment owner rootDiameter := by
  let radius := preparationRadius segment rootDiameter
  let bridge := bridgeRadius segment owner rootDiameter
  let p := rootPolynomialAt segment parameter
  let ownerLipschitz := RFAP.PolynomialBounds.denseLipschitzBound p
    owner.track.initial.box
  let margin :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment rootDiameterPositive
  have bridgePositive : 0 < bridge :=
    bridgeRadius_positive segment owner rootDiameterPositive
  have marginPositive : 0 < margin :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
      segment
  unfold sampleResidualTarget
  exact lt_min
    (lt_min (by decide)
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeThreshold_positive
        segment))
    (lt_min
      (RFAP.ConstructiveFraction.mul_pos_direct
        (rootLipschitz_positive segment)
        (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
          (RFAP.ConstructiveFraction.pow_pos_direct radiusPositive 2)))
      (lt_min
        (RFAP.ConstructiveFraction.mul_pos_direct marginPositive
          (RFAP.ConstructiveFraction.pow_pos_direct radiusPositive 2))
        (lt_min
          (RFAP.ConstructiveFraction.mul_pos_direct
            (RFAP.PolynomialBounds.denseLipschitzBound_pos _ _)
            (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
              (RFAP.ConstructiveFraction.pow_pos_direct bridgePositive 2)))
          (lt_min
            (RFAP.ConstructiveFraction.mul_pos_direct marginPositive
              (RFAP.ConstructiveFraction.pow_pos_direct bridgePositive 2))
            (RFAP.ConstructiveFraction.div_pos_direct
              owner.track.initial.clearance.positive (by decide))))))

/-- First inherited-owner sample satisfying every uniform and bridge
residual test. -/
def sampleIndex
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Nat :=
  CCL.FiniteGeometric.firstQuarterBelow
    (CCL.Riemann.CoherentRoot.residualScale
      (rootPolynomialAt segment parameter) owner.ambient owner.track)
    0 (sampleResidualTarget segment owner rootDiameter)

/-- The guaranteed shrinking-track fallback used if the cheap quadratic
Newton candidates do not yet satisfy the finite preparation tests. -/
def trackSample
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Gaussian :=
  (CCL.Riemann.CoherentRoot.approximation owner.track).sample
    (sampleIndex segment owner rootDiameter)

theorem trackSample_residual_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (trackSample segment owner rootDiameter)) <
      sampleResidualTarget segment owner rootDiameter :=
  (CCL.Riemann.CoherentRoot.sample_residual_le owner.track (by
    rw [CCL.PowerMonodromy.polynomial_degree]
    exact CCL.Riemann.SquareRootSheets.degreeTwo.positive)
      (sampleIndex segment owner rootDiameter)).trans_lt
    (CCL.FiniteGeometric.firstQuarterBelow_accurate
      (CCL.Riemann.CoherentRoot.residualScale
        (rootPolynomialAt segment parameter) owner.ambient owner.track)
      (CCL.Riemann.CoherentRoot.residualScale_nonneg
        (rootPolynomialAt segment parameter) owner.ambient owner.track)
      0 (sampleResidualTarget segment owner rootDiameter)
      (sampleResidualTarget_positive segment owner rootDiameterPositive))

/-- The shrinking-track fallback remains in the inherited owner's initial
box.  This proof is used only for totality; successful finite Newton
candidates bypass evaluation of the fallback itself. -/
theorem trackSample_inside_owner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    owner.track.initial.box.Contains
      (trackSample segment owner rootDiameter) := by
  change owner.track.initial.box.Contains
    (CCL.Riemann.CoherentRoot.state owner.track
      (sampleIndex segment owner rootDiameter)).box.anchor
  exact (CCL.Riemann.CoherentRoot.state_refines_of_le owner.track
    (Nat.zero_le _)).contains
      (CCL.Riemann.CoherentRoot.state owner.track
        (sampleIndex segment owner rootDiameter)).box.contains_anchor

/-- Rational midpoint of a displayed owner box. -/
def ownerMidpoint (box : Box) : Gaussian :=
  { re := (box.xLower + box.xUpper) / 2
    im := (box.yLower + box.yUpper) / 2 }

/-- One total rational Newton step for `z² = parameter`.  The canonical
Gaussian inverse sends zero to zero, so this remains an executable total
map; an unsuccessful orbit simply falls through to the certified track
fallback. -/
def squareRootNewtonStep (parameter point : Gaussian) : Gaussian :=
  let sum := point + parameter * point⁻¹
  { re := sum.re / 2
    im := sum.im / 2 }

/-- Check at most `fuel` rational Newton candidates, evaluating the expensive
track fallback only when none succeeds.  The fallback is deliberately a
thunk so compiled call-by-value evaluation does not construct it eagerly. -/
def firstNewtonOrFallback
    (parameter : Gaussian) (acceptable : Gaussian -> Prop)
    [DecidablePred acceptable] : Nat -> Gaussian -> (Unit -> Gaussian) ->
      Gaussian
  | 0, _point, fallback => fallback ()
  | fuel + 1, point, fallback =>
      if acceptable point then point
      else firstNewtonOrFallback parameter acceptable fuel
        (squareRootNewtonStep parameter point) fallback

theorem firstNewtonOrFallback_acceptable
    (parameter : Gaussian) (acceptable : Gaussian -> Prop)
    [DecidablePred acceptable]
    (fuel : Nat) (point : Gaussian) (fallback : Unit -> Gaussian)
    (fallbackAcceptable : acceptable (fallback ())) :
    acceptable
      (firstNewtonOrFallback parameter acceptable fuel point fallback) := by
  induction fuel generalizing point with
  | zero =>
      simpa only [firstNewtonOrFallback] using fallbackAcceptable
  | succ fuel inductionHypothesis =>
      by_cases pointAcceptable : acceptable point
      · simp only [firstNewtonOrFallback, pointAcceptable, if_pos]
      · simp only [firstNewtonOrFallback, pointAcceptable]
        exact inductionHypothesis (squareRootNewtonStep parameter point)

theorem firstNewtonOrFallback_property
    (parameter : Gaussian) (acceptable property : Gaussian -> Prop)
    [DecidablePred acceptable]
    (fuel : Nat) (point : Gaussian) (fallback : Unit -> Gaussian)
    (acceptedProperty : forall candidate, acceptable candidate ->
      property candidate)
    (fallbackProperty : property (fallback ())) :
    property
      (firstNewtonOrFallback parameter acceptable fuel point fallback) := by
  induction fuel generalizing point with
  | zero =>
      simpa only [firstNewtonOrFallback] using fallbackProperty
  | succ fuel inductionHypothesis =>
      by_cases pointAcceptable : acceptable point
      · simp only [firstNewtonOrFallback, pointAcceptable, if_pos]
        exact acceptedProperty point pointAcceptable
      · simp only [firstNewtonOrFallback, pointAcceptable]
        exact inductionHypothesis (squareRootNewtonStep parameter point)

/-- A preparation sample is accepted only when it is visibly inside the
inherited owner and its exact quadratic residual meets every uniform and
same-occurrence bridge request. -/
def SampleAcceptable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (point : Gaussian) : Prop :=
  owner.track.initial.box.Contains point ∧
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval point) <
      sampleResidualTarget segment owner rootDiameter

instance sampleAcceptableDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    DecidablePred (SampleAcceptable segment owner rootDiameter) :=
  fun point => by
    unfold SampleAcceptable
    infer_instance

/-- Prefer eight exact rational Newton candidates beginning at the owner-box
midpoint.  Generic owners retain the original certified shrinking-track
fallback, while explicit quadratic examples normally stop after only a few
rational steps. -/
def sample
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Gaussian :=
  firstNewtonOrFallback (polynomial.eval (segment.pointAt parameter))
    (SampleAcceptable segment owner rootDiameter) 8
    (ownerMidpoint owner.track.initial.box)
    (fun _ => trackSample segment owner rootDiameter)

theorem sample_acceptable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    SampleAcceptable segment owner rootDiameter
      (sample segment owner rootDiameter) := by
  unfold sample
  exact firstNewtonOrFallback_acceptable _ _ _ _ _
    ⟨trackSample_inside_owner segment owner rootDiameter,
      trackSample_residual_lt segment owner rootDiameterPositive⟩

theorem sample_residual_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <
      sampleResidualTarget segment owner rootDiameter :=
  (sample_acceptable segment owner rootDiameterPositive).2

theorem sample_residual_lt_quarter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) < 1 / 4 :=
  (sample_residual_lt segment owner rootDiameterPositive).trans_le
    ((min_le_left _ _).trans (min_le_left _ _))

theorem sample_residual_le_uniformThreshold
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeThreshold
        segment :=
  ((sample_residual_lt segment owner rootDiameterPositive).trans_le
    ((min_le_left _ _).trans (min_le_right _ _))).le

theorem sample_residual_le_uniformSource
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      rootLipschitz segment *
        (2 * preparationRadius segment rootDiameter ^ 2) :=
  ((sample_residual_lt segment owner rootDiameterPositive).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))).le

theorem sample_residual_le_uniformDisplacement
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment *
        preparationRadius segment rootDiameter ^ 2 :=
  ((sample_residual_lt segment owner rootDiameterPositive).trans_le
    ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))).le

theorem sample_residual_le_bridgeSource
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      RFAP.PolynomialBounds.denseLipschitzBound
          (rootPolynomialAt segment parameter) owner.track.initial.box *
        (2 * bridgeRadius segment owner rootDiameter ^ 2) :=
  ((sample_residual_lt segment owner rootDiameterPositive).trans_le
    ((min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))).le

theorem sample_residual_le_bridgeDisplacement
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment *
        bridgeRadius segment owner rootDiameter ^ 2 :=
  ((sample_residual_lt segment owner rootDiameterPositive).trans_le
    ((min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _)))))).le

theorem sample_residual_lt_ownerQuarter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <
      owner.track.initial.clearance.bound / 4 :=
  (sample_residual_lt segment owner rootDiameterPositive).trans_le
    ((min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _)))))

/-- The selected inherited-owner sample remains in that owner's initial
square. -/
theorem sample_inside_owner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    owner.track.initial.box.Contains (sample segment owner rootDiameter) := by
  unfold sample
  exact firstNewtonOrFallback_property _ _ _ _ _ _
    (fun _candidate accepted => accepted.1)
    (trackSample_inside_owner segment owner rootDiameter)

/-- The quadratic equation and the uniform quarter residual give a direct
norm-square bound for every selected sample. -/
theorem sample_normSq_le_rootSampleNormSqMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (sample segment owner rootDiameter) <=
      rootSampleNormSqMajorant segment := by
  let point := sample segment owner rootDiameter
  let radicand := polynomial.eval (segment.pointAt parameter)
  let bound := radicandNormBound segment
  let residual := (rootPolynomialAt segment parameter).eval point
  have radicandBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq radicand <= bound :=
    eval_normSq_le_radicandNormBound segment parameter inside
  have residualBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq residual <= 1 / 4 :=
    (sample_residual_lt_quarter segment owner rootDiameterPositive).le
  have powerIdentity : point ^ 2 = residual + radicand := by
    dsimp only [residual, rootPolynomialAt,
      CCL.Riemann.SquareRootReconditioning.rootPolynomial]
    rw [CCL.PowerMonodromy.polynomial_eval,
      CCL.Riemann.SquareRootSheets.degreeTwo_value]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  have pointSquareBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq point ^ 2 <=
        2 * ((1 / 4 : Coordinate) + bound) := by
    rw [← RFAP.ConstructiveGaussian.Gaussian.normSq_pow point 2,
      powerIdentity]
    exact (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add residualBound radicandBound) (by decide))
  have oneLeMajorant : (1 : Coordinate) <=
      2 * ((1 / 4 : Coordinate) + bound) := by
    calc
      1 <= 2 * ((1 / 4 : Coordinate) + 1) := by decide
      _ <= 2 * ((1 / 4 : Coordinate) + bound) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add le_rfl (one_le_radicandNormBound segment)) (by decide)
  let pointNorm := RFAP.ConstructiveGaussian.Gaussian.normSq point
  have pointNormBound : pointNorm <=
      2 * ((1 / 4 : Coordinate) + bound) := by
    by_cases atMostOne : pointNorm <= 1
    · exact atMostOne.trans oneLeMajorant
    · have oneLePoint : (1 : Coordinate) <= pointNorm :=
        (RFAP.ConstructiveFraction.lt_of_not_ge_direct atMostOne).le
      have pointLeSquare : pointNorm <= pointNorm ^ 2 := by
        rw [pow_two]
        calc
          pointNorm = pointNorm * 1 := by ring1
          _ <= pointNorm * pointNorm :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              oneLePoint
              (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg point)
      exact pointLeSquare.trans pointSquareBound
  simpa only [pointNorm, point, bound, rootSampleNormSqMajorant] using
    pointNormBound

/-- The derivative at every selected sample is bounded by the direct uniform
sample majorant. -/
theorem sample_rootDerivative_le_rootSampleDerivativeMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((RFAP.ConstructiveGCD.derivative
          (rootPolynomialAt segment parameter)).eval
            (sample segment owner rootDiameter)) <=
      rootSampleDerivativeMajorant segment := by
  rw [rootDerivative_normSq_formula]
  unfold rootSampleDerivativeMajorant
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    (sample_normSq_le_rootSampleNormSqMajorant segment parameter inside owner
      rootDiameterPositive) (by decide)

/-- The direct sample norm bound lies inside the smaller coordinate core of
the common root ambient. -/
theorem sample_normSq_le_rootSampleCoordinateRadius_sq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (sample segment owner rootDiameter) <=
      rootSampleCoordinateRadius segment ^ 2 := by
  let bound := radicandNormBound segment
  let radius := rootSampleCoordinateRadius segment
  have boundLeSquare : bound <= bound ^ 2 := by
    have oneLe := one_le_radicandNormBound segment
    have nonnegative : (0 : Coordinate) <= bound :=
      (by decide : (0 : Coordinate) <= 1).trans oneLe
    rw [pow_two]
    calc
      bound = bound * 1 := by ring1
      _ <= bound * bound :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct oneLe
          nonnegative
  have scalarBound :
      rootSampleNormSqMajorant segment <= radius ^ 2 := by
    have quarterLeBound : (1 / 4 : Coordinate) <= bound :=
      (by decide : (1 / 4 : Coordinate) <= 1).trans
        (one_le_radicandNormBound segment)
    dsimp only [rootSampleNormSqMajorant]
    change 2 * ((1 / 4 : Coordinate) + bound) <= radius ^ 2
    calc
      2 * ((1 / 4 : Coordinate) + bound) <= 2 * (bound + bound) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add quarterLeBound le_rfl) (by decide)
      _ = 4 * bound := by ring1
      _ <= 4 * bound ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          boundLeSquare (by decide)
      _ = radius ^ 2 := by
        dsimp only [radius, rootSampleCoordinateRadius]
        ring1
  exact (sample_normSq_le_rootSampleNormSqMajorant segment parameter inside
    owner rootDiameterPositive).trans scalarBound

/-- The smaller sample core gives four explicit coordinate bounds, leaving
one full rational unit to every side of the common root ambient. -/
theorem sample_rootSampleCoordinateBounds
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    -rootSampleCoordinateRadius segment <=
        (sample segment owner rootDiameter).re ∧
      (sample segment owner rootDiameter).re <=
        rootSampleCoordinateRadius segment ∧
      -rootSampleCoordinateRadius segment <=
        (sample segment owner rootDiameter).im ∧
      (sample segment owner rootDiameter).im <=
        rootSampleCoordinateRadius segment := by
  exact RFAP.AffineWinding.coordinate_bounds_of_normSq_le
    (by
      unfold rootSampleCoordinateRadius
      exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (radicandNormBound_positive segment).le)
    (sample_normSq_le_rootSampleCoordinateRadius_sq segment parameter inside
      owner rootDiameterPositive)

/-- Every selected sample lies in the common ambient, now by the direct unit
coordinate margin rather than a residual-Lipschitz strip. -/
theorem sample_inside_rootAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (rootAmbient segment).Contains (sample segment owner rootDiameter) := by
  let core := rootSampleCoordinateRadius segment
  have bounds := sample_rootSampleCoordinateBounds segment parameter inside
    owner rootDiameterPositive
  change -rootAmbientRadius segment <=
      (sample segment owner rootDiameter).re ∧
    (sample segment owner rootDiameter).re <= rootAmbientRadius segment ∧
    -rootAmbientRadius segment <= (sample segment owner rootDiameter).im ∧
    (sample segment owner rootDiameter).im <= rootAmbientRadius segment
  dsimp only [rootAmbientRadius]
  exact
    ⟨(by
        calc
          -(core + 1) <= -core := by
            exact RFAP.ConstructiveFraction.neg_le_neg_direct
              (le_add_of_nonneg_right (by decide))
          _ <= (sample segment owner rootDiameter).re := bounds.1),
      bounds.2.1.trans (le_add_of_nonneg_right (by decide)),
      (by
        calc
          -(core + 1) <= -core := by
            exact RFAP.ConstructiveFraction.neg_le_neg_direct
              (le_add_of_nonneg_right (by decide))
          _ <= (sample segment owner rootDiameter).im := bounds.2.2.1),
      bounds.2.2.2.trans (le_add_of_nonneg_right (by decide))⟩

/-- Direct separated restart input on the parameter-independent root
ambient.  Every scalar field is now controlled by segment data and the
requested root diameter; the inherited owner only supplies the occurrence
sample. -/
def restartInput
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ResidualWinding.SeparatedRestartInput
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation
        (rootAmbient := rootAmbient segment) segment parameter inside) := by
  let p := rootPolynomialAt segment parameter
  let radius := preparationRadius segment rootDiameter
  let separation :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation
      (rootAmbient := rootAmbient segment) segment parameter inside
  let point := sample segment owner rootDiameter
  have bounds := sample_rootSampleCoordinateBounds segment parameter inside
    owner rootDiameterPositive
  have twiceRadiusLt : 2 * radius < 1 :=
    two_preparationRadius_lt_one segment rootDiameterPositive
  let core := rootSampleCoordinateRadius segment
  have leftMargin : (rootAmbient segment).xLower + 2 * radius < point.re :=
    (by
      have shifted := RFAP.ConstructiveFraction.add_lt_add_left_direct
        twiceRadiusLt (-(core + 1))
      have coreLower : -(core + 1) + 2 * radius < -core := by
        calc
          -(core + 1) + 2 * radius < -(core + 1) + 1 := shifted
          _ = -core := by ring1
      change -(core + 1) + 2 * radius < point.re
      exact coreLower.trans_le bounds.1)
  have rightMargin : point.re + 2 * radius <
      (rootAmbient segment).xUpper :=
    (by
      change point.re + 2 * radius < core + 1
      exact (RFAP.ConstructiveFraction.add_le_add_right_direct bounds.2.1
          (2 * radius)).trans_lt
        (RFAP.ConstructiveFraction.add_lt_add_left_direct twiceRadiusLt core))
  have bottomMargin : (rootAmbient segment).yLower + 2 * radius < point.im :=
    (by
      have shifted := RFAP.ConstructiveFraction.add_lt_add_left_direct
        twiceRadiusLt (-(core + 1))
      have coreLower : -(core + 1) + 2 * radius < -core := by
        calc
          -(core + 1) + 2 * radius < -(core + 1) + 1 := shifted
          _ = -core := by ring1
      change -(core + 1) + 2 * radius < point.im
      exact coreLower.trans_le bounds.2.2.1)
  have topMargin : point.im + 2 * radius <
      (rootAmbient segment).yUpper :=
    (by
      change point.im + 2 * radius < core + 1
      exact (RFAP.ConstructiveFraction.add_le_add_right_direct bounds.2.2.2
          (2 * radius)).trans_lt
        (RFAP.ConstructiveFraction.add_lt_add_left_direct twiceRadiusLt core))
  apply RFAP.ResidualWinding.SeparatedRestartInput.ofAnchored point radius
    (preparationRadius_positive segment rootDiameterPositive)
    leftMargin rightMargin bottomMargin topMargin
  · change RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      RFAP.PolynomialBounds.denseLipschitzBound
          (rootPolynomialAt segment parameter) (rootAmbient segment) *
        (2 * preparationRadius segment rootDiameter ^ 2)
    rw [rootLipschitz_formula segment parameter]
    exact sample_residual_le_uniformSource segment owner rootDiameterPositive
  · change RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <= separation.threshold
    simpa only [rootLipschitz, separation,
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation_threshold]
      using sample_residual_le_uniformThreshold segment owner
        rootDiameterPositive
  · apply (RFAP.ConstructiveFraction.div_le_iff_pos
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
        segment)).2
    change RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      preparationRadius segment rootDiameter ^ 2 *
        CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment
    simpa only [RFAP.ConstructiveFraction.mul_comm]
      using sample_residual_le_uniformDisplacement segment owner
        rootDiameterPositive
  · change 2 * (36 *
        RFAP.PolynomialBounds.denseTaylorRemainderBound
          (rootPolynomialAt segment parameter) (rootAmbient segment) *
        preparationRadius segment rootDiameter ^ 2) <= separation.margin
    simpa only [separation,
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation_margin]
      using preparation_taylorSmall segment parameter rootDiameterPositive

theorem two_bridgeRadius_lt_ownerInterior
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    2 * bridgeRadius segment owner rootDiameter <
      owner.track.initial.clearance.residualInteriorRadius := by
  let radius := bridgeRadius segment owner rootDiameter
  let interior := owner.track.initial.clearance.residualInteriorRadius
  have radiusLe : radius <= (3 / 8 : Coordinate) * interior :=
    bridgeRadius_le_ownerInteriorScale segment owner rootDiameter
  have interiorPositive : 0 < interior :=
    owner.track.initial.clearance.residualInteriorRadius_pos
  calc
    2 * radius <= 2 * ((3 / 8 : Coordinate) * interior) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct radiusLe
        (by decide)
    _ = (2 * (3 / 8 : Coordinate)) * interior := by ring1
    _ = (3 / 4 : Coordinate) * interior := by
      rw [show (2 : Coordinate) * (3 / 8) = 3 / 4 by decide]
    _ < 1 * interior :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        (by decide) interiorPositive
    _ = interior := by ring1

/-- Same-sample separated restart strictly inside the inherited owner.  It
is used only to prove that the uniform restart carries the same root
occurrence. -/
def bridgeRestartInput
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ResidualWinding.SeparatedRestartInput
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation
        (rootAmbient := owner.track.initial.box) segment parameter inside) := by
  let p := rootPolynomialAt segment parameter
  let ownerBox := owner.track.initial.box
  let radius := bridgeRadius segment owner rootDiameter
  let separation :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation
      (rootAmbient := ownerBox) segment parameter inside
  let point := sample segment owner rootDiameter
  have margins := owner.track.initial.clearance.residualInteriorMargins
    (sample_inside_owner segment owner rootDiameter)
    (sample_residual_lt_ownerQuarter segment owner rootDiameterPositive)
  have twiceRadiusLt :
      2 * radius < owner.track.initial.clearance.residualInteriorRadius :=
    two_bridgeRadius_lt_ownerInterior segment owner rootDiameter
  have leftMargin : ownerBox.xLower + 2 * radius < point.re :=
    (RFAP.ConstructiveFraction.add_lt_add_left_direct twiceRadiusLt
      ownerBox.xLower).trans margins.1
  have rightMargin : point.re + 2 * radius < ownerBox.xUpper :=
    (RFAP.ConstructiveFraction.add_lt_add_left_direct twiceRadiusLt point.re).trans
      margins.2.1
  have bottomMargin : ownerBox.yLower + 2 * radius < point.im :=
    (RFAP.ConstructiveFraction.add_lt_add_left_direct twiceRadiusLt
      ownerBox.yLower).trans margins.2.2.1
  have topMargin : point.im + 2 * radius < ownerBox.yUpper :=
    (RFAP.ConstructiveFraction.add_lt_add_left_direct twiceRadiusLt point.im).trans
      margins.2.2.2
  apply RFAP.ResidualWinding.SeparatedRestartInput.ofAnchored point radius
    (bridgeRadius_positive segment owner rootDiameterPositive)
    leftMargin rightMargin bottomMargin topMargin
  · change RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      RFAP.PolynomialBounds.denseLipschitzBound
          (rootPolynomialAt segment parameter) owner.track.initial.box *
        (2 * bridgeRadius segment owner rootDiameter ^ 2)
    exact sample_residual_le_bridgeSource segment owner rootDiameterPositive
  · change RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <= separation.threshold
    simpa only [separation,
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation_threshold]
      using (sample_residual_le_bridgeSource segment owner
          rootDiameterPositive).trans
        (bridge_sourceThreshold segment owner rootDiameterPositive)
  · apply (RFAP.ConstructiveFraction.div_le_iff_pos
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
        segment)).2
    change RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      bridgeRadius segment owner rootDiameter ^ 2 *
        CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment
    simpa only [RFAP.ConstructiveFraction.mul_comm]
      using sample_residual_le_bridgeDisplacement segment owner
        rootDiameterPositive
  · change 2 * (36 *
        RFAP.PolynomialBounds.denseTaylorRemainderBound
          (rootPolynomialAt segment parameter) owner.track.initial.box *
        bridgeRadius segment owner rootDiameter ^ 2) <= separation.margin
    simpa only [separation,
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation_margin]
      using bridge_taylorSmall segment owner rootDiameterPositive

@[simp] theorem restartInput_source_anchor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (restartInput segment parameter inside owner rootDiameter
      rootDiameterPositive).source.anchor =
        sample segment owner rootDiameter := by
  change (RFAP.ResidualWinding.anchoredSquare
      (sample segment owner rootDiameter)
      (preparationRadius segment rootDiameter)
      (preparationRadius_positive segment rootDiameterPositive).le).anchor = _
  exact RFAP.ResidualWinding.anchoredSquare_anchor _ _ _

@[simp] theorem restartInput_radius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (restartInput segment parameter inside owner rootDiameter
      rootDiameterPositive).radius =
        preparationRadius segment rootDiameter := rfl

/-- The Newton affine term on the prepared square is controlled by the
derivative at its actual sample anchor. -/
theorem restart_newtonLinearization_boundary_le_majorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (z : Gaussian)
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (restartInput segment parameter inside owner rootDiameter
        rootDiameterPositive).centeredBox z) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((RFAP.NewtonWinding.newtonLinearization
          (rootPolynomialAt segment parameter)
          (restartInput segment parameter inside owner rootDiameter
            rootDiameterPositive).source).eval z) <=
      linearizationMajorant segment rootDiameter := by
  let restart := restartInput segment parameter inside owner rootDiameter
    rootDiameterPositive
  have derivativeBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((RFAP.ConstructiveGCD.derivative
            (rootPolynomialAt segment parameter)).eval
              restart.source.anchor) <=
        rootSampleDerivativeMajorant segment := by
    dsimp only [restart]
    rw [restartInput_source_anchor]
    exact sample_rootDerivative_le_rootSampleDerivativeMajorant segment
      parameter inside owner rootDiameterPositive
  have radial :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (z - RFAP.LocalExtraction.anchorNewtonCenter
            (rootPolynomialAt segment parameter) restart.source) <=
        2 * restart.radius ^ 2 := by
    apply RFAP.AffineWinding.centeredSquare_normSq_sub_center_le
      (RFAP.LocalExtraction.anchorNewtonCenter
        (rootPolynomialAt segment parameter) restart.source)
      restart.radiusPositive.le
    exact boundary.1
  rw [RFAP.NewtonWinding.newtonLinearization,
    RFAP.AffineWinding.affineCoordinate_eval,
    RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
          ((RFAP.ConstructiveGCD.derivative
            (rootPolynomialAt segment parameter)).eval restart.source.anchor) *
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (z - RFAP.LocalExtraction.anchorNewtonCenter
            (rootPolynomialAt segment parameter) restart.source) <=
      rootSampleDerivativeMajorant segment * (2 * restart.radius ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_direct derivativeBound radial
          (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
          (rootSampleDerivativeMajorant_positive segment).le
    _ = linearizationMajorant segment rootDiameter := by
      dsimp only [restart]
      rw [restartInput_radius]
      unfold linearizationMajorant
      ring1

@[simp] theorem bridgeRestartInput_source_anchor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeRestartInput segment parameter inside owner rootDiameter
      rootDiameterPositive).source.anchor =
        sample segment owner rootDiameter := by
  change (RFAP.ResidualWinding.anchoredSquare
      (sample segment owner rootDiameter)
      (bridgeRadius segment owner rootDiameter)
      (bridgeRadius_positive segment owner rootDiameterPositive).le).anchor = _
  exact RFAP.ResidualWinding.anchoredSquare_anchor _ _ _

@[simp] theorem bridgeRestartInput_radius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeRestartInput segment parameter inside owner rootDiameter
      rootDiameterPositive).radius =
        bridgeRadius segment owner rootDiameter := rfl

theorem bridgeRadius_lt_preparation
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    bridgeRadius segment owner rootDiameter <
      preparationRadius segment rootDiameter := by
  have bridgeLeQuarter : bridgeRadius segment owner rootDiameter <=
      (1 / 4 : Coordinate) * preparationRadius segment rootDiameter :=
    (min_le_right _ _).trans (min_le_left _ _)
  calc
    bridgeRadius segment owner rootDiameter <=
        (1 / 4 : Coordinate) * preparationRadius segment rootDiameter :=
      bridgeLeQuarter
    _ < 1 * preparationRadius segment rootDiameter :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        (by decide) (preparationRadius_positive segment rootDiameterPositive)
    _ = preparationRadius segment rootDiameter := by ring1

theorem restart_newtonCenter_eq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.LocalExtraction.anchorNewtonCenter
        (rootPolynomialAt segment parameter)
        (bridgeRestartInput segment parameter inside owner rootDiameter
          rootDiameterPositive).source =
      RFAP.LocalExtraction.anchorNewtonCenter
        (rootPolynomialAt segment parameter)
        (restartInput segment parameter inside owner rootDiameter
          rootDiameterPositive).source := by
  rw [RFAP.LocalExtraction.anchorNewtonCenter_eq,
    RFAP.LocalExtraction.anchorNewtonCenter_eq,
    bridgeRestartInput_source_anchor, restartInput_source_anchor]

private def inputAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :=
  CCL.Riemann.SquareRootReconditioning.isolationInput
    (segment.pointAt_eval_ne_zero parameter inside)

/-- Exact clearance bound of every uniform prepared owner.  This expression
contains only segment data and the requested root diameter. -/
def predictedClearance
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) : Coordinate :=
  let radius := preparationRadius segment rootDiameter
  (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment *
        radius ^ 2 -
      36 * 8 * (radius ^ 2) ^ 2) ^ 2 /
    (4 * linearizationMajorant segment rootDiameter)

private theorem oneEighth_sq_eq_one64 :
    (1 / 8 : Coordinate) ^ 2 = 1 / (8 * 8) := by decide

private theorem one64_mul_nineteenQuarter_sq_le_fiveEighth :
    (1 / (8 * 8) : Coordinate) * 1 ^ 2 <= 5 / 8 := by decide

private theorem fiveEighth_eq_one128_mul80 :
    (5 / 8 : Coordinate) = (1 / (16 * 8)) * (10 * 8) := by decide

private theorem zero_le_288 : (0 : Coordinate) <= 36 * 8 :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 36) (by decide)).le
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 8) (by decide)).le
private theorem zero_le_four : (0 : Coordinate) <= 4 := by decide
private theorem zero_le_one64 : (0 : Coordinate) <= 1 / (8 * 8) := by decide
private theorem zero_le_one128 :
    (0 : Coordinate) <= 1 / (16 * 8) := by decide

/-- A small derivative margin gives a simple scan-free upper bound for the
uniform predicted clearance.  The proof uses only the fixed radius cap and
the numerical lower bound on the linearization majorant, so it never reduces
the finite radicand scan. -/
theorem predictedClearance_le_oneOver128
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (marginLe :
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment <=
        (1 / 4 : Coordinate)) :
    predictedClearance segment rootDiameter <=
      (1 / (16 * 8) : Coordinate) := by
  let radius := preparationRadius segment rootDiameter
  let margin :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment
  let majorant := linearizationMajorant segment rootDiameter
  change
    (margin * radius ^ 2 - 36 * 8 * (radius ^ 2) ^ 2) ^ 2 /
        (4 * majorant) <= (1 / (16 * 8) : Coordinate)
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment rootDiameterPositive
  have radiusSqLe : radius ^ 2 <= (1 / (8 * 8) : Coordinate) := by
    calc
      radius ^ 2 <= (1 / 8 : Coordinate) ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le
          (preparationRadius_le_oneEighth segment rootDiameter) 2
      _ = 1 / (8 * 8) := oneEighth_sq_eq_one64
  have marginNonnegative : 0 <= margin :=
    (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
      segment).le
  have bracketNonnegative :
      0 <= margin + (36 * 8) * radius ^ 2 :=
    add_nonneg marginNonnegative
      (RFAP.ConstructiveFraction.mul_nonneg_direct zero_le_288
        (RFAP.ConstructiveFraction.sq_nonneg_direct radius))
  have taylorDenominatorPositive : (0 : Coordinate) < 72 * 8 :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 72) (by decide))
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 8) (by decide))
  have scaledTaylor : radius ^ 2 * (72 * 8) <= margin :=
    (RFAP.ConstructiveFraction.le_div_iff_pos taylorDenominatorPositive).mp
      (preparationRadius_sq_lt_taylorRatio segment
        rootDiameterPositive).le
  have secondTermNonnegative : 0 <= (36 * 8) * radius ^ 2 :=
    RFAP.ConstructiveFraction.mul_nonneg_direct zero_le_288
      (RFAP.ConstructiveFraction.sq_nonneg_direct radius)
  have secondTermLeMargin : (36 * 8) * radius ^ 2 <= margin := by
    calc
      (36 * 8) * radius ^ 2 = 1 * ((36 * 8) * radius ^ 2) := by ring1
      _ <= 2 * ((36 * 8) * radius ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (show (1 : Coordinate) <= 2 by decide) secondTermNonnegative
      _ = radius ^ 2 * (72 * 8) := by ring1
      _ <= margin := scaledTaylor
  have bracketLe :
      margin + (36 * 8) * radius ^ 2 <= (1 : Coordinate) := by
    calc
      margin + (36 * 8) * radius ^ 2 <= margin + margin :=
        add_le_add le_rfl secondTermLeMargin
      _ <= (1 / 4 : Coordinate) + 1 / 4 := add_le_add marginLe marginLe
      _ <= 1 := by decide
  have bracketSqLe :
      (margin + (36 * 8) * radius ^ 2) ^ 2 <=
        (1 : Coordinate) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct bracketNonnegative bracketLe 2
  have scaledBracketLe :
      radius ^ 2 * (margin + (36 * 8) * radius ^ 2) ^ 2 <=
        (5 / 8 : Coordinate) := by
    calc
      radius ^ 2 * (margin + (36 * 8) * radius ^ 2) ^ 2 <=
          (1 / (8 * 8) : Coordinate) *
            (margin + (36 * 8) * radius ^ 2) ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct radiusSqLe
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      _ <= (1 / (8 * 8) : Coordinate) * (1 : Coordinate) ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct bracketSqLe
          zero_le_one64
      _ <= 5 / 8 := one64_mul_nineteenQuarter_sq_le_fiveEighth
  have firstTermNonnegative : 0 <= margin * radius ^ 2 :=
    RFAP.ConstructiveFraction.mul_nonneg_direct marginNonnegative
      (RFAP.ConstructiveFraction.sq_nonneg_direct radius)
  have quadraticTermNonnegative :
      0 <= (36 * 8) * (radius ^ 2) ^ 2 :=
    RFAP.ConstructiveFraction.mul_nonneg_direct zero_le_288
      (RFAP.ConstructiveFraction.sq_nonneg_direct (radius ^ 2))
  have correctionNonnegative :
      0 <= 4 * (margin * radius ^ 2) * ((36 * 8) * (radius ^ 2) ^ 2) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct zero_le_four
        firstTermNonnegative) quadraticTermNonnegative
  have differenceSquareLe :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 <=
        (margin * radius ^ 2 + (36 * 8) * (radius ^ 2) ^ 2) ^ 2 := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 <=
          (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 +
            4 * (margin * radius ^ 2) *
              ((36 * 8) * (radius ^ 2) ^ 2) :=
        le_add_of_nonneg_right
          correctionNonnegative
      _ = (margin * radius ^ 2 + (36 * 8) * (radius ^ 2) ^ 2) ^ 2 := by
        ring1
  have numeratorLe :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 <=
        (5 / 8 : Coordinate) * radius ^ 2 := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 <=
          (margin * radius ^ 2 + (36 * 8) * (radius ^ 2) ^ 2) ^ 2 :=
        differenceSquareLe
      _ = radius ^ 2 *
          (radius ^ 2 * (margin + (36 * 8) * radius ^ 2) ^ 2) := by ring1
      _ <= radius ^ 2 * (5 / 8 : Coordinate) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          scaledBracketLe (RFAP.ConstructiveFraction.sq_nonneg_direct radius)
      _ = (5 / 8 : Coordinate) * radius ^ 2 := by ring1
  have majorantLower :
      (10 * 8) * radius ^ 2 <= 4 * majorant := by
    have base :=
      twenty_mul_preparationRadius_sq_le_linearizationMajorant segment
        rootDiameter
    calc
      (10 * 8) * radius ^ 2 = 4 * (20 * radius ^ 2) := by ring1
      _ <= 4 * majorant :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct base
          zero_le_four
  have numeratorLeScaledMajorant :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 <=
        (1 / (16 * 8) : Coordinate) * (4 * majorant) := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 <=
          (5 / 8 : Coordinate) * radius ^ 2 := numeratorLe
      _ = (1 / (16 * 8) : Coordinate) * ((10 * 8) * radius ^ 2) := by
        rw [← mul_assoc, ← fiveEighth_eq_one128_mul80]
      _ <= (1 / (16 * 8) : Coordinate) * (4 * majorant) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          majorantLower zero_le_one128
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (linearizationMajorant_positive segment rootDiameterPositive)
  exact (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).2
    numeratorLeScaledMajorant

/-- At radius at most `1/64`, the universal quadratic sample lower bound is
already strong enough to retain any ambient transport with a quarter-unit
residual margin.  This sharper finite estimate is useful for explicit path
cells whose valid margin is below `1/2`. -/
theorem predictedClearance_le_quarterTransportFloor_of_radius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (marginLe :
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment <=
        (1 / 4 : Coordinate))
    (radiusLe : preparationRadius segment rootDiameter ≤
      (1 / 64 : Coordinate)) :
    predictedClearance segment rootDiameter ≤
      (1 / 4 : Coordinate) ^ 2 / (4 * 65536) := by
  let radius := preparationRadius segment rootDiameter
  let margin :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment
  let majorant := linearizationMajorant segment rootDiameter
  change
    (margin * radius ^ 2 - 36 * 8 * (radius ^ 2) ^ 2) ^ 2 /
        (4 * majorant) ≤ (1 / 4 : Coordinate) ^ 2 / (4 * 65536)
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment rootDiameterPositive
  have radiusSqNonnegative : 0 ≤ radius ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct radius
  have radiusSqLe : radius ^ 2 ≤ (1 / 4096 : Coordinate) := by
    calc
      radius ^ 2 ≤ (1 / 64 : Coordinate) ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le
          radiusLe 2
      _ = (1 / 4096 : Coordinate) := by
        rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct]
        rw [one_mul]
        rw [show (64 : Coordinate) * 64 = 4096 by ring1]
  have marginNonnegative : 0 ≤ margin :=
    (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
      segment).le
  have taylorDenominatorPositive : (0 : Coordinate) < 72 * 8 :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 72) (by decide))
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 8) (by decide))
  have scaledTaylor : radius ^ 2 * (72 * 8) ≤ margin :=
    (RFAP.ConstructiveFraction.le_div_iff_pos taylorDenominatorPositive).mp
      (preparationRadius_sq_lt_taylorRatio segment
        rootDiameterPositive).le
  have secondTermNonnegative : 0 ≤ (36 * 8) * radius ^ 2 :=
    RFAP.ConstructiveFraction.mul_nonneg_direct zero_le_288
      radiusSqNonnegative
  have secondTermLeMargin : (36 * 8) * radius ^ 2 ≤ margin := by
    calc
      (36 * 8) * radius ^ 2 = 1 * ((36 * 8) * radius ^ 2) := by ring1
      _ ≤ 2 * ((36 * 8) * radius ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (show (1 : Coordinate) ≤ 2 by decide) secondTermNonnegative
      _ = radius ^ 2 * (72 * 8) := by ring1
      _ ≤ margin := scaledTaylor
  have correctionNonnegative : 0 ≤ (36 * 8) * (radius ^ 2) ^ 2 :=
    RFAP.ConstructiveFraction.mul_nonneg_direct zero_le_288
      (RFAP.ConstructiveFraction.sq_nonneg_direct (radius ^ 2))
  have correctionLeFirst :
      (36 * 8) * (radius ^ 2) ^ 2 ≤ margin * radius ^ 2 := by
    calc
      (36 * 8) * (radius ^ 2) ^ 2 =
          ((36 * 8) * radius ^ 2) * radius ^ 2 := by ring1
      _ ≤ margin * radius ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          secondTermLeMargin radiusSqNonnegative
  have differenceNonnegative :
      0 ≤ margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 :=
    RFAP.ConstructiveFraction.sub_nonneg_direct correctionLeFirst
  have differenceLeFirst :
      margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 ≤
        margin * radius ^ 2 := by
    calc
      margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 ≤
          margin * radius ^ 2 - 0 :=
        RFAP.ConstructiveFraction.sub_le_sub_left_direct
          correctionNonnegative _
      _ = margin * radius ^ 2 := by ring1
  have differenceSquareLe :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        (margin * radius ^ 2) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct differenceNonnegative
      differenceLeFirst 2
  have marginSquareLe : margin ^ 2 ≤ (1 / 16 : Coordinate) := by
    calc
      margin ^ 2 ≤ (1 / 4 : Coordinate) ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct marginNonnegative
          marginLe 2
      _ = (1 / 16 : Coordinate) := by decide
  have radiusFourthLe : (radius ^ 2) ^ 2 ≤
      (1 / 4096 : Coordinate) * radius ^ 2 := by
    rw [pow_two]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      radiusSqLe radiusSqNonnegative
  have numeratorLe :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        (1 / 65536 : Coordinate) * radius ^ 2 := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
          (margin * radius ^ 2) ^ 2 := differenceSquareLe
      _ = margin ^ 2 * (radius ^ 2) ^ 2 := by ring1
      _ ≤ (1 / 16 : Coordinate) * (radius ^ 2) ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          marginSquareLe
            (RFAP.ConstructiveFraction.sq_nonneg_direct (radius ^ 2))
      _ ≤ (1 / 16 : Coordinate) *
          ((1 / 4096 : Coordinate) * radius ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          radiusFourthLe (by decide)
      _ = ((1 / 16 : Coordinate) * (1 / 4096)) * radius ^ 2 := by ring1
      _ = (1 / 65536 : Coordinate) * radius ^ 2 := by
        have coefficientProduct :
            (1 / 16 : Coordinate) * (1 / 4096) = 1 / 65536 := by
          rw [RFAP.ConstructiveFraction.div_mul_div_direct]
          rw [one_mul]
          rw [show (16 : Coordinate) * 4096 = 65536 by ring1]
        rw [coefficientProduct]
  have majorantLower : (80 : Coordinate) * radius ^ 2 ≤ 4 * majorant := by
    have base :=
      twenty_mul_preparationRadius_sq_le_linearizationMajorant segment
        rootDiameter
    calc
      (80 : Coordinate) * radius ^ 2 = 4 * (20 * radius ^ 2) := by ring1
      _ ≤ 4 * majorant :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct base
          zero_le_four
  let floor : Coordinate := (1 / 4 : Coordinate) ^ 2 / (4 * 65536)
  have largeDenominatorPositive : (0 : Coordinate) < 4 * 65536 :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 4) (by decide))
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 65536) (by decide))
  have largeDenominatorNonzero : (4 * 65536 : Coordinate) ≠ 0 :=
    largeDenominatorPositive.ne'
  have sixtyFiveThousandFiveHundredThirtySixNonzero :
      (65536 : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 65536) (by decide)).ne'
  have coefficientLe : (1 / 65536 : Coordinate) ≤ floor * 80 := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct _
      largeDenominatorPositive
    calc
      (1 / 65536 : Coordinate) * (4 * 65536) =
          ((1 / 65536 : Coordinate) * 65536) * 4 := by ring1
      _ = 4 := by
        rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          sixtyFiveThousandFiveHundredThirtySixNonzero]
        ring1
      _ ≤ 5 := by decide
      _ = (floor * 80) * (4 * 65536) := by
        dsimp only [floor]
        rw [show (((1 / 4 : Coordinate) ^ 2 / (4 * 65536)) * 80) *
            (4 * 65536) =
          (((1 / 4 : Coordinate) ^ 2 / (4 * 65536)) *
            (4 * 65536)) * 80 by ring1]
        rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          largeDenominatorNonzero]
        rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct]
        rw [one_mul]
        rw [show (4 : Coordinate) * 4 = 16 by ring1]
        rw [show (80 : Coordinate) = 16 * 5 by ring1]
        rw [← mul_assoc,
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
            (show (16 : Coordinate) ≠ 0 by decide)]
        ring1
  have numeratorLeFloorMajorant :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        floor * (4 * majorant) := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
          (1 / 65536 : Coordinate) * radius ^ 2 := numeratorLe
      _ ≤ (floor * 80) * radius ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          coefficientLe radiusSqNonnegative
      _ = floor * (80 * radius ^ 2) := by ring1
      _ ≤ floor * (4 * majorant) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          majorantLower
            (RFAP.ConstructiveFraction.div_nonneg_direct
              (RFAP.ConstructiveFraction.sq_nonneg_direct (1 / 4))
                largeDenominatorPositive.le)
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (linearizationMajorant_positive segment rootDiameterPositive)
  exact (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).2
    numeratorLeFloorMajorant

/-- A segment-specific linearization lower bound upgrades the quarter-margin
estimate to the smaller transport floor associated with an eighth-unit
residual.  The additional premise is finite cached data: explicit cells can
establish it from one endpoint radicand sample without unfolding the full
dyadic majorant. -/
theorem predictedClearance_le_eighthTransportFloor_of_radius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (marginLe :
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment <=
        (1 / 4 : Coordinate))
    (radiusLe : preparationRadius segment rootDiameter ≤
      (1 / 64 : Coordinate))
    (majorantLower :
      256 * preparationRadius segment rootDiameter ^ 2 ≤
        4 * linearizationMajorant segment rootDiameter) :
    predictedClearance segment rootDiameter ≤
      (1 / 8 : Coordinate) ^ 2 / (4 * 65536) := by
  let radius := preparationRadius segment rootDiameter
  let margin :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment
  let majorant := linearizationMajorant segment rootDiameter
  change
    (margin * radius ^ 2 - 36 * 8 * (radius ^ 2) ^ 2) ^ 2 /
        (4 * majorant) ≤ (1 / 8 : Coordinate) ^ 2 / (4 * 65536)
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment rootDiameterPositive
  have radiusSqNonnegative : 0 ≤ radius ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct radius
  have radiusSqLe : radius ^ 2 ≤ (1 / 4096 : Coordinate) := by
    calc
      radius ^ 2 ≤ (1 / 64 : Coordinate) ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le
          radiusLe 2
      _ = (1 / 4096 : Coordinate) := by
        rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct]
        rw [one_mul]
        rw [show (64 : Coordinate) * 64 = 4096 by ring1]
  have marginNonnegative : 0 ≤ margin :=
    (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
      segment).le
  have taylorDenominatorPositive : (0 : Coordinate) < 72 * 8 :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 72) (by decide))
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 8) (by decide))
  have scaledTaylor : radius ^ 2 * (72 * 8) ≤ margin :=
    (RFAP.ConstructiveFraction.le_div_iff_pos taylorDenominatorPositive).mp
      (preparationRadius_sq_lt_taylorRatio segment
        rootDiameterPositive).le
  have secondTermNonnegative : 0 ≤ (36 * 8) * radius ^ 2 :=
    RFAP.ConstructiveFraction.mul_nonneg_direct zero_le_288
      radiusSqNonnegative
  have secondTermLeMargin : (36 * 8) * radius ^ 2 ≤ margin := by
    calc
      (36 * 8) * radius ^ 2 = 1 * ((36 * 8) * radius ^ 2) := by ring1
      _ ≤ 2 * ((36 * 8) * radius ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (show (1 : Coordinate) ≤ 2 by decide) secondTermNonnegative
      _ = radius ^ 2 * (72 * 8) := by ring1
      _ ≤ margin := scaledTaylor
  have correctionNonnegative : 0 ≤ (36 * 8) * (radius ^ 2) ^ 2 :=
    RFAP.ConstructiveFraction.mul_nonneg_direct zero_le_288
      (RFAP.ConstructiveFraction.sq_nonneg_direct (radius ^ 2))
  have correctionLeFirst :
      (36 * 8) * (radius ^ 2) ^ 2 ≤ margin * radius ^ 2 := by
    calc
      (36 * 8) * (radius ^ 2) ^ 2 =
          ((36 * 8) * radius ^ 2) * radius ^ 2 := by ring1
      _ ≤ margin * radius ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          secondTermLeMargin radiusSqNonnegative
  have differenceNonnegative :
      0 ≤ margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 :=
    RFAP.ConstructiveFraction.sub_nonneg_direct correctionLeFirst
  have differenceLeFirst :
      margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 ≤
        margin * radius ^ 2 := by
    calc
      margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 ≤
          margin * radius ^ 2 - 0 :=
        RFAP.ConstructiveFraction.sub_le_sub_left_direct
          correctionNonnegative _
      _ = margin * radius ^ 2 := by ring1
  have differenceSquareLe :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        (margin * radius ^ 2) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct differenceNonnegative
      differenceLeFirst 2
  have marginSquareLe : margin ^ 2 ≤ (1 / 16 : Coordinate) := by
    calc
      margin ^ 2 ≤ (1 / 4 : Coordinate) ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct marginNonnegative
          marginLe 2
      _ = (1 / 16 : Coordinate) := by decide
  have radiusFourthLe : (radius ^ 2) ^ 2 ≤
      (1 / 4096 : Coordinate) * radius ^ 2 := by
    rw [pow_two]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      radiusSqLe radiusSqNonnegative
  have numeratorLe :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        (1 / 65536 : Coordinate) * radius ^ 2 := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
          (margin * radius ^ 2) ^ 2 := differenceSquareLe
      _ = margin ^ 2 * (radius ^ 2) ^ 2 := by ring1
      _ ≤ (1 / 16 : Coordinate) * (radius ^ 2) ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          marginSquareLe
            (RFAP.ConstructiveFraction.sq_nonneg_direct (radius ^ 2))
      _ ≤ (1 / 16 : Coordinate) *
          ((1 / 4096 : Coordinate) * radius ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          radiusFourthLe (by decide)
      _ = ((1 / 16 : Coordinate) * (1 / 4096)) * radius ^ 2 := by ring1
      _ = (1 / 65536 : Coordinate) * radius ^ 2 := by
        have coefficientProduct :
            (1 / 16 : Coordinate) * (1 / 4096) = 1 / 65536 := by
          rw [RFAP.ConstructiveFraction.div_mul_div_direct]
          rw [one_mul]
          rw [show (16 : Coordinate) * 4096 = 65536 by ring1]
        rw [coefficientProduct]
  let floor : Coordinate := (1 / 8 : Coordinate) ^ 2 / (4 * 65536)
  have largeDenominatorPositive : (0 : Coordinate) < 4 * 65536 :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 4) (by decide))
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 65536) (by decide))
  have largeDenominatorNonzero : (4 * 65536 : Coordinate) ≠ 0 :=
    largeDenominatorPositive.ne'
  have sixtyFiveThousandFiveHundredThirtySixNonzero :
      (65536 : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 65536) (by decide)).ne'
  have sixtyFourNonzero : (64 : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 64) (by decide)).ne'
  have coefficientEq :
      (1 / 65536 : Coordinate) = floor * 256 := by
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      largeDenominatorNonzero
    calc
      (1 / 65536 : Coordinate) * (4 * 65536) = 4 := by
        rw [show (1 / 65536 : Coordinate) * (4 * 65536) =
          ((1 / 65536 : Coordinate) * 65536) * 4 by ring1]
        rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          sixtyFiveThousandFiveHundredThirtySixNonzero]
        ring1
      _ = (floor * 256) * (4 * 65536) := by
        dsimp only [floor]
        rw [show (((1 / 8 : Coordinate) ^ 2 / (4 * 65536)) * 256) *
            (4 * 65536) =
          (((1 / 8 : Coordinate) ^ 2 / (4 * 65536)) *
            (4 * 65536)) * 256 by ring1]
        rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          largeDenominatorNonzero]
        rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct]
        rw [one_mul]
        rw [show (8 : Coordinate) * 8 = 64 by ring1]
        rw [show (256 : Coordinate) = 64 * 4 by ring1]
        rw [← mul_assoc,
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
            sixtyFourNonzero]
        ring1
  have floorNonnegative : 0 ≤ floor :=
    RFAP.ConstructiveFraction.div_nonneg_direct
      (RFAP.ConstructiveFraction.sq_nonneg_direct (1 / 8))
      largeDenominatorPositive.le
  have numeratorLeFloorMajorant :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        floor * (4 * majorant) := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
          (1 / 65536 : Coordinate) * radius ^ 2 := numeratorLe
      _ = (floor * 256) * radius ^ 2 := by rw [coefficientEq]
      _ = floor * (256 * radius ^ 2) := by ring1
      _ ≤ floor * (4 * majorant) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          majorantLower floorNonnegative
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (linearizationMajorant_positive segment rootDiameterPositive)
  exact (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).2
    numeratorLeFloorMajorant

private theorem floorThirtyTwo_positive : (0 : Coordinate) < 32 := by
  rw [show (32 : Coordinate) = 2 ^ 5 by ring1]
  exact RFAP.ConstructiveFraction.pow_pos_direct (by decide) 5

private theorem floor_pow_ne_zero (value : Coordinate)
    (nonzero : value ≠ 0) : ∀ exponent : Nat, value ^ exponent ≠ 0
  | 0 => by
      simpa only [pow_zero] using (show (1 : Coordinate) ≠ 0 by decide)
  | exponent + 1 => by
      rw [pow_succ]
      exact RFAP.ConstructiveFraction.mul_ne_zero_direct
        (floor_pow_ne_zero value nonzero exponent) nonzero

private theorem floorSixtyFour_ne : (64 : Coordinate) ≠ 0 := by
  rw [show (64 : Coordinate) = 2 ^ 6 by ring1]
  exact floor_pow_ne_zero 2 (by decide) 6

private theorem oneQuarter_cube : (1 / 4 : Coordinate) ^ 3 = 1 / 64 := by
  rw [show (1 / 4 : Coordinate) ^ 3 =
    (1 / 4) * (1 / 4) * (1 / 4) by ring1]
  rw [RFAP.ConstructiveFraction.div_mul_div_direct,
    RFAP.ConstructiveFraction.div_mul_div_direct]
  apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
    (RFAP.ConstructiveFraction.mul_ne_zero_direct
      (RFAP.ConstructiveFraction.mul_ne_zero_direct (by decide) (by decide))
      (by decide))
    floorSixtyFour_ne
  ring1

private theorem floorSixtyFiveThousandFiveHundredThirtySix_ne :
    (65536 : Coordinate) ≠ 0 := by
  rw [show (65536 : Coordinate) = 2 ^ 16 by ring1]
  exact floor_pow_ne_zero 2 (by decide) 16

private theorem floorSixtyFiveThousandFiveHundredThirtySix_positive :
    (0 : Coordinate) < 65536 := by
  rw [show (65536 : Coordinate) = 2 ^ 16 by ring1]
  exact RFAP.ConstructiveFraction.pow_pos_direct (by decide) 16

private theorem floorOneOverThirtyTwo_mul_eight :
    (1 / 32 : Coordinate) * 8 = 1 / 4 := by
  rw [show (8 : Coordinate) = 8 / 1 by decide,
    RFAP.ConstructiveFraction.div_mul_div_direct]
  apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
    (RFAP.ConstructiveFraction.mul_ne_zero_direct
      floorThirtyTwo_positive.ne' (by decide))
    (by decide)
  ring1

private theorem clearanceFloor_mul_thirtyTwoThousandSevenHundredSixtyEight :
    ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * 32768 = 1 / 32 := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show (8 : Coordinate) ≠ 0 by decide)
  calc
    (((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * 32768) * 8 =
        ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * (32768 * 8) := by ring1
    _ = ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) *
        (4 * 65536) := by
      rw [show (32768 : Coordinate) * 8 = 4 * 65536 by ring1]
    _ = (1 / 2 : Coordinate) ^ 2 :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        (RFAP.ConstructiveFraction.mul_ne_zero_direct (by decide)
          floorSixtyFiveThousandFiveHundredThirtySix_ne)
    _ = 1 / 4 := by decide
    _ = (1 / 32 : Coordinate) * 8 := floorOneOverThirtyTwo_mul_eight.symm

private theorem floorOneOverSixtyFour_le_oneOverThirtyTwo :
    (1 / 64 : Coordinate) ≤ 1 / 32 := by
  apply RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
    (by decide) floorThirtyTwo_positive
  apply sub_nonneg.mp
  rw [show (64 : Coordinate) - 32 = 2 ^ 5 by ring1]
  exact RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) 5

private theorem oneOverSixtyFour_le_clearanceFloor_scaled :
    (1 / 64 : Coordinate) ≤
      (((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * 80) * (72 * 8) := by
  have floorNonnegative : (0 : Coordinate) ≤
      (1 / 2 : Coordinate) ^ 2 / (4 * 65536) :=
    RFAP.ConstructiveFraction.div_nonneg_direct
      (RFAP.ConstructiveFraction.sq_nonneg_direct (1 / 2))
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        floorSixtyFiveThousandFiveHundredThirtySix_positive.le)
  have scaleLe : (32768 : Coordinate) ≤ 80 * (72 * 8) := by
    apply sub_nonneg.mp
    rw [show (80 : Coordinate) * (72 * 8) - 32768 =
      13 * 2 ^ 10 by ring1]
    exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) 10)
  calc
    (1 / 64 : Coordinate) ≤ 1 / 32 :=
      floorOneOverSixtyFour_le_oneOverThirtyTwo
    _ = ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * 32768 :=
      clearanceFloor_mul_thirtyTwoThousandSevenHundredSixtyEight.symm
    _ ≤ ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) *
        (80 * (72 * 8)) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        scaleLe floorNonnegative
    _ = (((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * 80) *
        (72 * 8) := by ring1

/-- The Taylor-radius term sharpens the scan-free clearance estimate enough
to retain a transported prepared owner whose four side majorants are at most
`65536`. -/
theorem predictedClearance_le_transportFloor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (marginLe :
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment ≤
        (1 / 4 : Coordinate)) :
    predictedClearance segment rootDiameter ≤
      (1 / 2 : Coordinate) ^ 2 / (4 * 65536) := by
  let radius := preparationRadius segment rootDiameter
  let margin :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment
  let majorant := linearizationMajorant segment rootDiameter
  change
    (margin * radius ^ 2 - 36 * 8 * (radius ^ 2) ^ 2) ^ 2 /
        (4 * majorant) ≤ (1 / 2 : Coordinate) ^ 2 / (4 * 65536)
  have radiusSqNonnegative : (0 : Coordinate) ≤ radius ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct radius
  have marginNonnegative : (0 : Coordinate) ≤ margin :=
    (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
      segment).le
  have taylorDenominatorPositive : (0 : Coordinate) < 72 * 8 :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 72) (by decide))
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 8) (by decide))
  have scaledTaylor : radius ^ 2 * (72 * 8) ≤ margin :=
    (RFAP.ConstructiveFraction.le_div_iff_pos
      taylorDenominatorPositive).mp
      (preparationRadius_sq_lt_taylorRatio segment
        rootDiameterPositive).le
  have correctionCoefficientNonnegative :
      (0 : Coordinate) ≤ 36 * 8 :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 36) (by decide)).le
      (by decide)
  have correctionNonnegative :
      (0 : Coordinate) ≤ (36 * 8) * (radius ^ 2) ^ 2 :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      correctionCoefficientNonnegative
      (RFAP.ConstructiveFraction.sq_nonneg_direct (radius ^ 2))
  have correctionCoefficientLeMargin :
      (36 * 8) * radius ^ 2 ≤ margin := by
    calc
      (36 * 8) * radius ^ 2 = 1 * ((36 * 8) * radius ^ 2) := by ring1
      _ ≤ 2 * ((36 * 8) * radius ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (by decide) (RFAP.ConstructiveFraction.mul_nonneg_direct
            correctionCoefficientNonnegative radiusSqNonnegative)
      _ = radius ^ 2 * (72 * 8) := by ring1
      _ ≤ margin := scaledTaylor
  have correctionLeFirst :
      (36 * 8) * (radius ^ 2) ^ 2 ≤ margin * radius ^ 2 := by
    calc
      (36 * 8) * (radius ^ 2) ^ 2 =
          ((36 * 8) * radius ^ 2) * radius ^ 2 := by ring1
      _ ≤ margin * radius ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          correctionCoefficientLeMargin radiusSqNonnegative
  have differenceNonnegative :
      (0 : Coordinate) ≤
        margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 :=
    sub_nonneg.mpr correctionLeFirst
  have differenceLeFirst :
      margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 ≤
        margin * radius ^ 2 := by
    calc
      margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 ≤
          margin * radius ^ 2 - 0 :=
        RFAP.ConstructiveFraction.sub_le_sub_left_direct
          correctionNonnegative (margin * radius ^ 2)
      _ = margin * radius ^ 2 := by ring1
  have numeratorLe :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        (margin * radius ^ 2) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      differenceNonnegative differenceLeFirst 2
  have marginCubeLe : margin ^ 3 ≤ (1 / 4 : Coordinate) ^ 3 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct marginNonnegative marginLe 3
  have scaledCore :
      (margin ^ 2 * radius ^ 2) * (72 * 8) ≤ (1 / 64 : Coordinate) := by
    calc
      (margin ^ 2 * radius ^ 2) * (72 * 8) =
          margin ^ 2 * (radius ^ 2 * (72 * 8)) := by ring1
      _ ≤ margin ^ 2 * margin :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          scaledTaylor (RFAP.ConstructiveFraction.sq_nonneg_direct margin)
      _ = margin ^ 3 := by ring1
      _ ≤ (1 / 4 : Coordinate) ^ 3 := marginCubeLe
      _ = 1 / 64 := oneQuarter_cube
  have coreLe : margin ^ 2 * radius ^ 2 ≤
      ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * 80 := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      _ taylorDenominatorPositive
    exact scaledCore.trans oneOverSixtyFour_le_clearanceFloor_scaled
  have majorantLower : (80 : Coordinate) * radius ^ 2 ≤ 4 * majorant := by
    have base := twenty_mul_preparationRadius_sq_le_linearizationMajorant
      segment rootDiameter
    calc
      (80 : Coordinate) * radius ^ 2 = 4 * (20 * radius ^ 2) := by ring1
      _ ≤ 4 * majorant :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          base (by decide)
  have floorNonnegative : (0 : Coordinate) ≤
      (1 / 2 : Coordinate) ^ 2 / (4 * 65536) :=
    RFAP.ConstructiveFraction.div_nonneg_direct
      (RFAP.ConstructiveFraction.sq_nonneg_direct (1 / 2))
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        floorSixtyFiveThousandFiveHundredThirtySix_positive.le)
  have numeratorLeScaledMajorant :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * (4 * majorant) := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
          (margin * radius ^ 2) ^ 2 := numeratorLe
      _ = (margin ^ 2 * radius ^ 2) * radius ^ 2 := by ring1
      _ ≤ (((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * 80) *
          radius ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          coreLe radiusSqNonnegative
      _ = ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) *
          (80 * radius ^ 2) := by ring1
      _ ≤ ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) *
          (4 * majorant) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          majorantLower floorNonnegative
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (linearizationMajorant_positive segment rootDiameterPositive)
  exact (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).2
    numeratorLeScaledMajorant

/-- Winding-one state on the predictable uniform restart square. -/
def state
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomialAt segment parameter)
      (restartInput segment parameter inside owner rootDiameter
        rootDiameterPositive).centeredBox := by
  let restart := restartInput segment parameter inside owner
    rootDiameter rootDiameterPositive
  let isolation := inputAt segment parameter inside
  let majorant := linearizationMajorant segment rootDiameter
  let majorantPositive :=
    linearizationMajorant_positive segment rootDiameterPositive
  let majorantUpper : forall z : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary restart.centeredBox z ->
        RFAP.ConstructiveGaussian.Gaussian.normSq
          ((RFAP.NewtonWinding.newtonLinearization
            (rootPolynomialAt segment parameter) restart.source).eval z) <=
          majorant := by
    intro z boundary
    change RFAP.ConstructiveGaussian.Gaussian.normSq
        ((RFAP.NewtonWinding.newtonLinearization
          (rootPolynomialAt segment parameter) restart.source).eval z) <=
      linearizationMajorant segment rootDiameter
    exact restart_newtonLinearization_boundary_le_majorant segment parameter
      inside owner rootDiameter rootDiameterPositive z boundary
  exact restart.centeredStateWithMajorant isolation.degreeAtLeastTwo majorant
    majorantPositive majorantUpper

@[simp] theorem state_clearance_bound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (state segment parameter inside owner rootDiameter
      rootDiameterPositive).clearance.bound =
        predictedClearance segment rootDiameter := by
  unfold state
  rw [RFAP.ResidualWinding.SeparatedRestartInput.centeredStateWithMajorant_clearance_bound]
  unfold predictedClearance RFAP.NewtonWinding.separatedNewtonDominanceMargin
    RFAP.NewtonWinding.newtonErrorBudget
  rw [CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation_margin]
  change
    (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment *
          (restartInput segment parameter inside owner rootDiameter
            rootDiameterPositive).radius ^ 2 -
        36 * RFAP.PolynomialBounds.denseTaylorRemainderBound
            (rootPolynomialAt segment parameter) (rootAmbient segment) *
          ((restartInput segment parameter inside owner rootDiameter
            rootDiameterPositive).radius ^ 2) ^ 2) ^ 2 /
      (4 * linearizationMajorant segment rootDiameter) = _
  rw [restartInput_radius, rootTaylor_formula segment parameter]

theorem predictedClearance_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    0 < predictedClearance segment rootDiameter := by
  let parameter : Coordinate := 0
  let inside : (0 : Coordinate) <= parameter ∧ parameter <= 1 := by
    dsimp only [parameter]
    decide
  let radicand := polynomial.eval (segment.pointAt parameter)
  let owner : Owner radicand :=
    CCL.Riemann.SquareRootContinuationChain.Owner.independent
      (segment.pointAt_eval_ne_zero parameter inside) 0
  rw [<- state_clearance_bound segment parameter inside owner
    rootDiameter rootDiameterPositive]
  exact (state segment parameter inside owner rootDiameter
    rootDiameterPositive).clearance.positive

/-- Total shrinking program beginning at the uniform restart state. -/
def track
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ShrinkingTrack.WindingOneTrack
      (rootPolynomialAt segment parameter)
      (restartInput segment parameter inside owner rootDiameter
        rootDiameterPositive).centeredBox := by
  let restart := restartInput segment parameter inside owner
    rootDiameter rootDiameterPositive
  let isolation := inputAt segment parameter inside
  let majorant := linearizationMajorant segment rootDiameter
  let majorantPositive :=
    linearizationMajorant_positive segment rootDiameterPositive
  let majorantUpper : forall z : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary restart.centeredBox z ->
        RFAP.ConstructiveGaussian.Gaussian.normSq
          ((RFAP.NewtonWinding.newtonLinearization
            (rootPolynomialAt segment parameter) restart.source).eval z) <=
          majorant := by
    intro z boundary
    change RFAP.ConstructiveGaussian.Gaussian.normSq
        ((RFAP.NewtonWinding.newtonLinearization
          (rootPolynomialAt segment parameter) restart.source).eval z) <=
      linearizationMajorant segment rootDiameter
    exact restart_newtonLinearization_boundary_le_majorant segment parameter
      inside owner rootDiameter rootDiameterPositive z boundary
  exact restart.centeredTrackWithMajorant isolation.squarefree
    isolation.elimination isolation.degreeAtLeastTwo majorant majorantPositive
    majorantUpper

/-- Owner on the uniform predictable square.  The inherited owner affects
only the displayed occurrence sample, not the ambient, radius, or clearance
formula. -/
def prepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    Owner (polynomial.eval (segment.pointAt parameter)) where
  parameterNonzero := segment.pointAt_eval_ne_zero parameter inside
  ambient := (restartInput segment parameter inside owner rootDiameter
    rootDiameterPositive).centeredBox
  track := track segment parameter inside owner rootDiameter
    rootDiameterPositive

@[simp] theorem prepared_initial_box
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
      rootDiameterPositive).track.initial.box =
        (restartInput segment parameter inside owner rootDiameter
          rootDiameterPositive).centeredBox := by
  unfold prepared track RFAP.ResidualWinding.SeparatedRestartInput.centeredTrackWithMajorant
    RFAP.ShrinkingTrack.ofInitial
  rfl

@[simp] theorem prepared_clearance_bound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
      rootDiameterPositive).track.initial.clearance.bound =
        predictedClearance segment rootDiameter := by
  exact state_clearance_bound segment parameter inside owner
    rootDiameter rootDiameterPositive

@[simp] theorem prepared_diagonalSq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
      rootDiameterPositive).track.initial.box.diagonalSq =
        8 * preparationRadius segment rootDiameter ^ 2 := by
  change (restartInput segment parameter inside owner rootDiameter
    rootDiameterPositive).centeredBox.diagonalSq = _
  rw [RFAP.ResidualWinding.SeparatedRestartInput.centeredBox_diagonalSq,
    restartInput_radius]

/-- Uniform preparation satisfies the derivative-controlled diameter bound,
not merely the caller's usually much coarser requested diameter. -/
theorem prepared_diagonal_lt_derivativeDiameterBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
      rootDiameterPositive).track.initial.box.diagonalSq <
        derivativeDiameterBound segment := by
  rw [prepared_diagonalSq segment parameter inside owner rootDiameterPositive]
  unfold derivativeDiameterBound
  exact RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct (by decide)
    (preparationRadius_sq_lt_taylorRatio segment rootDiameterPositive)

theorem prepared_diagonal_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
      rootDiameterPositive).track.initial.box.diagonalSq < rootDiameter := by
  let radius := preparationRadius segment rootDiameter
  let diameterCap :=
    CCL.FiniteGeometric.dyadicSquareRadius (rootDiameter / 8)
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment rootDiameterPositive
  have radiusLe := preparationRadius_le_diameterCap segment rootDiameter
  have squareLe : radius ^ 2 <= diameterCap ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le radiusLe 2
  have targetPositive : 0 < rootDiameter / 8 :=
    RFAP.ConstructiveFraction.div_pos_direct rootDiameterPositive (by decide)
  have capSquareLt : diameterCap ^ 2 < rootDiameter / 8 :=
    CCL.FiniteGeometric.dyadicSquareRadius_sq_lt targetPositive
  rw [prepared_diagonalSq segment parameter inside owner rootDiameterPositive]
  calc
    8 * radius ^ 2 <= 8 * diameterCap ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareLe
        (by decide)
    _ < 8 * (rootDiameter / 8) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (by decide) capSquareLt
    _ = rootDiameter := by
      calc
        8 * (rootDiameter / 8) = (rootDiameter / 8) * 8 :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ = rootDiameter :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne rootDiameter 8
            (by decide)

/-- Same-sample shrinking track used as the common strict descendant of the
inherited and uniform owners. -/
def bridgeTrack
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ShrinkingTrack.WindingOneTrack
      (rootPolynomialAt segment parameter)
      (bridgeRestartInput segment parameter inside owner rootDiameter
        rootDiameterPositive).centeredBox := by
  let restart := bridgeRestartInput segment parameter inside owner
    rootDiameter rootDiameterPositive
  let isolation := inputAt segment parameter inside
  let majorant :=
    RFAP.NewtonWinding.separatedNewtonLinearizationMajorant
      (rootPolynomialAt segment parameter) owner.track.initial.box
      (bridgeRadius segment owner rootDiameter)
  let majorantPositive :=
    RFAP.NewtonWinding.separatedNewtonLinearizationMajorant_pos
      (rootPolynomialAt segment parameter) owner.track.initial.box
      (bridgeRadius_positive segment owner rootDiameterPositive)
  let majorantUpper : forall z : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary restart.centeredBox z ->
        RFAP.ConstructiveGaussian.Gaussian.normSq
          ((RFAP.NewtonWinding.newtonLinearization
            (rootPolynomialAt segment parameter) restart.source).eval z) <=
          majorant := fun _z boundary =>
    RFAP.NewtonWinding.newtonLinearization_boundary_le_majorant
      restart.sourceRefines restart.radiusPositive boundary
  exact restart.centeredTrackWithMajorant isolation.squarefree
    isolation.elimination isolation.degreeAtLeastTwo majorant majorantPositive
    majorantUpper

/-- The common bridge begins strictly inside the inherited owner. -/
theorem bridgeTrack_initial_strict_owner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeTrack segment parameter inside owner rootDiameter
      rootDiameterPositive).initial.box.StrictInterior
        owner.track.initial.box := by
  change (bridgeRestartInput segment parameter inside owner rootDiameter
      rootDiameterPositive).centeredBox.StrictInterior owner.track.initial.box
  exact (bridgeRestartInput segment parameter inside owner rootDiameter
    rootDiameterPositive).centeredBox_strict

/-- The same bridge is a strict concentric descendant of the uniform owner. -/
theorem bridgeTrack_initial_strict_prepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeTrack segment parameter inside owner rootDiameter
      rootDiameterPositive).initial.box.StrictInterior
        (prepared segment parameter inside owner rootDiameter
          rootDiameterPositive).track.initial.box := by
  change (bridgeRestartInput segment parameter inside owner rootDiameter
      rootDiameterPositive).centeredBox.StrictInterior
    (restartInput segment parameter inside owner rootDiameter
      rootDiameterPositive).centeredBox
  unfold RFAP.ResidualWinding.SeparatedRestartInput.centeredBox
  change
    (RFAP.AffineWinding.centeredSquare
      (RFAP.LocalExtraction.anchorNewtonCenter
        (rootPolynomialAt segment parameter)
        (bridgeRestartInput segment parameter inside owner rootDiameter
          rootDiameterPositive).source)
      (bridgeRadius segment owner rootDiameter)
      (bridgeRadius_positive segment owner rootDiameterPositive).le).StrictInterior
    (RFAP.AffineWinding.centeredSquare
      (RFAP.LocalExtraction.anchorNewtonCenter
        (rootPolynomialAt segment parameter)
        (restartInput segment parameter inside owner rootDiameter
          rootDiameterPositive).source)
      (preparationRadius segment rootDiameter)
      (preparationRadius_positive segment rootDiameterPositive).le)
  rw [restart_newtonCenter_eq segment parameter inside owner
    rootDiameter rootDiameterPositive]
  exact RFAP.AffineWinding.centeredSquare_strictInterior_of_lt _
    (bridgeRadius_positive segment owner rootDiameterPositive).le
    (preparationRadius_positive segment rootDiameterPositive).le
    (bridgeRadius_lt_preparation segment owner rootDiameterPositive)

attribute [irreducible] prepared

end CCL.Riemann.UniformSquareRootPreparation
