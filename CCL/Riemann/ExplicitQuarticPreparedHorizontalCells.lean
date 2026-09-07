import CCL.Riemann.ExplicitQuarticPreparedSecondCellGrid

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

namespace CCL.Riemann.ExplicitQuarticBranches

abbrev HorizontalGaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial

open RFAP.ComputablePolynomial.DensePolynomial

private theorem mulLine_one_coeff
    (origin direction a : Gaussian)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0)
    (leadingNonzero : a ≠ 0) (p : HorizontalGaussianPolynomial)
    (coeffs : p.coeffs = [a]) :
    (RFAP.PathPolynomial.mulLine origin direction p).coeffs =
      [direction * a, origin * a] := by
  unfold RFAP.PathPolynomial.mulLine
  have normalized : p.normalize.coeffs = [a] := by
    rw [normalize_coeffs, coeffs]
    simp [leadingNonzero]
  let originScaled : HorizontalGaussianPolynomial := ⟨[origin * a]⟩
  let directionScaled : HorizontalGaussianPolynomial := ⟨[direction * a]⟩
  have originScaleEq : scale origin p = originScaled := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    rw [scale_coeffs_of_ne_zero originNonzero, normalized]
    rfl
  have directionScaleEq : scale direction p = directionScaled := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    rw [scale_coeffs_of_ne_zero directionNonzero, normalized]
    rfl
  rw [originScaleEq, directionScaleEq]
  have directionScaledNormalized :
      directionScaled.normalize = directionScaled := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    unfold directionScaled normalize
    simp [directionNonzero, leadingNonzero,
      RFAP.ComputablePolynomial.DensePolynomial.mul_ne_zero_direct]
  unfold shift
  rw [if_neg]
  · rw [congrArg RFAP.ComputablePolynomial.DensePolynomial.coeffs
      directionScaledNormalized]
    change (RFAP.ComputablePolynomial.DensePolynomial.add originScaled
      ⟨[direction * a, 0]⟩).coeffs = _
    unfold RFAP.ComputablePolynomial.DensePolynomial.add originScaled normalize
    simp [padLeft, directionNonzero, leadingNonzero,
      RFAP.ComputablePolynomial.DensePolynomial.mul_ne_zero_direct]
  · unfold isZero directionScaled normalize
    simp [directionNonzero, leadingNonzero,
      RFAP.ComputablePolynomial.DensePolynomial.mul_ne_zero_direct]

private theorem mulLine_two_coeffs
    (origin direction a b : Gaussian)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0)
    (leadingNonzero : a ≠ 0) (p : HorizontalGaussianPolynomial)
    (coeffs : p.coeffs = [a, b]) :
    (RFAP.PathPolynomial.mulLine origin direction p).coeffs =
      [direction * a, direction * b + origin * a, origin * b] := by
  unfold RFAP.PathPolynomial.mulLine
  have normalized : p.normalize.coeffs = [a, b] := by
    rw [normalize_coeffs, coeffs]
    simp [leadingNonzero]
  let originScaled : HorizontalGaussianPolynomial :=
    ⟨[origin * a, origin * b]⟩
  let directionScaled : HorizontalGaussianPolynomial :=
    ⟨[direction * a, direction * b]⟩
  have originScaleEq : scale origin p = originScaled := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    rw [scale_coeffs_of_ne_zero originNonzero, normalized]
    rfl
  have directionScaleEq : scale direction p = directionScaled := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    rw [scale_coeffs_of_ne_zero directionNonzero, normalized]
    rfl
  rw [originScaleEq, directionScaleEq]
  have directionScaledNormalized :
      directionScaled.normalize = directionScaled := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    unfold directionScaled normalize
    simp [directionNonzero, leadingNonzero,
      RFAP.ComputablePolynomial.DensePolynomial.mul_ne_zero_direct]
  unfold shift
  rw [if_neg]
  · rw [congrArg RFAP.ComputablePolynomial.DensePolynomial.coeffs
      directionScaledNormalized]
    change (RFAP.ComputablePolynomial.DensePolynomial.add originScaled
      ⟨[direction * a, direction * b, 0]⟩).coeffs = _
    unfold RFAP.ComputablePolynomial.DensePolynomial.add originScaled normalize
    simp [padLeft, directionNonzero, leadingNonzero,
      RFAP.ComputablePolynomial.DensePolynomial.mul_ne_zero_direct]
    exact add_comm _ _
  · unfold isZero directionScaled normalize
    simp [directionNonzero, leadingNonzero,
      RFAP.ComputablePolynomial.DensePolynomial.mul_ne_zero_direct]

/-- Common affine direction of every outer horizontal quarter-cell. -/
def horizontalCellDirection : Gaussian := point (1 / 4) 0

/-- Symbolic quartic substitution along a horizontal quarter-cell. -/
def horizontalQuarticCache (origin : Gaussian) : HorizontalGaussianPolynomial :=
  ⟨[horizontalCellDirection ^ 4,
    4 * origin * horizontalCellDirection ^ 3,
    6 * origin ^ 2 * horizontalCellDirection ^ 2,
    4 * origin ^ 3 * horizontalCellDirection,
    origin ^ 4 - 1]⟩

private def horizontalStage1 (origin : Gaussian) :
    HorizontalGaussianPolynomial :=
  RFAP.PathPolynomial.mulLine origin horizontalCellDirection 0 +
    constant 1

private def horizontalStage2 (origin : Gaussian) :
    HorizontalGaussianPolynomial :=
  RFAP.PathPolynomial.mulLine origin horizontalCellDirection
      (horizontalStage1 origin) + constant 0

private def horizontalStage3 (origin : Gaussian) :
    HorizontalGaussianPolynomial :=
  RFAP.PathPolynomial.mulLine origin horizontalCellDirection
      (horizontalStage2 origin) + constant 0

private def horizontalStage4 (origin : Gaussian) :
    HorizontalGaussianPolynomial :=
  RFAP.PathPolynomial.mulLine origin horizontalCellDirection
      (horizontalStage3 origin) + constant 0

private theorem horizontalStage1_eq (origin : Gaussian) :
    horizontalStage1 origin = ⟨[1]⟩ := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  with_unfolding_all rfl

private theorem horizontalStage2_eq (origin : Gaussian)
    (originNonzero : origin ≠ 0) :
    horizontalStage2 origin = ⟨[horizontalCellDirection, origin]⟩ := by
  unfold horizontalStage2
  rw [horizontalStage1_eq, add_constant_zero, normalize_mulLine]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  rw [mulLine_one_coeff origin horizontalCellDirection 1 originNonzero
    (by with_unfolding_all decide) (by decide) ⟨[1]⟩ rfl]
  simp only [RFAP.ConstructiveGaussian.Gaussian.mul_one]

private theorem horizontalStage3_eq (origin : Gaussian)
    (originNonzero : origin ≠ 0) :
    horizontalStage3 origin = ⟨[horizontalCellDirection ^ 2,
      2 * origin * horizontalCellDirection, origin ^ 2]⟩ := by
  unfold horizontalStage3
  rw [horizontalStage2_eq origin originNonzero, add_constant_zero,
    normalize_mulLine]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  rw [mulLine_two_coeffs origin horizontalCellDirection horizontalCellDirection
    origin originNonzero (by with_unfolding_all decide)
      (by with_unfolding_all decide)
      ⟨[horizontalCellDirection, origin]⟩ rfl]
  simp only [List.cons.injEq]
  constructor
  · ring1
  · constructor
    · ring1
    · constructor
      · ring1
      · trivial

private theorem horizontalStage4_eq (origin : Gaussian)
    (originNonzero : origin ≠ 0) :
    horizontalStage4 origin = ⟨[horizontalCellDirection ^ 3,
      3 * origin * horizontalCellDirection ^ 2,
      3 * origin ^ 2 * horizontalCellDirection, origin ^ 3]⟩ := by
  unfold horizontalStage4
  rw [horizontalStage3_eq origin originNonzero, add_constant_zero,
    normalize_mulLine]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  rw [mulLine_three_coeffs origin horizontalCellDirection
    (horizontalCellDirection ^ 2) (2 * origin * horizontalCellDirection)
      (origin ^ 2) originNonzero (by with_unfolding_all decide)
      (RFAP.ConstructiveGaussian.Gaussian.pow_ne_zero_direct
        horizontalCellDirection (by with_unfolding_all decide) 2)
      ⟨[horizontalCellDirection ^ 2, 2 * origin * horizontalCellDirection,
        origin ^ 2]⟩ rfl]
  simp only [List.cons.injEq]
  constructor
  · ring1
  · constructor
    · ring1
    · constructor
      · ring1
      · constructor
        · ring1
        · trivial

/-- Exact symbolic coefficient cache for any nonzero horizontal cell start. -/
theorem horizontalQuarticCache_eq (origin : Gaussian)
    (originNonzero : origin ≠ 0) :
    RFAP.PathPolynomial.composeLine
        CCL.Riemann.FinitePeriodExamples.quarticPolynomial origin
          horizontalCellDirection = horizontalQuarticCache origin := by
  unfold RFAP.PathPolynomial.composeLine RFAP.PathPolynomial.composeLineCoeffs
  rw [quarticPolynomial_coeffs]
  change RFAP.PathPolynomial.mulLine origin horizontalCellDirection
      (horizontalStage4 origin) + constant (-1) = _
  rw [horizontalStage4_eq origin originNonzero]
  have mulEq :
      RFAP.PathPolynomial.mulLine origin horizontalCellDirection
          ⟨[horizontalCellDirection ^ 3,
            3 * origin * horizontalCellDirection ^ 2,
            3 * origin ^ 2 * horizontalCellDirection, origin ^ 3]⟩ =
        ⟨[horizontalCellDirection ^ 4,
          4 * origin * horizontalCellDirection ^ 3,
          6 * origin ^ 2 * horizontalCellDirection ^ 2,
          4 * origin ^ 3 * horizontalCellDirection, origin ^ 4]⟩ := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    rw [mulLine_four_coeffs origin horizontalCellDirection
      (horizontalCellDirection ^ 3)
        (3 * origin * horizontalCellDirection ^ 2)
        (3 * origin ^ 2 * horizontalCellDirection) (origin ^ 3)
        originNonzero (by with_unfolding_all decide)
        (RFAP.ConstructiveGaussian.Gaussian.pow_ne_zero_direct
          horizontalCellDirection (by with_unfolding_all decide) 3)
        ⟨[horizontalCellDirection ^ 3,
          3 * origin * horizontalCellDirection ^ 2,
          3 * origin ^ 2 * horizontalCellDirection, origin ^ 3]⟩ rfl]
    simp only [List.cons.injEq]
    constructor
    · ring1
    · constructor
      · ring1
      · constructor
        · ring1
        · constructor
          · ring1
          · constructor
            · ring1
            · trivial
  rw [mulEq, quartic_add_constant _ _ _ _ _
    (RFAP.ConstructiveGaussian.Gaussian.pow_ne_zero_direct
      horizontalCellDirection (by with_unfolding_all decide) 4)]
  unfold horizontalQuarticCache
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  rfl

/-- The dense-Horner slope for horizontal quarter-cells is monotone in the
squared norm of the cell's starting point. -/
theorem horizontalQuarticLipschitz_mono
    (origin target : Gaussian)
    (normLe : RFAP.ConstructiveGaussian.Gaussian.normSq origin ≤
      RFAP.ConstructiveGaussian.Gaussian.normSq target) :
    RFAP.PolynomialBounds.denseLipschitzBound
        (horizontalQuarticCache origin)
          CCL.Riemann.ClearSheetContinuation.parameterAmbient ≤
      RFAP.PolynomialBounds.denseLipschitzBound
        (horizontalQuarticCache target)
          CCL.Riemann.ClearSheetContinuation.parameterAmbient := by
  have normNonnegative :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg origin
  have squareLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq origin ^ 2 ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq target ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct normNonnegative normLe 2
  have cubeLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq origin ^ 3 ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq target ^ 3 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct normNonnegative normLe 3
  have secondLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (4 * origin * horizontalCellDirection ^ 3) ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (4 * target * horizontalCellDirection ^ 3) := by
    simp only [RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
      RFAP.ConstructiveGaussian.Gaussian.normSq_pow]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct normLe
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg 4))
      (RFAP.ConstructiveFraction.pow_nonneg_direct
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg
          horizontalCellDirection) 3)
  have thirdLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (6 * origin ^ 2 * horizontalCellDirection ^ 2) ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (6 * target ^ 2 * horizontalCellDirection ^ 2) := by
    simp only [RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
      RFAP.ConstructiveGaussian.Gaussian.normSq_pow]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareLe
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg 6))
      (RFAP.ConstructiveFraction.pow_nonneg_direct
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg
          horizontalCellDirection) 2)
  have fourthLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (4 * origin ^ 3 * horizontalCellDirection) ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (4 * target ^ 3 * horizontalCellDirection) := by
    simp only [RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
      RFAP.ConstructiveGaussian.Gaussian.normSq_pow]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct cubeLe
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg 4))
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg
        horizontalCellDirection)
  unfold horizontalQuarticCache
  rw [denseLipschitzBound_five_coeffs_parameterAmbient,
    denseLipschitzBound_five_coeffs_parameterAmbient]
  apply max_le_max le_rfl
  exact add_le_add
    (add_le_add
      (add_le_add le_rfl
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct secondLe
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 192) (by omega)).le))
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct thirdLe
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 32) (by omega)).le))
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct fourthLe
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 4) (by omega)).le)

/-! ## The third outer connector cell -/

/-- The third horizontal cell of the canonical quartic connector. -/
def thirdSegment := outerConnectorHead.restrict outerConnectorHeadWithin
  (2 / 8) (3 / 8) (by decide) (by decide)

theorem thirdWithin : thirdSegment.WithinAmbient :=
  outerConnectorHead.restrict_withinAmbient outerConnectorHeadWithin
    (2 / 8) (3 / 8) (by decide) (by decide)

theorem thirdSegment_start :
    thirdSegment.pointAt 0 = point (-3 / 4) (-1 / 2) := by
  with_unfolding_all decide

theorem thirdSegment_finish :
    thirdSegment.pointAt 1 = point (-1 / 2) (-1 / 2) := by
  with_unfolding_all decide

theorem thirdSegmentPolynomial_eq :
    CCL.Riemann.ClearSheetContinuation.segmentPolynomial thirdSegment =
      horizontalQuarticCache (point (-3 / 4) (-1 / 2)) := by
  unfold CCL.Riemann.ClearSheetContinuation.segmentPolynomial
  have startEq : outerConnectorHead.pointAt (2 / 8) =
      point (-3 / 4) (-1 / 2) := by
    with_unfolding_all decide
  have finishEq : outerConnectorHead.pointAt (3 / 8) =
      point (-1 / 2) (-1 / 2) := by
    with_unfolding_all decide
  rw [startEq, finishEq]
  have directionEq :
      point (-1 / 2) (-1 / 2) - point (-3 / 4) (-1 / 2) =
        horizontalCellDirection := by
    with_unfolding_all decide
  rw [directionEq]
  exact horizontalQuarticCache_eq (point (-3 / 4) (-1 / 2))
    (by with_unfolding_all decide)

private theorem secondSegmentPolynomial_horizontalCache :
    CCL.Riemann.ClearSheetContinuation.segmentPolynomial secondSegment =
      horizontalQuarticCache (point (-1) (-1 / 2)) := by
  unfold CCL.Riemann.ClearSheetContinuation.segmentPolynomial
  have startEq : outerConnectorHead.pointAt (1 / 8) =
      point (-1) (-1 / 2) := by
    with_unfolding_all decide
  have finishEq : outerConnectorHead.pointAt (2 / 8) =
      point (-3 / 4) (-1 / 2) := by
    with_unfolding_all decide
  unfold outerConnectorHead at startEq finishEq
  rw [startEq, finishEq]
  have directionEq :
      point (-3 / 4) (-1 / 2) - point (-1) (-1 / 2) =
        horizontalCellDirection := by
    with_unfolding_all decide
  rw [directionEq]
  exact horizontalQuarticCache_eq (point (-1) (-1 / 2))
    (by with_unfolding_all decide)

/-- The third cell inherits the exact second-cell dense-Horner slope bound.
This is the first production use of the symbolic horizontal-cell cache. -/
theorem thirdDenseLipschitzLe :
    RFAP.PolynomialBounds.denseLipschitzBound
        (CCL.Riemann.ClearSheetContinuation.segmentPolynomial thirdSegment)
          CCL.Riemann.ClearSheetContinuation.parameterAmbient ≤
      (1011 / 64 : Q) := by
  rw [thirdSegmentPolynomial_eq, ← secondDenseLipschitzEq,
    secondSegmentPolynomial_horizontalCache]
  apply horizontalQuarticLipschitz_mono
  unfold RFAP.ConstructiveGaussian.Gaussian.normSq
  with_unfolding_all decide

/-- Every retained inner edge of the third cell has no more variation than
the corresponding second-cell edge. -/
theorem thirdMeshVariationLeSecond (edge : Fin 8) :
    CCL.Riemann.ClearSheetContinuation.variationBound thirdSegment
      (secondMeshEndpoint (secondEdgeSource edge)).parameter
        (secondEdgeRequest edge).endpoint.parameter ≤
      CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
        (secondMeshEndpoint (secondEdgeSource edge)).parameter
          (secondEdgeRequest edge).endpoint.parameter := by
  rw [CCL.Riemann.ClearSheetContinuation.variationBound_eq_denseLipschitz,
    CCL.Riemann.ClearSheetContinuation.variationBound_eq_denseLipschitz,
    secondDenseLipschitzEq]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    thirdDenseLipschitzLe
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)

theorem thirdMeshVariationLtQuarter (edge : Fin 8) :
    CCL.Riemann.ClearSheetContinuation.variationBound thirdSegment
      (secondMeshEndpoint (secondEdgeSource edge)).parameter
        (secondEdgeRequest edge).endpoint.parameter < (1 / 4 : Q) := by
  apply (thirdMeshVariationLeSecond edge).trans_lt
  rw [secondMeshVariationEq edge, ← secondVariationEq]
  exact secondVariationLtQuarter

end CCL.Riemann.ExplicitQuarticBranches
