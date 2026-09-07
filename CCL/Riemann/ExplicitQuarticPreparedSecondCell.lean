import CCL.Riemann.ExplicitQuarticPreparedCertificates

/-!
# The second prepared cell of the explicit quartic connector

This module restricts the canonical horizontal connector to its second outer
cell and caches its affine quartic coefficients.  Small unit-scaled rational
calculations certify the exact dense-Horner variation, the dyadic preparation
radius, a segment-specific linearization lower bound, and the first retained
eighth-unit transport floor without increasing Lean's elaboration limits.
-/

namespace CCL.Riemann.ExplicitQuarticBranches

@[simp] private theorem pointReal (x y : Q) : (point x y).re = x := rfl

@[simp] private theorem pointImaginary (x y : Q) : (point x y).im = y := rfl

private theorem qNatPositive (n : Nat) (positive : 0 < n) :
    (0 : Q) < n :=
  RFAP.ConstructiveFraction.natCast_pos_direct positive

private def unit : Q := 1 / 256

private theorem scaledUnit (numerator scale : Int) (denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (cross : (numerator : Q) * 256 = (scale : Q) * denominator) :
    (numerator : Q) / denominator = (scale : Q) * unit := by
  unfold unit
  calc
    (numerator : Q) / denominator = (scale : Q) / 256 :=
      RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
        (qNatPositive denominator denominatorPositive).ne'
        (qNatPositive 256 (by decide)).ne' cross
    _ = (scale : Q) * (1 / 256) := by
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.one_mul]

private theorem unit_eq_scaled_square : unit = 256 * unit ^ 2 := by
  unfold unit
  rw [pow_two]
  calc
    (1 / 256 : Q) = 1 * (1 / 256) := by ring1
    _ = ((1 / 256 : Q) * 256) * (1 / 256) :=
      congrArg (fun value : Q => value * (1 / 256))
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          (qNatPositive 256 (by decide)).ne').symm
    _ = 256 * ((1 / 256 : Q) * (1 / 256)) := by ring1

private theorem unitSquare : unit ^ 2 = (1 / 65536 : Q) := by
  unfold unit
  rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct, one_mul]
  rw [show (256 : Q) * 256 = 65536 by ring1]

private theorem negativeDiv (numerator denominator : Q) :
    (-numerator) / denominator = -(numerator / denominator) := by
  simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  ring1

private theorem oneQuarterUnit : (1 / 4 : Q) = 64 * unit :=
  scaledUnit 1 64 4 (by decide) (by ring1)
private theorem oneSixteenthUnit : (1 / 16 : Q) = 16 * unit :=
  scaledUnit 1 16 16 (by decide) (by ring1)
private theorem oneHalfUnit : (1 / 2 : Q) = 128 * unit :=
  scaledUnit 1 128 2 (by decide) (by ring1)
private theorem negativeOneHalfUnit : (-1 / 2 : Q) = -128 * unit := by
  rw [negativeDiv, oneHalfUnit]
  ring1
private theorem negativeOneQuarterUnit : (-1 / 4 : Q) = -64 * unit := by
  rw [negativeDiv, oneQuarterUnit]
  ring1
private theorem threeQuarterUnit : (3 / 4 : Q) = 192 * unit :=
  scaledUnit 3 192 4 (by decide) (by ring1)
private theorem oneUnit : (1 : Q) = 256 * unit := by
  unfold unit
  calc
    (1 : Q) = (1 / 256 : Q) * 256 :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        (qNatPositive 256 (by decide)).ne').symm
    _ = 256 * (1 / 256 : Q) := by ring1
private theorem negativeOneUnit : (-1 : Q) = -256 * unit := by
  rw [show (-1 : Q) = -(1 : Q) by ring1, oneUnit]
  ring1
private theorem oneSixtyFourUnit : (1 / 64 : Q) = 4 * unit :=
  scaledUnit 1 4 64 (by decide) (by ring1)
private theorem oneSixtyFourPositive : (0 : Q) < 1 / 64 :=
  RFAP.ConstructiveFraction.div_pos_direct
    (qNatPositive 1 (by decide)) (qNatPositive 64 (by decide))

private theorem halfPow_antitone {m n : Nat} (order : m ≤ n) :
    (1 / 2 : Q) ^ n ≤ (1 / 2 : Q) ^ m := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [pow_add]
  have halfNonnegative : (0 : Q) ≤ 1 / 2 :=
    RFAP.ConstructiveFraction.div_nonneg_direct
      (show (0 : Q) ≤ 1 by decide) (qNatPositive 2 (by decide)).le
  have halfLeOne : (1 / 2 : Q) ≤ 1 := by decide
  have extraLeOne : (1 / 2 : Q) ^ extra ≤ 1 := by
    simpa only [one_pow] using
      RFAP.ConstructiveFraction.pow_le_pow_direct halfNonnegative halfLeOne extra
  calc
    (1 / 2 : Q) ^ m * (1 / 2) ^ extra ≤ (1 / 2) ^ m * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct extraLeOne
        (RFAP.ConstructiveFraction.pow_nonneg_direct halfNonnegative m)
    _ = (1 / 2 : Q) ^ m := by ring1

private theorem halfSquare : (1 / 2 : Q) ^ 2 = 1 / 4 := by
  rw [pow_two, oneHalfUnit, oneQuarterUnit]
  conv_rhs => rw [unit_eq_scaled_square]
  ring1

private theorem halfPowFour : (1 / 2 : Q) ^ 4 = 1 / 16 := by
  rw [show (1 / 2 : Q) ^ 4 = ((1 / 2 : Q) ^ 2) ^ 2 by ring1,
    halfSquare, pow_two, oneQuarterUnit, oneSixteenthUnit]
  conv_rhs => rw [unit_eq_scaled_square]
  ring1

private theorem halfPowFive : (1 / 2 : Q) ^ 5 = 1 / 32 := by
  have thirtySecondUnit : (1 / 32 : Q) = 8 * unit :=
    scaledUnit 1 8 32 (by decide) (by ring1)
  rw [show (1 / 2 : Q) ^ 5 = (1 / 2 : Q) ^ 4 * (1 / 2) by ring1,
    halfPowFour, oneSixteenthUnit, oneHalfUnit, thirtySecondUnit]
  conv_rhs => rw [unit_eq_scaled_square]
  ring1

private theorem halfPowSix : (1 / 2 : Q) ^ 6 = 1 / 64 := by
  have thirtySecondUnit : (1 / 32 : Q) = 8 * unit :=
    scaledUnit 1 8 32 (by decide) (by ring1)
  rw [show (1 / 2 : Q) ^ 6 = (1 / 2 : Q) ^ 5 * (1 / 2) by ring1,
    halfPowFive, thirtySecondUnit, oneHalfUnit, oneSixtyFourUnit]
  conv_rhs => rw [unit_eq_scaled_square]
  ring1

private theorem oneOver1024_eq_sixtyFourUnitSquare :
    (1 / 1024 : Q) = 64 * unit ^ 2 := by
  rw [unitSquare]
  calc
    (1 / 1024 : Q) = 64 / 65536 := by
      apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
        (qNatPositive 1024 (by omega)).ne'
        (qNatPositive 65536 (by omega)).ne'
      ring1
    _ = 64 * (1 / 65536 : Q) := by
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.one_mul]

private theorem dyadicSquareRadius_le_oneSixtyFour
    {target : Q} (targetPositive : 0 < target)
    (targetUpper : target ≤ (1 / 2304 : Q)) :
    CCL.FiniteGeometric.dyadicSquareRadius target ≤ (1 / 64 : Q) := by
  let exponent := CCL.FiniteGeometric.firstQuarterBelow 1 0 target
  have radiusEq : CCL.FiniteGeometric.dyadicSquareRadius target =
      (1 / 2 : Q) ^ exponent := rfl
  have squareLt : ((1 / 2 : Q) ^ exponent) ^ 2 < target := by
    rw [← radiusEq]
    exact CCL.FiniteGeometric.dyadicSquareRadius_sq_lt targetPositive
  have sixLe : 6 ≤ exponent := by
    by_cases order : 6 ≤ exponent
    · exact order
    · have exponentLe : exponent ≤ 5 := by omega
      have fifthLe := halfPow_antitone exponentLe
      have fifthNonnegative : (0 : Q) ≤ (1 / 2 : Q) ^ 5 :=
        RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) 5
      have fifthSquareLe : ((1 / 2 : Q) ^ 5) ^ 2 ≤
          ((1 / 2 : Q) ^ exponent) ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct fifthNonnegative fifthLe 2
      have oneOver1024Le : (1 / 1024 : Q) ≤
          ((1 / 2 : Q) ^ exponent) ^ 2 := by
        calc
          (1 / 1024 : Q) = ((1 / 2 : Q) ^ 5) ^ 2 := by
            have thirtySecondUnit : (1 / 32 : Q) = 8 * unit :=
              scaledUnit 1 8 32 (by decide) (by ring1)
            rw [halfPowFive, oneOver1024_eq_sixtyFourUnitSquare,
              thirtySecondUnit, pow_two]
            ring1
          _ ≤ ((1 / 2 : Q) ^ exponent) ^ 2 := fifthSquareLe
      have squareUpper : ((1 / 2 : Q) ^ exponent) ^ 2 ≤ 1 / 2304 :=
        squareLt.le.trans targetUpper
      have strictConstant : (1 / 2304 : Q) < 1 / 1024 := by
        have productPositive : (0 : Q) < 2304 * 1024 :=
          RFAP.ConstructiveFraction.mul_pos_direct
            (qNatPositive 2304 (by omega)) (qNatPositive 1024 (by omega))
        apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
          (c := (2304 : Q) * 1024) _ productPositive
        calc
          (1 / 2304 : Q) * (2304 * 1024) = 1024 := by
            rw [show (1 / 2304 : Q) * (2304 * 1024) =
              ((1 / 2304 : Q) * 2304) * 1024 by ring1]
            have cancel2304 : (1 / 2304 : Q) * 2304 = 1 :=
              RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
                (qNatPositive 2304 (by omega)).ne'
            rw [cancel2304]
            ring1
          _ < 2304 := RFAP.ConstructiveFraction.natCast_lt_direct
            (m := 1024) (n := 2304) (by omega)
          _ = (1 / 1024 : Q) * (2304 * 1024) := by
            rw [show (1 / 1024 : Q) * (2304 * 1024) =
              2304 * ((1 / 1024 : Q) * 1024) by ring1]
            have cancel1024 : (1 / 1024 : Q) * 1024 = 1 :=
              RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
                (qNatPositive 1024 (by omega)).ne'
            rw [cancel1024]
            ring1
      have impossible : (1 / 1024 : Q) < 1 / 1024 := by
        calc
          (1 / 1024 : Q) ≤ ((1 / 2 : Q) ^ exponent) ^ 2 :=
            oneOver1024Le
          _ ≤ 1 / 2304 := squareUpper
          _ < 1 / 1024 := strictConstant
      exact (lt_irrefl _ impossible).elim
  calc
    CCL.FiniteGeometric.dyadicSquareRadius target =
        (1 / 2 : Q) ^ exponent := radiusEq
    _ ≤ (1 / 2 : Q) ^ 6 := halfPow_antitone sixLe
    _ = (1 / 64 : Q) := halfPowSix
private theorem threeSixteenthUnit : (3 / 16 : Q) = 48 * unit :=
  scaledUnit 3 48 16 (by decide) (by ring1)
private theorem negativeThreeSixteenthUnit : (-3 / 16 : Q) = -48 * unit := by
  rw [negativeDiv, threeSixteenthUnit]
  ring1
private theorem threeThirtySecondUnit : (3 / 32 : Q) = 24 * unit :=
  scaledUnit 3 24 32 (by decide) (by ring1)
private theorem negativeThreeThirtySecondUnit : (-3 / 32 : Q) =
    -24 * unit := by
  rw [negativeDiv, threeThirtySecondUnit]
  ring1
private theorem nineSixteenthUnit : (9 / 16 : Q) = 144 * unit :=
  scaledUnit 9 144 16 (by decide) (by ring1)
private theorem elevenEighthUnit : (11 / 8 : Q) = 352 * unit :=
  scaledUnit 11 352 8 (by decide) (by ring1)
private theorem negativeElevenEighthUnit : (-11 / 8 : Q) = -352 * unit := by
  rw [negativeDiv, elevenEighthUnit]
  ring1
private theorem oneTwoFiftySixthUnit : (1 / 256 : Q) = unit := rfl
private theorem oneThirtySecondUnit : (1 / 32 : Q) = 8 * unit :=
  scaledUnit 1 8 32 (by decide) (by ring1)
private theorem negativeOneSixteenthUnit : (-1 / 16 : Q) = -16 * unit := by
  rw [negativeDiv, oneSixteenthUnit]
  ring1
private theorem negativeOneThirtySecondUnit : (-1 / 32 : Q) =
    -8 * unit := by
  rw [negativeDiv, oneThirtySecondUnit]
  ring1
private theorem nineThirtySecondUnit : (9 / 32 : Q) = 72 * unit :=
  scaledUnit 9 72 32 (by decide) (by ring1)
private theorem threeEighthUnit : (3 / 8 : Q) = 96 * unit :=
  scaledUnit 3 96 8 (by decide) (by ring1)
private theorem twentyThreeSixteenthUnit : (23 / 16 : Q) = 368 * unit :=
  scaledUnit 23 368 16 (by decide) (by ring1)
private theorem negativeTwentyThreeSixteenthUnit : (-23 / 16 : Q) =
    -368 * unit := by
  rw [negativeDiv, twentyThreeSixteenthUnit]
  ring1
private theorem threeHalfUnit : (3 / 2 : Q) = 384 * unit :=
  scaledUnit 3 384 2 (by decide) (by ring1)

private theorem secondStartNormEqUnit :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (-23 / 16) (3 / 2)) = 1105 * unit := by
  unfold RFAP.ConstructiveGaussian.Gaussian.normSq
  simp only [pointReal, pointImaginary]
  rw [negativeTwentyThreeSixteenthUnit, threeHalfUnit]
  conv_rhs => rw [unit_eq_scaled_square]
  ring1

private theorem secondStartNormLower : (15 / 4 : Q) ≤
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (-23 / 16) (3 / 2)) := by
  have unitNonnegative : (0 : Q) ≤ unit :=
    (RFAP.ConstructiveFraction.div_pos_direct
      (qNatPositive 1 (by omega)) (qNatPositive 256 (by omega))).le
  have fifteenQuarterUnit : (15 / 4 : Q) = 960 * unit :=
    scaledUnit 15 960 4 (by omega) (by ring1)
  rw [secondStartNormEqUnit, fifteenQuarterUnit]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    (RFAP.ConstructiveFraction.natCast_le_direct
      (m := 960) (n := 1105) (by omega)) unitNonnegative

private theorem point_ne_zero_of_re_ne {x y : Q} (realNonzero : x ≠ 0) :
    point x y ≠ 0 := by
  intro equality
  have realEquality := congrArg RFAP.ConstructiveGaussian.Gaussian.re equality
  exact realNonzero realEquality

private structure HeadData
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box}
    {start finish : RFAP.ConstructiveGaussian.Gaussian}
    (path : CCL.Riemann.BranchCuts.ClearPath polynomial ambient start finish) where
  middle : RFAP.ConstructiveGaussian.Gaussian
  head : CCL.Riemann.BranchCuts.ClearSegment polynomial ambient start middle
  tail : CCL.Riemann.BranchCuts.ClearPath polynomial ambient middle finish
  path_eq : path = .cons head tail

private def headData : HeadData (rawConnector 0 1) := by
  unfold rawConnector CCL.Riemann.BranchCuts.finiteConnectorAt
  exact ⟨_, _, _, rfl⟩

private theorem headWithin : headData.head.WithinAmbient := by
  have within := rawConnector_withinAmbient 0 1
  rw [headData.path_eq] at within
  exact within.head

/-- The horizontal head of the canonical outer connector, exposed once so
later restricted cells can share its finite clearance data without rebuilding
the private path decomposition. -/
def outerConnectorHead := headData.head

theorem outerConnectorHeadWithin : outerConnectorHead.WithinAmbient :=
  headWithin

def secondSegment := headData.head.restrict headWithin (1 / 8) (2 / 8)
  (by decide) (by decide)

theorem secondWithin : secondSegment.WithinAmbient :=
  headData.head.restrict_withinAmbient headWithin (1 / 8) (2 / 8)
    (by decide) (by decide)

def endpoint0 : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint :=
  CCL.Riemann.PreparedClearPathModels.zeroEndpoint

def endpoint1 : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint :=
  ⟨1 / 8, by decide⟩

def request0 : CCL.Riemann.PreparedSheetContinuation.StepRequest :=
  { endpoint := endpoint1
    rootDiameter := workingRootDiameter
    rootDiameterPositive := workingRootDiameter_positive }

private theorem secondStartEq : headData.head.pointAt (1 / 8) =
    point (-1) (-1 / 2) := by
  with_unfolding_all decide

theorem secondSegment_pointAt_zero :
    secondSegment.pointAt 0 = point (-1) (-1 / 2) := by
  rw [CCL.Riemann.BranchCuts.ClearSegment.pointAt_zero]
  exact secondStartEq

private theorem secondFinishEq : headData.head.pointAt (2 / 8) =
    point (-3 / 4) (-1 / 2) := by
  with_unfolding_all decide

/-- Affine coordinate formula for the second connector cell. -/
theorem secondSegment_pointAt (parameter : Q) :
    secondSegment.pointAt parameter =
      point ((-1) + parameter * ((-3 / 4) - (-1)))
        ((-1 / 2) + parameter * ((-1 / 2) - (-1 / 2))) := by
  change headData.head.pointAt (1 / 8) +
    CCL.FiniteExp.scale parameter
      (headData.head.pointAt (2 / 8) - headData.head.pointAt (1 / 8)) = _
  rw [secondStartEq, secondFinishEq]
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      CCL.FiniteExp.scale_re, pointReal]
  · simp only [
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      CCL.FiniteExp.scale_im, pointImaginary]

private def explicitSecond : CCL.Riemann.BranchCuts.ClearSegment
    CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial
      (CCL.Riemann.BranchCuts.Ambient
        CCL.Riemann.FinitePeriodExamples.quarticCurve)
      (point (-1) (-1 / 2)) (point (-3 / 4) (-1 / 2)) :=
  (secondSegment.castStart secondStartEq).castFinish secondFinishEq

private def secondPolynomialCache :
    RFAP.ConstructivePolynomial.GaussianPolynomial :=
  ⟨[point (1 / 256) 0, point (-1 / 16) (-1 / 32),
    point (9 / 32) (3 / 8), point (-1 / 4) (-11 / 8),
    point (-23 / 16) (3 / 2)]⟩

private def secondOrigin : RFAP.ConstructiveGaussian.Gaussian :=
  point (-1) (-1 / 2)

private def secondDirection : RFAP.ConstructiveGaussian.Gaussian :=
  point (1 / 4) 0

private def secondStage1 :=
  RFAP.PathPolynomial.mulLine secondOrigin secondDirection 0 +
    RFAP.ComputablePolynomial.DensePolynomial.constant
      (1 : RFAP.ConstructiveGaussian.Gaussian)

private def secondStage2 :=
  RFAP.PathPolynomial.mulLine secondOrigin secondDirection secondStage1 +
    RFAP.ComputablePolynomial.DensePolynomial.constant
      (0 : RFAP.ConstructiveGaussian.Gaussian)

private def secondStage3 :=
  RFAP.PathPolynomial.mulLine secondOrigin secondDirection secondStage2 +
    RFAP.ComputablePolynomial.DensePolynomial.constant
      (0 : RFAP.ConstructiveGaussian.Gaussian)

private def secondStage4 :=
  RFAP.PathPolynomial.mulLine secondOrigin secondDirection secondStage3 +
    RFAP.ComputablePolynomial.DensePolynomial.constant
      (0 : RFAP.ConstructiveGaussian.Gaussian)

private def secondStage5 :=
  RFAP.PathPolynomial.mulLine secondOrigin secondDirection secondStage4 +
    RFAP.ComputablePolynomial.DensePolynomial.constant
      (-1 : RFAP.ConstructiveGaussian.Gaussian)

private def secondCache1 : RFAP.ConstructivePolynomial.GaussianPolynomial :=
  ⟨[point 1 0]⟩

private def secondCache2 : RFAP.ConstructivePolynomial.GaussianPolynomial :=
  ⟨[point (1 / 4) 0, point (-1) (-1 / 2)]⟩

private def secondCache3 : RFAP.ConstructivePolynomial.GaussianPolynomial :=
  ⟨[point (1 / 16) 0, point (-1 / 2) (-1 / 4),
    point (3 / 4) 1]⟩

private def secondCache4 : RFAP.ConstructivePolynomial.GaussianPolynomial :=
  ⟨[point (1 / 64) 0, point (-3 / 16) (-3 / 32),
    point (9 / 16) (3 / 4), point (-1 / 4) (-11 / 8)]⟩

private theorem secondTrailingEq :
    secondOrigin * point (-1 / 4) (-11 / 8) +
        (-1 : RFAP.ConstructiveGaussian.Gaussian) =
      point (-23 / 16) (3 / 2) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · simp only [secondOrigin,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.neg_re,
      pointReal, pointImaginary]
    rw [negativeOneQuarterUnit, negativeOneHalfUnit,
      negativeElevenEighthUnit, negativeTwentyThreeSixteenthUnit,
      negativeOneUnit]
    calc
      (-256 * unit) * (-64 * unit) -
          (-128 * unit) * (-352 * unit) + -256 * unit =
        (-112) * (256 * unit ^ 2) + -256 * unit := by ring1
      _ = (-112) * unit + -256 * unit := by
        rw [← unit_eq_scaled_square]
      _ = -368 * unit := by ring1
  · simp only [secondOrigin,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.one_im,
      RFAP.ConstructiveGaussian.Gaussian.neg_im,
      pointReal, pointImaginary]
    rw [negativeElevenEighthUnit, negativeOneHalfUnit,
      negativeOneQuarterUnit, threeHalfUnit, negativeOneUnit]
    calc
      (-256 * unit) * (-352 * unit) +
          (-128 * unit) * (-64 * unit) + 0 =
        384 * (256 * unit ^ 2) := by ring1
      _ = 384 * unit := by rw [← unit_eq_scaled_square]

private theorem secondStage1Eq : secondStage1 = secondCache1 := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  with_unfolding_all decide

private theorem secondStage2Eq : secondStage2 = secondCache2 := by
  unfold secondStage2
  rw [secondStage1Eq]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  with_unfolding_all decide

private theorem secondStage3Eq : secondStage3 = secondCache3 := by
  unfold secondStage3
  rw [secondStage2Eq]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  with_unfolding_all decide

private theorem secondStage4Eq : secondStage4 = secondCache4 := by
  unfold secondStage4
  rw [secondStage3Eq]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  rw [RFAP.ComputablePolynomial.DensePolynomial.add_constant_zero,
    normalize_mulLine]
  rw [mulLine_three_coeffs secondOrigin secondDirection
    (point (1 / 16) 0) (point (-1 / 2) (-1 / 4))
      (point (3 / 4) 1) (by with_unfolding_all decide)
        (by with_unfolding_all decide) (by with_unfolding_all decide)
          secondCache3 rfl]
  simp only [secondDirection, secondOrigin, secondCache4,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals apply RFAP.ConstructiveGaussian.Gaussian.ext
  all_goals simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.add_im, pointReal, pointImaginary]
  all_goals try rw [negativeOneHalfUnit]
  all_goals try rw [negativeOneQuarterUnit]
  all_goals try rw [negativeOneUnit]
  all_goals try rw [negativeThreeSixteenthUnit]
  all_goals try rw [negativeThreeThirtySecondUnit]
  all_goals try rw [negativeElevenEighthUnit]
  all_goals try rw [oneQuarterUnit]
  all_goals try rw [oneSixteenthUnit]
  all_goals try rw [threeQuarterUnit]
  all_goals try rw [oneSixtyFourUnit]
  all_goals try rw [nineSixteenthUnit]
  all_goals try rw [oneUnit]
  all_goals try (conv_rhs => rw [unit_eq_scaled_square])
  all_goals ring1

private theorem secondStage5Eq : secondStage5 = secondPolynomialCache := by
  unfold secondStage5
  rw [secondStage4Eq]
  have multiplied : RFAP.PathPolynomial.mulLine secondOrigin secondDirection
      secondCache4 =
        ⟨[secondDirection * point (1 / 64) 0,
          secondDirection * point (-3 / 16) (-3 / 32) +
            secondOrigin * point (1 / 64) 0,
          secondDirection * point (9 / 16) (3 / 4) +
            secondOrigin * point (-3 / 16) (-3 / 32),
          secondDirection * point (-1 / 4) (-11 / 8) +
            secondOrigin * point (9 / 16) (3 / 4),
          secondOrigin * point (-1 / 4) (-11 / 8)]⟩ := by
    have directionNonzero : secondDirection ≠ 0 :=
      point_ne_zero_of_re_ne (by decide)
    have originNonzero : secondOrigin ≠ 0 :=
      point_ne_zero_of_re_ne (by decide)
    have cacheLeadingNonzero : point (1 / 64) 0 ≠ 0 :=
      point_ne_zero_of_re_ne oneSixtyFourPositive.ne'
    have leadingNonzero : secondDirection * point (1 / 64) 0 ≠ 0 :=
      RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
        directionNonzero cacheLeadingNonzero
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    exact mulLine_four_coeffs secondOrigin secondDirection
      (point (1 / 64) 0) (point (-3 / 16) (-3 / 32))
          (point (9 / 16) (3 / 4)) (point (-1 / 4) (-11 / 8))
          originNonzero directionNonzero cacheLeadingNonzero secondCache4 rfl
  have finalLeadingNonzero :
      secondDirection * point (1 / 64) 0 ≠ 0 :=
    RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      (point_ne_zero_of_re_ne (by decide))
      (point_ne_zero_of_re_ne oneSixtyFourPositive.ne')
  rw [multiplied, quartic_add_constant
    (secondDirection * point (-3 / 16) (-3 / 32) +
      secondOrigin * point (1 / 64) 0)
    (secondDirection * point (9 / 16) (3 / 4) +
      secondOrigin * point (-3 / 16) (-3 / 32))
    (secondDirection * point (-1 / 4) (-11 / 8) +
      secondOrigin * point (9 / 16) (3 / 4))
    (secondOrigin * point (-1 / 4) (-11 / 8))
    (-1 : RFAP.ConstructiveGaussian.Gaussian)
    finalLeadingNonzero]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp only [secondDirection, secondOrigin, secondPolynomialCache,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, secondTrailingEq⟩
  all_goals apply RFAP.ConstructiveGaussian.Gaussian.ext
  all_goals simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.add_im,
    pointReal, pointImaginary]
  all_goals try rw [negativeOneQuarterUnit]
  all_goals try rw [negativeOneHalfUnit]
  all_goals try rw [negativeThreeSixteenthUnit]
  all_goals try rw [negativeThreeThirtySecondUnit]
  all_goals try rw [negativeElevenEighthUnit]
  all_goals try rw [negativeOneSixteenthUnit]
  all_goals try rw [negativeOneThirtySecondUnit]
  all_goals try rw [negativeOneUnit]
  all_goals try rw [oneQuarterUnit]
  all_goals try rw [oneSixtyFourUnit]
  all_goals try rw [nineSixteenthUnit]
  all_goals try rw [threeQuarterUnit]
  all_goals try rw [nineThirtySecondUnit]
  all_goals try rw [threeEighthUnit]
  all_goals try rw [oneTwoFiftySixthUnit]
  all_goals try (conv_rhs => rw [unit_eq_scaled_square])
  all_goals ring1

private theorem secondPolynomialEq :
    CCL.Riemann.ClearSheetContinuation.segmentPolynomial explicitSecond =
      secondPolynomialCache := by
  unfold CCL.Riemann.ClearSheetContinuation.segmentPolynomial
  rw [show point (-3 / 4) (-1 / 2) - point (-1) (-1 / 2) =
      secondDirection by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      with_unfolding_all decide]
  change RFAP.PathPolynomial.composeLine
      CCL.Riemann.FinitePeriodExamples.quarticPolynomial secondOrigin
        secondDirection = secondPolynomialCache
  unfold RFAP.PathPolynomial.composeLine
    RFAP.PathPolynomial.composeLineCoeffs
  rw [quarticPolynomial_coeffs]
  change secondStage5 = secondPolynomialCache
  exact secondStage5Eq

/-- The dense-Horner slope of the second cell, cached independently of any
particular mesh edge so later cells can compare their smaller coefficient
norms without repeating this finite scan. -/
theorem secondDenseLipschitzEq :
    RFAP.PolynomialBounds.denseLipschitzBound
        (CCL.Riemann.ClearSheetContinuation.segmentPolynomial secondSegment)
          CCL.Riemann.ClearSheetContinuation.parameterAmbient =
      (1011 / 64 : Q) := by
  have castEq :
      CCL.Riemann.ClearSheetContinuation.segmentPolynomial secondSegment =
        CCL.Riemann.ClearSheetContinuation.segmentPolynomial explicitSecond := by
    unfold explicitSecond
    cases secondStartEq
    cases secondFinishEq
    rfl
  rw [castEq, secondPolynomialEq]
  unfold secondPolynomialCache
  rw [denseLipschitzBound_five_coeffs_parameterAmbient]
  have norm1 : RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (1 / 256) 0) = unit ^ 2 := by
    unfold RFAP.ConstructiveGaussian.Gaussian.normSq
    simp only [pointReal, pointImaginary]
    rw [oneTwoFiftySixthUnit]
    ring1
  have norm2 : RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (-1 / 16) (-1 / 32)) = 320 * unit ^ 2 := by
    unfold RFAP.ConstructiveGaussian.Gaussian.normSq
    simp only [pointReal, pointImaginary]
    rw [negativeOneSixteenthUnit, negativeOneThirtySecondUnit]
    ring1
  have norm3 : RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (9 / 32) (3 / 8)) = 14400 * unit ^ 2 := by
    unfold RFAP.ConstructiveGaussian.Gaussian.normSq
    simp only [pointReal, pointImaginary]
    rw [nineThirtySecondUnit, threeEighthUnit]
    ring1
  have norm4 : RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (-1 / 4) (-11 / 8)) = 128000 * unit ^ 2 := by
    unfold RFAP.ConstructiveGaussian.Gaussian.normSq
    simp only [pointReal, pointImaginary]
    rw [negativeOneQuarterUnit, negativeElevenEighthUnit]
    ring1
  rw [norm1, norm2, norm3, norm4]
  rw [show 1024 * unit ^ 2 + 192 * (320 * unit ^ 2) +
      32 * (14400 * unit ^ 2) + 4 * (128000 * unit ^ 2) =
        1035264 * unit ^ 2 by ring1]
  have slopeEq : 1035264 * unit ^ 2 = (1011 / 64 : Q) := by
    rw [unitSquare]
    calc
      1035264 * (1 / 65536 : Q) = 1035264 / 65536 := by
        simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
          RFAP.ConstructiveFraction.one_mul]
      _ = 1011 / 64 := by
        apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
          (qNatPositive 65536 (by omega)).ne'
          (qNatPositive 64 (by omega)).ne'
        ring1
  have slopeLower : (1 : Q) ≤ 1035264 * unit ^ 2 := by
    rw [slopeEq]
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := (64 : Q)) _ (qNatPositive 64 (by omega))
    have cancel : (1011 / 64 : Q) * 64 = 1011 :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        (qNatPositive 64 (by omega)).ne'
    calc
      (1 : Q) * 64 = 64 := by ring1
      _ ≤ 1011 := RFAP.ConstructiveFraction.natCast_le_direct
        (m := 64) (n := 1011) (by omega)
      _ = (1011 / 64 : Q) * 64 := cancel.symm
  rw [max_eq_right slopeLower, slopeEq]

/-- Exact squared-variation cache for the first local dyadic edge of the
second outer connector cell. -/
theorem secondVariationEq :
    CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
      endpoint0.parameter endpoint1.parameter = (1011 / 4096 : Q) := by
  have castEq :
      CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
          endpoint0.parameter endpoint1.parameter =
        CCL.Riemann.ClearSheetContinuation.variationBound explicitSecond
          endpoint0.parameter endpoint1.parameter := by
    unfold explicitSecond
    cases secondStartEq
    cases secondFinishEq
    rfl
  rw [castEq,
    CCL.Riemann.ClearSheetContinuation.variationBound_eq_denseLipschitz,
      secondPolynomialEq]
  unfold secondPolynomialCache
  rw [denseLipschitzBound_five_coeffs_parameterAmbient]
  have norm1 : RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (1 / 256) 0) = unit ^ 2 := by
    unfold RFAP.ConstructiveGaussian.Gaussian.normSq
    simp only [pointReal, pointImaginary]
    rw [oneTwoFiftySixthUnit]
    ring1
  have norm2 : RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (-1 / 16) (-1 / 32)) = 320 * unit ^ 2 := by
    unfold RFAP.ConstructiveGaussian.Gaussian.normSq
    simp only [pointReal, pointImaginary]
    rw [negativeOneSixteenthUnit, negativeOneThirtySecondUnit]
    ring1
  have norm3 : RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (9 / 32) (3 / 8)) = 14400 * unit ^ 2 := by
    unfold RFAP.ConstructiveGaussian.Gaussian.normSq
    simp only [pointReal, pointImaginary]
    rw [nineThirtySecondUnit, threeEighthUnit]
    ring1
  have norm4 : RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (-1 / 4) (-11 / 8)) = 128000 * unit ^ 2 := by
    unfold RFAP.ConstructiveGaussian.Gaussian.normSq
    simp only [pointReal, pointImaginary]
    rw [negativeOneQuarterUnit, negativeElevenEighthUnit]
    ring1
  rw [norm1, norm2, norm3, norm4]
  rw [show 1024 * unit ^ 2 + 192 * (320 * unit ^ 2) +
      32 * (14400 * unit ^ 2) + 4 * (128000 * unit ^ 2) =
        1035264 * unit ^ 2 by ring1]
  have slopeEq : 1035264 * unit ^ 2 = (1011 / 64 : Q) := by
    rw [unitSquare]
    calc
      1035264 * (1 / 65536 : Q) = 1035264 / 65536 := by
        simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
          RFAP.ConstructiveFraction.one_mul]
      _ = 1011 / 64 := by
        apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
          (qNatPositive 65536 (by omega)).ne'
          (qNatPositive 64 (by omega)).ne'
        ring1
  have slopeLower : (1 : Q) ≤ 1035264 * unit ^ 2 := by
    rw [slopeEq]
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := (64 : Q)) _ (qNatPositive 64 (by omega))
    have cancel : (1011 / 64 : Q) * 64 = 1011 :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        (qNatPositive 64 (by omega)).ne'
    calc
      (1 : Q) * 64 = 64 := by ring1
      _ ≤ 1011 := RFAP.ConstructiveFraction.natCast_le_direct
        (m := 64) (n := 1011) (by omega)
      _ = (1011 / 64 : Q) * 64 := cancel.symm
  rw [max_eq_right slopeLower, slopeEq]
  have endpointSquare :
      (endpoint0.parameter - endpoint1.parameter) ^ 2 = (1 / 64 : Q) := by
    change ((0 : Q) - 1 / 8) ^ 2 = 1 / 64
    have difference : (0 : Q) - 1 / 8 = (-1) / 8 := by
      rw [negativeDiv]
      ring1
    rw [difference, pow_two,
      RFAP.ConstructiveFraction.div_mul_div_direct]
    rw [show (-1 : Q) * (-1) = 1 by ring1,
      show (8 : Q) * 8 = 64 by ring1]
  rw [endpointSquare, RFAP.ConstructiveFraction.div_mul_div_direct]
  apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
    (RFAP.ConstructiveFraction.mul_ne_zero_direct
      (qNatPositive 64 (by omega)).ne' (qNatPositive 64 (by omega)).ne')
    (qNatPositive 4096 (by omega)).ne'
  ring1

theorem secondVariationLtQuarter :
    CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
    endpoint0.parameter endpoint1.parameter < (1 / 4 : Q) := by
  have castEq :
      CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
          endpoint0.parameter endpoint1.parameter =
        CCL.Riemann.ClearSheetContinuation.variationBound explicitSecond
          endpoint0.parameter endpoint1.parameter := by
    unfold explicitSecond
    cases secondStartEq
    cases secondFinishEq
    rfl
  rw [castEq,
    CCL.Riemann.ClearSheetContinuation.variationBound_eq_denseLipschitz,
      secondPolynomialEq]
  unfold secondPolynomialCache
  rw [denseLipschitzBound_five_coeffs_parameterAmbient]
  have norm1 : RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (1 / 256) 0) = unit ^ 2 := by
    unfold RFAP.ConstructiveGaussian.Gaussian.normSq
    simp only [pointReal, pointImaginary]
    rw [oneTwoFiftySixthUnit]
    ring1
  have norm2 : RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (-1 / 16) (-1 / 32)) = 320 * unit ^ 2 := by
    unfold RFAP.ConstructiveGaussian.Gaussian.normSq
    simp only [pointReal, pointImaginary]
    rw [negativeOneSixteenthUnit, negativeOneThirtySecondUnit]
    ring1
  have norm3 : RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (9 / 32) (3 / 8)) = 14400 * unit ^ 2 := by
    unfold RFAP.ConstructiveGaussian.Gaussian.normSq
    simp only [pointReal, pointImaginary]
    rw [nineThirtySecondUnit, threeEighthUnit]
    ring1
  have norm4 : RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (-1 / 4) (-11 / 8)) = 128000 * unit ^ 2 := by
    unfold RFAP.ConstructiveGaussian.Gaussian.normSq
    simp only [pointReal, pointImaginary]
    rw [negativeOneQuarterUnit, negativeElevenEighthUnit]
    ring1
  rw [norm1, norm2, norm3, norm4]
  rw [show 1024 * unit ^ 2 + 192 * (320 * unit ^ 2) +
      32 * (14400 * unit ^ 2) + 4 * (128000 * unit ^ 2) =
        1035264 * unit ^ 2 by ring1]
  have denominatorPositive : (0 : Q) < 65536 :=
    qNatPositive 65536 (by omega)
  have denominatorNonzero : (65536 : Q) ≠ 0 :=
    denominatorPositive.ne'
  have slopeLower : (1 : Q) ≤ 1035264 * unit ^ 2 := by
    rw [unitSquare]
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := (65536 : Q)) _ denominatorPositive
    calc
      (1 : Q) * 65536 = 65536 := by ring1
      _ ≤ 1035264 :=
        RFAP.ConstructiveFraction.natCast_le_direct
          (m := 65536) (n := 1035264) (by omega)
      _ = (1035264 * (1 / 65536 : Q)) * 65536 := by
        rw [show (1035264 * (1 / 65536 : Q)) * 65536 =
          1035264 * ((1 / 65536 : Q) * 65536) by ring1]
        rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          denominatorNonzero]
        ring1
  have slopeUpper : 1035264 * unit ^ 2 < (16 : Q) := by
    rw [unitSquare]
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := (65536 : Q)) _ denominatorPositive
    calc
      (1035264 * (1 / 65536 : Q)) * 65536 = 1035264 := by
        rw [show (1035264 * (1 / 65536 : Q)) * 65536 =
          1035264 * ((1 / 65536 : Q) * 65536) by ring1]
        rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          denominatorNonzero]
        ring1
      _ < 1048576 :=
        RFAP.ConstructiveFraction.natCast_lt_direct
          (m := 1035264) (n := 1048576) (by omega)
      _ = (16 : Q) * 65536 := by ring1
  rw [max_eq_right slopeLower]
  have endpointSquare :
      (endpoint0.parameter - endpoint1.parameter) ^ 2 = (1 / 64 : Q) := by
    change ((0 : Q) - 1 / 8) ^ 2 = 1 / 64
    have difference : (0 : Q) - 1 / 8 = (-1) / 8 := by
      rw [negativeDiv]
      ring1
    rw [difference, pow_two,
      RFAP.ConstructiveFraction.div_mul_div_direct]
    rw [show (-1 : Q) * (-1) = 1 by ring1,
      show (8 : Q) * 8 = 64 by ring1]
  rw [endpointSquare]
  calc
    1035264 * unit ^ 2 * (1 / 64) < 16 * (1 / 64) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        slopeUpper oneSixtyFourPositive
    _ = (1 / 4 : Q) := by
      rw [oneSixtyFourUnit, oneQuarterUnit]
      ring1

theorem secondFirstClearanceBoundEq : secondSegment.clearanceBound =
    firstConnectorSegment.clearanceBound := by
  unfold secondSegment firstConnectorSegment
  rw [CCL.Riemann.BranchCuts.ClearSegment.restrict_clearanceBound,
    CCL.Riemann.BranchCuts.ClearSegment.restrict_clearanceBound]
  rfl

theorem secondDerivativeMarginEq :
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
      secondSegment =
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
      firstConnectorSegment := by
  unfold CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeThreshold
  rw [secondFirstClearanceBoundEq]

theorem secondRadiusLe : CCL.Riemann.UniformSquareRootPreparation.preparationRadius
    secondSegment workingRootDiameter ≤ (1 / 64 : Q) := by
  unfold CCL.Riemann.UniformSquareRootPreparation.preparationRadius
  refine (min_le_right _ _).trans ((min_le_left _ _).trans ?_)
  apply dyadicSquareRadius_le_oneSixtyFour
  · exact RFAP.ConstructiveFraction.div_pos_direct
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
        secondSegment)
      (RFAP.ConstructiveFraction.mul_pos_direct
        (qNatPositive 72 (by omega)) (qNatPositive 8 (by omega)))
  · have marginLe :
        CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
          secondSegment ≤ (1 / 4 : Q) := by
      rw [secondDerivativeMarginEq]
      exact firstConnectorDerivativeMarginLe
    have denominatorPositive : (0 : Q) < 72 * 8 :=
      RFAP.ConstructiveFraction.mul_pos_direct
        (qNatPositive 72 (by omega)) (qNatPositive 8 (by omega))
    calc
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
          secondSegment / (72 * 8) ≤ (1 / 4 : Q) / (72 * 8) := by
        simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          marginLe
            (RFAP.ConstructiveFraction.inv_pos_direct denominatorPositive).le
      _ = (1 / 2304 : Q) := by
        apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
          denominatorPositive.ne' (qNatPositive 2304 (by omega)).ne'
        calc
          (1 / 4 : Q) * 2304 = (1 / 4 : Q) * (4 * 576) := by ring1
          _ = ((1 / 4 : Q) * 4) * 576 := by ring1
          _ = 576 := by
            have cancelFour : (1 / 4 : Q) * 4 = 1 :=
              RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
                (qNatPositive 4 (by omega)).ne'
            rw [cancelFour]
            ring1
          _ = (1 : Q) * (72 * 8) := by ring1

theorem secondPreparedClearanceLeTransportFloor :
    CCL.Riemann.PreparedSheetContinuation.preparedClearanceLower
    secondSegment endpoint0 request0 ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        (1 / 8 : Q) := by
  unfold CCL.Riemann.PreparedSheetContinuation.preparedClearanceLower
  have marginLe :
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
        secondSegment ≤ (1 / 4 : Q) := by
    rw [secondDerivativeMarginEq]
    exact firstConnectorDerivativeMarginLe
  have segmentStartEq : secondSegment.pointAt 0 = point (-1) (-1 / 2) := by
    rw [CCL.Riemann.BranchCuts.ClearSegment.pointAt_zero]
    exact secondStartEq
  have evaluationEq :
      CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (point (-1) (-1 / 2)) = point (-23 / 16) (3 / 2) := by
    with_unfolding_all decide
  have evalLeBound :=
    CCL.Riemann.UniformSquareRootPreparation.eval_normSq_le_radicandNormBound
      secondSegment 0 (by decide)
  rw [segmentStartEq] at evalLeBound
  change RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (point (-1) (-1 / 2))) ≤
    CCL.Riemann.UniformSquareRootPreparation.radicandNormBound
      secondSegment at evalLeBound
  rw [evaluationEq] at evalLeBound
  have fifteenQuarterUnit : (15 / 4 : Q) = 960 * unit :=
    scaledUnit 15 960 4 (by omega) (by ring1)
  have radicandLower : (15 / 4 : Q) ≤
      CCL.Riemann.UniformSquareRootPreparation.radicandNormBound
        secondSegment := secondStartNormLower.trans evalLeBound
  have sampleDerivativeLower : (32 : Q) ≤
      CCL.Riemann.UniformSquareRootPreparation.rootSampleDerivativeMajorant
        secondSegment := by
    unfold CCL.Riemann.UniformSquareRootPreparation.rootSampleDerivativeMajorant
      CCL.Riemann.UniformSquareRootPreparation.rootSampleNormSqMajorant
    calc
      (32 : Q) = 4 * (2 * ((1 / 4 : Q) + 15 / 4)) := by
        rw [oneQuarterUnit, fifteenQuarterUnit]
        calc
          (32 : Q) = 32 * (256 * unit) := by
            rw [← oneUnit]
            ring1
          _ = 4 * (2 * (64 * unit + 960 * unit)) := by ring1
      _ ≤ 4 * (2 * ((1 / 4 : Q) +
          CCL.Riemann.UniformSquareRootPreparation.radicandNormBound
            secondSegment)) := by
        apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        · apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          · exact add_le_add le_rfl radicandLower
          · decide
        · decide
  have radiusSqNonnegative : (0 : Q) ≤
      CCL.Riemann.UniformSquareRootPreparation.preparationRadius
          secondSegment workingRootDiameter ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  have majorantLower :
      256 * CCL.Riemann.UniformSquareRootPreparation.preparationRadius
          secondSegment workingRootDiameter ^ 2 ≤
        4 * CCL.Riemann.UniformSquareRootPreparation.linearizationMajorant
          secondSegment workingRootDiameter := by
    unfold CCL.Riemann.UniformSquareRootPreparation.linearizationMajorant
    calc
      256 * CCL.Riemann.UniformSquareRootPreparation.preparationRadius
          secondSegment workingRootDiameter ^ 2 =
        (8 * 32) *
          CCL.Riemann.UniformSquareRootPreparation.preparationRadius
            secondSegment workingRootDiameter ^ 2 := by ring1
      _ ≤ (8 *
          CCL.Riemann.UniformSquareRootPreparation.rootSampleDerivativeMajorant
            secondSegment) *
          CCL.Riemann.UniformSquareRootPreparation.preparationRadius
            secondSegment workingRootDiameter ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            sampleDerivativeLower (by decide)) radiusSqNonnegative
      _ = 4 * (2 *
          CCL.Riemann.UniformSquareRootPreparation.rootSampleDerivativeMajorant
            secondSegment *
          CCL.Riemann.UniformSquareRootPreparation.preparationRadius
            secondSegment workingRootDiameter ^ 2) := by ring1
  exact
    CCL.Riemann.UniformSquareRootPreparation.predictedClearance_le_eighthTransportFloor_of_radius
      secondSegment workingRootDiameter workingRootDiameter_positive marginLe
        secondRadiusLe majorantLower

theorem secondStartDirectBoundaryBounds :
    CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
    (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
      (point (-1) (-1 / 2))) firstConnectorBoxTwo (1 / 4 : Q)
        (3 / 4 : Q) := by
  apply CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryBoundsOfSideChecks
  all_goals with_unfolding_all decide +revert

end CCL.Riemann.ExplicitQuarticBranches
