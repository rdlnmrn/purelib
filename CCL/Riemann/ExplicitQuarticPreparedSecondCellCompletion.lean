import CCL.Riemann.ExplicitQuarticPreparedSecondCellRetained

namespace CCL.Riemann.ExplicitQuarticBranches

private theorem qNatPositiveLate (n : Nat) (positive : 0 < n) :
    (0 : Q) < n :=
  RFAP.ConstructiveFraction.natCast_pos_direct positive

private def lateRational (num : Int) (den : Nat) (denPositive : 0 < den)
    (left right : Int)
    (bezout : left * (num.natAbs : Int) + right * (den : Int) = 1) : Q where
  num := num
  den := den
  den_pos := denPositive
  reduced := ⟨⟨left, right, bezout⟩⟩

private theorem lateRational_eq_div (num : Int) (den : Nat)
    (denPositive : 0 < den) (left right : Int)
    (bezout : left * (num.natAbs : Int) + right * (den : Int) = 1) :
    lateRational num den denPositive left right bezout =
      (num : Q) / (den : Q) := by
  let value := lateRational num den denPositive left right bezout
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (qNatPositiveLate den denPositive).ne'
  calc
    value * (den : Q) = (num : Q) :=
      RFAP.ConstructiveFraction.representative_mul_den value
    _ = ((num : Q) / (den : Q)) * (den : Q) :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        (qNatPositiveLate den denPositive).ne').symm

private def lateOneOver1024 : Q :=
  lateRational 1 1024 (by omega) 1 0 (by omega)

private theorem lateOneOver1024_eq : lateOneOver1024 = (1 / 1024 : Q) :=
  lateRational_eq_div 1 1024 (by omega) 1 0 (by omega)

private def lateOneOver128 : Q :=
  lateRational 1 128 (by omega) 1 0 (by omega)

private theorem lateOneOver128_eq : lateOneOver128 = (1 / 128 : Q) :=
  lateRational_eq_div 1 128 (by omega) 1 0 (by omega)

private def lateThirteenSixtyFourths : Q :=
  lateRational 13 64 (by omega) 5 (-1) (by omega)

private theorem lateThirteenSixtyFourths_eq :
    lateThirteenSixtyFourths = (13 / 64 : Q) :=
  lateRational_eq_div 13 64 (by omega) 5 (-1) (by omega)

def secondConnectorBoxTwo : Box :=
  { xLower := lateRational (-5) 16 (by omega) (-3) 1 (by omega)
    xUpper := lateRational 19 16 (by omega) (-5) 6 (by omega)
    yLower := lateRational 11 16 (by omega) 3 (-2) (by omega)
    yUpper := lateRational 35 16 (by omega) 11 (-24) (by omega)
    x_valid := by with_unfolding_all decide
    y_valid := by with_unfolding_all decide }

def secondConnectorBoxThree : Box :=
  { xLower := lateRational (-19) 32 (by omega) (-5) 3 (by omega)
    xUpper := lateRational 29 32 (by omega) (-11) 10 (by omega)
    yLower := lateRational 13 32 (by omega) 5 (-2) (by omega)
    yUpper := lateRational 61 32 (by omega) (-11) 21 (by omega)
    x_valid := by with_unfolding_all decide
    y_valid := by with_unfolding_all decide }

theorem secondConnectorBoxTwoProper : secondConnectorBoxTwo.Proper := by
  constructor <;> with_unfolding_all decide

theorem secondConnectorBoxThreeProper : secondConnectorBoxThree.Proper := by
  constructor <;> with_unfolding_all decide

private theorem secondConnectorBoxTwoSmall (edge : Fin 8) :
    secondConnectorBoxTwo.diagonalSq <
      (secondEdgeRequest edge).rootDiameter := by
  change secondConnectorBoxTwo.diagonalSq < workingRootDiameter
  with_unfolding_all decide

private theorem secondConnectorBoxThreeSmall (edge : Fin 8) :
    secondConnectorBoxThree.diagonalSq <
      (secondEdgeRequest edge).rootDiameter := by
  change secondConnectorBoxThree.diagonalSq < workingRootDiameter
  with_unfolding_all decide

private theorem secondConnectorBoxTwoRefines :
    secondConnectorBoxTwo.Refines
      (CCL.Riemann.UniformSquareRootPreparation.rootAmbient secondSegment) := by
  change
    -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius secondSegment ≤
        secondConnectorBoxTwo.xLower ∧
      secondConnectorBoxTwo.xUpper ≤
          CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius secondSegment ∧
      -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius secondSegment ≤
          secondConnectorBoxTwo.yLower ∧
      secondConnectorBoxTwo.yUpper ≤
        CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius secondSegment
  have threeLe :=
    CCL.Riemann.UniformSquareRootPreparation.three_le_rootAmbientRadius
      secondSegment
  exact ⟨(RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
      (by with_unfolding_all decide),
    (by with_unfolding_all decide : secondConnectorBoxTwo.xUpper ≤ (3 : Q)).trans
      threeLe,
    (RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
      (by with_unfolding_all decide),
    (by with_unfolding_all decide : secondConnectorBoxTwo.yUpper ≤ (3 : Q)).trans
      threeLe⟩

private theorem secondConnectorBoxThreeRefines :
    secondConnectorBoxThree.Refines
      (CCL.Riemann.UniformSquareRootPreparation.rootAmbient secondSegment) := by
  change
    -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius secondSegment ≤
        secondConnectorBoxThree.xLower ∧
      secondConnectorBoxThree.xUpper ≤
          CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius secondSegment ∧
      -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius secondSegment ≤
          secondConnectorBoxThree.yLower ∧
      secondConnectorBoxThree.yUpper ≤
        CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius secondSegment
  have threeLe :=
    CCL.Riemann.UniformSquareRootPreparation.three_le_rootAmbientRadius
      secondSegment
  exact ⟨(RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
      (by with_unfolding_all decide),
    (by with_unfolding_all decide : secondConnectorBoxThree.xUpper ≤ (3 : Q)).trans
      threeLe,
    (RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
      (by with_unfolding_all decide),
    (by with_unfolding_all decide : secondConnectorBoxThree.yUpper ≤ (3 : Q)).trans
      threeLe⟩

private theorem secondDirectBoundsSixOld :
    CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (secondGridParameter 6) secondConnectorBoxOne
        (1 / 8 : Q) lateThirteenSixtyFourths := by
  rw [secondGridParameter_eq_reduced]
  apply CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryBoundsOfSideChecks
  all_goals with_unfolding_all decide +revert

private theorem secondDirectBoundsSixFirstMoving :
    CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (secondGridParameter 6) secondConnectorBoxTwo
        lateOneOver1024 lateOneOver128 := by
  rw [secondGridParameter_eq_reduced]
  apply CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryBoundsOfSideChecks
  all_goals with_unfolding_all decide +revert

private theorem secondDirectBoundsSixSecondMoving :
    CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (secondGridParameter 6) secondConnectorBoxThree
        (11 / 32 : Q) (3 / 4 : Q) := by
  rw [secondGridParameter_eq_reduced]
  apply CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryBoundsOfSideChecks
  all_goals with_unfolding_all decide +revert

theorem secondOwnerSixReady :
    CCL.Riemann.PreparedSheetContinuation.AlreadyPrepared secondSegment
      (secondMeshEndpoint 6) secondOwnerSix (secondEdgeRequest 6) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [secondOwnerSixBoxEq]
    exact secondConnectorBoxOneSmall 6
  · exact (predictedLeEighthFloor 6).trans
      secondEdgeFiveStep.advanceCache.clearanceFloor
  · rw [secondOwnerSixBoxEq]
    exact secondConnectorBoxOneRefines

theorem secondOwnerSixClearanceLeNineSixtyFourths :
    secondOwnerSix.track.initial.clearance.bound ≤ (9 / 64 : Q) := by
  have squareLe :
      (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
        secondSegment (secondMeshEndpoint 5) secondOwnerFive
          (secondEdgeRequest 5)).preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 ≤
        (3 / 4 : Q) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
        secondSegment (secondMeshEndpoint 5) secondOwnerFive
          (secondEdgeRequest 5)).preparedOwner.track.initial.ambientLeftClearance.positive.le
      secondEdgeFiveStep.preparedAmbientLeftLe 2
  calc
    secondOwnerSix.track.initial.clearance.bound ≤
        (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
          secondSegment (secondMeshEndpoint 5) secondOwnerFive
            (secondEdgeRequest 5)).preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4 :=
      secondEdgeFiveStep.advanceCache.clearanceQuarterSq
    _ ≤ (3 / 4 : Q) ^ 2 / 4 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct squareLe
        (RFAP.ConstructiveFraction.inv_pos_direct
          (qNatPositiveLate 4 (by omega))).le
    _ = (9 / 64 : Q) := by
      have square : (3 / 4 : Q) ^ 2 = 9 / 16 := by
        rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct]
        rw [show (3 : Q) * 3 = 9 by ring1,
          show (4 : Q) * 4 = 16 by ring1]
      rw [square]
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      calc
        9 * 16⁻¹ * 4⁻¹ = 9 * (16⁻¹ * 4⁻¹) := by ring1
        _ = 9 * ((16 : Q) * 4)⁻¹ :=
          congrArg (fun value : Q => 9 * value)
            (RFAP.ConstructiveFraction.inv_mul_direct 16 4).symm
        _ = 9 * (64 : Q)⁻¹ := by rw [show (16 : Q) * 4 = 64 by ring1]

private theorem lateNatDivLeNatDiv (m n d : Nat) (lessEqual : m ≤ n)
    (positive : 0 < d) : (m : Q) / d ≤ (n : Q) / d := by
  simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    (RFAP.ConstructiveFraction.natCast_le_direct lessEqual)
      (RFAP.ConstructiveFraction.inv_pos_direct
        (qNatPositiveLate d positive)).le

private theorem lateNineLeThirteen : (9 / 64 : Q) ≤ 13 / 64 := by
  exact lateNatDivLeNatDiv 9 13 64 (by decide) (by omega)

private theorem lateNineLeVariation : (9 / 64 : Q) ≤ 1011 / 4096 := by
  rw [show (9 / 64 : Q) = 576 / 4096 by
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      (qNatPositiveLate 64 (by omega)).ne'
        (qNatPositiveLate 4096 (by omega)).ne'
    ring1]
  exact lateNatDivLeNatDiv 576 1011 4096 (by decide) (by omega)

private theorem lateThirteenLeVariation : (13 / 64 : Q) ≤ 1011 / 4096 := by
  rw [show (13 / 64 : Q) = 832 / 4096 by
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      (qNatPositiveLate 64 (by omega)).ne'
        (qNatPositiveLate 4096 (by omega)).ne'
    ring1]
  exact lateNatDivLeNatDiv 832 1011 4096 (by decide) (by omega)

theorem secondOwnerSixNotCarries :
    ¬ CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
        (secondMeshEndpoint 6).parameter
          (secondEdgeRequest 6).endpoint.parameter <
      secondOwnerSix.track.initial.clearance.bound := by
  apply not_lt_of_ge
  rw [show CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
      (secondMeshEndpoint 6).parameter
        (secondEdgeRequest 6).endpoint.parameter = (1011 / 4096 : Q) by
    exact secondMeshVariationEq 6]
  exact secondOwnerSixClearanceLeNineSixtyFourths.trans lateNineLeVariation

theorem secondOwnerSixStrengthenedClearanceLeThirteenSixtyFourths :
    (CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
      secondOwnerSix).track.initial.clearance.bound ≤ (13 / 64 : Q) := by
  let cache : CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
      secondOwnerSix.track.initial.box (1 / 8 : Q)
        lateThirteenSixtyFourths := by
    rw [secondOwnerSixBoxEq]
    change CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
          secondConnectorBoxOne (1 / 8 : Q) lateThirteenSixtyFourths
    rw [quartic_eval_secondMeshEndpoint]
    exact secondDirectBoundsSixOld
  rw [CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max
    secondOwnerSix cache.leftNonzero cache.rightNonzero cache.bottomNonzero
      cache.topNonzero]
  apply max_le
  · exact secondOwnerSixClearanceLeNineSixtyFourths.trans lateNineLeThirteen
  · exact cache.le_upper.trans_eq lateThirteenSixtyFourths_eq

theorem secondOwnerSixStrengthenedNotCarries :
    ¬ CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
        (secondMeshEndpoint 6).parameter
          (secondEdgeRequest 6).endpoint.parameter <
      (CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        secondOwnerSix).track.initial.clearance.bound := by
  apply not_lt_of_ge
  rw [show CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
      (secondMeshEndpoint 6).parameter
        (secondEdgeRequest 6).endpoint.parameter = (1011 / 4096 : Q) by
    exact secondMeshVariationEq 6]
  exact secondOwnerSixStrengthenedClearanceLeThirteenSixtyFourths.trans
    lateThirteenLeVariation

theorem secondLateFirstBoxProjection :
    CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenterBox?
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
        secondOwnerSix.parameterNonzero secondConnectorBoxOne
          secondConnectorBoxOneProper = some secondConnectorBoxTwo := by
  change CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenterBox?
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
        secondOwnerSix.parameterNonzero secondConnectorBoxOne
          secondConnectorBoxOneProper = some secondConnectorBoxTwo
  have parameterNonzero : secondGridReducedParameter 6 ≠ 0 := by
    with_unfolding_all decide
  have computed :
      CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenterBox?
          (secondGridReducedParameter 6) parameterNonzero secondConnectorBoxOne
            secondConnectorBoxOneProper = some secondConnectorBoxTwo := by
    with_unfolding_all rfl
  simpa only [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
    using computed

def secondLateFirstMovingCache :
    { reset : CCL.Riemann.ExactQuadraticOwnerClearance.MovingRecenter
        _ secondOwnerSix //
      CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
        secondOwnerSix = some reset } := by
  generalize found :
    CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
      secondOwnerSix = result
  cases result with
  | none =>
      have succeeds : Option.map (fun reset => reset.ownerBox)
          (CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
            secondOwnerSix) = some secondConnectorBoxTwo := by
        rw [CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
          secondOwnerSix secondConnectorBoxOne secondConnectorBoxOneProper
            secondOwnerSixBoxEq, secondLateFirstBoxProjection]
      rw [found] at succeeds
      contradiction
  | some reset => exact ⟨reset, rfl⟩

def secondLateFirstMoving := secondLateFirstMovingCache.1

theorem secondLateFirstMovingFound :
    CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
      secondOwnerSix = some secondLateFirstMoving :=
  secondLateFirstMovingCache.2

theorem secondLateFirstRecenteredEq :
    CCL.Riemann.PreparedSheetContinuation.recentered secondOwnerSix =
      secondLateFirstMoving.owner :=
  CCL.Riemann.PreparedSheetContinuation.recentered_eq_of_movingRecenter_eq_some
    secondOwnerSix secondLateFirstMoving secondLateFirstMovingFound

theorem secondLateFirstMovingBoxEq :
    secondLateFirstMoving.ownerBox = secondConnectorBoxTwo := by
  have mapped : Option.map (fun reset => reset.ownerBox)
      (CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
        secondOwnerSix) = some secondConnectorBoxTwo := by
    rw [CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
      secondOwnerSix secondConnectorBoxOne secondConnectorBoxOneProper
        secondOwnerSixBoxEq, secondLateFirstBoxProjection]
  rw [secondLateFirstMovingFound] at mapped
  exact Option.some.inj mapped

theorem secondLateFirstMovingClearanceLower : lateOneOver1024 ≤
    secondLateFirstMoving.owner.track.initial.clearance.bound := by
  rw [secondLateFirstMoving.ownerDirectClearanceBound]
  apply CCL.Riemann.ExactQuadraticOwnerClearance.le_directBoundaryClearance_bound
  all_goals rw [secondLateFirstMovingBoxEq]
  case leftLe =>
    change lateOneOver1024 ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
            secondConnectorBoxTwo secondConnectorBoxTwo.xLower
    rw [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
    with_unfolding_all decide
  case rightLe =>
    change lateOneOver1024 ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
            secondConnectorBoxTwo secondConnectorBoxTwo.xUpper
    rw [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
    with_unfolding_all decide
  case bottomLe =>
    change lateOneOver1024 ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
            secondConnectorBoxTwo secondConnectorBoxTwo.yLower
    rw [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
    with_unfolding_all decide
  case topLe =>
    change lateOneOver1024 ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
            secondConnectorBoxTwo secondConnectorBoxTwo.yUpper
    rw [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
    with_unfolding_all decide

private theorem lateEighthFloorLeOneOver1024 :
    CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        (1 / 8 : Q) ≤ lateOneOver1024 := by
  rw [lateOneOver1024_eq]
  unfold CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
  have numeratorNonnegative : (0 : Q) ≤ (1 / 8 : Q) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  have sixteenLeDenominator : (16 : Q) ≤ 4 * 65536 := by
    calc
      (16 : Q) = 4 * 4 := by ring1
      _ ≤ 4 * 65536 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (RFAP.ConstructiveFraction.natCast_le_direct
            (m := 4) (n := 65536) (by decide))
          (qNatPositiveLate 4 (by omega)).le
  calc
    (1 / 8 : Q) ^ 2 / (4 * 65536) ≤ (1 / 8 : Q) ^ 2 / 16 :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        numeratorNonnegative (qNatPositiveLate 16 (by omega))
          sixteenLeDenominator
    _ = (1 / 1024 : Q) := by
      have square : (1 / 8 : Q) ^ 2 = 1 / 64 := by
        rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct]
        rw [show (1 : Q) * 1 = 1 by ring1,
          show (8 : Q) * 8 = 64 by ring1]
      rw [square]
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      calc
        1 * 64⁻¹ * 16⁻¹ = 1 * (64⁻¹ * 16⁻¹) := by ring1
        _ = 1 * ((64 : Q) * 16)⁻¹ :=
          congrArg (fun value : Q => 1 * value)
            (RFAP.ConstructiveFraction.inv_mul_direct 64 16).symm
        _ = 1 * (1024 : Q)⁻¹ := by
          rw [show (64 : Q) * 16 = 1024 by ring1]

theorem secondLateFirstRecenteredReady :
    CCL.Riemann.PreparedSheetContinuation.AlreadyPrepared secondSegment
      (secondMeshEndpoint 6)
        (CCL.Riemann.PreparedSheetContinuation.recentered secondOwnerSix)
          (secondEdgeRequest 6) := by
  rw [secondLateFirstRecenteredEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [secondLateFirstMoving.ownerInitialBox, secondLateFirstMovingBoxEq]
    exact secondConnectorBoxTwoSmall 6
  · exact (predictedLeEighthFloor 6).trans
      (lateEighthFloorLeOneOver1024.trans
        secondLateFirstMovingClearanceLower)
  · rw [secondLateFirstMoving.ownerInitialBox, secondLateFirstMovingBoxEq]
    exact secondConnectorBoxTwoRefines

theorem secondLateFirstMovingClearanceUpper :
    secondLateFirstMoving.owner.track.initial.clearance.bound ≤
      lateOneOver128 := by
  rw [secondLateFirstMoving.ownerDirectClearanceBound,
    CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance_bound,
    secondLateFirstMovingBoxEq]
  change min
      (CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
            secondConnectorBoxTwo secondConnectorBoxTwo.xLower)
      (min
        (CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
          (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
            (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
              secondConnectorBoxTwo secondConnectorBoxTwo.xUpper)
        (min
          (CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
              (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
                secondConnectorBoxTwo secondConnectorBoxTwo.yLower)
          (CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
              (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
                secondConnectorBoxTwo secondConnectorBoxTwo.yUpper))) ≤
      lateOneOver128
  rw [quartic_eval_secondMeshEndpoint]
  have upper := secondDirectBoundsSixFirstMoving.le_upper
  rw [CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance_bound]
    at upper
  exact upper

private theorem lateOneOver128LeVariation :
    lateOneOver128 ≤ (1011 / 4096 : Q) := by
  rw [lateOneOver128_eq,
    show (1 / 128 : Q) = 32 / 4096 by
      apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
        (qNatPositiveLate 128 (by omega)).ne'
          (qNatPositiveLate 4096 (by omega)).ne'
      ring1]
  exact lateNatDivLeNatDiv 32 1011 4096 (by decide) (by omega)

theorem secondLateFirstRecenteredNotCarries :
    ¬ CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
        (secondMeshEndpoint 6).parameter
          (secondEdgeRequest 6).endpoint.parameter <
      (CCL.Riemann.PreparedSheetContinuation.recentered
        secondOwnerSix).track.initial.clearance.bound := by
  rw [secondLateFirstRecenteredEq]
  apply not_lt_of_ge
  rw [show CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
      (secondMeshEndpoint 6).parameter
        (secondEdgeRequest 6).endpoint.parameter = (1011 / 4096 : Q) by
    exact secondMeshVariationEq 6]
  exact secondLateFirstMovingClearanceUpper.trans lateOneOver128LeVariation

theorem secondLateFirstStrengthenedClearanceUpper :
    (CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
      (CCL.Riemann.PreparedSheetContinuation.recentered
        secondOwnerSix)).track.initial.clearance.bound ≤ lateOneOver128 := by
  rw [secondLateFirstRecenteredEq]
  let cache : CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
      secondLateFirstMoving.owner.track.initial.box lateOneOver1024
        lateOneOver128 := by
    rw [secondLateFirstMoving.ownerInitialBox, secondLateFirstMovingBoxEq]
    change CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
          secondConnectorBoxTwo lateOneOver1024 lateOneOver128
    rw [quartic_eval_secondMeshEndpoint]
    exact secondDirectBoundsSixFirstMoving
  rw [CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max
    secondLateFirstMoving.owner cache.leftNonzero cache.rightNonzero
      cache.bottomNonzero cache.topNonzero]
  exact max_le secondLateFirstMovingClearanceUpper cache.le_upper

theorem secondLateFirstStrengthenedNotCarries :
    ¬ CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
        (secondMeshEndpoint 6).parameter
          (secondEdgeRequest 6).endpoint.parameter <
      (CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        (CCL.Riemann.PreparedSheetContinuation.recentered
          secondOwnerSix)).track.initial.clearance.bound := by
  apply not_lt_of_ge
  rw [show CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
      (secondMeshEndpoint 6).parameter
        (secondEdgeRequest 6).endpoint.parameter = (1011 / 4096 : Q) by
    exact secondMeshVariationEq 6]
  exact secondLateFirstStrengthenedClearanceUpper.trans
    lateOneOver128LeVariation

theorem secondLateSecondBoxProjection :
    CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenterBox?
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
        secondLateFirstMoving.owner.parameterNonzero secondConnectorBoxTwo
          secondConnectorBoxTwoProper = some secondConnectorBoxThree := by
  change CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenterBox?
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
        secondLateFirstMoving.owner.parameterNonzero secondConnectorBoxTwo
          secondConnectorBoxTwoProper = some secondConnectorBoxThree
  have parameterNonzero : secondGridReducedParameter 6 ≠ 0 := by
    with_unfolding_all decide
  have computed :
      CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenterBox?
          (secondGridReducedParameter 6) parameterNonzero secondConnectorBoxTwo
            secondConnectorBoxTwoProper = some secondConnectorBoxThree := by
    with_unfolding_all rfl
  simpa only [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
    using computed

def secondLateSecondMovingCache :
    { reset : CCL.Riemann.ExactQuadraticOwnerClearance.MovingRecenter
        _ secondLateFirstMoving.owner //
      CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
        secondLateFirstMoving.owner = some reset } := by
  generalize found :
    CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
      secondLateFirstMoving.owner = result
  cases result with
  | none =>
      have succeeds : Option.map (fun reset => reset.ownerBox)
          (CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
            secondLateFirstMoving.owner) = some secondConnectorBoxThree := by
        rw [CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
          secondLateFirstMoving.owner secondConnectorBoxTwo
            secondConnectorBoxTwoProper
              (secondLateFirstMoving.ownerInitialBox.trans
                secondLateFirstMovingBoxEq), secondLateSecondBoxProjection]
      rw [found] at succeeds
      contradiction
  | some reset => exact ⟨reset, rfl⟩

def secondLateSecondMoving := secondLateSecondMovingCache.1

theorem secondLateSecondMovingFound :
    CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
      secondLateFirstMoving.owner = some secondLateSecondMoving :=
  secondLateSecondMovingCache.2

theorem secondLateSecondRecenteredEq :
    CCL.Riemann.PreparedSheetContinuation.recentered
        secondLateFirstMoving.owner = secondLateSecondMoving.owner :=
  CCL.Riemann.PreparedSheetContinuation.recentered_eq_of_movingRecenter_eq_some
    secondLateFirstMoving.owner secondLateSecondMoving
      secondLateSecondMovingFound

theorem secondLateRecenteredTwiceEq :
    CCL.Riemann.PreparedSheetContinuation.recentered
        (CCL.Riemann.PreparedSheetContinuation.recentered secondOwnerSix) =
      secondLateSecondMoving.owner := by
  rw [secondLateFirstRecenteredEq]
  exact secondLateSecondRecenteredEq

theorem secondLateSecondMovingBoxEq :
    secondLateSecondMoving.ownerBox = secondConnectorBoxThree := by
  have mapped : Option.map (fun reset => reset.ownerBox)
      (CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
        secondLateFirstMoving.owner) = some secondConnectorBoxThree := by
    rw [CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
      secondLateFirstMoving.owner secondConnectorBoxTwo
        secondConnectorBoxTwoProper
          (secondLateFirstMoving.ownerInitialBox.trans
            secondLateFirstMovingBoxEq), secondLateSecondBoxProjection]
  rw [secondLateSecondMovingFound] at mapped
  exact Option.some.inj mapped

theorem secondLateSecondMovingClearance : (11 / 32 : Q) ≤
    secondLateSecondMoving.owner.track.initial.clearance.bound := by
  rw [secondLateSecondMoving.ownerDirectClearanceBound]
  apply CCL.Riemann.ExactQuadraticOwnerClearance.le_directBoundaryClearance_bound
  all_goals rw [secondLateSecondMovingBoxEq]
  case leftLe =>
    change (11 / 32 : Q) ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
            secondConnectorBoxThree secondConnectorBoxThree.xLower
    rw [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
    with_unfolding_all decide
  case rightLe =>
    change (11 / 32 : Q) ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
            secondConnectorBoxThree secondConnectorBoxThree.xUpper
    rw [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
    with_unfolding_all decide
  case bottomLe =>
    change (11 / 32 : Q) ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
            secondConnectorBoxThree secondConnectorBoxThree.yLower
    rw [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
    with_unfolding_all decide
  case topLe =>
    change (11 / 32 : Q) ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
            secondConnectorBoxThree secondConnectorBoxThree.yUpper
    rw [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
    with_unfolding_all decide

private theorem lateQuarterLeElevenThirtySeconds :
    (1 / 4 : Q) ≤ 11 / 32 := by
  rw [show (1 / 4 : Q) = 8 / 32 by
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      (qNatPositiveLate 4 (by omega)).ne'
        (qNatPositiveLate 32 (by omega)).ne'
    ring1]
  exact lateNatDivLeNatDiv 8 11 32 (by decide) (by omega)

theorem secondLateSecondRecenteredReady :
    CCL.Riemann.PreparedSheetContinuation.AlreadyPrepared secondSegment
      (secondMeshEndpoint 6)
        (CCL.Riemann.PreparedSheetContinuation.recentered
          (CCL.Riemann.PreparedSheetContinuation.recentered secondOwnerSix))
            (secondEdgeRequest 6) := by
  rw [secondLateRecenteredTwiceEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [secondLateSecondMoving.ownerInitialBox, secondLateSecondMovingBoxEq]
    exact secondConnectorBoxThreeSmall 6
  · have marginLe :
        CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
          secondSegment ≤ (1 / 4 : Q) := by
      rw [secondDerivativeMarginEq]
      exact firstConnectorDerivativeMarginLe
    exact
      (CCL.Riemann.UniformSquareRootPreparation.predictedClearance_le_oneOver128
        secondSegment (secondEdgeRequest 6).rootDiameter
          (secondEdgeRequest 6).rootDiameterPositive marginLe).trans
        ((show (1 / (16 * 8) : Q) ≤ 11 / 32 by
          with_unfolding_all decide).trans secondLateSecondMovingClearance)
  · rw [secondLateSecondMoving.ownerInitialBox, secondLateSecondMovingBoxEq]
    exact secondConnectorBoxThreeRefines

theorem secondLateSecondRecenteredCarries :
    CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
        (secondMeshEndpoint 6).parameter
          (secondEdgeRequest 6).endpoint.parameter <
      (CCL.Riemann.PreparedSheetContinuation.recentered
        (CCL.Riemann.PreparedSheetContinuation.recentered
          secondOwnerSix)).track.initial.clearance.bound := by
  rw [secondLateRecenteredTwiceEq]
  exact (secondVariationLtQuarterAt 6).trans_le
    (lateQuarterLeElevenThirtySeconds.trans secondLateSecondMovingClearance)

theorem secondLatePreparedEqRecenteredTwice :
    CCL.Riemann.PreparedSheetContinuation.prepared secondSegment
        (secondMeshEndpoint 6) secondOwnerSix (secondEdgeRequest 6) =
      CCL.Riemann.PreparedSheetContinuation.recentered
        (CCL.Riemann.PreparedSheetContinuation.recentered secondOwnerSix) :=
  CCL.Riemann.PreparedSheetContinuation.prepared_eq_recentered_twice_of_ready
    secondSegment (secondMeshEndpoint 6) secondOwnerSix (secondEdgeRequest 6)
      secondOwnerSixReady secondOwnerSixNotCarries
        secondOwnerSixStrengthenedNotCarries secondLateFirstRecenteredReady
          secondLateFirstRecenteredNotCarries
            secondLateFirstStrengthenedNotCarries
              secondLateSecondRecenteredReady
                secondLateSecondRecenteredCarries

theorem secondLateCanonicalSmall :
    CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
        (secondMeshEndpoint 6).parameter
          (secondEdgeRequest 6).endpoint.parameter <
      (CCL.Riemann.PreparedSheetContinuation.prepared secondSegment
        (secondMeshEndpoint 6) secondOwnerSix
          (secondEdgeRequest 6)).track.initial.clearance.bound := by
  rw [secondLatePreparedEqRecenteredTwice]
  exact secondLateSecondRecenteredCarries

def secondLateCachedSource :=
  CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical secondSegment
    (secondMeshEndpoint 6) secondOwnerSix (secondEdgeRequest 6)

theorem secondLateSecondMovingAmbientLeftLeThreeQuarters :
    secondLateSecondMoving.owner.track.initial.ambientLeftClearance.bound ≤
      (3 / 4 : Q) := by
  rw [secondLateSecondMoving.ownerAmbientLeftClearanceBound,
    CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance_bound,
    secondLateSecondMovingBoxEq]
  change min
      (CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
            secondConnectorBoxThree secondConnectorBoxThree.xLower)
      (min
        (CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
          (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
            (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
              secondConnectorBoxThree secondConnectorBoxThree.xUpper)
        (min
          (CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
              (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
                secondConnectorBoxThree secondConnectorBoxThree.yLower)
          (CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
              (secondSegment.pointAt (secondMeshEndpoint 6).parameter))
                secondConnectorBoxThree secondConnectorBoxThree.yUpper))) ≤
      (3 / 4 : Q)
  rw [quartic_eval_secondMeshEndpoint]
  have upper := secondDirectBoundsSixSecondMoving.le_upper
  rw [CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance_bound]
    at upper
  exact upper

theorem secondLatePreparedAmbientLeftLeThreeQuarters :
    secondLateCachedSource.preparedOwner.track.initial.ambientLeftClearance.bound ≤
      (3 / 4 : Q) := by
  rw [show secondLateCachedSource.preparedOwner =
      CCL.Riemann.PreparedSheetContinuation.prepared secondSegment
        (secondMeshEndpoint 6) secondOwnerSix (secondEdgeRequest 6) by rfl,
    secondLatePreparedEqRecenteredTwice, secondLateRecenteredTwiceEq]
  exact secondLateSecondMovingAmbientLeftLeThreeQuarters

theorem secondLateSecondRecenteredBudget :
    CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      (CCL.Riemann.PreparedSheetContinuation.recentered
        (CCL.Riemann.PreparedSheetContinuation.recentered secondOwnerSix)) := by
  rw [secondLateRecenteredTwiceEq]
  apply CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientBudget_of_box
    secondLateSecondMoving.owner secondConnectorBoxThree
  · exact secondLateSecondMoving.ownerInitialBox.trans
      secondLateSecondMovingBoxEq
  · exact secondLateSecondMoving.ownerAmbientBox.trans
      secondLateSecondMovingBoxEq
  · change RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 6).parameter)) ≤ (256 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondGridParameterNormSqLe 6
  all_goals with_unfolding_all decide

theorem secondLatePreparedDominance :
    CCL.Riemann.ExactQuadraticOwnerClearance.AmbientClearanceDominance
      secondLateCachedSource.preparedOwner := by
  rw [show secondLateCachedSource.preparedOwner =
      CCL.Riemann.PreparedSheetContinuation.prepared secondSegment
        (secondMeshEndpoint 6) secondOwnerSix (secondEdgeRequest 6) by rfl,
    secondLatePreparedEqRecenteredTwice, secondLateRecenteredTwiceEq]
  exact secondLateSecondMoving.ownerDominance

theorem secondLatePreparedBudget :
    CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      secondLateCachedSource.preparedOwner := by
  rw [show secondLateCachedSource.preparedOwner =
      CCL.Riemann.PreparedSheetContinuation.prepared secondSegment
        (secondMeshEndpoint 6) secondOwnerSix (secondEdgeRequest 6) by rfl,
    secondLatePreparedEqRecenteredTwice]
  exact secondLateSecondRecenteredBudget

theorem secondLatePreparedMargin : (1 / 8 : Q) ≤
    secondLateCachedSource.preparedOwner.track.initial.clearance.bound -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (secondSegment.pointAt (secondMeshEndpoint 6).parameter) -
          CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (secondSegment.pointAt
              (secondEdgeRequest 6).endpoint.parameter)) := by
  rw [show secondLateCachedSource.preparedOwner =
      CCL.Riemann.PreparedSheetContinuation.prepared secondSegment
        (secondMeshEndpoint 6) secondOwnerSix (secondEdgeRequest 6) by rfl,
    secondLatePreparedEqRecenteredTwice, secondLateRecenteredTwiceEq]
  calc
    (1 / 8 : Q) ≤ 11 / 32 - 1 / 32 := by with_unfolding_all decide
    _ ≤ secondLateSecondMoving.owner.track.initial.clearance.bound -
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
              (secondSegment.pointAt (secondMeshEndpoint 6).parameter) -
            CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
              (secondSegment.pointAt
                (secondEdgeRequest 6).endpoint.parameter)) :=
      RFAP.ConstructiveFraction.sub_le_sub_direct
        secondLateSecondMovingClearance
        (by
          simp only [secondEdgeRequest]
          change RFAP.ConstructiveGaussian.Gaussian.normSq
            (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
                (secondSegment.pointAt (secondMeshEndpoint 6).parameter) -
              CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
                (secondSegment.pointAt
                  (secondMeshEndpoint (secondEdgeTarget 6)).parameter)) ≤
            (1 / 32 : Q)
          rw [quartic_eval_secondMeshEndpoint, quartic_eval_secondMeshEndpoint]
          exact secondAdjacentDisplacementLe 6)

theorem secondEdgeSixAdvanceCache :
    CCL.Riemann.PreparedSheetContinuation.ParametricQuadraticAdvanceCache
      secondSegment secondWithin (secondMeshEndpoint 6) secondOwnerSix
        (secondEdgeRequest 6) secondLateCachedSource secondLateCanonicalSmall
          (1 / 8 : Q) := by
  apply CCL.Riemann.PreparedSheetContinuation.parametricQuadraticAdvanceCache
  · simp only [secondEdgeRequest]
    change CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 6).parameter) ≠
      CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 6)).parameter)
    rw [quartic_eval_secondMeshEndpoint, quartic_eval_secondMeshEndpoint]
    exact secondAdjacentParametersDifferent 6
  · exact RFAP.ConstructiveFraction.div_pos_direct
      (qNatPositiveLate 1 (by omega)) (qNatPositiveLate 8 (by omega))
  · exact predictedLeEighthFloor 6
  · exact secondLatePreparedDominance
  · exact secondLatePreparedMargin
  · exact secondLatePreparedBudget
  · simp only [secondEdgeRequest]
    change RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 6)).parameter)) ≤ (256 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondGridParameterNormSqLe 7

private theorem secondDirectBoundsSevenFinal :
    CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (secondGridParameter 7) secondConnectorBoxThree
        (1 / 4 : Q) (3 / 4 : Q) := by
  rw [secondGridParameter_eq_reduced]
  apply CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryBoundsOfSideChecks
  all_goals with_unfolding_all decide +revert

def secondOwnerSeven :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 7).parameter)) :=
  CCL.Riemann.PreparedSheetContinuation.advanceCached secondSegment secondWithin
    (secondMeshEndpoint 6) secondOwnerSix (secondEdgeRequest 6)
      secondLateCachedSource secondLateCanonicalSmall

theorem secondOwnerSevenBoxEq :
    secondOwnerSeven.track.initial.box = secondConnectorBoxThree := by
  calc
    secondOwnerSeven.track.initial.box =
        secondLateCachedSource.preparedOwner.track.initial.box :=
      secondEdgeSixAdvanceCache.initialBox
    _ = (CCL.Riemann.PreparedSheetContinuation.recentered
        (CCL.Riemann.PreparedSheetContinuation.recentered
          secondOwnerSix)).track.initial.box := by
      rw [show secondLateCachedSource.preparedOwner =
          CCL.Riemann.PreparedSheetContinuation.prepared secondSegment
            (secondMeshEndpoint 6) secondOwnerSix (secondEdgeRequest 6) by rfl,
        secondLatePreparedEqRecenteredTwice]
    _ = secondConnectorBoxThree := by
      rw [secondLateRecenteredTwiceEq,
        secondLateSecondMoving.ownerInitialBox,
          secondLateSecondMovingBoxEq]

private theorem secondOwnerSevenAmbientLeftLeThreeQuarters :
    secondOwnerSeven.track.initial.ambientLeftClearance.bound ≤
      (3 / 4 : Q) := by
  have squareLe :
      secondLateCachedSource.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 ≤
        (3 / 4 : Q) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      secondLateCachedSource.preparedOwner.track.initial.ambientLeftClearance.positive.le
        secondLatePreparedAmbientLeftLeThreeQuarters 2
  calc
    secondOwnerSeven.track.initial.ambientLeftClearance.bound ≤
        secondLateCachedSource.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4 :=
      secondEdgeSixAdvanceCache.ambientLeftQuarterSq
    _ ≤ (3 / 4 : Q) ^ 2 / 4 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct squareLe
        (RFAP.ConstructiveFraction.inv_pos_direct
          (qNatPositiveLate 4 (by omega))).le
    _ ≤ (3 / 4 : Q) := by
      rw [show (3 / 4 : Q) ^ 2 / 4 = 9 / 64 by
        have square : (3 / 4 : Q) ^ 2 = 9 / 16 := by
          rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct]
          rw [show (3 : Q) * 3 = 9 by ring1,
            show (4 : Q) * 4 = 16 by ring1]
        rw [square]
        simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        calc
          9 * 16⁻¹ * 4⁻¹ = 9 * (16⁻¹ * 4⁻¹) := by ring1
          _ = 9 * ((16 : Q) * 4)⁻¹ :=
            congrArg (fun value : Q => 9 * value)
              (RFAP.ConstructiveFraction.inv_mul_direct 16 4).symm
          _ = 9 * (64 : Q)⁻¹ := by
            rw [show (16 : Q) * 4 = 64 by ring1],
        show (3 / 4 : Q) = 48 / 64 by
          apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
            (qNatPositiveLate 4 (by omega)).ne'
              (qNatPositiveLate 64 (by omega)).ne'
          ring1]
      exact lateNatDivLeNatDiv 9 48 64 (by decide) (by omega)

private theorem secondOwnerSevenClearanceFloor :
    CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        (1 / 8 : Q) ≤ secondOwnerSeven.track.initial.clearance.bound := by
  unfold secondOwnerSeven
  exact secondEdgeSixAdvanceCache.clearanceFloor

private theorem secondOwnerSevenDominance :
    CCL.Riemann.ExactQuadraticOwnerClearance.AmbientClearanceDominance
      secondOwnerSeven := by
  unfold secondOwnerSeven
  exact secondEdgeSixAdvanceCache.dominance

private theorem secondOwnerSevenBudget :
    CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      secondOwnerSeven := by
  unfold secondOwnerSeven
  exact secondEdgeSixAdvanceCache.budget

theorem secondEdgeSevenStep :
    CCL.Riemann.PreparedSheetContinuation.ParametricSameBoxStep
      secondSegment secondWithin (secondMeshEndpoint 7) secondOwnerSeven
        (secondEdgeRequest 7) secondConnectorBoxThree
          (1 / 4 : Q) (3 / 4 : Q) (1 / 8 : Q) := by
  apply CCL.Riemann.PreparedSheetContinuation.parametricSameBoxStep
    secondSegment secondWithin (secondMeshEndpoint 7) secondOwnerSeven
      (secondEdgeRequest 7) secondConnectorBoxThree secondOwnerSevenBoxEq
        (secondConnectorBoxThreeSmall 7) secondConnectorBoxThreeRefines
        (CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
          (1 / 8 : Q)) (predictedLeEighthFloor 7)
            secondOwnerSevenClearanceFloor secondOwnerSevenDominance
              secondOwnerSevenBudget (1 / 4 : Q) (3 / 4 : Q)
                secondOwnerSevenAmbientLeftLeThreeQuarters
  · change CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 7).parameter))
          secondConnectorBoxThree (1 / 4 : Q) (3 / 4 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondDirectBoundsSevenFinal
  · exact secondVariationLtQuarterAt 7
  · simp only [secondEdgeRequest]
    change CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 7).parameter) ≠
      CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 7)).parameter)
    rw [quartic_eval_secondMeshEndpoint, quartic_eval_secondMeshEndpoint]
    exact secondAdjacentParametersDifferent 7
  · exact RFAP.ConstructiveFraction.div_pos_direct
      (qNatPositiveLate 1 (by omega)) (qNatPositiveLate 8 (by omega))
  · exact predictedLeEighthFloor 7
  · exact secondVariationMargin 7
  · simp only [secondEdgeRequest]
    change RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 7)).parameter)) ≤ (256 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondGridParameterNormSqLe 8

def secondOwnerEight :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 8).parameter)) :=
  CCL.Riemann.PreparedSheetContinuation.advanceCached secondSegment secondWithin
    (secondMeshEndpoint 7) secondOwnerSeven (secondEdgeRequest 7)
      (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
        secondSegment (secondMeshEndpoint 7) secondOwnerSeven
          (secondEdgeRequest 7)) secondEdgeSevenStep.canonicalSmall

theorem secondOwnerEightBoxEq :
    secondOwnerEight.track.initial.box = secondConnectorBoxThree :=
  secondEdgeSevenStep.nextOwnerBox

end CCL.Riemann.ExplicitQuarticBranches
