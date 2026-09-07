import CCL.Riemann.ExplicitQuarticPreparedSecondCellContinuation

namespace CCL.Riemann.ExplicitQuarticBranches

private theorem qNatPositiveRecenter (n : Nat) (positive : 0 < n) :
    (0 : Q) < n :=
  RFAP.ConstructiveFraction.natCast_pos_direct positive

private def boxRational (num : Int) (den : Nat) (denPositive : 0 < den)
    (left right : Int)
    (bezout : left * (num.natAbs : Int) + right * (den : Int) = 1) : Q where
  num := num
  den := den
  den_pos := denPositive
  reduced := ⟨⟨left, right, bezout⟩⟩

private theorem boxRational_eq_div (num : Int) (den : Nat)
    (denPositive : 0 < den) (left right : Int)
    (bezout : left * (num.natAbs : Int) + right * (den : Int) = 1) :
    boxRational num den denPositive left right bezout =
      (num : Q) / (den : Q) := by
  let value := boxRational num den denPositive left right bezout
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (qNatPositiveRecenter den denPositive).ne'
  calc
    value * (den : Q) = (num : Q) :=
      RFAP.ConstructiveFraction.representative_mul_den value
    _ = ((num : Q) / (den : Q)) * (den : Q) :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        (qNatPositiveRecenter den denPositive).ne').symm

private def thirteenSixtyFourths : Q :=
  boxRational 13 64 (by omega) 5 (-1) (by omega)

private theorem thirteenSixtyFourths_eq :
    thirteenSixtyFourths = (13 / 64 : Q) :=
  boxRational_eq_div 13 64 (by omega) 5 (-1) (by omega)

def secondConnectorBoxOne : Box :=
  { xLower := boxRational (-1) 32 (by omega) 1 0 (by omega)
    xUpper := boxRational 47 32 (by omega) 15 (-22) (by omega)
    yLower := boxRational 13 32 (by omega) 5 (-2) (by omega)
    yUpper := boxRational 61 32 (by omega) (-11) 21 (by omega)
    x_valid := by with_unfolding_all decide
    y_valid := by with_unfolding_all decide }

theorem secondConnectorBoxOneProper : secondConnectorBoxOne.Proper := by
  constructor <;> with_unfolding_all decide

theorem firstConnectorBoxTwoProperForRecenter :
    firstConnectorBoxTwo.Proper := by
  constructor <;> with_unfolding_all decide

theorem secondConnectorBoxOneSmall (edge : Fin 8) :
    secondConnectorBoxOne.diagonalSq <
      (secondEdgeRequest edge).rootDiameter := by
  change secondConnectorBoxOne.diagonalSq < workingRootDiameter
  with_unfolding_all decide

theorem secondConnectorBoxOneRefines :
    secondConnectorBoxOne.Refines
      (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
        secondSegment) := by
  change
    -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
        secondSegment ≤ secondConnectorBoxOne.xLower ∧
      secondConnectorBoxOne.xUpper ≤
        CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          secondSegment ∧
      -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
        secondSegment ≤ secondConnectorBoxOne.yLower ∧
      secondConnectorBoxOne.yUpper ≤
        CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          secondSegment
  have threeLe :=
    CCL.Riemann.UniformSquareRootPreparation.three_le_rootAmbientRadius
      secondSegment
  exact ⟨(RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
      (by with_unfolding_all decide),
    (by with_unfolding_all decide :
      secondConnectorBoxOne.xUpper ≤ (3 : Q)).trans threeLe,
    (RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
      (by with_unfolding_all decide),
    (by with_unfolding_all decide :
      secondConnectorBoxOne.yUpper ≤ (3 : Q)).trans threeLe⟩

private theorem secondDirectBoundsTwoWeak :
    CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (secondGridParameter 2) firstConnectorBoxTwo
        (1 / 8 : Q) thirteenSixtyFourths := by
  rw [secondGridParameter_eq_reduced]
  apply
    CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryBoundsOfSideChecks
  all_goals with_unfolding_all decide +revert

theorem secondOwnerTwoClearanceLeNineSixtyFourths :
    secondOwnerTwo.track.initial.clearance.bound ≤ (9 / 64 : Q) := by
  have squareLe :
      (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
        secondSegment (secondMeshEndpoint 1) secondOwnerOne
          (secondEdgeRequest 1)).preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 ≤
        (3 / 4 : Q) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
        secondSegment (secondMeshEndpoint 1) secondOwnerOne
          (secondEdgeRequest 1)).preparedOwner.track.initial.ambientLeftClearance.positive.le
      secondEdgeOneStep.preparedAmbientLeftLe 2
  calc
    secondOwnerTwo.track.initial.clearance.bound ≤
        (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
          secondSegment (secondMeshEndpoint 1) secondOwnerOne
            (secondEdgeRequest 1)).preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4 :=
      secondEdgeOneStep.advanceCache.clearanceQuarterSq
    _ ≤ (3 / 4 : Q) ^ 2 / 4 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct squareLe
        (RFAP.ConstructiveFraction.inv_pos_direct
          (qNatPositiveRecenter 4 (by omega))).le
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

private theorem nineSixtyFourthsLeVariation : (9 / 64 : Q) ≤ 1011 / 4096 := by
  rw [show (9 / 64 : Q) = 576 / 4096 by
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      (qNatPositiveRecenter 64 (by omega)).ne'
        (qNatPositiveRecenter 4096 (by omega)).ne'
    ring1]
  simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    (RFAP.ConstructiveFraction.natCast_le_direct (by decide))
      (RFAP.ConstructiveFraction.inv_pos_direct
        (qNatPositiveRecenter 4096 (by omega))).le

private theorem thirteenSixtyFourthsLeVariation :
    (13 / 64 : Q) ≤ 1011 / 4096 := by
  rw [show (13 / 64 : Q) = 832 / 4096 by
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      (qNatPositiveRecenter 64 (by omega)).ne'
        (qNatPositiveRecenter 4096 (by omega)).ne'
    ring1]
  simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    (RFAP.ConstructiveFraction.natCast_le_direct (by decide))
      (RFAP.ConstructiveFraction.inv_pos_direct
        (qNatPositiveRecenter 4096 (by omega))).le

theorem secondOwnerTwoReady :
    CCL.Riemann.PreparedSheetContinuation.AlreadyPrepared secondSegment
      (secondMeshEndpoint 2) secondOwnerTwo (secondEdgeRequest 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [secondOwnerTwoBoxEq]
    exact secondBoxSmall 2
  · exact (predictedLeEighthFloor 2).trans
      secondEdgeOneStep.advanceCache.clearanceFloor
  · rw [secondOwnerTwoBoxEq]
    exact secondBoxRefines

theorem secondOwnerTwoNotCarries :
    ¬ CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
        (secondMeshEndpoint 2).parameter
          (secondEdgeRequest 2).endpoint.parameter <
      secondOwnerTwo.track.initial.clearance.bound := by
  apply not_lt_of_ge
  rw [show CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
      (secondMeshEndpoint 2).parameter
        (secondEdgeRequest 2).endpoint.parameter = (1011 / 4096 : Q) by
    exact secondMeshVariationEq 2]
  exact secondOwnerTwoClearanceLeNineSixtyFourths.trans
    nineSixtyFourthsLeVariation

theorem secondOwnerTwoStrengthenedClearanceLeThirteenSixtyFourths :
    (CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
      secondOwnerTwo).track.initial.clearance.bound ≤ (13 / 64 : Q) := by
  let cache : CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 2).parameter))
      secondOwnerTwo.track.initial.box (1 / 8 : Q) thirteenSixtyFourths := by
    rw [secondOwnerTwoBoxEq]
    change CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 2).parameter))
          firstConnectorBoxTwo (1 / 8 : Q) thirteenSixtyFourths
    rw [quartic_eval_secondMeshEndpoint]
    exact secondDirectBoundsTwoWeak
  rw [CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max
    secondOwnerTwo cache.leftNonzero cache.rightNonzero cache.bottomNonzero
      cache.topNonzero]
  apply max_le
  · exact secondOwnerTwoClearanceLeNineSixtyFourths.trans
      (by
        rw [show (9 / 64 : Q) = 576 / 4096 by
          apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
            (qNatPositiveRecenter 64 (by omega)).ne'
              (qNatPositiveRecenter 4096 (by omega)).ne'
          ring1,
          show (13 / 64 : Q) = 832 / 4096 by
          apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
            (qNatPositiveRecenter 64 (by omega)).ne'
              (qNatPositiveRecenter 4096 (by omega)).ne'
          ring1]
        simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (RFAP.ConstructiveFraction.natCast_le_direct (by decide))
            (RFAP.ConstructiveFraction.inv_pos_direct
              (qNatPositiveRecenter 4096 (by omega))).le)
  · exact cache.le_upper.trans_eq thirteenSixtyFourths_eq

theorem secondOwnerTwoStrengthenedNotCarries :
    ¬ CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
        (secondMeshEndpoint 2).parameter
          (secondEdgeRequest 2).endpoint.parameter <
      (CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        secondOwnerTwo).track.initial.clearance.bound := by
  apply not_lt_of_ge
  rw [show CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
      (secondMeshEndpoint 2).parameter
        (secondEdgeRequest 2).endpoint.parameter = (1011 / 4096 : Q) by
    exact secondMeshVariationEq 2]
  exact secondOwnerTwoStrengthenedClearanceLeThirteenSixtyFourths.trans
    thirteenSixtyFourthsLeVariation

theorem secondFirstRecenterBoxProjection :
    CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenterBox?
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 2).parameter))
        secondOwnerTwo.parameterNonzero firstConnectorBoxTwo
          firstConnectorBoxTwoProperForRecenter = some secondConnectorBoxOne := by
  change CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenterBox?
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 2).parameter))
        secondOwnerTwo.parameterNonzero firstConnectorBoxTwo
          firstConnectorBoxTwoProperForRecenter = some secondConnectorBoxOne
  have parameterNonzero : secondGridReducedParameter 2 ≠ 0 := by
    with_unfolding_all decide
  have computed :
      CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenterBox?
          (secondGridReducedParameter 2) parameterNonzero firstConnectorBoxTwo
            firstConnectorBoxTwoProperForRecenter = some secondConnectorBoxOne := by
    with_unfolding_all rfl
  simpa only [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
    using computed

end CCL.Riemann.ExplicitQuarticBranches
