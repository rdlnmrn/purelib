import CCL.Riemann.ExplicitQuarticPreparedSecondCellFirstRecenter

namespace CCL.Riemann.ExplicitQuarticBranches

private theorem secondDirectBoundsThree :
    CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (secondGridParameter 3) secondConnectorBoxOne
        (1 / 4 : Q) (3 / 4 : Q) := by
  rw [secondGridParameter_eq_reduced]
  apply
    CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryBoundsOfSideChecks
  all_goals with_unfolding_all decide +revert

private theorem secondDirectBoundsFour :
    CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (secondGridParameter 4) secondConnectorBoxOne
        (1 / 4 : Q) (3 / 4 : Q) := by
  rw [secondGridParameter_eq_reduced]
  apply
    CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryBoundsOfSideChecks
  all_goals with_unfolding_all decide +revert

private theorem secondDirectBoundsFive :
    CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (secondGridParameter 5) secondConnectorBoxOne
        (1 / 4 : Q) (3 / 4 : Q) := by
  rw [secondGridParameter_eq_reduced]
  apply
    CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryBoundsOfSideChecks
  all_goals with_unfolding_all decide +revert

def secondOwnerThree :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 3).parameter)) :=
  CCL.Riemann.PreparedSheetContinuation.advanceCached secondSegment secondWithin
    (secondMeshEndpoint 2) secondOwnerTwo (secondEdgeRequest 2)
      secondFirstCachedSource secondFirstCanonicalSmall

theorem secondOwnerThreeBoxEq :
    secondOwnerThree.track.initial.box = secondConnectorBoxOne := by
  calc
    secondOwnerThree.track.initial.box =
        secondFirstCachedSource.preparedOwner.track.initial.box :=
      secondEdgeTwoAdvanceCache.initialBox
    _ = (CCL.Riemann.PreparedSheetContinuation.recentered
        secondOwnerTwo).track.initial.box := by
      rw [show secondFirstCachedSource.preparedOwner =
          CCL.Riemann.PreparedSheetContinuation.prepared secondSegment
            (secondMeshEndpoint 2) secondOwnerTwo (secondEdgeRequest 2) by rfl,
        secondFirstPreparedEqRecentered]
    _ = secondConnectorBoxOne := by
      rw [secondFirstRecenteredEq, secondFirstMoving.ownerInitialBox,
        secondFirstMovingBoxEq]

theorem secondOwnerThreeAmbientLeftLeThreeQuarters :
    secondOwnerThree.track.initial.ambientLeftClearance.bound ≤
      (3 / 4 : Q) := by
  have squareLe :
      secondFirstCachedSource.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 ≤
        (3 / 4 : Q) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      secondFirstCachedSource.preparedOwner.track.initial.ambientLeftClearance.positive.le
        secondFirstPreparedAmbientLeftLeThreeQuarters 2
  calc
    secondOwnerThree.track.initial.ambientLeftClearance.bound ≤
        secondFirstCachedSource.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4 :=
      secondEdgeTwoAdvanceCache.ambientLeftQuarterSq
    _ ≤ (3 / 4 : Q) ^ 2 / 4 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct squareLe
        (RFAP.ConstructiveFraction.inv_pos_direct (by decide)).le
    _ ≤ (3 / 4 : Q) := by with_unfolding_all decide

theorem secondEdgeThreeStep :
    CCL.Riemann.PreparedSheetContinuation.ParametricSameBoxStep
      secondSegment secondWithin (secondMeshEndpoint 3) secondOwnerThree
        (secondEdgeRequest 3) secondConnectorBoxOne
          (1 / 4 : Q) (3 / 4 : Q) (1 / 8 : Q) := by
  apply CCL.Riemann.PreparedSheetContinuation.parametricSameBoxStep
    secondSegment secondWithin (secondMeshEndpoint 3) secondOwnerThree
      (secondEdgeRequest 3) secondConnectorBoxOne secondOwnerThreeBoxEq
        (secondConnectorBoxOneSmall 3) secondConnectorBoxOneRefines
        CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloor
          ((predictedLeEighthFloor 3).trans eighthFloorLeHalfFloor)
            secondEdgeTwoAdvanceCache.clearanceFloor
              secondEdgeTwoAdvanceCache.dominance
                secondEdgeTwoAdvanceCache.budget
                  (1 / 4 : Q) (3 / 4 : Q)
                    secondOwnerThreeAmbientLeftLeThreeQuarters
  · change CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 3).parameter))
          secondConnectorBoxOne (1 / 4 : Q) (3 / 4 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondDirectBoundsThree
  · exact secondVariationLtQuarterAt 3
  · simp only [secondEdgeRequest]
    change CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 3).parameter) ≠
      CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 3)).parameter)
    rw [quartic_eval_secondMeshEndpoint, quartic_eval_secondMeshEndpoint]
    exact secondAdjacentParametersDifferent 3
  · exact RFAP.ConstructiveFraction.div_pos_direct (by decide) (by decide)
  · exact predictedLeEighthFloor 3
  · exact secondVariationMargin 3
  · simp only [secondEdgeRequest]
    change RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 3)).parameter)) ≤ (256 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondGridParameterNormSqLe 4

def secondOwnerFour :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 4).parameter)) :=
  CCL.Riemann.PreparedSheetContinuation.advanceCached secondSegment secondWithin
    (secondMeshEndpoint 3) secondOwnerThree (secondEdgeRequest 3)
      (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
        secondSegment (secondMeshEndpoint 3) secondOwnerThree
          (secondEdgeRequest 3)) secondEdgeThreeStep.canonicalSmall

theorem secondOwnerFourBoxEq :
    secondOwnerFour.track.initial.box = secondConnectorBoxOne :=
  secondEdgeThreeStep.nextOwnerBox

private theorem secondOwnerFourAmbientLeftLeThreeQuarters :
    secondOwnerFour.track.initial.ambientLeftClearance.bound ≤
      (3 / 4 : Q) :=
  secondEdgeThreeStep.nextAmbientLeftLeQuarter.trans
    (by with_unfolding_all decide)

private theorem secondOwnerFourClearanceFloor :
    CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        (1 / 8 : Q) ≤
      secondOwnerFour.track.initial.clearance.bound := by
  unfold secondOwnerFour
  exact secondEdgeThreeStep.advanceCache.clearanceFloor

private theorem secondOwnerFourDominance :
    CCL.Riemann.ExactQuadraticOwnerClearance.AmbientClearanceDominance
      secondOwnerFour := by
  unfold secondOwnerFour
  exact secondEdgeThreeStep.advanceCache.dominance

private theorem secondOwnerFourBudget :
    CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      secondOwnerFour := by
  unfold secondOwnerFour
  exact secondEdgeThreeStep.advanceCache.budget

theorem secondEdgeFourStep :
    CCL.Riemann.PreparedSheetContinuation.ParametricSameBoxStep
      secondSegment secondWithin (secondMeshEndpoint 4) secondOwnerFour
        (secondEdgeRequest 4) secondConnectorBoxOne
          (1 / 4 : Q) (3 / 4 : Q) (1 / 8 : Q) := by
  apply CCL.Riemann.PreparedSheetContinuation.parametricSameBoxStep
    secondSegment secondWithin (secondMeshEndpoint 4) secondOwnerFour
      (secondEdgeRequest 4) secondConnectorBoxOne secondOwnerFourBoxEq
        (secondConnectorBoxOneSmall 4) secondConnectorBoxOneRefines
        (CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
          (1 / 8 : Q)) (predictedLeEighthFloor 4)
            secondOwnerFourClearanceFloor
              secondOwnerFourDominance
                secondOwnerFourBudget
                  (1 / 4 : Q) (3 / 4 : Q)
                    secondOwnerFourAmbientLeftLeThreeQuarters
  · change CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 4).parameter))
          secondConnectorBoxOne (1 / 4 : Q) (3 / 4 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondDirectBoundsFour
  · exact secondVariationLtQuarterAt 4
  · simp only [secondEdgeRequest]
    change CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 4).parameter) ≠
      CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 4)).parameter)
    rw [quartic_eval_secondMeshEndpoint, quartic_eval_secondMeshEndpoint]
    exact secondAdjacentParametersDifferent 4
  · exact RFAP.ConstructiveFraction.div_pos_direct (by decide) (by decide)
  · exact predictedLeEighthFloor 4
  · exact secondVariationMargin 4
  · simp only [secondEdgeRequest]
    change RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 4)).parameter)) ≤ (256 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondGridParameterNormSqLe 5

def secondOwnerFive :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 5).parameter)) :=
  CCL.Riemann.PreparedSheetContinuation.advanceCached secondSegment secondWithin
    (secondMeshEndpoint 4) secondOwnerFour (secondEdgeRequest 4)
      (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
        secondSegment (secondMeshEndpoint 4) secondOwnerFour
          (secondEdgeRequest 4)) secondEdgeFourStep.canonicalSmall

theorem secondOwnerFiveBoxEq :
    secondOwnerFive.track.initial.box = secondConnectorBoxOne :=
  secondEdgeFourStep.nextOwnerBox

private theorem secondOwnerFiveAmbientLeftLeThreeQuarters :
    secondOwnerFive.track.initial.ambientLeftClearance.bound ≤
      (3 / 4 : Q) :=
  secondEdgeFourStep.nextAmbientLeftLeQuarter.trans
    (by with_unfolding_all decide)

private theorem secondOwnerFiveClearanceFloor :
    CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        (1 / 8 : Q) ≤
      secondOwnerFive.track.initial.clearance.bound := by
  unfold secondOwnerFive
  exact secondEdgeFourStep.advanceCache.clearanceFloor

private theorem secondOwnerFiveDominance :
    CCL.Riemann.ExactQuadraticOwnerClearance.AmbientClearanceDominance
      secondOwnerFive := by
  unfold secondOwnerFive
  exact secondEdgeFourStep.advanceCache.dominance

private theorem secondOwnerFiveBudget :
    CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      secondOwnerFive := by
  unfold secondOwnerFive
  exact secondEdgeFourStep.advanceCache.budget

theorem secondEdgeFiveStep :
    CCL.Riemann.PreparedSheetContinuation.ParametricSameBoxStep
      secondSegment secondWithin (secondMeshEndpoint 5) secondOwnerFive
        (secondEdgeRequest 5) secondConnectorBoxOne
          (1 / 4 : Q) (3 / 4 : Q) (1 / 8 : Q) := by
  apply CCL.Riemann.PreparedSheetContinuation.parametricSameBoxStep
    secondSegment secondWithin (secondMeshEndpoint 5) secondOwnerFive
      (secondEdgeRequest 5) secondConnectorBoxOne secondOwnerFiveBoxEq
        (secondConnectorBoxOneSmall 5) secondConnectorBoxOneRefines
        (CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
          (1 / 8 : Q)) (predictedLeEighthFloor 5)
            secondOwnerFiveClearanceFloor
              secondOwnerFiveDominance
                secondOwnerFiveBudget
                  (1 / 4 : Q) (3 / 4 : Q)
                    secondOwnerFiveAmbientLeftLeThreeQuarters
  · change CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 5).parameter))
          secondConnectorBoxOne (1 / 4 : Q) (3 / 4 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondDirectBoundsFive
  · exact secondVariationLtQuarterAt 5
  · simp only [secondEdgeRequest]
    change CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 5).parameter) ≠
      CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 5)).parameter)
    rw [quartic_eval_secondMeshEndpoint, quartic_eval_secondMeshEndpoint]
    exact secondAdjacentParametersDifferent 5
  · exact RFAP.ConstructiveFraction.div_pos_direct (by decide) (by decide)
  · exact predictedLeEighthFloor 5
  · exact secondVariationMargin 5
  · simp only [secondEdgeRequest]
    change RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 5)).parameter)) ≤ (256 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondGridParameterNormSqLe 6

def secondOwnerSix :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 6).parameter)) :=
  CCL.Riemann.PreparedSheetContinuation.advanceCached secondSegment secondWithin
    (secondMeshEndpoint 5) secondOwnerFive (secondEdgeRequest 5)
      (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
        secondSegment (secondMeshEndpoint 5) secondOwnerFive
          (secondEdgeRequest 5)) secondEdgeFiveStep.canonicalSmall

theorem secondOwnerSixBoxEq :
    secondOwnerSix.track.initial.box = secondConnectorBoxOne :=
  secondEdgeFiveStep.nextOwnerBox

end CCL.Riemann.ExplicitQuarticBranches
