import CCL.Riemann.ExplicitQuarticPreparedSecondCellRecenter

namespace CCL.Riemann.ExplicitQuarticBranches

def secondFirstMovingCache :
    { reset : CCL.Riemann.ExactQuadraticOwnerClearance.MovingRecenter
        _ secondOwnerTwo //
      CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
        secondOwnerTwo = some reset } := by
  generalize found :
    CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
      secondOwnerTwo = result
  cases result with
  | none =>
      have succeeds : Option.map
          (fun reset => reset.ownerBox)
          (CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
            secondOwnerTwo) = some secondConnectorBoxOne := by
        rw [CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
          secondOwnerTwo firstConnectorBoxTwo
            firstConnectorBoxTwoProperForRecenter secondOwnerTwoBoxEq,
          secondFirstRecenterBoxProjection]
      rw [found] at succeeds
      contradiction
  | some reset => exact ⟨reset, rfl⟩

def secondFirstMoving := secondFirstMovingCache.1

theorem secondFirstMovingFound :
    CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
      secondOwnerTwo = some secondFirstMoving :=
  secondFirstMovingCache.2

theorem secondFirstRecenteredEq :
    CCL.Riemann.PreparedSheetContinuation.recentered secondOwnerTwo =
      secondFirstMoving.owner :=
  CCL.Riemann.PreparedSheetContinuation.recentered_eq_of_movingRecenter_eq_some
    secondOwnerTwo secondFirstMoving secondFirstMovingFound

theorem secondFirstMovingBoxEq :
    secondFirstMoving.ownerBox = secondConnectorBoxOne := by
  have mapped : Option.map
      (fun reset => reset.ownerBox)
      (CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
        secondOwnerTwo) = some secondConnectorBoxOne := by
    rw [CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
      secondOwnerTwo firstConnectorBoxTwo
        firstConnectorBoxTwoProperForRecenter secondOwnerTwoBoxEq,
      secondFirstRecenterBoxProjection]
  rw [secondFirstMovingFound] at mapped
  exact Option.some.inj mapped

theorem secondFirstMovingClearance : (21 / 32 : Q) ≤
    secondFirstMoving.owner.track.initial.clearance.bound := by
  rw [secondFirstMoving.ownerDirectClearanceBound]
  apply CCL.Riemann.ExactQuadraticOwnerClearance.le_directBoundaryClearance_bound
  all_goals rw [secondFirstMovingBoxEq]
  case leftLe =>
    change (21 / 32 : Q) ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 2).parameter))
            secondConnectorBoxOne secondConnectorBoxOne.xLower
    rw [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
    with_unfolding_all decide
  case rightLe =>
    change (21 / 32 : Q) ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 2).parameter))
            secondConnectorBoxOne secondConnectorBoxOne.xUpper
    rw [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
    with_unfolding_all decide
  case bottomLe =>
    change (21 / 32 : Q) ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 2).parameter))
            secondConnectorBoxOne secondConnectorBoxOne.yLower
    rw [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
    with_unfolding_all decide
  case topLe =>
    change (21 / 32 : Q) ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 2).parameter))
            secondConnectorBoxOne secondConnectorBoxOne.yUpper
    rw [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
    with_unfolding_all decide

theorem secondFirstRecenteredReady :
    CCL.Riemann.PreparedSheetContinuation.AlreadyPrepared secondSegment
      (secondMeshEndpoint 2)
        (CCL.Riemann.PreparedSheetContinuation.recentered secondOwnerTwo)
          (secondEdgeRequest 2) := by
  rw [secondFirstRecenteredEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [secondFirstMoving.ownerInitialBox, secondFirstMovingBoxEq]
    exact secondConnectorBoxOneSmall 2
  · have marginLe :
        CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
          secondSegment ≤ (1 / 4 : Q) := by
      rw [secondDerivativeMarginEq]
      exact firstConnectorDerivativeMarginLe
    exact
      (CCL.Riemann.UniformSquareRootPreparation.predictedClearance_le_oneOver128
        secondSegment (secondEdgeRequest 2).rootDiameter
          (secondEdgeRequest 2).rootDiameterPositive marginLe).trans
        ((show (1 / (16 * 8) : Q) ≤ 21 / 32 by
          with_unfolding_all decide).trans secondFirstMovingClearance)
  · rw [secondFirstMoving.ownerInitialBox, secondFirstMovingBoxEq]
    exact secondConnectorBoxOneRefines

theorem secondFirstRecenteredCarries :
    CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
        (secondMeshEndpoint 2).parameter
          (secondEdgeRequest 2).endpoint.parameter <
      (CCL.Riemann.PreparedSheetContinuation.recentered
        secondOwnerTwo).track.initial.clearance.bound := by
  rw [secondFirstRecenteredEq]
  exact (secondVariationLtQuarterAt 2).trans_le
    ((show (1 / 4 : Q) ≤ 21 / 32 by with_unfolding_all decide).trans
      secondFirstMovingClearance)

theorem secondFirstPreparedEqRecentered :
    CCL.Riemann.PreparedSheetContinuation.prepared secondSegment
        (secondMeshEndpoint 2) secondOwnerTwo (secondEdgeRequest 2) =
      CCL.Riemann.PreparedSheetContinuation.recentered secondOwnerTwo :=
  CCL.Riemann.PreparedSheetContinuation.prepared_eq_recentered_of_ready
    secondSegment (secondMeshEndpoint 2) secondOwnerTwo (secondEdgeRequest 2)
      secondOwnerTwoReady secondOwnerTwoNotCarries
        secondOwnerTwoStrengthenedNotCarries secondFirstRecenteredReady
          secondFirstRecenteredCarries

theorem secondFirstCanonicalSmall :
    CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
        (secondMeshEndpoint 2).parameter
          (secondEdgeRequest 2).endpoint.parameter <
      (CCL.Riemann.PreparedSheetContinuation.prepared secondSegment
        (secondMeshEndpoint 2) secondOwnerTwo
          (secondEdgeRequest 2)).track.initial.clearance.bound :=
  CCL.Riemann.PreparedSheetContinuation.variation_lt_prepared_of_ready_of_recenteredCarries
    secondSegment (secondMeshEndpoint 2) secondOwnerTwo (secondEdgeRequest 2)
      secondOwnerTwoReady secondFirstRecenteredReady
        secondFirstRecenteredCarries

def secondFirstCachedSource :=
  CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical secondSegment
    (secondMeshEndpoint 2) secondOwnerTwo (secondEdgeRequest 2)

theorem secondFirstRecenteredAmbientLeftLeThreeQuarters :
    (CCL.Riemann.PreparedSheetContinuation.recentered
      secondOwnerTwo).track.initial.ambientLeftClearance.bound ≤
        (3 / 4 : Q) := by
  rw [secondFirstRecenteredEq,
    secondFirstMoving.ownerAmbientLeftClearanceBound,
    CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance_bound,
    secondFirstMovingBoxEq]
  change min
      (CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
          (secondSegment.pointAt (secondMeshEndpoint 2).parameter))
            secondConnectorBoxOne secondConnectorBoxOne.xLower)
      (min
        (CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
          (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
            (secondSegment.pointAt (secondMeshEndpoint 2).parameter))
              secondConnectorBoxOne secondConnectorBoxOne.xUpper)
        (min
          (CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
              (secondSegment.pointAt (secondMeshEndpoint 2).parameter))
                secondConnectorBoxOne secondConnectorBoxOne.yLower)
          (CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
              (secondSegment.pointAt (secondMeshEndpoint 2).parameter))
                secondConnectorBoxOne secondConnectorBoxOne.yUpper))) ≤
      (3 / 4 : Q)
  rw [quartic_eval_secondMeshEndpoint, secondGridParameter_eq_reduced]
  with_unfolding_all decide

theorem secondFirstPreparedAmbientLeftLeThreeQuarters :
    secondFirstCachedSource.preparedOwner.track.initial.ambientLeftClearance.bound ≤
      (3 / 4 : Q) := by
  rw [show secondFirstCachedSource.preparedOwner =
      CCL.Riemann.PreparedSheetContinuation.prepared secondSegment
        (secondMeshEndpoint 2) secondOwnerTwo (secondEdgeRequest 2) by rfl,
    secondFirstPreparedEqRecentered]
  exact secondFirstRecenteredAmbientLeftLeThreeQuarters

theorem secondFirstRecenteredBudget :
    CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      (CCL.Riemann.PreparedSheetContinuation.recentered secondOwnerTwo) := by
  rw [secondFirstRecenteredEq]
  apply CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientBudget_of_box
    secondFirstMoving.owner secondConnectorBoxOne
  · exact secondFirstMoving.ownerInitialBox.trans secondFirstMovingBoxEq
  · exact secondFirstMoving.ownerAmbientBox.trans secondFirstMovingBoxEq
  · change RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 2).parameter)) ≤ (256 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondGridParameterNormSqLe 2
  all_goals with_unfolding_all decide

theorem secondFirstPreparedDominance :
    CCL.Riemann.ExactQuadraticOwnerClearance.AmbientClearanceDominance
      secondFirstCachedSource.preparedOwner :=
  CCL.Riemann.PreparedSheetContinuation.prepared_ambientClearanceDominance_of_ready_of_recenteredCarries
    secondSegment (secondMeshEndpoint 2) secondOwnerTwo (secondEdgeRequest 2)
      secondOwnerTwoReady secondFirstRecenteredReady
        secondFirstRecenteredCarries secondEdgeOneStep.advanceCache.dominance

theorem secondFirstPreparedBudget :
    CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      secondFirstCachedSource.preparedOwner :=
  CCL.Riemann.PreparedSheetContinuation.prepared_quadraticAmbientBudget_of_ready_of_recenteredCarries
    secondSegment (secondMeshEndpoint 2) secondOwnerTwo (secondEdgeRequest 2)
      secondOwnerTwoReady secondFirstRecenteredReady
        secondFirstRecenteredCarries secondEdgeOneStep.advanceCache.budget
          secondFirstRecenteredBudget

theorem secondFirstRecenteredMargin : (1 / 2 : Q) ≤
    (CCL.Riemann.PreparedSheetContinuation.recentered
        secondOwnerTwo).track.initial.clearance.bound -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (secondSegment.pointAt (secondMeshEndpoint 2).parameter) -
          CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (secondSegment.pointAt
              (secondEdgeRequest 2).endpoint.parameter)) := by
  calc
    (1 / 2 : Q) ≤ 21 / 32 - 1 / 32 := by with_unfolding_all decide
    _ ≤ (CCL.Riemann.PreparedSheetContinuation.recentered
          secondOwnerTwo).track.initial.clearance.bound -
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
              (secondSegment.pointAt (secondMeshEndpoint 2).parameter) -
            CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
              (secondSegment.pointAt
                (secondEdgeRequest 2).endpoint.parameter)) :=
      RFAP.ConstructiveFraction.sub_le_sub_direct
        ((by rw [secondFirstRecenteredEq]; exact secondFirstMovingClearance))
        ((by
          simp only [secondEdgeRequest]
          change RFAP.ConstructiveGaussian.Gaussian.normSq
            (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
                (secondSegment.pointAt (secondMeshEndpoint 2).parameter) -
              CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
                (secondSegment.pointAt
                  (secondMeshEndpoint (secondEdgeTarget 2)).parameter)) ≤
            (1 / 32 : Q)
          rw [quartic_eval_secondMeshEndpoint, quartic_eval_secondMeshEndpoint]
          exact secondAdjacentDisplacementLe 2))

theorem secondFirstPreparedMargin : (1 / 2 : Q) ≤
    secondFirstCachedSource.preparedOwner.track.initial.clearance.bound -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (secondSegment.pointAt (secondMeshEndpoint 2).parameter) -
          CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (secondSegment.pointAt
              (secondEdgeRequest 2).endpoint.parameter)) := by
  rw [show secondFirstCachedSource.preparedOwner =
      CCL.Riemann.PreparedSheetContinuation.prepared secondSegment
        (secondMeshEndpoint 2) secondOwnerTwo (secondEdgeRequest 2) by rfl,
    secondFirstPreparedEqRecentered]
  exact secondFirstRecenteredMargin

theorem secondEdgeTwoAdvanceCache :
    CCL.Riemann.PreparedSheetContinuation.QuadraticAdvanceCache
      secondSegment secondWithin (secondMeshEndpoint 2) secondOwnerTwo
        (secondEdgeRequest 2) secondFirstCachedSource
          secondFirstCanonicalSmall := by
  apply CCL.Riemann.PreparedSheetContinuation.quadraticAdvanceCache
  · simp only [secondEdgeRequest]
    change CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 2).parameter) ≠
      CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 2)).parameter)
    rw [quartic_eval_secondMeshEndpoint, quartic_eval_secondMeshEndpoint]
    exact secondAdjacentParametersDifferent 2
  · rw [secondDerivativeMarginEq]
    exact firstConnectorDerivativeMarginLe
  · exact secondFirstPreparedDominance
  · exact secondFirstPreparedMargin
  · exact secondFirstPreparedBudget
  · simp only [secondEdgeRequest]
    change RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 2)).parameter)) ≤ (256 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondGridParameterNormSqLe 3

end CCL.Riemann.ExplicitQuarticBranches
