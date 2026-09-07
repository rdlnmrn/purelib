import CCL.Riemann.ExplicitQuarticPreparedSecondCellGrid

/-!
# Retained continuation into the second quartic connector cell

This module splices the terminal owner of the first certified outer cell into
the second cell, retains the inherited exact box for its first two dyadic
edges, and records the state needed for the first finite moving recenter.
-/

namespace CCL.Riemann.ExplicitQuarticBranches

private theorem finNineCasesContinuation (index : Fin 9) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
  rcases index with ⟨value, bound⟩
  omega0

private theorem finEightCasesContinuation (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  omega0

private theorem qNatPositiveContinuation (n : Nat) (positive : 0 < n) :
    (0 : Q) < n :=
  RFAP.ConstructiveFraction.natCast_pos_direct positive

theorem firstFinishPointEqSecondStart :
    firstConnectorSegment.pointAt
        (firstConnectorMeshEndpoint 8).parameter =
      secondSegment.pointAt (secondMeshEndpoint 0).parameter := by
  rw [show (firstConnectorMeshEndpoint 8).parameter = 1 by rfl,
    firstConnectorSegment_pointAt,
      show secondSegment.pointAt (secondMeshEndpoint 0).parameter =
        point (-1) (-1 / 2) by exact secondSegment_pointAt_zero]
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · change (-5 / 4 : Q) + 1 * ((-1) - (-5 / 4)) = -1
    ring1
  · change (-1 / 2 : Q) + 1 * ((-1 / 2) - (-1 / 2)) = -1 / 2
    ring1

def secondOwnerZero :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 0).parameter)) := by
  cases firstFinishPointEqSecondStart
  exact firstConnectorOwnerEight

theorem secondOwnerZeroBoxEq :
    secondOwnerZero.track.initial.box = firstConnectorBoxTwo := by
  unfold secondOwnerZero
  exact firstConnectorOwnerEightBoxEq

theorem secondBoxSmall (edge : Fin 8) :
    firstConnectorBoxTwo.diagonalSq <
      (secondEdgeRequest edge).rootDiameter := by
  change firstConnectorBoxTwo.diagonalSq < workingRootDiameter
  with_unfolding_all decide

theorem secondBoxRefines :
    firstConnectorBoxTwo.Refines
      (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
        secondSegment) := by
  change
    -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
        secondSegment ≤ firstConnectorBoxTwo.xLower ∧
      firstConnectorBoxTwo.xUpper ≤
        CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          secondSegment ∧
      -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
        secondSegment ≤ firstConnectorBoxTwo.yLower ∧
      firstConnectorBoxTwo.yUpper ≤
        CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          secondSegment
  have threeLe :=
    CCL.Riemann.UniformSquareRootPreparation.three_le_rootAmbientRadius
      secondSegment
  exact ⟨(RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
      (by with_unfolding_all decide),
    (by with_unfolding_all decide :
      firstConnectorBoxTwo.xUpper ≤ (3 : Q)).trans threeLe,
    (RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
      (by with_unfolding_all decide),
    (by with_unfolding_all decide :
      firstConnectorBoxTwo.yUpper ≤ (3 : Q)).trans threeLe⟩

theorem predictedLeEighthFloor (edge : Fin 8) :
    CCL.Riemann.PreparedSheetContinuation.preparedClearanceLower
      secondSegment (secondMeshEndpoint (secondEdgeSource edge))
        (secondEdgeRequest edge) ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        (1 / 8 : Q) := by
  change CCL.Riemann.UniformSquareRootPreparation.predictedClearance
      secondSegment workingRootDiameter ≤
    CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
      (1 / 8 : Q)
  have cached := secondPreparedClearanceLeTransportFloor
  change CCL.Riemann.UniformSquareRootPreparation.predictedClearance
      secondSegment workingRootDiameter ≤
    CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
      (1 / 8 : Q) at cached
  exact cached

theorem eighthFloorLeHalfFloor :
    CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        (1 / 8 : Q) ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloor := by
  unfold CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
    CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloor
  have marginLe : (1 / 8 : Q) ≤ 1 / 2 :=
    RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
      (show (0 : Q) ≤ 1 by exact (qNatPositiveContinuation 1 (by omega)).le)
      (qNatPositiveContinuation 2 (by omega))
      (RFAP.ConstructiveFraction.natCast_le_direct
        (m := 2) (n := 8) (by decide))
  have marginNonnegative : (0 : Q) ≤ 1 / 8 :=
    RFAP.ConstructiveFraction.div_nonneg_direct
      (qNatPositiveContinuation 1 (by omega)).le
      (qNatPositiveContinuation 8 (by omega)).le
  have squareLe : (1 / 8 : Q) ^ 2 ≤ (1 / 2 : Q) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct marginNonnegative marginLe 2
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct squareLe
    (RFAP.ConstructiveFraction.inv_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct
        (qNatPositiveContinuation 4 (by omega))
          (qNatPositiveContinuation 65536 (by omega)))).le

private theorem pointNormLe256
    (real imaginary : Q)
    (coefficientLe : real ^ 2 + imaginary ^ 2 ≤ 281474976710656) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (real * (1 / 1048576)) (imaginary * (1 / 1048576))) ≤
      (256 : Q) := by
  unfold RFAP.ConstructiveGaussian.Gaussian.normSq
  change (real * (1 / 1048576 : Q)) ^ 2 +
      (imaginary * (1 / 1048576 : Q)) ^ 2 ≤ 256
  have unitSquareNonnegative : (0 : Q) ≤ (1 / 1048576 : Q) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  calc
    (real * (1 / 1048576 : Q)) ^ 2 +
        (imaginary * (1 / 1048576 : Q)) ^ 2 =
      (real ^ 2 + imaginary ^ 2) * (1 / 1048576 : Q) ^ 2 := by ring1
    _ ≤ 281474976710656 * (1 / 1048576 : Q) ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        coefficientLe unitSquareNonnegative
    _ = (256 : Q) := by
      have cancel : (1 / 1048576 : Q) * 1048576 = 1 :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          (qNatPositiveContinuation 1048576 (by omega)).ne'
      rw [pow_two]
      calc
        281474976710656 *
            ((1 / 1048576 : Q) * (1 / 1048576)) =
          256 * (((1 / 1048576 : Q) * 1048576) *
            ((1 / 1048576 : Q) * 1048576)) := by ring1
        _ = 256 := by
          rw [cancel]
          ring1

theorem secondGridParameterNormSqLe (index : Fin 9) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (secondGridParameter index) ≤ (256 : Q) := by
  rcases finNineCasesContinuation index with h | h | h | h | h | h | h | h | h
  all_goals subst index
  all_goals simp only [secondGridParameter]
  all_goals apply pointNormLe256
  · rw [show (((-1507328 : Q) ^ 2 + 1572864 ^ 2)) =
      (4745938862080 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  · rw [show (((-1535615 : Q) ^ 2 + 1398720 ^ 2)) =
      (4314531066625 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  · rw [show (((-1555440 : Q) ^ 2 + 1236480 ^ 2)) =
      (3948276384000 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  · rw [show (((-1567535 : Q) ^ 2 + 1085760 ^ 2)) =
      (3636040753825 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  · rw [show (((-1572608 : Q) ^ 2 + 946176 ^ 2)) =
      (3368344944640 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  · rw [show (((-1571343 : Q) ^ 2 + 817344 ^ 2)) =
      (3137170037985 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  · rw [show (((-1564400 : Q) ^ 2 + 698880 ^ 2)) =
      (2935780614400 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  · rw [show (((-1552415 : Q) ^ 2 + 590400 ^ 2)) =
      (2758564492225 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  · rw [show (((-1536000 : Q) ^ 2 + 491520 ^ 2)) =
      (2600887910400 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)

private theorem secondDirectBoundsZero :
    CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (secondGridParameter 0) firstConnectorBoxTwo
        (1 / 4 : Q) (3 / 4 : Q) := by
  rw [secondGridParameter_eq_reduced]
  apply
    CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryBoundsOfSideChecks
  all_goals with_unfolding_all decide +revert

private theorem secondDirectBoundsOne :
    CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (secondGridParameter 1) firstConnectorBoxTwo
        (1 / 4 : Q) (3 / 4 : Q) := by
  rw [secondGridParameter_eq_reduced]
  apply
    CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryBoundsOfSideChecks
  all_goals with_unfolding_all decide +revert

private theorem secondOwnerZeroFloor :
    CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        (1 / 8 : Q) ≤ secondOwnerZero.track.initial.clearance.bound := by
  unfold secondOwnerZero
  exact eighthFloorLeHalfFloor.trans
    firstConnectorEdgeSevenStep.advanceCache.clearanceFloor

private theorem secondOwnerZeroAmbientLeftLe :
    secondOwnerZero.track.initial.ambientLeftClearance.bound ≤ (3 / 4 : Q) := by
  unfold secondOwnerZero
  exact firstConnectorEdgeSevenStep.nextAmbientLeftLeNineSixteenths.trans
    (by decide)

private theorem secondOwnerZeroDominance :
    CCL.Riemann.ExactQuadraticOwnerClearance.AmbientClearanceDominance
      secondOwnerZero := by
  unfold secondOwnerZero
  exact firstConnectorEdgeSevenStep.advanceCache.dominance

private theorem secondOwnerZeroBudget :
    CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      secondOwnerZero := by
  unfold secondOwnerZero
  exact firstConnectorEdgeSevenStep.advanceCache.budget

theorem secondVariationLtQuarterAt (edge : Fin 8) :
    CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
        (secondMeshEndpoint (secondEdgeSource edge)).parameter
          (secondEdgeRequest edge).endpoint.parameter < (1 / 4 : Q) := by
  have cached := secondVariationLtQuarter
  rw [secondVariationEq] at cached
  rw [secondMeshVariationEq]
  exact cached

theorem secondEdgeZeroStep :
    CCL.Riemann.PreparedSheetContinuation.ParametricSameBoxStep
      secondSegment secondWithin (secondMeshEndpoint 0) secondOwnerZero
        (secondEdgeRequest 0) firstConnectorBoxTwo
          (1 / 4 : Q) (3 / 4 : Q) (1 / 8 : Q) := by
  apply CCL.Riemann.PreparedSheetContinuation.parametricSameBoxStep
    secondSegment secondWithin (secondMeshEndpoint 0) secondOwnerZero
      (secondEdgeRequest 0) firstConnectorBoxTwo secondOwnerZeroBoxEq
        (secondBoxSmall 0) secondBoxRefines
        (CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
          (1 / 8 : Q)) (predictedLeEighthFloor 0) secondOwnerZeroFloor
            secondOwnerZeroDominance secondOwnerZeroBudget
              (1 / 4 : Q) (3 / 4 : Q) secondOwnerZeroAmbientLeftLe
  · change CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 0).parameter))
          firstConnectorBoxTwo (1 / 4 : Q) (3 / 4 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondDirectBoundsZero
  · exact secondVariationLtQuarterAt 0
  · simp only [secondEdgeRequest]
    change CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 0).parameter) ≠
      CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 0)).parameter)
    rw [quartic_eval_secondMeshEndpoint, quartic_eval_secondMeshEndpoint]
    exact secondAdjacentParametersDifferent 0
  · exact RFAP.ConstructiveFraction.div_pos_direct
      (qNatPositiveContinuation 1 (by omega))
        (qNatPositiveContinuation 8 (by omega))
  · exact predictedLeEighthFloor 0
  · exact secondVariationMargin 0
  · simp only [secondEdgeRequest]
    change RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 0)).parameter)) ≤ (256 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondGridParameterNormSqLe 1

def secondOwnerOne :=
  CCL.Riemann.PreparedSheetContinuation.advanceCached secondSegment secondWithin
    (secondMeshEndpoint 0) secondOwnerZero (secondEdgeRequest 0)
      (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
        secondSegment (secondMeshEndpoint 0) secondOwnerZero
          (secondEdgeRequest 0)) secondEdgeZeroStep.canonicalSmall

theorem secondOwnerOneBoxEq :
    secondOwnerOne.track.initial.box = firstConnectorBoxTwo :=
  secondEdgeZeroStep.nextOwnerBox

private theorem secondOwnerOneAmbientLeftLe :
    secondOwnerOne.track.initial.ambientLeftClearance.bound ≤ (3 / 4 : Q) :=
  secondEdgeZeroStep.nextAmbientLeftLeQuarter.trans (by decide)

theorem secondEdgeOneStep :
    CCL.Riemann.PreparedSheetContinuation.ParametricSameBoxStep
      secondSegment secondWithin (secondMeshEndpoint 1) secondOwnerOne
        (secondEdgeRequest 1) firstConnectorBoxTwo
          (1 / 4 : Q) (3 / 4 : Q) (1 / 8 : Q) := by
  apply CCL.Riemann.PreparedSheetContinuation.parametricSameBoxStep
    secondSegment secondWithin (secondMeshEndpoint 1) secondOwnerOne
      (secondEdgeRequest 1) firstConnectorBoxTwo secondOwnerOneBoxEq
        (secondBoxSmall 1) secondBoxRefines
        (CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
          (1 / 8 : Q)) (predictedLeEighthFloor 1)
            secondEdgeZeroStep.advanceCache.clearanceFloor
              secondEdgeZeroStep.advanceCache.dominance
                secondEdgeZeroStep.advanceCache.budget
                  (1 / 4 : Q) (3 / 4 : Q) secondOwnerOneAmbientLeftLe
  · change CCL.Riemann.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 1).parameter))
          firstConnectorBoxTwo (1 / 4 : Q) (3 / 4 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondDirectBoundsOne
  · exact secondVariationLtQuarterAt 1
  · simp only [secondEdgeRequest]
    change CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 1).parameter) ≠
      CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 1)).parameter)
    rw [quartic_eval_secondMeshEndpoint, quartic_eval_secondMeshEndpoint]
    exact secondAdjacentParametersDifferent 1
  · exact RFAP.ConstructiveFraction.div_pos_direct
      (qNatPositiveContinuation 1 (by omega))
        (qNatPositiveContinuation 8 (by omega))
  · exact predictedLeEighthFloor 1
  · exact secondVariationMargin 1
  · simp only [secondEdgeRequest]
    change RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondSegment.pointAt
          (secondMeshEndpoint (secondEdgeTarget 1)).parameter)) ≤ (256 : Q)
    rw [quartic_eval_secondMeshEndpoint]
    exact secondGridParameterNormSqLe 2

def secondOwnerTwo :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (secondSegment.pointAt (secondMeshEndpoint 2).parameter)) :=
  CCL.Riemann.PreparedSheetContinuation.advanceCached secondSegment secondWithin
    (secondMeshEndpoint 1) secondOwnerOne (secondEdgeRequest 1)
      (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
        secondSegment (secondMeshEndpoint 1) secondOwnerOne
          (secondEdgeRequest 1)) secondEdgeOneStep.canonicalSmall

theorem secondOwnerTwoBoxEq :
    secondOwnerTwo.track.initial.box = firstConnectorBoxTwo :=
  secondEdgeOneStep.nextOwnerBox


end CCL.Riemann.ExplicitQuarticBranches
