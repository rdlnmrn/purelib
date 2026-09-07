import CCL.Riemann.ExplicitQuarticPreparedSecondCell

/-!
# The dyadic grid of the second prepared quartic connector cell

This module caches the nine Gaussian-rational radicands of the second outer
connector cell on its depth-three dyadic mesh.  A common fine unit keeps the
endpoint evaluations and all eight squared displacements constructive and
small enough to elaborate at the ordinary limits.
-/

namespace CCL.Riemann.ExplicitQuarticBranches

@[simp] private theorem pointRealSecond (x y : Q) : (point x y).re = x := rfl

@[simp] private theorem pointImaginarySecond (x y : Q) : (point x y).im = y := rfl

private theorem finNineCasesSecond (index : Fin 9) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
  rcases index with ⟨value, bound⟩
  omega0

private theorem finEightCasesSecond (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  omega0

private theorem qNatPositiveSecond (n : Nat) (positive : 0 < n) :
    (0 : Q) < n :=
  RFAP.ConstructiveFraction.natCast_pos_direct positive

private def reducedSecond (num : Int) (den : Nat) (denPositive : 0 < den)
    (left right : Int)
    (bezout : left * (num.natAbs : Int) + right * (den : Int) = 1) : Q where
  num := num
  den := den
  den_pos := denPositive
  reduced := ⟨⟨left, right, bezout⟩⟩

private theorem reducedSecond_eq_div (num : Int) (den : Nat)
    (denPositive : 0 < den) (left right : Int)
    (bezout : left * (num.natAbs : Int) + right * (den : Int) = 1) :
    reducedSecond num den denPositive left right bezout =
      (num : Q) / (den : Q) := by
  let value := reducedSecond num den denPositive left right bezout
  have denominatorPositive : (0 : Q) < den :=
    qNatPositiveSecond den denPositive
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    denominatorPositive.ne'
  calc
    value * (den : Q) = (num : Q) :=
      RFAP.ConstructiveFraction.representative_mul_den value
    _ = ((num : Q) / (den : Q)) * (den : Q) :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        denominatorPositive.ne').symm

private theorem over_eq_reduced
    (left denominator : Q) (num : Int) (den : Nat)
    (denPositive : 0 < den) (bezoutLeft bezoutRight : Int)
    (bezout : bezoutLeft * (num.natAbs : Int) +
      bezoutRight * (den : Int) = 1)
    (denominatorPositive : 0 < denominator)
    (cross : left * (den : Q) = (num : Q) * denominator) :
    left / denominator =
      reducedSecond num den denPositive bezoutLeft bezoutRight bezout := by
  rw [reducedSecond_eq_div]
  exact RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
    denominatorPositive.ne' (qNatPositiveSecond den denPositive).ne' cross

private theorem secondConnectorRealAt (k n : Q) (sum : k + n = 32) :
    (-1 : Q) + (k / 8) * ((-3 / 4) - (-1)) = -(n / 32) := by
  have dx : (-3 / 4 : Q) - (-1) = 1 / 4 := by
    decide
  have product : (k / 8 : Q) * (1 / 4) = k / 32 := by
    rw [RFAP.ConstructiveFraction.div_mul_div_direct]
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      (RFAP.ConstructiveFraction.mul_ne_zero_direct
        (qNatPositiveSecond 8 (by omega)).ne'
          (qNatPositiveSecond 4 (by omega)).ne')
      (qNatPositiveSecond 32 (by omega)).ne'
    ring1
  have startCommon : (-1 : Q) = -32 / 32 := by
    change (-1 : Q) / 1 = (-32 : Q) / 32
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      (qNatPositiveSecond 1 (by omega)).ne'
      (qNatPositiveSecond 32 (by omega)).ne'
    ring1
  rw [dx, product, startCommon]
  simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  rw [← sum]
  ring1

private theorem secondAffineGridPoint (k n : Q) (sum : k + n = 32) :
    point ((-1) + (k / 8) * ((-3 / 4) - (-1)))
        ((-1 / 2) + (k / 8) * ((-1 / 2) - (-1 / 2))) =
      point (-(n / 32)) (-1 / 2) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · simp only [pointRealSecond]
    exact secondConnectorRealAt k n sum
  · simp only [pointImaginarySecond]
    ring1

private theorem adjacentParameterSquare (k : Q) :
    (k / 8 - (k + 1) / 8) ^ 2 = (0 - 1 / 8 : Q) ^ 2 := by
  simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  ring1

private def fineUnit : Q := 1 / 1048576

private theorem fineUnitNonnegative : (0 : Q) ≤ fineUnit :=
  (RFAP.ConstructiveFraction.div_pos_direct
    (qNatPositiveSecond 1 (by omega))
      (qNatPositiveSecond 1048576 (by omega))).le

private theorem scaledFine (numerator scale : Q) (denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (cross : numerator * 1048576 = scale * denominator) :
    numerator / denominator = scale * fineUnit := by
  unfold fineUnit
  calc
    numerator / denominator = scale / 1048576 :=
      RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
        (qNatPositiveSecond denominator denominatorPositive).ne'
        (qNatPositiveSecond 1048576 (by omega)).ne' cross
    _ = scale * (1 / 1048576) := by
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.one_mul]

private theorem fineUnit_eq_scaled_square :
    fineUnit = 1048576 * fineUnit ^ 2 := by
  unfold fineUnit
  rw [pow_two]
  calc
    (1 / 1048576 : Q) = 1 * (1 / 1048576) := by ring1
    _ = ((1 / 1048576 : Q) * 1048576) * (1 / 1048576) :=
      congrArg (fun value : Q => value * (1 / 1048576))
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          (qNatPositiveSecond 1048576 (by omega)).ne').symm
    _ = 1048576 * ((1 / 1048576 : Q) * (1 / 1048576)) := by ring1

private theorem oneThirtySecondFine :
    (1 / 32 : Q) = 32768 * fineUnit :=
  scaledFine 1 32768 32 (by omega) (by ring1)

private theorem oneEighthFine :
    (1 / 8 : Q) = 131072 * fineUnit :=
  scaledFine 1 131072 8 (by omega) (by ring1)

private theorem variationFine :
    (1011 / 4096 : Q) = 258816 * fineUnit :=
  scaledFine 1011 258816 4096 (by omega) (by ring1)

private theorem scaledPointsNormLe
    (sourceReal sourceImaginary targetReal targetImaginary : Q)
    (coefficientLe :
      (sourceReal - targetReal) ^ 2 +
          (sourceImaginary - targetImaginary) ^ 2 ≤ 34359738368) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (sourceReal * fineUnit) (sourceImaginary * fineUnit) -
        point (targetReal * fineUnit) (targetImaginary * fineUnit)) ≤
      (1 / 32 : Q) := by
  unfold RFAP.ConstructiveGaussian.Gaussian.normSq
  simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
    RFAP.ConstructiveGaussian.Gaussian.sub_im,
    pointRealSecond, pointImaginarySecond]
  calc
    (sourceReal * fineUnit - targetReal * fineUnit) ^ 2 +
        (sourceImaginary * fineUnit - targetImaginary * fineUnit) ^ 2 =
      ((sourceReal - targetReal) ^ 2 +
        (sourceImaginary - targetImaginary) ^ 2) * fineUnit ^ 2 := by ring1
    _ ≤ 34359738368 * fineUnit ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        coefficientLe (RFAP.ConstructiveFraction.sq_nonneg_direct fineUnit)
    _ = (1 / 32 : Q) := by
      rw [oneThirtySecondFine]
      conv_rhs => rw [fineUnit_eq_scaled_square]
      ring1

def secondGridInput : Fin 9 → Gaussian
  | ⟨0, _⟩ => point (-(32 / 32)) (-1 / 2)
  | ⟨1, _⟩ => point (-(31 / 32)) (-1 / 2)
  | ⟨2, _⟩ => point (-(30 / 32)) (-1 / 2)
  | ⟨3, _⟩ => point (-(29 / 32)) (-1 / 2)
  | ⟨4, _⟩ => point (-(28 / 32)) (-1 / 2)
  | ⟨5, _⟩ => point (-(27 / 32)) (-1 / 2)
  | ⟨6, _⟩ => point (-(26 / 32)) (-1 / 2)
  | ⟨7, _⟩ => point (-(25 / 32)) (-1 / 2)
  | ⟨8, _⟩ => point (-(24 / 32)) (-1 / 2)

def secondGridParameter : Fin 9 → Gaussian
  | ⟨0, _⟩ => point (-1507328 * fineUnit) (1572864 * fineUnit)
  | ⟨1, _⟩ => point (-1535615 * fineUnit) (1398720 * fineUnit)
  | ⟨2, _⟩ => point (-1555440 * fineUnit) (1236480 * fineUnit)
  | ⟨3, _⟩ => point (-1567535 * fineUnit) (1085760 * fineUnit)
  | ⟨4, _⟩ => point (-1572608 * fineUnit) (946176 * fineUnit)
  | ⟨5, _⟩ => point (-1571343 * fineUnit) (817344 * fineUnit)
  | ⟨6, _⟩ => point (-1564400 * fineUnit) (698880 * fineUnit)
  | ⟨7, _⟩ => point (-1552415 * fineUnit) (590400 * fineUnit)
  | ⟨8, _⟩ => point (-1536000 * fineUnit) (491520 * fineUnit)

/-- Canonically reduced representatives of the same nine cached radicands.
These are used by the exact boundary-resultant checks. -/
def secondGridReducedParameter : Fin 9 → Gaussian
  | ⟨0, _⟩ => point
      (reducedSecond (-23) 16 (by omega) 7 (-10) (by omega))
      (reducedSecond 3 2 (by omega) 1 (-1) (by omega))
  | ⟨1, _⟩ => point
      (reducedSecond (-1535615) 1048576 (by omega) 414079 (-606409) (by omega))
      (reducedSecond 21855 16384 (by omega) 1695 (-2261) (by omega))
  | ⟨2, _⟩ => point
      (reducedSecond (-97215) 65536 (by omega) 29759 (-44144) (by omega))
      (reducedSecond 2415 2048 (by omega) (-625) 737 (by omega))
  | ⟨3, _⟩ => point
      (reducedSecond (-1567535) 1048576 (by omega) (-312369) 466966 (by omega))
      (reducedSecond 16965 16384 (by omega) 141 (-146) (by omega))
  | ⟨4, _⟩ => point
      (reducedSecond (-6143) 4096 (by omega) 2047 (-3070) (by omega))
      (reducedSecond 231 256 (by omega) (-41) 37 (by omega))
  | ⟨5, _⟩ => point
      (reducedSecond (-1571343) 1048576 (by omega) 373999 (-560456) (by omega))
      (reducedSecond 12771 16384 (by omega) 7115 (-5546) (by omega))
  | ⟨6, _⟩ => point
      (reducedSecond (-97775) 65536 (by omega) 20751 (-30959) (by omega))
      (reducedSecond 1365 2048 (by omega) (-3) 2 (by omega))
  | ⟨7, _⟩ => point
      (reducedSecond (-1552415) 1048576 (by omega) (-275489) 407861 (by omega))
      (reducedSecond 9225 16384 (by omega) (-5575) 3139 (by omega))
  | ⟨8, _⟩ => point
      (reducedSecond (-375) 256 (by omega) 71 (-104) (by omega))
      (reducedSecond 15 32 (by omega) 15 (-7) (by omega))

private theorem quarticGridEvaluation_scaled (n : Q) :
    CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (point (-(n / 32)) (-1 / 2)) =
      point ((n ^ 4 - 1536 * n ^ 2 - 983040) * fineUnit)
        (64 * (n ^ 3 - 256 * n) * fineUnit) := by
  rw [quarticGridEvaluation]
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · simp only [pointRealSecond]
    exact scaledFine _ _ 1048576 (by omega) (by ring1)
  · simp only [pointImaginarySecond]
    exact scaledFine _ _ 16384 (by omega) (by ring1)

theorem quartic_eval_secondGridInput (index : Fin 9) :
    CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondGridInput index) = secondGridParameter index := by
  rcases finNineCasesSecond index with h | h | h | h | h | h | h | h | h
  all_goals subst index
  all_goals simp only [secondGridInput]
  all_goals rw [quarticGridEvaluation_scaled]
  all_goals apply RFAP.ConstructiveGaussian.Gaussian.ext
  all_goals simp only [secondGridParameter, pointRealSecond,
    pointImaginarySecond]
  all_goals ring1

private theorem quartic_eval_secondGridInput_reduced (index : Fin 9) :
    CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (secondGridInput index) = secondGridReducedParameter index := by
  rcases finNineCasesSecond index with h | h | h | h | h | h | h | h | h
  all_goals subst index
  all_goals simp only [secondGridInput, secondGridReducedParameter]
  all_goals rw [quarticGridEvaluation]
  all_goals
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · simp only [pointRealSecond]
      apply over_eq_reduced (denominator := (1048576 : Q))
      · exact qNatPositiveSecond 1048576 (by omega)
      · ring1
    · simp only [pointImaginarySecond]
      apply over_eq_reduced (denominator := (16384 : Q))
      · exact qNatPositiveSecond 16384 (by omega)
      · ring1

theorem secondGridParameter_eq_reduced (index : Fin 9) :
    secondGridParameter index = secondGridReducedParameter index :=
  (quartic_eval_secondGridInput index).symm.trans
    (quartic_eval_secondGridInput_reduced index)

def secondGridEndpoint : Fin 9 →
    CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint
  | ⟨0, _⟩ => ⟨0 / 8, by decide⟩
  | ⟨1, _⟩ => ⟨1 / 8, by decide⟩
  | ⟨2, _⟩ => ⟨2 / 8, by decide⟩
  | ⟨3, _⟩ => ⟨3 / 8, by decide⟩
  | ⟨4, _⟩ => ⟨4 / 8, by decide⟩
  | ⟨5, _⟩ => ⟨5 / 8, by decide⟩
  | ⟨6, _⟩ => ⟨6 / 8, by decide⟩
  | ⟨7, _⟩ => ⟨7 / 8, by decide⟩
  | ⟨8, _⟩ => ⟨8 / 8, by decide⟩

/-- Boundary-aligned presentations of the same nine mesh endpoints. -/
def secondMeshEndpoint : Fin 9 →
    CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint
  | ⟨0, _⟩ => CCL.Riemann.PreparedClearPathModels.zeroEndpoint
  | ⟨1, _⟩ => secondGridEndpoint 1
  | ⟨2, _⟩ => secondGridEndpoint 2
  | ⟨3, _⟩ => secondGridEndpoint 3
  | ⟨4, _⟩ => secondGridEndpoint 4
  | ⟨5, _⟩ => secondGridEndpoint 5
  | ⟨6, _⟩ => secondGridEndpoint 6
  | ⟨7, _⟩ => secondGridEndpoint 7
  | ⟨8, _⟩ => CCL.Riemann.PreparedClearPathModels.oneEndpoint

theorem secondMeshEndpoint_parameter (index : Fin 9) :
    (secondMeshEndpoint index).parameter =
      (secondGridEndpoint index).parameter := by
  rcases finNineCasesSecond index with h | h | h | h | h | h | h | h | h
  all_goals subst index
  all_goals rfl

theorem secondSegment_pointAt_gridEndpoint (index : Fin 9) :
    secondSegment.pointAt (secondGridEndpoint index).parameter =
      secondGridInput index := by
  rcases finNineCasesSecond index with h | h | h | h | h | h | h | h | h
  all_goals subst index
  all_goals rw [secondSegment_pointAt]
  all_goals simp only [secondGridEndpoint, secondGridInput]
  all_goals exact secondAffineGridPoint _ _ (by ring1)

theorem quartic_eval_secondGridEndpoint (index : Fin 9) :
    CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
      (secondSegment.pointAt (secondGridEndpoint index).parameter) =
        secondGridParameter index := by
  rw [secondSegment_pointAt_gridEndpoint]
  exact quartic_eval_secondGridInput index

theorem quartic_eval_secondMeshEndpoint (index : Fin 9) :
    CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
      (secondSegment.pointAt (secondMeshEndpoint index).parameter) =
        secondGridParameter index := by
  rw [secondMeshEndpoint_parameter]
  exact quartic_eval_secondGridEndpoint index

def secondEdgeSource : Fin 8 → Fin 9
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 4
  | ⟨5, _⟩ => 5
  | ⟨6, _⟩ => 6
  | ⟨7, _⟩ => 7

def secondEdgeTarget : Fin 8 → Fin 9
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 5
  | ⟨5, _⟩ => 6
  | ⟨6, _⟩ => 7
  | ⟨7, _⟩ => 8

def secondEdgeRequest (edge : Fin 8) :
    CCL.Riemann.PreparedSheetContinuation.StepRequest :=
  { endpoint := secondMeshEndpoint (secondEdgeTarget edge)
    rootDiameter := workingRootDiameter
    rootDiameterPositive := workingRootDiameter_positive }

theorem secondMeshVariationEq (edge : Fin 8) :
    CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
      (secondMeshEndpoint (secondEdgeSource edge)).parameter
        (secondEdgeRequest edge).endpoint.parameter = (1011 / 4096 : Q) := by
  calc
    _ = CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
        endpoint0.parameter endpoint1.parameter := by
      rw [CCL.Riemann.ClearSheetContinuation.variationBound_eq_denseLipschitz,
        CCL.Riemann.ClearSheetContinuation.variationBound_eq_denseLipschitz]
      congr 1
      rcases finEightCasesSecond edge with h | h | h | h | h | h | h | h
      all_goals subst edge
      all_goals simp only [secondMeshEndpoint, secondGridEndpoint,
        secondEdgeSource,
        secondEdgeRequest, secondEdgeTarget, endpoint0, endpoint1]
      all_goals exact adjacentParameterSquare _
    _ = (1011 / 4096 : Q) := secondVariationEq

theorem secondAdjacentDisplacementLe (edge : Fin 8) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (secondGridParameter (secondEdgeSource edge) -
        secondGridParameter (secondEdgeTarget edge)) ≤ (1 / 32 : Q) := by
  rcases finEightCasesSecond edge with h | h | h | h | h | h | h | h
  all_goals subst edge
  all_goals simp only [secondGridParameter, secondEdgeSource, secondEdgeTarget]
  · apply scaledPointsNormLe
    rw [show (((-1507328 : Q) - (-1535615)) ^ 2 +
      (1572864 - 1398720) ^ 2) = (31126287105 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)

  · apply scaledPointsNormLe
    rw [show (((-1535615 : Q) - (-1555440)) ^ 2 +
      (1398720 - 1236480) ^ 2) = (26714848225 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)

  · apply scaledPointsNormLe
    rw [show (((-1555440 : Q) - (-1567535)) ^ 2 +
      (1236480 - 1085760) ^ 2) = (22862807425 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  · apply scaledPointsNormLe
    rw [show (((-1567535 : Q) - (-1572608)) ^ 2 +
      (1085760 - 946176) ^ 2) = (19509428385 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  · apply scaledPointsNormLe
    rw [show (((-1572608 : Q) - (-1571343)) ^ 2 +
      (946176 - 817344) ^ 2) = (16599284449 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  · apply scaledPointsNormLe
    rw [show (((-1571343 : Q) - (-1564400)) ^ 2 +
      (817344 - 698880) ^ 2) = (14081924545 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  · apply scaledPointsNormLe
    rw [show (((-1564400 : Q) - (-1552415)) ^ 2 +
      (698880 - 590400) ^ 2) = (11911550625 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  · apply scaledPointsNormLe
    rw [show (((-1552415 : Q) - (-1536000)) ^ 2 +
      (590400 - 491520) ^ 2) = (10046706625 : Q) by ring1]
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)

theorem secondAdjacentParametersDifferent (edge : Fin 8) :
    secondGridParameter (secondEdgeSource edge) ≠
      secondGridParameter (secondEdgeTarget edge) := by
  rw [secondGridParameter_eq_reduced, secondGridParameter_eq_reduced]
  rcases finEightCasesSecond edge with h | h | h | h | h | h | h | h
  all_goals subst edge
  all_goals with_unfolding_all decide

theorem secondVariationMargin (edge : Fin 8) : (1 / 8 : Q) ≤
    CCL.Riemann.ClearSheetContinuation.variationBound secondSegment
      (secondMeshEndpoint (secondEdgeSource edge)).parameter
        (secondEdgeRequest edge).endpoint.parameter -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
            (secondSegment.pointAt
              (secondMeshEndpoint (secondEdgeSource edge)).parameter) -
          CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
            (secondSegment.pointAt
              (secondEdgeRequest edge).endpoint.parameter)) := by
  rw [secondMeshVariationEq]
  simp only [secondEdgeRequest]
  rw [quartic_eval_secondMeshEndpoint, quartic_eval_secondMeshEndpoint]
  change (1 / 8 : Q) ≤ 1011 / 4096 -
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (secondGridParameter (secondEdgeSource edge) -
        secondGridParameter (secondEdgeTarget edge))
  have displacement := secondAdjacentDisplacementLe edge
  calc
    (1 / 8 : Q) ≤ 1011 / 4096 - 1 / 32 := by
      rw [oneEighthFine, variationFine, oneThirtySecondFine]
      calc
        (131072 : Q) * fineUnit ≤ 226048 * fineUnit :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (RFAP.ConstructiveFraction.natCast_le_direct (by decide))
            fineUnitNonnegative
        _ = 258816 * fineUnit - 32768 * fineUnit := by ring1
    _ ≤ 1011 / 4096 -
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (secondGridParameter (secondEdgeSource edge) -
            secondGridParameter (secondEdgeTarget edge)) :=
      RFAP.ConstructiveFraction.sub_le_sub_left_direct displacement _

end CCL.Riemann.ExplicitQuarticBranches
