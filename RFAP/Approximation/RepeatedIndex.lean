import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.BestApproximation

/-!
# Finite exclusion of repeated coefficient index two

This file continues the finite normal form in `BestApproximation`.  It keeps
the remaining argument in normalized Gaussian-rational coordinates and
records every cylinder alternative explicitly.  No completed complex point,
compactness argument, or unbounded search is used.
-/

namespace RFAP.RepeatedIndex

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Pair := RFAP.HurwitzRational.ConvergentPair
abbrev Fraction := RFAP.HurwitzRational.Fraction

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight.GaussianInt

def diagonalStep : GaussianInt := ⟨1, 1⟩

def doubledDiagonalStep : GaussianInt := ⟨2, 2⟩

def doubledAxisStep : GaussianInt := ⟨2, 0⟩

/-- The normalized finite data consumed by the three canonical transition
exclusions. -/
structure NormalizedCylinderData (coefficient : GaussianInt) where
  errorRatio : Gaussian
  denominatorRatio : Gaussian
  errorInside : normSq errorRatio < 1
  factorFour : (1 : Coordinate) < 4 * normSq errorRatio
  denominatorInside : normSq denominatorRatio < 1
  errorTransition :
    normSq (1 + toGaussian coefficient * errorRatio) < normSq errorRatio
  denominatorTransition :
    1 < normSq (denominatorRatio + toGaussian coefficient)
  selfObstruction : ∀ unit : GaussianInt, normNat unit = 1 →
    (2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∨
      2 ≤ normSq (1 - toGaussian unit * denominatorRatio)
  nextObstruction : ∀ unit : GaussianInt, normNat unit = 1 →
    (2 : Coordinate) * normSq errorRatio ≤
        normSq (errorRatio - toGaussian unit) ∨
      2 * normSq (denominatorRatio + toGaussian coefficient) ≤
        normSq (1 - toGaussian unit * denominatorRatio)

/-- Cancel an explicitly inverted nonzero Gaussian on the right. -/
private theorem mul_inv_mul_cancel (left right : Gaussian)
    (rightNonzero : right ≠ 0) :
    (left * RFAP.ConstructiveGaussian.Gaussian.inv right) * right = left := by
  calc
    (left * RFAP.ConstructiveGaussian.Gaussian.inv right) * right =
        left * (RFAP.ConstructiveGaussian.Gaussian.inv right * right) :=
      RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
    _ = left * 1 := by
      rw [RFAP.ConstructiveGaussian.Gaussian.inv_mul right rightNonzero]
    _ = left := RFAP.ConstructiveGaussian.Gaussian.mul_one _

/-- Normalize homogeneous error and denominator coordinates by their two
positive reference quadrances.  Every conclusion is obtained by multiplying
back by the displayed nonzero reference, so the construction uses no choice
of a completed quotient. -/
def normalizeCylinderData
    (coefficient : GaussianInt)
    (largeError smallError nextError : Gaussian)
    (lowerDenominator middleDenominator upperDenominator : Gaussian)
    (largeErrorNonzero : largeError ≠ 0)
    (middleDenominatorNonzero : middleDenominator ≠ 0)
    (errorOrdered : normSq smallError < normSq largeError)
    (nextErrorOrdered : normSq nextError < normSq smallError)
    (factorFour : normSq largeError < 4 * normSq smallError)
    (denominatorOrdered :
      normSq lowerDenominator < normSq middleDenominator)
    (nextDenominatorOrdered :
      normSq middleDenominator < normSq upperDenominator)
    (errorIdentity :
      nextError = largeError + toGaussian coefficient * smallError)
    (denominatorIdentity :
      upperDenominator =
        lowerDenominator + toGaussian coefficient * middleDenominator)
    (selfObstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) * normSq largeError ≤
          normSq (smallError - toGaussian unit * largeError) ∨
        2 * normSq middleDenominator ≤
          normSq (middleDenominator -
            toGaussian unit * lowerDenominator))
    (nextObstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) * normSq smallError ≤
          normSq (smallError - toGaussian unit * largeError) ∨
        2 * normSq upperDenominator ≤
          normSq (middleDenominator -
            toGaussian unit * lowerDenominator)) :
    NormalizedCylinderData coefficient := by
  let errorRatio :=
    smallError * RFAP.ConstructiveGaussian.Gaussian.inv largeError
  let denominatorRatio :=
    lowerDenominator *
      RFAP.ConstructiveGaussian.Gaussian.inv middleDenominator
  have largeNormPositive : 0 < normSq largeError := normSq_pos largeErrorNonzero
  have middleNormPositive : 0 < normSq middleDenominator :=
    normSq_pos middleDenominatorNonzero
  have largeNormNonzero : normSq largeError ≠ 0 := ne_of_gt largeNormPositive
  have middleNormNonzero : normSq middleDenominator ≠ 0 :=
    ne_of_gt middleNormPositive
  have errorRatioNorm :
      normSq errorRatio =
        normSq smallError * (normSq largeError)⁻¹ := by
    dsimp only [errorRatio]
    rw [normSq_mul,
      RFAP.ConstructiveGaussian.Gaussian.normSq_inv largeError
        largeErrorNonzero]
  have denominatorRatioNorm :
      normSq denominatorRatio =
        normSq lowerDenominator * (normSq middleDenominator)⁻¹ := by
    dsimp only [denominatorRatio]
    rw [normSq_mul,
      RFAP.ConstructiveGaussian.Gaussian.normSq_inv middleDenominator
        middleDenominatorNonzero]
  have errorInside : normSq errorRatio < 1 := by
    rw [errorRatioNorm]
    change normSq smallError / normSq largeError < 1
    exact (RFAP.ConstructiveFraction.div_lt_iff_pos largeNormPositive).mpr
      (by simpa only [RFAP.ConstructiveFraction.one_mul] using errorOrdered)
  have normalizedFactorFour :
      (1 : Coordinate) < 4 * normSq errorRatio := by
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := normSq largeError)
    · calc
        (1 : Coordinate) * normSq largeError = normSq largeError := by ring1
        _ < 4 * normSq smallError := factorFour
        _ = (4 * normSq errorRatio) * normSq largeError := by
          rw [errorRatioNorm]
          symm
          calc
            (4 * (normSq smallError * (normSq largeError)⁻¹)) *
                normSq largeError =
                4 * (normSq smallError *
                  ((normSq largeError)⁻¹ * normSq largeError)) := by
              rw [RFAP.ConstructiveFraction.mul_assoc,
                RFAP.ConstructiveFraction.mul_assoc]
            _ = 4 * normSq smallError := by
              rw [RFAP.ConstructiveFraction.inv_mul_cancel _
                largeNormNonzero]
              ring1
    · exact largeNormPositive
  have denominatorInside : normSq denominatorRatio < 1 := by
    rw [denominatorRatioNorm]
    change normSq lowerDenominator / normSq middleDenominator < 1
    exact (RFAP.ConstructiveFraction.div_lt_iff_pos middleNormPositive).mpr
      (by
        simpa only [RFAP.ConstructiveFraction.one_mul] using
          denominatorOrdered)
  have errorRatioCancel : errorRatio * largeError = smallError := by
    dsimp only [errorRatio]
    exact mul_inv_mul_cancel smallError largeError largeErrorNonzero
  have denominatorRatioCancel :
      denominatorRatio * middleDenominator = lowerDenominator := by
    dsimp only [denominatorRatio]
    exact mul_inv_mul_cancel lowerDenominator middleDenominator
      middleDenominatorNonzero
  have normalizedErrorIdentity :
      nextError * RFAP.ConstructiveGaussian.Gaussian.inv largeError =
        1 + toGaussian coefficient * errorRatio := by
    calc
      nextError * RFAP.ConstructiveGaussian.Gaussian.inv largeError =
          (largeError + toGaussian coefficient * smallError) *
            RFAP.ConstructiveGaussian.Gaussian.inv largeError := by
        rw [errorIdentity]
      _ = largeError * RFAP.ConstructiveGaussian.Gaussian.inv largeError +
          (toGaussian coefficient * smallError) *
            RFAP.ConstructiveGaussian.Gaussian.inv largeError :=
        RFAP.ConstructiveGaussian.Gaussian.right_distrib _ _ _
      _ = 1 + toGaussian coefficient * errorRatio := by
        rw [RFAP.ConstructiveGaussian.Gaussian.mul_inv largeError
          largeErrorNonzero]
        dsimp only [errorRatio]
        rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
  have normalizedDenominatorIdentity :
      upperDenominator *
          RFAP.ConstructiveGaussian.Gaussian.inv middleDenominator =
        denominatorRatio + toGaussian coefficient := by
    calc
      upperDenominator *
          RFAP.ConstructiveGaussian.Gaussian.inv middleDenominator =
          (lowerDenominator +
              toGaussian coefficient * middleDenominator) *
            RFAP.ConstructiveGaussian.Gaussian.inv middleDenominator := by
        rw [denominatorIdentity]
      _ = lowerDenominator *
            RFAP.ConstructiveGaussian.Gaussian.inv middleDenominator +
          (toGaussian coefficient * middleDenominator) *
            RFAP.ConstructiveGaussian.Gaussian.inv middleDenominator :=
        RFAP.ConstructiveGaussian.Gaussian.right_distrib _ _ _
      _ = denominatorRatio + toGaussian coefficient := by
        dsimp only [denominatorRatio]
        rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
          RFAP.ConstructiveGaussian.Gaussian.mul_inv middleDenominator
            middleDenominatorNonzero,
          RFAP.ConstructiveGaussian.Gaussian.mul_one]
  have normalizedErrorTransition :
      normSq (1 + toGaussian coefficient * errorRatio) <
        normSq errorRatio := by
    rw [← normalizedErrorIdentity, errorRatioNorm, normSq_mul,
      RFAP.ConstructiveGaussian.Gaussian.normSq_inv largeError
        largeErrorNonzero]
    exact RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      nextErrorOrdered
      (RFAP.ConstructiveFraction.inv_pos_direct largeNormPositive)
  have normalizedDenominatorTransition :
      1 < normSq (denominatorRatio + toGaussian coefficient) := by
    rw [← normalizedDenominatorIdentity, normSq_mul,
      RFAP.ConstructiveGaussian.Gaussian.normSq_inv middleDenominator
        middleDenominatorNonzero]
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := normSq middleDenominator)
    · calc
        (1 : Coordinate) * normSq middleDenominator =
            normSq middleDenominator := by ring1
        _ < normSq upperDenominator := nextDenominatorOrdered
        _ =
            (normSq upperDenominator * (normSq middleDenominator)⁻¹) *
              normSq middleDenominator := by
          symm
          calc
            (normSq upperDenominator * (normSq middleDenominator)⁻¹) *
                normSq middleDenominator =
                normSq upperDenominator *
                  ((normSq middleDenominator)⁻¹ *
                    normSq middleDenominator) :=
              RFAP.ConstructiveFraction.mul_assoc _ _ _
            _ = normSq upperDenominator := by
              rw [RFAP.ConstructiveFraction.inv_mul_cancel _
                middleNormNonzero]
              ring1
    · exact middleNormPositive
  refine
    { errorRatio := errorRatio
      denominatorRatio := denominatorRatio
      errorInside := errorInside
      factorFour := normalizedFactorFour
      denominatorInside := denominatorInside
      errorTransition := normalizedErrorTransition
      denominatorTransition := normalizedDenominatorTransition
      selfObstruction := ?_
      nextObstruction := ?_ }
  · intro unit unitNorm
    rcases selfObstruction unit unitNorm with
      errorExterior | denominatorExterior
    · left
      let normalizedDifference := errorRatio - toGaussian unit
      have scaledDifference :
          normalizedDifference * largeError =
            smallError - toGaussian unit * largeError := by
        calc
          normalizedDifference * largeError =
              errorRatio * largeError - toGaussian unit * largeError := by
            dsimp only [normalizedDifference]
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.mul_re,
                RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
              ring1
          _ = smallError - toGaussian unit * largeError := by
            rw [errorRatioCancel]
      apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
        (c := normSq largeError)
      · calc
          (2 : Coordinate) * normSq largeError ≤
              normSq (smallError - toGaussian unit * largeError) :=
            errorExterior
          _ = normSq normalizedDifference * normSq largeError := by
            rw [← scaledDifference, normSq_mul]
      · exact largeNormPositive
    · right
      let normalizedDifference :=
        (1 : Gaussian) - toGaussian unit * denominatorRatio
      have scaledDifference :
          normalizedDifference * middleDenominator =
            middleDenominator - toGaussian unit * lowerDenominator := by
        calc
          normalizedDifference * middleDenominator =
              middleDenominator -
                toGaussian unit *
                  (denominatorRatio * middleDenominator) := by
            dsimp only [normalizedDifference]
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.mul_re,
                RFAP.ConstructiveGaussian.Gaussian.mul_im,
                RFAP.ConstructiveGaussian.Gaussian.one_re,
                RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
              ring1
          _ = middleDenominator - toGaussian unit * lowerDenominator := by
            rw [denominatorRatioCancel]
      apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
        (c := normSq middleDenominator)
      · calc
          (2 : Coordinate) * normSq middleDenominator ≤
              normSq (middleDenominator -
                toGaussian unit * lowerDenominator) := denominatorExterior
          _ = normSq normalizedDifference * normSq middleDenominator := by
            rw [← scaledDifference, normSq_mul]
      · exact middleNormPositive
  · intro unit unitNorm
    rcases nextObstruction unit unitNorm with
      errorExterior | denominatorExterior
    · left
      let normalizedDifference := errorRatio - toGaussian unit
      have scaledDifference :
          normalizedDifference * largeError =
            smallError - toGaussian unit * largeError := by
        calc
          normalizedDifference * largeError =
              errorRatio * largeError - toGaussian unit * largeError := by
            dsimp only [normalizedDifference]
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.mul_re,
                RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
              ring1
          _ = smallError - toGaussian unit * largeError := by
            rw [errorRatioCancel]
      apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
        (c := normSq largeError)
      · calc
          ((2 : Coordinate) * normSq errorRatio) * normSq largeError =
              2 * normSq smallError := by
            rw [errorRatioNorm]
            calc
              (2 * (normSq smallError * (normSq largeError)⁻¹)) *
                  normSq largeError =
                  2 * (normSq smallError *
                    ((normSq largeError)⁻¹ * normSq largeError)) := by
                rw [RFAP.ConstructiveFraction.mul_assoc,
                  RFAP.ConstructiveFraction.mul_assoc]
              _ = 2 * normSq smallError := by
                rw [RFAP.ConstructiveFraction.inv_mul_cancel _
                  largeNormNonzero]
                ring1
          _ ≤ normSq (smallError - toGaussian unit * largeError) :=
            errorExterior
          _ = normSq normalizedDifference * normSq largeError := by
            rw [← scaledDifference, normSq_mul]
      · exact largeNormPositive
    · right
      let normalizedDifference :=
        (1 : Gaussian) - toGaussian unit * denominatorRatio
      have scaledDifference :
          normalizedDifference * middleDenominator =
            middleDenominator - toGaussian unit * lowerDenominator := by
        calc
          normalizedDifference * middleDenominator =
              middleDenominator -
                toGaussian unit *
                  (denominatorRatio * middleDenominator) := by
            dsimp only [normalizedDifference]
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.mul_re,
                RFAP.ConstructiveGaussian.Gaussian.mul_im,
                RFAP.ConstructiveGaussian.Gaussian.one_re,
                RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
              ring1
          _ = middleDenominator - toGaussian unit * lowerDenominator := by
            rw [denominatorRatioCancel]
      apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
        (c := normSq middleDenominator)
      · calc
          (2 * normSq (denominatorRatio + toGaussian coefficient)) *
              normSq middleDenominator =
              2 * normSq upperDenominator := by
            rw [← normalizedDenominatorIdentity, normSq_mul,
              RFAP.ConstructiveGaussian.Gaussian.normSq_inv middleDenominator
                middleDenominatorNonzero]
            calc
              (2 * (normSq upperDenominator *
                    (normSq middleDenominator)⁻¹)) *
                  normSq middleDenominator =
                  2 * (normSq upperDenominator *
                    ((normSq middleDenominator)⁻¹ *
                      normSq middleDenominator)) := by
                rw [RFAP.ConstructiveFraction.mul_assoc,
                  RFAP.ConstructiveFraction.mul_assoc]
              _ = 2 * normSq upperDenominator := by
                rw [RFAP.ConstructiveFraction.inv_mul_cancel _
                  middleNormNonzero]
                ring1
          _ ≤ normSq (middleDenominator -
              toGaussian unit * lowerDenominator) := denominatorExterior
          _ = normSq normalizedDifference * normSq middleDenominator := by
            rw [← scaledDifference, normSq_mul]
      · exact middleNormPositive

/-- A finite Gaussian-unit certificate carries quadrance one. -/
theorem normNat_eq_one_of_isGaussianUnit {unit : GaussianInt}
    (property : RFAP.HurwitzGeometry.IsGaussianUnit unit) :
    normNat unit = 1 := by
  have quadrance :=
    RFAP.HurwitzGeometry.normSq_toGaussian_eq_one_of_isGaussianUnit property
  rw [normSq_toGaussian] at quadrance
  exact RFAP.ConstructiveFraction.natCast_injective_direct quadrance

/-- Transport normalized data through a displayed Gaussian-unit associate.
The error ratio rotates by the associate and the denominator ratio by its
displayed conjugate inverse; all four unit tests are merely permuted. -/
def transportNormalizedData
    (coefficient canonical associate : GaussianInt)
    (associateProperty : RFAP.HurwitzGeometry.IsGaussianUnit associate)
    (associated : coefficient = canonical * associate)
    (data : NormalizedCylinderData coefficient) :
    NormalizedCylinderData canonical := by
  let inverseAssociate := RFAP.HurwitzGeometry.conjugate associate
  let associateValue := toGaussian associate
  let inverseAssociateValue := toGaussian inverseAssociate
  let errorRatio := associateValue * data.errorRatio
  let denominatorRatio := inverseAssociateValue * data.denominatorRatio
  have associateNorm : normNat associate = 1 :=
    normNat_eq_one_of_isGaussianUnit associateProperty
  have inverseAssociateNorm : normNat inverseAssociate = 1 := by
    dsimp only [inverseAssociate]
    rw [RFAP.HurwitzGeometry.normNat_conjugate, associateNorm]
  have associateQuadrance : normSq associateValue = (1 : Coordinate) := by
    dsimp only [associateValue]
    rw [normSq_toGaussian, associateNorm]
    rfl
  have inverseAssociateQuadrance :
      normSq inverseAssociateValue = (1 : Coordinate) := by
    dsimp only [inverseAssociateValue]
    rw [normSq_toGaussian, inverseAssociateNorm]
    rfl
  have associateInverseInteger : associate * inverseAssociate = 1 := by
    dsimp only [inverseAssociate]
    exact RFAP.HurwitzGeometry.self_mul_conjugate_of_isGaussianUnit
      associateProperty
  have associateInverse :
      associateValue * inverseAssociateValue = (1 : Gaussian) := by
    dsimp only [associateValue, inverseAssociateValue]
    rw [← toGaussian_mul, associateInverseInteger, toGaussian_one]
  have errorRatioNorm : normSq errorRatio = normSq data.errorRatio := by
    dsimp only [errorRatio]
    rw [normSq_mul, associateQuadrance]
    ring1
  have denominatorRatioNorm :
      normSq denominatorRatio = normSq data.denominatorRatio := by
    dsimp only [denominatorRatio]
    rw [normSq_mul, inverseAssociateQuadrance]
    ring1
  have coefficientValue :
      toGaussian coefficient = toGaussian canonical * associateValue := by
    dsimp only [associateValue]
    rw [associated, toGaussian_mul]
  have errorTransitionIdentity :
      1 + toGaussian canonical * errorRatio =
        1 + toGaussian coefficient * data.errorRatio := by
    dsimp only [errorRatio]
    rw [coefficientValue,
      RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
  have denominatorTransitionIdentity :
      associateValue *
          (denominatorRatio + toGaussian canonical) =
        data.denominatorRatio + toGaussian coefficient := by
    calc
      associateValue *
          (denominatorRatio + toGaussian canonical) =
          associateValue * denominatorRatio +
            associateValue * toGaussian canonical :=
        RFAP.ConstructiveGaussian.Gaussian.left_distrib _ _ _
      _ = (associateValue * inverseAssociateValue) *
            data.denominatorRatio +
          toGaussian canonical * associateValue := by
        dsimp only [denominatorRatio]
        rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
          RFAP.ConstructiveGaussian.Gaussian.mul_comm associateValue
            (toGaussian canonical)]
      _ = data.denominatorRatio + toGaussian coefficient := by
        rw [associateInverse, RFAP.ConstructiveGaussian.Gaussian.one_mul,
          ← coefficientValue]
  have denominatorTransitionNorm :
      normSq (denominatorRatio + toGaussian canonical) =
        normSq (data.denominatorRatio + toGaussian coefficient) := by
    have normIdentity := congrArg normSq denominatorTransitionIdentity
    rw [normSq_mul, associateQuadrance] at normIdentity
    simpa only [RFAP.ConstructiveFraction.one_mul] using normIdentity
  refine
    { errorRatio := errorRatio
      denominatorRatio := denominatorRatio
      errorInside := by rw [errorRatioNorm]; exact data.errorInside
      factorFour := by rw [errorRatioNorm]; exact data.factorFour
      denominatorInside := by
        rw [denominatorRatioNorm]
        exact data.denominatorInside
      errorTransition := by
        rw [errorTransitionIdentity, errorRatioNorm]
        exact data.errorTransition
      denominatorTransition := by
        rw [denominatorTransitionNorm]
        exact data.denominatorTransition
      selfObstruction := ?_
      nextObstruction := ?_ }
  · intro unit unitNorm
    let sourceUnit := inverseAssociate * unit
    have sourceUnitNorm : normNat sourceUnit = 1 := by
      dsimp only [sourceUnit]
      rw [RFAP.HurwitzGeometry.normNat_mul, inverseAssociateNorm, unitNorm]
    have sourceUnitValue :
        toGaussian sourceUnit = inverseAssociateValue * toGaussian unit := by
      dsimp only [sourceUnit, inverseAssociateValue]
      rw [toGaussian_mul]
    have rotatedSourceUnit :
        associateValue * toGaussian sourceUnit = toGaussian unit := by
      calc
        associateValue * toGaussian sourceUnit =
            associateValue *
              (inverseAssociateValue * toGaussian unit) := by
          rw [sourceUnitValue]
        _ = (associateValue * inverseAssociateValue) * toGaussian unit :=
          (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm
        _ = toGaussian unit := by
          rw [associateInverse, RFAP.ConstructiveGaussian.Gaussian.one_mul]
    rcases data.selfObstruction sourceUnit sourceUnitNorm with
      errorExterior | denominatorExterior
    · left
      have differenceIdentity :
          errorRatio - toGaussian unit =
            associateValue *
              (data.errorRatio - toGaussian sourceUnit) := by
        calc
          errorRatio - toGaussian unit =
              associateValue * data.errorRatio -
                associateValue * toGaussian sourceUnit := by
            dsimp only [errorRatio]
            rw [rotatedSourceUnit]
          _ = associateValue *
              (data.errorRatio - toGaussian sourceUnit) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.mul_re,
                RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
              ring1
      rw [differenceIdentity, normSq_mul, associateQuadrance]
      simpa only [RFAP.ConstructiveFraction.one_mul] using errorExterior
    · right
      have differenceIdentity :
          (1 : Gaussian) - toGaussian unit * denominatorRatio =
            1 - toGaussian sourceUnit * data.denominatorRatio := by
        dsimp only [denominatorRatio]
        rw [sourceUnitValue]
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im,
            RFAP.ConstructiveGaussian.Gaussian.one_re,
            RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
          ring1
      rw [differenceIdentity]
      exact denominatorExterior
  · intro unit unitNorm
    let sourceUnit := inverseAssociate * unit
    have sourceUnitNorm : normNat sourceUnit = 1 := by
      dsimp only [sourceUnit]
      rw [RFAP.HurwitzGeometry.normNat_mul, inverseAssociateNorm, unitNorm]
    have sourceUnitValue :
        toGaussian sourceUnit = inverseAssociateValue * toGaussian unit := by
      dsimp only [sourceUnit, inverseAssociateValue]
      rw [toGaussian_mul]
    have rotatedSourceUnit :
        associateValue * toGaussian sourceUnit = toGaussian unit := by
      calc
        associateValue * toGaussian sourceUnit =
            associateValue *
              (inverseAssociateValue * toGaussian unit) := by
          rw [sourceUnitValue]
        _ = (associateValue * inverseAssociateValue) * toGaussian unit :=
          (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm
        _ = toGaussian unit := by
          rw [associateInverse, RFAP.ConstructiveGaussian.Gaussian.one_mul]
    rcases data.nextObstruction sourceUnit sourceUnitNorm with
      errorExterior | denominatorExterior
    · left
      have differenceIdentity :
          errorRatio - toGaussian unit =
            associateValue *
              (data.errorRatio - toGaussian sourceUnit) := by
        calc
          errorRatio - toGaussian unit =
              associateValue * data.errorRatio -
                associateValue * toGaussian sourceUnit := by
            dsimp only [errorRatio]
            rw [rotatedSourceUnit]
          _ = associateValue *
              (data.errorRatio - toGaussian sourceUnit) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.mul_re,
                RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
              ring1
      rw [errorRatioNorm, differenceIdentity, normSq_mul,
        associateQuadrance]
      simpa only [RFAP.ConstructiveFraction.one_mul] using errorExterior
    · right
      have differenceIdentity :
          (1 : Gaussian) - toGaussian unit * denominatorRatio =
            1 - toGaussian sourceUnit * data.denominatorRatio := by
        dsimp only [denominatorRatio]
        rw [sourceUnitValue]
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im,
            RFAP.ConstructiveGaussian.Gaussian.one_re,
            RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
          ring1
      rw [denominatorTransitionNorm, differenceIdentity]
      exact denominatorExterior

/-- Every quadrance-two coefficient is a displayed unit associate of the
canonical diagonal coefficient `1+i`. -/
theorem exists_unit_associate_of_normNat_eq_two
    (coefficient : GaussianInt) (coefficientNorm : normNat coefficient = 2) :
    ∃ associate, RFAP.HurwitzGeometry.IsGaussianUnit associate ∧
      coefficient = diagonalStep * associate := by
  have coefficientDiagonal :=
    RFAP.HurwitzGeometry.isDiagonal_of_normNat_eq_two coefficientNorm
  have canonicalDiagonal :
      RFAP.HurwitzGeometry.IsDiagonal diagonalStep := Or.inl rfl
  exact RFAP.HurwitzGeometry.exists_unit_right_factor_of_diagonals
    coefficientDiagonal canonicalDiagonal

/-- Every quadrance-four coefficient is a displayed unit associate of the
canonical axial coefficient `2`. -/
theorem exists_unit_associate_of_normNat_eq_four
    (coefficient : GaussianInt) (coefficientNorm : normNat coefficient = 4) :
    ∃ associate, RFAP.HurwitzGeometry.IsGaussianUnit associate ∧
      coefficient = doubledAxisStep * associate := by
  rcases RFAP.HurwitzGeometry.axisDouble_cases_of_normNat_eq_four
      coefficientNorm with
    coefficientCase | coefficientCase | coefficientCase | coefficientCase
  · exact ⟨1, Or.inl rfl, coefficientCase⟩
  · exact ⟨-1, Or.inr (Or.inl rfl), by
      rw [coefficientCase]
      decide⟩
  · exact ⟨RFAP.HurwitzGeometry.imaginaryUnit,
      Or.inr (Or.inr (Or.inl rfl)), by
        rw [coefficientCase]
        decide⟩
  · exact ⟨-RFAP.HurwitzGeometry.imaginaryUnit,
      Or.inr (Or.inr (Or.inr rfl)), by
        rw [coefficientCase]
        decide⟩

/-- The four Gaussian integers of quadrance eight are precisely the doubled
diagonals.  This is a bounded coordinate case split. -/
theorem doubledDiagonal_cases_of_normNat_eq_eight
    {coefficient : GaussianInt} (coefficientNorm : normNat coefficient = 8) :
    coefficient = ⟨2, 2⟩ ∨ coefficient = ⟨2, -2⟩ ∨
      coefficient = ⟨-2, 2⟩ ∨ coefficient = ⟨-2, -2⟩ :=
  RFAP.HurwitzGeometry.doubledDiagonal_cases_of_normNat_eq_eight
    coefficientNorm

/-- Every quadrance-eight coefficient is a displayed unit associate of the
canonical doubled diagonal coefficient `2+2i`. -/
theorem exists_unit_associate_of_normNat_eq_eight
    (coefficient : GaussianInt) (coefficientNorm : normNat coefficient = 8) :
    ∃ associate, RFAP.HurwitzGeometry.IsGaussianUnit associate ∧
      coefficient = doubledDiagonalStep * associate := by
  rcases doubledDiagonal_cases_of_normNat_eq_eight coefficientNorm with
    coefficientCase | coefficientCase | coefficientCase | coefficientCase
  · exact ⟨1, Or.inl rfl, coefficientCase⟩
  · exact ⟨-RFAP.HurwitzGeometry.imaginaryUnit,
      Or.inr (Or.inr (Or.inr rfl)), by
        rw [coefficientCase]
        decide⟩
  · exact ⟨RFAP.HurwitzGeometry.imaginaryUnit,
      Or.inr (Or.inr (Or.inl rfl)), by
        rw [coefficientCase]
        decide⟩
  · exact ⟨-1, Or.inr (Or.inl rfl), by
      rw [coefficientCase]
      decide⟩

/-- The parallelogram identity in the exact Gaussian-rational coordinate
model. -/
theorem normSq_sub_add_parallelogram (left right : Gaussian) :
    normSq (left - right) + normSq (left + right) =
      2 * (normSq left + normSq right) := by
  dsimp only [normSq]
  simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
    RFAP.ConstructiveGaussian.Gaussian.sub_im,
    RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.add_im]
  ring1

/-- A coordinate of a Gaussian rational in the open unit disc is strictly
larger than minus one. -/
theorem neg_one_lt_coordinate_of_square_lt_one {value : Coordinate}
    (small : value ^ 2 < 1) : -1 < value := by
  have lower : (-1 : Coordinate) ≤ value :=
    RFAP.ConstructiveFraction.neg_le_of_sq_le_sq_direct
      (show (0 : Coordinate) ≤ 1 by decide) small.le
  refine ⟨lower, ?_⟩
  intro reverse
  have equal : value = -1 := le_antisymm reverse lower
  rw [equal] at small
  exact (not_lt_of_ge (show (1 : Coordinate) ≤ 1 by decide) small)

theorem coordinate_lt_one_of_square_lt_one {value : Coordinate}
    (small : value ^ 2 < 1) : value < 1 := by
  have upper : value ≤ (1 : Coordinate) :=
    RFAP.ConstructiveFraction.le_of_sq_le_sq_direct
      (show (0 : Coordinate) ≤ 1 by decide) small.le
  refine ⟨upper, ?_⟩
  intro reverse
  have equal : value = 1 := le_antisymm upper reverse
  rw [equal] at small
  exact (not_lt_of_ge (show (1 : Coordinate) ≤ 1 by decide) small)

theorem real_square_lt_one_of_normSq_lt_one {value : Gaussian}
    (inside : normSq value < 1) : value.re ^ 2 < 1 :=
  (le_add_of_nonneg_right
    (RFAP.ConstructiveFraction.sq_nonneg_direct value.im)).trans_lt inside

theorem imaginary_square_lt_one_of_normSq_lt_one {value : Gaussian}
    (inside : normSq value < 1) : value.im ^ 2 < 1 := by
  have reordered : value.im ^ 2 + value.re ^ 2 < 1 := by
    calc
      value.im ^ 2 + value.re ^ 2 = normSq value := by
        dsimp only [normSq]
        ring1
      _ < 1 := inside
  exact (le_add_of_nonneg_right
    (RFAP.ConstructiveFraction.sq_nonneg_direct value.re)).trans_lt reordered

theorem neg_one_lt_real_of_normSq_lt_one {value : Gaussian}
    (inside : normSq value < 1) : -1 < value.re :=
  neg_one_lt_coordinate_of_square_lt_one
    (real_square_lt_one_of_normSq_lt_one inside)

theorem neg_one_lt_imaginary_of_normSq_lt_one {value : Gaussian}
    (inside : normSq value < 1) : -1 < value.im :=
  neg_one_lt_coordinate_of_square_lt_one
    (imaginary_square_lt_one_of_normSq_lt_one inside)

theorem real_lt_one_of_normSq_lt_one {value : Gaussian}
    (inside : normSq value < 1) : value.re < 1 :=
  coordinate_lt_one_of_square_lt_one
    (real_square_lt_one_of_normSq_lt_one inside)

theorem imaginary_lt_one_of_normSq_lt_one {value : Gaussian}
    (inside : normSq value < 1) : value.im < 1 :=
  coordinate_lt_one_of_square_lt_one
    (imaginary_square_lt_one_of_normSq_lt_one inside)

/-- The self-cylinder alternatives for opposite units must cross: one unit
escapes through the error coordinate and the opposite unit through the
denominator coordinate. -/
theorem opposite_self_obstructions_cross
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (unit : GaussianInt) (unitNorm : normNat unit = 1)
    (unitObstruction :
      (2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∨
        2 ≤ normSq (1 - toGaussian unit * denominatorRatio))
    (oppositeObstruction :
      (2 : Coordinate) ≤ normSq (errorRatio - toGaussian (-unit)) ∨
        2 ≤ normSq (1 - toGaussian (-unit) * denominatorRatio)) :
    ((2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∧
        2 ≤ normSq (1 - toGaussian (-unit) * denominatorRatio)) ∨
      ((2 : Coordinate) ≤ normSq (1 - toGaussian unit * denominatorRatio) ∧
        2 ≤ normSq (errorRatio - toGaussian (-unit))) := by
  have unitQuadrance : normSq (toGaussian unit) = (1 : Coordinate) := by
    rw [normSq_toGaussian, unitNorm]
    rfl
  have negatedUnitIdentity : toGaussian (-unit) = -toGaussian unit :=
    toGaussian_neg unit
  have errorParallelogram :
      normSq (errorRatio - toGaussian unit) +
          normSq (errorRatio - toGaussian (-unit)) =
        2 * (1 + normSq errorRatio) := by
    rw [negatedUnitIdentity]
    have plusIdentity :
        errorRatio - -toGaussian unit = errorRatio + toGaussian unit := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im] <;>
        ring1
    rw [plusIdentity, normSq_sub_add_parallelogram, unitQuadrance]
    ring1
  have errorNotBoth :
      ¬ ((2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∧
        2 ≤ normSq (errorRatio - toGaussian (-unit))) := by
    intro both
    exact RFAP.BestApproximation.not_both_opposite_exterior errorInside
      both.1 both.2 errorParallelogram
  have multipliedRatioQuadrance :
      normSq (toGaussian unit * denominatorRatio) =
        normSq denominatorRatio := by
    rw [normSq_mul, unitQuadrance]
    ring1
  have denominatorParallelogram :
      normSq (1 - toGaussian unit * denominatorRatio) +
          normSq (1 - toGaussian (-unit) * denominatorRatio) =
        2 * (1 + normSq denominatorRatio) := by
    rw [negatedUnitIdentity]
    have plusIdentity :
        (1 : Gaussian) - -toGaussian unit * denominatorRatio =
          1 + toGaussian unit * denominatorRatio := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
        ring1
    rw [plusIdentity, normSq_sub_add_parallelogram,
      multipliedRatioQuadrance, normSq_one]
  have denominatorNotBoth :
      ¬ ((2 : Coordinate) ≤
          normSq (1 - toGaussian unit * denominatorRatio) ∧
        2 ≤ normSq (1 - toGaussian (-unit) * denominatorRatio)) := by
    intro both
    exact RFAP.BestApproximation.not_both_opposite_exterior
      denominatorInside both.1 both.2 denominatorParallelogram
  rcases unitObstruction with unitError | unitDenominator
  · rcases oppositeObstruction with oppositeError | oppositeDenominator
    · exact (errorNotBoth ⟨unitError, oppositeError⟩).elim
    · exact Or.inl ⟨unitError, oppositeDenominator⟩
  · rcases oppositeObstruction with oppositeError | oppositeDenominator
    · exact Or.inr ⟨unitDenominator, oppositeError⟩
    · exact (denominatorNotBoth
        ⟨unitDenominator, oppositeDenominator⟩).elim

/-- For the `1+i` transition, the `-1` error translate cannot reach the
self-cylinder boundary. -/
theorem diagonalStep_negativeOne_error_impossible
    (errorRatio : Gaussian) (errorInside : normSq errorRatio < 1)
    (transition :
      normSq (1 + toGaussian diagonalStep * errorRatio) <
        normSq errorRatio) :
    ¬ (2 : Coordinate) ≤
      normSq (errorRatio - toGaussian (-1 : GaussianInt)) := by
  intro exterior
  let quadrance := normSq errorRatio
  have transitionExpanded :
      1 + quadrance + 2 * (errorRatio.re - errorRatio.im) < 0 := by
    have difference := RFAP.ConstructiveFraction.sub_neg_direct transition
    calc
      1 + quadrance + 2 * (errorRatio.re - errorRatio.im) =
          normSq (1 + toGaussian diagonalStep * errorRatio) -
            normSq errorRatio := by
        dsimp only [quadrance, diagonalStep, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im, Int.cast_one]
        ring1
      _ < 0 := difference
  have exteriorExpanded :
      (2 : Coordinate) ≤ 1 + quadrance + 2 * errorRatio.re := by
    calc
      (2 : Coordinate) ≤
          normSq (errorRatio - toGaussian (-1 : GaussianInt)) := exterior
      _ = 1 + quadrance + 2 * errorRatio.re := by
        dsimp only [quadrance, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
          Int.cast_neg, Int.cast_one, Int.cast_zero]
        ring1
  have twiceGapNegative :
      2 - 2 * errorRatio.im < (0 : Coordinate) := by
    calc
      2 - 2 * errorRatio.im ≤
          (1 + quadrance + 2 * errorRatio.re) -
            2 * errorRatio.im := by
        convert RFAP.ConstructiveFraction.add_le_add_right_direct
          exteriorExpanded (-2 * errorRatio.im) using 1 <;> ring1
      _ = 1 + quadrance +
          2 * (errorRatio.re - errorRatio.im) := by ring1
      _ < 0 := transitionExpanded
  have twiceOrdered : (2 : Coordinate) < 2 * errorRatio.im := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      twiceGapNegative (2 * errorRatio.im)
    convert shifted using 1
    all_goals ring1
  have imaginaryGreaterThanOne : (1 : Coordinate) < errorRatio.im := by
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := 2)
    · convert twiceOrdered using 1 <;> ring1
    · decide
  exact (not_lt_of_ge (imaginary_lt_one_of_normSq_lt_one errorInside).le)
    imaginaryGreaterThanOne

/-- For the `1+i` transition, the `i` error translate cannot reach the
self-cylinder boundary. -/
theorem diagonalStep_positiveImaginary_error_impossible
    (errorRatio : Gaussian) (errorInside : normSq errorRatio < 1)
    (transition :
      normSq (1 + toGaussian diagonalStep * errorRatio) <
        normSq errorRatio) :
    ¬ (2 : Coordinate) ≤ normSq
      (errorRatio - toGaussian RFAP.HurwitzGeometry.imaginaryUnit) := by
  intro exterior
  let quadrance := normSq errorRatio
  have transitionExpanded :
      1 + quadrance + 2 * (errorRatio.re - errorRatio.im) < 0 := by
    have difference := RFAP.ConstructiveFraction.sub_neg_direct transition
    calc
      1 + quadrance + 2 * (errorRatio.re - errorRatio.im) =
          normSq (1 + toGaussian diagonalStep * errorRatio) -
            normSq errorRatio := by
        dsimp only [quadrance, diagonalStep, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im, Int.cast_one]
        ring1
      _ < 0 := difference
  have exteriorExpanded :
      (2 : Coordinate) ≤ 1 + quadrance - 2 * errorRatio.im := by
    calc
      (2 : Coordinate) ≤ normSq
          (errorRatio -
            toGaussian RFAP.HurwitzGeometry.imaginaryUnit) := exterior
      _ = 1 + quadrance - 2 * errorRatio.im := by
        dsimp only [quadrance, normSq, toGaussian,
          RFAP.HurwitzGeometry.imaginaryUnit]
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im, Int.cast_one,
          Int.cast_zero]
        ring1
  have twiceSumNegative :
      2 + 2 * errorRatio.re < (0 : Coordinate) := by
    calc
      2 + 2 * errorRatio.re ≤
          (1 + quadrance - 2 * errorRatio.im) +
            2 * errorRatio.re := by
        exact RFAP.ConstructiveFraction.add_le_add_right_direct
          exteriorExpanded (2 * errorRatio.re)
      _ = 1 + quadrance +
          2 * (errorRatio.re - errorRatio.im) := by ring1
      _ < 0 := transitionExpanded
  have twiceOrdered :
      (2 : Coordinate) < 2 * (-errorRatio.re) := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      twiceSumNegative (-2 * errorRatio.re)
    convert shifted using 1
    all_goals ring1
  have negativeRealGreaterThanOne :
      (1 : Coordinate) < -errorRatio.re := by
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := 2)
    · convert twiceOrdered using 1 <;> ring1
    · decide
  have realLessThanNegativeOne : errorRatio.re < (-1 : Coordinate) := by
    have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct
      negativeRealGreaterThanOne
    simpa only [neg_neg] using negated
  exact (not_lt_of_ge
    (neg_one_lt_real_of_normSq_lt_one errorInside).le)
      realLessThanNegativeOne

/-- For the `1+i` denominator transition, the `-1` centered translate is
too small to reach twice the next denominator quadrance. -/
theorem diagonalStep_negativeOne_nextDenominator_impossible
    (denominatorRatio : Gaussian)
    (denominatorInside : normSq denominatorRatio < 1)
    (nextOutside :
      1 < normSq (denominatorRatio + toGaussian diagonalStep)) :
    ¬ (2 : Coordinate) *
        normSq (denominatorRatio + toGaussian diagonalStep) ≤
      normSq (1 -
        toGaussian (-1 : GaussianInt) * denominatorRatio) := by
  intro exterior
  let quadrance := normSq denominatorRatio
  have nextExpanded :
      0 < quadrance + 1 +
        2 * denominatorRatio.re + 2 * denominatorRatio.im := by
    have shifted := RFAP.ConstructiveFraction.sub_pos_direct nextOutside
    calc
      0 < normSq (denominatorRatio + toGaussian diagonalStep) - 1 := shifted
      _ = quadrance + 1 +
          2 * denominatorRatio.re + 2 * denominatorRatio.im := by
        dsimp only [quadrance, diagonalStep, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im, Int.cast_one]
        ring1
  have exteriorExpanded :
      2 * (quadrance + 2 +
          2 * denominatorRatio.re + 2 * denominatorRatio.im) ≤
        1 + quadrance + 2 * denominatorRatio.re := by
    calc
      2 * (quadrance + 2 +
          2 * denominatorRatio.re + 2 * denominatorRatio.im) =
          2 * normSq (denominatorRatio + toGaussian diagonalStep) := by
        dsimp only [quadrance, diagonalStep, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im, Int.cast_one]
        ring1
      _ ≤ normSq (1 -
          toGaussian (-1 : GaussianInt) * denominatorRatio) := exterior
      _ = 1 + quadrance + 2 * denominatorRatio.re := by
        dsimp only [quadrance, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
          Int.cast_neg, Int.cast_one, Int.cast_zero]
        ring1
  have exteriorPolynomial :
      quadrance + 3 + 2 * denominatorRatio.re +
          4 * denominatorRatio.im ≤ 0 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤
          (1 + quadrance + 2 * denominatorRatio.re) -
            2 * (quadrance + 2 +
              2 * denominatorRatio.re + 2 * denominatorRatio.im) :=
        RFAP.ConstructiveFraction.sub_nonneg_direct exteriorExpanded
      _ = 0 - (quadrance + 3 + 2 * denominatorRatio.re +
          4 * denominatorRatio.im) := by ring1
  have twiceSumNegative :
      2 + 2 * denominatorRatio.im < (0 : Coordinate) := by
    have polynomialLtNext :
        quadrance + 3 + 2 * denominatorRatio.re +
            4 * denominatorRatio.im <
          quadrance + 1 + 2 * denominatorRatio.re +
            2 * denominatorRatio.im :=
      lt_of_le_of_lt exteriorPolynomial nextExpanded
    have negativeDifference :=
      RFAP.ConstructiveFraction.sub_neg_direct polynomialLtNext
    convert negativeDifference using 1
    ring1
  have twiceOrdered :
      (2 : Coordinate) < 2 * (-denominatorRatio.im) := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      twiceSumNegative (-2 * denominatorRatio.im)
    convert shifted using 1 <;> ring1
  have negativeImaginaryGreaterThanOne :
      (1 : Coordinate) < -denominatorRatio.im := by
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := 2)
    · convert twiceOrdered using 1 <;> ring1
    · decide
  have imaginaryLessThanNegativeOne :
      denominatorRatio.im < (-1 : Coordinate) := by
    have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct
      negativeImaginaryGreaterThanOne
    simpa only [neg_neg] using negated
  exact (not_lt_of_ge
    (neg_one_lt_imaginary_of_normSq_lt_one denominatorInside).le)
      imaginaryLessThanNegativeOne

/-- The adjacent `i` centered translate is likewise too small for the next
denominator cylinder of a `1+i` transition. -/
theorem diagonalStep_positiveImaginary_nextDenominator_impossible
    (denominatorRatio : Gaussian)
    (denominatorInside : normSq denominatorRatio < 1)
    (nextOutside :
      1 < normSq (denominatorRatio + toGaussian diagonalStep)) :
    ¬ (2 : Coordinate) *
        normSq (denominatorRatio + toGaussian diagonalStep) ≤
      normSq (1 -
        toGaussian RFAP.HurwitzGeometry.imaginaryUnit *
          denominatorRatio) := by
  intro exterior
  let quadrance := normSq denominatorRatio
  have nextExpanded :
      0 < quadrance + 1 +
        2 * denominatorRatio.re + 2 * denominatorRatio.im := by
    have shifted := RFAP.ConstructiveFraction.sub_pos_direct nextOutside
    calc
      0 < normSq (denominatorRatio + toGaussian diagonalStep) - 1 := shifted
      _ = quadrance + 1 +
          2 * denominatorRatio.re + 2 * denominatorRatio.im := by
        dsimp only [quadrance, diagonalStep, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im, Int.cast_one]
        ring1
  have exteriorExpanded :
      2 * (quadrance + 2 +
          2 * denominatorRatio.re + 2 * denominatorRatio.im) ≤
        1 + quadrance + 2 * denominatorRatio.im := by
    calc
      2 * (quadrance + 2 +
          2 * denominatorRatio.re + 2 * denominatorRatio.im) =
          2 * normSq (denominatorRatio + toGaussian diagonalStep) := by
        dsimp only [quadrance, diagonalStep, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im, Int.cast_one]
        ring1
      _ ≤ normSq (1 -
          toGaussian RFAP.HurwitzGeometry.imaginaryUnit *
            denominatorRatio) := exterior
      _ = 1 + quadrance + 2 * denominatorRatio.im := by
        dsimp only [quadrance, normSq, toGaussian,
          RFAP.HurwitzGeometry.imaginaryUnit]
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im,
          Int.cast_one, Int.cast_zero]
        ring1
  have exteriorPolynomial :
      quadrance + 3 + 4 * denominatorRatio.re +
          2 * denominatorRatio.im ≤ 0 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤
          (1 + quadrance + 2 * denominatorRatio.im) -
            2 * (quadrance + 2 +
              2 * denominatorRatio.re + 2 * denominatorRatio.im) :=
        RFAP.ConstructiveFraction.sub_nonneg_direct exteriorExpanded
      _ = 0 - (quadrance + 3 + 4 * denominatorRatio.re +
          2 * denominatorRatio.im) := by ring1
  have twiceSumNegative :
      2 + 2 * denominatorRatio.re < (0 : Coordinate) := by
    have polynomialLtNext :
        quadrance + 3 + 4 * denominatorRatio.re +
            2 * denominatorRatio.im <
          quadrance + 1 + 2 * denominatorRatio.re +
            2 * denominatorRatio.im :=
      lt_of_le_of_lt exteriorPolynomial nextExpanded
    have negativeDifference :=
      RFAP.ConstructiveFraction.sub_neg_direct polynomialLtNext
    convert negativeDifference using 1
    ring1
  have twiceOrdered :
      (2 : Coordinate) < 2 * (-denominatorRatio.re) := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      twiceSumNegative (-2 * denominatorRatio.re)
    convert shifted using 1 <;> ring1
  have negativeRealGreaterThanOne :
      (1 : Coordinate) < -denominatorRatio.re := by
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := 2)
    · convert twiceOrdered using 1 <;> ring1
    · decide
  have realLessThanNegativeOne :
      denominatorRatio.re < (-1 : Coordinate) := by
    have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct
      negativeRealGreaterThanOne
    simpa only [neg_neg] using negated
  exact (not_lt_of_ge
    (neg_one_lt_real_of_normSq_lt_one denominatorInside).le)
      realLessThanNegativeOne

/-- The doubled diagonal transition still excludes the `-1` error exterior;
the factor-four error bound supplies the extra margin. -/
theorem doubledDiagonalStep_negativeOne_error_impossible
    (errorRatio : Gaussian) (errorInside : normSq errorRatio < 1)
    (factorFour : (1 : Coordinate) < 4 * normSq errorRatio)
    (transition :
      normSq (1 + toGaussian doubledDiagonalStep * errorRatio) <
        normSq errorRatio) :
    ¬ (2 : Coordinate) ≤
      normSq (errorRatio - toGaussian (-1 : GaussianInt)) := by
  intro exterior
  let quadrance := normSq errorRatio
  have transitionExpanded :
      1 + 7 * quadrance +
          4 * (errorRatio.re - errorRatio.im) < 0 := by
    have difference := RFAP.ConstructiveFraction.sub_neg_direct transition
    calc
      1 + 7 * quadrance + 4 * (errorRatio.re - errorRatio.im) =
          normSq (1 + toGaussian doubledDiagonalStep * errorRatio) -
            normSq errorRatio := by
        dsimp only [quadrance, doubledDiagonalStep, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im, Int.cast_ofNat]
        ring1
      _ < 0 := difference
  have exteriorExpanded :
      (2 : Coordinate) ≤ 1 + quadrance + 2 * errorRatio.re := by
    calc
      (2 : Coordinate) ≤
          normSq (errorRatio - toGaussian (-1 : GaussianInt)) := exterior
      _ = 1 + quadrance + 2 * errorRatio.re := by
        dsimp only [quadrance, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
          Int.cast_neg, Int.cast_one, Int.cast_zero]
        ring1
  have realBase : 1 - quadrance ≤ 2 * errorRatio.re := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance + 2 * errorRatio.re) - 2 :=
        RFAP.ConstructiveFraction.sub_nonneg_direct exteriorExpanded
      _ = 2 * errorRatio.re - (1 - quadrance) := by ring1
  have realScaled : 2 - 2 * quadrance ≤ 4 * errorRatio.re := by
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      realBase (show (0 : Coordinate) ≤ 2 by decide)
    convert scaled using 1
    all_goals ring1
  have lowerTransitionNegative :
      3 + 5 * quadrance - 4 * errorRatio.im < (0 : Coordinate) := by
    calc
      3 + 5 * quadrance - 4 * errorRatio.im ≤
          1 + 7 * quadrance +
            4 * (errorRatio.re - errorRatio.im) := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ 4 * errorRatio.re - (2 - 2 * quadrance) :=
            RFAP.ConstructiveFraction.sub_nonneg_direct realScaled
          _ =
              (1 + 7 * quadrance +
                  4 * (errorRatio.re - errorRatio.im)) -
                (3 + 5 * quadrance - 4 * errorRatio.im) := by ring1
      _ < 0 := transitionExpanded
  have quadrancePositive : 0 < quadrance := by
    have fourPositive : (0 : Coordinate) < 4 * quadrance :=
      (show (0 : Coordinate) < 1 by decide).trans factorFour
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := 4)
    · convert fourPositive using 1 <;> ring1
    · decide
  have fourQuadranceLtFive :
      4 * quadrance < 5 * quadrance := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      quadrancePositive (4 * quadrance)
    convert shifted using 1 <;> ring1
  have oneLtFiveQuadrance : (1 : Coordinate) < 5 * quadrance :=
    factorFour.trans fourQuadranceLtFive
  have fourLtThreePlusFive :
      (4 : Coordinate) < 3 + 5 * quadrance := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      oneLtFiveQuadrance 3
    convert shifted using 1 <;> ring1
  have fourGapNegative :
      4 - 4 * errorRatio.im < (0 : Coordinate) := by
    calc
      4 - 4 * errorRatio.im <
          3 + 5 * quadrance - 4 * errorRatio.im := by
        convert RFAP.ConstructiveFraction.add_lt_add_right_direct
          fourLtThreePlusFive (-4 * errorRatio.im) using 1 <;> ring1
      _ < 0 := lowerTransitionNegative
  have fourOrdered : (4 : Coordinate) < 4 * errorRatio.im := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      fourGapNegative (4 * errorRatio.im)
    convert shifted using 1 <;> ring1
  have imaginaryGreaterThanOne : (1 : Coordinate) < errorRatio.im := by
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := 4)
    · convert fourOrdered using 1 <;> ring1
    · decide
  exact (not_lt_of_ge (imaginary_lt_one_of_normSq_lt_one errorInside).le)
    imaginaryGreaterThanOne

/-- The adjacent `i` error exterior is excluded symmetrically for the
doubled diagonal transition. -/
theorem doubledDiagonalStep_positiveImaginary_error_impossible
    (errorRatio : Gaussian) (errorInside : normSq errorRatio < 1)
    (factorFour : (1 : Coordinate) < 4 * normSq errorRatio)
    (transition :
      normSq (1 + toGaussian doubledDiagonalStep * errorRatio) <
        normSq errorRatio) :
    ¬ (2 : Coordinate) ≤ normSq
      (errorRatio - toGaussian RFAP.HurwitzGeometry.imaginaryUnit) := by
  intro exterior
  let quadrance := normSq errorRatio
  have transitionExpanded :
      1 + 7 * quadrance +
          4 * (errorRatio.re - errorRatio.im) < 0 := by
    have difference := RFAP.ConstructiveFraction.sub_neg_direct transition
    calc
      1 + 7 * quadrance + 4 * (errorRatio.re - errorRatio.im) =
          normSq (1 + toGaussian doubledDiagonalStep * errorRatio) -
            normSq errorRatio := by
        dsimp only [quadrance, doubledDiagonalStep, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im, Int.cast_ofNat]
        ring1
      _ < 0 := difference
  have exteriorExpanded :
      (2 : Coordinate) ≤ 1 + quadrance - 2 * errorRatio.im := by
    calc
      (2 : Coordinate) ≤ normSq
          (errorRatio -
            toGaussian RFAP.HurwitzGeometry.imaginaryUnit) := exterior
      _ = 1 + quadrance - 2 * errorRatio.im := by
        dsimp only [quadrance, normSq, toGaussian,
          RFAP.HurwitzGeometry.imaginaryUnit]
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im, Int.cast_one,
          Int.cast_zero]
        ring1
  have imaginaryBase :
      1 - quadrance ≤ -2 * errorRatio.im := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance - 2 * errorRatio.im) - 2 :=
        RFAP.ConstructiveFraction.sub_nonneg_direct exteriorExpanded
      _ = -2 * errorRatio.im - (1 - quadrance) := by ring1
  have imaginaryScaled :
      2 - 2 * quadrance ≤ -4 * errorRatio.im := by
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      imaginaryBase (show (0 : Coordinate) ≤ 2 by decide)
    convert scaled using 1 <;> ring1
  have lowerTransitionNegative :
      3 + 5 * quadrance + 4 * errorRatio.re < (0 : Coordinate) := by
    calc
      3 + 5 * quadrance + 4 * errorRatio.re ≤
          1 + 7 * quadrance +
            4 * (errorRatio.re - errorRatio.im) := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ -4 * errorRatio.im - (2 - 2 * quadrance) :=
            RFAP.ConstructiveFraction.sub_nonneg_direct imaginaryScaled
          _ =
              (1 + 7 * quadrance +
                  4 * (errorRatio.re - errorRatio.im)) -
                (3 + 5 * quadrance + 4 * errorRatio.re) := by ring1
      _ < 0 := transitionExpanded
  have quadrancePositive : 0 < quadrance := by
    have fourPositive : (0 : Coordinate) < 4 * quadrance :=
      (show (0 : Coordinate) < 1 by decide).trans factorFour
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := 4)
    · convert fourPositive using 1 <;> ring1
    · decide
  have fourQuadranceLtFive :
      4 * quadrance < 5 * quadrance := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      quadrancePositive (4 * quadrance)
    convert shifted using 1 <;> ring1
  have oneLtFiveQuadrance : (1 : Coordinate) < 5 * quadrance :=
    factorFour.trans fourQuadranceLtFive
  have fourLtThreePlusFive :
      (4 : Coordinate) < 3 + 5 * quadrance := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      oneLtFiveQuadrance 3
    convert shifted using 1 <;> ring1
  have fourSumNegative :
      4 + 4 * errorRatio.re < (0 : Coordinate) := by
    calc
      4 + 4 * errorRatio.re <
          3 + 5 * quadrance + 4 * errorRatio.re := by
        exact RFAP.ConstructiveFraction.add_lt_add_right_direct
          fourLtThreePlusFive (4 * errorRatio.re)
      _ < 0 := lowerTransitionNegative
  have fourOrdered : (4 : Coordinate) < 4 * (-errorRatio.re) := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      fourSumNegative (-4 * errorRatio.re)
    convert shifted using 1 <;> ring1
  have negativeRealGreaterThanOne :
      (1 : Coordinate) < -errorRatio.re := by
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := 4)
    · convert fourOrdered using 1 <;> ring1
    · decide
  have realLessThanNegativeOne : errorRatio.re < (-1 : Coordinate) := by
    have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct
      negativeRealGreaterThanOne
    simpa only [neg_neg] using negated
  exact (not_lt_of_ge
    (neg_one_lt_real_of_normSq_lt_one errorInside).le)
      realLessThanNegativeOne

/-- The `-1` next-denominator exterior is impossible for the doubled
diagonal coefficient already from the open-unit-disc bound. -/
theorem doubledDiagonalStep_negativeOne_nextDenominator_impossible
    (denominatorRatio : Gaussian)
    (denominatorInside : normSq denominatorRatio < 1) :
    ¬ (2 : Coordinate) *
        normSq (denominatorRatio + toGaussian doubledDiagonalStep) ≤
      normSq (1 -
        toGaussian (-1 : GaussianInt) * denominatorRatio) := by
  intro exterior
  let quadrance := normSq denominatorRatio
  have exteriorExpanded :
      2 * (quadrance + 8 +
          4 * denominatorRatio.re + 4 * denominatorRatio.im) ≤
        1 + quadrance + 2 * denominatorRatio.re := by
    calc
      2 * (quadrance + 8 +
          4 * denominatorRatio.re + 4 * denominatorRatio.im) =
          2 * normSq
            (denominatorRatio + toGaussian doubledDiagonalStep) := by
        dsimp only [quadrance, doubledDiagonalStep, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im, Int.cast_ofNat]
        ring1
      _ ≤ normSq (1 -
          toGaussian (-1 : GaussianInt) * denominatorRatio) := exterior
      _ = 1 + quadrance + 2 * denominatorRatio.re := by
        dsimp only [quadrance, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
          Int.cast_neg, Int.cast_one, Int.cast_zero]
        ring1
  have exteriorPolynomial :
      quadrance + 15 + 6 * denominatorRatio.re +
          8 * denominatorRatio.im ≤ 0 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤
          (1 + quadrance + 2 * denominatorRatio.re) -
            2 * (quadrance + 8 +
              4 * denominatorRatio.re + 4 * denominatorRatio.im) :=
        RFAP.ConstructiveFraction.sub_nonneg_direct exteriorExpanded
      _ = 0 - (quadrance + 15 + 6 * denominatorRatio.re +
          8 * denominatorRatio.im) := by ring1
  have realShiftPositive :
      0 < denominatorRatio.re + (1 : Coordinate) := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      (neg_one_lt_real_of_normSq_lt_one denominatorInside) 1
    convert shifted using 1
    all_goals ring1
  have imaginaryShiftPositive :
      0 < denominatorRatio.im + (1 : Coordinate) := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      (neg_one_lt_imaginary_of_normSq_lt_one denominatorInside) 1
    convert shifted using 1
    all_goals ring1
  have sixRealPositive :
      0 < 6 * (denominatorRatio.re + 1) :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (by decide) realShiftPositive
  have eightImaginaryPositive :
      0 < 8 * (denominatorRatio.im + 1) :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (by decide) imaginaryShiftPositive
  have basePositive : 0 < quadrance + 1 := by
    calc
      (0 : Coordinate) < 1 := by decide
      _ ≤ quadrance + 1 := by
        have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
          (normSq_nonneg denominatorRatio) 1
        convert shifted using 1
        all_goals ring1
  have withRealPositive :
      0 < quadrance + 1 + 6 * (denominatorRatio.re + 1) := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      sixRealPositive (quadrance + 1)
    have increased :
        quadrance + 1 <
          6 * (denominatorRatio.re + 1) + (quadrance + 1) := by
      convert shifted using 1
      all_goals ring1
    have increased' :
        quadrance + 1 <
          quadrance + 1 + 6 * (denominatorRatio.re + 1) := by
      convert increased using 1
      all_goals ring1
    exact basePositive.trans increased'
  have polynomialPositive :
      0 < quadrance + 15 + 6 * denominatorRatio.re +
          8 * denominatorRatio.im := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      eightImaginaryPositive
        (quadrance + 1 + 6 * (denominatorRatio.re + 1))
    exact withRealPositive.trans (by
      calc
        quadrance + 1 + 6 * (denominatorRatio.re + 1) <
            8 * (denominatorRatio.im + 1) +
              (quadrance + 1 + 6 * (denominatorRatio.re + 1)) := by
          convert shifted using 1
          all_goals ring1
        _ = quadrance + 15 + 6 * denominatorRatio.re +
            8 * denominatorRatio.im := by ring1)
  exact (not_lt_of_ge exteriorPolynomial) polynomialPositive

/-- The adjacent `i` next-denominator exterior is impossible by the same
finite coordinate estimate. -/
theorem doubledDiagonalStep_positiveImaginary_nextDenominator_impossible
    (denominatorRatio : Gaussian)
    (denominatorInside : normSq denominatorRatio < 1) :
    ¬ (2 : Coordinate) *
        normSq (denominatorRatio + toGaussian doubledDiagonalStep) ≤
      normSq (1 -
        toGaussian RFAP.HurwitzGeometry.imaginaryUnit *
          denominatorRatio) := by
  intro exterior
  let quadrance := normSq denominatorRatio
  have exteriorExpanded :
      2 * (quadrance + 8 +
          4 * denominatorRatio.re + 4 * denominatorRatio.im) ≤
        1 + quadrance + 2 * denominatorRatio.im := by
    calc
      2 * (quadrance + 8 +
          4 * denominatorRatio.re + 4 * denominatorRatio.im) =
          2 * normSq
            (denominatorRatio + toGaussian doubledDiagonalStep) := by
        dsimp only [quadrance, doubledDiagonalStep, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im, Int.cast_ofNat]
        ring1
      _ ≤ normSq (1 -
          toGaussian RFAP.HurwitzGeometry.imaginaryUnit *
            denominatorRatio) := exterior
      _ = 1 + quadrance + 2 * denominatorRatio.im := by
        dsimp only [quadrance, normSq, toGaussian,
          RFAP.HurwitzGeometry.imaginaryUnit]
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im,
          Int.cast_one, Int.cast_zero]
        ring1
  have exteriorPolynomial :
      quadrance + 15 + 8 * denominatorRatio.re +
          6 * denominatorRatio.im ≤ 0 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤
          (1 + quadrance + 2 * denominatorRatio.im) -
            2 * (quadrance + 8 +
              4 * denominatorRatio.re + 4 * denominatorRatio.im) :=
        RFAP.ConstructiveFraction.sub_nonneg_direct exteriorExpanded
      _ = 0 - (quadrance + 15 + 8 * denominatorRatio.re +
          6 * denominatorRatio.im) := by ring1
  have realShiftPositive :
      0 < denominatorRatio.re + (1 : Coordinate) := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      (neg_one_lt_real_of_normSq_lt_one denominatorInside) 1
    convert shifted using 1
    all_goals ring1
  have imaginaryShiftPositive :
      0 < denominatorRatio.im + (1 : Coordinate) := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      (neg_one_lt_imaginary_of_normSq_lt_one denominatorInside) 1
    convert shifted using 1
    all_goals ring1
  have eightRealPositive :
      0 < 8 * (denominatorRatio.re + 1) :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (by decide) realShiftPositive
  have sixImaginaryPositive :
      0 < 6 * (denominatorRatio.im + 1) :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (by decide) imaginaryShiftPositive
  have basePositive : 0 < quadrance + 1 := by
    calc
      (0 : Coordinate) < 1 := by decide
      _ ≤ quadrance + 1 := by
        have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
          (normSq_nonneg denominatorRatio) 1
        convert shifted using 1
        all_goals ring1
  have withRealPositive :
      0 < quadrance + 1 + 8 * (denominatorRatio.re + 1) := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      eightRealPositive (quadrance + 1)
    have increased :
        quadrance + 1 <
          8 * (denominatorRatio.re + 1) + (quadrance + 1) := by
      convert shifted using 1
      all_goals ring1
    have increased' :
        quadrance + 1 <
          quadrance + 1 + 8 * (denominatorRatio.re + 1) := by
      convert increased using 1
      all_goals ring1
    exact basePositive.trans increased'
  have polynomialPositive :
      0 < quadrance + 15 + 8 * denominatorRatio.re +
          6 * denominatorRatio.im := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      sixImaginaryPositive
        (quadrance + 1 + 8 * (denominatorRatio.re + 1))
    exact withRealPositive.trans (by
      calc
        quadrance + 1 + 8 * (denominatorRatio.re + 1) <
            6 * (denominatorRatio.im + 1) +
              (quadrance + 1 + 8 * (denominatorRatio.re + 1)) := by
          convert shifted using 1
          all_goals ring1
        _ = quadrance + 15 + 8 * denominatorRatio.re +
            6 * denominatorRatio.im := by ring1)
  exact (not_lt_of_ge exteriorPolynomial) polynomialPositive

/-- An axial `2` transition excludes the opposite `-1` error exterior. -/
theorem doubledAxisStep_negativeOne_error_impossible
    (errorRatio : Gaussian)
    (transition :
      normSq (1 + toGaussian doubledAxisStep * errorRatio) <
        normSq errorRatio) :
    ¬ (2 : Coordinate) ≤
      normSq (errorRatio - toGaussian (-1 : GaussianInt)) := by
  intro exterior
  let quadrance := normSq errorRatio
  have transitionExpanded :
      1 + 3 * quadrance + 4 * errorRatio.re < 0 := by
    have difference := RFAP.ConstructiveFraction.sub_neg_direct transition
    calc
      1 + 3 * quadrance + 4 * errorRatio.re =
          normSq (1 + toGaussian doubledAxisStep * errorRatio) -
            normSq errorRatio := by
        dsimp only [quadrance, doubledAxisStep, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im, Int.cast_ofNat,
          Int.cast_zero]
        ring1
      _ < 0 := difference
  have exteriorExpanded :
      (2 : Coordinate) ≤ 1 + quadrance + 2 * errorRatio.re := by
    calc
      (2 : Coordinate) ≤
          normSq (errorRatio - toGaussian (-1 : GaussianInt)) := exterior
      _ = 1 + quadrance + 2 * errorRatio.re := by
        dsimp only [quadrance, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
          Int.cast_neg, Int.cast_one, Int.cast_zero]
        ring1
  have realBase : 1 - quadrance ≤ 2 * errorRatio.re := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance + 2 * errorRatio.re) - 2 :=
        RFAP.ConstructiveFraction.sub_nonneg_direct exteriorExpanded
      _ = 2 * errorRatio.re - (1 - quadrance) := by ring1
  have realScaled : 2 - 2 * quadrance ≤ 4 * errorRatio.re := by
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      realBase (show (0 : Coordinate) ≤ 2 by decide)
    convert scaled using 1 <;> ring1
  have positiveLower : 0 < 3 + quadrance := by
    calc
      (0 : Coordinate) < 3 := by decide
      _ ≤ 3 + quadrance := by
        have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
          (normSq_nonneg errorRatio) 3
        convert shifted using 1 <;> ring1
  have lowerNegative : 3 + quadrance < (0 : Coordinate) := by
    calc
      3 + quadrance ≤ 1 + 3 * quadrance + 4 * errorRatio.re := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ 4 * errorRatio.re - (2 - 2 * quadrance) :=
            RFAP.ConstructiveFraction.sub_nonneg_direct realScaled
          _ = (1 + 3 * quadrance + 4 * errorRatio.re) -
              (3 + quadrance) := by ring1
      _ < 0 := transitionExpanded
  exact (not_lt_of_ge positiveLower.le) lowerNegative

/-- For the axial coefficient, the `-1` next-denominator exterior is already
incompatible with the open unit disc. -/
theorem doubledAxisStep_negativeOne_nextDenominator_impossible
    (denominatorRatio : Gaussian)
    (denominatorInside : normSq denominatorRatio < 1) :
    ¬ (2 : Coordinate) *
        normSq (denominatorRatio + toGaussian doubledAxisStep) ≤
      normSq (1 -
        toGaussian (-1 : GaussianInt) * denominatorRatio) := by
  intro exterior
  let quadrance := normSq denominatorRatio
  have exteriorExpanded :
      2 * (quadrance + 4 + 4 * denominatorRatio.re) ≤
        1 + quadrance + 2 * denominatorRatio.re := by
    calc
      2 * (quadrance + 4 + 4 * denominatorRatio.re) =
          2 * normSq
            (denominatorRatio + toGaussian doubledAxisStep) := by
        dsimp only [quadrance, doubledAxisStep, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im, Int.cast_ofNat,
          Int.cast_zero]
        ring1
      _ ≤ normSq (1 -
          toGaussian (-1 : GaussianInt) * denominatorRatio) := exterior
      _ = 1 + quadrance + 2 * denominatorRatio.re := by
        dsimp only [quadrance, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
          Int.cast_neg, Int.cast_one, Int.cast_zero]
        ring1
  have exteriorPolynomial :
      quadrance + 7 + 6 * denominatorRatio.re ≤ 0 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance + 2 * denominatorRatio.re) -
          2 * (quadrance + 4 + 4 * denominatorRatio.re) :=
        RFAP.ConstructiveFraction.sub_nonneg_direct exteriorExpanded
      _ = 0 - (quadrance + 7 + 6 * denominatorRatio.re) := by ring1
  have realShiftPositive :
      0 < denominatorRatio.re + (1 : Coordinate) := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      (neg_one_lt_real_of_normSq_lt_one denominatorInside) 1
    convert shifted using 1
    all_goals ring1
  have sixRealPositive :
      0 < 6 * (denominatorRatio.re + 1) :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (by decide) realShiftPositive
  have basePositive : 0 < quadrance + 1 := by
    calc
      (0 : Coordinate) < 1 := by decide
      _ ≤ quadrance + 1 := by
        have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
          (normSq_nonneg denominatorRatio) 1
        convert shifted using 1
        all_goals ring1
  have polynomialPositive :
      0 < quadrance + 7 + 6 * denominatorRatio.re := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      sixRealPositive (quadrance + 1)
    have increased : quadrance + 1 <
        6 * (denominatorRatio.re + 1) + (quadrance + 1) := by
      convert shifted using 1
      all_goals ring1
    exact basePositive.trans (by
      calc
        quadrance + 1 <
            6 * (denominatorRatio.re + 1) + (quadrance + 1) := increased
        _ = quadrance + 7 + 6 * denominatorRatio.re := by ring1)
  exact (not_lt_of_ge exteriorPolynomial) polynomialPositive

/-- Once the two transition-specific error exteriors and the two
transition-specific denominator exteriors have been excluded, the four
remaining cylinder branches are exactly the irrational diagonal boundary
pattern. -/
theorem diagonal_obstruction_core_impossible
    (errorRatio denominatorRatio nextDenominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (selfObstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∨
        2 ≤ normSq (1 - toGaussian unit * denominatorRatio))
    (nextObstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) * normSq errorRatio ≤
          normSq (errorRatio - toGaussian unit) ∨
        2 * normSq nextDenominatorRatio ≤
          normSq (1 - toGaussian unit * denominatorRatio))
    (negativeOneErrorImpossible :
      ¬ (2 : Coordinate) ≤
        normSq (errorRatio - toGaussian (-1 : GaussianInt)))
    (positiveImaginaryErrorImpossible :
      ¬ (2 : Coordinate) ≤ normSq
        (errorRatio -
          toGaussian RFAP.HurwitzGeometry.imaginaryUnit))
    (negativeOneNextDenominatorImpossible :
      ¬ (2 : Coordinate) * normSq nextDenominatorRatio ≤
        normSq (1 -
          toGaussian (-1 : GaussianInt) * denominatorRatio))
    (positiveImaginaryNextDenominatorImpossible :
      ¬ (2 : Coordinate) * normSq nextDenominatorRatio ≤
        normSq (1 -
          toGaussian RFAP.HurwitzGeometry.imaginaryUnit *
            denominatorRatio)) :
    False := by
  have realCross := opposite_self_obstructions_cross errorRatio
    denominatorRatio errorInside denominatorInside 1 rfl
    (selfObstruction 1 rfl) (selfObstruction (-1) (by decide))
  obtain ⟨positiveOneError, negativeOneDenominator⟩ :=
    realCross.resolve_right (fun alternative =>
      negativeOneErrorImpossible alternative.2)
  have imaginaryCross := opposite_self_obstructions_cross errorRatio
    denominatorRatio errorInside denominatorInside
    RFAP.HurwitzGeometry.imaginaryUnit (by decide)
    (selfObstruction RFAP.HurwitzGeometry.imaginaryUnit (by decide))
    (selfObstruction (-RFAP.HurwitzGeometry.imaginaryUnit) (by decide))
  obtain ⟨positiveImaginaryDenominator, negativeImaginaryError⟩ :=
    imaginaryCross.resolve_left (fun alternative =>
      positiveImaginaryErrorImpossible alternative.1)
  have negativeOneNext := nextObstruction (-1) (by decide)
  have negativeOneNextError := negativeOneNext.resolve_right
    negativeOneNextDenominatorImpossible
  have positiveImaginaryNext :=
    nextObstruction RFAP.HurwitzGeometry.imaginaryUnit (by decide)
  have positiveImaginaryNextError := positiveImaginaryNext.resolve_right
    positiveImaginaryNextDenominatorImpossible
  have positiveOneIdentity :
      errorRatio - toGaussian (1 : GaussianInt) = errorRatio - 1 := by
    rw [toGaussian_one]
  have negativeOneIdentity :
      errorRatio - toGaussian (-1 : GaussianInt) = errorRatio + 1 := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [toGaussian_neg, toGaussian_one,
        RFAP.ConstructiveGaussian.Gaussian.neg_re,
        RFAP.ConstructiveGaussian.Gaussian.neg_im,
        RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        RFAP.ConstructiveGaussian.Gaussian.one_re,
        RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
      ring1
  have negativeImaginaryIdentity :
      errorRatio -
          toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit) =
        errorRatio +
          toGaussian RFAP.HurwitzGeometry.imaginaryUnit := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [toGaussian_neg,
        RFAP.ConstructiveGaussian.Gaussian.neg_re,
        RFAP.ConstructiveGaussian.Gaussian.neg_im,
        RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;>
      ring1
  rw [positiveOneIdentity] at positiveOneError
  rw [negativeOneIdentity] at negativeOneNextError
  rw [negativeImaginaryIdentity] at negativeImaginaryError
  exact RFAP.BestApproximation.centered_diagonal_error_pattern_impossible
    1 errorRatio (by decide) positiveOneError negativeOneNextError
      positiveImaginaryNextError negativeImaginaryError

/-- Complete finite normalized exclusion for the canonical `1+i`
coefficient. -/
theorem diagonalStep_obstructions_impossible
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (errorTransition :
      normSq (1 + toGaussian diagonalStep * errorRatio) <
        normSq errorRatio)
    (denominatorTransition :
      1 < normSq (denominatorRatio + toGaussian diagonalStep))
    (selfObstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∨
        2 ≤ normSq (1 - toGaussian unit * denominatorRatio))
    (nextObstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) * normSq errorRatio ≤
          normSq (errorRatio - toGaussian unit) ∨
        2 * normSq (denominatorRatio + toGaussian diagonalStep) ≤
          normSq (1 - toGaussian unit * denominatorRatio)) :
    False := by
  exact diagonal_obstruction_core_impossible errorRatio denominatorRatio
    (denominatorRatio + toGaussian diagonalStep) errorInside
    denominatorInside selfObstruction nextObstruction
    (diagonalStep_negativeOne_error_impossible errorRatio errorInside
      errorTransition)
    (diagonalStep_positiveImaginary_error_impossible errorRatio errorInside
      errorTransition)
    (diagonalStep_negativeOne_nextDenominator_impossible denominatorRatio
      denominatorInside denominatorTransition)
    (diagonalStep_positiveImaginary_nextDenominator_impossible
      denominatorRatio denominatorInside denominatorTransition)

/-- Complete finite normalized exclusion for the canonical `2+2i`
coefficient. -/
theorem doubledDiagonalStep_obstructions_impossible
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (factorFour : (1 : Coordinate) < 4 * normSq errorRatio)
    (denominatorInside : normSq denominatorRatio < 1)
    (errorTransition :
      normSq (1 + toGaussian doubledDiagonalStep * errorRatio) <
        normSq errorRatio)
    (selfObstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∨
        2 ≤ normSq (1 - toGaussian unit * denominatorRatio))
    (nextObstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) * normSq errorRatio ≤
          normSq (errorRatio - toGaussian unit) ∨
        2 * normSq
            (denominatorRatio + toGaussian doubledDiagonalStep) ≤
          normSq (1 - toGaussian unit * denominatorRatio)) :
    False := by
  exact diagonal_obstruction_core_impossible errorRatio denominatorRatio
    (denominatorRatio + toGaussian doubledDiagonalStep) errorInside
    denominatorInside selfObstruction nextObstruction
    (doubledDiagonalStep_negativeOne_error_impossible errorRatio errorInside
      factorFour errorTransition)
    (doubledDiagonalStep_positiveImaginary_error_impossible errorRatio
      errorInside factorFour errorTransition)
    (doubledDiagonalStep_negativeOne_nextDenominator_impossible
      denominatorRatio denominatorInside)
    (doubledDiagonalStep_positiveImaginary_nextDenominator_impossible
      denominatorRatio denominatorInside)

/-- Complete finite normalized exclusion for the canonical axial coefficient
`2`.  The two real unit translates pin an exact boundary equality; the
factor-four estimate then makes the axial transition inequality impossible. -/
theorem doubledAxisStep_obstructions_impossible
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (factorFour : (1 : Coordinate) < 4 * normSq errorRatio)
    (denominatorInside : normSq denominatorRatio < 1)
    (errorTransition :
      normSq (1 + toGaussian doubledAxisStep * errorRatio) <
        normSq errorRatio)
    (selfObstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∨
        2 ≤ normSq (1 - toGaussian unit * denominatorRatio))
    (nextObstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) * normSq errorRatio ≤
          normSq (errorRatio - toGaussian unit) ∨
        2 * normSq (denominatorRatio + toGaussian doubledAxisStep) ≤
          normSq (1 - toGaussian unit * denominatorRatio)) :
    False := by
  have realCross := opposite_self_obstructions_cross errorRatio
    denominatorRatio errorInside denominatorInside 1 rfl
    (selfObstruction 1 rfl) (selfObstruction (-1) (by decide))
  obtain ⟨positiveOneError, _⟩ := realCross.resolve_right
    (fun alternative =>
      doubledAxisStep_negativeOne_error_impossible errorRatio
        errorTransition alternative.2)
  have negativeOneNext := nextObstruction (-1) (by decide)
  have negativeOneNextError := negativeOneNext.resolve_right
    (doubledAxisStep_negativeOne_nextDenominator_impossible
      denominatorRatio denominatorInside)
  let quadrance := normSq errorRatio
  have positiveOneExpanded :
      (2 : Coordinate) ≤ 1 + quadrance - 2 * errorRatio.re := by
    calc
      (2 : Coordinate) ≤
          normSq (errorRatio - toGaussian (1 : GaussianInt)) :=
        positiveOneError
      _ = 1 + quadrance - 2 * errorRatio.re := by
        dsimp only [quadrance, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
          Int.cast_one, Int.cast_zero]
        ring1
  have negativeOneExpanded :
      2 * quadrance ≤ 1 + quadrance + 2 * errorRatio.re := by
    calc
      2 * quadrance ≤
          normSq (errorRatio - toGaussian (-1 : GaussianInt)) :=
        negativeOneNextError
      _ = 1 + quadrance + 2 * errorRatio.re := by
        dsimp only [quadrance, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
          Int.cast_neg, Int.cast_one, Int.cast_zero]
        ring1
  have realUpper : 2 * errorRatio.re ≤ quadrance - 1 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance - 2 * errorRatio.re) - 2 :=
        RFAP.ConstructiveFraction.sub_nonneg_direct positiveOneExpanded
      _ = (quadrance - 1) - 2 * errorRatio.re := by ring1
  have realLower : quadrance - 1 ≤ 2 * errorRatio.re := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance + 2 * errorRatio.re) - 2 * quadrance :=
        RFAP.ConstructiveFraction.sub_nonneg_direct negativeOneExpanded
      _ = 2 * errorRatio.re - (quadrance - 1) := by ring1
  have realIdentity : 2 * errorRatio.re = quadrance - 1 :=
    le_antisymm realUpper realLower
  have realScaledIdentity :
      4 * errorRatio.re = 2 * (quadrance - 1) := by
    have scaled := congrArg (fun value : Coordinate => 2 * value)
      realIdentity
    convert scaled using 1
    all_goals ring1
  have transitionExpanded :
      1 + 3 * quadrance + 4 * errorRatio.re < 0 := by
    have difference := RFAP.ConstructiveFraction.sub_neg_direct
      errorTransition
    calc
      1 + 3 * quadrance + 4 * errorRatio.re =
          normSq (1 + toGaussian doubledAxisStep * errorRatio) -
            normSq errorRatio := by
        dsimp only [quadrance, doubledAxisStep, normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im, Int.cast_ofNat,
          Int.cast_zero]
        ring1
      _ < 0 := difference
  have fiveQuadranceLtOne : 5 * quadrance < (1 : Coordinate) := by
    apply RFAP.ConstructiveFraction.lt_of_sub_neg_direct
    calc
      5 * quadrance - 1 =
          1 + 3 * quadrance + 4 * errorRatio.re := by
        rw [realScaledIdentity]
        ring1
      _ < 0 := transitionExpanded
  have quadrancePositive : 0 < quadrance := by
    have fourPositive : (0 : Coordinate) < 4 * quadrance :=
      (show (0 : Coordinate) < 1 by decide).trans factorFour
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := 4)
    · convert fourPositive using 1 <;> ring1
    · decide
  have fourQuadranceLtFive :
      4 * quadrance < 5 * quadrance := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      quadrancePositive (4 * quadrance)
    convert shifted using 1 <;> ring1
  exact (not_lt_of_ge fiveQuadranceLtOne.le)
    (factorFour.trans fourQuadranceLtFive)

/-- Normalized cylinder data with a quadrance-two transition coefficient is
impossible, after rotating its displayed coefficient to `1+i`. -/
theorem NormalizedCylinderData.impossible_of_coefficientNorm_eq_two
    {coefficient : GaussianInt} (data : NormalizedCylinderData coefficient)
    (coefficientNorm : normNat coefficient = 2) : False := by
  obtain ⟨associate, associateProperty, associated⟩ :=
    exists_unit_associate_of_normNat_eq_two coefficient coefficientNorm
  let canonicalData := transportNormalizedData coefficient diagonalStep
    associate associateProperty associated data
  exact diagonalStep_obstructions_impossible canonicalData.errorRatio
    canonicalData.denominatorRatio canonicalData.errorInside
    canonicalData.denominatorInside canonicalData.errorTransition
    canonicalData.denominatorTransition canonicalData.selfObstruction
    canonicalData.nextObstruction

/-- Normalized cylinder data with a quadrance-four transition coefficient is
impossible, after rotating its displayed coefficient to `2`. -/
theorem NormalizedCylinderData.impossible_of_coefficientNorm_eq_four
    {coefficient : GaussianInt} (data : NormalizedCylinderData coefficient)
    (coefficientNorm : normNat coefficient = 4) : False := by
  obtain ⟨associate, associateProperty, associated⟩ :=
    exists_unit_associate_of_normNat_eq_four coefficient coefficientNorm
  let canonicalData := transportNormalizedData coefficient doubledAxisStep
    associate associateProperty associated data
  exact doubledAxisStep_obstructions_impossible canonicalData.errorRatio
    canonicalData.denominatorRatio canonicalData.errorInside
    canonicalData.factorFour canonicalData.denominatorInside
    canonicalData.errorTransition canonicalData.selfObstruction
    canonicalData.nextObstruction

/-- Normalized cylinder data with a quadrance-eight transition coefficient is
impossible, after rotating its displayed coefficient to `2+2i`. -/
theorem NormalizedCylinderData.impossible_of_coefficientNorm_eq_eight
    {coefficient : GaussianInt} (data : NormalizedCylinderData coefficient)
    (coefficientNorm : normNat coefficient = 8) : False := by
  obtain ⟨associate, associateProperty, associated⟩ :=
    exists_unit_associate_of_normNat_eq_eight coefficient coefficientNorm
  let canonicalData := transportNormalizedData coefficient
    doubledDiagonalStep associate associateProperty associated data
  exact doubledDiagonalStep_obstructions_impossible canonicalData.errorRatio
    canonicalData.denominatorRatio canonicalData.errorInside
    canonicalData.factorFour canonicalData.denominatorInside
    canonicalData.errorTransition canonicalData.selfObstruction
    canonicalData.nextObstruction

/-- The three coefficient quadrances left by the bounded repeated-index
normal form are all impossible. -/
theorem NormalizedCylinderData.impossible_of_coefficientNorm_cases
    {coefficient : GaussianInt} (data : NormalizedCylinderData coefficient)
    (coefficientNorm : normNat coefficient = 2 ∨
      normNat coefficient = 4 ∨ normNat coefficient = 8) : False := by
  rcases coefficientNorm with normTwo | normFour | normEight
  · exact data.impossible_of_coefficientNorm_eq_two normTwo
  · exact data.impossible_of_coefficientNorm_eq_four normFour
  · exact data.impossible_of_coefficientNorm_eq_eight normEight

/-- Two consecutive best-approximation transitions cannot both have
coefficient-index quadrance two.  The proof constructs the normalized
cylinder record directly from the finite normal form and invokes the
three-case normalized exclusion above. -/
theorem repeatedIndexTwo_impossible
    {source : Fraction} {lower middle upper : Pair}
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper)
    (leftIndexTwo :
      RFAP.BestApproximation.coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo :
      RFAP.BestApproximation.coefficientIndexQuadrance middle upper = 2) :
    False := by
  obtain ⟨lowerUnit, step, lowerUnitNorm, stepCases, transitionIdentity⟩ :=
    first.repeatedIndexTwo_finiteNormalForm second leftIndexTwo rightIndexTwo
  let determinantValue :=
    RFAP.BestApproximation.coefficientDeterminant lower middle
  let coefficient := determinantValue * step
  let largeError :=
    toGaussian lowerUnit * RFAP.HurwitzApproximation.error source.value lower
  let smallError := RFAP.HurwitzApproximation.error source.value middle
  let nextError := RFAP.HurwitzApproximation.error source.value upper
  let lowerDenominator :=
    toGaussian lowerUnit * toGaussian lower.denominator
  let middleDenominator := toGaussian middle.denominator
  let upperDenominator := toGaussian upper.denominator
  have determinantNorm : normNat determinantValue = 2 := by
    simpa only [determinantValue,
      RFAP.BestApproximation.coefficientIndexQuadrance] using leftIndexTwo
  have coefficientNormCases :
      normNat coefficient = 2 ∨ normNat coefficient = 4 ∨
        normNat coefficient = 8 := by
    dsimp only [coefficient]
    rw [RFAP.HurwitzGeometry.normNat_mul, determinantNorm]
    rcases stepCases with stepOne | stepTwo | stepFour
    · exact Or.inl (by rw [stepOne])
    · exact Or.inr (Or.inl (by rw [stepTwo]))
    · exact Or.inr (Or.inr (by rw [stepFour]))
  have largeErrorNorm :
      normSq largeError =
        normSq (RFAP.HurwitzApproximation.error source.value lower) := by
    dsimp only [largeError]
    rw [normSq_mul, normSq_toGaussian, lowerUnitNorm]
    ring1
  have lowerDenominatorNorm :
      normSq lowerDenominator = normSq (toGaussian lower.denominator) := by
    dsimp only [lowerDenominator]
    rw [normSq_mul, normSq_toGaussian, lowerUnitNorm]
    ring1
  have rawErrorOrdered :
      normSq (RFAP.HurwitzApproximation.error source.value middle) <
        normSq (RFAP.HurwitzApproximation.error source.value lower) :=
    first.2.1.2.1 lower first.1.1 first.2.2.1
  have largeErrorNonzero : largeError ≠ 0 := by
    intro largeErrorZero
    have lowerNormZero := congrArg normSq largeErrorZero
    rw [largeErrorNorm, normSq_zero] at lowerNormZero
    have impossible := rawErrorOrdered
    rw [lowerNormZero] at impossible
    exact (not_lt_of_ge
      (normSq_nonneg
        (RFAP.HurwitzApproximation.error source.value middle))) impossible
  have middleDenominatorNonzero : middleDenominator ≠ 0 := by
    intro middleZero
    apply first.2.1.1
    apply toGaussian_eq_zero.mp
    exact middleZero
  have errorOrdered : normSq smallError < normSq largeError := by
    rw [largeErrorNorm]
    exact rawErrorOrdered
  have nextErrorOrdered : normSq nextError < normSq smallError := by
    dsimp only [nextError, smallError]
    exact second.2.1.2.1 middle second.1.1 second.2.2.1
  have factorFour : normSq largeError < 4 * normSq smallError := by
    rw [largeErrorNorm]
    dsimp only [smallError]
    exact first.errorQuadrance_lower_lt_four_mul_upper_of_index_two
      leftIndexTwo
  have denominatorOrdered :
      normSq lowerDenominator < normSq middleDenominator := by
    rw [lowerDenominatorNorm]
    dsimp only [middleDenominator]
    rw [normSq_toGaussian, normSq_toGaussian]
    exact RFAP.ConstructiveFraction.natCast_lt_direct first.2.2.1
  have nextDenominatorOrdered :
      normSq middleDenominator < normSq upperDenominator := by
    dsimp only [middleDenominator, upperDenominator]
    rw [normSq_toGaussian, normSq_toGaussian]
    exact RFAP.ConstructiveFraction.natCast_lt_direct second.2.2.1
  have errorIdentity :
      nextError = largeError + toGaussian coefficient * smallError := by
    dsimp only [nextError, largeError, coefficient, determinantValue,
      smallError]
    rw [transitionIdentity,
      RFAP.BestApproximation.error_linearCombination]
  have denominatorIdentity :
      upperDenominator =
        lowerDenominator + toGaussian coefficient * middleDenominator := by
    dsimp only [upperDenominator, lowerDenominator, coefficient,
      determinantValue, middleDenominator]
    rw [transitionIdentity]
    simp only [RFAP.BestApproximation.linearCombination, toGaussian_add,
      toGaussian_mul]
  have selfObstruction (unit : GaussianInt) (unitNorm : normNat unit = 1) :
      (2 : Coordinate) * normSq largeError ≤
          normSq (smallError - toGaussian unit * largeError) ∨
        2 * normSq middleDenominator ≤
          normSq (middleDenominator -
            toGaussian unit * lowerDenominator) := by
    let sourceUnit := unit * lowerUnit
    have sourceUnitNorm : normNat sourceUnit = 1 := by
      dsimp only [sourceUnit]
      rw [RFAP.HurwitzGeometry.normNat_mul, unitNorm, lowerUnitNorm]
    have obstruction := first.centeredUnit_selfCoordinateObstruction
      leftIndexTwo sourceUnit sourceUnitNorm
    rw [largeErrorNorm]
    simpa only [largeError, smallError, lowerDenominator,
      middleDenominator, sourceUnit, toGaussian_mul,
      RFAP.ConstructiveGaussian.Gaussian.mul_assoc] using obstruction
  have nextObstruction (unit : GaussianInt) (unitNorm : normNat unit = 1) :
      (2 : Coordinate) * normSq smallError ≤
          normSq (smallError - toGaussian unit * largeError) ∨
        2 * normSq upperDenominator ≤
          normSq (middleDenominator -
            toGaussian unit * lowerDenominator) := by
    let sourceUnit := unit * lowerUnit
    have sourceUnitNorm : normNat sourceUnit = 1 := by
      dsimp only [sourceUnit]
      rw [RFAP.HurwitzGeometry.normNat_mul, unitNorm, lowerUnitNorm]
    have obstruction := first.centeredUnit_nextCoordinateObstruction second
      leftIndexTwo sourceUnit sourceUnitNorm
    simpa only [largeError, smallError, lowerDenominator,
      middleDenominator, upperDenominator, sourceUnit, toGaussian_mul,
      RFAP.ConstructiveGaussian.Gaussian.mul_assoc] using obstruction
  let data := normalizeCylinderData coefficient largeError smallError nextError
    lowerDenominator middleDenominator upperDenominator largeErrorNonzero
    middleDenominatorNonzero errorOrdered nextErrorOrdered factorFour
    denominatorOrdered nextDenominatorOrdered errorIdentity denominatorIdentity
    selfObstruction nextObstruction
  exact data.impossible_of_coefficientNorm_cases coefficientNormCases

/-- After an index-two consecutive transition, the next consecutive
transition has index one. -/
theorem nextCoefficientIndexQuadrance_eq_one_of_eq_two
    {source : Fraction} {lower middle upper : Pair}
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper)
    (leftIndexTwo :
      RFAP.BestApproximation.coefficientIndexQuadrance lower middle = 2) :
    RFAP.BestApproximation.coefficientIndexQuadrance middle upper = 1 := by
  rcases second.coefficientIndexQuadrance_eq_one_or_two with
    rightIndexOne | rightIndexTwo
  · exact rightIndexOne
  · exact False.elim
      (repeatedIndexTwo_impossible first second leftIndexTwo rightIndexTwo)

end RFAP.RepeatedIndex
