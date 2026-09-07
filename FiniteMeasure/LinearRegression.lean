import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.CovarianceAlgebra

/-!
# Exact finite rational linear regression

For a predictor of explicitly positive finite variance, the least-squares
slope and centered affine prediction are rational.  The residual has zero
mean, is orthogonal to the predictor and prediction, and yields an exact
explained/residual variance decomposition.
-/

namespace FiniteMeasure

namespace Distribution

/-- Exact rational least-squares slope. -/
def regressionSlope {α : Type} (distribution : Distribution α)
    (predictor response : α → Coordinate) : Coordinate :=
  distribution.covariance predictor response /
    distribution.variance predictor

/-- Centered affine least-squares prediction. -/
def linearPrediction {α : Type} (distribution : Distribution α)
    (predictor response : α → Coordinate) : α → Coordinate :=
  fun item =>
    distribution.regressionSlope predictor response *
        (predictor item - distribution.expectation predictor) +
      distribution.expectation response

/-- Response minus its displayed rational linear prediction. -/
def regressionResidual {α : Type} (distribution : Distribution α)
    (predictor response : α → Coordinate) : α → Coordinate :=
  fun item => response item - distribution.linearPrediction predictor response item

/-- The centered affine prediction has exactly the response mean. -/
theorem expectation_linearPrediction {α : Type}
    (distribution : Distribution α) (predictor response : α → Coordinate) :
    distribution.expectation
        (distribution.linearPrediction predictor response) =
      distribution.expectation response := by
  unfold linearPrediction
  rw [distribution.expectation_add, distribution.expectation_scale,
    distribution.expectation_sub]
  rw [distribution.expectation_constant (distribution.expectation predictor),
    distribution.expectation_constant (distribution.expectation response)]
  ring1

/-- The regression residual is exactly centered. -/
theorem expectation_regressionResidual {α : Type}
    (distribution : Distribution α) (predictor response : α → Coordinate) :
    distribution.expectation
        (distribution.regressionResidual predictor response) = 0 := by
  unfold regressionResidual
  rw [distribution.expectation_sub,
    distribution.expectation_linearPrediction]
  ring1

/-- Prediction plus residual reconstructs the response pointwise. -/
theorem linearPrediction_add_regressionResidual {α : Type}
    (distribution : Distribution α) (predictor response : α → Coordinate)
    (item : α) :
    distribution.linearPrediction predictor response item +
      distribution.regressionResidual predictor response item =
        response item := by
  unfold regressionResidual
  ring1

/-- Positive predictor variance makes the regression residual orthogonal to
the predictor. -/
theorem covariance_predictor_regressionResidual_eq_zero {α : Type}
    (distribution : Distribution α) (predictor response : α → Coordinate)
    (positive : 0 < distribution.variance predictor) :
    distribution.covariance predictor
        (distribution.regressionResidual predictor response) = 0 := by
  unfold regressionResidual linearPrediction
  rw [distribution.covariance_sub_right,
    distribution.covariance_add_constant_right,
    distribution.covariance_scale_right,
    distribution.covariance_sub_right,
    distribution.covariance_self,
    distribution.covariance_constant_right]
  unfold regressionSlope
  simp only [sub_zero]
  calc
    distribution.covariance predictor response -
          distribution.covariance predictor response /
              distribution.variance predictor *
            distribution.variance predictor =
        distribution.covariance predictor response -
          distribution.covariance predictor response :=
      congrArg
        (fun value => distribution.covariance predictor response - value)
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ positive.ne')
    _ = 0 := by ring1

/-- The fitted prediction is itself orthogonal to the residual. -/
theorem covariance_linearPrediction_regressionResidual_eq_zero {α : Type}
    (distribution : Distribution α) (predictor response : α → Coordinate)
    (positive : 0 < distribution.variance predictor) :
    distribution.covariance
        (distribution.linearPrediction predictor response)
        (distribution.regressionResidual predictor response) = 0 := by
  unfold linearPrediction
  rw [distribution.covariance_add_constant_left,
    distribution.covariance_scale_left,
    distribution.covariance_sub_left,
    distribution.covariance_constant_left,
    distribution.covariance_predictor_regressionResidual_eq_zero
      predictor response positive]
  ring1

/-- Exact explained-plus-residual variance decomposition. -/
theorem variance_eq_linearPrediction_add_regressionResidual {α : Type}
    (distribution : Distribution α) (predictor response : α → Coordinate)
    (positive : 0 < distribution.variance predictor) :
    distribution.variance response =
      distribution.variance
          (distribution.linearPrediction predictor response) +
        distribution.variance
          (distribution.regressionResidual predictor response) := by
  calc
    distribution.variance response =
        distribution.variance (fun item =>
          distribution.linearPrediction predictor response item +
            distribution.regressionResidual predictor response item) :=
      distribution.variance_congr _ _ (fun item =>
        (distribution.linearPrediction_add_regressionResidual
          predictor response item).symm)
    _ = distribution.variance
          (distribution.linearPrediction predictor response) +
        distribution.variance
          (distribution.regressionResidual predictor response) := by
      rw [distribution.variance_add,
        distribution.covariance_linearPrediction_regressionResidual_eq_zero
          predictor response positive]
      ring1

/-- Fitting a finite rational linear predictor cannot explain more than the
response variance. -/
theorem variance_linearPrediction_le_response {α : Type}
    (distribution : Distribution α) (predictor response : α → Coordinate)
    (positive : 0 < distribution.variance predictor) :
    distribution.variance
        (distribution.linearPrediction predictor response) ≤
      distribution.variance response := by
  rw [distribution.variance_eq_linearPrediction_add_regressionResidual
    predictor response positive]
  exact le_add_of_nonneg_right
    (distribution.variance_nonneg
      (distribution.regressionResidual predictor response))

/-- The residual variance is also at most the original response variance. -/
theorem variance_regressionResidual_le_response {α : Type}
    (distribution : Distribution α) (predictor response : α → Coordinate)
    (positive : 0 < distribution.variance predictor) :
    distribution.variance
        (distribution.regressionResidual predictor response) ≤
      distribution.variance response := by
  rw [distribution.variance_eq_linearPrediction_add_regressionResidual
    predictor response positive]
  exact le_add_of_nonneg_left
    (distribution.variance_nonneg
      (distribution.linearPrediction predictor response))

end Distribution

end FiniteMeasure
