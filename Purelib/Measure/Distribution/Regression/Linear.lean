module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Stability
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Measure.Distribution.Moments.Covariance
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

@[expose] public section

/-!
# Exact finite rational linear regression

For a predictor of explicitly positive finite variance, the least-squares
slope and centered affine prediction are rational.  The residual has zero
mean, is orthogonal to the predictor and prediction, and yields an exact
explained/residual variance decomposition.
-/

namespace Purelib.Measure

namespace Distribution

section
open Purelib.Data.Rat
/-- Divide original predictor-response covariance by original predictor variance.

The rational expression uses total division; orthogonality and variance decomposition separately require positive
predictor variance. -/
def regressionSlope {α : Type} (distribution : Distribution α)
    (predictor response : α → Fraction.Rational) : Fraction.Rational :=
  distribution.covariance predictor response /
    distribution.variance predictor

/-- Center the original predictor, scale by its retained regression slope, and add the original response mean. -/
def linearPrediction {α : Type} (distribution : Distribution α)
    (predictor response : α → Fraction.Rational) : α → Fraction.Rational :=
  fun item =>
    distribution.regressionSlope predictor response *
        (predictor item - distribution.expectation predictor) +
      distribution.expectation response

/-- Subtract the exact original linear prediction from the response pointwise. -/
def regressionResidual {α : Type} (distribution : Distribution α)
    (predictor response : α → Fraction.Rational) : α → Fraction.Rational :=
  fun item => response item - distribution.linearPrediction predictor response item

/-- The exact linear prediction has the original response expectation. -/
theorem expectation_linearPrediction {α : Type}
    (distribution : Distribution α) (predictor response : α → Fraction.Rational) :
    distribution.expectation
        (distribution.linearPrediction predictor response) =
      distribution.expectation response := by
  unfold linearPrediction
  rw [distribution.expectation_add, distribution.expectation_scale,
    distribution.expectation_sub]
  rw [distribution.expectation_constant (distribution.expectation predictor),
    distribution.expectation_constant (distribution.expectation response)]
  ring1

/-- The exact regression residual has expectation zero. -/
theorem expectation_regressionResidual {α : Type}
    (distribution : Distribution α) (predictor response : α → Fraction.Rational) :
    distribution.expectation
        (distribution.regressionResidual predictor response) = 0 := by
  unfold regressionResidual
  rw [distribution.expectation_sub,
    distribution.expectation_linearPrediction]
  ring1

/-- The exact original prediction and residual sum pointwise to the response. -/
theorem linearPrediction_add_regressionResidual {α : Type}
    (distribution : Distribution α) (predictor response : α → Fraction.Rational)
    (item : α) :
    distribution.linearPrediction predictor response item +
      distribution.regressionResidual predictor response item =
        response item := by
  unfold regressionResidual
  ring1

/-- With positive original predictor variance, the predictor has zero covariance with its exact regression residual. -/
theorem covariance_predictor_regressionResidual_eq_zero {α : Type}
    (distribution : Distribution α) (predictor response : α → Fraction.Rational)
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
  have varianceZero : distribution.variance predictor - 0 =
      distribution.variance predictor := by ring1
  rewrite [varianceZero]
  calc
    distribution.covariance predictor response -
          distribution.covariance predictor response /
              distribution.variance predictor *
            distribution.variance predictor =
        distribution.covariance predictor response -
          distribution.covariance predictor response :=
      congrArg
        (fun value => distribution.covariance predictor response - value)
        (Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne')
    _ = 0 := by ring1

/-- With positive predictor variance, the exact original prediction and residual have zero covariance. -/
theorem covariance_linearPrediction_regressionResidual_eq_zero {α : Type}
    (distribution : Distribution α) (predictor response : α → Fraction.Rational)
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

/-- Positive predictor variance splits original response variance into exact prediction and residual variances. -/
theorem variance_eq_linearPrediction_add_regressionResidual {α : Type}
    (distribution : Distribution α) (predictor response : α → Fraction.Rational)
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

/-- With positive predictor variance, the exact prediction variance is at most original response variance. -/
theorem variance_linearPrediction_le_response {α : Type}
    (distribution : Distribution α) (predictor response : α → Fraction.Rational)
    (positive : 0 < distribution.variance predictor) :
    distribution.variance
        (distribution.linearPrediction predictor response) ≤
      distribution.variance response := by
  rw [distribution.variance_eq_linearPrediction_add_regressionResidual
    predictor response positive]
  exact le_add_of_nonneg_right
    (distribution.variance_nonneg
      (distribution.regressionResidual predictor response))

/-- With positive predictor variance, the exact residual variance is at most original response variance. -/
theorem variance_regressionResidual_le_response {α : Type}
    (distribution : Distribution α) (predictor response : α → Fraction.Rational)
    (positive : 0 < distribution.variance predictor) :
    distribution.variance
        (distribution.regressionResidual predictor response) ≤
      distribution.variance response := by
  rw [distribution.variance_eq_linearPrediction_add_regressionResidual
    predictor response positive]
  exact le_add_of_nonneg_left
    (distribution.variance_nonneg
      (distribution.linearPrediction predictor response))

end

end Distribution

end Purelib.Measure
