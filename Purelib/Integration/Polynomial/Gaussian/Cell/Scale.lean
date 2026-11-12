module

public import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
public import Purelib.Polynomial.Ascending.Gaussian.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Ascending.Gaussian.Integral
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.List.Map
import Purelib.Tactic.Ring

/-! # Scaling original polynomial integration cells and their observations -/

public section
namespace Purelib.Integration.Polynomial.Gaussian.Cell.Basic

open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Data.Rat.Fraction
open Purelib.Polynomial.Ascending

namespace LocalObservation

/-- Scale the original integrand reading, residual and allowance at the same parameter. -/
@[expose] def scale {polynomial : Gaussian.CoefficientPolynomial}
    {allowance : Purelib.Data.Rat.Fraction.Rational}
    (factor : Basic.Canonical) (observation : LocalObservation polynomial allowance) :
    LocalObservation (Gaussian.Arithmetic.scale factor polynomial) (Basic.Canonical.normSq factor * allowance) where
  parameter := observation.parameter
  integrandReading := factor * observation.integrandReading
  error := factor * observation.error
  decomposition := by
    rw [Gaussian.Evaluation.eval_scale, ← observation.decomposition]
    ring1
  error_le := by
    rw [Basic.Canonical.normSq_mul]
    exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct observation.error_le
      (Basic.Canonical.normSq_nonneg factor)

end LocalObservation

namespace CellModel

/-- Scale a cell's polynomial and every original observation while preserving both endpoints. -/
@[expose] def scale (factor : Basic.Canonical) (cell : CellModel) : CellModel where
  start := cell.start
  finish := cell.finish
  polynomial := Gaussian.Arithmetic.scale factor cell.polynomial
  localAllowance := Basic.Canonical.normSq factor * cell.localAllowance
  localAllowance_nonneg := Order.Arithmetic.mul_nonneg_direct
    (Basic.Canonical.normSq_nonneg factor) cell.localAllowance_nonneg
  observations := cell.observations.map (LocalObservation.scale factor)

/-- Scaling preserves the original path displacement. -/
theorem scale_displacement (factor : Basic.Canonical) (cell : CellModel) :
    (cell.scale factor).displacement = cell.displacement := rfl

/-- Integrating the scaled original polynomial scales the original finite integral sample. -/
theorem scale_integralSample (factor : Basic.Canonical) (cell : CellModel) :
    (cell.scale factor).integralSample = factor * cell.integralSample := by
  change cell.displacement * Gaussian.Integral.definiteIntegral
    (Gaussian.Arithmetic.scale factor cell.polynomial) 0 1 = _
  rw [Gaussian.Integral.definiteIntegral_scale]
  change cell.displacement * (factor * Gaussian.Integral.definiteIntegral cell.polynomial 0 1) =
    factor * (cell.displacement * Gaussian.Integral.definiteIntegral cell.polynomial 0 1)
  ring1

/-- The scaled cell pays its original displacement-weighted allowance times the coefficient's squared norm. -/
theorem scale_weightedAllowance (factor : Basic.Canonical) (cell : CellModel) :
    (cell.scale factor).weightedAllowance = Basic.Canonical.normSq factor * cell.weightedAllowance := by
  change Basic.Canonical.normSq cell.displacement *
    (Basic.Canonical.normSq factor * cell.localAllowance) =
      Basic.Canonical.normSq factor * (Basic.Canonical.normSq cell.displacement * cell.localAllowance)
  ring1

/-- Scaling retains the number and order of original local observations. -/
theorem scale_observations_length (factor : Basic.Canonical) (cell : CellModel) :
    (cell.scale factor).observations.length = cell.observations.length :=
  Map.length_map _ cell.observations

end CellModel
end Purelib.Integration.Polynomial.Gaussian.Cell.Basic
end
