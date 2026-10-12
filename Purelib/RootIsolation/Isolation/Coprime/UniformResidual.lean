module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Target
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Winding.Bounds.Residual
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Quantitative finite bounds for two coprime polynomials

This module extracts the reusable two-polynomial content of the squarefree
derivative-margin argument.  A displayed Bézout certificate gives an explicit
threshold below which a small value of the left polynomial forces a positive
lower bound for the right polynomial.  Applying the estimate to every point
of a sufficiently refined winding-one box supplies boundary clearance and
zero winding for the other polynomial.
-/

namespace Purelib.RootIsolation.Isolation.Coprime.UniformResidual

/-- Refine the original track state at the coefficient-computed uniform residual radius.

The supplied positive threshold and original ambient box determine the finite accuracy request. -/
@[expose] def uniformlySmallState
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Track.Basic.WindingOneTrack p ambient)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold) :
    State.WindingOne.Basic.WindingOneState p ambient :=
  track.refine current (Dense.Gaussian.Bounds.Box.Target.uniformResidualRadius p ambient threshold)
    (Dense.Gaussian.Bounds.Box.Target.uniformResidualRadius_pos p ambient thresholdPositive)

/-- Every point of the retained uniform refinement has squared polynomial residual strictly below the requested
threshold.

The original polynomial must have positive degree; the radius budget controls its ambient Lipschitz bound. -/
theorem uniformlySmallState_residual_lt
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Track.Basic.WindingOneTrack p ambient)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    {threshold : Fraction.Rational} (thresholdPositive : 0 < threshold)
    {z : Gaussian.Basic.Canonical}
    (inside : (Isolation.Coprime.UniformResidual.uniformlySmallState track current threshold
      thresholdPositive).box.Contains z) :
    Data.Gaussian.Norm.Basic.normSq (p.eval z) < threshold := by
  let radius := Dense.Gaussian.Bounds.Box.Target.uniformResidualRadius p ambient threshold
  let state := Isolation.Coprime.UniformResidual.uniformlySmallState track current threshold thresholdPositive
  have residual := Winding.Bounds.Residual.normSq_eval_le_four_lipschitz_diagonal
    degreePositive state inside
  have diagonal := track.accurate current radius
    (Dense.Gaussian.Bounds.Box.Target.uniformResidualRadius_pos p ambient thresholdPositive)
  have radiusSquare := Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Target.uniformResidualRadius_sq_le p ambient
    thresholdPositive
  have radiusBudget : radius ≤
      threshold / (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient) := Fraction.Order.Basic.min_le_right _ _
  have scaled : radius * (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient) ≤ threshold :=
    (Fraction.Order.Field.le_div_iff_pos
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient))).mp radiusBudget
  have positiveProduct : 0 < Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * radius :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient)
      (Dense.Gaussian.Bounds.Box.Target.uniformResidualRadius_pos p ambient thresholdPositive)
  calc
    Data.Gaussian.Norm.Basic.normSq (p.eval z) ≤
        4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * state.box.diagonalSq := by simpa only
          [Gaussian.Norm.Basic.normSq_eq_canonical] using residual
    _ ≤ 4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * radius ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct diagonal
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient)).le
    _ ≤ 4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * radius :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusSquare
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient)).le
    _ < radius * (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient) := by
      calc
        4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * radius =
            4 * (Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * radius) := by ring1
        _ < 8 * (Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * radius) :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
            (show (4 : Fraction.Rational) < 8 by decide) positiveProduct
        _ = radius * (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient) := by ring1
    _ ≤ threshold := scaled
end Purelib.RootIsolation.Isolation.Coprime.UniformResidual

end
