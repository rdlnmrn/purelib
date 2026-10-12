module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Bounds
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

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

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Target

/-! ## Uniform residual refinement and cross-polynomial separation -/

/-- Positive radius making every point of the requested winding-one box have
residual strictly below a supplied positive threshold. -/
@[expose] def uniformResidualRadius
    (p : CoefficientPolynomial) (ambient : Box) (threshold : Fraction.Rational) :
    Fraction.Rational :=
  min 1 (threshold / (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient))

/-- A positive target residual threshold yields a positive computed uniform radius. -/
theorem uniformResidualRadius_pos
    (p : CoefficientPolynomial) (ambient : Box) {threshold : Fraction.Rational}
    (thresholdPositive : 0 < threshold) :
    0 < uniformResidualRadius p ambient threshold := by
  exact Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Field.div_pos_direct thresholdPositive
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient)))

section
/-- The computed uniform radius lies between zero and one, so its square is no larger than itself. -/
theorem uniformResidualRadius_sq_le
    (p : CoefficientPolynomial) (ambient : Box) {threshold : Fraction.Rational}
    (thresholdPositive : 0 < threshold) :
    uniformResidualRadius p ambient threshold ^ 2 ≤
      uniformResidualRadius p ambient threshold := by
  let radius := uniformResidualRadius p ambient threshold
  have positive := uniformResidualRadius_pos p ambient thresholdPositive
  have leOne : radius ≤ 1 := Fraction.Order.Basic.min_le_left _ _
  rw [pow_two]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    leOne positive.le).trans_eq (_root_.one_mul radius)
end

end Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Target

end
