module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Bounds
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

/-!
# Refinement radii for bounded residuals

The retained threshold and ambient Lipschitz bound determine the original
minimum radius. Scalar inequalities certify the same squared-radius request.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual.Radius

/-- Compute the refinement radius from a threshold and ambient Lipschitz bound.

The minimum of one and the original threshold ratio retains the input
polynomial and ambient box. Its positivity and squared-radius bound require
a positive supplied threshold. -/
@[expose] public def residualRefinementRadius
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box)
    (threshold : Fraction.Rational) : Fraction.Rational :=
  min 1 (threshold / Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient)

/-- A positive residual threshold makes the computed refinement radius positive.

Both one and the quotient by the positive ambient Lipschitz bound are positive.
The retained minimum therefore satisfies the same strict lower bound. -/
public theorem residualRefinementRadius_pos
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box) {threshold : Fraction.Rational}
    (thresholdPositive : 0 < threshold) :
    0 < Dense.Gaussian.Bounds.Box.Residual.Radius.residualRefinementRadius p ambient threshold := by
  exact Fraction.Order.Basic.lt_min
    (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by decide))
    (Fraction.Order.Field.div_pos_direct thresholdPositive
      (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient))

/-- The retained squared radius times its Lipschitz bound fits the threshold.

A positive threshold makes the original radius positive and at most one.
Its ratio bound and the ambient positive Lipschitz multiplier certify this
comparison for the same polynomial and ambient box. -/
public theorem lipschitz_mul_residualRadius_sq_le
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box) {threshold : Fraction.Rational}
    (thresholdPositive : 0 < threshold) :
    Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient *
        Dense.Gaussian.Bounds.Box.Residual.Radius.residualRefinementRadius p ambient threshold ^ 2 ≤ threshold := by
  let radius := Dense.Gaussian.Bounds.Box.Residual.Radius.residualRefinementRadius p ambient threshold
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient
  have radiusPositive := Dense.Gaussian.Bounds.Box.Residual.Radius.residualRefinementRadius_pos p ambient
    thresholdPositive
  have radiusLeOne : radius ≤ 1 := Fraction.Order.Basic.min_le_left _ _
  have radiusRatio : radius ≤ threshold / lipschitz := Fraction.Order.Basic.min_le_right _ _
  have lipschitzPositive := Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient
  have squareLeRadius : radius ^ 2 ≤ radius := by
    rw [pow_two]
    calc
      radius * radius ≤ 1 * radius :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          radiusLeOne radiusPositive.le
      _ = radius := by ring1
  have ratioScaled : radius * lipschitz ≤ threshold :=
    (Fraction.Order.Field.le_div_iff_pos lipschitzPositive).mp radiusRatio
  calc
    lipschitz * radius ^ 2 ≤ lipschitz * radius :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareLeRadius
        lipschitzPositive.le
    _ = radius * lipschitz := by ring1
    _ ≤ threshold := ratioScaled

end Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual.Radius
