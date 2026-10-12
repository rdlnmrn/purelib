module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Uniform
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

public section

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

/-!
# Excluding a displayed clear point from a winding-one track

A fixed rational point at which the polynomial is nonzero cannot remain in
an arbitrarily small nonzero-winding box.  The proof uses the existing finite
constant-dominance homotopy: if the point were inside, its nonzero value and
the box's coefficient-computed variation bound would force winding zero.

This is the terminal-point part of the persistent CCL equality handler.  A
local CCL terminal is either an exact polynomial root, or one explicit track
refinement excludes that displayed rational point.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Point

/-- Positive rational radius small enough to exclude one displayed nonroot. -/
@[expose] def exclusionRadius
    (p : CoefficientPolynomial) (ambient : Box) (point : Gaussian.Basic.Canonical) :
      Fraction.Rational :=
  min 1
    (Data.Gaussian.Norm.Basic.normSq (p.eval point) /
      (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient))

/-- A displayed nonroot has a positive exclusion radius computed from its exact residual quadrance. -/
theorem exclusionRadius_pos
    (p : CoefficientPolynomial) (ambient : Box) (point : Gaussian.Basic.Canonical)
    (nonroot : p.eval point ≠ 0) :
    0 < exclusionRadius p ambient point := by
  have valuePositive : 0 < Data.Gaussian.Norm.Basic.normSq (p.eval point) := Gaussian.Norm.Basic.normSq_pos nonroot
  have denominatorPositive :
      0 < 8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient)
  exact Purelib.Data.Rat.Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Field.div_pos_direct valuePositive
      denominatorPositive)

/-- The nonroot exclusion radius makes the squared-variation bound strictly smaller than the point's residual quadrance.
-/
theorem exclusion_margin
    (p : CoefficientPolynomial) (ambient : Box) (point : Gaussian.Basic.Canonical)
    (nonroot : p.eval point ≠ 0) :
    Dense.Gaussian.Bounds.Box.Exclusion.Uniform.exclusionCoefficient p ambient *
        exclusionRadius p ambient point ^ 2 <
      Data.Gaussian.Norm.Basic.normSq (p.eval point) := by
  let value := Data.Gaussian.Norm.Basic.normSq (p.eval point)
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient
  let radius := exclusionRadius p ambient point
  let quotient := value / (8 * lipschitz)
  have valuePositive : 0 < value := Gaussian.Norm.Basic.normSq_pos nonroot
  have lipschitzPositive : 0 < lipschitz :=
    Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient
  have denominatorPositive : 0 < 8 * lipschitz :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) lipschitzPositive
  have quotientPositive : 0 < quotient :=
    Fraction.Order.Field.div_pos_direct valuePositive denominatorPositive
  have radiusPositive : 0 < radius :=
    exclusionRadius_pos p ambient point nonroot
  have radiusLeOne : radius ≤ 1 := by
    exact Purelib.Data.Rat.Fraction.Order.Basic.min_le_left 1 quotient
  have radiusLeQuotient : radius ≤ quotient := by
    exact Purelib.Data.Rat.Fraction.Order.Basic.min_le_right 1 quotient
  have radiusSquareLe : radius ^ 2 ≤ radius := by
    rw [pow_two]
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        radiusLeOne radiusPositive.le
    exact scaled.trans_eq (_root_.one_mul radius)
  have coefficientPositive : 0 < 4 * lipschitz :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) lipschitzPositive
  have squareScaled :
      (4 * lipschitz) * radius ^ 2 ≤ (4 * lipschitz) * radius :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      radiusSquareLe coefficientPositive.le
  have radiusScaled :
      (4 * lipschitz) * radius ≤ (4 * lipschitz) * quotient :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      radiusLeQuotient coefficientPositive.le
  have fourLtEight : 4 * lipschitz < 8 * lipschitz :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      (by decide) lipschitzPositive
  have quotientScaled :
      (4 * lipschitz) * quotient < (8 * lipschitz) * quotient :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      fourLtEight quotientPositive
  have cancellation : (8 * lipschitz) * quotient = value := by
    calc
      (8 * lipschitz) * quotient = quotient * (8 * lipschitz) :=
        Fraction.Field.mul_comm _ _
      _ = value :=
        Fraction.Field.div_mul_cancel_of_ne value
          (8 * lipschitz) denominatorPositive.ne'
  change (4 * lipschitz) * radius ^ 2 < value
  exact squareScaled.trans_lt
    (radiusScaled.trans_lt (quotientScaled.trans_eq cancellation))

end Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Point

end
