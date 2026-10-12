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
# Positive uniform polynomial residual radii

For a Gaussian-rational polynomial and an ambient rational box, the retained
box Lipschitz coefficient determines the radius
`min 1 (lower / (8 * denseLipschitzBound p ambient))`. A positive supplied
residual lower bound makes this exact radius positive. The fourfold ambient
Lipschitz coefficient times its squared radius is strictly below that same
lower bound.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Uniform

/-- Four times the ambient polynomial Lipschitz coefficient. -/
@[expose] def exclusionCoefficient (p : CoefficientPolynomial) (ambient : Box) :
  Fraction.Rational :=
  4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient

/-- The fourfold box Lipschitz exclusion coefficient is positive. -/
theorem exclusionCoefficient_pos
    (p : CoefficientPolynomial) (ambient : Box) :
    0 < exclusionCoefficient p ambient :=
  Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient)

/-- Positive rational radius computed from any uniform lower bound for the
polynomial residual.  The bound need not be attained by a displayed point. -/
@[expose] def uniformExclusionRadius
    (p : CoefficientPolynomial) (ambient : Box) (lower : Fraction.Rational) :
    Fraction.Rational :=
  min 1 (lower / (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient))

/-- A positive residual lower bound yields a positive computed uniform exclusion radius. -/
theorem uniformExclusionRadius_pos
    (p : CoefficientPolynomial) (ambient : Box) {lower : Fraction.Rational}
    (positive : 0 < lower) :
    0 < uniformExclusionRadius p ambient lower := by
  have denominatorPositive :
      0 < 8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient)
  exact Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Field.div_pos_direct positive denominatorPositive)

/-- The squared uniform radius leaves a strict positive residual margin.

For a positive supplied lower bound, the fourfold Lipschitz coefficient
times the squared minimum radius lies strictly below that same bound. -/
theorem uniform_exclusion_margin
    (p : CoefficientPolynomial) (ambient : Box) {lower : Fraction.Rational}
    (positive : 0 < lower) :
    exclusionCoefficient p ambient *
        uniformExclusionRadius p ambient lower ^ 2 < lower := by
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient
  let radius := uniformExclusionRadius p ambient lower
  let quotient := lower / (8 * lipschitz)
  have lipschitzPositive : 0 < lipschitz :=
    Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient
  have denominatorPositive : 0 < 8 * lipschitz :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) lipschitzPositive
  have quotientPositive : 0 < quotient :=
    Fraction.Order.Field.div_pos_direct positive denominatorPositive
  have radiusPositive : 0 < radius :=
    uniformExclusionRadius_pos p ambient positive
  have radiusLeOne : radius ≤ 1 := Fraction.Order.Basic.min_le_left 1 quotient
  have radiusLeQuotient : radius ≤ quotient := Fraction.Order.Basic.min_le_right 1 quotient
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
  have cancellation : (8 * lipschitz) * quotient = lower := by
    calc
      (8 * lipschitz) * quotient = quotient * (8 * lipschitz) :=
        Fraction.Field.mul_comm _ _
      _ = lower :=
        Fraction.Field.div_mul_cancel_of_ne lower
          (8 * lipschitz) denominatorPositive.ne'
  change (4 * lipschitz) * radius ^ 2 < lower
  exact squareScaled.trans_lt
    (radiusScaled.trans_lt (quotientScaled.trans_eq cancellation))
end Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Uniform

end
