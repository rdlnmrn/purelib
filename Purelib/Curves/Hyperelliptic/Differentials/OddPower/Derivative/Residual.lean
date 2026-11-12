module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Data.Gaussian.Norm.Reciprocal
import Purelib.Tactic.Ring

/-! # The original square residual pays the cleared derivative discrepancy

The independently constructed derivative numerator contains the original
curve polynomial. At a displayed inexact sheet reading its difference from
the original two Leibniz terms is exactly the original square residual times
the first numerator coefficient and the next reciprocal power. A positive
sheet floor and fixed coefficient box give an explicit finite error factor.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative.Residual

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

/-- The two original Leibniz specifications evaluated on one unchanged displayed sheet reading. -/
@[expose] def leibnizReading {polynomial : CoefficientPolynomial}
    {primitive : OddPowerDifferential polynomial} (specification : Specification polynomial primitive)
    (point reading : Canonical) : Canonical :=
  (specification.first.scale * specification.first.numerator.eval point) *
      reading⁻¹ ^ primitive.denominatorExponent -
    (specification.last.scale * specification.last.numerator.eval point) *
      reading⁻¹ ^ (primitive.denominatorExponent + 2)

/-- The displayed square residual is the entire discrepancy between the independent and Leibniz derivative readings.

The original curve value and both original derivative specifications remain
unchanged. Nonzeroness of this actual reading permits only the exact two-factor
reciprocal cancellation; no exact-root substitution is made.
-/
theorem difference_eq {polynomial : CoefficientPolynomial}
    {primitive : OddPowerDifferential polynomial} (specification : Specification polynomial primitive)
    (point : Canonical) (observation : Observation.RootObservation) (nonzero : observation.witness ≠ 0) :
    Observation.scalarReading specification.differential point observation -
        leibnizReading specification point observation.witness =
      (specification.first.scale * specification.first.numerator.eval point) *
        (polynomial.eval point - observation.witness * observation.witness) *
          observation.witness⁻¹ ^ (primitive.denominatorExponent + 2) := by
  let reading := observation.witness
  have inverseCancel : reading⁻¹ * reading = 1 := by
    simpa only [Gaussian.Field.inv_eq] using Gaussian.Field.inv_mul reading nonzero
  have cancellation : (reading * reading) * reading⁻¹ ^ (primitive.denominatorExponent + 2) =
      reading⁻¹ ^ primitive.denominatorExponent := by
    calc
      _ = reading⁻¹ ^ primitive.denominatorExponent * (reading⁻¹ * reading) ^ 2 := by
        rewrite [pow_add, pow_two]
        ring1
      _ = _ := by rewrite [inverseCancel, pow_two, Gaussian.Basic.one_mul, Gaussian.Basic.mul_one]; rfl
  unfold Observation.scalarReading leibnizReading
  rewrite [specification.differential_exponent, specification.coefficient_eq point]
  calc
    _ = (specification.first.scale * specification.first.numerator.eval point) * polynomial.eval point *
        reading⁻¹ ^ (primitive.denominatorExponent + 2) -
      (specification.first.scale * specification.first.numerator.eval point) *
        reading⁻¹ ^ primitive.denominatorExponent := by dsimp only [reading]; ring1
    _ = _ := by rewrite [← cancellation]; dsimp only [reading]; ring1

/-- The fixed-box discrepancy factor retains the original primitive scale, numerator derivative and sheet floor. -/
@[expose] def factor (primitive : OddPowerDifferential radicand) (box : Box)
    (floor : Fraction.Rational) : Fraction.Rational :=
  Norm.Basic.normSq primitive.scale * Bounds.Box.denseEvalNormBound (GCD.derivative primitive.numerator) box *
    floor⁻¹ ^ (primitive.denominatorExponent + 2)

/-- The actual source square-residual payment bounds the independent derivative's discrepancy from the Leibniz terms. -/
theorem difference_normSq_le {polynomial : CoefficientPolynomial}
    {primitive : OddPowerDifferential polynomial} (specification : Specification polynomial primitive)
    (point : Canonical) (observation : Observation.RootObservation) (nonzero : observation.witness ≠ 0)
    {box : Box} (inside : box.Contains point) {floor allowance : Fraction.Rational}
    (positive : 0 < floor) (lower : floor ≤ Norm.Basic.normSq observation.witness)
    (residual : Norm.Basic.normSq (observation.witness * observation.witness - polynomial.eval point) ≤ allowance) :
    Norm.Basic.normSq (Observation.scalarReading specification.differential point observation -
      leibnizReading specification point observation.witness) ≤ factor primitive box floor * allowance := by
  have numerator : Norm.Basic.normSq (specification.first.scale * specification.first.numerator.eval point) ≤
      Norm.Basic.normSq primitive.scale * Bounds.Box.denseEvalNormBound (GCD.derivative primitive.numerator) box := by
    rewrite [specification.first_eq, specification.numeratorDerivative_eq, Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Bounds.Box.normSq_eval_le_denseEvalNormBound (GCD.derivative primitive.numerator) inside)
      (Norm.Basic.normSq_nonneg _)
  have reverse : polynomial.eval point - observation.witness * observation.witness =
      -(observation.witness * observation.witness - polynomial.eval point) := by ring1
  rewrite [difference_eq specification point observation nonzero, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul,
    reverse, Norm.Basic.normSq_neg]
  have coefficient := Fraction.Order.Arithmetic.mul_le_mul_direct numerator residual (Norm.Basic.normSq_nonneg _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg primitive.scale)
      (Bounds.Box.denseHornerNormBounds_nonneg (GCD.derivative primitive.numerator) box).1)
  have coefficientNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Norm.Basic.normSq_nonneg (specification.first.scale * specification.first.numerator.eval point))
    (Norm.Basic.normSq_nonneg (observation.witness * observation.witness - polynomial.eval point))
  exact (Fraction.Order.Arithmetic.mul_le_mul_direct coefficient
    (Norm.Reciprocal.power_normSq_le positive lower (primitive.denominatorExponent + 2))
    (Norm.Basic.normSq_nonneg _)
    (coefficientNonnegative.trans coefficient)).trans_eq (by unfold factor; ring1)

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative.Residual
