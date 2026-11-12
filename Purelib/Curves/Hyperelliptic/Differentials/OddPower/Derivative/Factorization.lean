module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Data.Gaussian.Norm.Reciprocal
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

/-!
# Spatial derivative residuals with an exact retained ordinate factor

The original curve value and spatial polynomial derivative factor through
an exact nonzero ordinate and one cofactor. The primitive's chart chain rule
uses the displayed inexact cofactor root. Its difference from the independent
cleared spatial derivative is exactly the original cofactor square residual.
Positive ordinate and cofactor floors pay an explicit fixed-box bound.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative.Factorization

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {polynomial : CoefficientPolynomial} {primitive : OddPowerDifferential polynomial}

/-- The primitive chain rule retains both original ordinate and cofactor reciprocal powers.

The numerator derivative is the original specification cache. The base,
ordinate and cofactor velocities are distinct prescribed inputs; the cofactor
root derivative uses the original half coefficient and displayed root.
-/
@[expose] def chainReading (specification : Specification polynomial primitive)
    (point ordinate cofactor baseVelocity ordinateVelocity cofactorDerivative : Canonical) : Canonical :=
  primitive.scale *
    (specification.numeratorDerivative.eval point * baseVelocity *
        ordinate⁻¹ ^ primitive.denominatorExponent * cofactor⁻¹ ^ primitive.denominatorExponent -
      exponentCoefficient primitive * primitive.numerator.eval point * ordinateVelocity *
        ordinate⁻¹ ^ (primitive.denominatorExponent + 1) * cofactor⁻¹ ^ primitive.denominatorExponent -
      (exponentCoefficient primitive / 2) * primitive.numerator.eval point * cofactorDerivative * baseVelocity *
        ordinate⁻¹ ^ primitive.denominatorExponent * cofactor⁻¹ ^ (primitive.denominatorExponent + 2))

/-- The independently constructed derivative is evaluated with the full original factored odd sheet denominator. -/
@[expose] def spatialReading (specification : Specification polynomial primitive)
    (point ordinate cofactor baseVelocity : Canonical) : Canonical :=
  specification.differential.scale * specification.differential.numerator.eval point * baseVelocity *
    ordinate⁻¹ ^ specification.differential.denominatorExponent *
      cofactor⁻¹ ^ specification.differential.denominatorExponent

/-- One exact nonzero factor cancels a single occurrence from the original reciprocal power. -/
private theorem reciprocal_one (value : Canonical) (nonzero : value ≠ 0) (exponent : Nat) :
    value * value⁻¹ ^ (exponent + 1) = value⁻¹ ^ exponent := by
  have cancellation : value⁻¹ * value = 1 := by
    simpa only [Gaussian.Field.inv_eq] using Gaussian.Field.inv_mul value nonzero
  calc
    _ = value⁻¹ ^ exponent * (value⁻¹ * value) := by rewrite [pow_succ]; ring1
    _ = _ := by rewrite [cancellation, Gaussian.Basic.mul_one]; rfl

/-- Two exact nonzero factors cancel the original reciprocal power's two additional occurrences. -/
private theorem reciprocal_two (value : Canonical) (nonzero : value ≠ 0) (exponent : Nat) :
    (value * value) * value⁻¹ ^ (exponent + 2) = value⁻¹ ^ exponent := by
  have cancellation : value⁻¹ * value = 1 := by
    simpa only [Gaussian.Field.inv_eq] using Gaussian.Field.inv_mul value nonzero
  calc
    _ = value⁻¹ ^ exponent * (value⁻¹ * value) ^ 2 := by rewrite [pow_add, pow_two]; ring1
    _ = _ := by rewrite [cancellation, pow_two, Gaussian.Basic.one_mul, Gaussian.Basic.mul_one]; rfl

/-- Exact curve factorization and its genuine spatial product rule isolate the entire chart derivative discrepancy.

The two equalities concern the original curve and derivative caches, not the
desired primitive conclusion. The displayed cofactor root remains inexact;
its unchanged square residual is retained as the final explicit factor.
-/
theorem difference_eq (specification : Specification polynomial primitive)
    (point ordinate cofactor baseVelocity ordinateVelocity cofactorValue cofactorDerivative : Canonical)
    (ordinateNonzero : ordinate ≠ 0) (cofactorNonzero : cofactor ≠ 0)
    (curve_eq : polynomial.eval point = cofactorValue * (ordinate * ordinate))
    (curveVelocity_eq : specification.polynomialDerivative.eval point * baseVelocity =
      cofactorDerivative * baseVelocity * (ordinate * ordinate) +
        2 * cofactorValue * ordinate * ordinateVelocity) :
    spatialReading specification point ordinate cofactor baseVelocity -
        chainReading specification point ordinate cofactor baseVelocity ordinateVelocity cofactorDerivative =
      primitive.scale *
        (specification.numeratorDerivative.eval point * baseVelocity * ordinate -
          exponentCoefficient primitive * primitive.numerator.eval point * ordinateVelocity) *
        ordinate⁻¹ ^ (primitive.denominatorExponent + 1) *
        cofactor⁻¹ ^ (primitive.denominatorExponent + 2) * (cofactorValue - cofactor * cofactor) := by
  have half : (2 : Canonical)⁻¹ * 2 = 1 := by decide +kernel
  have coefficient : specification.differential.scale * specification.differential.numerator.eval point *
      baseVelocity =
      primitive.scale * specification.numeratorDerivative.eval point * baseVelocity * cofactorValue *
          (ordinate * ordinate) -
        (primitive.scale * exponentCoefficient primitive / 2) * primitive.numerator.eval point *
          cofactorDerivative * baseVelocity * (ordinate * ordinate) -
        primitive.scale * exponentCoefficient primitive * primitive.numerator.eval point *
          cofactorValue * ordinate * ordinateVelocity := by
    rewrite [specification.coefficient_eq point, specification.first_eq, specification.last_eq]
    change ((primitive.scale * specification.numeratorDerivative.eval point) * polynomial.eval point -
      (primitive.scale * exponentCoefficient primitive / 2) *
        (primitive.numerator * specification.polynomialDerivative).eval point) * baseVelocity = _
    rewrite [Purelib.Polynomial.Dense.Basic.DensePolynomial.eval_mul,
      Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      _ = primitive.scale * specification.numeratorDerivative.eval point * polynomial.eval point * baseVelocity -
        primitive.scale * exponentCoefficient primitive * (2 : Canonical)⁻¹ * primitive.numerator.eval point *
          (specification.polynomialDerivative.eval point * baseVelocity) := by ring1
      _ = primitive.scale * specification.numeratorDerivative.eval point * baseVelocity * cofactorValue *
            (ordinate * ordinate) -
          primitive.scale * exponentCoefficient primitive * (2 : Canonical)⁻¹ * primitive.numerator.eval point *
            cofactorDerivative * baseVelocity * (ordinate * ordinate) -
          primitive.scale * exponentCoefficient primitive * primitive.numerator.eval point *
            cofactorValue * ordinate * ordinateVelocity * ((2 : Canonical)⁻¹ * 2) := by
        rewrite [curve_eq, curveVelocity_eq]
        ring1
      _ = _ := by rewrite [half, Gaussian.Basic.mul_one]; rfl
  have ordinateTwo := reciprocal_two ordinate ordinateNonzero primitive.denominatorExponent
  have ordinateNext : ordinate * ordinate⁻¹ ^ (primitive.denominatorExponent + 2) =
      ordinate⁻¹ ^ (primitive.denominatorExponent + 1) := by
    simpa only [Nat.add_assoc] using
      reciprocal_one ordinate ordinateNonzero (primitive.denominatorExponent + 1)
  have cofactorTwo := reciprocal_two cofactor cofactorNonzero primitive.denominatorExponent
  have ordinateOne := reciprocal_one ordinate ordinateNonzero primitive.denominatorExponent
  unfold spatialReading chainReading
  rewrite [specification.differential_exponent]
  calc
    _ = (primitive.scale * specification.numeratorDerivative.eval point * baseVelocity *
          ordinate⁻¹ ^ primitive.denominatorExponent -
        primitive.scale * exponentCoefficient primitive * primitive.numerator.eval point * ordinateVelocity *
          ordinate⁻¹ ^ (primitive.denominatorExponent + 1)) *
        cofactor⁻¹ ^ (primitive.denominatorExponent + 2) * (cofactorValue - cofactor * cofactor) := by
      rewrite [coefficient]
      calc
        _ = (primitive.scale * specification.numeratorDerivative.eval point * baseVelocity * cofactorValue *
                ((ordinate * ordinate) * ordinate⁻¹ ^ (primitive.denominatorExponent + 2)) -
            (primitive.scale * exponentCoefficient primitive / 2) * primitive.numerator.eval point *
              cofactorDerivative * baseVelocity *
                ((ordinate * ordinate) * ordinate⁻¹ ^ (primitive.denominatorExponent + 2)) -
            primitive.scale * exponentCoefficient primitive * primitive.numerator.eval point * cofactorValue *
              ordinateVelocity * (ordinate * ordinate⁻¹ ^ (primitive.denominatorExponent + 2))) *
              cofactor⁻¹ ^ (primitive.denominatorExponent + 2) -
            primitive.scale *
              (specification.numeratorDerivative.eval point * baseVelocity *
                  ordinate⁻¹ ^ primitive.denominatorExponent * cofactor⁻¹ ^ primitive.denominatorExponent -
                exponentCoefficient primitive * primitive.numerator.eval point * ordinateVelocity *
                  ordinate⁻¹ ^ (primitive.denominatorExponent + 1) * cofactor⁻¹ ^ primitive.denominatorExponent -
                (exponentCoefficient primitive / 2) * primitive.numerator.eval point * cofactorDerivative *
                  baseVelocity * ordinate⁻¹ ^ primitive.denominatorExponent *
                    cofactor⁻¹ ^ (primitive.denominatorExponent + 2)) := by ring1
        _ = _ := by
          rewrite [ordinateTwo, ordinateNext, ← cofactorTwo, Algebra.Field.ExplicitField.div_eq_mul_inv,
            Algebra.Field.ExplicitField.div_eq_mul_inv]
          ring1
    _ = _ := by rewrite [← ordinateOne]; ring1

/-- The fixed-box residual factor retains the original numerator, scale, exponent and two distinct root floors. -/
@[expose] def factor (primitive : OddPowerDifferential polynomial) (box : Box)
    (ordinateFloor cofactorFloor baseVelocityUpper ordinateUpper ordinateVelocityUpper : Fraction.Rational) :
    Fraction.Rational :=
  Norm.Basic.normSq primitive.scale *
    (2 * (Bounds.Box.denseEvalNormBound (GCD.derivative primitive.numerator) box *
          baseVelocityUpper * ordinateUpper +
        Norm.Basic.normSq (exponentCoefficient primitive) *
          Bounds.Box.denseEvalNormBound primitive.numerator box * ordinateVelocityUpper)) *
    ordinateFloor⁻¹ ^ (primitive.denominatorExponent + 1) *
    cofactorFloor⁻¹ ^ (primitive.denominatorExponent + 2)

/-- The factored derivative residual budget is nonnegative under its original floors and geometric ceilings. -/
theorem factor_nonnegative (primitive : OddPowerDifferential polynomial) (box : Box)
    {ordinateFloor cofactorFloor baseVelocityUpper ordinateUpper ordinateVelocityUpper : Fraction.Rational}
    (ordinatePositive : 0 < ordinateFloor) (cofactorPositive : 0 < cofactorFloor)
    (baseVelocityNonnegative : 0 ≤ baseVelocityUpper) (ordinateNonnegative : 0 ≤ ordinateUpper)
    (ordinateVelocityNonnegative : 0 ≤ ordinateVelocityUpper) :
    0 ≤ factor primitive box ordinateFloor cofactorFloor baseVelocityUpper ordinateUpper ordinateVelocityUpper := by
  have derivativeNonnegative := (Bounds.Box.denseHornerNormBounds_nonneg (GCD.derivative primitive.numerator) box).1
  have numeratorNonnegative := (Bounds.Box.denseHornerNormBounds_nonneg primitive.numerator box).1
  have first := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct derivativeNonnegative baseVelocityNonnegative) ordinateNonnegative
  have last := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg (exponentCoefficient primitive))
      numeratorNonnegative) ordinateVelocityNonnegative
  unfold factor
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg primitive.scale)
        (Arithmetic.mul_nonneg_direct (by decide +kernel)
          (Arithmetic.add_le_add_direct first last)))
      (Arithmetic.pow_nonneg_direct (Fraction.Order.Field.inv_pos_direct ordinatePositive).le _))
    (Arithmetic.pow_nonneg_direct (Fraction.Order.Field.inv_pos_direct cofactorPositive).le _)

/-- The original source square residual quantitatively bounds both prescribed derivative readings' discrepancy. -/
theorem difference_normSq_le (specification : Specification polynomial primitive)
    (point ordinate cofactor baseVelocity ordinateVelocity cofactorValue cofactorDerivative : Canonical)
    (ordinateNonzero : ordinate ≠ 0) (cofactorNonzero : cofactor ≠ 0)
    (curve_eq : polynomial.eval point = cofactorValue * (ordinate * ordinate))
    (curveVelocity_eq : specification.polynomialDerivative.eval point * baseVelocity =
      cofactorDerivative * baseVelocity * (ordinate * ordinate) +
        2 * cofactorValue * ordinate * ordinateVelocity)
    {box : Box} (inside : box.Contains point)
    {ordinateFloor cofactorFloor baseVelocityUpper ordinateUpper ordinateVelocityUpper allowance : Fraction.Rational}
    (ordinatePositive : 0 < ordinateFloor) (cofactorPositive : 0 < cofactorFloor)
    (ordinateLower : ordinateFloor ≤ Norm.Basic.normSq ordinate)
    (cofactorLower : cofactorFloor ≤ Norm.Basic.normSq cofactor)
    (baseVelocityBound : Norm.Basic.normSq baseVelocity ≤ baseVelocityUpper)
    (ordinateBound : Norm.Basic.normSq ordinate ≤ ordinateUpper)
    (ordinateVelocityBound : Norm.Basic.normSq ordinateVelocity ≤ ordinateVelocityUpper)
    (residual : Norm.Basic.normSq (cofactor * cofactor - cofactorValue) ≤ allowance) :
    Norm.Basic.normSq (spatialReading specification point ordinate cofactor baseVelocity -
      chainReading specification point ordinate cofactor baseVelocity ordinateVelocity cofactorDerivative) ≤
      factor primitive box ordinateFloor cofactorFloor baseVelocityUpper ordinateUpper ordinateVelocityUpper *
        allowance := by
  have derivativeBound : Norm.Basic.normSq (specification.numeratorDerivative.eval point) ≤
      Bounds.Box.denseEvalNormBound (GCD.derivative primitive.numerator) box := by
    rewrite [specification.numeratorDerivative_eq]
    exact Bounds.Box.normSq_eval_le_denseEvalNormBound _ inside
  have numeratorBound := Bounds.Box.normSq_eval_le_denseEvalNormBound primitive.numerator inside
  have firstProduct := Arithmetic.mul_le_mul_direct derivativeBound baseVelocityBound
    (Norm.Basic.normSq_nonneg _) ((Norm.Basic.normSq_nonneg _).trans derivativeBound)
  have first := Arithmetic.mul_le_mul_direct firstProduct ordinateBound
    (Norm.Basic.normSq_nonneg _)
    ((Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg _)
      (Norm.Basic.normSq_nonneg _)).trans firstProduct)
  have lastProduct := Arithmetic.mul_le_mul_of_nonneg_left_direct numeratorBound
    (Norm.Basic.normSq_nonneg (exponentCoefficient primitive))
  have last := Arithmetic.mul_le_mul_direct lastProduct ordinateVelocityBound
    (Norm.Basic.normSq_nonneg _)
    ((Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg _)
      (Norm.Basic.normSq_nonneg _)).trans lastProduct)
  have numerator : Norm.Basic.normSq
      (specification.numeratorDerivative.eval point * baseVelocity * ordinate -
        exponentCoefficient primitive * primitive.numerator.eval point * ordinateVelocity) ≤
      2 * (Bounds.Box.denseEvalNormBound (GCD.derivative primitive.numerator) box *
          baseVelocityUpper * ordinateUpper +
        Norm.Basic.normSq (exponentCoefficient primitive) *
          Bounds.Box.denseEvalNormBound primitive.numerator box * ordinateVelocityUpper) := by
    exact (Norm.Bounds.normSq_sub_le_two _ _).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct
          (by simpa only [Norm.Basic.normSq_mul] using first)
          (by simpa only [Norm.Basic.normSq_mul] using last)) (by decide +kernel))
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct numerator
    (Norm.Basic.normSq_nonneg primitive.scale)
  have scaledNonnegative : 0 ≤ Norm.Basic.normSq primitive.scale * Norm.Basic.normSq
      (specification.numeratorDerivative.eval point * baseVelocity * ordinate -
        exponentCoefficient primitive * primitive.numerator.eval point * ordinateVelocity) :=
    Arithmetic.mul_nonneg_direct
      (Norm.Basic.normSq_nonneg primitive.scale) (Norm.Basic.normSq_nonneg _)
  have ordinatePaid := Arithmetic.mul_le_mul_direct scaled
    (Norm.Reciprocal.power_normSq_le ordinatePositive ordinateLower (primitive.denominatorExponent + 1))
    (Norm.Basic.normSq_nonneg _) (scaledNonnegative.trans scaled)
  have ordinatePaidNonnegative := Arithmetic.mul_nonneg_direct scaledNonnegative
    (Norm.Basic.normSq_nonneg (ordinate⁻¹ ^ (primitive.denominatorExponent + 1)))
  have cofactorPaid := Arithmetic.mul_le_mul_direct ordinatePaid
    (Norm.Reciprocal.power_normSq_le cofactorPositive cofactorLower (primitive.denominatorExponent + 2))
    (Norm.Basic.normSq_nonneg _) (ordinatePaidNonnegative.trans ordinatePaid)
  have cofactorPaidNonnegative := Arithmetic.mul_nonneg_direct ordinatePaidNonnegative
    (Norm.Basic.normSq_nonneg (cofactor⁻¹ ^ (primitive.denominatorExponent + 2)))
  have reverse : cofactorValue - cofactor * cofactor = -(cofactor * cofactor - cofactorValue) := by ring1
  rewrite [difference_eq specification point ordinate cofactor baseVelocity ordinateVelocity
    cofactorValue cofactorDerivative ordinateNonzero cofactorNonzero curve_eq curveVelocity_eq,
    reverse, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul,
    Norm.Basic.normSq_mul, Norm.Basic.normSq_neg]
  exact Arithmetic.mul_le_mul_direct cofactorPaid residual
    (Norm.Basic.normSq_nonneg _) (cofactorPaidNonnegative.trans cofactorPaid)

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative.Factorization

end
