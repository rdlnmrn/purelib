module
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Basic
import Purelib.Tactic.Ring
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.GaussianInt.Conjugate
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Fraction.NaturalDenominator.ScaledNumerator
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.LCM
public import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Polynomial
import Purelib.Polynomial.Dense.GaussianInt.Evaluation
public import Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous
import Purelib.Data.List.Map

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Data

section
@[expose] public section

/-!
# Intrinsic Gaussian-denominator residual bounds

This module repeats the finite homogeneous-evaluation argument with a
displayed Gaussian-integer denominator.  It also gives exact conversions in
both directions between Gaussian-denominator records and the older positive
natural common-denominator records.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Residual.GaussianDenominator

open Purelib.Data Purelib.Data.List
open Purelib.Polynomial.Dense.Gaussian.Denominator

/-- Explicit Gaussian-integer residual numerator for a displayed Gaussian
fraction. -/
def residualNumerator (p :
  CoefficientPolynomial) (fraction : GaussianInt.Fraction) :
    GaussianInt :=
  Dense.GaussianInt.Evaluation.Homogeneous.homogeneousEval fraction.numerator fraction.denominator
    (Dense.Gaussian.Denominator.Clearing.LCM.lcmClear p.normalize.coeffs).coefficients

/-- Homogeneous integer residual readback retains the exact cleared polynomial evaluation.

The original normalized coefficient list, LCM scale and Gaussian denominator
power determine the same integral numerator and source evaluation. -/
theorem residualNumerator_identity
    (p : CoefficientPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianInt.Fraction) :
    GaussianInt.toGaussian (residualNumerator p fraction) =
      GaussianInt.toGaussian fraction.denominator ^ p.natDegree *
        (⟨(Dense.Gaussian.Denominator.Clearing.coefficientScale p : Fraction.Rational), 0⟩ *
          p.eval fraction.value) := by
  obtain ⟨tail, coefficients, tailLength⟩ :=
    DensePolynomial.normalized_coeffs_shape nonzero
  unfold residualNumerator
    Dense.Gaussian.Denominator.Clearing.coefficientScale
  rw [show p.normalize.coeffs = p.leadingCoeff :: tail from coefficients]
  rw [show (Dense.Gaussian.Denominator.Clearing.LCM.lcmClear
      (p.leadingCoeff :: tail)).coefficients =
        Gaussian.Fraction.NaturalDenominator.ScaledNumerator.scaledGaussianCoefficient
            (Dense.Gaussian.Denominator.Clearing.LCM.lcmScale (p.leadingCoeff :: tail))
            p.leadingCoeff ::
          tail.map (Gaussian.Fraction.NaturalDenominator.ScaledNumerator.scaledGaussianCoefficient
            (Dense.Gaussian.Denominator.Clearing.LCM.lcmScale (p.leadingCoeff :: tail)))
    from rfl]
  rw [Dense.GaussianInt.Evaluation.Homogeneous.homogeneousEval_cons_eq_scaled]
  have remainingLength :
      (tail.map (Gaussian.Fraction.NaturalDenominator.ScaledNumerator.scaledGaussianCoefficient
        (Dense.Gaussian.Denominator.Clearing.LCM.lcmScale
          (p.leadingCoeff :: tail)))).length = p.natDegree := by
    exact (Map.length_map _ tail).trans tailLength
  rw [remainingLength]
  change
    GaussianInt.toGaussian fraction.denominator ^ p.natDegree *
        Dense.GaussianInt.Evaluation.evalIntegers fraction.value
          (Dense.Gaussian.Denominator.Clearing.LCM.lcmClear
            (p.leadingCoeff :: tail)).coefficients = _
  rw [Dense.Gaussian.Denominator.Clearing.LCM.eval_lcmClear]
  rw [← DensePolynomial.eval_normalize]
  unfold DensePolynomial.eval
  rw [coefficients]

/-- The intrinsic Gaussian-denominator scaled residual is exactly the norm of
the displayed integral numerator.

The retained Gaussian denominator and scaled integral numerator describe the same
polynomial evaluation. Their exact quadrances give the displayed residual
identity. -/
theorem scaled_height_mul_residual_eq_normNat
    (p : CoefficientPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianInt.Fraction) :
    (Dense.Gaussian.Denominator.Clearing.coefficientScale p : Fraction.Rational) ^ 2 *
          (fraction.height : Fraction.Rational) ^ p.natDegree *
        Data.Gaussian.Norm.Basic.normSq (p.eval fraction.value) =
      (GaussianInt.normNat (residualNumerator p fraction) :
        Fraction.Rational) := by
  have denominatorNorm :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian fraction.denominator) =
        (fraction.height : Fraction.Rational) := by
    exact GaussianInt.normSq_toGaussian fraction.denominator
  have scaleNorm :
      Data.Gaussian.Norm.Basic.normSq
          (⟨(Dense.Gaussian.Denominator.Clearing.coefficientScale p : Fraction.Rational), 0⟩ :
            Gaussian.Basic.Canonical) =
        (Dense.Gaussian.Denominator.Clearing.coefficientScale p : Fraction.Rational) ^ 2 := by
    change
      (Dense.Gaussian.Denominator.Clearing.coefficientScale p : Fraction.Rational) ^ 2 + 0 ^ 2 = _
    rw [pow_two (0 : Rat.Fraction.Rational), zero_mul, add_zero]
  rw [← GaussianInt.normSq_toGaussian, residualNumerator_identity p nonzero
    fraction,
    Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul, Gaussian.Power.normSq_pow, denominatorNorm,
      scaleNorm]
  rw [mul_comm
    ((Dense.Gaussian.Denominator.Clearing.coefficientScale p : Rat.Fraction.Rational) ^ 2)
    ((fraction.height : Rat.Fraction.Rational) ^ p.natDegree), mul_assoc]

/-- A nonzero polynomial evaluation gives a nonzero integral residual numerator. -/
theorem residualNumerator_ne_zero
    (p : CoefficientPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianInt.Fraction)
    (residualNonzero : p.eval fraction.value ≠ 0) :
    residualNumerator p fraction ≠ 0 := by
  intro numeratorZero
  have embeddedZero := congrArg GaussianInt.toGaussian numeratorZero
  rw [GaussianInt.toGaussian_zero, residualNumerator_identity p nonzero
    fraction]
    at embeddedZero
  have denominatorNonzero := fraction.denominatorGaussianNonzero
  have scalePositive := Dense.Gaussian.Denominator.Clearing.coefficientScale_pos p
  have scaleNonzero :
      (⟨(Dense.Gaussian.Denominator.Clearing.coefficientScale p : Fraction.Rational), 0⟩ :
        Gaussian.Basic.Canonical) ≠ 0 := by
    intro zero
    have realZero := congrArg Gaussian.Basic.re zero
    have scaleZero := Fraction.Cast.Compatibility.natCast_injective_direct
      (realZero.trans (Nat.cast_zero).symm)
    exact (Nat.ne_of_gt scalePositive) scaleZero
  have productNonzero := Gaussian.Field.mul_ne_zero_direct
    (Gaussian.Power.pow_ne_zero_direct _
      denominatorNonzero p.natDegree)
    (Gaussian.Field.mul_ne_zero_direct scaleNonzero
      residualNonzero)
  exact productNonzero embeddedZero

/-- Intrinsic Gaussian-denominator height obstruction. -/
theorem one_le_scaled_height_mul_residual
    (p : CoefficientPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianInt.Fraction)
    (residualNonzero : p.eval fraction.value ≠ 0) :
    (1 : Fraction.Rational) ≤
      (Dense.Gaussian.Denominator.Clearing.coefficientScale p : Fraction.Rational) ^ 2 *
        (fraction.height : Fraction.Rational) ^ p.natDegree *
          Data.Gaussian.Norm.Basic.normSq (p.eval fraction.value) := by
  have numeratorPositive := GaussianInt.normNat_pos
    (residualNumerator_ne_zero p nonzero fraction residualNonzero)
  have castLower : (1 : Fraction.Rational) ≤
      (GaussianInt.normNat (residualNumerator p fraction) :
        Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct numeratorPositive
  rw [← scaled_height_mul_residual_eq_normNat p nonzero fraction]
    at castLower
  exact castLower
end Purelib.Polynomial.Dense.Gaussian.Residual.GaussianDenominator

end
