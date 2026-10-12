module
import Purelib.Data.List.Map
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.Gaussian.Fraction.NaturalDenominator.ScaledNumerator
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.LCM
public import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Polynomial
import Purelib.Polynomial.Dense.GaussianInt.Evaluation
public import Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic.Canonical.Fraction (NaturalDenominator)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite denominator-height lower bounds for polynomial residuals

The finite coefficient list is cleared to Gaussian integers by a structural
product of the canonical coordinate denominators.  Homogeneous evaluation at
a displayed common-denominator Gaussian fraction then gives an integral
numerator.  If the residual is nonzero, its integral norm is at least one.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Residual.NaturalDenominator

/-- Integral homogeneous numerator of a polynomial evaluation at a displayed
common-denominator Gaussian fraction. -/
def residualNumerator (p :
  CoefficientPolynomial) (fraction :
    NaturalDenominator) :
    GaussianInt :=
  Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.homogeneousEval fraction.numerator fraction.denominator
    (Dense.Gaussian.Denominator.Clearing.LCM.lcmClear p.normalize.coeffs).coefficients

/-- Embedding the explicit integral residual numerator gives the original evaluation multiplied by the retained
denominator power and coefficient scale. -/
theorem residualNumerator_identity
    (p : CoefficientPolynomial) (nonzero : p.isZero = false)
    (fraction : NaturalDenominator) :
    GaussianInt.toGaussian
        (residualNumerator p fraction) =
      ⟨(fraction.denominator : Fraction.Rational), 0⟩ ^ p.natDegree *
        (⟨(Dense.Gaussian.Denominator.Clearing.coefficientScale p : Fraction.Rational), 0⟩ *
          p.eval fraction.value) := by
  obtain ⟨tail, coefficients, tailLength⟩ :=
    DensePolynomial.normalized_coeffs_shape nonzero
  unfold residualNumerator
    Dense.Gaussian.Denominator.Clearing.coefficientScale
  rw [show p.normalize.coeffs = p.leadingCoeff :: tail from coefficients]
  rw [show (Dense.Gaussian.Denominator.Clearing.LCM.lcmClear (p.leadingCoeff :: tail)).coefficients =
      Gaussian.Fraction.NaturalDenominator.ScaledNumerator.scaledGaussianCoefficient
        (Dense.Gaussian.Denominator.Clearing.LCM.lcmScale (p.leadingCoeff :: tail))
          p.leadingCoeff ::
        tail.map
          (Gaussian.Fraction.NaturalDenominator.ScaledNumerator.scaledGaussianCoefficient
            (Dense.Gaussian.Denominator.Clearing.LCM.lcmScale (p.leadingCoeff :: tail)))
    from rfl]
  rw [Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.homogeneousEval_cons_eq_scaled]
  have remainingLength :
      (tail.map
        (Gaussian.Fraction.NaturalDenominator.ScaledNumerator.scaledGaussianCoefficient
          (Dense.Gaussian.Denominator.Clearing.LCM.lcmScale (p.leadingCoeff :: tail)))).length =
          p.natDegree := by
    exact (Data.List.Map.length_map _ tail).trans tailLength
  rw [remainingLength]
  change
    ⟨(fraction.denominator : Fraction.Rational), 0⟩ ^ p.natDegree *
        Dense.GaussianInt.Evaluation.evalIntegers fraction.value
          (Dense.Gaussian.Denominator.Clearing.LCM.lcmClear (p.leadingCoeff :: tail)).coefficients = _
  rw [Dense.Gaussian.Denominator.Clearing.LCM.eval_lcmClear]
  rw [← DensePolynomial.eval_normalize]
  unfold DensePolynomial.eval
  rw [coefficients]

/-- A nonzero displayed residual produces a nonzero integral homogeneous
numerator. -/
theorem residualNumerator_ne_zero
    (p : CoefficientPolynomial) (nonzero : p.isZero = false)
    (fraction : NaturalDenominator) (residualNonzero : p.eval fraction.value ≠ 0) :
    residualNumerator p fraction ≠ 0 := by
  intro numeratorZero
  have embeddedZero := congrArg
    GaussianInt.toGaussian numeratorZero
  rw [GaussianInt.toGaussian_zero,
    residualNumerator_identity p nonzero fraction] at embeddedZero
  have denominatorNonzero :
      (⟨(fraction.denominator : Fraction.Rational), 0⟩ : Gaussian.Basic.Canonical) ≠ 0 := by
    intro zero
    have realZero := congrArg Gaussian.Basic.re zero
    have denominatorZero := Fraction.Cast.Compatibility.natCast_injective_direct
      (realZero.trans (Nat.cast_zero).symm)
    exact (Nat.ne_of_gt fraction.denominatorPositive) denominatorZero
  have scalePositive : 0 < Dense.Gaussian.Denominator.Clearing.coefficientScale p :=
    Dense.Gaussian.Denominator.Clearing.coefficientScale_pos p
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

open Purelib.Algebra in
/-- Exact finite residual identity underlying the denominator-height bound.
The scaled residual is not merely bounded below: it is the norm of the
explicit homogeneous Gaussian-integer numerator. -/
theorem scaled_height_mul_residual_eq_normNat
    (p : CoefficientPolynomial) (nonzero : p.isZero = false)
    (fraction : NaturalDenominator) :
    (Dense.Gaussian.Denominator.Clearing.coefficientScale p : Fraction.Rational) ^ 2 *
          (fraction.height : Fraction.Rational) ^ p.natDegree *
        Data.Gaussian.Norm.Basic.normSq (p.eval fraction.value) =
      (GaussianInt.normNat
        (residualNumerator p fraction) : Fraction.Rational) := by
  have denominatorNorm :
      Data.Gaussian.Norm.Basic.normSq (⟨(fraction.denominator : Fraction.Rational), 0⟩ : Gaussian.Basic.Canonical) =
        (fraction.height : Fraction.Rational) := by
    change (fraction.denominator : Fraction.Rational) ^ 2 + 0 ^ 2 =
      (fraction.denominator ^ 2 : Nat)
    rw [NatCast.pow]
    ring1
  have scaleNorm :
      Data.Gaussian.Norm.Basic.normSq (⟨(Dense.Gaussian.Denominator.Clearing.coefficientScale p :
        Fraction.Rational), 0⟩ : Gaussian.Basic.Canonical) =
        (Dense.Gaussian.Denominator.Clearing.coefficientScale p : Fraction.Rational) ^ 2 := by
    change (Dense.Gaussian.Denominator.Clearing.coefficientScale p : Fraction.Rational) ^ 2 + 0 ^ 2 = _
    ring1
  rw [← GaussianInt.normSq_toGaussian,
    residualNumerator_identity p nonzero fraction,
      Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul,
    Gaussian.Power.normSq_pow, denominatorNorm, scaleNorm]
  ring1

/-- Equality in the unit lower bound occurs exactly when the displayed
integral residual numerator has Gaussian norm one. -/
theorem scaled_height_mul_residual_eq_one_iff
    (p : CoefficientPolynomial) (nonzero : p.isZero = false)
    (fraction : NaturalDenominator) :
    (Dense.Gaussian.Denominator.Clearing.coefficientScale p : Fraction.Rational) ^ 2 *
          (fraction.height : Fraction.Rational) ^ p.natDegree *
        Data.Gaussian.Norm.Basic.normSq (p.eval fraction.value) = 1 ↔
      GaussianInt.normNat
        (residualNumerator p fraction) = 1 := by
  rw [scaled_height_mul_residual_eq_normNat p nonzero fraction]
  constructor
  · intro equality
    apply Fraction.Cast.Compatibility.natCast_injective_direct
    simpa only [Nat.cast_one] using equality
  · intro equality
    rw [equality, Nat.cast_one]

/-- Finite Liouville-type lower bound in multiplied form.  No root object is
used: the proof is only coefficient clearing, homogeneous evaluation, and the
fact that a nonzero Gaussian integer has norm at least one. -/
theorem one_le_scaled_height_mul_residual
    (p : CoefficientPolynomial) (nonzero : p.isZero = false)
    (fraction : NaturalDenominator) (residualNonzero : p.eval fraction.value ≠ 0) :
    (1 : Fraction.Rational) ≤
      (Dense.Gaussian.Denominator.Clearing.coefficientScale p : Fraction.Rational) ^ 2 *
        (fraction.height : Fraction.Rational) ^ p.natDegree *
          Data.Gaussian.Norm.Basic.normSq (p.eval fraction.value) := by
  have numeratorNonzero :=
    residualNumerator_ne_zero p nonzero fraction residualNonzero
  have numeratorPositive :=
    GaussianInt.normNat_pos numeratorNonzero
  have oneLeNat : 1 ≤
      GaussianInt.normNat
        (residualNumerator p fraction) := numeratorPositive
  have oneLeCast : (1 : Fraction.Rational) ≤
      (GaussianInt.normNat
        (residualNumerator p fraction) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct oneLeNat
  rw [← scaled_height_mul_residual_eq_normNat p nonzero fraction]
    at oneLeCast
  exact oneLeCast

end Purelib.Polynomial.Dense.Gaussian.Residual.NaturalDenominator

end
