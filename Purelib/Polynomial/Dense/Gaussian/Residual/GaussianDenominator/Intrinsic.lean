module
import Purelib.Data.Rat.Fraction
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Data.GaussianInt.Fraction.Canonical.Height
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Polynomial
public import Purelib.Polynomial.Dense.Gaussian.Residual.GaussianDenominator
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Fraction.Canonical
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data.GaussianInt.Fraction.Canonical

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Intrinsic Gaussian-denominator residual bounds

This module repeats the finite homogeneous-evaluation argument with a
displayed Gaussian-integer denominator.  It also gives exact conversions in
both directions between Gaussian-denominator records and the older positive
natural common-denominator records.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Residual.GaussianDenominator.Intrinsic

/-- Homogeneous residual numerator evaluated at the canonical reduced
coordinates. -/
def intrinsicResidualNumerator
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (fraction : GaussianInt.Fraction) : GaussianInt :=
  residualNumerator p
    (Height.canonicalReduction fraction).displayed

/-- The residual obstruction computed at canonical reduced coordinates is an
exact Gaussian-integer norm identity. -/
theorem
  scaled_intrinsicHeight_mul_residual_eq_normNat
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianInt.Fraction) :
    (Denominator.Clearing.coefficientScale p : Fraction.Rational) ^ 2 *
          (Height.intrinsicHeight fraction : Fraction.Rational) ^ p.natDegree *
        Gaussian.Norm.Basic.normSq (p.eval fraction.value) =
      (GaussianInt.normNat (intrinsicResidualNumerator p fraction)
        : Fraction.Rational) := by
  have identity := scaled_height_mul_residual_eq_normNat p nonzero
    (Height.canonicalReduction fraction).displayed
  change
    (Denominator.Clearing.coefficientScale p : Fraction.Rational) ^ 2 *
          ((Height.canonicalReduction fraction).height : Fraction.Rational) ^ p.natDegree
            *
        Gaussian.Norm.Basic.normSq (p.eval fraction.value) =
      (GaussianInt.normNat
        (residualNumerator p
          (Height.canonicalReduction fraction).displayed) :
          Fraction.Rational)
  rw [← Height.canonicalReduction_value fraction]
  exact identity

/-- Intrinsic reduced Gaussian-denominator height obstruction. -/
theorem
  one_le_scaled_intrinsicHeight_mul_residual
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianInt.Fraction)
    (residualNonzero : p.eval fraction.value ≠ 0) :
    (1 : Fraction.Rational) ≤
      (Denominator.Clearing.coefficientScale p : Fraction.Rational) ^ 2 *
        (Height.intrinsicHeight fraction : Fraction.Rational) ^ p.natDegree *
          Gaussian.Norm.Basic.normSq (p.eval fraction.value) := by
  have reducedResidualNonzero :
      p.eval (Height.canonicalReduction fraction).displayed.value ≠ 0 := by
    change p.eval (Height.canonicalReduction fraction).value ≠ 0
    rw [Height.canonicalReduction_value]
    exact residualNonzero
  have bound := one_le_scaled_height_mul_residual p nonzero
    (Height.canonicalReduction fraction).displayed reducedResidualNonzero
  change
    (1 : Fraction.Rational) ≤
      (Denominator.Clearing.coefficientScale p : Fraction.Rational) ^ 2 *
        ((Height.canonicalReduction fraction).height : Fraction.Rational) ^ p.natDegree *
          Gaussian.Norm.Basic.normSq (p.eval fraction.value)
  rw [← Height.canonicalReduction_value fraction]
  exact bound
end Purelib.Polynomial.Dense.Gaussian.Residual.GaussianDenominator.Intrinsic

end
