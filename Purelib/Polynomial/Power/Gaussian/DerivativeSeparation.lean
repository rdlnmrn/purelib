module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import all Purelib.Data.Gaussian.Power.Residual.Bounds

import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import all Purelib.Data.Rat.Fraction.Power.Order

import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
public import Purelib.Polynomial.Power.Gaussian
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Polynomial.Power.Gaussian.DerivativeSeparation
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- Uniform finite derivative separation for `Z^d-w` on any displayed box
when the exact parameter has quadrance one.  The threshold `1/4` and margin
`1/8` do not depend on a completed root or on a compactness argument. -/
def unitParameterDerivativeSeparation
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (_degreeAtLeastTwo : 2 ≤ degree.value)
    (ambient : Box) :
    Dense.Gaussian.Derivative.Separation.Basic.Certificate
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) ambient where
  threshold := 1 / 4
  threshold_pos := by decide
  margin := 1 / 8
  margin_pos := by decide
  lower := by
    intro point _inside residualSmall
    have powerResidual : Data.Gaussian.Norm.Basic.normSq (point ^ degree.value - parameter) ≤
        (1 / 4 : Fraction.Rational) := by
      rw [← Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval parameter point degree]
      exact residualSmall
    have powerLower := Purelib.Data.Gaussian.Power.Residual.Bounds.one_fourth_le_normSq_power_of_residual_le_quarter
      parameterUnit powerResidual
    have predecessorLower := Purelib.Data.Rat.Fraction.Power.Order.one_eighth_le_power_predecessor degree.positive
      powerLower (Gaussian.Norm.Basic.normSq_nonneg point)
    rw [Power.Gaussian.derivative_eval, Gaussian.Norm.Basic.normSq_mul, Purelib.Data.Gaussian.Power.normSq_pow]
    have degreeCastLower : (1 : Fraction.Rational) ≤
        (degree.value : Fraction.Rational) :=
      Purelib.Data.Rat.Fraction.Cast.Order.natCast_le_direct degree.positive
    have degreeNormLower : (1 : Fraction.Rational) ≤
        Data.Gaussian.Norm.Basic.normSq (degree.value : Gaussian.Basic.Canonical) := by
      have identity : Data.Gaussian.Norm.Basic.normSq (degree.value : Gaussian.Basic.Canonical) =
          (degree.value : Fraction.Rational) ^ 2 := by
        simp only [Data.Gaussian.Norm.Basic.normSq,
          Purelib.Data.Gaussian.Cast.natCast_re,
          Purelib.Data.Gaussian.Cast.natCast_im]
        ring1
      rw [identity]
      simpa only [one_pow] using
        Purelib.Data.Rat.Fraction.Order.Arithmetic.pow_le_pow_direct
          (show (0 : Fraction.Rational) ≤ 1 by decide) degreeCastLower 2
    calc
      (1 / 8 : Fraction.Rational) =
          1 * (1 / 8 : Fraction.Rational) := by ring1
      _ ≤ Data.Gaussian.Norm.Basic.normSq (degree.value : Gaussian.Basic.Canonical) *
          (Data.Gaussian.Norm.Basic.normSq point ^ (degree.value - 1)) :=
        Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_direct degreeNormLower
          predecessorLower (by decide)
          (Gaussian.Norm.Basic.normSq_nonneg (degree.value : Gaussian.Basic.Canonical))
end Purelib.Polynomial.Power.Gaussian.DerivativeSeparation

end
