module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Norm.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

section
@[expose] public section

/-!
# Finite rational curves and denominator-cleared polynomial evaluation

A rationally parameterized Gaussian curve is represented by two finite dense
Gaussian polynomials `N(t)` and `D(t)`.  Evaluation means `N(t) / D(t)` only
at an explicitly supplied nonzero denominator.  A Horner fold computes
`D(t)^n p(N(t)/D(t))` without division; its real and imaginary coefficient
polynomials are therefore suitable for finite gcd and Sturm calculations.
-/

namespace Purelib.RationalFunctions.Curve

/- The doubled public name `Purelib.CCL.Boundary.Curve.Rational.RationalCurve` is intentional:
the outer component names the module and the inner component names its main
finite data type. -/

open Purelib.Polynomial in
set_option genInjectivity false in
/-- A rational Gaussian curve represented by two finite dense polynomials.

The numerator and denominator are evaluated at rational parameters embedded in the Gaussian rationals. Affine
cancellation identities require an explicit nonzero denominator at the chosen parameter. -/
structure RationalCurve where
  /-- The dense Gaussian polynomial defining the curve's numerator. -/ numerator :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  /-- The dense Gaussian polynomial defining the curve's denominator. -/ denominator :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial

constructive_injectivity RationalCurve

namespace RationalCurve

open Purelib.Data
open Purelib.RationalFunctions
/-- Evaluate the numerator at the Gaussian embedding of a rational parameter. -/
def numeratorAt (curve : Curve.RationalCurve) (parameter :
  Rational) : Canonical :=
  curve.numerator.eval (Gaussian.Cast.Path.ofCoordinate parameter)

/-- Evaluate the denominator at the Gaussian embedding of a rational parameter. -/
def denominatorAt
    (curve : Curve.RationalCurve) (parameter : Rational) : Canonical :=
  curve.denominator.eval
    (Gaussian.Cast.Path.ofCoordinate parameter)

/-- Multiply the evaluated numerator by the inverse of the evaluated denominator.

This definition uses the Gaussian field's total inverse operation. Its affine cancellation guarantees require a separate
nonzero-denominator witness. -/
def point (curve : Curve.RationalCurve) (parameter :
  Rational) : Canonical :=
  curve.numeratorAt parameter * (curve.denominatorAt parameter)⁻¹

/-- At a nonzero denominator, multiplying the affine point by that denominator recovers the numerator. -/
theorem numeratorAt_eq_point_mul_denominatorAt
    (curve : Curve.RationalCurve) (parameter : Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    curve.numeratorAt parameter =
      curve.point parameter * curve.denominatorAt parameter := by
  unfold Curve.RationalCurve.point
  symm
  calc
    (curve.numeratorAt parameter * (curve.denominatorAt parameter)⁻¹) *
        curve.denominatorAt parameter =
      curve.numeratorAt parameter *
        ((curve.denominatorAt parameter)⁻¹ *
          curve.denominatorAt parameter) :=
      Gaussian.Basic.mul_assoc _ _ _
    _ = curve.numeratorAt parameter * 1 := by
      rw [Canonical.inv_mul_cancel _
        denominatorNonzero]
    _ = curve.numeratorAt parameter :=
      Gaussian.Basic.mul_one _
end RationalCurve
end Purelib.RationalFunctions.Curve

end
