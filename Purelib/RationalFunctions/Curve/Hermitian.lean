module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RationalFunctions.Curve.Coordinates
import Purelib.Tactic.Ring

open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

section
@[expose] public section

/-!
# CCL formulas cleared along rational boundary curves

Every Hermitian atom pulled back to a rational curve is compiled to one
explicit univariate rational polynomial.  Its value is the original atom
form multiplied by the positive quadrance of the curve denominator, so all
six parser sign tests are preserved at every displayed non-pole parameter.

This finite compiler lets the event layer feed all atoms of a candidate
one-bit formula into the existing equality/apart gcd profiler.  No affine
point, polynomial root, or limiting value is introduced by the translation.
-/

namespace Purelib.RationalFunctions.Curve.Hermitian

open Purelib.Data
open Purelib.Polynomial
open Purelib.Geometry
open Purelib.RationalFunctions
/-- Compile a Hermitian form along a rational curve to a denominator-cleared rational polynomial.

The radial coefficient scales numerator quadrance, the linear coefficients scale the two affine coordinate numerators,
and the constant scales denominator quadrance. -/
def clearedForm (curve : Curve.RationalCurve) (form :
  HermitianForm) : (DensePolynomial Rat.Fraction.Rational) :=
  DensePolynomial.scale form.radial (Curve.Coordinates.numeratorNormSq curve) +
    DensePolynomial.scale form.realLinear
      (Curve.Coordinates.affineRealNumerator curve) +
    DensePolynomial.scale form.imagLinear
      (Curve.Coordinates.affineImaginaryNumerator curve) +
    DensePolynomial.scale form.constant
      (Curve.Coordinates.denominatorNormSq curve)

/-- Cleared Hermitian evaluation equals denominator quadrance times the affine Hermitian value.

The curve denominator is explicitly nonzero at the rational parameter. Its positive quadrance is the common factor
introduced by clearing the affine coordinates. -/
theorem eval_clearedForm
    (curve : Curve.RationalCurve) (form : HermitianForm)
    (parameter : Rat.Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (clearedForm curve form).eval parameter =
      Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter) *
        form.eval (curve.point parameter) := by
  have numeratorIdentity :=
    curve.numeratorAt_eq_point_mul_denominatorAt parameter
      denominatorNonzero
  have normIdentity := congrArg Gaussian.Norm.Basic.normSq numeratorIdentity
  rw [Gaussian.Norm.Basic.normSq_mul] at normIdentity
  simp only [clearedForm, DensePolynomial.eval_add, DensePolynomial.eval_scale,
    Curve.Coordinates.eval_numeratorNormSq,
    Curve.Coordinates.eval_affineRealNumerator_eq_point_mul_normSq
      curve parameter denominatorNonzero,
    Curve.Coordinates.eval_affineImaginaryNumerator_eq_point_mul_normSq
      curve parameter denominatorNonzero,
    Curve.Coordinates.eval_denominatorNormSq,
    HermitianForm.eval]
  rw [normIdentity]
  ring1
end Purelib.RationalFunctions.Curve.Hermitian

end
