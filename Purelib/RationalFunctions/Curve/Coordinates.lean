module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
public import Purelib.Polynomial.Dense.Gaussian.Components
public import Purelib.Polynomial.Dense.Multiplication
public import Purelib.RationalFunctions.Curve.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

section
@[expose] public section

/-!
# Finite box conditions along a rational curve

A rational curve is stored homogeneously as `N(t) / D(t)`.  On every
displayed parameter where `D(t)` is nonzero, membership of the affine point
in a rational box is equivalent to four nonnegative univariate polynomial
evaluations.  The common positive factor is the explicitly displayed
quadrance `normSq (D(t))`, so no denominator sign choice or square root is
needed.

The nonzero members of the four-polynomial family are also collected into a
single finite product guard.  A later common Sturm subdivision can therefore
cut once while preserving all box-edge signs; identically-zero edge
conditions remain explicit instead of making the guard vanish.
-/

namespace Purelib.RationalFunctions.Curve.Coordinates

section
open Purelib.Data
section
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- Extract the rational real-coordinate polynomial of the curve numerator. -/
def numeratorReal (curve : Curve.RationalCurve) :
  (DensePolynomial Rational) :=
  Dense.Gaussian.Components.realPart curve.numerator

/-- Extract the rational imaginary-coordinate polynomial of the curve numerator. -/
def numeratorImaginary (curve : Curve.RationalCurve) :
  (DensePolynomial Rational) :=
  Dense.Gaussian.Components.imagPart curve.numerator

/-- Extract the rational real-coordinate polynomial of the curve denominator. -/
def denominatorReal (curve : Curve.RationalCurve) :
  (DensePolynomial Rational) :=
  Dense.Gaussian.Components.realPart curve.denominator

/-- Extract the rational imaginary-coordinate polynomial of the curve denominator. -/
def denominatorImaginary (curve : Curve.RationalCurve) :
  (DensePolynomial Rational) :=
  Dense.Gaussian.Components.imagPart curve.denominator

/-- Form the sum of squares of the two denominator coordinate polynomials. -/
def denominatorNormSq (curve : Curve.RationalCurve) :
  (DensePolynomial Rational) :=
  denominatorReal curve * denominatorReal curve +
    denominatorImaginary curve * denominatorImaginary curve

/-- Form the real coordinate polynomial of the numerator times the conjugate denominator. -/
def affineRealNumerator (curve : Curve.RationalCurve) :
  (DensePolynomial Rational) :=
  numeratorReal curve * denominatorReal curve +
    numeratorImaginary curve * denominatorImaginary curve

/-- Form the imaginary coordinate polynomial of the numerator times the conjugate denominator. -/
def affineImaginaryNumerator (curve : Curve.RationalCurve) :
  (DensePolynomial Rational) :=
  numeratorImaginary curve * denominatorReal curve -
    numeratorReal curve * denominatorImaginary curve

/-- The denominator quadrance polynomial evaluates to the quadrance of the denominator value. -/
@[simp] theorem eval_denominatorNormSq
    (curve : Curve.RationalCurve) (parameter : Rational) :
    (denominatorNormSq curve).eval parameter =
      Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter) := by
  simp only [denominatorNormSq, denominatorReal,
    denominatorImaginary,
    DensePolynomial.eval_add, DensePolynomial.eval_mul, Dense.Gaussian.Components.eval_realPart,
    Dense.Gaussian.Components.eval_imagPart,
    Curve.RationalCurve.denominatorAt, Gaussian.Norm.Basic.normSq]
  ring1

/-- The real numerator polynomial evaluates to the real part of numerator times conjugate denominator. -/
@[simp] theorem eval_affineRealNumerator
    (curve : Curve.RationalCurve) (parameter : Rational) :
    (affineRealNumerator curve).eval parameter =
      (curve.numeratorAt parameter *
        Gaussian.Basic.conj
          (curve.denominatorAt parameter)).re := by
  simp only [affineRealNumerator, numeratorReal,
    numeratorImaginary,
    denominatorReal, denominatorImaginary, DensePolynomial.eval_add,
      DensePolynomial.eval_mul,
    Dense.Gaussian.Components.eval_realPart,
    Dense.Gaussian.Components.eval_imagPart,
    Curve.RationalCurve.numeratorAt,
    Curve.RationalCurve.denominatorAt,
    Gaussian.Basic.mul_re,
    Gaussian.Basic.conj]
  ring1

/-- The imaginary numerator polynomial evaluates to the imaginary part of numerator times conjugate denominator. -/
@[simp] theorem eval_affineImaginaryNumerator
    (curve : Curve.RationalCurve) (parameter : Rational) :
    (affineImaginaryNumerator curve).eval parameter =
      (curve.numeratorAt parameter *
        Gaussian.Basic.conj
          (curve.denominatorAt parameter)).im := by
  simp only [affineImaginaryNumerator, numeratorReal,
    numeratorImaginary,
    denominatorReal, denominatorImaginary, DensePolynomial.eval_sub,
      DensePolynomial.eval_mul,
    Dense.Gaussian.Components.eval_realPart,
    Dense.Gaussian.Components.eval_imagPart,
    Curve.RationalCurve.numeratorAt,
    Curve.RationalCurve.denominatorAt,
    Gaussian.Basic.mul_im,
    Gaussian.Basic.conj]
  ring1

end

open Purelib.RationalFunctions
/-- At a nonzero denominator, the real numerator polynomial equals the affine real coordinate times denominator
quadrance. -/
theorem eval_affineRealNumerator_eq_point_mul_normSq
    (curve : Curve.RationalCurve) (parameter : Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (affineRealNumerator curve).eval parameter =
      (curve.point parameter).re * Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter) := by
  have numeratorIdentity :=
    curve.numeratorAt_eq_point_mul_denominatorAt parameter denominatorNonzero
  have realIdentity :=
    congrArg Canonical.re numeratorIdentity
  have imaginaryIdentity :=
    congrArg Canonical.im numeratorIdentity
  rw [eval_affineRealNumerator]
  simp only [Gaussian.Basic.mul_re,
    Gaussian.Basic.mul_im,
    Gaussian.Basic.conj] at realIdentity imaginaryIdentity ⊢
  rw [realIdentity, imaginaryIdentity]
  simp only [Gaussian.Norm.Basic.normSq]
  ring1

/-- At a nonzero denominator, the imaginary numerator polynomial equals the affine imaginary coordinate times
denominator quadrance. -/
theorem eval_affineImaginaryNumerator_eq_point_mul_normSq
    (curve : Curve.RationalCurve) (parameter : Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (affineImaginaryNumerator curve).eval parameter =
      (curve.point parameter).im * Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter) := by
  have numeratorIdentity :=
    curve.numeratorAt_eq_point_mul_denominatorAt parameter denominatorNonzero
  have realIdentity :=
    congrArg Canonical.re numeratorIdentity
  have imaginaryIdentity :=
    congrArg Canonical.im numeratorIdentity
  rw [eval_affineImaginaryNumerator]
  simp only [Gaussian.Basic.mul_re,
    Gaussian.Basic.mul_im,
    Gaussian.Basic.conj] at realIdentity imaginaryIdentity ⊢
  rw [realIdentity, imaginaryIdentity]
  simp only [Gaussian.Norm.Basic.normSq]
  ring1
end

end Purelib.RationalFunctions.Curve.Coordinates

end

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

namespace Purelib.RationalFunctions.Curve.Coordinates

open Purelib.Data
open Purelib.Polynomial
open Purelib.RationalFunctions
/-- Form the sum of squares of the two numerator coordinate polynomials. -/
def numeratorNormSq (curve : Curve.RationalCurve) :
  (DensePolynomial Rational) :=
  numeratorReal curve *
      numeratorReal curve +
    numeratorImaginary curve *
      numeratorImaginary curve

/-- The numerator quadrance polynomial evaluates to the quadrance of the numerator value. -/
@[simp] theorem eval_numeratorNormSq
    (curve : Curve.RationalCurve) (parameter : Rational) :
    (numeratorNormSq curve).eval parameter =
      Gaussian.Norm.Basic.normSq (curve.numeratorAt parameter) := by
  simp only [numeratorNormSq,
    numeratorReal,
    numeratorImaginary,
    DensePolynomial.eval_add, DensePolynomial.eval_mul,
    Dense.Gaussian.Components.eval_realPart,
    Dense.Gaussian.Components.eval_imagPart,
    Curve.RationalCurve.numeratorAt, Gaussian.Norm.Basic.normSq]
  ring1
end Purelib.RationalFunctions.Curve.Coordinates

end
