module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Gaussian.Cast.Imaginary
public import Purelib.Data.Gaussian.Constants
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Data.Gaussian.Cast
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

@[expose] public section

namespace Purelib.Polynomial.Dense.Gaussian.Path.Axis

/-- The rational real component of polynomial evaluation along a vertical affine line.

The fixed coordinate is retained as the line origin; the parameter runs along its coordinate direction. -/
def verticalPathReal (p :
  CoefficientPolynomial) (x :
  Fraction.Rational) : (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.Gaussian.Path.Components.pathReal p (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit

/-- The rational imaginary component of polynomial evaluation along a vertical affine line.

The fixed coordinate is retained as the line origin; the parameter runs along its coordinate direction. -/
def verticalPathImag (p :
  CoefficientPolynomial) (x :
  Fraction.Rational) : (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.Gaussian.Path.Components.pathImag p (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit

/-- The rational real component of polynomial evaluation along a horizontal affine line.

The fixed coordinate is retained as the line origin; the parameter runs along its coordinate direction. -/
def horizontalPathReal (p :
  CoefficientPolynomial) (y :
  Fraction.Rational) : (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.Gaussian.Path.Components.pathReal p (Gaussian.Cast.Imaginary.horizontalBase y)
    Gaussian.Constants.horizontalDirection

/-- The rational imaginary component of polynomial evaluation along a horizontal affine line.

The fixed coordinate is retained as the line origin; the parameter runs along its coordinate direction. -/
def horizontalPathImag (p :
  CoefficientPolynomial) (y :
  Fraction.Rational) : (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.Gaussian.Path.Components.pathImag p (Gaussian.Cast.Imaginary.horizontalBase y)
    Gaussian.Constants.horizontalDirection
end Purelib.Polynomial.Dense.Gaussian.Path.Axis

end
