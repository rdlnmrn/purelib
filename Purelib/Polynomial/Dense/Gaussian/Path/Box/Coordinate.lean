module
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Gaussian.Components
public import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
public import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine.Coordinate
public import Purelib.Polynomial.Dense.Rational.Constants.RawLinear
public import Purelib.Polynomial.Dense.Rational.Monomial.Coordinate

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic

/-!
# Coordinate components on finite box edges

The coordinate polynomial is substituted on the original horizontal and vertical affine edges. Component projection
retains one monic coordinate table and one two-slot rational constant table.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Path.Box.Coordinate

open Purelib.Data.Rat

open Purelib.Polynomial

/-- The real component of the coordinate polynomial on a horizontal edge.

The exact dense coefficient representation is the coordinate; the edge endpoints do not affect this component
polynomial. -/
public theorem coordinate_horizontal_real (y a b : Fraction.Rational) :
    (Sides.horizontalEdge Monomial.Coordinate.coordinatePolynomial y a
      b).realPart =
      Rational.Monomial.Coordinate.coordinateVariable := open Purelib.Data in by
  change Components.realPart (Substitution.Affine.composeLine
    Monomial.Coordinate.coordinatePolynomial
      (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection) =
        Rational.Monomial.Coordinate.coordinateVariable
  rw [Substitution.Affine.Coordinate.composeLine_coordinate
    (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection (by
    intro equal
    have real := congrArg (fun z : Gaussian.Basic.Canonical => z.re) equal
    change (1 : Fraction.Rational) = 0 at real
    exact (Ne.symm Fraction.Field.zero_ne_one) real)]
  rfl

/-- The imag component of the coordinate polynomial on a horizontal edge.

The exact dense coefficient representation is the line height; the edge endpoints do not affect this component
polynomial. -/
public theorem coordinate_horizontal_imag (y a b : Fraction.Rational) :
    (Sides.horizontalEdge Monomial.Coordinate.coordinatePolynomial y a
      b).imagPart =
      Rational.Constants.RawLinear.rawConstant y := open Purelib.Data in by
  change Components.imagPart (Substitution.Affine.composeLine
    Monomial.Coordinate.coordinatePolynomial
      (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection) =
        Rational.Constants.RawLinear.rawConstant y
  rw [Substitution.Affine.Coordinate.composeLine_coordinate
    (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection (by
    intro equal
    have real := congrArg (fun z : Gaussian.Basic.Canonical => z.re) equal
    change (1 : Fraction.Rational) = 0 at real
    exact (Ne.symm Fraction.Field.zero_ne_one) real)]
  rfl

/-- The real component of the coordinate polynomial on a vertical edge.

The exact dense coefficient representation is the line position; the edge endpoints do not affect this component
polynomial. -/
public theorem coordinate_vertical_real (x a b : Fraction.Rational) :
    (Sides.verticalEdge Monomial.Coordinate.coordinatePolynomial x a b).realPart
      =
      Rational.Constants.RawLinear.rawConstant x := open Purelib.Data in by
  change Components.realPart (Substitution.Affine.composeLine
    Monomial.Coordinate.coordinatePolynomial
      (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit) =
        Rational.Constants.RawLinear.rawConstant x
  rw [Substitution.Affine.Coordinate.composeLine_coordinate
    (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit (by
    intro equal
    have imaginary := congrArg (fun z : Gaussian.Basic.Canonical => z.im) equal
    change (1 : Fraction.Rational) = 0 at imaginary
    exact (Ne.symm Fraction.Field.zero_ne_one) imaginary)]
  rfl

/-- The imag component of the coordinate polynomial on a vertical edge.

The exact dense coefficient representation is the coordinate; the edge endpoints do not affect this component
polynomial. -/
public theorem coordinate_vertical_imag (x a b : Fraction.Rational) :
    (Sides.verticalEdge Monomial.Coordinate.coordinatePolynomial x a b).imagPart
      =
      Rational.Monomial.Coordinate.coordinateVariable := open Purelib.Data in by
  change Components.imagPart (Substitution.Affine.composeLine
    Monomial.Coordinate.coordinatePolynomial
      (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit) =
        Rational.Monomial.Coordinate.coordinateVariable
  rw [Substitution.Affine.Coordinate.composeLine_coordinate
    (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit (by
    intro equal
    have imaginary := congrArg (fun z : Gaussian.Basic.Canonical => z.im) equal
    change (1 : Fraction.Rational) = 0 at imaginary
    exact (Ne.symm Fraction.Field.zero_ne_one) imaginary)]
  rfl

end Purelib.Polynomial.Dense.Gaussian.Path.Box.Coordinate
