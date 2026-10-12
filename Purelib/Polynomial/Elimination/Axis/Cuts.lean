module
public import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Central
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)

open Purelib.Data.Rat

open Purelib.Geometry.Rational

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

namespace Purelib.Polynomial.Elimination.Axis.Cuts

/-- Find a clear vertical cut inside a proper box.

The finite central scan uses the retained nonzero vertical eliminant and its degree bound. -/
def verticalSafeCoordinate {p :
  CoefficientPolynomial}
  {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) (box :
      Box)
    (proper : box.Proper) : Fraction.Rational :=
  Dense.Rational.Nonzero.Search.Central.centralSearchValue elimination.vertical degreeBound proper.1
    elimination.vertical_nonzero elimination.vertical_degree

/-- Find a clear horizontal cut inside a proper box.

The finite central scan uses the retained nonzero horizontal eliminant and its degree bound. -/
def horizontalSafeCoordinate {p :
  CoefficientPolynomial}
  {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) (box :
      Box)
    (proper : box.Proper) : Fraction.Rational :=
  Dense.Rational.Nonzero.Search.Central.centralSearchValue elimination.horizontal degreeBound proper.2
    elimination.horizontal_nonzero elimination.horizontal_degree

/-- The vertical cut is strictly internal and its eliminant value is nonzero. -/
theorem verticalSafeCoordinate_spec
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) (box :
      Box)
    (proper : box.Proper) :
    elimination.vertical.eval
        (verticalSafeCoordinate elimination box proper) ≠ 0 ∧
      box.xLower < verticalSafeCoordinate elimination box proper ∧
      verticalSafeCoordinate elimination box proper < box.xUpper :=
  Dense.Rational.Nonzero.Search.Central.centralSearchValue_spec elimination.vertical degreeBound proper.1
    elimination.vertical_nonzero elimination.vertical_degree

/-- The horizontal cut is strictly internal and its eliminant value is nonzero. -/
theorem horizontalSafeCoordinate_spec
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) (box :
      Box)
    (proper : box.Proper) :
    elimination.horizontal.eval
        (horizontalSafeCoordinate elimination box proper) ≠ 0 ∧
      box.yLower < horizontalSafeCoordinate elimination box proper ∧
      horizontalSafeCoordinate elimination box proper < box.yUpper :=
  Dense.Rational.Nonzero.Search.Central.centralSearchValue_spec elimination.horizontal degreeBound proper.2
    elimination.horizontal_nonzero elimination.horizontal_degree

/-- Both horizontal widths after the vertical cut are less than two thirds of the original width. -/
theorem verticalSafeCoordinate_contraction
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) (box :
      Box)
    (proper : box.Proper) :
    verticalSafeCoordinate elimination box proper - box.xLower <
        (2 / 3 : Fraction.Rational) * box.widthX ∧
      box.xUpper - verticalSafeCoordinate elimination box proper <
        (2 / 3 : Fraction.Rational) * box.widthX := by
  simpa only [verticalSafeCoordinate, Box.widthX] using
    Dense.Rational.Nonzero.Search.Central.centralSearchValue_contraction elimination.vertical degreeBound proper.1
    elimination.vertical_nonzero elimination.vertical_degree

/-- Both vertical widths after the horizontal cut are less than two thirds of the original width. -/
theorem horizontalSafeCoordinate_contraction
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) (box :
      Box)
    (proper : box.Proper) :
    horizontalSafeCoordinate elimination box proper - box.yLower <
        (2 / 3 : Fraction.Rational) * box.widthY ∧
      box.yUpper - horizontalSafeCoordinate elimination box proper <
        (2 / 3 : Fraction.Rational) * box.widthY := by
  simpa only [horizontalSafeCoordinate, Box.widthY] using
    Dense.Rational.Nonzero.Search.Central.centralSearchValue_contraction elimination.horizontal degreeBound proper.2
    elimination.horizontal_nonzero elimination.horizontal_degree
end Purelib.Polynomial.Elimination.Axis.Cuts

end
