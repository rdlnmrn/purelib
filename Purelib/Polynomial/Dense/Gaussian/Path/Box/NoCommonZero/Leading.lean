module
import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
public import Purelib.Polynomial.Dense.Gaussian.Coefficients.LeadingSplit
public import Purelib.Polynomial.Dense.Gaussian.Path.Box.NoCommonZero
import Purelib.Polynomial.Dense.Gaussian.Path.Box.NoCommonZero.Constant
import Purelib.Polynomial.Dense.Gaussian.Path.Box.NoCommonZero.Coordinate

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Subdivision

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Path.Box.NoCommonZero.Leading

/-- The leading monomial has coprime coordinate paths on the coefficient-computed large square.

Positive polynomial degree supplies a nonzero leading coefficient and a positive coordinate power on the boundary. -/
theorem
  leadingMonomial_largeSquare_boundaryCoprime
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 <
      p.natDegree) :
    Dense.Gaussian.Path.Box.NoCommonZero.BoundaryCoprime (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) := by
  have polynomialNonzero := Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos degreePositive
  have leadingNonzero := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero polynomialNonzero
  exact (Dense.Gaussian.Path.Box.NoCommonZero.Constant.gaussianConstant_boundaryCoprime leadingNonzero
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p)).mul
    (by
      simpa only [Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox] using
        Dense.Gaussian.Path.Box.NoCommonZero.Coordinate.coordinatePositivePower_symmetric_boundaryCoprime
          (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p) (p.natDegree - 1))
end Purelib.Polynomial.Dense.Gaussian.Path.Box.NoCommonZero.Leading

end
