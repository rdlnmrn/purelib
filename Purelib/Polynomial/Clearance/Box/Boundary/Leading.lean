module
public import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Constant
public import Purelib.Polynomial.Clearance.Box.Boundary.Coordinate
import Purelib.Polynomial.Clearance.Box.Boundary.Operations
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
public import Purelib.Polynomial.Dense.Gaussian.Coefficients.LeadingSplit

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate

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

namespace Purelib.Polynomial.Clearance.Box.Boundary.Leading

/-- The displayed leading coefficient clearance and the radial power
clearance multiply to a quantitative boundary certificate for the leading
monomial. -/
def leadingMonomial_largeSquare_boundaryClearance
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 <
      p.natDegree) :
    Clearance.Box.Boundary.Basic.BoundaryClearance
      (Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p) (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
        p) := by
  have polynomialNonzero := Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos degreePositive
  have leadingNonzero := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero polynomialNonzero
  exact Clearance.Box.Boundary.Basic.BoundaryClearance.mul
    (Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance leadingNonzero
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p))
    (by
      simpa only [Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox] using
        Clearance.Box.Boundary.Coordinate.coordinatePositivePower_symmetric_boundaryClearance
          (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p) (p.natDegree - 1))
end Purelib.Polynomial.Clearance.Box.Boundary.Leading

end
