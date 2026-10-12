module
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

namespace Purelib.Polynomial.Clearance.Box.Boundary.Basic.BoundaryClearance
section

/-- A clearance for the normalized finite coefficient list is also a
clearance for the original representation. -/
def ofNormalize
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (clearance : BoundaryClearance p.normalize box) :
    BoundaryClearance p box where
  bound := clearance.bound
  positive := clearance.positive
  lower := by
    intro z boundary
    simpa only [Dense.Basic.DensePolynomial.eval_normalize]
      using clearance.lower z boundary

/-- Quantitative boundary clearance is closed under polynomial
multiplication.  The displayed lower bound is the product of the two finite
lower bounds. -/
def mul
    {p q : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (left : BoundaryClearance p box)
    (right : BoundaryClearance q box) : BoundaryClearance (p *
      q) box where
  bound := left.bound * right.bound
  positive := Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_pos_direct
    left.positive right.positive
  lower := by
    intro z boundary
    rw [Dense.Basic.DensePolynomial.eval_mul, Gaussian.Basic.Canonical.normSq_mul]
    exact Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_direct
      (left.lower z boundary) (right.lower z boundary)
      right.positive.le
      (Gaussian.Basic.Canonical.normSq_nonneg (p.eval z))

end

end Purelib.Polynomial.Clearance.Box.Boundary.Basic.BoundaryClearance

end
