module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Operations
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
public import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

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

namespace Purelib.Polynomial.Clearance.Box.Boundary.Coordinate

/-- The coordinate itself has the explicit radial squared-norm clearance on
the boundary of a symmetric square. -/
def coordinate_symmetric_boundaryClearance
    {R : Fraction.Rational} (positive : 0 < R) :
    BoundaryClearance Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (Box.symmetric R positive.le) where
  bound := R ^ 2
  positive := by
    rw [pow_two]
    exact Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_pos_direct positive positive
  lower := by
    intro z boundary
    rw [Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval]
    rcases boundary with ⟨_inside, side⟩
    rcases side with left | right | bottom | top
    · change z.re = -R at left
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      change R ^ 2 ≤ z.re ^ 2 + z.im ^ 2
      rw [left]
      rw [show (-R) ^ 2 = R ^ 2 by ring1]
      exact le_add_of_nonneg_right
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.sq_nonneg_direct z.im)
    · change z.re = R at right
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      change R ^ 2 ≤ z.re ^ 2 + z.im ^ 2
      rw [right]
      exact le_add_of_nonneg_right
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.sq_nonneg_direct z.im)
    · change z.im = -R at bottom
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      change R ^ 2 ≤ z.re ^ 2 + z.im ^ 2
      rw [bottom]
      rw [show (-R) ^ 2 = R ^ 2 by ring1]
      exact le_add_of_nonneg_left
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.sq_nonneg_direct z.re)
    · change z.im = R at top
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      change R ^ 2 ≤ z.re ^ 2 + z.im ^ 2
      rw [top]
      exact le_add_of_nonneg_left
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.sq_nonneg_direct z.re)

/-- Every positive coordinate power carries an explicit product clearance on
a positive symmetric square. -/
def coordinatePositivePower_symmetric_boundaryClearance
    {R : Fraction.Rational} (positive : 0 < R) :
    ∀ n : Nat,
      BoundaryClearance
        (Dense.Gaussian.Power.Coordinate.coordinatePositivePower n)
        (Box.symmetric R positive.le)
  | 0 => coordinate_symmetric_boundaryClearance positive
  | n + 1 =>
      BoundaryClearance.mul
        (coordinatePositivePower_symmetric_boundaryClearance
          positive n)
        (coordinate_symmetric_boundaryClearance positive)
end Purelib.Polynomial.Clearance.Box.Boundary.Coordinate

end
