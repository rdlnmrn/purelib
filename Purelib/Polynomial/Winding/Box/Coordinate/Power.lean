module

import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Clearance.Box.Boundary.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
public import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Coordinate
import Purelib.Polynomial.Winding.Box.Product
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Algebra.Group.Negation

open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-!
# Winding of positive coordinate powers

Finite multiplication of the original coordinate polynomial determines
its raw winding on a positive symmetric rational square.
-/

namespace Purelib.Polynomial.Winding.Box.Coordinate.Power

/-- Raw winding of the positive coordinate powers follows by the audited
closed-box product theorem.

The radius is strictly positive. Each retained coordinate-power factor
has the same proper symmetric square, and finite multiplication gives
four times the displayed positive exponent. -/
public theorem quadrupledBoxWinding_coordinatePositivePower
    {R : Fraction.Rational} (positive : 0 < R) (n : Nat) :
    Winding.Box.Basic.quadrupledBoxWinding (Dense.Gaussian.Power.Coordinate.coordinatePositivePower n)
        (Box.symmetric R positive.le) =
      (4 : Int) * (n + 1) := by
  induction n with
  | zero =>
      change Winding.Box.Basic.quadrupledBoxWinding Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
          (Box.symmetric R positive.le) = 4
      exact (Winding.Box.Coordinate.coordinate_symmetric_normalization positive).1
  | succ n inductionHypothesis =>
      let box := Box.symmetric R positive.le
      have proper : box.Proper := by
        have reflected := Fraction.Order.Arithmetic.neg_lt_neg_direct positive
        have zeroNegation : -(0 : Fraction.Rational) = 0 := by ring1
        rewrite [zeroNegation] at reflected
        exact ⟨reflected.trans positive, reflected.trans positive⟩
      have product :=
        Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
          (Dense.Gaussian.Power.Coordinate.coordinatePositivePower n)
            Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial box proper
          (Clearance.Box.Boundary.Coordinate.coordinatePositivePower_symmetric_boundaryClearance positive n)
          (Clearance.Box.Boundary.Coordinate.coordinate_symmetric_boundaryClearance positive)
      have coordinateWinding := (Winding.Box.Coordinate.coordinate_symmetric_normalization positive).1
      change Winding.Box.Basic.quadrupledBoxWinding
          (Dense.Gaussian.Power.Coordinate.coordinatePositivePower n *
            Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial) box =
        (4 : Int) * (n + 2)
      rw [product, inductionHypothesis, coordinateWinding]
      ring1

end Purelib.Polynomial.Winding.Box.Coordinate.Power
