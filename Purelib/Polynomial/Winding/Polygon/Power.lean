module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
public import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
import Purelib.Polynomial.Winding.Polygon.Basic
public import Purelib.Polynomial.Winding.Polygon.Product
import Purelib.Tactic.Ring
import Purelib.Algebra.NatCast

/-!
# Positive coordinate powers on closed polygonal chains

The indexed finite certificate retains each coordinate multiplication's product
identity on the same closed vertex list. Induction on that certificate scales
the retained raw winding by the displayed positive integer power.
-/

namespace Purelib.Polynomial.Winding.Polygon.Power

open Purelib
open Purelib.Data
open Purelib.Polynomial

/-! ## Positive coordinate powers -/

/-- The finite product data needed to build the positive coordinate power
on every edge of one closed polygon.

Its successor retains the previous exponent certificate and the next multiplication identity for the same closed vertex
list. -/
public inductive ClosedPositivePowerFormula (base : Gaussian.Basic.Canonical)
    (vertices : List Gaussian.Basic.Canonical) : Nat → Prop
  /-- The first positive power is the coordinate polynomial itself. -/ | zero :
    Purelib.Polynomial.Winding.Polygon.Power.ClosedPositivePowerFormula base vertices 0
  /-- Retain the previous power certificate and the next multiplication's closed-chain product formula. -/ | succ
    {exponent : Nat}
      (previous : Purelib.Polynomial.Winding.Polygon.Power.ClosedPositivePowerFormula base vertices exponent)
      (product : Winding.Polygon.Product.ClosedProductFormula
        (Dense.Gaussian.Power.Coordinate.coordinatePositivePower exponent)
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial base vertices) :
      Purelib.Polynomial.Winding.Polygon.Power.ClosedPositivePowerFormula base vertices (exponent + 1)

/-- Raising every vertex path value to the displayed positive power
multiplies the raw closed-walk winding by that power.

The product identities telescope on the same closed chain. Induction on the retained exponent certificate identifies the
exact natural cast multiplying its coordinate winding. -/
public theorem closedRaw_coordinatePositivePower
    (base : Gaussian.Basic.Canonical) (vertices : List Gaussian.Basic.Canonical) :
    ∀ (exponent : Nat), Winding.Polygon.Power.ClosedPositivePowerFormula base vertices exponent →
      Winding.Polygon.Basic.closedRaw
          (Dense.Gaussian.Power.Coordinate.coordinatePositivePower exponent)
          base vertices =
        ((exponent + 1 : Nat) : Int) *
          Winding.Polygon.Basic.closedRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial base vertices := by
  intro exponent formula
  induction formula with
  | zero =>
      change Winding.Polygon.Basic.closedRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
          base vertices = (1 : Int) *
            Winding.Polygon.Basic.closedRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial base vertices
      ring1
  | @succ exponent previous product inductionHypothesis =>
      have productWinding := Winding.Polygon.Product.closedRaw_mul_of_formula
        (Dense.Gaussian.Power.Coordinate.coordinatePositivePower exponent)
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial base vertices product
      change Winding.Polygon.Basic.closedRaw
          (Dense.Gaussian.Power.Coordinate.coordinatePositivePower exponent *
            Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial) base vertices =
        (((exponent + 1 + 1 : Nat) : Int) *
          Winding.Polygon.Basic.closedRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial base vertices)
      rw [productWinding, inductionHypothesis]
      simp only [Algebra.NatCast.add, Nat.cast_one]
      ring1

end Purelib.Polynomial.Winding.Polygon.Power
