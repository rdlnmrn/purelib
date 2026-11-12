module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Rational.Box.Boundary
public import Purelib.Geometry.Rational.Box.Subdivision
public import Purelib.Geometry.Rational.Box.Enclosure
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Tactic.Ring
import Purelib.Algebra.Group.Negation

open Purelib.Data
open Purelib
open Purelib.Polynomial
open Purelib.Data.Rat

/-!
# Coefficient-computed rational square bounds

The retained dense coefficient radius determines the original symmetric box.
Its positivity and boundary coordinates give exact finite quadrance bounds.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box

/-- The symmetric rational box whose radius is the polynomial's computed large-square radius.

Its four endpoints are the opposite signs of the same coefficient-computed
radius. The supplied nonnegative radius is retained by the symmetric-box constructor. -/
@[expose] public def largeSquareBox (p : Basic.CanonicalCoefficients.CoefficientPolynomial) : Geometry.Rational.Box :=
  Geometry.Rational.Box.symmetric (denseLargeSquareRadius p)
    (denseLargeSquareRadius_pos p).le

/-- The positive computed large-square radius gives a proper box.

The computed radius is strictly positive. Strict negation and transitivity
therefore separate the lower and upper endpoint on each coordinate. -/
public theorem largeSquareBox_proper (p : Basic.CanonicalCoefficients.CoefficientPolynomial) :
    (largeSquareBox p).Proper := by
  have positive := denseLargeSquareRadius_pos p
  have reflected := Fraction.Order.Arithmetic.neg_lt_neg_direct positive
  have zeroNegation : -(0 : Fraction.Rational) = 0 := by ring1
  rewrite [zeroNegation] at reflected
  exact ⟨reflected.trans positive, reflected.trans positive⟩

/-- Boundary quadrance lies between the squared large-square radius and twice that square.

Each coordinate lies between the opposite radius bounds, and one boundary
coordinate attains an endpoint. These facts give the upper sum-of-squares
bound and the lower bound from that attained coordinate. -/
public theorem largeSquare_boundary_norm_bounds
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {z : Gaussian.Basic.Canonical}
    (boundary : Geometry.Rational.Box.Boundary.OnBoxBoundary
      (largeSquareBox p) z) :
    denseLargeSquareRadius p ^ 2 ≤ Gaussian.Norm.Basic.normSq z ∧
      Gaussian.Norm.Basic.normSq z ≤ 2 * denseLargeSquareRadius p ^ 2 := open
        Purelib.Data.Rat in by
  rcases boundary with ⟨inside, side⟩
  change -denseLargeSquareRadius p ≤ z.re ∧
      z.re ≤ denseLargeSquareRadius p ∧
      -denseLargeSquareRadius p ≤ z.im ∧
      z.im ≤ denseLargeSquareRadius p at inside
  change z.re = -denseLargeSquareRadius p ∨
      z.re = denseLargeSquareRadius p ∨
      z.im = -denseLargeSquareRadius p ∨
      z.im = denseLargeSquareRadius p at side
  have realSquare := Bounds.Square.symmetric_coordinate_sq_bound inside.1 inside.2.1
  have imaginarySquare :=
    Bounds.Square.symmetric_coordinate_sq_bound inside.2.2.1 inside.2.2.2
  have upper : Gaussian.Norm.Basic.normSq z ≤ 2 * denseLargeSquareRadius p ^ 2
    := by
    change z.re ^ 2 + z.im ^ 2 ≤ _
    exact (add_le_add realSquare imaginarySquare).trans_eq (by ring1)
  refine ⟨?_, upper⟩
  rcases side with onLeft | onRight | onBottom | onTop
  · change denseLargeSquareRadius p ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onLeft]
    calc
      denseLargeSquareRadius p ^ 2 =
          (-denseLargeSquareRadius p) ^ 2 + 0 := by ring1
      _ ≤ (-denseLargeSquareRadius p) ^ 2 + z.im ^ 2 :=
        add_le_add (le_refl _)
          (Fraction.Order.Arithmetic.sq_nonneg_direct z.im)
  · change denseLargeSquareRadius p ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onRight]
    exact le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct z.im)
  · change denseLargeSquareRadius p ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onBottom]
    calc
      denseLargeSquareRadius p ^ 2 =
          0 + (-denseLargeSquareRadius p) ^ 2 := by ring1
      _ ≤ z.re ^ 2 + (-denseLargeSquareRadius p) ^ 2 :=
        add_le_add
          (Fraction.Order.Arithmetic.sq_nonneg_direct z.re) (le_refl _)
  · change denseLargeSquareRadius p ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onTop]
    exact le_add_of_nonneg_left
      (Fraction.Order.Arithmetic.sq_nonneg_direct z.re)

/-- Compute a positive square radius from the original polynomial coefficients and finite input box endpoints. -/
@[expose] public def enclosingRadius (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (boxes : List Geometry.Rational.Box) : Fraction.Rational :=
  max (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p) (Geometry.Rational.Box.enclosureRadius boxes)

/-- The original coefficient-computed root radius lies below the same finite-input enclosing radius. -/
public theorem enclosingRadius_ge_coefficients (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (boxes : List Geometry.Rational.Box) :
    Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ enclosingRadius p boxes :=
  Fraction.Order.Basic.le_max_left _ _

/-- The original coefficient bound makes the finite-input enclosing radius strictly positive. -/
public theorem enclosingRadius_pos (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (boxes : List Geometry.Rational.Box) : 0 < enclosingRadius p boxes :=
  (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).trans_le
    (enclosingRadius_ge_coefficients p boxes)

/-- Retain one centered support square containing the original coefficient radius and every supplied input box. -/
@[expose] public def enclosingSquare (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (boxes : List Geometry.Rational.Box) : Geometry.Rational.Box :=
  Geometry.Rational.Box.symmetric (enclosingRadius p boxes) (enclosingRadius_pos p boxes).le

/-- Every retained original input box refines the same coefficient-derived common support square. -/
public theorem refines_enclosingSquare (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    {box : Geometry.Rational.Box} {boxes : List Geometry.Rational.Box} (member : box ∈ boxes) :
    box.Refines (enclosingSquare p boxes) :=
  box.refines_symmetric_of_enclosingRadius_le (enclosingRadius_pos p boxes).le
    ((Geometry.Rational.Box.enclosingRadius_le_of_mem member).trans (Fraction.Order.Basic.le_max_right _ _))

end Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
