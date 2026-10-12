module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Rational.Box.Boundary
public import Purelib.Geometry.Rational.Box.Subdivision
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
  Geometry.Rational.Box.symmetric (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p)
    (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).le

/-- The positive computed large-square radius gives a proper box.

The computed radius is strictly positive. Strict negation and transitivity
therefore separate the lower and upper endpoint on each coordinate. -/
public theorem largeSquareBox_proper (p : Basic.CanonicalCoefficients.CoefficientPolynomial) :
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p).Proper := by
  have positive := Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p
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
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) z) :
    Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq z ∧
      Data.Gaussian.Norm.Basic.normSq z ≤ 2 * Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2 := open
        Purelib.Data.Rat in by
  rcases boundary with ⟨inside, side⟩
  change -Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ z.re ∧
      z.re ≤ Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ∧
      -Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ z.im ∧
      z.im ≤ Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p at inside
  change z.re = -Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ∨
      z.re = Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ∨
      z.im = -Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ∨
      z.im = Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p at side
  have realSquare := Data.Rat.Bounds.Square.symmetric_coordinate_sq_bound inside.1 inside.2.1
  have imaginarySquare :=
    Data.Rat.Bounds.Square.symmetric_coordinate_sq_bound inside.2.2.1 inside.2.2.2
  have upper : Data.Gaussian.Norm.Basic.normSq z ≤ 2 * Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2
    := by
    change z.re ^ 2 + z.im ^ 2 ≤ _
    exact (add_le_add realSquare imaginarySquare).trans_eq (by ring1)
  refine ⟨?_, upper⟩
  rcases side with onLeft | onRight | onBottom | onTop
  · change Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onLeft]
    calc
      Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2 =
          (-Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p) ^ 2 + 0 := by ring1
      _ ≤ (-Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p) ^ 2 + z.im ^ 2 :=
        add_le_add (le_refl _)
          (Fraction.Order.Arithmetic.sq_nonneg_direct z.im)
  · change Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onRight]
    exact le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct z.im)
  · change Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onBottom]
    calc
      Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2 =
          0 + (-Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p) ^ 2 := by ring1
      _ ≤ z.re ^ 2 + (-Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p) ^ 2 :=
        add_le_add
          (Fraction.Order.Arithmetic.sq_nonneg_direct z.re) (le_refl _)
  · change Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onTop]
    exact le_add_of_nonneg_left
      (Fraction.Order.Arithmetic.sq_nonneg_direct z.re)

end Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
