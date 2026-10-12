module
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Rational.Box.Boundary
public import Purelib.Geometry.Rational.Box.Subdivision

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational.Box

section
@[expose] public section

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

namespace Purelib.Geometry.Rational.Box.Square.Symmetric.Norm

/-- Boundary norm bounds for an arbitrary positive symmetric rational square. -/
theorem symmetric_boundary_norm_bounds
    {radius : Fraction.Rational} (radiusNonnegative : 0 ≤ radius) {z : Data.Gaussian.Basic.Canonical}
    (boundary : Boundary.OnBoxBoundary
      (Rational.Box.symmetric radius radiusNonnegative) z) :
    radius ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq z ∧ Data.Gaussian.Norm.Basic.normSq z ≤ 2 * radius ^
      2 := by
  rcases boundary with ⟨inside, side⟩
  change -radius ≤ z.re ∧ z.re ≤ radius ∧
      -radius ≤ z.im ∧ z.im ≤ radius at inside
  change z.re = -radius ∨ z.re = radius ∨
      z.im = -radius ∨ z.im = radius at side
  have realSquare := Bounds.Square.symmetric_coordinate_sq_bound inside.1 inside.2.1
  have imaginarySquare :=
    Bounds.Square.symmetric_coordinate_sq_bound inside.2.2.1 inside.2.2.2
  have upper : Data.Gaussian.Norm.Basic.normSq z ≤ 2 * radius ^ 2 := by
    change z.re ^ 2 + z.im ^ 2 ≤ _
    exact (add_le_add realSquare imaginarySquare).trans_eq (by ring1)
  refine ⟨?_, upper⟩
  rcases side with onLeft | onRight | onBottom | onTop
  · change radius ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onLeft]
    calc
      radius ^ 2 = (-radius) ^ 2 + 0 := by ring1
      _ ≤ (-radius) ^ 2 + z.im ^ 2 :=
        add_le_add le_rfl (Fraction.Order.Arithmetic.sq_nonneg_direct z.im)
  · change radius ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onRight]
    exact le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct z.im)
  · change radius ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onBottom]
    calc
      radius ^ 2 = 0 + (-radius) ^ 2 := by ring1
      _ ≤ z.re ^ 2 + (-radius) ^ 2 :=
        add_le_add (Fraction.Order.Arithmetic.sq_nonneg_direct z.re) le_rfl
  · change radius ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onTop]
    exact le_add_of_nonneg_left
      (Fraction.Order.Arithmetic.sq_nonneg_direct z.re)
end Purelib.Geometry.Rational.Box.Square.Symmetric.Norm

end
