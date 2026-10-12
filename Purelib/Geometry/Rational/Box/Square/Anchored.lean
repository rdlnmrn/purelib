module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Dimensions
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

section
@[expose] public section

/-!
# Winding bands from displayed rational residuals

A sufficiently small value of a squarefree polynomial at a displayed
Gaussian-rational sample gives a finite Newton certificate.  When supplied
with explicit rational displacement, Taylor, and containment budgets, the
selected eliminant-safe band has winding four and therefore starts a normal
shrinking track.

Nothing in this module turns a small residual, a winding count, or a Sturm
count into a root.  The only distinguished point is the supplied rational
anchor of `source`.
-/

namespace Purelib.Geometry.Rational.Box.Square.Anchored

/-- Positive square extending up and right from one displayed rational sample. Its fixed box anchor is definitionally
that sample. -/
def anchoredSquare (point : Data.Gaussian.Basic.Canonical) (radius
  : Fraction.Rational)
    (nonnegative : 0 ≤ radius) : Rational.Box where
  xLower := point.re
  xUpper := point.re + radius
  yLower := point.im
  yUpper := point.im + radius
  x_valid := le_add_of_nonneg_right nonnegative
  y_valid := le_add_of_nonneg_right nonnegative

/-- The anchor of the upward-right square is its supplied base point. -/
@[simp] theorem anchoredSquare_anchor
    (point : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) (nonnegative : 0 ≤ radius) :
    (anchoredSquare point radius nonnegative).anchor = point := by
  apply Data.Gaussian.Basic.ext <;> rfl

/-- A positive anchored-square radius gives positive width and height. -/
theorem anchoredSquare_proper
    (point : Data.Gaussian.Basic.Canonical) {radius : Fraction.Rational} (positive : 0 < radius) :
    (anchoredSquare point radius positive.le).Proper := by
  constructor
  · calc
      point.re = 0 + point.re := by ring1
      _ < radius + point.re :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct positive point.re
      _ = point.re + radius := by ring1
  · calc
      point.im = 0 + point.im := by ring1
      _ < radius + point.im :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct positive point.im
      _ = point.im + radius := by ring1

/-- The anchored square has squared diagonal twice the squared radius. -/
@[simp] theorem anchoredSquare_diagonalSq
    (point : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) (nonnegative : 0 ≤ radius) :
    (anchoredSquare point radius nonnegative).diagonalSq = 2 * radius ^ 2 := by
  dsimp only [anchoredSquare, Rational.Box.diagonalSq,
    Rational.Box.widthX, Rational.Box.widthY]
  ring1

end Purelib.Geometry.Rational.Box.Square.Anchored

end
