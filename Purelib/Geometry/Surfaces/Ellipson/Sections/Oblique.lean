module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Coordinates.Polar.Squared
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry.Coordinates.Polar

open Purelib.Geometry.Coordinates.Polar.Squared

section
public section

/-!
# Divine Proportions, Appendix B: the ellipson

This module formalizes every finite algebraic assertion in Appendix B: the
defining surface, its full coordinate symmetry, its tetrahedral intersection
with the algebraic boundary of the unit cube, the coordinate-plane ellipse
sections and their four tangencies, the oblique section, and its rational
polar equation.  The volume calculation in Exercise B.1 is an analytic
integral and remains outside the agreed finite boundary.
-/

namespace Purelib.Geometry

namespace Surfaces.Ellipson.Sections.Oblique

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The source's suitable-coordinate oblique equation, multiplied by six to remove its sole scalar denominator. -/
@[expose] def ObliqueCoordinateCurve (root a b : K)
  : Prop :=
  6 * root * a * (3 * b ^ 2 - a ^ 2) -
      36 * (a ^ 2 + b ^ 2) + 5 = 0

/-- The oblique curve has the source's rational polar equation, with `root²=6` supplied as a finite witness and all
denominators cleared. -/
theorem oblique_rational_polar_cleared
    (root a b spread Q : K)
    (rootSquare : root ^ 2 = 6)
    (coordinates : RationalSphericalCoordinates.PolarCoordinateSquares
      (a ^ 2) (b ^ 2) spread Q)
    (onCurve : ObliqueCoordinateCurve root a b) :
    (6 * Q) ^ 3 * (spread * (3 - 4 * spread) ^ 2) =
      (36 * Q - 5) ^ 2 := by
  have squareCoordinates :=
    Squared.polar_coordinate_squares
      (a ^ 2) (b ^ 2) spread Q coordinates
  have linearEquation :
      6 * root * a * ((3 - 4 * spread) * Q) = 36 * Q - 5 := by
    apply Group.eq_of_sub_eq_zero
    calc
      6 * root * a * ((3 - 4 * spread) * Q) - (36 * Q - 5) =
        6 * root * a * (3 * b ^ 2 - a ^ 2) -
          36 * (a ^ 2 + b ^ 2) + 5 := by
        rw [squareCoordinates.1, squareCoordinates.2, coordinates.1]
        ring1
      _ = 0 := onCurve
  calc
    (6 * Q) ^ 3 * (spread * (3 - 4 * spread) ^ 2) =
        36 * 6 * (spread * Q) * Q ^ 2 * (3 - 4 * spread) ^ 2 := by
      ring1
    _ = 36 * root ^ 2 * a ^ 2 * Q ^ 2 *
          (3 - 4 * spread) ^ 2 := by
      rw [rootSquare, coordinates.2]
    _ = (6 * root * a * ((3 - 4 * spread) * Q)) ^ 2 := by ring1
    _ = (36 * Q - 5) ^ 2 := by rw [linearEquation]
end Surfaces.Ellipson.Sections.Oblique
end Purelib.Geometry

end

end
