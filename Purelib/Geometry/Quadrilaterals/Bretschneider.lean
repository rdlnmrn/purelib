module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Determinant
public import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Polygons.SignedArea.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Polygons

/-!
# Divine Proportions, Chapter 9: finite oriented areas

An oriented polygon is represented by a finite `List` of points.  The
denominator-free primitive is twice its signed area; the book's signed area is
obtained by dividing that finite sum by two.  This keeps the cancellation and
characteristic assumptions visible while the core shoelace and
Bretschneider identities remain polynomial.
-/

@[expose] public section

namespace Purelib.Geometry.Quadrilaterals.Bretschneider

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Bretschneider's polynomial identity for the quadrea of four ordered points.

The diagonal quadrances and the alternating sum of side quadrances determine the squared signed area, without division
or nondegeneracy assumptions. -/
theorem bretschneider_formula
    (first second third fourth : Plane.Point K) :
    SignedArea.Basic.polygonQuadrea [first, second, third, fourth] =
      4 * Quadrance.quadrance first third * Quadrance.quadrance second fourth -
        (Quadrance.quadrance first second + Quadrance.quadrance third fourth -
          Quadrance.quadrance second third - Quadrance.quadrance first fourth) ^ 2 := by
  simp only [SignedArea.Basic.polygonQuadrea, SignedArea.Basic.polygonDoubleSignedArea,
    SignedArea.Basic.polygonDoubleSignedAreaAux, Determinant.positionDeterminant, Quadrance.quadrance]
  ring1

end Purelib.Geometry.Quadrilaterals.Bretschneider

end
