module

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Triangles.Right.Quadrance
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.RationalBounds
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Plane.Line.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.Geometry.Trigonometry

open Purelib.Geometry.Trigonometry.QuadTriple

section
@[expose] public section

/-!
# Divine Proportions, Exercise 5.13

The source's maximum claim is stated without a supremum or completed real
object.  For every requested third quadrance, quadrea is bounded above by
`4 Q₁ Q₂`; equality holds exactly at the Pythagorean value.  The geometric
form then identifies equality with perpendicularity at the third vertex.
-/

section

namespace Purelib.Geometry.Triangles.Quadrea.RationalBounds.ExerciseFiveThirteen

/-- Exercise 5.13 in its geometric form. The pointwise upper bound is the constructive meaning of “maximum possible”,
and its equality case is exactly a right vertex at `third`. -/
theorem exercise_5_13
    (first second third : Geometry.Plane.Point Fraction.Rational)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third) :
    Quadrea.Basic.quadrea first second third ≤
        4 * Quadrance.quadrance second third * Quadrance.quadrance first third ∧
      (Quadrea.Basic.quadrea first second third =
          4 * Quadrance.quadrance second third * Quadrance.quadrance first third ↔
        (Incidence.lineThrough first third firstThirdDistinct).Perpendicular
          (Incidence.lineThrough second third secondThirdDistinct)) := by
  have scalarResult := RationalBounds.ExerciseFiveThirteen.exercise_5_13_scalar
    (Quadrance.quadrance second third)
    (Quadrance.quadrance first third)
    (Quadrance.quadrance first second)
  constructor
  · exact scalarResult.1
  · change
      QuadTriple.Basic.archimedesFunction
          (Quadrance.quadrance second third)
          (Quadrance.quadrance first third)
          (Quadrance.quadrance first second) =
          4 * Quadrance.quadrance second third * Quadrance.quadrance first third ↔ _
    exact scalarResult.2.trans (Right.Quadrance.pythagoras_iff_perpendicular first second third
      firstThirdDistinct secondThirdDistinct
        (by decide : (2 : Fraction.Rational) ≠ 0))

end Purelib.Geometry.Triangles.Quadrea.RationalBounds.ExerciseFiveThirteen

end

end
