module
public import Purelib.Geometry.Circles.Diameter.Basic
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Finite.Five
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.Ring.Defs

open Purelib.Algebra.Field

open Purelib

open Purelib.Geometry
open Purelib.Geometry.Plane

section
/-!
# Divine Proportions, Exercise 16.6: antipodal quadrance sums

The printed exercise omits a non-null hypothesis.  An executable `F₅`
counterexample below shows that the claim fails on a null circle.  For a
non-null circle, its displayed intersection makes every diameter non-null;
midpoint uniqueness then identifies the two equidistant diameter points as
antipodes, giving an explicit constant quadrance sum.
-/

@[expose] public section

namespace Purelib.Curves.Plane

variable {K : Type*} [ExplicitField K]

namespace Conic

/-- The printed Exercise 16.6 is false without the non-null premise.  Over
`F₅`, two distinct equidistant points on a null diameter give different sums
at two points of the same null circle. -/
theorem exercise_16_6_null_circle_counterexample :
    let center : Plane.Point Finite.Five.Element := ⟨0, 0⟩
    let first : Plane.Point Finite.Five.Element := ⟨1, 2⟩
    let second : Plane.Point Finite.Five.Element := ⟨2, 4⟩
    let left : Plane.Point Finite.Five.Element := center
    let right : Plane.Point Finite.Five.Element := ⟨1, 3⟩
    let circle := Curves.Plane.Conic.circleConic center 0
    let diameterLine : Plane.Line Finite.Five.Element :=
      { a := 2
        b := -1
        c := 0
        direction_nonzero := Or.inl (by decide) }
    circle.IsDiameter diameterLine center ∧
      first ≠ second ∧
      diameterLine.Contains first ∧ diameterLine.Contains second ∧
      Point.Quadrance.quadrance first center = Point.Quadrance.quadrance second center ∧
      circle.Contains left ∧ circle.Contains right ∧
      Point.Quadrance.quadrance first left + Point.Quadrance.quadrance second left ≠
      Point.Quadrance.quadrance first right + Point.Quadrance.quadrance second right := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ⟨⟨1, 2⟩, ?_⟩⟩
    · unfold Plane.Line.Contains
      decide
    · constructor
      · unfold Plane.Line.Contains
        decide
      · unfold Curves.Plane.Conic.Contains Curves.Plane.Conic.circleConic
          Curves.Plane.Conic.evaluate
        decide
  · decide
  · unfold Plane.Line.Contains
    decide
  · unfold Plane.Line.Contains
    decide
  · unfold Point.Quadrance.quadrance
    decide
  · unfold Curves.Plane.Conic.Contains Curves.Plane.Conic.circleConic
      Curves.Plane.Conic.evaluate
    decide
  · unfold Curves.Plane.Conic.Contains Curves.Plane.Conic.circleConic
      Curves.Plane.Conic.evaluate
    decide
  · unfold Point.Quadrance.quadrance
    decide

end Conic

end Purelib.Curves.Plane

end

end
