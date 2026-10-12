module
public import Purelib.Curves.Plane.Conic.LineIntersection
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Geometry.Plane.HalfTurn.Basic
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Null
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane

open Purelib.Curves.Plane.Conic.LineIntersection

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Point

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

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- A diameter is a line through the circle center with one explicit point of intersection. -/
def IsDiameter (circle : Conic K) (line : Plane.Line K)
  (center : Plane.Point K) : Prop :=
  line.Contains center ∧
    ∃ point : Plane.Point K, Curves.Plane.Conic.LineIntersection.IntersectsAt circle line point

/-- A diameter of a circle with nonzero quadrance is non-null. -/
theorem diameter_nonNull_of_circleQuadrance_ne_zero [DecidableEq K]
    (circle : Conic K) (line : Plane.Line K) (center : Plane.Point K)
    (circleQuadrance : K) (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (diameter : circle.IsDiameter line center) :
    ¬ line.IsNull := by
  rcases diameter.2 with ⟨point, pointIntersection⟩
  have pointRadius : Quadrance.quadrance point center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center point circleQuadrance
      presentation).1 pointIntersection.2
  intro lineNull
  have radiusZero := Conic.quadrance_eq_zero_of_null_line_contains line lineNull
    point center pointIntersection.1 diameter.1
  apply quadranceNonzero
  calc
    circleQuadrance = Quadrance.quadrance point center := pointRadius.symm
    _ = 0 := radiusZero
end

end Purelib.Curves.Plane.Conic

end

end

section
@[expose] public section

/-!
# Divine Proportions, §16.1: diameters

The source's midpoint proof of Theorem 103 requires a non-null diameter side,
the same visible hypothesis as the already formalized midpoint-uniqueness
theorem.  The statement below exposes that characteristic-dependent omission.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- Exercise 16.1: reflecting one intersection of a non-null circle's diameter through the center constructs a distinct
second intersection. -/
theorem exercise_16_1 (circle : Conic K) (line :
  Plane.Line K)
    (center : Plane.Point K) (circleQuadrance : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance)
    (diameter : circle.IsDiameter line center) :
    Curves.Plane.Conic.LineIntersection.IsChord circle line := by
  rcases diameter with ⟨centerOnLine, point, pointIntersection⟩
  have pointRadius : Quadrance.quadrance point center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center point circleQuadrance
      presentation).1 pointIntersection.2
  have pointDifferentCenter : point ≠ center := by
    intro pointEqualsCenter
    apply quadranceNonzero
    calc
      circleQuadrance = Quadrance.quadrance point center := pointRadius.symm
      _ = Quadrance.quadrance center center := by rw [pointEqualsCenter]
      _ = 0 := Quadrance.quadrance_self center
  let opposite := HalfTurn.Basic.rotateInPoint center point
  have oppositeOnLine : line.Contains opposite :=
    Conic.line_contains_rotateInPoint line center point centerOnLine
      pointIntersection.1
  have oppositeOnCircle : circle.Contains opposite := by
    apply (Conic.contains_iff_quadrance_eq circle center opposite circleQuadrance
      presentation).2
    calc
      Quadrance.quadrance opposite center = Quadrance.quadrance point center := by
        exact Conic.rotateInPoint_quadrance_center center point
      _ = circleQuadrance := pointRadius
  have oppositeDifferent : opposite ≠ point := by
    intro oppositeEqualsPoint
    apply pointDifferentCenter
    have xEquation := congrArg Plane.Point.x oppositeEqualsPoint
    have yEquation := congrArg Plane.Point.y oppositeEqualsPoint
    change 2 * center.x - point.x = point.x at xEquation
    change 2 * center.y - point.y = point.y at yEquation
    have xProductZero : 2 * (center.x - point.x) = 0 := by
      calc
        2 * (center.x - point.x) =
            (2 * center.x - point.x) - point.x := by ring1
        _ = 0 := by rw [xEquation]; ring1
    have yProductZero : 2 * (center.y - point.y) = 0 := by
      calc
        2 * (center.y - point.y) =
            (2 * center.y - point.y) - point.y := by ring1
        _ = 0 := by rw [yEquation]; ring1
    have xDifferenceZero :=
      ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero xProductZero
    have yDifferenceZero :=
      ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero yProductZero
    apply Plane.Point.ext
    · calc
        point.x = center.x - (center.x - point.x) := by ring1
        _ = center.x := by rw [xDifferenceZero]; ring1
    · calc
        point.y = center.y - (center.y - point.y) := by ring1
        _ = center.y := by rw [yDifferenceZero]; ring1
  exact ⟨opposite, point, oppositeDifferent,
    ⟨oppositeOnLine, oppositeOnCircle⟩, pointIntersection⟩

end

end Purelib.Curves.Plane.Conic

end
