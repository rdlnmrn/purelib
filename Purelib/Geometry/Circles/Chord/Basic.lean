module
public import Purelib.Curves.Plane.Conic.LineIntersection
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
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

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

section
/-!
# Divine Proportions, §16.1: circle chords

The source introduces a square root of `-1` while excluding null chords.  The
proof here stays constructive: two cleared square identities show directly
that equal-radius points with null separation would force the radius to vanish.
-/

@[expose] public section

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- Equal-radius distinct points cannot have null separation unless the common radius itself is zero. -/
theorem radius_eq_zero_of_equal_radii_and_null_separation [DecidableEq K]
    (first second center : Plane.Point K) (radius : K)
    (distinct : first ≠ second) (twoNonzero : (2 : K) ≠ 0)
    (firstRadius : Quadrance.quadrance center first = radius)
    (secondRadius : Quadrance.quadrance center second = radius)
    (separationZero : Quadrance.quadrance first second = 0) :
    radius = 0 := by
  have xDifferenceNonzero : second.x - first.x ≠ 0 := by
    intro xDifferenceZero
    have xEqual : second.x = first.x := by
      calc
        second.x = (second.x - first.x) + first.x := by ring1
        _ = first.x := by rw [xDifferenceZero]; ring1
    have ySquareZero : (second.y - first.y) *
        (second.y - first.y) = 0 := by
      calc
        (second.y - first.y) * (second.y - first.y) =
            Quadrance.quadrance first second := by
          unfold Quadrance.quadrance
          rw [xDifferenceZero]
          ring1
        _ = 0 := separationZero
    have yDifferenceZero : second.y - first.y = 0 := by
      by_cases yDifferenceZero : second.y - first.y = 0
      · exact yDifferenceZero
      · exact False.elim
          ((ExplicitField.mul_ne_zero yDifferenceZero yDifferenceZero)
            ySquareZero)
    have yEqual : second.y = first.y := by
      calc
        second.y = (second.y - first.y) + first.y := by ring1
        _ = first.y := by rw [yDifferenceZero]; ring1
    exact distinct (Plane.Point.ext xEqual.symm yEqual.symm)
  have xDifferenceSquareNonzero : (second.x - first.x) ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      ExplicitField.mul_ne_zero xDifferenceNonzero
        xDifferenceNonzero
  have dotProductZero :
      (second.x - first.x) * (first.x - center.x) +
        (second.y - first.y) * (first.y - center.y) = 0 := by
    have twiceDotZero :
        2 * ((second.x - first.x) * (first.x - center.x) +
          (second.y - first.y) * (first.y - center.y)) = 0 := by
      calc
        2 * ((second.x - first.x) * (first.x - center.x) +
            (second.y - first.y) * (first.y - center.y)) =
          (Quadrance.quadrance center second - Quadrance.quadrance center first) -
            Quadrance.quadrance first second := by
              unfold Quadrance.quadrance
              ring1
        _ = 0 := by
          rw [firstRadius, secondRadius, separationZero]
          ring1
    exact ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero twiceDotZero
  have coordinateSquareProductsEqual :
      (second.x - first.x) ^ 2 * (first.x - center.x) ^ 2 =
        (second.y - first.y) ^ 2 * (first.y - center.y) ^ 2 := by
    have coordinateProductEquality :
        (second.x - first.x) * (first.x - center.x) =
          -((second.y - first.y) * (first.y - center.y)) := by
      calc
        (second.x - first.x) * (first.x - center.x) =
            ((second.x - first.x) * (first.x - center.x) +
              (second.y - first.y) * (first.y - center.y)) -
              (second.y - first.y) * (first.y - center.y) := by ring1
        _ = -((second.y - first.y) * (first.y - center.y)) := by
          rw [dotProductZero]
          ring1
    calc
      (second.x - first.x) ^ 2 * (first.x - center.x) ^ 2 =
          ((second.x - first.x) * (first.x - center.x)) ^ 2 := by ring1
      _ = (-((second.y - first.y) *
          (first.y - center.y))) ^ 2 := by rw [coordinateProductEquality]
      _ = (second.y - first.y) ^ 2 *
          (first.y - center.y) ^ 2 := by ring1
  have scaledRadiusZero :
      (second.x - first.x) ^ 2 * Quadrance.quadrance center first = 0 := by
    calc
      (second.x - first.x) ^ 2 * Quadrance.quadrance center first =
          (second.x - first.x) ^ 2 * (first.x - center.x) ^ 2 +
            (second.x - first.x) ^ 2 * (first.y - center.y) ^ 2 := by
        unfold Quadrance.quadrance
        ring1
      _ = (second.y - first.y) ^ 2 * (first.y - center.y) ^ 2 +
          (second.x - first.x) ^ 2 * (first.y - center.y) ^ 2 := by
        rw [coordinateSquareProductsEqual]
      _ = Quadrance.quadrance first second * (first.y - center.y) ^ 2 := by
        unfold Quadrance.quadrance
        ring1
      _ = 0 := by rw [separationZero]; ring1
  have firstRadiusZero := ExplicitField.eq_zero_of_mul_eq_zero_left
    xDifferenceSquareNonzero scaledRadiusZero
  calc
    radius = Quadrance.quadrance center first := firstRadius.symm
    _ = 0 := firstRadiusZero

/-- Theorem 104 (Circle chord): a chord of a non-null circle is non-null. -/
theorem circle_chord [DecidableEq K]
    (circle : Conic K) (line : Plane.Line K) (center : Plane.Point K)
    (circleQuadrance : K) (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance)
    (chord : Curves.Plane.Conic.LineIntersection.IsChord circle line) :
    ¬ line.IsNull := by
  rcases chord with
    ⟨first, second, distinct, firstIntersection, secondIntersection⟩
  have firstRadiusFromPoint : Quadrance.quadrance first center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center first circleQuadrance
      presentation).1 firstIntersection.2
  have secondRadiusFromPoint : Quadrance.quadrance second center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center second circleQuadrance
      presentation).1 secondIntersection.2
  have firstRadius : Quadrance.quadrance center first = circleQuadrance := by
    calc
      Quadrance.quadrance center first = Quadrance.quadrance first center :=
        Quadrance.quadrance_symm center first
      _ = circleQuadrance := firstRadiusFromPoint
  have secondRadius : Quadrance.quadrance center second = circleQuadrance := by
    calc
      Quadrance.quadrance center second = Quadrance.quadrance second center :=
        Quadrance.quadrance_symm center second
      _ = circleQuadrance := secondRadiusFromPoint
  intro lineNull
  have separationZero := Conic.quadrance_eq_zero_of_null_line_contains line lineNull
    first second firstIntersection.1 secondIntersection.1
  exact quadranceNonzero
    (radius_eq_zero_of_equal_radii_and_null_separation first second center
      circleQuadrance distinct twoNonzero firstRadius secondRadius
      separationZero)
end

end Purelib.Curves.Plane.Conic

end

end

section
@[expose] public section

/-!
# Divine Proportions, §16.2: subtended spreads

The Extended spread law supplies the fixed cleared ratio on a circle.  A
second finite determinant identity for the two radius vectors converts that
ratio into the source's `S₂(s) = 4s(1-s)` formula.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- The line through two distinct points of a non-null circle is non-null. -/
theorem lineThrough_circle_points_nonNull [DecidableEq K]
    (circle : Conic K) (center : Plane.Point K) (circleQuadrance : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance)
    (first second : Plane.Point K) (distinct : first ≠ second)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second) :
    ¬ (Incidence.lineThrough first second distinct).IsNull := by
  apply circle_chord circle (Incidence.lineThrough first second distinct) center
    circleQuadrance twoNonzero quadranceNonzero presentation
  exact ⟨first, second, distinct,
    ⟨Incidence.lineThrough_contains_first first second distinct, firstOnCircle⟩,
    ⟨Incidence.lineThrough_contains_second first second distinct, secondOnCircle⟩⟩
end

end Purelib.Curves.Plane.Conic

end
