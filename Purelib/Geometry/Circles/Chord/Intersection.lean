module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Curves.Plane.Conic.LineIntersection
import Purelib.Geometry.Circles.Chord.Basic
public import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Geometry.Plane.Line.Affine
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Affine
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

@[expose] public section

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- Exercise 16.3: a line cannot have three distinct intersections with a non-null circle. -/
theorem exercise_16_3 [DecidableEq K]
    (circle : Conic K) (line : Plane.Line K) (center : Plane.Point K)
    (circleQuadrance : K) (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance) :
    ¬ Conic.LineIntersection.HasThreeDistinctIntersections circle line := by
  intro threeIntersections
  rcases threeIntersections with
    ⟨first, second, third, firstSecondDistinct, firstThirdDistinct,
      secondThirdDistinct, firstIntersection, secondIntersection,
      thirdIntersection⟩
  have firstRadiusFromPoint : Quadrance.quadrance first center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center first circleQuadrance
      presentation).1 firstIntersection.2
  have secondRadiusFromPoint : Quadrance.quadrance second center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center second circleQuadrance
      presentation).1 secondIntersection.2
  have separationNonzero : Quadrance.quadrance first second ≠ 0 := by
    intro separationZero
    apply quadranceNonzero
    exact Conic.radius_eq_zero_of_equal_radii_and_null_separation
      first second center circleQuadrance firstSecondDistinct twoNonzero
      (by
        calc
          Quadrance.quadrance center first = Quadrance.quadrance first center :=
            Quadrance.quadrance_symm center first
          _ = circleQuadrance := firstRadiusFromPoint)
      (by
        calc
          Quadrance.quadrance center second = Quadrance.quadrance second center :=
            Quadrance.quadrance_symm center second
          _ = circleQuadrance := secondRadiusFromPoint)
      separationZero
  have allLinePoints := Conic.LineIntersection.conic_line_intersection circle line
    ⟨first, second, third, firstSecondDistinct, firstThirdDistinct,
      secondThirdDistinct, firstIntersection, secondIntersection,
      thirdIntersection⟩
  have testPointOnLine : line.Contains (Affine.thalesPoint 2 first second) := by
    have firstOnLine := firstIntersection.1
    have secondOnLine := secondIntersection.1
    unfold Plane.Line.Contains at firstOnLine secondOnLine ⊢
    unfold Affine.thalesPoint Affine.affineCombination
    calc
      line.a * ((1 - 2) * first.x + 2 * second.x) +
          line.b * ((1 - 2) * first.y + 2 * second.y) + line.c =
        (1 - 2) *
            (line.a * first.x + line.b * first.y + line.c) +
          2 * (line.a * second.x + line.b * second.y + line.c) := by ring1
      _ = 0 := by
        rw [firstOnLine, secondOnLine]
        ring1
  have testPointZero :
      circle.evaluate (Affine.thalesPoint 2 first second) = 0 :=
    allLinePoints (Affine.thalesPoint 2 first second) testPointOnLine
  have firstZero : circle.evaluate first = 0 := firstIntersection.2
  have secondZero : circle.evaluate second = 0 := secondIntersection.2
  have factorNonzero : (2 : K) * (2 - 1) ≠ 0 := by
    intro factorZero
    apply twoNonzero
    calc
      (2 : K) = 2 * (2 - 1) := by ring1
      _ = 0 := factorZero
  have restrictionProductZero :
      ((2 : K) * (2 - 1)) *
        (Conic.LineIntersection.lineRestrictionQuadratic circle) first second = 0 := by
    calc
      ((2 : K) * (2 - 1)) *
          (Conic.LineIntersection.lineRestrictionQuadratic circle) first second =
        circle.evaluate (Affine.thalesPoint 2 first second) := by
          rw [Conic.LineIntersection.evaluate_thalesPoint, firstZero, secondZero]
          ring1
      _ = 0 := testPointZero
  have restrictionZero :=
    ExplicitField.eq_zero_of_mul_eq_zero_left factorNonzero restrictionProductZero
  have restrictionFormula :
      (Conic.LineIntersection.lineRestrictionQuadratic circle) first second =
        circle.d * Quadrance.quadrance first second := by
    unfold Conic.LineIntersection.lineRestrictionQuadratic Quadrance.quadrance
    rw [presentation.1, ← presentation.2.1]
    ring1
  have restrictionNonzero :
      (Conic.LineIntersection.lineRestrictionQuadratic circle) first second ≠ 0 := by
    rw [restrictionFormula]
    exact ExplicitField.mul_ne_zero presentation.2.2.1
      separationNonzero
  exact restrictionNonzero restrictionZero

end

end Purelib.Curves.Plane.Conic

end
