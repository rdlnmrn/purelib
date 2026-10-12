module
public import Purelib.Geometry.Circles.Diameter.Basic
public import Purelib.Geometry.Triangles.Circumcircle.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Affine.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Right.Midpoint
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Geometry.Plane.Line.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Point.Affine

section
@[expose] public section

/-!
# Divine Proportions, §16.1: diameters

The source's midpoint proof of Theorem 103 requires a non-null diameter side,
the same visible hypothesis as the already formalized midpoint-uniqueness
theorem.  The statement below exposes that characteristic-dependent omission.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

/-- The metric core of Theorem 103: once the displayed center is the midpoint, the Right midpoint theorem gives the
right vertex immediately. -/
theorem right_diameter_of_center_eq_midpoint [DecidableEq K]
    (first second third center : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0)
    (centerIsMidpoint : center = Affine.midpoint first second)
    (firstRadius : Quadrance.quadrance center first = Quadrance.quadrance center third) :
    (Incidence.lineThrough first third firstThirdDistinct).Perpendicular
      (Incidence.lineThrough second third secondThirdDistinct) := by
  apply (Triangles.Right.Midpoint.right_midpoint first second third firstThirdDistinct
    secondThirdDistinct twoNonzero).1
  rw [← centerIsMidpoint]
  exact firstRadius

/-- Theorem 103 (Right diameter), corrected by exposing the non-null diameter side required by the source's appeal to
midpoint uniqueness. -/
theorem right_diameter [DecidableEq K]
    (circle : Conic K) (first second third center : Plane.Point K)
    (circleQuadrance : K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0)
    (diameterSideNonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull)
    (circumcircle : circle.IsCircumcircleOf
      first second third center circleQuadrance)
    (diameter : circle.IsDiameter
      (Incidence.lineThrough first second firstSecondDistinct) center) :
    (Incidence.lineThrough first third firstThirdDistinct).Perpendicular
      (Incidence.lineThrough second third secondThirdDistinct) := by
  rcases circumcircle with
    ⟨presentation, firstOnCircle, secondOnCircle, thirdOnCircle⟩
  have firstRadiusFromPoint :
      Quadrance.quadrance first center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center first circleQuadrance
      presentation).1 firstOnCircle
  have secondRadiusFromPoint :
      Quadrance.quadrance second center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center second circleQuadrance
      presentation).1 secondOnCircle
  have thirdRadiusFromPoint :
      Quadrance.quadrance third center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center third circleQuadrance
      presentation).1 thirdOnCircle
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
  have thirdRadius : Quadrance.quadrance center third = circleQuadrance := by
    calc
      Quadrance.quadrance center third = Quadrance.quadrance third center :=
        Quadrance.quadrance_symm center third
      _ = circleQuadrance := thirdRadiusFromPoint
  have centerIsMidpoint : center = Affine.midpoint first second :=
    Quadrance.midpoint_unique_of_equal_quadrance first second center
      firstSecondDistinct twoNonzero diameterSideNonNull diameter.1
      (firstRadius.trans secondRadius.symm)
  exact right_diameter_of_center_eq_midpoint first second third center
    firstThirdDistinct secondThirdDistinct twoNonzero centerIsMidpoint
    (firstRadius.trans thirdRadius.symm)
end

end Purelib.Curves.Plane.Conic

end
