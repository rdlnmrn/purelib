module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Geometry.Circles.Conic.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Dot
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Group.Negation
import Purelib.Data.Nat.Order
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Quadrilaterals.Basic

section
@[expose] public section

/-!
# Divine Proportions, §16.2: equal products

The source derives Theorem 106 from subtended spreads and the Spread law.  The
finite algebra underneath that proof is stronger: along any displayed chord,
the product of the two endpoint quadrances is the square of the intersection
point's circle-power.  This form needs no non-null hypotheses or division.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

/-- The finite four-point determinant which vanishes when the points lie on one circle, written relative to the fourth
point. -/
def fourPointCircleDeterminant
    (first second third fourth : Plane.Point K) : K :=
  Quadrance.quadrance first fourth * Incidence.pointDeterminant fourth second third -
    Quadrance.quadrance second fourth * Incidence.pointDeterminant fourth first third +
    Quadrance.quadrance third fourth * Incidence.pointDeterminant fourth first second

/-- Four displayed points on one circle make the finite circle determinant vanish. No distinctness, non-nullness, or
division is needed. -/
theorem fourPointCircleDeterminant_eq_zero
    (circle : Conic K) (center : Plane.Point K) (circleQuadrance : K)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (first second third fourth : Plane.Point K)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second)
    (thirdOnCircle : circle.Contains third)
    (fourthOnCircle : circle.Contains fourth) :
    fourPointCircleDeterminant first second third fourth = 0 := by
  have firstRadius : Quadrance.quadrance first center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center first circleQuadrance
      presentation).1 firstOnCircle
  have secondRadius : Quadrance.quadrance second center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center second circleQuadrance
      presentation).1 secondOnCircle
  have thirdRadius : Quadrance.quadrance third center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center third circleQuadrance
      presentation).1 thirdOnCircle
  have fourthRadius : Quadrance.quadrance fourth center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center fourth circleQuadrance
      presentation).1 fourthOnCircle
  have firstChord := Conic.chordQuadrance_eq_twice_dot center first fourth
    circleQuadrance firstRadius fourthRadius
  have secondChord := Conic.chordQuadrance_eq_twice_dot center second fourth
    circleQuadrance secondRadius fourthRadius
  have thirdChord := Conic.chordQuadrance_eq_twice_dot center third fourth
    circleQuadrance thirdRadius fourthRadius
  unfold fourPointCircleDeterminant Incidence.pointDeterminant
  rw [firstChord, secondChord, thirdChord]
  ring1
end

end Purelib.Curves.Plane.Conic

end

section
@[expose] public section

/-!
# Divine Proportions, Theorem 109: cyclic quadrilaterals

A quadrilateral is kept as four displayed points together with the source's
finite distinctness and noncollinearity certificates.  The cyclic predicate
stores an explicit conic, center, quadrance, circle presentation, and four
incidence proofs.

The printed four-by-four determinant is expanded by `determinantThree`; no
matrix determinant, permutation enumeration, or quotient of cyclic orderings
is introduced.  A translated determinant identity then gives both directions
of Theorem 109 constructively.
-/

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

/-- The source's determinant with rows `[xᵢ²+yᵢ², xᵢ, yᵢ, 1]`, expanded along its first row. -/
def coordinateCircleDeterminant
    (first second third fourth : Plane.Point K) : K :=
  Quadrilateral.circleRowNorm first *
      Quadrilateral.determinantThree second.x second.y 1 third.x third.y 1
        fourth.x fourth.y 1 -
    first.x *
      Quadrilateral.determinantThree (Quadrilateral.circleRowNorm second) second.y 1
        (Quadrilateral.circleRowNorm third) third.y 1
        (Quadrilateral.circleRowNorm fourth) fourth.y 1 +
    first.y *
      Quadrilateral.determinantThree (Quadrilateral.circleRowNorm second) second.x 1
        (Quadrilateral.circleRowNorm third) third.x 1
        (Quadrilateral.circleRowNorm fourth) fourth.x 1 -
    Quadrilateral.determinantThree (Quadrilateral.circleRowNorm second) second.x second.y
      (Quadrilateral.circleRowNorm third) third.x third.y
      (Quadrilateral.circleRowNorm fourth) fourth.x fourth.y

/-- Translating the printed four-by-four determinant to the fourth point gives the already useful quadrance/determinant
expression from Chapter 16. -/
theorem
  coordinateCircleDeterminant_eq_fourPointCircleDeterminant
    (first second third fourth : Plane.Point K) :
    coordinateCircleDeterminant first second third fourth =
      Curves.Plane.Conic.fourPointCircleDeterminant first second third fourth := by
  unfold coordinateCircleDeterminant Quadrilateral.circleRowNorm Quadrilateral.determinantThree
    Curves.Plane.Conic.fourPointCircleDeterminant Incidence.pointDeterminant Quadrance.quadrance
  ring1

/-- The four-point determinant expanded using quadrances from an arbitrary displayed center. This identity does not
assume that any radii are equal. -/
theorem fourPointCircleDeterminant_center_formula
    (first second third fourth center : Plane.Point K) :
    Conic.fourPointCircleDeterminant first second third fourth =
      Quadrance.quadrance first center * Incidence.pointDeterminant fourth second third -
        Quadrance.quadrance second center * Incidence.pointDeterminant fourth first third +
        Quadrance.quadrance third center * Incidence.pointDeterminant fourth first second -
        Quadrance.quadrance fourth center * Incidence.pointDeterminant first second third := by
  unfold Conic.fourPointCircleDeterminant Incidence.pointDeterminant Quadrance.quadrance
  ring1

/-- If the first three points have a common displayed radius, the four-point determinant is their noncollinearity
determinant times the fourth point's circle-power. -/
theorem fourPointCircleDeterminant_eq_radius_difference
    (first second third fourth center : Plane.Point K) (circleQuadrance : K)
    (firstRadius : Quadrance.quadrance first center = circleQuadrance)
    (secondRadius : Quadrance.quadrance second center = circleQuadrance)
    (thirdRadius : Quadrance.quadrance third center = circleQuadrance) :
    Curves.Plane.Conic.fourPointCircleDeterminant first second third fourth =
      Incidence.pointDeterminant first second third *
        (circleQuadrance - Quadrance.quadrance fourth center) := by
  rw [fourPointCircleDeterminant_center_formula, firstRadius, secondRadius,
    thirdRadius]
  unfold Incidence.pointDeterminant
  ring1
end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end
