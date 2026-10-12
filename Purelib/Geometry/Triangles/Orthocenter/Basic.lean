module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Construction
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Point.Basic

import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Triangles.Circumcenter.Affine
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

section
open Purelib
open Purelib.Geometry
open Purelib.Geometry.Plane
open Purelib.Geometry.Plane.Line

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

public section

/-!
# Divine Proportions, §12.3: altitudes and the orthocenter

Each triangle altitude is an explicit line.  The first two are nonparallel
whenever the vertices are noncollinear, so their intersection is executable.
The coefficient determinant of all three altitude lines vanishes by a single
polynomial identity, proving that the third passes through the same point.
-/

section

open Purelib.Algebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Triangles.Orthocenter.Basic

/-- The altitude from `first` to the opposite side `second third`. -/
@[expose] def triangleAltitudeFromFirst [DecidableEq K]
    (first second third : Plane.Point K) (secondThirdDistinct : second ≠ third) :
    Plane.Line K :=
  Construction.altitudeThrough first (Incidence.lineThrough second third secondThirdDistinct)

/-- The altitude from `second` to the opposite side `first third`. -/
@[expose] def triangleAltitudeFromSecond [DecidableEq K]
    (first second third : Plane.Point K) (firstThirdDistinct : first ≠ third) :
    Plane.Line K :=
  Construction.altitudeThrough second (Incidence.lineThrough first third firstThirdDistinct)

/-- The altitude from `third` to the opposite side `first second`. -/
@[expose] def triangleAltitudeFromThird [DecidableEq K]
    (first second third : Plane.Point K) (firstSecondDistinct : first ≠ second) :
    Plane.Line K :=
  Construction.altitudeThrough third (Incidence.lineThrough first second firstSecondDistinct)

/-- The first two triangle altitudes are nonparallel for a noncollinear triangle. -/
theorem triangle_altitudes_not_parallel
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third) :
    ¬ (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromFirst first second third secondThirdDistinct).Parallel
      (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromSecond first second third firstThirdDistinct) := by
  intro parallel
  apply notCollinear
  apply (Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
  change
    (-(Incidence.lineThrough second third secondThirdDistinct).b) *
        (Incidence.lineThrough first third firstThirdDistinct).a -
      (-(Incidence.lineThrough first third firstThirdDistinct).b) *
        (Incidence.lineThrough second third secondThirdDistinct).a = 0 at parallel
  simp only [Incidence.lineThrough_a, Incidence.lineThrough_b] at parallel
  have parallelNormalized :
      (second.x - third.x) * (first.y - third.y) -
        (first.x - third.x) * (second.y - third.y) = 0 := by
    calc
      (second.x - third.x) * (first.y - third.y) -
          (first.x - third.x) * (second.y - third.y) =
        -(third.x - second.x) * (first.y - third.y) -
          -(third.x - first.x) * (second.y - third.y) := by ring1
      _ = 0 := parallel
  calc
    Incidence.pointDeterminant first second third =
        -((second.x - third.x) * (first.y - third.y) -
          (first.x - third.x) * (second.y - third.y)) := by
            unfold Incidence.pointDeterminant
            ring1
    _ = 0 := by rw [parallelNormalized]; ring1

/-- The displayed orthocenter: the explicit intersection of the altitudes from the first two vertices. -/
@[expose] def orthocenterPoint [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third) : Plane.Point K :=
  Intersection.lineIntersection
    (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromFirst first second third secondThirdDistinct)
    (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromSecond first second third firstThirdDistinct)
    (Geometry.Triangles.Orthocenter.Basic.triangle_altitudes_not_parallel first second third firstThirdDistinct
      secondThirdDistinct notCollinear)

/-- The coefficient determinant of the three triangle altitudes vanishes. -/
theorem triangle_altitudes_determinant_zero [DecidableEq K]
    (first second third : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third) :
    Incidence.lineDeterminant
        (Triangles.Orthocenter.Basic.triangleAltitudeFromFirst first second third secondThirdDistinct)
        (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromSecond first second third firstThirdDistinct)
        (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromThird first second third firstSecondDistinct) = 0 :=
          by
  unfold Incidence.lineDeterminant Triangles.Orthocenter.Basic.triangleAltitudeFromFirst
    Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromSecond
      Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromThird Construction.altitudeThrough
    Incidence.lineThrough
  ring1

/-- The intersection of the first two altitudes lies on all three triangle altitudes.

Distinct vertices and noncollinearity certify the side constructions and the nonparallel altitude intersection. -/
theorem orthocenter
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third) :
    let center := Triangles.Orthocenter.Basic.orthocenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear
    (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromFirst first second third
        secondThirdDistinct).Contains center ∧
      (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromSecond first second third
        firstThirdDistinct).Contains center ∧
      (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromThird first second third
        firstSecondDistinct).Contains center := by
  dsimp only
  let nonparallel := Geometry.Triangles.Orthocenter.Basic.triangle_altitudes_not_parallel first second third
    firstThirdDistinct secondThirdDistinct notCollinear
  constructor
  · unfold Triangles.Orthocenter.Basic.orthocenterPoint
    exact Intersection.lineIntersection_on_first
      (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromFirst first second third secondThirdDistinct)
      (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromSecond first second third firstThirdDistinct)
      nonparallel
  constructor
  · unfold Triangles.Orthocenter.Basic.orthocenterPoint
    exact Intersection.lineIntersection_on_second
      (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromFirst first second third secondThirdDistinct)
      (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromSecond first second third firstThirdDistinct)
      nonparallel
  · unfold Triangles.Orthocenter.Basic.orthocenterPoint
    exact Intersection.lineIntersection_on_third_of_determinant_eq_zero
      (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromFirst first second third secondThirdDistinct)
      (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromSecond first second third firstThirdDistinct)
      (Geometry.Triangles.Orthocenter.Basic.triangleAltitudeFromThird first second third firstSecondDistinct)
      nonparallel
      (Geometry.Triangles.Orthocenter.Basic.triangle_altitudes_determinant_zero first second third
        firstSecondDistinct firstThirdDistinct secondThirdDistinct)

end Purelib.Geometry.Triangles.Orthocenter.Basic

end

end
