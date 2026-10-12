module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Line.Intersection
public import Purelib.Geometry.Plane.Line.PerpendicularBisector
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance

import Purelib.Algebra.Field.ExplicitField
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

section
open Purelib
open Purelib.Geometry
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Plane.Point

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

public section

/-!
# Divine Proportions, Chapter 12: circumcenters

The circumcenter is an explicit finite line intersection.  Noncollinearity
proves its denominator nonzero; equal-quadrance transitivity then supplies the
third perpendicular-bisector incidence.
-/

section

open Purelib.Algebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Triangles.Circumcenter.Basic

/-- Two side perpendicular bisectors used to construct the circumcenter are nonparallel precisely because the three
vertices are noncollinear. -/
theorem circumcenter_bisectors_not_parallel
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third) :
    ¬ (PerpendicularBisector.perpendicularBisector second third secondThirdDistinct).Parallel
      (PerpendicularBisector.perpendicularBisector first third firstThirdDistinct) := by
  intro parallel
  apply notCollinear
  apply (Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
  unfold Plane.Line.Parallel PerpendicularBisector.perpendicularBisector at parallel
  calc
    Incidence.pointDeterminant first second third =
        -((second.x - third.x) * (first.y - third.y) -
          (first.x - third.x) * (second.y - third.y)) := by
      unfold Incidence.pointDeterminant
      ring1
    _ = 0 := by rw [parallel]; ring1

/-- The displayed circumcenter: the explicit intersection of the perpendicular bisectors of `A₂A₃` and `A₁A₃`. -/
@[expose] def circumcenterPoint [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third) : Plane.Point K :=
  Intersection.lineIntersection
    (PerpendicularBisector.perpendicularBisector second third secondThirdDistinct)
    (PerpendicularBisector.perpendicularBisector first third firstThirdDistinct)
    (Geometry.Triangles.Circumcenter.Basic.circumcenter_bisectors_not_parallel first second third
      firstThirdDistinct secondThirdDistinct notCollinear)

/-- The circumquadrance belonging to the displayed circumcenter. -/
@[expose] def circumquadrance [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third) : K :=
  Quadrance.quadrance
    (Geometry.Triangles.Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear)
    first

/-- The constructed circumcenter lies on all three perpendicular bisectors and has equal quadrance to all vertices.

The vertices are distinct and noncollinear, and two is nonzero. -/
theorem circumcenter [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    let center := Triangles.Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear
    (PerpendicularBisector.perpendicularBisector second third secondThirdDistinct).Contains center ∧
      (PerpendicularBisector.perpendicularBisector first third firstThirdDistinct).Contains center ∧
      (PerpendicularBisector.perpendicularBisector first second firstSecondDistinct).Contains center ∧
      Quadrance.quadrance center first = Quadrance.quadrance center second ∧
      Quadrance.quadrance center second = Quadrance.quadrance center third := by
  dsimp only
  let nonparallel := Geometry.Triangles.Circumcenter.Basic.circumcenter_bisectors_not_parallel first second third
    firstThirdDistinct secondThirdDistinct notCollinear
  have onSecondThird :
      (PerpendicularBisector.perpendicularBisector second third secondThirdDistinct).Contains
        (Triangles.Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear) := by
    unfold Triangles.Circumcenter.Basic.circumcenterPoint
    exact Intersection.lineIntersection_on_first
      (PerpendicularBisector.perpendicularBisector second third secondThirdDistinct)
      (PerpendicularBisector.perpendicularBisector first third firstThirdDistinct) nonparallel
  have onFirstThird :
      (PerpendicularBisector.perpendicularBisector first third firstThirdDistinct).Contains
        (Triangles.Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear) := by
    unfold Triangles.Circumcenter.Basic.circumcenterPoint
    exact Intersection.lineIntersection_on_second
      (PerpendicularBisector.perpendicularBisector second third secondThirdDistinct)
      (PerpendicularBisector.perpendicularBisector first third firstThirdDistinct) nonparallel
  have equalSecondThird :
      Quadrance.quadrance
          (Triangles.Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
            secondThirdDistinct notCollinear) second =
        Quadrance.quadrance
          (Triangles.Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
            secondThirdDistinct notCollinear) third :=
    (PerpendicularBisector.equal_quadrance_iff_perpendicularBisector_contains second third
      (Triangles.Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear)
      secondThirdDistinct twoNonzero).2 onSecondThird
  have equalFirstThird :
      Quadrance.quadrance
          (Triangles.Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
            secondThirdDistinct notCollinear) first =
        Quadrance.quadrance
          (Triangles.Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
            secondThirdDistinct notCollinear) third :=
    (PerpendicularBisector.equal_quadrance_iff_perpendicularBisector_contains first third
      (Triangles.Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear)
      firstThirdDistinct twoNonzero).2 onFirstThird
  have equalFirstSecond :
      Quadrance.quadrance
          (Triangles.Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
            secondThirdDistinct notCollinear) first =
        Quadrance.quadrance
          (Triangles.Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
            secondThirdDistinct notCollinear) second :=
    equalFirstThird.trans equalSecondThird.symm
  have onFirstSecond :
      (PerpendicularBisector.perpendicularBisector first second firstSecondDistinct).Contains
        (Triangles.Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear) :=
    (PerpendicularBisector.equal_quadrance_iff_perpendicularBisector_contains first second
      (Triangles.Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear)
      firstSecondDistinct twoNonzero).1 equalFirstSecond
  exact ⟨onSecondThird, onFirstThird, onFirstSecond, equalFirstSecond,
    equalSecondThird⟩

end Purelib.Geometry.Triangles.Circumcenter.Basic

end

end
