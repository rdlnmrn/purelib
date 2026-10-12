module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Circles.Conic.Basic
public import Purelib.Geometry.Circles.Diameter.Basic
import Purelib.Geometry.Plane.Line.Affine
public import Purelib.Geometry.Plane.Line.Altitude
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Construction
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Null
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Affine.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Dot
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Median.Quadrance
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field (ExplicitField)

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Point.Affine

section
public section

/-!
# Divine Proportions, Theorem 117: the nine point circle

All nine points and the circle are explicit finite constructions.  The six
midpoint incidences follow from the cleared Euler relation `2C+O=A₁+A₂+A₃`.
For an altitude foot, the side-midpoint and vertex--orthocenter midpoint form
a diameter: a denominator-cleared dot-product lemma supplies the right-angle
calculation even when the foot coincides with a diameter endpoint.
-/

namespace Purelib.Geometry.Circles.Diameter.Quadrance

variable {K : Type*} [ExplicitField K]

/-- A right vertex has the same quadrance from the midpoint as either endpoint, without any distinctness premise on the
three points. -/
theorem midpoint_right_quadrance_of_dot_zero
    [DecidableEq K]
    (first second rightVertex : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (rightAngle : Dot.pointVectorDot rightVertex first second = 0) :
    Quadrance.quadrance (Affine.midpoint first second) first =
      Quadrance.quadrance (Affine.midpoint first second) rightVertex := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero :=
      ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero
  have pythagoras :
      Quadrance.quadrance first rightVertex + Quadrance.quadrance second rightVertex =
        Quadrance.quadrance first second := by
    apply Group.eq_of_sub_eq_zero
    calc
      Quadrance.quadrance first rightVertex + Quadrance.quadrance second rightVertex -
          Quadrance.quadrance first second =
        2 * Dot.pointVectorDot rightVertex first second := by
          unfold Quadrance.quadrance Dot.pointVectorDot
          ring1
      _ = 0 := by rw [rightAngle]; ring1
  have endpointCleared :
      Quadrance.quadrance (Affine.midpoint first second) first * 4 =
        Quadrance.quadrance first second := by
    rw [Quadrance.midpoint_quadrance first second twoNonzero]
    exact ExplicitField.div_mul_cancel _ fourNonzero
  have rightCleared := Triangles.Median.Quadrance.median_quadrance_cleared
    first second rightVertex twoNonzero
  apply ExplicitField.eq_of_mul_eq_mul_right fourNonzero
  calc
    Quadrance.quadrance (Affine.midpoint first second) first * 4 =
        Quadrance.quadrance first second := endpointCleared
    _ = 2 * Quadrance.quadrance first rightVertex +
          2 * Quadrance.quadrance second rightVertex - Quadrance.quadrance first second := by
      rw [← pythagoras]
      ring1
    _ = Quadrance.quadrance (Affine.midpoint first second) rightVertex * 4 :=
      rightCleared.symm

/-- An altitude foot from one endpoint of a diameter has the same quadrance from the diameter midpoint as that endpoint.
The other endpoint is supplied as the midpoint of a non-null target side. -/
theorem altitudeFoot_diameter_quadrance
    [DecidableEq K]
    (source sideFirst sideSecond : Plane.Point K)
    (sideDistinct : sideFirst ≠ sideSecond)
    (twoNonzero : (2 : K) ≠ 0)
    (sideNonNull :
      ¬ (Incidence.lineThrough sideFirst sideSecond sideDistinct).IsNull) :
    let oppositeSideMidpoint := Affine.midpoint sideFirst sideSecond
    let center := Affine.midpoint source oppositeSideMidpoint
    let foot := Altitude.altitudeFoot source
      (Incidence.lineThrough sideFirst sideSecond sideDistinct) sideNonNull
    Quadrance.quadrance center foot = Quadrance.quadrance center source := by
  dsimp only
  let sideLine := Incidence.lineThrough sideFirst sideSecond sideDistinct
  let oppositeSideMidpoint := Affine.midpoint sideFirst sideSecond
  let center := Affine.midpoint source oppositeSideMidpoint
  let foot := Altitude.altitudeFoot source sideLine sideNonNull
  have midpointOnLine : sideLine.Contains oppositeSideMidpoint :=
    Affine.line_contains_midpoint sideLine sideFirst sideSecond twoNonzero
      (Incidence.lineThrough_contains_first sideFirst sideSecond sideDistinct)
      (Incidence.lineThrough_contains_second sideFirst sideSecond sideDistinct)
  have footOnLine : sideLine.Contains foot :=
    Altitude.altitudeFoot_on_line source sideLine sideNonNull
  have sourceOnAltitude :
      (Construction.altitudeThrough source sideLine).Contains source :=
    Construction.altitudeThrough_contains source sideLine
  have footOnAltitude :
      (Construction.altitudeThrough source sideLine).Contains foot :=
    Altitude.altitudeFoot_on_altitude source sideLine sideNonNull
  have rightAngle :
      Dot.pointVectorDot foot oppositeSideMidpoint source = 0 :=
    Altitude.pointVectorDot_eq_zero_of_line_altitude sideLine source
      oppositeSideMidpoint source foot sideNonNull midpointOnLine footOnLine
      sourceOnAltitude footOnAltitude
  have rightQuadrance := midpoint_right_quadrance_of_dot_zero
    oppositeSideMidpoint source foot twoNonzero rightAngle
  have midpointOrder :
      Affine.midpoint oppositeSideMidpoint source = center := by
    exact Affine.midpoint_symm oppositeSideMidpoint source
  rw [midpointOrder] at rightQuadrance
  have endpointQuadrance := Quadrance.midpoint_equal_quadrance source
    oppositeSideMidpoint twoNonzero
  exact rightQuadrance.symm.trans endpointQuadrance.symm
end Purelib.Geometry.Circles.Diameter.Quadrance

end

section
/-!
# Divine Proportions, Exercise 16.6: antipodal quadrance sums

The printed exercise omits a non-null hypothesis.  An executable `F₅`
counterexample below shows that the claim fails on a null circle.  For a
non-null circle, its displayed intersection makes every diameter non-null;
midpoint uniqueness then identifies the two equidistant diameter points as
antipodes, giving an explicit constant quadrance sum.
-/

public section

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- The sum of quadrances to two symmetric diameter points is constant on a circle.

For distinct diameter points equidistant from the center, the sum is twice their center quadrance plus twice the circle
quadrance. The circle quadrance and two must be nonzero (Exercise 16.6). -/
theorem exercise_16_6 [DecidableEq K]
    (circle : Conic K) (line : Plane.Line K) (center first second point : Plane.Point K)
    (circleQuadrance : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (diameter : circle.IsDiameter line center)
    (firstSecondDistinct : first ≠ second)
    (firstOnDiameter : line.Contains first)
    (secondOnDiameter : line.Contains second)
    (equalCenterQuadrances :
      Quadrance.quadrance first center = Quadrance.quadrance second center)
    (pointOnCircle : circle.Contains point) :
    Quadrance.quadrance first point + Quadrance.quadrance second point =
      2 * (Quadrance.quadrance first center + circleQuadrance) := by
  have diameterNonNull := Conic.diameter_nonNull_of_circleQuadrance_ne_zero circle
    line center circleQuadrance quadranceNonzero presentation diameter
  have throughEquivalent :
      (Incidence.lineThrough first second firstSecondDistinct).Equivalent line :=
    Incidence.lineThrough_unique first second firstSecondDistinct line
      firstOnDiameter secondOnDiameter
  have throughNonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull := by
    exact Conic.nonNull_of_equivalent
      (Incidence.lineThrough first second firstSecondDistinct) line
      throughEquivalent diameterNonNull
  have centerEqualQuadrances :
      Quadrance.quadrance center first = Quadrance.quadrance center second := by
    calc
      Quadrance.quadrance center first = Quadrance.quadrance first center :=
        Quadrance.quadrance_symm center first
      _ = Quadrance.quadrance second center := equalCenterQuadrances
      _ = Quadrance.quadrance center second := Quadrance.quadrance_symm second center
  have centerIsMidpoint : center = Affine.midpoint first second :=
    Quadrance.midpoint_unique_of_equal_quadrance first second center
      firstSecondDistinct twoNonzero throughNonNull
      (Relations.line_contains_of_equivalent
        (Plane.Line.equivalent_symm throughEquivalent) center diameter.1)
      centerEqualQuadrances
  have midpointX := congrArg Plane.Point.x centerIsMidpoint
  have midpointY := congrArg Plane.Point.y centerIsMidpoint
  change center.x = (first.x + second.x) / 2 at midpointX
  change center.y = (first.y + second.y) / 2 at midpointY
  have xSum : first.x + second.x = 2 * center.x := by
    calc
      first.x + second.x = ((first.x + second.x) / 2) * 2 :=
        (ExplicitField.div_mul_cancel
          (first.x + second.x) twoNonzero).symm
      _ = center.x * 2 := by rw [← midpointX]
      _ = 2 * center.x := by ring1
  have ySum : first.y + second.y = 2 * center.y := by
    calc
      first.y + second.y = ((first.y + second.y) / 2) * 2 :=
        (ExplicitField.div_mul_cancel
          (first.y + second.y) twoNonzero).symm
      _ = center.y * 2 := by rw [← midpointY]
      _ = 2 * center.y := by ring1
  have pointRadius : Quadrance.quadrance point center = circleQuadrance :=
    (Conic.contains_iff_quadrance_eq circle center point circleQuadrance
      presentation).1 pointOnCircle
  calc
    Quadrance.quadrance first point + Quadrance.quadrance second point =
        2 * (Quadrance.quadrance first center + Quadrance.quadrance point center) :=
      Conic.antipodal_quadrance_sum first second center point xSum ySum
    _ = 2 * (Quadrance.quadrance first center + circleQuadrance) := by
      rw [pointRadius]

/-- The corrected exercise's literal independence statement for two requested circle points, still with only finite
witnesses. -/
theorem exercise_16_6_independent [DecidableEq K]
    (circle : Conic K) (line : Plane.Line K) (center first second : Plane.Point K)
    (circleQuadrance : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (diameter : circle.IsDiameter line center)
    (firstSecondDistinct : first ≠ second)
    (firstOnDiameter : line.Contains first)
    (secondOnDiameter : line.Contains second)
    (equalCenterQuadrances :
      Quadrance.quadrance first center = Quadrance.quadrance second center)
    (left right : Plane.Point K)
    (leftOnCircle : circle.Contains left)
    (rightOnCircle : circle.Contains right) :
    Quadrance.quadrance first left + Quadrance.quadrance second left =
      Quadrance.quadrance first right + Quadrance.quadrance second right := by
  calc
    Quadrance.quadrance first left + Quadrance.quadrance second left =
        2 * (Quadrance.quadrance first center + circleQuadrance) :=
      exercise_16_6 circle line center first second left circleQuadrance
        twoNonzero quadranceNonzero presentation diameter firstSecondDistinct
        firstOnDiameter secondOnDiameter equalCenterQuadrances leftOnCircle
    _ = Quadrance.quadrance first right + Quadrance.quadrance second right :=
      (exercise_16_6 circle line center first second right circleQuadrance
        twoNonzero quadranceNonzero presentation diameter firstSecondDistinct
        firstOnDiameter secondOnDiameter equalCenterQuadrances
        rightOnCircle).symm
end

end Purelib.Curves.Plane.Conic

end

end

end
