module
import Purelib.Data.List.Filter
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Init.Prelude
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Curves.Plane.Conic.Basic

open Purelib

open Purelib.Curves.Plane (Conic)

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

section
@[expose] public section

/-!
# Divine Proportions, Example 15.2 and Exercise 15.3

The two source figures are retained as literal finite coordinate grids.  Their
entries are checked against central quadrance, and filtering the displayed
points by a quadrance label gives the printed circle counts.  These are finite
display certificates: they do not assert that either coordinate list globally
enumerates an ambient field carrier.
-/

namespace Purelib.Geometry.Conics.Circle.Finite.Display

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Evaluate central quadrance on every row of a displayed point grid. -/
def centralQuadranceRows (center : Geometry.Plane.Point K)
    (rows : List (List (Geometry.Plane.Point K))) : List (List K) :=
  rows.map fun row => row.map fun point => Quadrance.quadrance point center

/-- The points in one displayed row carrying a requested central-circle label. -/
def displayedCirclePoints [DecidableEq K] (center :
  Geometry.Plane.Point K)
    (row : List (Geometry.Plane.Point K)) (circleQuadrance : K) : List (Geometry.Plane.Point K) :=
  row.filter fun point =>
    decide (Quadrance.quadrance point center = circleQuadrance)

/-- Filter every displayed row by one requested central-circle label. -/
def displayedCirclePointRows [DecidableEq K] (center :
  Geometry.Plane.Point K)
    (rows : List (List (Geometry.Plane.Point K)))
    (circleQuadrance : K) : List (List (Geometry.Plane.Point K)) :=
  rows.map fun row => displayedCirclePoints center row circleQuadrance

/-- Sum the finitely many row lengths in one displayed circle. -/
def displayedCircleCount [DecidableEq K] (center :
  Geometry.Plane.Point K)
    (rows : List (List (Geometry.Plane.Point K))) (circleQuadrance : K) : Nat :=
  (displayedCirclePointRows center rows circleQuadrance).foldl
    (fun count row => count + row.length) 0

/-- The finite point counts attached to a list of displayed circle labels. -/
def displayedCircleCounts [DecidableEq K] (center :
  Geometry.Plane.Point K)
    (rows : List (List (Geometry.Plane.Point K))) (circleQuadrances : List K) : List Nat :=
  circleQuadrances.map fun circleQuadrance =>
    displayedCircleCount center rows circleQuadrance

/-- A source figure is certified by its exact quadrance table, a duplicate-free point grid and label list, and the
requested finite count for every label. -/
def CentralCircleDisplayCertified [DecidableEq K]
    (center : Geometry.Plane.Point K) (rows : List (List (Geometry.Plane.Point K)))
    (valueRows : List (List K)) (circleQuadrances : List K)
    (counts : List Nat) : Prop :=
  centralQuadranceRows center rows = valueRows ∧
    rows.flatten.Nodup ∧
    circleQuadrances.Nodup ∧
    displayedCircleCounts center rows circleQuadrances = counts

open Purelib.Data.List in
/-- Every filtered point is incident with the normalized circle carrying its filter label. -/
theorem displayedCirclePoint_contains [DecidableEq K] [Nontrivial
  K]
    (center point : Geometry.Plane.Point K) (row : List (Geometry.Plane.Point K))
    (circleQuadrance : K)
    (membership : point ∈ displayedCirclePoints center row circleQuadrance) :
    (Conic.circleConic center circleQuadrance).Contains point := by
  apply (Conic.contains_iff_quadrance_eq
    (Conic.circleConic center circleQuadrance) center point
    circleQuadrance
    (Conic.circleConic_isCirclePresentation center circleQuadrance)).2
  unfold displayedCirclePoints at membership
  exact of_decide_eq_true ((Filter.mem_filter.mp membership).2)

end

end Purelib.Geometry.Conics.Circle.Finite.Display

end
