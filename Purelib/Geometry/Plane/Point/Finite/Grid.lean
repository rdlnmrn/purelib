module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
public import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude

section
public section

/-!
# Divine Proportions, Example 15.2 and Exercise 15.3

The two source figures are retained as literal finite coordinate grids.  Their
entries are checked against central quadrance, and filtering the displayed
points by a quadrance label gives the printed circle counts.  These are finite
display certificates: they do not assert that either coordinate list globally
enumerates an ambient field carrier.
-/

namespace Purelib.Geometry.Plane.Point.Finite.Grid

open Purelib
open Purelib.Data.List
open Purelib.Geometry

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The row of displayed points with a fixed second coordinate. -/
@[expose] def pointRow (xCoordinates : List K) (yCoordinate : K) : List
  (Geometry.Plane.Point K) :=
  xCoordinates.map fun xCoordinate => ⟨xCoordinate, yCoordinate⟩

/-- The literal Cartesian grid obtained from the displayed coordinate labels. -/
@[expose] def pointRows (xCoordinates yCoordinates : List K) : List
  (List (Geometry.Plane.Point K)) :=
  yCoordinates.map fun yCoordinate => pointRow xCoordinates yCoordinate

omit [Purelib.Algebra.Field.ExplicitField K] in
/-- Distinct horizontal and vertical labels produce distinct displayed grid points, without a carrier enumeration. -/
theorem pointRows_flatten_nodup [DecidableEq K]
    {xCoordinates yCoordinates : List K}
    (xNodup : xCoordinates.Nodup) (yNodup : yCoordinates.Nodup) :
    (pointRows xCoordinates yCoordinates).flatten.Nodup := by
  change
    (yCoordinates.flatMap fun yCoordinate =>
      pointRow xCoordinates yCoordinate).Nodup
  induction yCoordinates with
  | nil => exact List.Pairwise.nil
  | cons head tail inductionHypothesis =>
      rcases List.pairwise_cons.mp yNodup with
        ⟨headFresh, tailNodup⟩
      change
        (pointRow xCoordinates head ++
          tail.flatMap fun yCoordinate =>
            pointRow xCoordinates yCoordinate).Nodup
      apply Nodup.nodup_append
      · unfold pointRow
        exact Data.List.Nodup.nodup_map_of_injective
          (function := fun xCoordinate => (⟨xCoordinate, head⟩ : Geometry.Plane.Point K))
          (fun _ _ pointsEqual => congrArg Geometry.Plane.Point.x pointsEqual) xNodup
      · exact inductionHypothesis tailNodup
      · intro firstPoint firstMembership secondPoint secondMembership pointsEqual
        rcases Map.mem_map.mp firstMembership with
          ⟨_, _, firstPointEqual⟩
        rcases Flatten.mem_flatMap.mp secondMembership with
          ⟨otherY, otherYMembership, secondRowMembership⟩
        rcases Map.mem_map.mp secondRowMembership with
          ⟨_, _, secondPointEqual⟩
        apply headFresh otherY otherYMembership
        calc
          head = firstPoint.y := congrArg Geometry.Plane.Point.y firstPointEqual
          _ = secondPoint.y := congrArg Geometry.Plane.Point.y pointsEqual
          _ = otherY := (congrArg Geometry.Plane.Point.y secondPointEqual).symm

end

end Purelib.Geometry.Plane.Point.Finite.Grid

end
