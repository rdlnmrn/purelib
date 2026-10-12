module
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Riemann.Paths.RectangularSegmentRefinement
public import Purelib.Riemann.Meshes.RectangularObservationMesh
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Tactic.Ring

public section

/-! A physical side interval cannot cross a retained source-fragment
endpoint. Transport that fact to the original parent's affine parameter,
in either orientation, without constructing another partition or mesh. -/
namespace Purelib.Geometry.Rectangle.SourceIntervals

open Purelib
open Purelib.Data
open Purelib.Data.List
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Meshes
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Box)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentSplit)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Data.Rat.Fraction.Compatibility
variable {columns rows : Nat} {geometry : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry columns rows}
  {cuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts geometry}
  {box : Purelib.Riemann.Normalization.InverseRootPolynomial.Box}

/-- Select a point's vertical or horizontal rational coordinate. -/
@[expose] def axisCoordinate (vertical : Bool) (point : InverseRootPolynomial.Gaussian) : Coordinate :=
  if vertical then point.im else point.re

/-- Selecting either coordinate commutes with the original affine segment interpolation.

The Boolean axis selects the retained real or imaginary component. Both
components use the same original endpoints and rational parameter. -/
theorem axis_affine (vertical : Bool) (first last : InverseRootPolynomial.Gaussian) (parameter :
  InverseRootPolynomial.Coordinate) :
    axisCoordinate vertical (PreparedSegmentCuts.point first last parameter) =
      axisCoordinate vertical first + parameter * (axisCoordinate vertical last - axisCoordinate vertical first) := by
  cases vertical <;> rfl

/-- Matching a selected coordinate and its perpendicular coordinate identifies a Gaussian point.

The Boolean selector determines which retained component is real and which is imaginary.
Both scalar equalities identify the complete original pair without selecting another point. -/
theorem point_from_axes {left right : InverseRootPolynomial.Gaussian} (vertical : Bool)
    (along : axisCoordinate vertical left = axisCoordinate vertical right)
    (across : axisCoordinate (!vertical) left = axisCoordinate (!vertical) right) : left = right := by
  cases vertical with
  | false => exact Data.Gaussian.Basic.ext along across
  | true => exact Data.Gaussian.Basic.ext across along

/-- Read the chosen retained axis interval list from the observation mesh. -/
@[expose] def axisIntervals (mesh : RectangularObservationMesh.ObservationMesh cuts box) (vertical : Bool) : List
  Interval :=
  if vertical then mesh.partition.y.intervals else mesh.partition.x.intervals

/-- A retained observation point cannot lie strictly inside any chosen axis interval.

The selected horizontal or vertical partition retains the original observation point coordinate. Its cut certificate
excludes that coordinate from every retained interval interior. -/
theorem axis_cut_outside (mesh : RectangularObservationMesh.ObservationMesh cuts box) (vertical : Bool)
    {interval : PreparedAxisPartitions.Interval} (member : interval ∈ Geometry.Rectangle.SourceIntervals.axisIntervals
      mesh vertical)
    {point : InverseRootPolynomial.Gaussian} (present : point ∈ mesh.points) :
    Geometry.Rectangle.SourceIntervals.axisCoordinate vertical point ≤ interval.lower ∨ interval.upper ≤
      Geometry.Rectangle.SourceIntervals.axisCoordinate vertical point := by
  cases vertical with
  | false => exact mesh.partition.x.cut_outside member (Map.mem_map_of_mem (f := fun point => point.re) present)
  | true => exact mesh.partition.y.cut_outside member (Map.mem_map_of_mem (f := fun point => point.im) present)

/-- The exact affine relation between a parameter interval and a physical axis interval.

The two alternatives retain the nonzero velocity's sign and the appropriate endpoint equations in either orientation. -/
@[expose] def AxisCorrespondence (vertical : Bool) (first last : InverseRootPolynomial.Gaussian) (range physical :
  PreparedAxisPartitions.Interval) : Prop :=
  let origin := Geometry.Rectangle.SourceIntervals.axisCoordinate vertical first
  let velocity := Geometry.Rectangle.SourceIntervals.axisCoordinate vertical last - origin
  (0 < velocity ∧ origin + range.lower * velocity = physical.lower ∧ origin + range.upper * velocity = physical.upper) ∨
    (velocity < 0 ∧ origin + range.lower * velocity = physical.upper ∧ origin + range.upper * velocity = physical.lower)

/-- A positive affine velocity reflects weak coordinate order back to parameter order.

The strictly positive retained velocity permits order reflection after removing the common origin. Both affine readings
use this same velocity. -/
private theorem affine_le {origin velocity first last : InverseRootPolynomial.Coordinate} (positive : 0 < velocity)
    (bound : origin + first * velocity ≤ origin + last * velocity) : first ≤ last := by
  apply Rat.Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := velocity) _ positive
  apply Rat.Fraction.Order.Arithmetic.le_of_add_le_add_right_direct (c := origin)
  rw [Rat.Fraction.Field.add_comm (first * velocity), Rat.Fraction.Field.add_comm (last * velocity)]
  exact bound

/-- A negative affine velocity reflects reversed coordinate order back to parameter order.

Negating both readings gives a strictly positive velocity while retaining the original origin and parameters. Positive
order reflection then gives the stated reversed comparison. -/
private theorem affine_le_reverse {origin velocity first last : InverseRootPolynomial.Coordinate} (negative : velocity <
  0)
    (bound : origin + last * velocity ≤ origin + first * velocity) : first ≤ last := by
  have positive : 0 < -velocity := by simpa only [neg_zero, -eq_self, -iff_self] using
    Rat.Fraction.Order.Arithmetic.neg_lt_neg_direct negative
  have reversed := Rat.Fraction.Order.Arithmetic.neg_le_neg_direct bound
  have equal (parameter : InverseRootPolynomial.Coordinate) : -(origin + parameter * velocity) = -origin + parameter *
    (-velocity) := by ring1
  rw [equal, equal] at reversed
  exact Geometry.Rectangle.SourceIntervals.affine_le positive reversed

/-- Transport an outside-interval comparison from the physical coordinate to its exact affine parameter interval.

The original correspondence records the sign of the nonzero velocity and both endpoint equations. Each sign branch
transports the actual comparison to the matching parameter endpoint. -/
theorem parameter_outside {vertical : Bool} {first last : InverseRootPolynomial.Gaussian} {range physical :
  PreparedAxisPartitions.Interval}
    (correspondence : Geometry.Rectangle.SourceIntervals.AxisCorrespondence vertical first last range physical)
      (parameter : InverseRootPolynomial.Coordinate)
    (outside : Geometry.Rectangle.SourceIntervals.axisCoordinate vertical (PreparedSegmentCuts.point first last
      parameter) ≤ physical.lower ∨
      physical.upper ≤ Geometry.Rectangle.SourceIntervals.axisCoordinate vertical (PreparedSegmentCuts.point first last
        parameter)) :
    parameter ≤ range.lower ∨ range.upper ≤ parameter := by
  have projected := axis_affine vertical first last parameter
  rw [projected] at outside
  rcases correspondence with ⟨positive, lower, upper⟩ | ⟨negative, lower, upper⟩
  · rw [← lower, ← upper] at outside
    exact outside.elim (fun bound => Or.inl (Geometry.Rectangle.SourceIntervals.affine_le positive bound)) (fun bound =>
      Or.inr (Geometry.Rectangle.SourceIntervals.affine_le positive bound))
  · rw [← upper, ← lower] at outside
    exact outside.elim (fun bound => Or.inr (Geometry.Rectangle.SourceIntervals.affine_le_reverse negative bound))
      (fun bound => Or.inl (Geometry.Rectangle.SourceIntervals.affine_le_reverse negative bound))

/-- Locate the original source piece containing a retained physical side interval.

The exact affine correspondence transports the mesh's no-crossing certificate to the source parameter interval. The
supplied split and its cached points provide the selected piece and endpoint containment witnesses. -/
@[expose] def locateSourceInterval (mesh : RectangularObservationMesh.ObservationMesh cuts box)
    {sourceColumns sourceRows : Nat} {sourceGeometry : RectangularInverseModels.Geometry sourceColumns sourceRows}
    {sourceCuts : RectangularSegmentSplitting.GridCuts sourceGeometry} {first last : InverseRootPolynomial.Gaussian}
    (split : RectangularSegmentSplitting.SegmentSplit sourceCuts first last)
    (retained : ∀ point ∈ split.points, point ∈ mesh.points)
    (vertical : Bool) (physical : PreparedAxisPartitions.Interval) (member : physical ∈
      Geometry.Rectangle.SourceIntervals.axisIntervals mesh vertical)
    (range : PreparedAxisPartitions.Interval) (within : 0 ≤ range.lower ∧ range.upper ≤ 1)
    (correspondence : Geometry.Rectangle.SourceIntervals.AxisCorrespondence vertical first last range physical) :
      RectangularSegmentRefinement.Subinterval split range :=
  RectangularSegmentRefinement.locateInterval split range within (fun parameter present =>
    Geometry.Rectangle.SourceIntervals.parameter_outside correspondence parameter
    (Geometry.Rectangle.SourceIntervals.axis_cut_outside mesh vertical member (retained _
      (RectangularSegmentRefinement.coordinate_point_mem split present))))

/-- Adjacent retained intervals on either mesh axis share their original endpoint.

The selected partition keeps the original index values and retained bounds; its consecutive certificate identifies the
common endpoint. -/
public theorem axis_consecutive (mesh : RectangularObservationMesh.ObservationMesh cuts box) (vertical : Bool)
    (before after : Fin (SourceIntervals.axisIntervals mesh vertical).length)
    (next : after.val = before.val + 1) :
    ((SourceIntervals.axisIntervals mesh vertical)[after.val]'after.isLt).lower =
      ((SourceIntervals.axisIntervals mesh vertical)[before.val]'before.isLt).upper := by
  have bound : before.val + 1 < (SourceIntervals.axisIntervals mesh vertical).length := next ▸ after.isLt
  cases vertical with
  | false =>
    have equal := mesh.partition.x.consecutive before.val bound
    simpa only [← next, SourceIntervals.axisIntervals, if_pos (rfl : true = true), if_neg Bool.false_ne_true, -eq_self,
      -iff_self] using equal.symm
  | true =>
    have equal := mesh.partition.y.consecutive before.val bound
    simpa only [← next, SourceIntervals.axisIntervals, if_pos (rfl : true = true), if_neg Bool.false_ne_true, -eq_self,
      -iff_self] using equal.symm

end Purelib.Geometry.Rectangle.SourceIntervals

end
