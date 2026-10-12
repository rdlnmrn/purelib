module
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Data.Gaussian.Basic

public import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Integration.RectangularExteriorCornerOwners
public import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Geometry.Rectangle.Partition.RectangularOverlapGeometry

@[expose] public section

/-! At an outer corner, containment determines the model cell uniquely.
Thus independently retained owners read the same primitive exactly. -/
namespace Purelib.Riemann.Readings.RectangularOuterCornerReadings

open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial Box Coordinate)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Normalization.RectangularInverseModels (Axis Geometry Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Geometry.Rectangle.Partition.RectangularOverlapGeometry.Axis (coordinate_lt)

open Purelib.Geometry.Rectangle.Partition.RectangularOverlapGeometry in
/-- The strictly ordered retained axis coordinates determine their indices uniquely. -/
private theorem coordinate_injective {steps : Nat} (axis : Axis steps)
    (first last : Fin (steps + 2)) (equal : axis.coordinates first = axis.coordinates last) : first = last := by
  rcases Nat.lt_trichotomy first.val last.val with before | same | after
  · exact (not_lt_of_ge equal.ge (Axis.coordinate_lt axis first last before)).elim
  · exact Fin.ext same
  · exact (not_lt_of_ge equal.le (Axis.coordinate_lt axis last first after)).elim

/-- Two contained axis intervals owning the same outer endpoint have the same retained cell index.

Both intervals stay within the supplied outer bounds, and the selected lower or upper endpoint lies in each interval. -/
private theorem endpoint_owner {steps : Nat} (axis : Axis steps) (first last : Fin (steps + 1))
    {lower upper : Coordinate} (high : Bool)
    (firstBounds : lower ≤ axis.coordinates first.castSucc ∧ axis.coordinates first.succ ≤ upper)
    (lastBounds : lower ≤ axis.coordinates last.castSucc ∧ axis.coordinates last.succ ≤ upper)
    (firstInside : axis.coordinates first.castSucc ≤ (if high then upper else lower) ∧
      (if high then upper else lower) ≤ axis.coordinates first.succ)
    (lastInside : axis.coordinates last.castSucc ≤ (if high then upper else lower) ∧
      (if high then upper else lower) ≤ axis.coordinates last.succ) : first = last := by
  cases high
  · have firstEq := le_antisymm firstInside.1 firstBounds.1
    have lastEq := le_antisymm lastInside.1 lastBounds.1
    exact Fin.ext (congrArg (fun index : Fin (steps + 2) => index.val) (coordinate_injective axis first.castSucc
      last.castSucc (firstEq.trans lastEq.symm)))
  · have firstEq := le_antisymm firstBounds.2 firstInside.2
    have lastEq := le_antisymm lastBounds.2 lastInside.2
    exact Fin.ext (Nat.succ.inj (congrArg (fun index : Fin (steps + 2) => index.val) (coordinate_injective axis
      first.succ last.succ (firstEq.trans lastEq.symm))))

variable {columns rows : Nat} {geometry : Geometry columns rows} {box : Box}

open Purelib.Geometry.Rectangle.Partition in
/-- Owners of the same outer rectangle corner have the same original model column and row.

Every model cell refines that rectangle, so endpoint containment uniquely determines the two retained axis intervals. -/
theorem OwnedVertex.outer_corner_indices (first last : OwnedVertex geometry)
    (refines : ∀ column row, (geometry.box column row).Refines box) (right above : Bool)
    (firstPoint : first.point = PreparedRectangleCuts.corner box right above)
    (lastPoint : last.point = PreparedRectangleCuts.corner box right above) :
    first.column = last.column ∧ first.row = last.row := by
  have firstInside := first.contains
  have lastInside := last.contains
  rw [firstPoint] at firstInside
  rw [lastPoint] at lastInside
  have firstBounds := refines first.column first.row
  have lastBounds := refines last.column last.row
  exact ⟨endpoint_owner geometry.x first.column last.column right
    ⟨firstBounds.1, firstBounds.2.1⟩ ⟨lastBounds.1, lastBounds.2.1⟩
    ⟨firstInside.1, firstInside.2.1⟩ ⟨lastInside.1, lastInside.2.1⟩,
    endpoint_owner geometry.y first.row last.row above firstBounds.2.2 lastBounds.2.2 firstInside.2.2 lastInside.2.2⟩

open Purelib.Data in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.LinearAlgebra in
/-- An independently retained point-reading owner gives the exact original outer-corner primitive value.

Both owners lie in model cells refining the same rectangle and read the same displayed corner; uniqueness of their
column and row identifies the aligned value. -/
theorem PointReadings.outer_corner_value {polynomial numerator : Polynomial}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    {count : Nat} {points : Fin count → Gaussian.Basic.Canonical} (readings : PointReadings anchors offsets points)
    (refines : ∀ column row, (geometry.box column row).Refines box)
    (owner : OwnedVertex geometry) (index : Fin count) (right above : Bool)
    (ownerPoint : owner.point = PreparedRectangleCuts.corner box right above)
    (readingPoint : points index = PreparedRectangleCuts.corner box right above) :
    anchors.alignedValue offsets owner.column owner.row owner.point = readings.values index := by
  have point := (readings.point_eq index).trans readingPoint
  have indices := OwnedVertex.outer_corner_indices owner (readings.owners index) refines right above ownerPoint point
  rw [readings.value_eq, indices.1, indices.2, ownerPoint, point]

end Purelib.Riemann.Readings.RectangularOuterCornerReadings
