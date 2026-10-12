module
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularObservationOwners
import Purelib.Topology.Polygon.Stokes

import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
public import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Geometry.Rectangle.Partition.RectangularOverlapGeometry

@[expose] public section

/-! Matching proper rectangles have the same retained model owner. Their
subdivided sides and corner values therefore agree exactly on one bank. -/
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Normalization.RectangularInverseModels (Axis)
namespace Purelib.Riemann.Readings.RectangularObservationOwnerCoherence
open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian Coordinate)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Readings.RectangularObservationOwners (BoxOwner)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)

open Purelib.Geometry in
/-- Two axis intervals containing the same proper subinterval have the same retained owner index. -/
private theorem axis_owner {steps : Nat} (axis : Axis steps) (first last : Fin (steps + 1))
    {lower upper : Coordinate} (proper : lower < upper)
    (firstBounds : axis.coordinates first.castSucc ≤ lower ∧ upper ≤ axis.coordinates first.succ)
    (lastBounds : axis.coordinates last.castSucc ≤ lower ∧ upper ≤ axis.coordinates last.succ) : first = last := by
  rcases Nat.lt_trichotomy first.val last.val with before | equal | after
  · have separated := Rectangle.Partition.RectangularOverlapGeometry.Axis.coordinate_mono axis first.succ last.castSucc
      (Nat.succ_le_of_lt before)
    exact (not_lt_of_ge (firstBounds.2.trans (separated.trans lastBounds.1)) proper).elim
  · exact Fin.ext equal
  · have separated := Rectangle.Partition.RectangularOverlapGeometry.Axis.coordinate_mono axis last.succ first.castSucc
      (Nat.succ_le_of_lt after)
    exact (not_lt_of_ge (lastBounds.2.trans (separated.trans firstBounds.1)) proper).elim

/-- Two retained model owners of the same proper rectangle have equal column and row indices. -/
theorem BoxOwner.indices_eq {columns rows : Nat} {geometry : Geometry columns rows} {box : Box}
    (first last : BoxOwner geometry box) (proper : box.Proper) :
    first.column = last.column ∧ first.row = last.row :=
  ⟨axis_owner geometry.x first.column last.column proper.1
      ⟨first.refines.1, first.refines.2.1⟩ ⟨last.refines.1, last.refines.2.1⟩,
    axis_owner geometry.y first.row last.row proper.2 first.refines.2.2 last.refines.2.2⟩

namespace ObservationMesh
variable {columns rows : Nat} {geometry : Geometry columns rows}
  {firstCuts lastCuts : GridCuts geometry} {firstBox lastBox : Box}
  (first : ObservationMesh firstCuts firstBox) (last : ObservationMesh lastCuts lastBox)

open Purelib.Geometry in
/-- Matching actual partition intervals identify the two retained cell owner indices. -/
theorem ownerAt_indices_eq
    (firstColumn : Fin first.partition.x.intervals.length) (firstRow : Fin first.partition.y.intervals.length)
    (lastColumn : Fin last.partition.x.intervals.length) (lastRow : Fin last.partition.y.intervals.length)
    (horizontal : first.partition.x.intervals[firstColumn.val]'firstColumn.isLt =
      last.partition.x.intervals[lastColumn.val]'lastColumn.isLt)
    (vertical : first.partition.y.intervals[firstRow.val]'firstRow.isLt =
      last.partition.y.intervals[lastRow.val]'lastRow.isLt) :
    (first.ownerAt firstColumn firstRow).column = (last.ownerAt lastColumn lastRow).column ∧
      (first.ownerAt firstColumn firstRow).row = (last.ownerAt lastColumn lastRow).row := by
  let retained := last.ownerAt lastColumn lastRow
  let transported : BoxOwner geometry (Rectangle.Partition.PreparedRectangleCuts.intervalBox
      (first.partition.x.intervals[firstColumn.val]'firstColumn.isLt)
      (first.partition.y.intervals[firstRow.val]'firstRow.isLt)) :=
    ⟨retained.column, retained.row, (congrArg₂ Rectangle.Partition.PreparedRectangleCuts.intervalBox horizontal
      vertical).symm ▸ retained.refines⟩
  exact BoxOwner.indices_eq (first.ownerAt firstColumn firstRow) transported
    ⟨(first.partition.x.intervals[firstColumn.val]'firstColumn.isLt).ordered,
      (first.partition.y.intervals[firstRow.val]'firstRow.isLt).ordered⟩

section
open Purelib.Riemann
/-- Matching intervals and depths identify all four actual subdivided cell sides.

Owner-index equality uses the same original value bank in both retained observation meshes. -/
theorem cellSides_eq_of_intervals
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint)
    (firstColumn : Fin first.partition.x.intervals.length) (firstRow : Fin first.partition.y.intervals.length)
    (lastColumn : Fin last.partition.x.intervals.length) (lastRow : Fin last.partition.y.intervals.length)
    (horizontal : first.partition.x.intervals[firstColumn.val]'firstColumn.isLt =
      last.partition.x.intervals[lastColumn.val]'lastColumn.isLt)
    (vertical : first.partition.y.intervals[firstRow.val]'firstRow.isLt =
      last.partition.y.intervals[lastRow.val]'lastRow.isLt)
    (depth : first.depth = last.depth) :
    first.cellSides values firstColumn firstRow = last.cellSides values lastColumn lastRow := by
  have owners := ownerAt_indices_eq first last firstColumn firstRow lastColumn lastRow horizontal vertical
  dsimp only [Meshes.RectangularObservationMesh.ObservationMesh.cellSides]
  simp only [Fin.getElem_fin]
  rw [owners.1, owners.2, horizontal, vertical, depth]

/-- Matching partition intervals identify all four retained corner values.

The equality preserves the original owners and endpoint values used by perimeter joining chords. -/
theorem cornerGrid_eq_of_intervals
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint)
    (firstColumn : Fin (first.boundaryColumns + 1)) (firstRow : Fin (first.boundaryRows + 1))
    (lastColumn : Fin (last.boundaryColumns + 1)) (lastRow : Fin (last.boundaryRows + 1))
    (horizontal : first.partition.x.intervals[(Fin.cast first.boundaryColumns_eq firstColumn).val]'(Fin.cast
      first.boundaryColumns_eq firstColumn).isLt =
      last.partition.x.intervals[(Fin.cast last.boundaryColumns_eq lastColumn).val]'(Fin.cast last.boundaryColumns_eq
        lastColumn).isLt)
    (vertical : first.partition.y.intervals[(Fin.cast first.boundaryRows_eq firstRow).val]'(Fin.cast
      first.boundaryRows_eq firstRow).isLt =
      last.partition.y.intervals[(Fin.cast last.boundaryRows_eq lastRow).val]'(Fin.cast last.boundaryRows_eq
        lastRow).isLt) :
    first.cornerGrid values firstColumn firstRow = last.cornerGrid values lastColumn lastRow := by
  have owners := ownerAt_indices_eq first last (Fin.cast first.boundaryColumns_eq firstColumn)
    (Fin.cast first.boundaryRows_eq firstRow) (Fin.cast last.boundaryColumns_eq lastColumn)
    (Fin.cast last.boundaryRows_eq lastRow) horizontal vertical
  dsimp only [Meshes.RectangularObservationMesh.ObservationMesh.cornerGrid]
  simp only [Fin.getElem_fin]
  rw [owners.1, owners.2, horizontal, vertical]

end

namespace ClippedAssembly

/-- Matching cells have equal cached sides and corners in their original clipped assemblies.

Exact interval and depth equalities transport both side-area readings and all four endpoint values without reevaluating
the primitive bank. -/
theorem cell_eq_of_intervals
    {values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint}
    (firstAssembly : ClippedAssembly first values) (lastAssembly : ClippedAssembly last values)
    (firstColumn : Fin (first.boundaryColumns + 1)) (firstRow : Fin (first.boundaryRows + 1))
    (lastColumn : Fin (last.boundaryColumns + 1)) (lastRow : Fin (last.boundaryRows + 1))
    (horizontal : first.partition.x.intervals[(Fin.cast first.boundaryColumns_eq firstColumn).val]'(Fin.cast
      first.boundaryColumns_eq firstColumn).isLt =
      last.partition.x.intervals[(Fin.cast last.boundaryColumns_eq lastColumn).val]'(Fin.cast last.boundaryColumns_eq
        lastColumn).isLt)
    (vertical : first.partition.y.intervals[(Fin.cast first.boundaryRows_eq firstRow).val]'(Fin.cast
      first.boundaryRows_eq firstRow).isLt =
      last.partition.y.intervals[(Fin.cast last.boundaryRows_eq lastRow).val]'(Fin.cast last.boundaryRows_eq
        lastRow).isLt)
    (depth : first.depth = last.depth) :
    firstAssembly.sides firstColumn firstRow = lastAssembly.sides lastColumn lastRow ∧
      firstAssembly.corners firstColumn firstRow = lastAssembly.corners lastColumn lastRow := by
  constructor
  · exact (firstAssembly.sides_eq firstColumn firstRow).trans
      ((cellSides_eq_of_intervals first last values (Fin.cast first.boundaryColumns_eq firstColumn)
        (Fin.cast first.boundaryRows_eq firstRow) (Fin.cast last.boundaryColumns_eq lastColumn)
        (Fin.cast last.boundaryRows_eq lastRow) horizontal vertical depth).trans
          (lastAssembly.sides_eq lastColumn lastRow).symm)
  · exact (firstAssembly.corners_eq firstColumn firstRow).trans
      ((cornerGrid_eq_of_intervals first last values firstColumn firstRow lastColumn lastRow horizontal vertical).trans
        (lastAssembly.corners_eq lastColumn lastRow).symm)

end ClippedAssembly
end ObservationMesh
end Purelib.Riemann.Readings.RectangularObservationOwnerCoherence
