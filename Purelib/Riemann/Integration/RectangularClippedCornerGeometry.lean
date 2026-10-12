module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Topology.Polygon.Stokes

public import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Geometry.Rectangle.Partition.PreparedAxisAdjacency
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Readings.RectangularObservationOwners
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Geometry.Rational.Box.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-! The four retained owners at an interior clipped-grid junction all
contain the identical physical point. -/
namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

open Purelib.Data.Rat

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)

variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry} {box :
  Purelib.Geometry.Rational.Box}

section
open Purelib.Geometry.Rectangle.Partition
/-- Adjacent retained horizontal intervals meet at the same original coordinate. -/
theorem x_next (mesh : ObservationMesh cuts
  box) (column : Fin mesh.boundaryColumns) :
    mesh.partition.x.intervals[Fin.cast mesh.boundaryColumns_eq column.castSucc].upper =
      mesh.partition.x.intervals[Fin.cast mesh.boundaryColumns_eq column.succ].lower := by
  exact Geometry.Rectangle.AxisPartition.Adjacency.consecutive mesh.partition.x column.val (by
      rw [← mesh.boundaryColumns_eq];
      omega)

/-- Adjacent retained vertical intervals meet at the same original coordinate. -/
theorem y_next (mesh : ObservationMesh cuts
  box) (row : Fin mesh.boundaryRows) :
    mesh.partition.y.intervals[Fin.cast mesh.boundaryRows_eq row.castSucc].upper =
      mesh.partition.y.intervals[Fin.cast mesh.boundaryRows_eq row.succ].lower := by
  exact Geometry.Rectangle.AxisPartition.Adjacency.consecutive mesh.partition.y row.val (by
      rw [← mesh.boundaryRows_eq];
      omega)

end

/-- The exact common coordinate of four neighboring original observation cells.

The upper endpoints of the original horizontal and vertical intervals determine this coordinate. Their retained casts
identify the same bounded mesh indices. -/
@[expose] def junctionPoint (mesh :
  ObservationMesh cuts box) (column : Fin mesh.boundaryColumns) (row : Fin mesh.boundaryRows) : Gaussian :=
  ⟨mesh.partition.x.intervals[Fin.cast mesh.boundaryColumns_eq column.castSucc].upper,
    mesh.partition.y.intervals[Fin.cast mesh.boundaryRows_eq row.castSucc].upper⟩

/-- Retain the original model-cell owner of the common junction in the selected adjacent quadrant.

The right and above flags select the exact neighboring interval indices; their adjacency and refinement certificates
prove containment of the same junction point. -/
@[expose] def junctionOwner (mesh :
  ObservationMesh cuts box) (column : Fin mesh.boundaryColumns) (row : Fin mesh.boundaryRows)
    (right above : Bool) : OwnedVertex geometry := by
  let xIndex := Fin.cast mesh.boundaryColumns_eq (if right then column.succ else column.castSucc)
  let yIndex := Fin.cast mesh.boundaryRows_eq (if above then row.succ else row.castSucc)
  let owner := mesh.ownerAt xIndex yIndex
  refine ⟨owner.column, owner.row, mesh.junctionPoint column row, owner.refines.contains ?_⟩
  change (mesh.partition.x.intervals[xIndex.val]'xIndex.isLt).lower ≤ (mesh.junctionPoint column row).re ∧
    (mesh.junctionPoint column row).re ≤ (mesh.partition.x.intervals[xIndex.val]'xIndex.isLt).upper ∧
    (mesh.partition.y.intervals[yIndex.val]'yIndex.isLt).lower ≤ (mesh.junctionPoint column row).im ∧
    (mesh.junctionPoint column row).im ≤ (mesh.partition.y.intervals[yIndex.val]'yIndex.isLt).upper
  have horizontal : (mesh.partition.x.intervals[xIndex.val]'xIndex.isLt).lower ≤ (mesh.junctionPoint column row).re ∧
      (mesh.junctionPoint column row).re ≤ (mesh.partition.x.intervals[xIndex.val]'xIndex.isLt).upper := by
    cases right with
    | false => exact ⟨(mesh.partition.x.intervals[xIndex.val]'xIndex.isLt).ordered.le, le_rfl⟩
    | true =>
        change (mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq column.succ).val]'(Fin.cast
          mesh.boundaryColumns_eq column.succ).isLt).lower ≤
            (mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq column.castSucc).val]'(Fin.cast
              mesh.boundaryColumns_eq column.castSucc).isLt).upper ∧
            (mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq column.castSucc).val]'(Fin.cast
              mesh.boundaryColumns_eq column.castSucc).isLt).upper ≤
              (mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq column.succ).val]'(Fin.cast
                mesh.boundaryColumns_eq column.succ).isLt).upper
        constructor
        · exact Eq.mp (congrArg (fun lower => lower ≤ (mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq
            column.castSucc).val]'(Fin.cast mesh.boundaryColumns_eq column.castSucc).isLt).upper)
            (mesh.x_next column)) (Fraction.Order.Basic.le_refl _)
        · exact Eq.mpr (congrArg (fun lower => lower ≤ (mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq
            column.succ).val]'(Fin.cast mesh.boundaryColumns_eq column.succ).isLt).upper)
            (mesh.x_next column)) (mesh.partition.x.intervals[xIndex.val]'xIndex.isLt).ordered.le
  have vertical : (mesh.partition.y.intervals[yIndex.val]'yIndex.isLt).lower ≤ (mesh.junctionPoint column row).im ∧
      (mesh.junctionPoint column row).im ≤ (mesh.partition.y.intervals[yIndex.val]'yIndex.isLt).upper := by
    cases above with
    | false => exact ⟨(mesh.partition.y.intervals[yIndex.val]'yIndex.isLt).ordered.le, le_rfl⟩
    | true =>
        change (mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq row.succ).val]'(Fin.cast mesh.boundaryRows_eq
          row.succ).isLt).lower ≤
            (mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq row.castSucc).val]'(Fin.cast mesh.boundaryRows_eq
              row.castSucc).isLt).upper ∧
            (mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq row.castSucc).val]'(Fin.cast mesh.boundaryRows_eq
              row.castSucc).isLt).upper ≤
              (mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq row.succ).val]'(Fin.cast mesh.boundaryRows_eq
                row.succ).isLt).upper
        constructor
        · exact Eq.mp (congrArg (fun lower => lower ≤ (mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq
            row.castSucc).val]'(Fin.cast mesh.boundaryRows_eq row.castSucc).isLt).upper)
            (mesh.y_next row)) (Fraction.Order.Basic.le_refl _)
        · exact Eq.mpr (congrArg (fun lower => lower ≤ (mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq
            row.succ).val]'(Fin.cast mesh.boundaryRows_eq row.succ).isLt).upper)
            (mesh.y_next row)) (mesh.partition.y.intervals[yIndex.val]'yIndex.isLt).ordered.le
  exact ⟨horizontal.1, horizontal.2, vertical⟩

/-- Every retained quadrant owner reads back the exact original common junction point. -/
theorem junctionOwner_point (mesh :
  ObservationMesh cuts box) (column : Fin mesh.boundaryColumns) (row : Fin mesh.boundaryRows)
    (right above : Bool) : (mesh.junctionOwner column row right above).point = mesh.junctionPoint column row := rfl

open Purelib.Riemann.Meshes in
/-- The four cached cell-corner values read the same original junction through their respective owners.

The exact horizontal and vertical adjacency equations identify coordinates while preserving all four original model-cell
indices. -/
theorem corner_junction (mesh : ObservationMesh
  cuts box)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint)
    (column : Fin mesh.boundaryColumns) (row : Fin mesh.boundaryRows) :
    let value := fun right above =>
      let owner := mesh.junctionOwner column row right above
      values owner.column owner.row owner.point
    (mesh.cornerGrid values column.castSucc row.castSucc).upperRight = value false false ∧
    (mesh.cornerGrid values column.castSucc row.succ).lowerRight = value false true ∧
    (mesh.cornerGrid values column.succ row.succ).lowerLeft = value true true ∧
    (mesh.cornerGrid values column.succ row.castSucc).upperLeft = value true false := by
  dsimp only [RectangularObservationMesh.ObservationMesh.cornerGrid,
    RectangularObservationMesh.ObservationMesh.junctionOwner, RectangularObservationMesh.ObservationMesh.junctionPoint,
    Bool.false_eq_true, reduceIte]
  rw [mesh.x_next column, mesh.y_next row]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

end
