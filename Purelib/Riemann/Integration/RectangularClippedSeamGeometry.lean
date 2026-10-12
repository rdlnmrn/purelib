module
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Geometry.Rational.Affine
import Purelib.Riemann.Periods.BilinearGridBoundary
public import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularObservationOwners
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps

import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
import Purelib.Riemann.Integration.RectangularClippedCornerGeometry
public import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

/-! Actual adjacent clipped cells supply both owners of each corrected seam.
The ribbon retains the cross-chart endpoint terms of the grid identity. -/
section

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open Purelib.Riemann.Readings.RectangularObservationOwners (BoxOwner)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (line_zero line_one)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry} {box :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Box}

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

/-- The exact paired vertical segment between horizontally adjacent original observation cells.

Both retained model owners contain the shared segment, with the original horizontal interval adjacency identifying its
common coordinate. -/
def horizontalSeamPiece (mesh : ObservationMesh
  cuts box)
    (column : Fin mesh.boundaryColumns) (row : Fin (mesh.boundaryRows + 1)) : PairedSegmentPiece geometry geometry := by
  let left := mesh.ownerAt (Fin.cast mesh.boundaryColumns_eq column.castSucc) (Fin.cast mesh.boundaryRows_eq row)
  let right := mesh.ownerAt (Fin.cast mesh.boundaryColumns_eq column.succ) (Fin.cast mesh.boundaryRows_eq row)
  exact left.verticalPiece right rfl rfl
    mesh.partition.x.intervals[Fin.cast mesh.boundaryColumns_eq column.castSucc].upper
    ⟨mesh.partition.x.intervals[Fin.cast mesh.boundaryColumns_eq column.castSucc].ordered.le, le_rfl⟩
    (by
      change mesh.partition.x.intervals[Fin.cast mesh.boundaryColumns_eq column.succ].lower ≤
          mesh.partition.x.intervals[Fin.cast mesh.boundaryColumns_eq column.castSucc].upper ∧
        mesh.partition.x.intervals[Fin.cast mesh.boundaryColumns_eq column.castSucc].upper ≤
          mesh.partition.x.intervals[Fin.cast mesh.boundaryColumns_eq column.succ].upper
      rw [mesh.x_next column]
      exact ⟨le_rfl, mesh.partition.x.intervals[Fin.cast mesh.boundaryColumns_eq column.succ].ordered.le⟩)

/-- The exact paired horizontal segment between vertically adjacent original observation cells.

Both retained model owners contain the shared segment, with the original vertical interval adjacency identifying its
common coordinate. -/
def verticalSeamPiece (mesh : ObservationMesh
  cuts box)
    (column : Fin (mesh.boundaryColumns + 1)) (row : Fin mesh.boundaryRows) : PairedSegmentPiece geometry geometry := by
  let above := mesh.ownerAt (Fin.cast mesh.boundaryColumns_eq column) (Fin.cast mesh.boundaryRows_eq row.succ)
  let below := mesh.ownerAt (Fin.cast mesh.boundaryColumns_eq column) (Fin.cast mesh.boundaryRows_eq row.castSucc)
  exact above.horizontalPiece below rfl rfl
    mesh.partition.y.intervals[Fin.cast mesh.boundaryRows_eq row.castSucc].upper
    (by
      change mesh.partition.y.intervals[Fin.cast mesh.boundaryRows_eq row.succ].lower ≤
          mesh.partition.y.intervals[Fin.cast mesh.boundaryRows_eq row.castSucc].upper ∧
        mesh.partition.y.intervals[Fin.cast mesh.boundaryRows_eq row.castSucc].upper ≤
          mesh.partition.y.intervals[Fin.cast mesh.boundaryRows_eq row.succ].upper
      rw [mesh.y_next row]
      exact ⟨le_rfl, mesh.partition.y.intervals[Fin.cast mesh.boundaryRows_eq row.succ].ordered.le⟩)
    ⟨mesh.partition.y.intervals[Fin.cast mesh.boundaryRows_eq row.castSucc].ordered.le, le_rfl⟩

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

section

variable {mesh : ObservationMesh cuts box}
    {values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint}

open Purelib.Geometry.Rational
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Polynomial.Rectangle
open Purelib.Riemann.Meshes
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings
open Purelib.Topology.Polygon

namespace Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly

/-- The original horizontal seam minus its endpoint correction equals the exact paired dyadic ribbon difference.

The retained vertical seam segment supplies both original model owners and the common depth; cached sides and corners
preserve the oriented primitive readbacks. -/
theorem
  horizontal_eq_dyadic
  (assembly : ClippedAssembly mesh values)
    (column : Fin mesh.boundaryColumns) (row : Fin (mesh.boundaryRows + 1)) :
    let piece := mesh.horizontalSeamPiece column row
    let point := fun parameter => Affine.line piece.first (piece.last - piece.first) parameter
    Boundary.Assembly.horizontalSeam (fun column row => assembly.sides column row) column row -
      BilinearGridBoundary.horizontalEndpoint assembly.corners column row =
      DyadicBilinearBoundaryRibbon.dyadicDifference
        (fun parameter => values piece.leftColumn piece.leftRow (point parameter))
        (fun parameter => values piece.rightColumn piece.rightRow (point parameter)) mesh.depth 0 1 := by
  dsimp only
  simp only [Boundary.Assembly.horizontalSeam, assembly.sides_eq,
    BilinearGridBoundary.horizontalEndpoint, assembly.corners_eq, RectangularObservationMesh.ObservationMesh.sideGrid,
      RectangularObservationMesh.ObservationMesh.cellSides, RectangularObservationMesh.ObservationMesh.cornerGrid]
  rw [← mesh.x_next column]
  rw [DyadicBilinearBoundaryRibbon.verticalBoundary_eq_lineArea,
    DyadicBilinearBoundaryRibbon.verticalBoundary_eq_lineArea]
  dsimp only [RectangularObservationMesh.ObservationMesh.horizontalSeamPiece,
    RectangularObservationOwners.BoxOwner.verticalPiece, PreparedRectangleCuts.intervalBox]
  rw [DyadicBilinearBoundaryRibbon.dyadicDifference, line_one, line_zero]
  simp only [Stokes.edgeArea, Stokes.PrimitivePoint.sub]
  ring1

/-- The original vertical seam minus its endpoint correction equals the exact paired dyadic ribbon difference.

The retained horizontal seam segment supplies both original model owners and the common depth; cached sides and corners
preserve the oriented primitive readbacks. -/
theorem
  vertical_eq_dyadic
  (assembly : ClippedAssembly mesh values)
    (column : Fin (mesh.boundaryColumns + 1)) (row : Fin mesh.boundaryRows) :
    let piece := mesh.verticalSeamPiece column row
    let point := fun parameter => Affine.line piece.first (piece.last - piece.first) parameter
    Boundary.Assembly.verticalSeam (fun column row => assembly.sides column row) column row -
      BilinearGridBoundary.verticalEndpoint assembly.corners column row =
      DyadicBilinearBoundaryRibbon.dyadicDifference
        (fun parameter => values piece.leftColumn piece.leftRow (point parameter))
        (fun parameter => values piece.rightColumn piece.rightRow (point parameter)) mesh.depth 0 1 := by
  dsimp only
  simp only [Boundary.Assembly.verticalSeam, assembly.sides_eq,
    BilinearGridBoundary.verticalEndpoint, assembly.corners_eq, RectangularObservationMesh.ObservationMesh.sideGrid,
      RectangularObservationMesh.ObservationMesh.cellSides, RectangularObservationMesh.ObservationMesh.cornerGrid]
  rw [← mesh.y_next row]
  rw [DyadicBilinearBoundaryRibbon.horizontalBoundary_eq_lineArea,
    DyadicBilinearBoundaryRibbon.horizontalBoundary_eq_lineArea]
  dsimp only [RectangularObservationMesh.ObservationMesh.verticalSeamPiece,
    RectangularObservationOwners.BoxOwner.horizontalPiece, PreparedRectangleCuts.intervalBox]
  rw [DyadicBilinearBoundaryRibbon.dyadicDifference, line_one, line_zero]
  simp only [Stokes.edgeArea, Stokes.PrimitivePoint.sub]
  ring1

end Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly

end
end
