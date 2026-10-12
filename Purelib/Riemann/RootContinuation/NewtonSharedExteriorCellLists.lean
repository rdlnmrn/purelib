module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas
import Purelib.Riemann.RootContinuation.NewtonSharedExteriorBoundaryIntervals
import Purelib.Riemann.RootContinuation.NewtonSharedExteriorIntervalSpines
public import Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterEntries
import Purelib.Integration.Path.IndexedBlockReadback
import Purelib.Integration.Polynomial.Rectangle.StitchedSideRegrouping
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
public import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Riemann.Meshes.LiftedPuncturedGrid

public section

/-! Exact ordered readback of the whole-face boundary caches as the flattened
observation-piece caches, retaining every owner-specific endpoint. -/
namespace Purelib.Riemann.RootContinuation.NewtonSharedExteriorCellLists

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (surfaceMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest (BasisArcPreparations)
open Purelib.Riemann.Branches.NewtonSharedExteriorCuts (SharedExteriorCuts)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices (columns rows pieceIndex)
open Purelib.Riemann.Normalization
variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {target radius : Data.Rat.Fraction.Rational} {grid : NewtonGrid preparation
    target radius}
  {observations : ProtectedObservations original} {lifted : LiftedPuncturedGrid grid.punctured}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    grid.faces.regulars}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {partitions : SurfacePartitions observations grid} {preparations :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular domains}

open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas (Entry)

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Gaussian
section
open Purelib.Data.List
open Purelib.Integration.Path
open Purelib.Integration.Polynomial.Rectangle
open Purelib.Riemann.RootContinuation
open Purelib.Topology.Polygon
/-- Read the whole bottom cell list as flattened piece lists.

Uses the exact shared column interval spine at the first row, retaining cell sides, endpoints and indexed bounds through
the list readback. -/
theorem bottom_cells (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (depth : Nat)
    (values : Fin (((domains.get position).domain sheet).steps + 1) →
      Fin (((domains.get position).domain sheet).steps + 1) → Basic.Canonical → Stokes.PrimitivePoint) :
    let whole := (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
      depth).entries.get position
    let meshes := fun column => ((Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
      shared.surface sheet depth).get position).entries.get
      ((Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) column 0)
    ∀ (wholeAssembly : ClippedAssembly whole values)
      (pieces : (column : Fin ((Meshes.Newton.Surface.PieceIndices.columns (partitions.get position)) + 1)) →
        ClippedAssembly (meshes column) values),
      List.ofFn (ClippedPerimeterEntries.bottomCells wholeAssembly) = (List.ofFn (fun column => List.ofFn
        (ClippedPerimeterEntries.bottomCells (pieces column)))).flatten := by
  dsimp only
  intro wholeAssembly pieces
  let whole := (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
    depth).entries.get position
  let meshes := fun column => ((Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface
    sheet depth).get position).entries.get
    ((Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) column 0)
  apply IndexedBlockReadback.ofFn_flatten
    (fun index => whole.partition.x.intervals[(Fin.cast whole.boundaryColumns_eq index).val]'
      (Fin.cast whole.boundaryColumns_eq index).isLt) (ClippedPerimeterEntries.bottomCells wholeAssembly)
    (fun column index => (meshes column).partition.x.intervals[(Fin.cast (meshes column).boundaryColumns_eq index).val]'
      (Fin.cast (meshes column).boundaryColumns_eq index).isLt)
    (fun column => (ClippedPerimeterEntries.bottomCells (pieces column)))
  · rw [IndexedBlockReadback.ofFn_get_cast]
    have localKeys := OfFn.Basic.ofFn_congr (fun column =>
      IndexedBlockReadback.ofFn_get_cast (meshes column).partition.x.intervals (meshes column).boundaryColumns_eq)
    exact (NewtonSharedExteriorIntervalSpines.x_spine shared position 0 sheet depth depth).trans (congrArg List.flatten
      localKeys).symm
  · intro column localIndex wholeIndex same
    have cell := NewtonSharedExteriorBoundaryIntervals.bottom_cell shared position column sheet depth values
      wholeAssembly (pieces column) wholeIndex localIndex same
    apply StitchedSideAreas.Entry.eq_of_fields
    · exact congrArg (fun sides => sides.bottom) cell.1
    · exact congrArg (fun corners => corners.lowerLeft) cell.2
    · exact congrArg (fun corners => corners.lowerRight) cell.2

/-- Read the whole top cell list as flattened piece lists.

Uses the exact shared column interval spine at the last row, retaining cell sides, endpoints and indexed bounds through
the list readback. -/
theorem top_cells (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (depth : Nat)
    (values : Fin (((domains.get position).domain sheet).steps + 1) →
      Fin (((domains.get position).domain sheet).steps + 1) → Basic.Canonical → Stokes.PrimitivePoint) :
    let whole := (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
      depth).entries.get position
    let meshes := fun column => ((Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
      shared.surface sheet depth).get position).entries.get
      ((Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) column (Fin.last
        (Meshes.Newton.Surface.PieceIndices.rows (partitions.get position))))
    ∀ (wholeAssembly : ClippedAssembly whole values)
      (pieces : (column : Fin ((Meshes.Newton.Surface.PieceIndices.columns (partitions.get position)) + 1)) →
        ClippedAssembly (meshes column) values),
      List.ofFn (ClippedPerimeterEntries.topCells wholeAssembly) = (List.ofFn (fun column => List.ofFn
        (ClippedPerimeterEntries.topCells (pieces column)))).flatten := by
  dsimp only
  intro wholeAssembly pieces
  let whole := (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
    depth).entries.get position
  let meshes := fun column => ((Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface
    sheet depth).get position).entries.get
    ((Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) column (Fin.last
      (Meshes.Newton.Surface.PieceIndices.rows (partitions.get position))))
  apply IndexedBlockReadback.ofFn_flatten
    (fun index => whole.partition.x.intervals[(Fin.cast whole.boundaryColumns_eq index).val]'
      (Fin.cast whole.boundaryColumns_eq index).isLt) (ClippedPerimeterEntries.topCells wholeAssembly)
    (fun column index => (meshes column).partition.x.intervals[(Fin.cast (meshes column).boundaryColumns_eq index).val]'
      (Fin.cast (meshes column).boundaryColumns_eq index).isLt)
    (fun column => (ClippedPerimeterEntries.topCells (pieces column)))
  · rw [IndexedBlockReadback.ofFn_get_cast]
    have localKeys := OfFn.Basic.ofFn_congr (fun column =>
      IndexedBlockReadback.ofFn_get_cast (meshes column).partition.x.intervals (meshes column).boundaryColumns_eq)
    exact (NewtonSharedExteriorIntervalSpines.x_spine shared position (Fin.last (Meshes.Newton.Surface.PieceIndices.rows
      (partitions.get position))) sheet depth depth).trans (congrArg List.flatten localKeys).symm
  · intro column localIndex wholeIndex same
    have cell := NewtonSharedExteriorBoundaryIntervals.top_cell shared position column sheet depth values wholeAssembly
      (pieces column) wholeIndex localIndex same
    apply StitchedSideAreas.Entry.eq_of_fields
    · exact congrArg (fun sides => sides.top) cell.1
    · exact congrArg (fun corners => corners.upperLeft) cell.2
    · exact congrArg (fun corners => corners.upperRight) cell.2

/-- Read the whole left cell list as flattened piece lists.

Uses the exact shared row interval spine at the first column, retaining cell sides, endpoints and indexed bounds through
the list readback. -/
theorem left_cells (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (depth : Nat)
    (values : Fin (((domains.get position).domain sheet).steps + 1) →
      Fin (((domains.get position).domain sheet).steps + 1) → Basic.Canonical → Stokes.PrimitivePoint) :
    let whole := (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
      depth).entries.get position
    let meshes := fun row => ((Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface
      sheet depth).get position).entries.get
      ((Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) 0 row)
    ∀ (wholeAssembly : ClippedAssembly whole values)
      (pieces : (row : Fin ((Meshes.Newton.Surface.PieceIndices.rows (partitions.get position)) + 1)) → ClippedAssembly
        (meshes row) values),
      List.ofFn (ClippedPerimeterEntries.leftCells wholeAssembly) = (List.ofFn (fun row => List.ofFn
        (ClippedPerimeterEntries.leftCells (pieces row)))).flatten := by
  dsimp only
  intro wholeAssembly pieces
  let whole := (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
    depth).entries.get position
  let meshes := fun row => ((Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface
    sheet depth).get position).entries.get
    ((Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) 0 row)
  apply IndexedBlockReadback.ofFn_flatten
    (fun index => whole.partition.y.intervals[(Fin.cast whole.boundaryRows_eq index).val]'
      (Fin.cast whole.boundaryRows_eq index).isLt) (ClippedPerimeterEntries.leftCells wholeAssembly)
    (fun row index => (meshes row).partition.y.intervals[(Fin.cast (meshes row).boundaryRows_eq index).val]'
      (Fin.cast (meshes row).boundaryRows_eq index).isLt)
    (fun row => (ClippedPerimeterEntries.leftCells (pieces row)))
  · rw [IndexedBlockReadback.ofFn_get_cast]
    have localKeys := OfFn.Basic.ofFn_congr (fun row =>
      IndexedBlockReadback.ofFn_get_cast (meshes row).partition.y.intervals (meshes row).boundaryRows_eq)
    exact (NewtonSharedExteriorIntervalSpines.y_spine shared position 0 sheet depth depth).trans (congrArg List.flatten
      localKeys).symm
  · intro row localIndex wholeIndex same
    have cell := NewtonSharedExteriorBoundaryIntervals.left_cell shared position row sheet depth values wholeAssembly
      (pieces row) wholeIndex localIndex same
    apply StitchedSideAreas.Entry.eq_of_fields
    · exact congrArg (fun sides => sides.left) cell.1
    · exact congrArg (fun corners => corners.lowerLeft) cell.2
    · exact congrArg (fun corners => corners.upperLeft) cell.2

/-- Read the whole right cell list as flattened piece lists.

Uses the exact shared row interval spine at the last column, retaining cell sides, endpoints and indexed bounds through
the list readback. -/
theorem right_cells (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (depth : Nat)
    (values : Fin (((domains.get position).domain sheet).steps + 1) →
      Fin (((domains.get position).domain sheet).steps + 1) → Basic.Canonical → Stokes.PrimitivePoint) :
    let whole := (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
      depth).entries.get position
    let meshes := fun row => ((Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface
      sheet depth).get position).entries.get
      ((Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) (Fin.last
        (Meshes.Newton.Surface.PieceIndices.columns (partitions.get position))) row)
    ∀ (wholeAssembly : ClippedAssembly whole values)
      (pieces : (row : Fin ((Meshes.Newton.Surface.PieceIndices.rows (partitions.get position)) + 1)) → ClippedAssembly
        (meshes row) values),
      List.ofFn (ClippedPerimeterEntries.rightCells wholeAssembly) = (List.ofFn (fun row => List.ofFn
        (ClippedPerimeterEntries.rightCells (pieces row)))).flatten := by
  dsimp only
  intro wholeAssembly pieces
  let whole := (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
    depth).entries.get position
  let meshes := fun row => ((Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface
    sheet depth).get position).entries.get
    ((Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) (Fin.last
      (Meshes.Newton.Surface.PieceIndices.columns (partitions.get position))) row)
  apply IndexedBlockReadback.ofFn_flatten
    (fun index => whole.partition.y.intervals[(Fin.cast whole.boundaryRows_eq index).val]'
      (Fin.cast whole.boundaryRows_eq index).isLt) (ClippedPerimeterEntries.rightCells wholeAssembly)
    (fun row index => (meshes row).partition.y.intervals[(Fin.cast (meshes row).boundaryRows_eq index).val]'
      (Fin.cast (meshes row).boundaryRows_eq index).isLt)
    (fun row => (ClippedPerimeterEntries.rightCells (pieces row)))
  · rw [IndexedBlockReadback.ofFn_get_cast]
    have localKeys := OfFn.Basic.ofFn_congr (fun row =>
      IndexedBlockReadback.ofFn_get_cast (meshes row).partition.y.intervals (meshes row).boundaryRows_eq)
    exact (NewtonSharedExteriorIntervalSpines.y_spine shared position (Fin.last
      (Meshes.Newton.Surface.PieceIndices.columns (partitions.get position))) sheet depth depth).trans (congrArg
      List.flatten localKeys).symm
  · intro row localIndex wholeIndex same
    have cell := NewtonSharedExteriorBoundaryIntervals.right_cell shared position row sheet depth values wholeAssembly
      (pieces row) wholeIndex localIndex same
    apply StitchedSideAreas.Entry.eq_of_fields
    · exact congrArg (fun sides => sides.right) cell.1
    · exact congrArg (fun corners => corners.lowerRight) cell.2
    · exact congrArg (fun corners => corners.upperRight) cell.2

end

open Purelib.Integration.Polynomial.Rectangle
open Purelib.Topology.Polygon
/-- Concatenate the retained bottom piece perimeters into the whole entry.

Regroups the exact flattened bottom cell list and uses each perimeter readback, preserving the side area and its ordered
endpoints. -/
theorem bottom_perimeter (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (depth : Nat)
    (values : Fin (((domains.get position).domain sheet).steps + 1) →
      Fin (((domains.get position).domain sheet).steps + 1) → Basic.Canonical → Stokes.PrimitivePoint) :
    let whole := (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
      depth).entries.get position
    let meshes := fun column => ((Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
      shared.surface sheet depth).get position).entries.get
      ((Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) column 0)
    ∀ (wholeAssembly : ClippedAssembly whole values)
      (pieces : (column : Fin ((Meshes.Newton.Surface.PieceIndices.columns (partitions.get position)) + 1)) →
        ClippedAssembly (meshes column) values)
      (wholePerimeter : wholeAssembly.Perimeter) (perimeters : ∀ column, (pieces column).Perimeter),
      (ClippedPerimeterEntries.Perimeter.bottomEntry wholePerimeter) = StitchedSideAreas.Entry.concatenate (fun column
        => (ClippedPerimeterEntries.Perimeter.bottomEntry (perimeters column))) := by
  dsimp only
  intro wholeAssembly pieces wholePerimeter perimeters
  exact (ClippedPerimeterEntries.Perimeter.bottomEntry_eq wholePerimeter).symm.trans
    ((StitchedSideRegrouping.concatenate_of_flatten (ClippedPerimeterEntries.bottomCells wholeAssembly) (fun column =>
      (ClippedPerimeterEntries.bottomCells (pieces column)))
      (bottom_cells shared position sheet depth values wholeAssembly pieces)).trans
        (StitchedSideRegrouping.concatenate_congr (fun column => (ClippedPerimeterEntries.Perimeter.bottomEntry_eq
          (perimeters column)))))

/-- Concatenate the retained top piece perimeters into the whole entry.

Regroups the exact flattened top cell list and uses each perimeter readback, preserving the side area and its ordered
endpoints. -/
theorem top_perimeter (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (depth : Nat)
    (values : Fin (((domains.get position).domain sheet).steps + 1) →
      Fin (((domains.get position).domain sheet).steps + 1) → Basic.Canonical → Stokes.PrimitivePoint) :
    let whole := (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
      depth).entries.get position
    let meshes := fun column => ((Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains
      shared.surface sheet depth).get position).entries.get
      ((Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) column (Fin.last
        (Meshes.Newton.Surface.PieceIndices.rows (partitions.get position))))
    ∀ (wholeAssembly : ClippedAssembly whole values)
      (pieces : (column : Fin ((Meshes.Newton.Surface.PieceIndices.columns (partitions.get position)) + 1)) →
        ClippedAssembly (meshes column) values)
      (wholePerimeter : wholeAssembly.Perimeter) (perimeters : ∀ column, (pieces column).Perimeter),
      (ClippedPerimeterEntries.Perimeter.topEntry wholePerimeter) = StitchedSideAreas.Entry.concatenate (fun column =>
        (ClippedPerimeterEntries.Perimeter.topEntry (perimeters column))) := by
  dsimp only
  intro wholeAssembly pieces wholePerimeter perimeters
  exact (ClippedPerimeterEntries.Perimeter.topEntry_eq wholePerimeter).symm.trans
    ((StitchedSideRegrouping.concatenate_of_flatten (ClippedPerimeterEntries.topCells wholeAssembly) (fun column =>
      (ClippedPerimeterEntries.topCells (pieces column)))
      (top_cells shared position sheet depth values wholeAssembly pieces)).trans
        (StitchedSideRegrouping.concatenate_congr (fun column => (ClippedPerimeterEntries.Perimeter.topEntry_eq
          (perimeters column)))))

/-- Concatenate the retained left piece perimeters into the whole entry.

Regroups the exact flattened left cell list and uses each perimeter readback, preserving the side area and its ordered
endpoints. -/
theorem left_perimeter (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (depth : Nat)
    (values : Fin (((domains.get position).domain sheet).steps + 1) →
      Fin (((domains.get position).domain sheet).steps + 1) → Basic.Canonical → Stokes.PrimitivePoint) :
    let whole := (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
      depth).entries.get position
    let meshes := fun row => ((Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface
      sheet depth).get position).entries.get
      ((Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) 0 row)
    ∀ (wholeAssembly : ClippedAssembly whole values)
      (pieces : (row : Fin ((Meshes.Newton.Surface.PieceIndices.rows (partitions.get position)) + 1)) → ClippedAssembly
        (meshes row) values)
      (wholePerimeter : wholeAssembly.Perimeter) (perimeters : ∀ row, (pieces row).Perimeter),
      (ClippedPerimeterEntries.Perimeter.leftEntry wholePerimeter) = StitchedSideAreas.Entry.concatenate (fun row =>
        (ClippedPerimeterEntries.Perimeter.leftEntry (perimeters row))) := by
  dsimp only
  intro wholeAssembly pieces wholePerimeter perimeters
  exact (ClippedPerimeterEntries.Perimeter.leftEntry_eq wholePerimeter).symm.trans
    ((StitchedSideRegrouping.concatenate_of_flatten (ClippedPerimeterEntries.leftCells wholeAssembly) (fun row =>
      (ClippedPerimeterEntries.leftCells (pieces row)))
      (left_cells shared position sheet depth values wholeAssembly pieces)).trans
        (StitchedSideRegrouping.concatenate_congr (fun row => (ClippedPerimeterEntries.Perimeter.leftEntry_eq
          (perimeters row)))))

/-- Concatenate the retained right piece perimeters into the whole entry.

Regroups the exact flattened right cell list and uses each perimeter readback, preserving the side area and its ordered
endpoints. -/
theorem right_perimeter (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (depth : Nat)
    (values : Fin (((domains.get position).domain sheet).steps + 1) →
      Fin (((domains.get position).domain sheet).steps + 1) → Basic.Canonical → Stokes.PrimitivePoint) :
    let whole := (Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
      depth).entries.get position
    let meshes := fun row => ((Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface
      sheet depth).get position).entries.get
      ((Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) (Fin.last
        (Meshes.Newton.Surface.PieceIndices.columns (partitions.get position))) row)
    ∀ (wholeAssembly : ClippedAssembly whole values)
      (pieces : (row : Fin ((Meshes.Newton.Surface.PieceIndices.rows (partitions.get position)) + 1)) → ClippedAssembly
        (meshes row) values)
      (wholePerimeter : wholeAssembly.Perimeter) (perimeters : ∀ row, (pieces row).Perimeter),
      (ClippedPerimeterEntries.Perimeter.rightEntry wholePerimeter) = StitchedSideAreas.Entry.concatenate (fun row =>
        (ClippedPerimeterEntries.Perimeter.rightEntry (perimeters row))) := by
  dsimp only
  intro wholeAssembly pieces wholePerimeter perimeters
  exact (ClippedPerimeterEntries.Perimeter.rightEntry_eq wholePerimeter).symm.trans
    ((StitchedSideRegrouping.concatenate_of_flatten (ClippedPerimeterEntries.rightCells wholeAssembly) (fun row =>
      (ClippedPerimeterEntries.rightCells (pieces row)))
      (right_cells shared position sheet depth values wholeAssembly pieces)).trans
        (StitchedSideRegrouping.concatenate_congr (fun row => (ClippedPerimeterEntries.Perimeter.rightEntry_eq
          (perimeters row)))))

end

end Purelib.Riemann.RootContinuation.NewtonSharedExteriorCellLists
