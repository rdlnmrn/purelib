module
import Purelib.Data.List.Filter
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
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
public import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Riemann.Readings.RectangularObservationEndpoints
import Purelib.Polynomial.Geometry.Grid.AxisNeighbors
import Purelib.Riemann.Readings.RectangularObservationOwnerCoherence

public section

/-! Boundary pieces retain the same extreme fine interval as the whole face.
This identifies the transverse owners in the perimeter concatenation. -/
namespace Purelib.Riemann.RootContinuation.NewtonSharedExteriorBoundaryIntervals

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest (BasisArcPreparations)
open Purelib.Riemann.Branches.NewtonSharedExteriorCuts (SharedExteriorCuts)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices (columns rows columns_eq rows_eq pieceIndex
  piece_box)
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

/-- Membership in a retained filtered list gives membership in the original list. -/
private theorem member_of_filter {α : Type} {first last : List α} {predicate : α → Bool}
    (equal : first = last.filter predicate) {entry : α} (member : entry ∈ first) : entry ∈ last :=
  (Data.List.Filter.mem_filter.mp (equal ▸ member)).1

section
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
section
open Purelib.Polynomial.Geometry.Grid
/-- The bottom boundary piece retains the whole face's first vertical fine interval.

The shared exterior cuts preserve interval membership and the exact outer endpoint, independently of the two observation
depths and selected sheet. -/
theorem bottom_interval (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (column : Fin ((PieceIndices.columns (partitions.get position)) + 1))
    (sheet : Fin 2) (wholeDepth pieceDepth : Nat) :
    let whole := (RegularMeshes.build domains shared.source.cuts sheet wholeDepth).entries.get position
    let piece := (pieceIndex (partitions.get position)) column (0)
    let mesh := ((MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet pieceDepth).get
      position).entries.get piece
    mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq 0).val]'(Fin.cast mesh.boundaryRows_eq 0).isLt =
      whole.partition.y.intervals[(Fin.cast whole.boundaryRows_eq 0).val]'(Fin.cast whole.boundaryRows_eq 0).isLt := by
  dsimp only
  let whole := (RegularMeshes.build domains shared.source.cuts sheet wholeDepth).entries.get position
  let piece := (pieceIndex (partitions.get position)) column (0)
  let mesh := ((MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet pieceDepth).get
    position).entries.get piece
  have member : mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq 0).val]'(Fin.cast mesh.boundaryRows_eq 0).isLt
    ∈
      whole.partition.y.intervals := by
    exact member_of_filter (shared.piece_y_intervals position piece sheet wholeDepth pieceDepth)
      (List.getElem_mem (Fin.cast mesh.boundaryRows_eq 0).isLt)
  apply AxisNeighbors.eq_of_lower whole.partition.y.ordered
    (whole.partition.y.intervals_eq ▸ member)
    (whole.partition.y.intervals_eq ▸ List.getElem_mem (Fin.cast whole.boundaryRows_eq 0).isLt)
  have innerEndpoint := mesh.partition.y.first_lower (Fin.cast mesh.boundaryRows_eq 0).isLt
  have outerEndpoint := whole.partition.y.first_lower (Fin.cast whole.boundaryRows_eq 0).isLt
  have coarseEndpoint := (partitions.get position).cuts.y.first_lower (Fin.cast (PieceIndices.rows_eq (partitions.get
    position)) 0).isLt
  have boundary : ((partitions.get position).cuts.boxes[piece.val]'piece.isLt).yLower =
      (grid.faces.regulars[position.val]'position.isLt).cell.box.yLower := by
    rw [(PieceIndices.piece_box (partitions.get position))]
    exact coarseEndpoint
  exact innerEndpoint.trans (boundary.trans outerEndpoint.symm)

/-- The top boundary piece retains the whole face's last vertical fine interval.

The shared exterior cuts preserve interval membership and the exact outer endpoint, independently of the two observation
depths and selected sheet. -/
theorem top_interval (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (column : Fin ((PieceIndices.columns (partitions.get position)) + 1))
    (sheet : Fin 2) (wholeDepth pieceDepth : Nat) :
    let whole := (RegularMeshes.build domains shared.source.cuts sheet wholeDepth).entries.get position
    let piece := (pieceIndex (partitions.get position)) column (Fin.last (PieceIndices.rows (partitions.get position)))
    let mesh := ((MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet pieceDepth).get
      position).entries.get piece
    mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq (Fin.last mesh.boundaryRows)).val]'(Fin.cast
      mesh.boundaryRows_eq (Fin.last mesh.boundaryRows)).isLt =
      whole.partition.y.intervals[(Fin.cast whole.boundaryRows_eq (Fin.last whole.boundaryRows)).val]'(Fin.cast
        whole.boundaryRows_eq (Fin.last whole.boundaryRows)).isLt := by
  dsimp only
  let whole := (RegularMeshes.build domains shared.source.cuts sheet wholeDepth).entries.get position
  let piece := (pieceIndex (partitions.get position)) column (Fin.last (PieceIndices.rows (partitions.get position)))
  let mesh := ((MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet pieceDepth).get
    position).entries.get piece
  have member : mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq (Fin.last mesh.boundaryRows)).val]'(Fin.cast
    mesh.boundaryRows_eq (Fin.last mesh.boundaryRows)).isLt ∈
      whole.partition.y.intervals := by
    exact member_of_filter (shared.piece_y_intervals position piece sheet wholeDepth pieceDepth)
      (List.getElem_mem (Fin.cast mesh.boundaryRows_eq (Fin.last mesh.boundaryRows)).isLt)
  apply AxisNeighbors.eq_of_upper whole.partition.y.ordered
    (whole.partition.y.intervals_eq ▸ member)
    (whole.partition.y.intervals_eq ▸ List.getElem_mem (Fin.cast whole.boundaryRows_eq (Fin.last
      whole.boundaryRows)).isLt)
  have innerEndpoint := mesh.partition.y.last_upper (Fin.cast mesh.boundaryRows_eq (Fin.last mesh.boundaryRows))
    mesh.boundaryRows_eq
  have outerEndpoint := whole.partition.y.last_upper (Fin.cast whole.boundaryRows_eq (Fin.last whole.boundaryRows))
    whole.boundaryRows_eq
  have coarseEndpoint := (partitions.get position).cuts.y.last_upper (Fin.cast (PieceIndices.rows_eq (partitions.get
    position)) (Fin.last (PieceIndices.rows (partitions.get position)))) (PieceIndices.rows_eq (partitions.get
    position))
  have boundary : ((partitions.get position).cuts.boxes[piece.val]'piece.isLt).yUpper =
      (grid.faces.regulars[position.val]'position.isLt).cell.box.yUpper := by
    rw [(PieceIndices.piece_box (partitions.get position))]
    exact coarseEndpoint
  exact innerEndpoint.trans (boundary.trans outerEndpoint.symm)

/-- The left boundary piece retains the whole face's first horizontal fine interval.

The shared exterior cuts preserve interval membership and the exact outer endpoint, independently of the two observation
depths and selected sheet. -/
theorem left_interval (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (row : Fin ((PieceIndices.rows (partitions.get position)) + 1))
    (sheet : Fin 2) (wholeDepth pieceDepth : Nat) :
    let whole := (RegularMeshes.build domains shared.source.cuts sheet wholeDepth).entries.get position
    let piece := (pieceIndex (partitions.get position)) (0) row
    let mesh := ((MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet pieceDepth).get
      position).entries.get piece
    mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq 0).val]'(Fin.cast mesh.boundaryColumns_eq 0).isLt =
      whole.partition.x.intervals[(Fin.cast whole.boundaryColumns_eq 0).val]'(Fin.cast whole.boundaryColumns_eq 0).isLt
        := by
  dsimp only
  let whole := (RegularMeshes.build domains shared.source.cuts sheet wholeDepth).entries.get position
  let piece := (pieceIndex (partitions.get position)) (0) row
  let mesh := ((MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet pieceDepth).get
    position).entries.get piece
  have member : mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq 0).val]'(Fin.cast mesh.boundaryColumns_eq
    0).isLt ∈
      whole.partition.x.intervals := by
    exact member_of_filter (shared.piece_x_intervals position piece sheet wholeDepth pieceDepth)
      (List.getElem_mem (Fin.cast mesh.boundaryColumns_eq 0).isLt)
  apply AxisNeighbors.eq_of_lower whole.partition.x.ordered
    (whole.partition.x.intervals_eq ▸ member)
    (whole.partition.x.intervals_eq ▸ List.getElem_mem (Fin.cast whole.boundaryColumns_eq 0).isLt)
  have innerEndpoint := mesh.partition.x.first_lower (Fin.cast mesh.boundaryColumns_eq 0).isLt
  have outerEndpoint := whole.partition.x.first_lower (Fin.cast whole.boundaryColumns_eq 0).isLt
  have coarseEndpoint := (partitions.get position).cuts.x.first_lower (Fin.cast (PieceIndices.columns_eq (partitions.get
    position)) 0).isLt
  have boundary : ((partitions.get position).cuts.boxes[piece.val]'piece.isLt).xLower =
      (grid.faces.regulars[position.val]'position.isLt).cell.box.xLower := by
    rw [(PieceIndices.piece_box (partitions.get position))]
    exact coarseEndpoint
  exact innerEndpoint.trans (boundary.trans outerEndpoint.symm)

/-- The right boundary piece retains the whole face's last horizontal fine interval.

The shared exterior cuts preserve interval membership and the exact outer endpoint, independently of the two observation
depths and selected sheet. -/
theorem right_interval (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (row : Fin ((PieceIndices.rows (partitions.get position)) + 1))
    (sheet : Fin 2) (wholeDepth pieceDepth : Nat) :
    let whole := (RegularMeshes.build domains shared.source.cuts sheet wholeDepth).entries.get position
    let piece := (pieceIndex (partitions.get position)) (Fin.last (PieceIndices.columns (partitions.get position))) row
    let mesh := ((MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet pieceDepth).get
      position).entries.get piece
    mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns)).val]'(Fin.cast
      mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns)).isLt =
      whole.partition.x.intervals[(Fin.cast whole.boundaryColumns_eq (Fin.last whole.boundaryColumns)).val]'(Fin.cast
        whole.boundaryColumns_eq (Fin.last whole.boundaryColumns)).isLt := by
  dsimp only
  let whole := (RegularMeshes.build domains shared.source.cuts sheet wholeDepth).entries.get position
  let piece := (pieceIndex (partitions.get position)) (Fin.last (PieceIndices.columns (partitions.get position))) row
  let mesh := ((MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet pieceDepth).get
    position).entries.get piece
  have member : mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq (Fin.last
    mesh.boundaryColumns)).val]'(Fin.cast mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns)).isLt ∈
      whole.partition.x.intervals := by
    exact member_of_filter (shared.piece_x_intervals position piece sheet wholeDepth pieceDepth)
      (List.getElem_mem (Fin.cast mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns)).isLt)
  apply AxisNeighbors.eq_of_upper whole.partition.x.ordered
    (whole.partition.x.intervals_eq ▸ member)
    (whole.partition.x.intervals_eq ▸ List.getElem_mem (Fin.cast whole.boundaryColumns_eq (Fin.last
      whole.boundaryColumns)).isLt)
  have innerEndpoint := mesh.partition.x.last_upper (Fin.cast mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns))
    mesh.boundaryColumns_eq
  have outerEndpoint := whole.partition.x.last_upper (Fin.cast whole.boundaryColumns_eq (Fin.last
    whole.boundaryColumns)) whole.boundaryColumns_eq
  have coarseEndpoint := (partitions.get position).cuts.x.last_upper (Fin.cast (PieceIndices.columns_eq (partitions.get
    position)) (Fin.last (PieceIndices.columns (partitions.get position)))) (PieceIndices.columns_eq (partitions.get
    position))
  have boundary : ((partitions.get position).cuts.boxes[piece.val]'piece.isLt).xUpper =
      (grid.faces.regulars[position.val]'position.isLt).cell.box.xUpper := by
    rw [(PieceIndices.piece_box (partitions.get position))]
    exact coarseEndpoint
  exact innerEndpoint.trans (boundary.trans outerEndpoint.symm)

end

open Purelib.Data
open Purelib.Riemann.Readings.RectangularObservationAssembly
open Purelib.Riemann.Readings.RectangularObservationOwnerCoherence.ObservationMesh
open Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
open Purelib.Topology
/-- Read the exact cached sides and corners of a bottom boundary piece from the whole face.

Equality of the along-boundary intervals combines with the retained extreme transverse interval and common primitive
values at the same depth, preserving both owner indices. -/
theorem bottom_cell (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (column : Fin ((PieceIndices.columns (partitions.get position)) + 1))
    (sheet : Fin 2) (depth : Nat)
    (values : Fin (((domains.get position).domain sheet).steps + 1) →
      Fin (((domains.get position).domain sheet).steps + 1) → Gaussian.Basic.Canonical → Polygon.Stokes.PrimitivePoint)
        :
    let whole := (RegularMeshes.build domains shared.source.cuts sheet depth).entries.get position
    let piece := (pieceIndex (partitions.get position)) column 0
    let mesh := ((MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet depth).get
      position).entries.get piece
    ∀ (wholeAssembly : ObservationMesh.ClippedAssembly whole values)
      (pieceAssembly : ObservationMesh.ClippedAssembly mesh values)
      (wholeIndex : Fin (whole.boundaryColumns + 1)) (pieceIndex : Fin (mesh.boundaryColumns + 1)),
      mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq pieceIndex).val]'
          (Fin.cast mesh.boundaryColumns_eq pieceIndex).isLt =
        whole.partition.x.intervals[(Fin.cast whole.boundaryColumns_eq wholeIndex).val]'
          (Fin.cast whole.boundaryColumns_eq wholeIndex).isLt →
      pieceAssembly.sides pieceIndex 0 = wholeAssembly.sides wholeIndex 0 ∧
        pieceAssembly.corners pieceIndex 0 = wholeAssembly.corners wholeIndex 0 := by
  dsimp only
  intro wholeAssembly pieceAssembly wholeIndex pieceIndex along
  apply ClippedAssembly.cell_eq_of_intervals
    _ _ pieceAssembly wholeAssembly _ _ _ _
  · exact along
  · exact bottom_interval shared position column sheet depth depth
  · dsimp only [MeshCompatibility.surfaceMeshes, RegularMeshes.build]
    rw [Vector.DependentVector.ofFn_get, Vector.DependentVector.ofFn_get]
    dsimp only [LocalMeshes.build]
    rw [Vector.DependentVector.ofFn_get]
    rfl

/-- Read the exact cached sides and corners of a top boundary piece from the whole face.

Equality of the along-boundary intervals combines with the retained extreme transverse interval and common primitive
values at the same depth, preserving both owner indices. -/
theorem top_cell (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (column : Fin ((PieceIndices.columns (partitions.get position)) + 1))
    (sheet : Fin 2) (depth : Nat)
    (values : Fin (((domains.get position).domain sheet).steps + 1) →
      Fin (((domains.get position).domain sheet).steps + 1) → Gaussian.Basic.Canonical → Polygon.Stokes.PrimitivePoint)
        :
    let whole := (RegularMeshes.build domains shared.source.cuts sheet depth).entries.get position
    let piece := (pieceIndex (partitions.get position)) column (Fin.last (PieceIndices.rows (partitions.get position)))
    let mesh := ((MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet depth).get
      position).entries.get piece
    ∀ (wholeAssembly : ObservationMesh.ClippedAssembly whole values)
      (pieceAssembly : ObservationMesh.ClippedAssembly mesh values)
      (wholeIndex : Fin (whole.boundaryColumns + 1)) (pieceIndex : Fin (mesh.boundaryColumns + 1)),
      mesh.partition.x.intervals[(Fin.cast mesh.boundaryColumns_eq pieceIndex).val]'
          (Fin.cast mesh.boundaryColumns_eq pieceIndex).isLt =
        whole.partition.x.intervals[(Fin.cast whole.boundaryColumns_eq wholeIndex).val]'
          (Fin.cast whole.boundaryColumns_eq wholeIndex).isLt →
      pieceAssembly.sides pieceIndex (Fin.last mesh.boundaryRows) = wholeAssembly.sides wholeIndex (Fin.last
        whole.boundaryRows) ∧
        pieceAssembly.corners pieceIndex (Fin.last mesh.boundaryRows) = wholeAssembly.corners wholeIndex (Fin.last
          whole.boundaryRows) := by
  dsimp only
  intro wholeAssembly pieceAssembly wholeIndex pieceIndex along
  apply ClippedAssembly.cell_eq_of_intervals
    _ _ pieceAssembly wholeAssembly _ _ _ _
  · exact along
  · exact top_interval shared position column sheet depth depth
  · dsimp only [MeshCompatibility.surfaceMeshes, RegularMeshes.build]
    rw [Vector.DependentVector.ofFn_get, Vector.DependentVector.ofFn_get]
    dsimp only [LocalMeshes.build]
    rw [Vector.DependentVector.ofFn_get]
    rfl

/-- Read the exact cached sides and corners of a left boundary piece from the whole face.

Equality of the along-boundary intervals combines with the retained extreme transverse interval and common primitive
values at the same depth, preserving both owner indices. -/
theorem left_cell (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (row : Fin ((PieceIndices.rows (partitions.get position)) + 1))
    (sheet : Fin 2) (depth : Nat)
    (values : Fin (((domains.get position).domain sheet).steps + 1) →
      Fin (((domains.get position).domain sheet).steps + 1) → Gaussian.Basic.Canonical → Polygon.Stokes.PrimitivePoint)
        :
    let whole := (RegularMeshes.build domains shared.source.cuts sheet depth).entries.get position
    let piece := (pieceIndex (partitions.get position)) 0 row
    let mesh := ((MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet depth).get
      position).entries.get piece
    ∀ (wholeAssembly : ObservationMesh.ClippedAssembly whole values)
      (pieceAssembly : ObservationMesh.ClippedAssembly mesh values)
      (wholeIndex : Fin (whole.boundaryRows + 1)) (pieceIndex : Fin (mesh.boundaryRows + 1)),
      mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq pieceIndex).val]'
          (Fin.cast mesh.boundaryRows_eq pieceIndex).isLt =
        whole.partition.y.intervals[(Fin.cast whole.boundaryRows_eq wholeIndex).val]'
          (Fin.cast whole.boundaryRows_eq wholeIndex).isLt →
      pieceAssembly.sides 0 pieceIndex = wholeAssembly.sides 0 wholeIndex ∧
        pieceAssembly.corners 0 pieceIndex = wholeAssembly.corners 0 wholeIndex := by
  dsimp only
  intro wholeAssembly pieceAssembly wholeIndex pieceIndex along
  apply ClippedAssembly.cell_eq_of_intervals
    _ _ pieceAssembly wholeAssembly _ _ _ _
  · exact left_interval shared position row sheet depth depth
  · exact along
  · dsimp only [MeshCompatibility.surfaceMeshes, RegularMeshes.build]
    rw [Vector.DependentVector.ofFn_get, Vector.DependentVector.ofFn_get]
    dsimp only [LocalMeshes.build]
    rw [Vector.DependentVector.ofFn_get]
    rfl

/-- Read the exact cached sides and corners of a right boundary piece from the whole face.

Equality of the along-boundary intervals combines with the retained extreme transverse interval and common primitive
values at the same depth, preserving both owner indices. -/
theorem right_cell (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (row : Fin ((PieceIndices.rows (partitions.get position)) + 1))
    (sheet : Fin 2) (depth : Nat)
    (values : Fin (((domains.get position).domain sheet).steps + 1) →
      Fin (((domains.get position).domain sheet).steps + 1) → Gaussian.Basic.Canonical → Polygon.Stokes.PrimitivePoint)
        :
    let whole := (RegularMeshes.build domains shared.source.cuts sheet depth).entries.get position
    let piece := (pieceIndex (partitions.get position)) (Fin.last (PieceIndices.columns (partitions.get position))) row
    let mesh := ((MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet depth).get
      position).entries.get piece
    ∀ (wholeAssembly : ObservationMesh.ClippedAssembly whole values)
      (pieceAssembly : ObservationMesh.ClippedAssembly mesh values)
      (wholeIndex : Fin (whole.boundaryRows + 1)) (pieceIndex : Fin (mesh.boundaryRows + 1)),
      mesh.partition.y.intervals[(Fin.cast mesh.boundaryRows_eq pieceIndex).val]'
          (Fin.cast mesh.boundaryRows_eq pieceIndex).isLt =
        whole.partition.y.intervals[(Fin.cast whole.boundaryRows_eq wholeIndex).val]'
          (Fin.cast whole.boundaryRows_eq wholeIndex).isLt →
      pieceAssembly.sides (Fin.last mesh.boundaryColumns) pieceIndex = wholeAssembly.sides (Fin.last
        whole.boundaryColumns) wholeIndex ∧
        pieceAssembly.corners (Fin.last mesh.boundaryColumns) pieceIndex = wholeAssembly.corners (Fin.last
          whole.boundaryColumns) wholeIndex := by
  dsimp only
  intro wholeAssembly pieceAssembly wholeIndex pieceIndex along
  apply ClippedAssembly.cell_eq_of_intervals
    _ _ pieceAssembly wholeAssembly _ _ _ _
  · exact right_interval shared position row sheet depth depth
  · exact along
  · dsimp only [MeshCompatibility.surfaceMeshes, RegularMeshes.build]
    rw [Vector.DependentVector.ofFn_get, Vector.DependentVector.ofFn_get]
    dsimp only [LocalMeshes.build]
    rw [Vector.DependentVector.ofFn_get]
    rfl

end

end Purelib.Riemann.RootContinuation.NewtonSharedExteriorBoundaryIntervals
