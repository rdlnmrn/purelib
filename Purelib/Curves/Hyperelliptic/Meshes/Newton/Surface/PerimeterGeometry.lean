module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Integration.Path.JoinedTraceProperties
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation
import Purelib.Riemann.Paths.RectangularHorizontalTraceLengths
import Purelib.Riemann.Paths.RectangularVerticalTraceLengths
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Integration.Path

open Purelib.Riemann.Paths

@[expose] public section

/-! The concatenated surface perimeter lies on the original face sides.
Every retained owner supplies containment for the actual comparison path. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterGeometry

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces PiecePerimeterTraces)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational} {grid :
    Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {observations : Purelib.Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    grid.faces.regulars} {sheet : Fin 2}
  {partitions : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid} {coarse :
    Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {fixed : Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error :
    Purelib.Data.Rat.Fraction.Rational}
  {energy : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed error}
  {position : Fin grid.faces.regulars.length}

open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)

namespace FacePerimeterTraces

/-- Every actual original bottom boundary piece lies on the corresponding side of the complete face box. -/
private theorem bottom_piece_boundary (column : Fin ((PieceIndices.columns (partitions.get position)) + 1)) :
    ((partitions.get position).cuts.boxes[(PieceIndices.pieceIndex (partitions.get position) column 0).val]'
      (PieceIndices.pieceIndex (partitions.get position) column 0).isLt).yLower =
        (grid.faces.regulars[position.val]'position.isLt).cell.box.yLower := by
  rw [PieceIndices.piece_box (partitions.get position)]
  exact (partitions.get position).cuts.y.first_lower
    (Fin.cast (PieceIndices.rows_eq (partitions.get position)) 0).isLt

/-- Every actual owned vertex of the retained bottom perimeter has the original face-side coordinate. -/
theorem bottom_height (traces : PerimeterTraces.FacePerimeterTraces energy position)
    (vertex : Fin (traces.bottom.rest.length + 1)) :
    (traces.bottom.indexed vertex).point.im = (grid.faces.regulars[position.val]'position.isLt).cell.box.yLower := by
  have valid : JoinedTraceProperties.All traces.bottom (fun owner => owner.point.im =
    (grid.faces.regulars[position.val]'position.isLt).cell.box.yLower) := by
    rw [traces.bottom_eq]
    apply JoinedTraceProperties.concatenate_all
    intro column
    dsimp only [PiecePerimeterTraces.bottomPieces, RectangularOwnedPerimeterTraces.bottomOwned]
    apply JoinedTraceProperties.ofIndexed_all
    intro index
    let piece := PieceIndices.pieceIndex (partitions.get position) column 0
    let mesh := (energy.meshes.get position).entries.get piece
    let trace := (traces.pieces.get piece).bottom
    exact (RectangularHorizontalTraceLengths.point_height trace _).trans (mesh.y_first.trans
      (Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterGeometry.FacePerimeterTraces.bottom_piece_boundary column))
  exact valid.indexed vertex

/-- The complete original bottom perimeter retains physical side geometry and containment from each actual vertex owner.
-/
def bottomGeometry (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    SidePreparation.SideGeometry (domains.get position).models
      (fun vertex => (traces.bottom.indexed vertex).point) :=
  .horizontal (domains.get position).models _ (fun vertex =>
    let owner := traces.bottom.indexed vertex
    (((domains.get position).domain sheet).patch.cell_refines owner.column owner.row).contains owner.contains)
    (Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterGeometry.FacePerimeterTraces.bottom_height traces)

/-- Every actual original top boundary piece lies on the corresponding side of the complete face box. -/
private theorem top_piece_boundary (column : Fin ((PieceIndices.columns (partitions.get position)) + 1)) :
    ((partitions.get position).cuts.boxes[(PieceIndices.pieceIndex (partitions.get position) column (Fin.last
      (PieceIndices.rows (partitions.get position)))).val]'
      (PieceIndices.pieceIndex (partitions.get position) column (Fin.last (PieceIndices.rows (partitions.get
        position)))).isLt).yUpper = (grid.faces.regulars[position.val]'position.isLt).cell.box.yUpper := by
  rw [PieceIndices.piece_box (partitions.get position)]
  exact (partitions.get position).cuts.y.last_upper _ (PieceIndices.rows_eq (partitions.get position))

/-- Every actual owned vertex of the retained top perimeter has the original face-side coordinate. -/
theorem top_height (traces : PerimeterTraces.FacePerimeterTraces energy position)
    (vertex : Fin (traces.top.rest.length + 1)) :
    (traces.top.indexed vertex).point.im = (grid.faces.regulars[position.val]'position.isLt).cell.box.yUpper := by
  have valid : JoinedTraceProperties.All traces.top (fun owner => owner.point.im =
    (grid.faces.regulars[position.val]'position.isLt).cell.box.yUpper) := by
    rw [traces.top_eq]
    apply JoinedTraceProperties.concatenate_all
    intro column
    dsimp only [PiecePerimeterTraces.topPieces, RectangularOwnedPerimeterTraces.topOwned]
    apply JoinedTraceProperties.ofIndexed_all
    intro index
    let piece := PieceIndices.pieceIndex (partitions.get position) column (Fin.last (PieceIndices.rows (partitions.get
      position)))
    let mesh := (energy.meshes.get position).entries.get piece
    let trace := (traces.pieces.get piece).top
    exact (RectangularHorizontalTraceLengths.point_height trace _).trans (mesh.y_last.trans
      (Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterGeometry.FacePerimeterTraces.top_piece_boundary column))
  exact valid.indexed vertex

/-- The complete original top perimeter retains physical side geometry and containment from each actual vertex owner. -/
def topGeometry (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    SidePreparation.SideGeometry (domains.get position).models
      (fun vertex => (traces.top.indexed vertex).point) :=
  .horizontal (domains.get position).models _ (fun vertex =>
    let owner := traces.top.indexed vertex
    (((domains.get position).domain sheet).patch.cell_refines owner.column owner.row).contains owner.contains)
    (Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterGeometry.FacePerimeterTraces.top_height traces)

/-- Every actual original left boundary piece lies on the corresponding side of the complete face box. -/
private theorem left_piece_boundary (column : Fin ((PieceIndices.rows (partitions.get position)) + 1)) :
    ((partitions.get position).cuts.boxes[(PieceIndices.pieceIndex (partitions.get position) 0 column).val]'
      (PieceIndices.pieceIndex (partitions.get position) 0 column).isLt).xLower =
        (grid.faces.regulars[position.val]'position.isLt).cell.box.xLower := by
  rw [PieceIndices.piece_box (partitions.get position)]
  exact (partitions.get position).cuts.x.first_lower
    (Fin.cast (PieceIndices.columns_eq (partitions.get position)) 0).isLt

/-- Every actual owned vertex of the retained left perimeter has the original face-side coordinate. -/
theorem left_horizontal (traces : PerimeterTraces.FacePerimeterTraces energy position)
    (vertex : Fin (traces.left.rest.length + 1)) :
    (traces.left.indexed vertex).point.re = (grid.faces.regulars[position.val]'position.isLt).cell.box.xLower := by
  have valid : JoinedTraceProperties.All traces.left (fun owner => owner.point.re =
    (grid.faces.regulars[position.val]'position.isLt).cell.box.xLower) := by
    rw [traces.left_eq]
    apply JoinedTraceProperties.concatenate_all
    intro column
    dsimp only [PiecePerimeterTraces.leftPieces, RectangularOwnedPerimeterTraces.leftOwned]
    apply JoinedTraceProperties.ofIndexed_all
    intro index
    let piece := PieceIndices.pieceIndex (partitions.get position) 0 column
    let mesh := (energy.meshes.get position).entries.get piece
    let trace := (traces.pieces.get piece).left
    exact (RectangularVerticalTraceLengths.point_horizontal trace _).trans (mesh.x_first.trans
      (Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterGeometry.FacePerimeterTraces.left_piece_boundary column))
  exact valid.indexed vertex

/-- The complete original left perimeter retains physical side geometry and containment from each actual vertex owner.
-/
def leftGeometry (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    SidePreparation.SideGeometry (domains.get position).models
      (fun vertex => (traces.left.indexed vertex).point) :=
  .vertical (domains.get position).models _ (fun vertex =>
    let owner := traces.left.indexed vertex
    (((domains.get position).domain sheet).patch.cell_refines owner.column owner.row).contains owner.contains)
    (Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterGeometry.FacePerimeterTraces.left_horizontal traces)

/-- Every actual original right boundary piece lies on the corresponding side of the complete face box. -/
private theorem right_piece_boundary (column : Fin ((PieceIndices.rows (partitions.get position)) + 1)) :
    ((partitions.get position).cuts.boxes[(PieceIndices.pieceIndex (partitions.get position) (Fin.last
      (PieceIndices.columns (partitions.get position))) column).val]'
      (PieceIndices.pieceIndex (partitions.get position) (Fin.last (PieceIndices.columns (partitions.get position)))
        column).isLt).xUpper = (grid.faces.regulars[position.val]'position.isLt).cell.box.xUpper := by
  rw [PieceIndices.piece_box (partitions.get position)]
  exact (partitions.get position).cuts.x.last_upper _ (PieceIndices.columns_eq (partitions.get position))

/-- Every actual owned vertex of the retained right perimeter has the original face-side coordinate. -/
theorem right_horizontal (traces : PerimeterTraces.FacePerimeterTraces energy position)
    (vertex : Fin (traces.right.rest.length + 1)) :
    (traces.right.indexed vertex).point.re = (grid.faces.regulars[position.val]'position.isLt).cell.box.xUpper := by
  have valid : JoinedTraceProperties.All traces.right (fun owner => owner.point.re =
    (grid.faces.regulars[position.val]'position.isLt).cell.box.xUpper) := by
    rw [traces.right_eq]
    apply JoinedTraceProperties.concatenate_all
    intro column
    dsimp only [PiecePerimeterTraces.rightPieces, RectangularOwnedPerimeterTraces.rightOwned]
    apply JoinedTraceProperties.ofIndexed_all
    intro index
    let piece := PieceIndices.pieceIndex (partitions.get position) (Fin.last (PieceIndices.columns (partitions.get
      position))) column
    let mesh := (energy.meshes.get position).entries.get piece
    let trace := (traces.pieces.get piece).right
    exact (RectangularVerticalTraceLengths.point_horizontal trace _).trans (mesh.x_last.trans
      (Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterGeometry.FacePerimeterTraces.right_piece_boundary column))
  exact valid.indexed vertex

/-- The complete original right perimeter retains physical side geometry and containment from each actual vertex owner.
-/
def rightGeometry (traces : PerimeterTraces.FacePerimeterTraces energy position) :
    SidePreparation.SideGeometry (domains.get position).models
      (fun vertex => (traces.right.indexed vertex).point) :=
  .vertical (domains.get position).models _ (fun vertex =>
    let owner := traces.right.indexed vertex
    (((domains.get position).domain sheet).patch.cell_refines owner.column owner.row).contains owner.contains)
    (Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterGeometry.FacePerimeterTraces.right_horizontal traces)

end FacePerimeterTraces
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterGeometry
