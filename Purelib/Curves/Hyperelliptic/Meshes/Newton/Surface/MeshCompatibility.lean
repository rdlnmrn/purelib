module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Flatten

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
public import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Init.Data.List.OfFn
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy

public section

/-! Complete surface meshes share all model cuts across faces and sheets.
Spatial and numerical refinement preserve those actual interval lists. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)

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

/-- Equal retained endpoints and cut lists produce equal finite axis-interval lists. -/
private theorem axis_intervals_eq {firstLower firstUpper lastLower lastUpper : Fraction.Rational}
    (firstProper : firstLower < firstUpper) (lastProper : lastLower < lastUpper)
    {firstCuts lastCuts : List Fraction.Rational} (lowerEq : firstLower = lastLower) (upperEq : firstUpper = lastUpper)
    (cutsEq : firstCuts = lastCuts) :
    (Geometry.Rectangle.AxisPartition.build firstLower firstUpper firstProper firstCuts).intervals =
      (Geometry.Rectangle.AxisPartition.build lastLower lastUpper lastProper lastCuts).intervals := by
  cases lowerEq
  cases upperEq
  cases cutsEq
  rfl

set_option genInjectivity false in
/-- One cached cut list includes every model boundary on every piece and sheet. -/
structure SurfaceCuts (partitions : NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid)
    (domains : DomainBanks.FaceDomainBank frames grid.faces.regulars) where
  /-- The cached list of all retained model-boundary points over faces, pieces and sheets. -/ points : List
    Data.Gaussian.Basic.Canonical
  /-- Every boundary point of every actual retained piece and sheet occurs in the shared cut list. -/ includes : ∀
    (position : Fin grid.faces.regulars.length)
    (piece : Fin (partitions.get position).cuts.boxes.length) (sheet : Fin 2) point,
    point ∈ ((domains.get position).domain sheet).cuts.rectanglePoints
      ((partitions.get position).cuts.boxes[piece.val]'piece.isLt) → point ∈ points

constructive_injectivity SurfaceCuts

/-- Cache all actual model cuts in face, piece and sheet order. -/
@[expose] def SurfaceCuts.build (partitions : NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid)
    (domains : DomainBanks.FaceDomainBank frames grid.faces.regulars) :
      Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains :=
  let points := (List.ofFn fun position : Fin grid.faces.regulars.length => position).flatMap fun position =>
    (List.ofFn fun piece : Fin (partitions.get position).cuts.boxes.length => piece).flatMap fun piece =>
      (List.ofFn fun sheet : Fin 2 => sheet).flatMap fun sheet =>
        ((domains.get position).domain sheet).cuts.rectanglePoints
          ((partitions.get position).cuts.boxes[piece.val]'piece.isLt)
  ⟨points, fun position piece sheet _ member => Flatten.mem_flatMap.mpr
    ⟨position, List.OfFn.Basic.mem_ofFn.mpr ⟨position, rfl⟩, Flatten.mem_flatMap.mpr
      ⟨piece, List.OfFn.Basic.mem_ofFn.mpr ⟨piece, rfl⟩, Flatten.mem_flatMap.mpr
        ⟨sheet, List.OfFn.Basic.mem_ofFn.mpr ⟨sheet, rfl⟩, member⟩⟩⟩⟩

/-- Construct each retained sheet's piece meshes using the same cached complete-surface cut list. -/
@[expose] def surfaceMeshes (partitions : NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid)
    (domains : DomainBanks.FaceDomainBank frames grid.faces.regulars) (surfaceCuts :
      Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains)
    (sheet : Fin 2) (depth : Nat) : NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet :=
  DependentVector.ofFn fun position => LocalMeshes.build (partitions.get position)
    domains sheet surfaceCuts.points (fun piece => surfaceCuts.includes position piece sheet) depth

/-- Equal transverse extents have identical cuts, including across faces and sheets. -/
theorem surfaceMeshes_x_compatible (partitions : NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid)
    (domains : DomainBanks.FaceDomainBank frames grid.faces.regulars) (surfaceCuts :
      Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains)
    (firstSheet lastSheet : Fin 2)
    (firstDepth lastDepth : Nat) (first last : Fin grid.faces.regulars.length)
    (firstPiece : Fin (partitions.get first).cuts.boxes.length)
    (lastPiece : Fin (partitions.get last).cuts.boxes.length)
    (lowerEq : ((partitions.get first).cuts.boxes[firstPiece.val]'firstPiece.isLt).xLower =
      ((partitions.get last).cuts.boxes[lastPiece.val]'lastPiece.isLt).xLower)
    (upperEq : ((partitions.get first).cuts.boxes[firstPiece.val]'firstPiece.isLt).xUpper =
      ((partitions.get last).cuts.boxes[lastPiece.val]'lastPiece.isLt).xUpper) :
    (((Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
      firstSheet firstDepth).get first).entries.get firstPiece).partition.x.intervals =
      (((Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
        lastSheet lastDepth).get last).entries.get lastPiece).partition.x.intervals := by
  dsimp only [Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes]
  rw [DependentVector.ofFn_get, DependentVector.ofFn_get]
  dsimp only [LocalMeshes.build]
  rw [DependentVector.ofFn_get, DependentVector.ofFn_get]
  exact Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.axis_intervals_eq _ _ lowerEq upperEq rfl

/-- Equal transverse extents have identical cuts, including across faces and sheets. -/
theorem surfaceMeshes_y_compatible (partitions : NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid)
    (domains : DomainBanks.FaceDomainBank frames grid.faces.regulars) (surfaceCuts :
      Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains)
    (firstSheet lastSheet : Fin 2)
    (firstDepth lastDepth : Nat) (first last : Fin grid.faces.regulars.length)
    (firstPiece : Fin (partitions.get first).cuts.boxes.length)
    (lastPiece : Fin (partitions.get last).cuts.boxes.length)
    (lowerEq : ((partitions.get first).cuts.boxes[firstPiece.val]'firstPiece.isLt).yLower =
      ((partitions.get last).cuts.boxes[lastPiece.val]'lastPiece.isLt).yLower)
    (upperEq : ((partitions.get first).cuts.boxes[firstPiece.val]'firstPiece.isLt).yUpper =
      ((partitions.get last).cuts.boxes[lastPiece.val]'lastPiece.isLt).yUpper) :
    (((Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
      firstSheet firstDepth).get first).entries.get firstPiece).partition.y.intervals =
      (((Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
        lastSheet lastDepth).get last).entries.get lastPiece).partition.y.intervals := by
  dsimp only [Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes]
  rw [DependentVector.ofFn_get, DependentVector.ofFn_get]
  dsimp only [LocalMeshes.build]
  rw [DependentVector.ofFn_get, DependentVector.ofFn_get]
  exact Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.axis_intervals_eq _ _ lowerEq upperEq rfl

namespace SurfaceRequest

variable {partitions : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {surfaceCuts : Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains}
    {coarse : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {fixed : Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error :
    Purelib.Data.Rat.Fraction.Rational}

/-- Refining the retained surface request preserves each piece's exact horizontal interval list. -/
theorem mesh_x_intervals (request : NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed error)
    (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length) :
    ((request.meshes.get position).entries.get piece).partition.x.intervals =
      ((coarse.get position).entries.get piece).partition.x.intervals := by
  rw [request.mesh_eq, ((request.entries.get position).get piece).mesh_eq]
  rfl

/-- Refining the retained surface request preserves each piece's exact vertical interval list. -/
theorem mesh_y_intervals (request : NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed error)
    (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length) :
    ((request.meshes.get position).entries.get piece).partition.y.intervals =
      ((coarse.get position).entries.get piece).partition.y.intervals := by
  rw [request.mesh_eq, ((request.entries.get position).get piece).mesh_eq]
  rfl

/-- Pieces in one retained column share exactly the same horizontal intervals after request refinement. -/
theorem mesh_x_compatible {depth : Nat}
    (request : NewtonRequestedSurfaceEnergy.SurfaceRequest partitions
      (Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts sheet
      depth) fixed error)
    (position : Fin grid.faces.regulars.length)
    (column : Fin (PieceIndices.columns (partitions.get position) + 1)) (first last : Fin (PieceIndices.rows
      (partitions.get position) + 1)) :
    ((request.meshes.get position).entries.get (PieceIndices.pieceIndex (partitions.get position) column
      first)).partition.x.intervals =
      ((request.meshes.get position).entries.get (PieceIndices.pieceIndex (partitions.get position) column
        last)).partition.x.intervals := by
  rw [(Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceRequest.mesh_x_intervals request),
    (Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceRequest.mesh_x_intervals request)]
  dsimp only [Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes]
  rw [DependentVector.ofFn_get]
  dsimp only [LocalMeshes.build]
  rw [DependentVector.ofFn_get, DependentVector.ofFn_get]
  apply Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.axis_intervals_eq
  · rw [PieceIndices.piece_box (partitions.get position), PieceIndices.piece_box (partitions.get position)]
    rfl
  · rw [PieceIndices.piece_box (partitions.get position), PieceIndices.piece_box (partitions.get position)]
    rfl
  · rfl

/-- Pieces in one retained row share exactly the same vertical intervals after request refinement. -/
theorem mesh_y_compatible {depth : Nat}
    (request : NewtonRequestedSurfaceEnergy.SurfaceRequest partitions
      (Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts sheet
      depth) fixed error)
    (position : Fin grid.faces.regulars.length)
    (first last : Fin (PieceIndices.columns (partitions.get position) + 1)) (row : Fin (PieceIndices.rows
      (partitions.get position) + 1)) :
    ((request.meshes.get position).entries.get (PieceIndices.pieceIndex (partitions.get position) first
      row)).partition.y.intervals =
      ((request.meshes.get position).entries.get (PieceIndices.pieceIndex (partitions.get position) last
        row)).partition.y.intervals := by
  rw [(Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceRequest.mesh_y_intervals request),
    (Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceRequest.mesh_y_intervals request)]
  dsimp only [Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes]
  rw [DependentVector.ofFn_get]
  dsimp only [LocalMeshes.build]
  rw [DependentVector.ofFn_get, DependentVector.ofFn_get]
  apply Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.axis_intervals_eq
  · rw [PieceIndices.piece_box (partitions.get position), PieceIndices.piece_box (partitions.get position)]
    rfl
  · rw [PieceIndices.piece_box (partitions.get position), PieceIndices.piece_box (partitions.get position)]
    rfl
  · rfl

end SurfaceRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
