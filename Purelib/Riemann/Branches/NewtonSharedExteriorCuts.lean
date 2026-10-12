module
import Purelib.Data.List.OfFn.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitionRestriction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Polynomial.Dense.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Mathlib.Order.Basic

open Purelib

public section

/-! One retained cut bank serves the whole regular faces, all observation
pieces and every exterior source occurrence. Piece endpoints are included
explicitly so that restriction preserves the actual interval spines. -/
namespace Purelib.Riemann.Branches.NewtonSharedExteriorCuts
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
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior (BasisSourceCuts)
open Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
open Purelib.Riemann.Normalization
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {lifted : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank lifted.frames
    grid.faces.regulars}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rectangle.Partition in
set_option genInjectivity false in
/-- One retained cut-point set shared by original surface pieces and exterior basis sources.

The record retains the exact partition-corner list, original domain cuts and source preparation, with inclusion
certificates for every original face, piece and sheet. -/
structure SharedExteriorCuts (partitions : SurfacePartitions observations grid)
    (preparations : Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular domains) where
  /-- The retained ordered diagonal corners of all original surface partition pieces. -/ partitionPoints : List
    Basic.Canonical
  /-- The corner list is the exact original face-by-piece flattening of lower and upper diagonal corners. -/
    partitionPoints_eq : partitionPoints = (List.ofFn (fun position : Fin grid.faces.regulars.length =>
    position)).flatMap
    (fun position => (partitions.get position).cuts.boxes.flatMap
      (fun box => [PreparedRectangleCuts.corner box false false, PreparedRectangleCuts.corner box true true]))
  /-- The retained original-domain common cuts extended by surface-piece and partition-corner points. -/ base :
    Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains
  /-- Every exact retained partition corner belongs to the original common base cuts. -/ partition_included : ∀ point ∈
    partitionPoints, point ∈ base.points
  /-- The exterior basis-source cut owner prepared from that exact common base. -/ source :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts preparations base
  /-- Each original face-piece-sheet rectangle point belongs to the same retained exterior source cuts. -/
    surface_included : ∀ (position : Fin grid.faces.regulars.length)
    (piece : Fin (partitions.get position).cuts.boxes.length) (sheet : Fin 2) point,
    point ∈ ((domains.get position).domain sheet).cuts.rectanglePoints
      ((partitions.get position).cuts.boxes[piece.val]'piece.isLt) → point ∈ source.cuts.points

constructive_injectivity SharedExteriorCuts

namespace SharedExteriorCuts
variable {partitions : SurfacePartitions observations grid} {preparations :
  BasisArcPreparations regular domains}

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Rectangle.Partition in
/-- Combine original whole-surface, piece and partition-corner cuts before preparing exterior source cuts.

The resulting source owner extends that same base, and all original piece rectangle points retain their explicit
membership in its point list. -/
@[expose] def build (partitions : SurfacePartitions observations grid) (preparations :
  Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular domains)
    (whole : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains) (pieces :
      Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains) : SharedExteriorCuts partitions
      preparations :=
  let partitionPoints := (List.ofFn (fun position : Fin grid.faces.regulars.length => position)).flatMap
    (fun position => (partitions.get position).cuts.boxes.flatMap
      (fun box => [PreparedRectangleCuts.corner box false false, PreparedRectangleCuts.corner box true true]))
  let base : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains := ⟨whole.points ++
    (pieces.points ++ partitionPoints),
    fun position sheet point member => List.mem_append_left _ (whole.includes position sheet point member)⟩
  let source := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts.build preparations base
  ⟨partitionPoints, rfl, base, fun _ member => List.mem_append_right _ (List.mem_append_right _ member), source,
    fun position piece sheet point member => List.mem_append_left _
      (List.mem_append_right _ (List.mem_append_left _ (pieces.includes position piece sheet point member)))⟩

open Purelib.Curves.Hyperelliptic in
/-- View the original shared exterior source cuts as a surface-cut owner using the retained piece inclusion proof. -/
@[expose] def surface (shared : SharedExteriorCuts partitions preparations) :
  Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains :=
  ⟨shared.source.cuts.points, shared.surface_included⟩

open Purelib.Data.List in
open Purelib.Geometry.Rectangle.Partition in
/-- Both original diagonal corners of every partition piece belong to the shared source cut list. -/
theorem corner_mem (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length)
    (high : Bool) : PreparedRectangleCuts.corner ((partitions.get position).cuts.boxes[piece.val]'piece.isLt)
      high high ∈ shared.source.cuts.points := by
  rw [shared.source.points_eq]
  apply List.mem_append_left
  apply shared.partition_included
  rw [shared.partitionPoints_eq]
  apply Flatten.mem_flatMap.mpr
  refine ⟨position, Data.List.OfFn.Basic.mem_ofFn.mpr ⟨position, rfl⟩, ?_⟩
  apply Flatten.mem_flatMap.mpr
  refine ⟨_, List.getElem_mem piece.isLt, ?_⟩
  cases high
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

open Purelib.Curves.Hyperelliptic
open Purelib.Data
open Purelib.Data.List
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Topology
/-- Each original piece's horizontal intervals are the exact bounded filter of the whole-face intervals.

Both meshes use the same retained source cuts, and the original partition corners certify the restriction endpoints;
whole and piece dyadic depths remain independent. -/
theorem piece_x_intervals (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length)
    (sheet : Fin 2) (wholeDepth pieceDepth : Nat) :
    (((Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet pieceDepth).get
      position).entries.get piece).partition.x.intervals =
      (((Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
        wholeDepth).entries.get position).partition.x.intervals).filter
        (fun interval => decide (((partitions.get position).cuts.boxes[piece.val]'piece.isLt).xLower ≤ interval.lower ∧
          interval.upper ≤ ((partitions.get position).cuts.boxes[piece.val]'piece.isLt).xUpper)) := by
  let box := (partitions.get position).cuts.boxes[piece.val]'piece.isLt
  let outer := Geometry.Rectangle.CutPartition.build (grid.faces.regulars[position.val]'position.isLt).cell.box
    (grid.faces.regulars[position.val]'position.isLt).cell.box_proper shared.source.cuts.points
  let inner := Geometry.Rectangle.CutPartition.build box
    ((partitions.get position).cuts.proper (List.getElem_mem piece.isLt)) shared.source.cuts.points
  have refines := (partitions.get position).cuts.refines (List.getElem_mem piece.isLt)
  have inside : (grid.faces.regulars[position.val]'position.isLt).cell.box.xLower ≤ box.xLower ∧
      box.xUpper ≤ (grid.faces.regulars[position.val]'position.isLt).cell.box.xUpper := ⟨refines.1, refines.2.1⟩
  have firstMember : box.xLower ∈ shared.source.cuts.points.map (fun point => point.re) :=
    Map.mem_map.mpr ⟨_, shared.corner_mem position piece false, rfl⟩
  have lastMember : box.xUpper ∈ shared.source.cuts.points.map (fun point => point.re) :=
    Map.mem_map.mpr ⟨_, shared.corner_mem position piece true, rfl⟩
  have firstRetained := outer.x.cut_mem firstMember ⟨inside.1, inner.x.proper.le.trans inside.2⟩
  have lastRetained := outer.x.cut_mem lastMember ⟨inside.1.trans inner.x.proper.le, inside.2⟩
  have equal := PreparedAxisPartitionRestriction.intervals_restriction outer.x inner.x inside.1 inside.2 firstRetained
    lastRetained
  dsimp only [Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes,
    Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build]
  rw [Vector.DependentVector.ofFn_get, Vector.DependentVector.ofFn_get]
  dsimp only [NewtonObservationSurfaceEnergy.LocalMeshes.build]
  rw [Vector.DependentVector.ofFn_get]
  exact equal

/-- Each original piece's vertical intervals are the exact bounded filter of the whole-face intervals.

Both meshes use the same retained source cuts, and the original partition corners certify the restriction endpoints;
whole and piece dyadic depths remain independent. -/
theorem piece_y_intervals (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length)
    (sheet : Fin 2) (wholeDepth pieceDepth : Nat) :
    (((Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet pieceDepth).get
      position).entries.get piece).partition.y.intervals =
      (((Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
        wholeDepth).entries.get position).partition.y.intervals).filter
        (fun interval => decide (((partitions.get position).cuts.boxes[piece.val]'piece.isLt).yLower ≤ interval.lower ∧
          interval.upper ≤ ((partitions.get position).cuts.boxes[piece.val]'piece.isLt).yUpper)) := by
  let box := (partitions.get position).cuts.boxes[piece.val]'piece.isLt
  let outer := Geometry.Rectangle.CutPartition.build (grid.faces.regulars[position.val]'position.isLt).cell.box
    (grid.faces.regulars[position.val]'position.isLt).cell.box_proper shared.source.cuts.points
  let inner := Geometry.Rectangle.CutPartition.build box
    ((partitions.get position).cuts.proper (List.getElem_mem piece.isLt)) shared.source.cuts.points
  have refines := (partitions.get position).cuts.refines (List.getElem_mem piece.isLt)
  have inside : (grid.faces.regulars[position.val]'position.isLt).cell.box.yLower ≤ box.yLower ∧
      box.yUpper ≤ (grid.faces.regulars[position.val]'position.isLt).cell.box.yUpper := refines.2.2
  have firstMember : box.yLower ∈ shared.source.cuts.points.map (fun point => point.im) :=
    Map.mem_map.mpr ⟨_, shared.corner_mem position piece false, rfl⟩
  have lastMember : box.yUpper ∈ shared.source.cuts.points.map (fun point => point.im) :=
    Map.mem_map.mpr ⟨_, shared.corner_mem position piece true, rfl⟩
  have firstRetained := outer.y.cut_mem firstMember ⟨inside.1, inner.y.proper.le.trans inside.2⟩
  have lastRetained := outer.y.cut_mem lastMember ⟨inside.1.trans inner.y.proper.le, inside.2⟩
  have equal := PreparedAxisPartitionRestriction.intervals_restriction outer.y inner.y inside.1 inside.2 firstRetained
    lastRetained
  dsimp only [Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes,
    Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build]
  rw [Vector.DependentVector.ofFn_get, Vector.DependentVector.ofFn_get]
  dsimp only [NewtonObservationSurfaceEnergy.LocalMeshes.build]
  rw [Vector.DependentVector.ofFn_get]
  exact equal

end SharedExteriorCuts
end Purelib.Riemann.Branches.NewtonSharedExteriorCuts
