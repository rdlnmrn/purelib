module
import Purelib.Data.List.Flatten
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic

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
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitionRestriction
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
public import Purelib.Riemann.Branches.NewtonSharedExteriorCuts

public section

/-! Concatenating all observation-piece interval spines gives the exact
whole-face spine on the retained shared cut bank. -/
namespace Purelib.Riemann.RootContinuation.NewtonSharedExteriorIntervalSpines

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

open Purelib.Data in

open Purelib.Curves in
open Purelib.Data in
open Purelib.Geometry in
/-- Concatenating actual observation-piece horizontal interval lists gives the retained whole-face horizontal spine.

The original shared cut bank contains every piece corner, so exact interval restriction identifies the ordered lists
independently of whole and piece mesh depths. -/
theorem x_spine (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (row : Fin ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows
      (partitions.get position)) + 1))
    (sheet : Fin 2) (wholeDepth pieceDepth : Nat) :
    ((Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
      wholeDepth).entries.get position).partition.x.intervals =
      (List.ofFn (fun column : Fin ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns (partitions.get position))
        + 1) =>
        (((Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet
          pieceDepth).get position).entries.get
          ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) column
            row)).partition.x.intervals)).flatten := by
  let partition := partitions.get position
  let box := (grid.faces.regulars[position.val]'position.isLt).cell.box
  let outer := Geometry.Rectangle.AxisPartition.build box.xLower box.xUpper
    (grid.faces.regulars[position.val]'position.isLt).cell.box_proper.1
    (shared.source.cuts.points.map (fun point => point.re))
  have retained (interval : Rectangle.Partition.PreparedAxisPartitions.Interval) (member : interval ∈
    partition.cuts.x.intervals) :
      interval.lower ∈ outer.coordinates ∧ interval.upper ∈ outer.coordinates := by
    obtain ⟨n, bound, equal⟩ := List.mem_iff_getElem.mp member
    let index : Fin ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns partition) + 1) := Fin.cast
      (Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns_eq partition).symm ⟨n, bound⟩
    have pointMember (high : Bool) : (if high then interval.upper else interval.lower) ∈
        shared.source.cuts.points.map (fun point => point.re) := by
      apply List.Map.mem_map.mpr
      refine ⟨_, shared.corner_mem position ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition)
        index 0) high, ?_⟩
      rw [(Hyperelliptic.Meshes.Newton.Surface.PieceIndices.piece_box partition)]
      cases high
      · exact congrArg (fun entry : Rectangle.Partition.PreparedAxisPartitions.Interval => entry.lower) equal
      · exact congrArg (fun entry : Rectangle.Partition.PreparedAxisPartitions.Interval => entry.upper) equal
    have bounds := partition.cuts.x.interval_bounds member
    exact ⟨outer.cut_mem (pointMember false) ⟨bounds.1, interval.ordered.le.trans bounds.2⟩,
      outer.cut_mem (pointMember true) ⟨bounds.1.trans interval.ordered.le, bounds.2⟩⟩
  let restrict := fun interval : Rectangle.Partition.PreparedAxisPartitions.Interval =>
    outer.intervals.filter (fun fine => decide (interval.lower ≤ fine.lower ∧ fine.upper ≤ interval.upper))
  have pieces :
      List.ofFn (fun column : Fin ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns partition) + 1) =>
        (((Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet
          pieceDepth).get position).entries.get
          ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition) column row)).partition.x.intervals) =
        partition.cuts.x.intervals.map restrict := by
    apply Eq.trans (List.OfFn.Basic.ofFn_congr (fun column =>
      show (((Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface
        sheet pieceDepth).get position).entries.get
        ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition) column row)).partition.x.intervals =
        restrict (partition.cuts.x.intervals[(Fin.cast (Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns_eq
          partition) column).val]'(Fin.cast (Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns_eq partition)
          column).isLt) from ?_))
      (List.OfFn.Basic.ofFn_map_cast partition.cuts.x.intervals
        (Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns_eq partition) restrict)
    rw [shared.piece_x_intervals position ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition)
      column row) sheet wholeDepth pieceDepth,
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build_x_intervals,
        (Hyperelliptic.Meshes.Newton.Surface.PieceIndices.piece_box partition)]
    rfl
  rw [Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build_x_intervals]
  exact (Rectangle.Partition.PreparedAxisPartitionRestriction.intervals_flatMap outer partition.cuts.x retained).trans
    ((List.Flatten.flatMap_eq partition.cuts.x.intervals restrict).trans (congrArg List.flatten pieces).symm)

open Purelib.Curves in
open Purelib.Data in
open Purelib.Geometry in
/-- Concatenating actual observation-piece vertical interval lists gives the retained whole-face vertical spine.

The original shared cut bank contains every piece corner, so exact interval restriction identifies the ordered lists
independently of whole and piece mesh depths. -/
theorem y_spine (shared : SharedExteriorCuts partitions preparations)
    (position : Fin grid.faces.regulars.length) (column : Fin ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.columns
      (partitions.get position)) + 1))
    (sheet : Fin 2) (wholeDepth pieceDepth : Nat) :
    ((Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains shared.source.cuts sheet
      wholeDepth).entries.get position).partition.y.intervals =
      (List.ofFn (fun row : Fin ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows (partitions.get position)) + 1)
        =>
        (((Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet
          pieceDepth).get position).entries.get
          ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex (partitions.get position)) column
            row)).partition.y.intervals)).flatten := by
  let partition := partitions.get position
  let box := (grid.faces.regulars[position.val]'position.isLt).cell.box
  let outer := Geometry.Rectangle.AxisPartition.build box.yLower box.yUpper
    (grid.faces.regulars[position.val]'position.isLt).cell.box_proper.2
    (shared.source.cuts.points.map (fun point => point.im))
  have retained (interval : Rectangle.Partition.PreparedAxisPartitions.Interval) (member : interval ∈
    partition.cuts.y.intervals) :
      interval.lower ∈ outer.coordinates ∧ interval.upper ∈ outer.coordinates := by
    obtain ⟨n, bound, equal⟩ := List.mem_iff_getElem.mp member
    let index : Fin ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows partition) + 1) := Fin.cast
      (Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows_eq partition).symm ⟨n, bound⟩
    have pointMember (high : Bool) : (if high then interval.upper else interval.lower) ∈
        shared.source.cuts.points.map (fun point => point.im) := by
      apply List.Map.mem_map.mpr
      refine ⟨_, shared.corner_mem position ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition) 0
        index) high, ?_⟩
      rw [(Hyperelliptic.Meshes.Newton.Surface.PieceIndices.piece_box partition)]
      cases high
      · exact congrArg (fun entry : Rectangle.Partition.PreparedAxisPartitions.Interval => entry.lower) equal
      · exact congrArg (fun entry : Rectangle.Partition.PreparedAxisPartitions.Interval => entry.upper) equal
    have bounds := partition.cuts.y.interval_bounds member
    exact ⟨outer.cut_mem (pointMember false) ⟨bounds.1, interval.ordered.le.trans bounds.2⟩,
      outer.cut_mem (pointMember true) ⟨bounds.1.trans interval.ordered.le, bounds.2⟩⟩
  let restrict := fun interval : Rectangle.Partition.PreparedAxisPartitions.Interval =>
    outer.intervals.filter (fun fine => decide (interval.lower ≤ fine.lower ∧ fine.upper ≤ interval.upper))
  have pieces :
      List.ofFn (fun row : Fin ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows partition) + 1) =>
        (((Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface sheet
          pieceDepth).get position).entries.get
          ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition) column row)).partition.y.intervals) =
        partition.cuts.y.intervals.map restrict := by
    apply Eq.trans (List.OfFn.Basic.ofFn_congr (fun row =>
      show (((Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains shared.surface
        sheet pieceDepth).get position).entries.get
        ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition) column row)).partition.y.intervals =
        restrict (partition.cuts.y.intervals[(Fin.cast (Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows_eq
          partition) row).val]'(Fin.cast (Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows_eq partition) row).isLt)
          from ?_))
      (List.OfFn.Basic.ofFn_map_cast partition.cuts.y.intervals
        (Hyperelliptic.Meshes.Newton.Surface.PieceIndices.rows_eq partition) restrict)
    rw [shared.piece_y_intervals position ((Hyperelliptic.Meshes.Newton.Surface.PieceIndices.pieceIndex partition)
      column row) sheet wholeDepth pieceDepth,
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build_y_intervals,
        (Hyperelliptic.Meshes.Newton.Surface.PieceIndices.piece_box partition)]
    rfl
  rw [Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build_y_intervals]
  exact (Rectangle.Partition.PreparedAxisPartitionRestriction.intervals_flatMap outer partition.cuts.y retained).trans
    ((List.Flatten.flatMap_eq partition.cuts.y.intervals restrict).trans (congrArg List.flatten pieces).symm)

end Purelib.Riemann.RootContinuation.NewtonSharedExteriorIntervalSpines
