module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Membership
import Purelib.Data.List.Nodup

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryCounts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.List.Permutation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedCircuitCorrections
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularNeighborUniqueness
import Init.Prelude
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits

open Purelib.Data.List

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder

open Purelib.Riemann.Meshes

open Purelib.RootIsolation.SquareRoot.Grid

public section

/-! Exact regular-face positions retained by the ordered circuit partition. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryCounts (nodup_ofFn_injective)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {base : Purelib.Data.Gaussian.Basic.Canonical}

/-- Positions come from the retained leaf locations; no face lookup is repeated. -/
@[expose] def regularIndices : {tree : RowCircuitOrder.CellCircuits bank.grid base} → BranchCellBank.CircuitPartition
  faces tree → List (Fin faces.regulars.length)
  | _, .nil => []
  | _, .regular location => [location.index]
  | _, .hole _ => []
  | _, .append first last => first.regularIndices ++ last.regularIndices

/-- Reading the regular-face bank at a retained location gives its exact indexed cell. -/
private theorem location_cell {cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)}
    (location : PuncturedGridFaces.RegularLocation faces.regulars cell) :
    (faces.regulars[location.index.val]'location.index.isLt).cell = cell := by
  rw [location.indexed, location.cell_eq]

/-- A regular-face position occurs in the retained partition precisely when its cell occurs in the circuit tree. -/
theorem regularIndices_exact {tree : RowCircuitOrder.CellCircuits bank.grid base} (partition :
  BranchCellBank.CircuitPartition faces tree)
    (index : Fin faces.regulars.length) : index ∈ partition.regularIndices ↔
      (faces.regulars[index.val]'index.isLt).cell ∈ tree.cells := by
  induction partition with
  | nil => exact ⟨fun impossible => (List.not_mem_nil impossible).elim,
      fun impossible => (List.not_mem_nil impossible).elim⟩
  | @regular cell member stem location =>
      change index ∈ [location.index] ↔ (faces.regulars[index.val]'index.isLt).cell ∈ [cell]
      constructor
      · intro member
        have same := Membership.mem_singleton.mp member
        cases same
        exact Membership.mem_singleton.mpr
          (Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.location_cell
          location)
      · intro member
        apply Membership.mem_singleton.mpr
        exact faces.position_eq_of_cell index location.index ((Membership.mem_singleton.mp member).trans
          (Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.location_cell
          location).symm)
  | @hole cell member stem location =>
      constructor
      · intro impossible
        exact (List.not_mem_nil impossible).elim
      · intro member
        have same := Membership.mem_singleton.mp member
        exact ((faces.regulars[index.val]'index.isLt).unassigned location.hole.index
          (same.trans (location.cell_eq.symm.trans location.hole.cell_eq))).elim
  | @append firstTree lastTree first last ihFirst ihLast =>
      change index ∈ first.regularIndices ++ last.regularIndices ↔
        (faces.regulars[index.val]'index.isLt).cell ∈ firstTree.cells ++ lastTree.cells
      constructor
      · intro member
        rcases Membership.mem_append.mp member with member | member
        · exact Membership.mem_append.mpr (Or.inl (ihFirst.mp member))
        · exact Membership.mem_append.mpr (Or.inr (ihLast.mp member))
      · intro member
        rcases Membership.mem_append.mp member with member | member
        · exact Membership.mem_append.mpr (Or.inl (ihFirst.mpr member))
        · exact Membership.mem_append.mpr (Or.inr (ihLast.mpr member))

/-- A partition of distinct circuit cells contains no repeated regular-face position. -/
theorem regularIndices_unique {tree : RowCircuitOrder.CellCircuits bank.grid base} (partition :
  BranchCellBank.CircuitPartition faces tree)
    (unique : tree.cells.Nodup) : partition.regularIndices.Nodup := by
  induction partition with
  | nil => exact .nil
  | regular => exact Nodup.nodup_singleton _
  | hole => exact .nil
  | append first last ihFirst ihLast =>
      have parts := Permutation.nodup_append_parts unique
      apply Nodup.nodup_append (ihFirst parts.1) (ihLast parts.2.1)
      intro firstIndex firstMember lastIndex lastMember same
      exact parts.2.2 _ ((first.regularIndices_exact _).mp firstMember)
        _ ((last.regularIndices_exact _).mp lastMember)
        (congrArg (fun index : Fin faces.regulars.length => (faces.regulars[index.val]'index.isLt).cell) same)

/-- Compiling the retained partition preserves its exact ordered list of regular-face positions. -/
theorem compile_regularIndices {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}
    (edges : RootEdgeBank frames) (vertices : LiftedVertices.VertexBank bank.grid)
    {tree : RowCircuitOrder.CellCircuits bank.grid base} (partition : BranchCellBank.CircuitPartition faces tree) (sheet
      : Fin 2) :
    ((partition.compile edges vertices sheet).regulars.map (fun occurrence => occurrence.location.index)) =
      partition.regularIndices := by
  induction partition generalizing sheet with
  | nil => rfl
  | regular => rfl
  | hole => rfl
  | append first last ihFirst ihLast =>
      change List.map _ ((first.compile edges vertices sheet).regulars ++
        (last.compile edges vertices (first.compile edges vertices sheet).finish).regulars) = _
      rw [Map.map_append, ihFirst, ihLast]
      rfl

/-- Complete regular-cell coverage becomes a permutation of the actual cached face positions. -/
theorem regularIndices_coverage {tree : RowCircuitOrder.CellCircuits bank.grid base} (partition :
  BranchCellBank.CircuitPartition faces tree)
    (unique : tree.cells.Nodup)
    (complete : ∀ index : Fin faces.regulars.length, (faces.regulars[index.val]'index.isLt).cell ∈ tree.cells) :
    List.Perm partition.regularIndices (List.ofFn (fun index : Fin faces.regulars.length => index)) := by
  apply Permutation.of_nodup_mem_iff (partition.regularIndices_unique unique)
    (BoundaryCounts.nodup_ofFn_injective _ (fun _ _ equal => equal))
  intro index
  exact ⟨fun _ => OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩,
    fun _ => (partition.regularIndices_exact index).mpr (complete index)⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
