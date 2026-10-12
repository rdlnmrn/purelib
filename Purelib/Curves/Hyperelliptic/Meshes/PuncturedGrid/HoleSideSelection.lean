module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Pairwise

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularNeighborUniqueness
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Riemann

@[expose] public section

/-! Hole component selection is exactly geometric adjacency, independent of
which certified neighbor bank supplied the retained classification. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSideSelection

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {face : Meshes.PuncturedGridFaces.RegularFace bank} {side :
    Meshes.GridLiftedDualSteps.GridSide}

/-- Equal original hole cells have the same retained position in the unique physical-hole list. -/
theorem hole_position_eq_of_cell (faces : Meshes.PuncturedGridFaces.PuncturedFaces bank)
    (first second : Fin faces.holes.length)
    (equal : faces.holes[first.val].cell = faces.holes[second.val].cell) : first = second := open Purelib in by
  rcases Nat.lt_trichotomy first.val second.val with before | same | after
  · have separated := Data.List.Pairwise.pairwise_getElem faces.holes_pairwise _ _ first.isLt second.isLt before
    exact (separated (Hyperelliptic.Branches.BranchFaceClassification.FaceKind.branch_unique
      faces.holes[first.val].cell_eq
      (equal.trans faces.holes[second.val].cell_eq))).elim
  · exact Fin.ext same
  · have separated := Data.List.Pairwise.pairwise_getElem faces.holes_pairwise _ _ second.isLt first.isLt after
    exact (separated (Hyperelliptic.Branches.BranchFaceClassification.FaceKind.branch_unique
      faces.holes[second.val].cell_eq
      (equal.symm.trans faces.holes[first.val].cell_eq))).elim

/-- Geometric adjacency to the requested original hole selects the supplied component value.

Unique original cell matches identify the retained hole position in the neighbor
classification. Its component selector then returns the original supplied value
without changing either the side witness or the hole list. -/
theorem SideNeighbor.hole_value_of_matches (neighbor : Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor faces face
  side)
    (hole : Fin faces.holes.length) (value : Gaussian.Basic.Canonical)
    (matching : side.Matches face.cell.box faces.holes[hole.val].cell.box) :
    Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue neighbor (.hole hole) value =
      value := by
  cases neighbor with
  | exterior exterior =>
      exact (Meshes.GridLiftedDualSteps.GridSide.exterior_no_match exterior faces.holes[hole.val].cell.box_proper
        faces.holes[hole.val].cell.box_refines matching).elim
  | neighbor cell member neighborMatches location =>
    have equal := Meshes.GridLiftedDualSteps.GridSide.matches_unique side faces.holes[hole.val].member member matching
      neighborMatches
    cases location with
    | regular position foundEq =>
        exact (faces.regulars[position.val].unassigned faces.holes[hole.val].index
          (foundEq.trans (equal.symm.trans faces.holes[hole.val].cell_eq))).elim
    | hole position foundEq =>
        have same := Hyperelliptic.Meshes.PuncturedGrid.HoleSideSelection.hole_position_eq_of_cell faces hole position
          (equal.trans foundEq.symm)
        simp only [Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue, if_pos same,
          -eq_self, -iff_self]
        rfl

/-- The retained hole-component value is exactly the indicator of actual geometric side adjacency.

The original side matches the selected hole exactly when that hole position can
contribute. Every other retained classification returns zero, preserving both the
original geometry and the supplied contribution. -/
theorem SideNeighbor.hole_value_eq (neighbor : Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor faces face side)
    (hole : Fin faces.holes.length) (value : Gaussian.Basic.Canonical) :
    Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue neighbor (.hole hole) value =
      if side.Matches face.cell.box faces.holes[hole.val].cell.box then value else 0 := by
  by_cases matching : side.Matches face.cell.box faces.holes[hole.val].cell.box
  · rw [if_pos matching]
    exact Hyperelliptic.Meshes.PuncturedGrid.HoleSideSelection.SideNeighbor.hole_value_of_matches neighbor hole value
      matching
  · rw [if_neg matching]
    cases neighbor with
    | exterior exterior => rfl
    | neighbor cell member neighborMatches location =>
      cases location with
      | regular position foundEq => rfl
      | hole position foundEq =>
        have different : hole ≠ position := by
          intro same
          subst hole
          apply matching
          rw [← foundEq] at neighborMatches
          exact neighborMatches
        simp only [Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue, if_neg
          different, -eq_self, -iff_self]
        rfl

/-- A fixed side of one hole has at most one adjacent regular face. -/
theorem hole_side_unique (hole : Fin faces.holes.length) (first second : Fin faces.regulars.length)
    (firstMatch : side.Matches faces.regulars[first.val].cell.box faces.holes[hole.val].cell.box)
    (secondMatch : side.Matches faces.regulars[second.val].cell.box faces.holes[hole.val].cell.box) : first = second :=
  Meshes.PuncturedGridFaces.PuncturedFaces.position_eq_of_cell faces first second
    (Meshes.GridLiftedDualSteps.GridSide.matches_unique side.opposite
    faces.regulars[first.val].member faces.regulars[second.val].member firstMatch.reverse secondMatch.reverse)

/-- Summing a fixed original hole side over all regular faces selects its unique adjacent regular-face value. -/
theorem NeighborBank.hole_side_sum (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (hole : Fin
  faces.holes.length)
    (position : Fin faces.regulars.length) (values : Fin faces.regulars.length → Gaussian.Basic.Canonical)
    (matching : side.Matches faces.regulars[position.val].cell.box faces.holes[hole.val].cell.box) :
    FiniteSum.Fin.sumFin (fun index =>
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue
      (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
      (neighbors.entries.get index) side) (.hole hole) (values index)) = values position := by
  have equal (index : Fin faces.regulars.length) :
      Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue
        (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
        (neighbors.entries.get index) side) (.hole hole) (values index) =
        if index = position then values index else 0 := by
    rw [Hyperelliptic.Meshes.PuncturedGrid.HoleSideSelection.SideNeighbor.hole_value_eq
      (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
      (neighbors.entries.get index) side) hole (values index)]
    by_cases same : index = position
    · subst index
      rw [if_pos matching, if_pos rfl]
    · have absent : ¬ side.Matches faces.regulars[index.val].cell.box faces.holes[hole.val].cell.box :=
        fun found => same (Hyperelliptic.Meshes.PuncturedGrid.HoleSideSelection.hole_side_unique hole index position
          found matching)
      rw [if_neg absent, if_neg same]
  rw [FiniteSum.Fin.sumFin_congr equal]
  exact FiniteSum.Fin.sumFin_ite_eq position values

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSideSelection
