module
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.UnmatchedPhysicalSides
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitLocations
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Tactic.QuotientFreeOmega

/-! Exact finite selection of regular and physical side contributions. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
public section
open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Riemann

namespace BranchCellBank.PuncturedFaces

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {face : Meshes.PuncturedGridFaces.RegularFace bank} {side :
    Meshes.GridLiftedDualSteps.GridSide}

attribute [local congr] FiniteSum.Fin.sumFin_congr

/-- Decide whether the retained side neighbor is the regular face at a given original list position. -/
instance (neighbor : Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor faces face side) (position : Fin
  faces.regulars.length) :
    Decidable (neighbor.RegularAt position) := by
  cases neighbor with
  | neighbor cell member matching location =>
    cases location <;> unfold Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor.RegularAt <;> infer_instance
  | exterior equal => unfold Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor.RegularAt; infer_instance

/-- Retain the supplied value precisely when the original side neighbor is regular. -/
@[expose]
def SideNeighbor.regularValue (neighbor : Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor faces face side) (value
  : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  match neighbor with
  | .neighbor _ _ _ (.regular _ _) => value
  | .neighbor _ _ _ (.hole _ _) => 0
  | .exterior _ => 0

/-- Retain the supplied value precisely when the original side meets a hole or exterior boundary. -/
@[expose]
def SideNeighbor.physicalValue (neighbor : Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor faces face side) (value
  : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  match neighbor with
  | .neighbor _ _ _ (.regular _ _) => 0
  | .neighbor _ _ _ (.hole _ _) => value
  | .exterior _ => value

/-- Every side value splits exactly into its original regular and physical contributions. -/
theorem SideNeighbor.value_split (neighbor : Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor faces face side)
  (value : Gaussian.Basic.Canonical) :
    value =
      Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
      neighbor value +
      Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.physicalValue
      neighbor value := by
  cases neighbor with
  | neighbor cell member matching location =>
      cases location <;> dsimp only [regularValue, physicalValue] <;> ring1
  | exterior equal => dsimp only [regularValue, physicalValue]; ring1

/-- Summing the regular-position indicator selects exactly the retained regular neighbor contribution.

The finite neighbor classification keeps the same matching side and retained contribution. Each branch reads the
original scalar value at its supplied index before summing. -/
theorem SideNeighbor.sum_regular (neighbor : Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor faces face side)
  (value : Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun position => if neighbor.RegularAt position then value else 0) =
      Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
      neighbor value := by
  cases neighbor with
  | neighbor cell member matching location =>
      cases location with
      | regular found equal =>
          change FiniteSum.Fin.sumFin (fun position => if found = position then value else 0) = value
          have swap : ∀ position : Fin faces.regulars.length,
              (if found = position then value else 0) = (if position = found then value else 0) := by
            intro position
            by_cases equal : found = position
            · rewrite [if_pos equal, if_pos equal.symm]
              exact Eq.refl _
            · rewrite [if_neg equal, if_neg (fun h => equal h.symm)]
              exact Eq.refl _
          rw [FiniteSum.Fin.sumFin_congr swap]
          exact FiniteSum.Fin.sumFin_ite_eq found (fun _ => value)
      | hole found equal =>
          change FiniteSum.Fin.sumFin (fun _ : Fin faces.regulars.length => if False then value else 0) = 0
          change FiniteSum.Fin.sumFin (fun _ : Fin faces.regulars.length => (0 : Gaussian.Basic.Canonical)) = 0
          exact FiniteSum.Fin.sumFin_zero
  | exterior equal =>
      change FiniteSum.Fin.sumFin (fun _ : Fin faces.regulars.length => if False then value else 0) = 0
      change FiniteSum.Fin.sumFin (fun _ : Fin faces.regulars.length => (0 : Gaussian.Basic.Canonical)) = 0
      exact FiniteSum.Fin.sumFin_zero

/-- Summing actual geometric side matches selects exactly the original regular neighbor contribution.

The finite neighbor classification keeps the same matching side and retained contribution. Each branch reads the
original scalar value at its supplied index before summing. -/
theorem SideNeighbor.sum_matching (neighbor : Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor faces face side)
  (value : Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun position : Fin faces.regulars.length => if side.Matches face.cell.box (faces.regulars.get
      position).cell.box then value else 0) =
      Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
        neighbor value := by
  have equal : ∀ position : Fin faces.regulars.length,
      (if side.Matches face.cell.box (faces.regulars.get position).cell.box then value else 0) =
        (if neighbor.RegularAt position then value else 0) := by
    intro position
    by_cases regular : neighbor.RegularAt position
    · have matching : side.Matches face.cell.box (faces.regulars.get position).cell.box :=
        neighbor.matches_of_regular position regular
      rewrite [if_pos regular, if_pos matching]
      exact Eq.refl _
    · have unmatched : ¬side.Matches face.cell.box (faces.regulars.get position).cell.box :=
        fun matching => regular (neighbor.regular_of_matches position matching)
      rewrite [if_neg regular, if_neg unmatched]
      exact Eq.refl _
  rw [FiniteSum.Fin.sumFin_congr equal]
  exact Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.sum_regular
    neighbor value

/-- Select the retained neighbor on the requested oriented side. -/
@[expose]
def FaceNeighbors.at (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.FaceNeighbors faces face) : (side :
  Meshes.GridLiftedDualSteps.GridSide) → Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor faces face side
  | .bottom => neighbors.bottom
  | .right => neighbors.right
  | .top => neighbors.top
  | .left => neighbors.left

/-- The finite sum of matching regular-side differences equals the outgoing regular contribution minus the opposite-side
incoming contribution.

The identity uses the original neighbor bank and its geometric matching relation without changing the face enumeration.
-/
theorem NeighborBank.pair_sum (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (side :
  Meshes.GridLiftedDualSteps.GridSide)
    (outgoing incoming : Fin faces.regulars.length → Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun next =>
      if side.Matches faces.regulars[first.val].cell.box faces.regulars[next.val].cell.box then
        outgoing first - incoming next else 0)) =
      FiniteSum.Fin.sumFin (fun first =>
        Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
        (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
        (neighbors.entries.get first) side) (outgoing first)) -
        FiniteSum.Fin.sumFin (fun next =>
          SideNeighbor.regularValue
          (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
          (neighbors.entries.get next) side.opposite) (incoming next)) := by
  have split : ∀ first next : Fin faces.regulars.length,
      (if side.Matches faces.regulars[first.val].cell.box faces.regulars[next.val].cell.box then
        outgoing first - incoming next else 0) =
      (if side.Matches faces.regulars[first.val].cell.box faces.regulars[next.val].cell.box then outgoing first else 0)
        -
        (if side.Matches faces.regulars[first.val].cell.box faces.regulars[next.val].cell.box then incoming next else 0)
          := by
    intro first next
    by_cases matching : side.Matches faces.regulars[first.val].cell.box faces.regulars[next.val].cell.box
    · rewrite [if_pos matching, if_pos matching, if_pos matching]
      exact Eq.refl _
    · rewrite [if_neg matching, if_neg matching, if_neg matching, Data.Gaussian.Basic.sub_zero]
      exact Eq.refl _
  rw [FiniteSum.Fin.sumFin_congr (fun first => FiniteSum.Fin.sumFin_congr (split first))]
  simp only [FiniteSum.Fin.sumFin_sub]
  have regularRows : ∀ first : Fin faces.regulars.length,
      FiniteSum.Fin.sumFin (fun next => if side.Matches faces.regulars[first.val].cell.box
        faces.regulars[next.val].cell.box then outgoing first else 0) =
        Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.regularValue
          (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
            (neighbors.entries.get first) side) (outgoing first) := by
    intro first
    simpa only [List.get_eq_getElem] using
      (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.sum_matching
        (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
          (neighbors.entries.get first) side) (outgoing first))
  rw [FiniteSum.Fin.sumFin_congr regularRows]
  rw [FiniteSum.Fin.sumFin_swap (fun first next : Fin faces.regulars.length =>
    if side.Matches faces.regulars[first.val].cell.box faces.regulars[next.val].cell.box then incoming next else 0)]
  congr 1
  apply FiniteSum.Fin.sumFin_congr
  intro next
  have reversed : ∀ first : Fin faces.regulars.length,
      (if side.Matches faces.regulars[first.val].cell.box faces.regulars[next.val].cell.box then incoming next else 0) =
      (if side.opposite.Matches faces.regulars[next.val].cell.box faces.regulars[first.val].cell.box then incoming next
        else 0) := by
    intro first
    have equivalence : side.Matches faces.regulars[first.val].cell.box faces.regulars[next.val].cell.box ↔
        side.opposite.Matches faces.regulars[next.val].cell.box faces.regulars[first.val].cell.box := by
      cases side <;> exact ⟨fun matching => matching.reverse, fun matching => matching.reverse⟩
    by_cases matching : side.Matches faces.regulars[first.val].cell.box faces.regulars[next.val].cell.box
    · rw [if_pos matching, if_pos (equivalence.mp matching)]
    · rw [if_neg matching, if_neg (fun h => matching (equivalence.mpr h))]
  rw [FiniteSum.Fin.sumFin_congr reversed]
  exact Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.SideNeighbor.sum_matching
    (Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
    (neighbors.entries.get next) side.opposite) (incoming next)

end BranchCellBank.PuncturedFaces
end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
