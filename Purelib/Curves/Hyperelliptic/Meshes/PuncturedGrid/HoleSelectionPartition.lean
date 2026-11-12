module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleNeighborValues
import Init.Prelude
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.PuncturedGridFaces

public section

/-! Exact selected/omitted partition of all hole-side values. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSelectionPartition
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides (value)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents (componentEvaluation)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub sumFin_swap sumFin_zero)
attribute [local congr] FiniteSum.Fin.sumFin_congr
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher} {faces : PuncturedFaces bank}

/-- The complete signed hole-side evaluation on the original neighbor bank. -/
@[expose] def fullHoleEvaluation (neighbors : PuncturedFaces.NeighborBank faces)
    (values : GridSide → Fin faces.regulars.length → Gaussian) : Gaussian :=
  FiniteSum.Fin.sumFin (fun p => (neighbors.entries.get p).right.holeValue (values .right p)) -
    FiniteSum.Fin.sumFin (fun p => (neighbors.entries.get p).left.holeValue (values .left p)) -
    (FiniteSum.Fin.sumFin (fun p => (neighbors.entries.get p).top.holeValue (values .top p)) -
      FiniteSum.Fin.sumFin (fun p => (neighbors.entries.get p).bottom.holeValue (values .bottom p)))

/-- The signed hole-side contribution of precisely the regular faces omitted by the selection. -/
@[expose] def omittedHoleEvaluation (neighbors : PuncturedFaces.NeighborBank faces)
    (keep : Fin faces.regulars.length → Bool) (values : GridSide → Fin faces.regulars.length →
      Gaussian) : Gaussian :=
  FiniteSum.Fin.sumFin (fun p => if keep p = false then (neighbors.entries.get p).right.holeValue (values .right p) else
    0) -
    FiniteSum.Fin.sumFin (fun p => if keep p = false then (neighbors.entries.get p).left.holeValue (values .left p) else
      0) -
    (FiniteSum.Fin.sumFin (fun p => if keep p = false then (neighbors.entries.get p).top.holeValue (values .top p) else
      0) -
      FiniteSum.Fin.sumFin (fun p => if keep p = false then (neighbors.entries.get p).bottom.holeValue (values .bottom
        p) else 0))

/-- One original hole-neighbor value splits into selected component values and its omitted-face contribution. -/
private theorem neighbor_partition {face : RegularFace bank} {side : GridSide}
    (neighbor : PuncturedFaces.SideNeighbor faces face side) (keep : Bool) (v : Gaussian) :
    neighbor.holeValue v = FiniteSum.Fin.sumFin (fun hole => SideNeighbor.componentValue neighbor (.hole hole)
      (SelectedSides.value keep v)) +
      (if keep = false then neighbor.holeValue v else 0) := by
  cases keep with
  | true =>
    simp only [-eq_self, -iff_self, SelectedSides.value, if_neg (show (true : Bool) ≠ false by decide +kernel),
      add_zero]
    exact neighbor.holeValue_components v
  | false =>
    have zero (hole : Fin faces.holes.length) : SideNeighbor.componentValue neighbor (.hole hole) (0 :
      Gaussian) = 0 := by
      cases neighbor with
      | exterior _ => rfl
      | neighbor _ _ _ location =>
        cases location with
        | regular _ _ => rfl
        | hole found _ => exact ite_self _
    simp only [-eq_self, -iff_self, SelectedSides.value, if_neg (show (false : Bool) ≠ true by decide +kernel), if_pos
      (rfl : (false : Bool) = false), FiniteSum.Fin.sumFin_congr zero, FiniteSum.Fin.sumFin_zero, zero_add]
    rfl

/-- The complete hole contribution of one side splits into selected hole components and omitted-face values. -/
private theorem side_partition (neighbors : PuncturedFaces.NeighborBank faces)
    (keep : Fin faces.regulars.length → Bool) (values : GridSide → Fin faces.regulars.length →
      Gaussian) (side : GridSide) :
    FiniteSum.Fin.sumFin (fun p => (FaceNeighbors.at (neighbors.entries.get p) side).holeValue (values side p)) =
      FiniteSum.Fin.sumFin (fun hole => FiniteSum.Fin.sumFin (fun p => SideNeighbor.componentValue (FaceNeighbors.at
        (neighbors.entries.get p) side) (.hole hole) (SelectedSides.value (keep p) (values side p)))) +
      FiniteSum.Fin.sumFin (fun p => if keep p = false then (FaceNeighbors.at (neighbors.entries.get p) side).holeValue
        (values side p) else 0) := by
  rw [FiniteSum.Fin.sumFin_congr (fun p =>
    HoleSelectionPartition.neighbor_partition (FaceNeighbors.at
    (neighbors.entries.get p) side) (keep p) (values side p)), FiniteSum.Fin.sumFin_add,
    FiniteSum.Fin.sumFin_swap (fun p hole => SideNeighbor.componentValue (FaceNeighbors.at (neighbors.entries.get p)
      side) (.hole hole) (SelectedSides.value (keep p) (values side p)))]

/-- The complete hole-side evaluation equals the sum of selected hole components plus the actual omitted contribution.
-/
theorem fullHoleEvaluation_partition (neighbors : PuncturedFaces.NeighborBank faces)
    (keep : Fin faces.regulars.length → Bool) (values : GridSide → Fin faces.regulars.length →
      Gaussian) :
    HoleSelectionPartition.fullHoleEvaluation neighbors values =
      FiniteSum.Fin.sumFin (fun hole => SelectedPhysicalComponents.componentEvaluation neighbors keep values (.hole
        hole)) + HoleSelectionPartition.omittedHoleEvaluation neighbors keep
        values := by
  have b := HoleSelectionPartition.side_partition neighbors keep values
    .bottom
  have r := HoleSelectionPartition.side_partition neighbors keep values .right
  have t := HoleSelectionPartition.side_partition neighbors keep values .top
  have l := HoleSelectionPartition.side_partition neighbors keep values .left
  dsimp only [FaceNeighbors.at] at b r t l
  unfold HoleSelectionPartition.fullHoleEvaluation
  rw [b, r, t, l]
  simp only [-eq_self, -iff_self, SelectedPhysicalComponents.componentEvaluation,
    HoleSelectionPartition.omittedHoleEvaluation, FiniteSum.Fin.sumFin_sub]
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSelectionPartition
