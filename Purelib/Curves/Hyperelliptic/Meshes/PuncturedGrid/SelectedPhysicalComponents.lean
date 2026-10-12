module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.PuncturedGridFaces

@[expose] public section

/-! Component readback for the selected physical-side evaluation. Each hole
index is the retained neighbor index, including zero and repeated side values. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues (PhysicalComponent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides (value)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition.SelectedSides (physicalEvaluation)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_swap sumFin_sub sumFin_add)
attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher} {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank}

/-- The actual selected side values associated to one physical component. -/
def componentEvaluation (neighbors : PuncturedFaces.NeighborBank faces)
    (keep : Fin faces.regulars.length → Bool) (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length →
      Data.Gaussian.Basic.Canonical)
    (component : PhysicalComponentValues.PhysicalComponent faces) : Gaussian :=
  FiniteSum.Fin.sumFin (fun p => SideNeighbor.componentValue (neighbors.entries.get p).right component
    (SelectedSides.value (keep p) (values .right p))) -
    FiniteSum.Fin.sumFin (fun p => SideNeighbor.componentValue (neighbors.entries.get p).left component
      (SelectedSides.value (keep p) (values .left p))) -
    (FiniteSum.Fin.sumFin (fun p => SideNeighbor.componentValue (neighbors.entries.get p).top component
      (SelectedSides.value (keep p) (values .top p))) -
      FiniteSum.Fin.sumFin (fun p => SideNeighbor.componentValue (neighbors.entries.get p).bottom component
        (SelectedSides.value (keep p) (values .bottom p))))

/-- The selected physical values for one side split into the original exterior component and retained hole components.
-/
private theorem side_components (neighbors : PuncturedFaces.NeighborBank faces)
    (keep : Fin faces.regulars.length → Bool) (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length →
      Data.Gaussian.Basic.Canonical) (side : GridLiftedDualSteps.GridSide) :
    FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue (FaceNeighbors.at (neighbors.entries.get p) side)
      (SelectedSides.value (keep p) (values side p))) =
      FiniteSum.Fin.sumFin (fun p => SideNeighbor.componentValue (FaceNeighbors.at (neighbors.entries.get p) side)
        .exterior (SelectedSides.value (keep p) (values side p))) +
      FiniteSum.Fin.sumFin (fun hole => FiniteSum.Fin.sumFin (fun p =>
        SideNeighbor.componentValue (FaceNeighbors.at (neighbors.entries.get p) side) (.hole hole) (SelectedSides.value
          (keep p) (values side p)))) := by
  rw [FiniteSum.Fin.sumFin_congr (fun p => SideNeighbor.physical_components (FaceNeighbors.at (neighbors.entries.get p)
    side) (SelectedSides.value (keep p) (values side p))), FiniteSum.Fin.sumFin_add,
    FiniteSum.Fin.sumFin_swap (fun p hole => SideNeighbor.componentValue (FaceNeighbors.at (neighbors.entries.get p)
      side) (.hole hole) (SelectedSides.value (keep p) (values side p)))]

/-- The complete selected physical-side evaluation equals its exterior evaluation plus the sum over original hole
indices.

The equality preserves zero terms, repeated occurrences and the side-neighbor assignments of the retained bank. -/
theorem physicalEvaluation_components (neighbors : PuncturedFaces.NeighborBank faces)
    (keep : Fin faces.regulars.length → Bool) (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length →
      Data.Gaussian.Basic.Canonical) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition.SelectedSides.physicalEvaluation
      neighbors keep values = Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation
      neighbors keep values .exterior +
      FiniteSum.Fin.sumFin (fun hole =>
        Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation neighbors keep values
        (.hole hole)) := by
  have bottom := Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents.side_components neighbors keep
    values .bottom
  have right := Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents.side_components neighbors keep
    values .right
  have top := Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents.side_components neighbors keep values
    .top
  have left := Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents.side_components neighbors keep
    values .left
  dsimp only [FaceNeighbors.at] at bottom right top left
  unfold SelectedSides.physicalEvaluation
  rw [right, left, top, bottom]
  simp only [Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation,
    FiniteSum.Fin.sumFin_sub]
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
