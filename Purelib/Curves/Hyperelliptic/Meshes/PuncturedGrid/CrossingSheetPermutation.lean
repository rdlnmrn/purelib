module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Algebra

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.GridLiftedFaces

open Purelib.Riemann.Meshes.GridLiftedMesh

@[expose] public section

/-! Actual dual crossings permute both retained face sheets. -/
section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (Crossing)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {face : RegularFace bank}

section

namespace Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

/-- Lifted faces with equal original starting sheets have equal transported starting sheets on every side. -/
theorem sideStartSheet_eq {firstSheet lastSheet
  : Fin 2}
    (first : BranchCellBank.LiftedFace vertices edges face firstSheet) (last : BranchCellBank.LiftedFace vertices edges
      face lastSheet)
    (equal : firstSheet = lastSheet) (side : GridLiftedDualSteps.GridSide) : first.sideStartSheet side =
      last.sideStartSheet side := by
  cases equal
  cases side with
  | bottom => rfl
  | right => exact first.bottom_eq.trans last.bottom_eq.symm
  | top =>
      change first.upperRight = last.upperRight
      rw [first.right_eq, last.right_eq, first.bottom_eq, last.bottom_eq]
  | left =>
      change first.upperLeft = last.upperLeft
      rw [first.top_eq, last.top_eq, first.right_eq, last.right_eq, first.bottom_eq, last.bottom_eq]

/-- The two original face sheets have distinct transported finishing sheets on every side. -/
theorem sideFinishSheet_ne (zero :
  BranchCellBank.LiftedFace vertices edges face 0) (one : BranchCellBank.LiftedFace vertices edges face 1)
    (side : GridLiftedDualSteps.GridSide) : zero.sideFinishSheet side ≠ one.sideFinishSheet side := by
  cases side with
  | bottom => exact zero.sideStartSheet_ne one .right
  | right => exact zero.sideStartSheet_ne one .top
  | top => exact zero.sideStartSheet_ne one .left
  | left => exact (by decide : (0 : Fin 2) ≠ 1)

end Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

end

section
variable {faces : PuncturedFaces bank} {mesh :
  LiftedMesh vertices edges faces}
  {firstPosition nextPosition : Fin faces.regulars.length} {firstSide nextSide :
    GridSide}
  {firstUpper lastUpper : Bool}

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.Crossing

/-- Crossings from the two original face sheets reach distinct destination sheets. -/
theorem next_sheet_ne
    {zero : mesh.LocatedFace firstPosition 0} {one : mesh.LocatedFace firstPosition 1}
    (first : LiftedMesh.Crossing zero firstSide nextPosition nextSide firstUpper lastUpper)
    (last : LiftedMesh.Crossing one firstSide nextPosition nextSide firstUpper lastUpper) :
    first.next.sheet ≠ last.next.sheet := by
  intro equal
  have same := first.next.located.lifted.sideStartSheet_eq last.next.located.lifted equal nextSide
  exact (zero.lifted.sideFinishSheet_ne one.lifted firstSide)
    (first.next.start_eq.symm.trans (same.trans last.next.start_eq))

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.Crossing

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingSheetPermutation.LiftedMesh

/-- A pair of distinct indices in the two-element sheet set preserves the sum of both Gaussian values. -/
private theorem two_sum (zero one : Fin 2) (different : zero ≠ one)
    (values : Fin 2 → Data.Gaussian.Basic.Canonical) : values zero + values one = values 0 + values 1 := by
  have unequal : zero.val ≠ one.val := fun equal => different (Fin.ext equal)
  have zeroBound := zero.isLt
  have oneBound := one.isLt
  by_cases first : zero.val = 0
  · have second : one.val = 1 := by omega
    rw [show zero = 0 from Fin.ext first, show one = 1 from Fin.ext second]
  · have first : zero.val = 1 := by omega
    have second : one.val = 0 := by omega
    rw [show zero = 1 from Fin.ext first, show one = 0 from Fin.ext second]
    exact add_comm _ _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingSheetPermutation.LiftedMesh

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingSheetPermutation.LiftedMesh.Crossing

/-- The two actual dual crossings permute the destination sheets and therefore preserve their finite sum. -/
theorem sum_destination
    (source : (sheet : Fin 2) → mesh.LocatedFace firstPosition sheet)
    (crossings : (sheet : Fin 2) → LiftedMesh.Crossing (source sheet) firstSide nextPosition nextSide firstUpper
      lastUpper)
    (values : Fin 2 → Data.Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun sheet => values (crossings sheet).next.sheet) =
      FiniteSum.Fin.sumFin values := by
  simp only [FiniteSum.Fin.sumFin_succ]
  change values (crossings 0).next.sheet + (values (crossings 1).next.sheet + 0) = values 0 + (values 1 + 0)
  simpa only [add_zero] using CrossingSheetPermutation.LiftedMesh.two_sum _ _
    ((crossings 0).next_sheet_ne (crossings 1)) values

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingSheetPermutation.LiftedMesh.Crossing

end
end
