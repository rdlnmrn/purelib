module
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
public import Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceDecisions
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Tactic.Ring

public section

/-! Exact signed readback of the acquired interface list to the selected
boundary expression. The original sheet occurrences and directions remain. -/
namespace Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceReadback

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests (PerimeterTraceBank)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (FacePerimeters)
open Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank (InterfaceRow InterfaceBank)
open Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters.AllHoleExcision (fineMask)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (sideAreaRemainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.LiftedPuncturedGrid
  (selectedSideRemainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandSideReferences (BandSideReference)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {lifted : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank lifted.frames
    grid.faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
  {meshTarget : Rational} {i j : Fin genus}
  {request : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains cuts sheet
    coarseDepth) fixed meshTarget}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub sumFin_zero sumFin_swap)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

namespace InterfaceRow
variable {excision : AllHoleExcision grid lifted} {traces :
  PerimeterTraceBank request}
  {position : Fin grid.faces.regulars.length}

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- The retained row's eight signed occurrences equal the two-sheet oriented side sum.

Both sheets retain the original bottom, right, negative top and negative left order and the same perimeter cache. -/
theorem sum_values {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
    (row : InterfaceRow excision traces i j position) (perimeters :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize i j) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (row.values perimeters) = FiniteSum.Fin.sumFin (fun sheet =>
      row.bottom.value perimeters sheet + row.right.value perimeters sheet -
        row.top.value perimeters sheet - row.left.value perimeters sheet) := by
  simp only [-eq_self, -iff_self, NewtonSelectedInterfaceBank.InterfaceRow.values,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum, FiniteSum.Fin.sumFin_succ]
  change _ = _ + (_ + 0)
  rw [show (Fin.succ 0 : Fin 2) = 1 by decide]
  ring1

end InterfaceRow

namespace InterfaceBank
variable {excision : AllHoleExcision grid lifted} {traces :
  PerimeterTraceBank request}

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
/-- The retained interface decisions sum to the original selected-to-discarded outgoing contribution on one side. -/
private theorem sum_side {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (bank : InterfaceBank excision traces i j) (neighbors : PuncturedFaces.NeighborBank grid.faces)
    (perimeters : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize
        i j)
      (side : GridSide) :
    FiniteSum.Fin.sumFin (fun p => FiniteSum.Fin.sumFin (fun sheet => ((bank.rows.get p).sideDecision side).value
      perimeters sheet)) =
      Meshes.PuncturedGrid.SelectedBoundaryDecomposition.SelectedSides.outgoingSum (fineMask excision)
        (fun side p => FiniteSum.Fin.sumFin (fun sheet => Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder
          perimeters p sheet side)) side := by
  rw [FiniteSum.Fin.sumFin_congr (fun p => FiniteSum.Fin.sumFin_congr (fun sheet =>
    ((bank.rows.get p).sideDecision side).value_eq_sum
      (Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
        (neighbors.entries.get p) side) perimeters sheet))]
  rw [FiniteSum.Fin.sumFin_congr (fun p => FiniteSum.Fin.sumFin_swap (fun sheet next =>
    if side.Matches (grid.faces.regulars[p.val]'p.isLt).cell.box (grid.faces.regulars[next.val]'next.isLt).cell.box ∧
      fineMask excision p = true ∧ fineMask excision next = false then
        Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters p sheet side else 0))]
  apply FiniteSum.Fin.sumFin_congr
  intro p
  apply FiniteSum.Fin.sumFin_congr
  intro next
  by_cases active : side.Matches (grid.faces.regulars[p.val]'p.isLt).cell.box
    (grid.faces.regulars[next.val]'next.isLt).cell.box ∧
      fineMask excision p = true ∧ fineMask excision next = false
  · simp only [-eq_self, -iff_self, if_pos active]
    rfl
  · simp only [-eq_self, -iff_self, if_neg active, FiniteSum.Fin.sumFin_zero]
    rfl

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- The exact interface-bank readback equals the original selected-boundary interface evaluation.

The finite sums preserve the original face mask, matched neighbor relation and the signed two-sheet side occurrences of
each retained row. -/
theorem sum_eq_interfaces {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (bank : InterfaceBank excision traces i j) (neighbors : PuncturedFaces.NeighborBank grid.faces)
    (perimeters : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize
        i j) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (bank.values perimeters) =
      Meshes.PuncturedGrid.SelectedBoundaryDecomposition.SelectedSides.interfaceEvaluation (fineMask excision)
      (fun side p => FiniteSum.Fin.sumFin (fun sheet => Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder
        perimeters p sheet side)) := by
  rw [NewtonSelectedInterfaceBank.InterfaceBank.values,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum_flatMap]
  unfold List.finRange
  rw [Data.List.OfFn.Basic.map_ofFn, ← Data.Gaussian.Norm.Sum.Indexed.sumFin_eq_gaussianSum]
  dsimp only [Function.comp_def]
  rw [FiniteSum.Fin.sumFin_congr (fun p => InterfaceRow.sum_values (bank.rows.get p) perimeters)]
  simp only [-eq_self, -iff_self, FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_sub,
    Meshes.PuncturedGrid.SelectedBoundaryDecomposition.SelectedSides.interfaceEvaluation]
  have bottom := sum_side bank neighbors perimeters .bottom
  have right := sum_side bank neighbors perimeters .right
  have top := sum_side bank neighbors perimeters .top
  have left := sum_side bank neighbors perimeters .left
  dsimp only [-eq_self, -iff_self, InterfaceRow.sideDecision] at bottom right top left
  rw [bottom, right, top, left]

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- The original selected-side remainder splits into its physical-boundary contribution and retained interface-bank sum.

Both terms use the same original neighbors, face mask and perimeter readings, preserving the exact physical/interface
decomposition. -/
theorem selected_boundary_eq {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
  domains stage}
    (bank : InterfaceBank excision traces i j) (neighbors : PuncturedFaces.NeighborBank grid.faces)
    (perimeters : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize
        i j) :
    Meshes.PuncturedGrid.SelectedSideRemainders.LiftedPuncturedGrid.selectedSideRemainder perimeters neighbors (fineMask
      excision) =
      Meshes.PuncturedGrid.SelectedBoundaryDecomposition.SelectedSides.physicalEvaluation neighbors (fineMask excision)
        (fun side p => FiniteSum.Fin.sumFin (fun sheet => Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder
          perimeters p sheet side)) + Data.Gaussian.Norm.Sum.Basic.gaussianSum (bank.values perimeters) := by
  rw [InterfaceBank.sum_eq_interfaces bank neighbors perimeters]
  exact Meshes.PuncturedGrid.SelectedBoundaryDecomposition.SelectedSides.boundaryEvaluation_partition neighbors
    (fineMask excision) _

end InterfaceBank
end Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceReadback
