module
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
public import Purelib.Riemann.RootContinuation.NewtonOmittedHoleBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSelectionPartition
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOmittedHoleDecisions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Tactic.Ring

public section

/-! Exact signed readback of the acquired omitted-hole list to the complete
hole boundary expression. The original sheet occurrences and directions remain. -/
namespace Purelib.Riemann.RootContinuation.NewtonOmittedHoleReadback

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests (PerimeterTraceBank)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (FacePerimeters)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (sideAreaRemainder)
open Purelib.Riemann.RootContinuation.NewtonOmittedHoleBank (OmittedHoleRow OmittedHoleBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSelectionPartition (omittedHoleEvaluation)
open Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters.AllHoleExcision (fineMask)
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

namespace OmittedHoleRow
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
    (row : OmittedHoleRow excision traces i j position) (perimeters :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize i j) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (row.values perimeters) = FiniteSum.Fin.sumFin (fun sheet =>
      row.bottom.value perimeters sheet + row.right.value perimeters sheet -
        row.top.value perimeters sheet - row.left.value perimeters sheet) := by
  simp only [NewtonOmittedHoleBank.OmittedHoleRow.values, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
    FiniteSum.Fin.sumFin_succ,
    -eq_self, -iff_self]
  change _ = _ + (_ + 0)
  rw [show (1 : Fin 2) = Fin.succ 0 by decide]
  ring1

end OmittedHoleRow

namespace OmittedHoleBank
variable {excision : AllHoleExcision grid lifted} {traces :
  PerimeterTraceBank request}

open Purelib.Algebra in
open Purelib.Data.Gaussian in
/-- Summing both original sheets commutes with the retained physical neighbor's omitted-hole selection. -/
private theorem neighbor_sum {face : RegularFace grid.shrunk.prepared.toBranchCellBank} {side : GridSide}
    (neighbor : PuncturedFaces.SideNeighbor grid.faces face side) (keep : Bool) (values : Fin 2 → Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun sheet => if keep = false then neighbor.holeValue (values sheet) else 0) =
      if keep = false then neighbor.holeValue (FiniteSum.Fin.sumFin values) else 0 := by
  by_cases discarded : keep = false
  · simp only [if_pos discarded, -eq_self, -iff_self]
    cases neighbor with
    | exterior _ => exact FiniteSum.Fin.sumFin_zero
    | neighbor _ _ _ location =>
      cases location with
      | regular _ _ => exact FiniteSum.Fin.sumFin_zero
      | hole _ _ => rfl
  · simp only [if_neg discarded, FiniteSum.Fin.sumFin_zero, -eq_self, -iff_self]
    rfl

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
/-- The retained omitted-hole decisions read back the exact masked physical-neighbor contribution on one side. -/
private theorem sum_side {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (bank : OmittedHoleBank excision traces i j) (neighbors : PuncturedFaces.NeighborBank grid.faces)
    (perimeters : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize
        i j)
      (side : GridSide) :
    FiniteSum.Fin.sumFin (fun p => FiniteSum.Fin.sumFin (fun sheet => ((bank.rows.get p).sideDecision side).value
      perimeters sheet)) =
      FiniteSum.Fin.sumFin (fun p => if fineMask excision p = false then
        (Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
        (neighbors.entries.get p) side).holeValue
        (FiniteSum.Fin.sumFin (fun sheet => Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters p sheet
          side)) else 0) := by
  apply FiniteSum.Fin.sumFin_congr
  intro p
  rw [FiniteSum.Fin.sumFin_congr (fun sheet => ((bank.rows.get p).sideDecision side).value_eq
    (Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at (neighbors.entries.get p)
      side) perimeters sheet)]
  exact neighbor_sum (Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
    (neighbors.entries.get p) side) (fineMask excision p) _

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- The retained omitted-hole bank reads back the original omitted physical-hole evaluation.

The finite sum preserves the original face mask, physical neighbors, both sheets and signed boundary orientation of the
stored eight-entry rows. -/
theorem sum_eq_omitted {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (bank : OmittedHoleBank excision traces i j) (neighbors : PuncturedFaces.NeighborBank grid.faces)
    (perimeters : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize
        i j) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (bank.values perimeters) =
      Meshes.PuncturedGrid.HoleSelectionPartition.omittedHoleEvaluation neighbors (fineMask excision)
      (fun side p => FiniteSum.Fin.sumFin (fun sheet => Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder
        perimeters p sheet side)) := by
  rw [NewtonOmittedHoleBank.OmittedHoleBank.values, Data.Gaussian.Norm.Sum.Basic.gaussianSum_flatMap]
  unfold List.finRange
  rw [Data.List.OfFn.Basic.map_ofFn, ← Data.Gaussian.Norm.Sum.Indexed.sumFin_eq_gaussianSum]
  dsimp only [Function.comp_def]
  rw [FiniteSum.Fin.sumFin_congr (fun p => OmittedHoleRow.sum_values (bank.rows.get p) perimeters)]
  simp only [FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_sub,
    Meshes.PuncturedGrid.HoleSelectionPartition.omittedHoleEvaluation, -eq_self, -iff_self]
  have b := sum_side bank neighbors perimeters .bottom
  have r := sum_side bank neighbors perimeters .right
  have t := sum_side bank neighbors perimeters .top
  have l := sum_side bank neighbors perimeters .left
  dsimp only [OmittedHoleRow.sideDecision,
    Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at, -eq_self, -iff_self]
    at b r t l
  rw [b, r, t, l]
  ring1

end OmittedHoleBank
end Purelib.Riemann.RootContinuation.NewtonOmittedHoleReadback
