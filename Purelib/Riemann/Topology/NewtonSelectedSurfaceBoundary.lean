module
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Periods.BilinearBoundaryReadback
import Purelib.Riemann.Topology.NewtonSewnExcision

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSums
public import Purelib.Riemann.Branches.NewtonRequestedCutComparison
public import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCutBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnBilinearRequest
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-! The actual retained annular surface consumes selected crossing accounting.
Boundary-side and boundary-triangle terms remain explicit for tour transport. -/
namespace Purelib.Riemann.Branches.NewtonRequestedCutComparison

open Purelib
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles (PairedComparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition (selectedFullTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.LiftedPuncturedGrid (selectedSideRemainder
  selectedSideRemainder_eq)
open Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters.AllHoleExcision (fineMask)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {request : FamilyAreaRequest
    preparation target radius}
  {lifted : LiftedPuncturedGrid request.single.grid.punctured}
  {excision : AllHoleExcision request.single.grid lifted}
  {prepared :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
    excision} {first second : Fin genus}
  {domains : FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}
  {comparison :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
    prepared first second domains}
  {cutTarget : Rational} {floor stage : Nat}
  {cut : CutPairingRequest lifted domains first
    second cutTarget floor}
  {cache : Numerics domains stage}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Topology.Polygon.Stokes (OrientedTriangle edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)
attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

namespace CutAnnularReadings
variable {readings : CutPairingRequest.Readings
  cut cache}

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Topology in
/-- The original selected triangle-source mask sum equals the exact retained fine-face area selection. -/
private theorem selected_source_sum :
    FiniteSum.Fin.sumFin (fun source => if excision.entries.any (fun entry =>
      NewtonSewnExcision.AllHoleExcision.sourceMask entry source) then
      Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea readings.left readings.right source else 0)
        =
      Meshes.PuncturedGrid.SelectedTrianglePartition.selectedFullTriangleArea readings.left readings.right (fineMask
        excision) := by
  rw [Meshes.PuncturedGrid.TriangleSums.LiftedMesh.triangle_sum lifted.mesh]
  apply FiniteSum.Fin.sumFin_congr
  intro position
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  have mask (upper : Bool) :
      excision.entries.any (fun entry => NewtonSewnExcision.AllHoleExcision.sourceMask entry
        (lifted.mesh.triangleIndex position sheet upper)) = (fineMask excision) position := by
    exact congrArg (fineMask excision) (NewtonSewnExcision.AllHoleExcision.sourcePosition_triangleIndex lifted position
      sheet upper)
  rw [mask false, mask true]
  rfl

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Periods in
open Purelib.Riemann.Topology in
/-- The cached selected annular area approximates the original selected source area within a quarter cut target.

The full sewn area and its retained complement are compared separately before their exact partition identity isolates
the original selected sources. -/
theorem selected_source_accurate (cached : CutAnnularReadings comparison readings) (later : cut.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (cached.annuli.selectedArea -
      Meshes.PuncturedGrid.SelectedTrianglePartition.selectedFullTriangleArea readings.left readings.right (fineMask
        excision)) ≤ cutTarget / 4 := by
  have full := cut.sewing.accurate (cut.sewing_le.trans later) readings.left readings.right readings.surface
  have remaining := Meshes.PuncturedGrid.SelectedSewnBilinearRequest.BilinearPreparation.Request.selected_accurate
    cut.sewing (cut.sewing_le.trans later) readings.left readings.right
    readings.surface cached.remaining.retained.remaining
  have sumPartition :
      FiniteSum.Fin.sumFin (Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea readings.left
        readings.right) =
      Meshes.PuncturedGrid.SelectedTrianglePartition.selectedFullTriangleArea readings.left readings.right (fineMask
        excision) +
      FiniteSum.Fin.sumFin (fun source => if !(excision.entries.any (fun entry =>
        NewtonSewnExcision.AllHoleExcision.sourceMask entry source)) then
        Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea readings.left readings.right source else
          0) := by
    rw [← selected_source_sum (readings := readings), ← FiniteSum.Fin.sumFin_add]
    apply FiniteSum.Fin.sumFin_congr
    intro source
    cases excision.entries.any (fun entry => NewtonSewnExcision.AllHoleExcision.sourceMask entry source) <;>
      simp only [Bool.not, if_neg Bool.false_ne_true, if_pos (rfl : true = true), -eq_self, -iff_self] <;> ring1
  have remainingEq : cached.remaining.remainingArea =
      edgeListArea readings.surface.values (cached.remaining.retained.remaining.triangles.flatMap
        OrientedTriangle.boundary) :=
    cached.remaining.remainingArea_eq.trans (BilinearBoundaryReadback.triangles_eq_raw readings.surface _).symm
  rw [← remainingEq] at remaining
  have partition := cached.remaining.partition
  rw [cached.remaining.boundary_eq_bilinear readings.surface] at partition
  have equal : cached.annuli.selectedArea - Meshes.PuncturedGrid.SelectedTrianglePartition.selectedFullTriangleArea
    readings.left readings.right (fineMask excision) =
      (readings.surface.boundaryArea - FiniteSum.Fin.sumFin
        (Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea readings.left readings.right)) -
      (cached.remaining.remainingArea - FiniteSum.Fin.sumFin (fun source =>
        if !(excision.entries.any (fun entry => NewtonSewnExcision.AllHoleExcision.sourceMask entry source)) then
          Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea readings.left readings.right source
            else 0)) := by
    rw [← partition, sumPartition]
    ring1
  rw [equal]
  exact (Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct full.le
      remaining.le) (by decide)).trans_eq
      ((show 2 * ((cutTarget / 4) / 4 + (cutTarget / 4) / 4) = ((cutTarget / 4) / 4) * 4 by ring1).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The cached selected annular area plus the original selected side remainder meets the paid cut target.

The same retained source mask and normalized neighbor readings combine source-area accuracy with the original selected
crossing correction. -/
theorem selected_boundary_bound (cached : CutAnnularReadings comparison readings) (later : cut.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (cached.annuli.selectedArea +
      Meshes.PuncturedGrid.SelectedSideRemainders.LiftedPuncturedGrid.selectedSideRemainder readings.normalized
      readings.neighbors (fineMask excision)) ≤ cutTarget := by
  have source := cached.selected_source_accurate later
  have crossing := Meshes.PuncturedGrid.SelectedCutBoundary.Readings.selected_corrected_bound readings (fineMask
    excision) later
  have equal : cached.annuli.selectedArea +
    Meshes.PuncturedGrid.SelectedSideRemainders.LiftedPuncturedGrid.selectedSideRemainder readings.normalized
    readings.neighbors (fineMask excision) =
      (cached.annuli.selectedArea - Meshes.PuncturedGrid.SelectedTrianglePartition.selectedFullTriangleArea
        readings.left readings.right (fineMask excision)) +
      Meshes.PuncturedGrid.SelectedCutBoundary.Readings.selectedCorrection readings (fineMask excision) := by
    rw [Meshes.PuncturedGrid.SelectedTrianglePartition.CrossingBank.selected_triangle_partition cut.crossings
      readings.neighbors readings.left readings.right (fineMask excision)]
    dsimp only [Meshes.PuncturedGrid.SelectedCutBoundary.Readings.selectedCorrection, -eq_self, -iff_self]
    rw [Meshes.PuncturedGrid.SelectedSideRemainders.LiftedPuncturedGrid.selectedSideRemainder_eq readings.normalized
      readings.neighbors readings.left readings.right (fineMask excision)]
    ring1
  rw [equal]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct source
      crossing) (by decide)).trans_eq
      ((show 2 * (cutTarget / 4 + cutTarget / 4) = (cutTarget / 4) * 4 by ring1).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))

end CutAnnularReadings
end Purelib.Riemann.Branches.NewtonRequestedCutComparison
