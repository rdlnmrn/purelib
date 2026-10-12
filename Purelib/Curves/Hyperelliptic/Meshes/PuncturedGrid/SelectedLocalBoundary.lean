module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCornerBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSums
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCutBoundary
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCornerBounds

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCutBoundary

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSums

open Purelib.Riemann.Meshes

public section

/-! Local triangle decay includes the actual fine-side remainder. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedLocalBoundary

open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest (Readings)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition (selectedFullTriangleArea
  selectedBoundaryTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.LiftedPuncturedGrid (selectedSideRemainder
  selectedSideRemainder_eq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas (physicalTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCutBoundary.Readings (selectedCorrection
  selected_corrected_bound)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {i j : Fin genus} {target : Rational} {floor stage : Nat}
  {request : CutPairingRequest lifted domains i j
    target floor} {cache : Numerics
    domains stage}

/-- The actual selected source triangles plus their retained fine-side remainder fit the paid local boundary budget. -/
theorem selected_local_boundary_bound (readings : CutPairingRequest.Readings request cache)
    (keep : Fin base.faces.regulars.length → Bool) (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (SelectedTrianglePartition.selectedFullTriangleArea readings.left
      readings.right keep +
      LiftedPuncturedGrid.selectedSideRemainder readings.normalized readings.neighbors keep) ≤ target / 4 := by
  rw [LiftedPuncturedGrid.selectedSideRemainder_eq readings.normalized readings.neighbors readings.left readings.right,
    CrossingBank.selected_triangle_partition request.crossings readings.neighbors readings.left readings.right]
  have equal : CrossingBank.selectedTriangleArea request.crossings readings.left readings.right keep +
      SelectedTrianglePartition.selectedBoundaryTriangleArea readings.neighbors readings.left readings.right keep +
      (FacePerimeters.selectedBoundary readings.normalized readings.neighbors keep -
        SelectedTrianglePartition.selectedBoundaryTriangleArea readings.neighbors readings.left readings.right keep) =
          Readings.selectedCorrection readings keep := by
    unfold Readings.selectedCorrection
    ring1
  rw [equal]
  exact Readings.selected_corrected_bound readings keep later

/-- With every regular face selected, no regular-to-discarded interface remains. The retained remainder is exactly the
existing physical correction. -/
theorem all_side_remainder_eq_physical (readings : CutPairingRequest.Readings request cache) :
    LiftedPuncturedGrid.selectedSideRemainder readings.normalized readings.neighbors (fun _ => true) = readings.physical
      := by
  rw [LiftedPuncturedGrid.selectedSideRemainder_eq readings.normalized readings.neighbors readings.left readings.right]
  have transition (side : GridLiftedDualSteps.GridSide) : FacePerimeters.selectedTransition readings.normalized (fun _
    => true) side = 0 := by
    unfold FacePerimeters.selectedTransition
    have zero (first last : Fin base.faces.regulars.length) :
        (if side.Matches (base.faces.regulars[first.val]'first.isLt).cell.box
          (base.faces.regulars[last.val]'last.isLt).cell.box then
          SelectedSides.transition true true (FacePerimeters.sideSum readings.normalized side first)
            (FacePerimeters.sideSum readings.normalized side.opposite last) else 0) = 0 := by
      split
      · change (0 : Data.Gaussian.Basic.Canonical) - 0 = 0
        rfl
      · rfl
    rw [FiniteSum.Fin.sumFin_congr (fun first => (FiniteSum.Fin.sumFin_congr (zero first)).trans
      FiniteSum.Fin.sumFin_zero),
      FiniteSum.Fin.sumFin_zero]
  have boundary : FacePerimeters.selectedBoundary readings.normalized readings.neighbors (fun _ => true) =
      FacePerimeters.physicalPerimeter readings.normalized readings.neighbors := by
    unfold FacePerimeters.selectedBoundary
    rw [transition, transition, add_zero]
    change FacePerimeters.physicalPerimeter readings.normalized readings.neighbors - 0 = _
    exact Data.Gaussian.Basic.sub_zero _
  have triangles : SelectedTrianglePartition.selectedBoundaryTriangleArea readings.neighbors readings.left
    readings.right (fun _ => true) =
      CrossingTriangleAreas.physicalTriangleArea readings.neighbors readings.left readings.right := by
    have selected (area : Data.Gaussian.Basic.Canonical) :
        SelectedSides.value true area = area := by
      unfold SelectedSides.value
      exact if_pos rfl
    have omitted (area : Data.Gaussian.Basic.Canonical) :
        SelectedSides.value (true && !true) area = 0 := by
      change (if false = true then area else 0) = 0
      exact if_neg Bool.noConfusion
    unfold SelectedTrianglePartition.selectedBoundaryTriangleArea
    have interface (side : GridLiftedDualSteps.GridSide)
        (first : Fin base.faces.regulars.length) (area : Data.Gaussian.Basic.Canonical) :
        FiniteSum.Fin.sumFin (fun last : Fin base.faces.regulars.length =>
          if side.Matches (base.faces.regulars[first.val]'first.isLt).cell.box
              (base.faces.regulars[last.val]'last.isLt).cell.box then
            SelectedSides.value (true && !true) area else 0) = 0 := by
      refine (FiniteSum.Fin.sumFin_congr (fun last => ?_)).trans FiniteSum.Fin.sumFin_zero
      split
      · exact omitted area
      · rfl
    rw [FiniteSum.Fin.sumFin_congr (fun first =>
      (FiniteSum.Fin.sumFin_congr (fun sheet => interface .right first _)).trans
        FiniteSum.Fin.sumFin_zero),
      FiniteSum.Fin.sumFin_zero,
      FiniteSum.Fin.sumFin_congr (fun first =>
        (FiniteSum.Fin.sumFin_congr (fun sheet => interface .top first _)).trans
          FiniteSum.Fin.sumFin_zero),
      FiniteSum.Fin.sumFin_zero, add_zero, add_zero]
    unfold CrossingTriangleAreas.physicalTriangleArea
    apply FiniteSum.Fin.sumFin_congr
    intro first
    apply FiniteSum.Fin.sumFin_congr
    intro sheet
    rw [selected, selected]

  rw [boundary, triangles]
  rfl

/-- Taking every source retains the physical sides of the punctured mesh. No decay of the triangle sum alone is
asserted. -/
theorem local_boundary_bound (readings : CutPairingRequest.Readings request cache) (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (TriangleReadings.bilinearArea readings.left
      readings.right) +
      LiftedPuncturedGrid.selectedSideRemainder readings.normalized readings.neighbors (fun _ => true)) ≤ target / 4 :=
        by
  have allRead : SelectedTrianglePartition.selectedFullTriangleArea readings.left readings.right (fun _ => true) =
      FiniteSum.Fin.sumFin (TriangleReadings.bilinearArea readings.left readings.right) := by
    unfold SelectedTrianglePartition.selectedFullTriangleArea
    exact (LiftedMesh.triangle_sum lifted.mesh (TriangleReadings.bilinearArea readings.left readings.right)).symm
  have bound := selected_local_boundary_bound readings
    (fun _ => true) later
  rw [allRead] at bound
  exact bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedLocalBoundary
