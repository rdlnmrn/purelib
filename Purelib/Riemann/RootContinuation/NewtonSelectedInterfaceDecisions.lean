module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
public import Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitLocations
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid

public section

/-! Exhaustive certified decisions for the actual selected regular interfaces.
Inactive sides retain a proof that no selected-to-discarded neighbor exists. -/
namespace Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceDecisions
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
open Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters.AllHoleExcision (fineMask)
open Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceRequests (InterfaceRequest)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests (PerimeterTraceBank)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (FacePerimeters)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (sideAreaRemainder)
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

open Purelib.Curves.Hyperelliptic in
/-- No original matching regular neighbor forms a selected-to-discarded interface on this side. -/
@[expose] def NoInterface (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (position : Fin
  grid.faces.regulars.length)
    (side : GridSide) : Prop :=
  ∀ next : Fin grid.faces.regulars.length,
    side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
      (grid.faces.regulars[next.val]'next.isLt).cell.box →
    fineMask excision position = true → fineMask excision next = false → False

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- A certified absent interface or its exact selected-to-discarded neighbor and allocated request.

The retained original face, side, mask and neighbor index distinguish the negative certificate from the concrete request
and its selection evidence. -/
inductive InterfaceDecision (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request)
    (i j : Fin genus) (position : Fin grid.faces.regulars.length) (side : GridSide) where
  /-- Retain a certificate excluding every original selected-to-discarded neighbor on this side. -/ | absent
    (certificate : NoInterface excision position side)
  /-- Retain the exact neighbor index, matched side, original selection evidence and allocated interface request. -/ |
    present (next : Fin grid.faces.regulars.length)
      (matching : side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
        (grid.faces.regulars[next.val]'next.isLt).cell.box)
      (selected : fineMask excision position = true) (discarded : fineMask excision next = false)
      (allocated : InterfaceRequest excision traces i j position side)

constructive_injectivity InterfaceDecision

namespace InterfaceDecision
variable {excision : AllHoleExcision grid lifted} {traces :
  PerimeterTraceBank request}
  {position : Fin grid.faces.regulars.length} {side : GridSide}

open Purelib.Curves.Hyperelliptic in
/-- Classify the original side neighbor and retain the exact interface request when the selection changes.

Exterior and physical-hole neighbors produce absence certificates; a regular neighbor is retained only when the original
current face is selected and that exact neighbor is discarded. -/
@[expose] def build (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request)
    (i j : Fin genus) (position : Fin grid.faces.regulars.length) (side : GridSide)
    (neighbor : PuncturedFaces.SideNeighbor grid.faces (grid.faces.regulars[position.val]'position.isLt) side) :
    InterfaceDecision excision traces i j position side := by
  by_cases selected : fineMask excision position = true
  · have locate := neighbor.regular_of_matches
    have matched := neighbor.matches_of_regular
    cases neighbor with
    | exterior equal =>
      exact .absent (fun next matching _ _ => locate next matching)
    | neighbor cell member matching location =>
      cases location with
      | hole found equal => exact .absent (fun next matching _ _ => locate next matching)
      | regular found equal =>
        have physical := matched found rfl
        by_cases kept : fineMask excision found = true
        · refine .absent ?_
          intro next matching _ discarded
          have same : found = next := locate next matching
          subst next
          exact Bool.noConfusion (discarded.symm.trans kept)
        · have discarded := Bool.eq_false_iff.mpr kept
          exact .present found physical selected discarded
            (InterfaceRequest.build excision traces i j position found side physical selected discarded)
  · exact .absent (fun _ _ kept _ => selected kept)

/-- Read the retained interface request stage, using zero for a certified absent interface. -/
@[expose] def index : InterfaceDecision excision traces i j position side → Nat
  | .absent _ => 0
  | .present _ _ _ _ allocated => allocated.index

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- Read the original selected-side remainder, using zero for certified absence. -/
@[expose] def value {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (perimeters : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize
        i j)
      (sheet : Fin 2) :
    InterfaceDecision excision traces i j position side → Basic.Canonical
  | .absent _ => 0
  | .present _ _ _ _ _ => Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters position sheet side

/-- Any original regular neighbor matching the retained side equals the exact classified neighbor. -/
private theorem matching_unique
    (neighbor : PuncturedFaces.SideNeighbor grid.faces (grid.faces.regulars[position.val]'position.isLt) side)
    {first next : Fin grid.faces.regulars.length}
    (left : side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
      (grid.faces.regulars[first.val]'first.isLt).cell.box)
    (right : side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
      (grid.faces.regulars[next.val]'next.isLt).cell.box) : first = next := by
  have a := neighbor.regular_of_matches first left
  have b := neighbor.regular_of_matches next right
  cases neighbor with
  | exterior equal => exact a.elim
  | neighbor cell member matching location =>
    cases location with
    | hole found equal => exact a.elim
    | regular found equal => exact a.symm.trans b

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
/-- The retained decision equals the finite sum over matching selected-to-discarded neighbors.

The original neighbor classification supplies uniqueness; an absence certificate makes every summand zero, while a
present decision retains its exact neighbor and perimeter reading. -/
theorem value_eq_sum {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (decision : InterfaceDecision excision traces i j position side)
    (neighbor : PuncturedFaces.SideNeighbor grid.faces (grid.faces.regulars[position.val]'position.isLt) side)
    (perimeters : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize
        i j)
      (sheet : Fin 2) :
    decision.value perimeters sheet = FiniteSum.Fin.sumFin (fun next =>
      if side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
        (grid.faces.regulars[next.val]'next.isLt).cell.box ∧
        fineMask excision position = true ∧ fineMask excision next = false then
          Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters position sheet side else 0) := by
  cases decision with
  | absent certificate =>
    symm
    have equal (next : Fin grid.faces.regulars.length) :
        (if side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
          (grid.faces.regulars[next.val]'next.isLt).cell.box ∧
          fineMask excision position = true ∧ fineMask excision next = false then
          Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters position sheet side else 0) = 0 :=
      if_neg (fun h => certificate next h.1 h.2.1 h.2.2)
    rw [FiniteSum.Fin.sumFin_congr equal]
    exact FiniteSum.Fin.sumFin_zero
  | present found physical selected discarded allocated =>
    have equal (next : Fin grid.faces.regulars.length) :
        (if side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
          (grid.faces.regulars[next.val]'next.isLt).cell.box ∧
          fineMask excision position = true ∧ fineMask excision next = false then
          Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters position sheet side else 0) =
        (if next = found then Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters position sheet side
          else 0) := by
      by_cases same : next = found
      · subst next
        rw [if_pos ⟨physical, selected, discarded⟩, if_pos rfl]
      · rw [if_neg same, if_neg (fun h => same (matching_unique neighbor h.1 physical))]
    rw [FiniteSum.Fin.sumFin_congr equal, FiniteSum.Fin.sumFin_ite_eq]
    rfl

end InterfaceDecision
end Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceDecisions
