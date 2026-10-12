module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
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
public import Purelib.Riemann.RootContinuation.NewtonOmittedHoleGeometry
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleNeighborValues
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitLocations
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Polynomial.Dense.Basic

public section

/-! Exhaustive certified omitted-hole decisions using retained neighbors. -/
namespace Purelib.Riemann.RootContinuation.NewtonOmittedHoleDecisions
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
/-- No original hole matches this side of a discarded regular face. -/
@[expose] def NoOmittedHole (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (position : Fin
  grid.faces.regulars.length)
    (side : GridSide) : Prop :=
  ∀ hole : Fin grid.faces.holes.length,
    side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
      (grid.faces.holes[hole.val]'hole.isLt).cell.box → fineMask excision position = false → False

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- A certified original omitted-hole absence or a matched retained hole with its allocated interface request.

The present case retains the exact classified hole index, original side match and discarded selection equation; the
absent case rules out that same physical configuration. -/
inductive OmittedHoleDecision (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request)
    (i j : Fin genus) (position : Fin grid.faces.regulars.length) (side : GridSide) where
  /-- Retain the certificate excluding an original omitted-hole match on this face side. -/ | absent (certificate :
    NoOmittedHole excision position side)
  /-- Retain the exact original hole, physical side match, discarded selection and allocated interface request. -/ |
    present (hole : Fin grid.faces.holes.length)
      (matching : side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
        (grid.faces.holes[hole.val]'hole.isLt).cell.box)
      (discarded : fineMask excision position = false)
      (allocated : InterfaceRequest excision traces i j position side)

constructive_injectivity OmittedHoleDecision

namespace OmittedHoleDecision
variable {excision : AllHoleExcision grid lifted} {traces :
  PerimeterTraceBank request}
  {position : Fin grid.faces.regulars.length} {side : GridSide}

open Purelib.Curves.Hyperelliptic in
/-- Decide the original omitted-hole case from the retained neighbor and exact selection test.

A classified hole supplies its original excision entry and boundary certificate; exterior, regular-neighbor and
selected-face cases retain explicit absence proofs. -/
@[expose] def build (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request)
    (i j : Fin genus) (position : Fin grid.faces.regulars.length) (side : GridSide)
    (neighbor : PuncturedFaces.SideNeighbor grid.faces (grid.faces.regulars[position.val]'position.isLt) side) :
    OmittedHoleDecision excision traces i j position side := by
  by_cases discarded : fineMask excision position = false
  · have supported := neighbor.hasHole_of_matches
    cases neighbor with
    | exterior equal => exact .absent (fun hole matching _ => supported hole matching)
    | neighbor cell member matching location =>
      cases location with
      | regular found equal => exact .absent (fun hole matching _ => supported hole matching)
      | hole found equal =>
        have physical : side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
            (grid.faces.holes[found.val]'found.isLt).cell.box := by
          rw [equal]
          exact matching
        let entry := excision.entryForHole found
        exact .present found physical discarded
          (InterfaceRequest.ofBoundary excision traces i j position side entry.val entry.property.1
            (excision.omittedHole_boundary position found side physical discarded))
  · exact .absent (fun _ _ gone => discarded gone)

/-- The retained interface stage for a present original hole, or zero for certified absence. -/
@[expose] def index : OmittedHoleDecision excision traces i j position side → Nat
  | .absent _ => 0
  | .present _ _ _ allocated => allocated.index

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- The original side-area remainder for a present omitted hole, or zero for certified absence. -/
@[expose] def value {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (perimeters : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize
        i j)
      (sheet : Fin 2) :
    OmittedHoleDecision excision traces i j position side → Basic.Canonical
  | .absent _ => 0
  | .present _ _ _ _ => Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters position sheet side

open Purelib.Curves.Hyperelliptic in
/-- The retained decision reads exactly the omitted-hole contribution of any certified original neighbor. -/
theorem value_eq {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
    (decision : OmittedHoleDecision excision traces i j position side)
    (neighbor : PuncturedFaces.SideNeighbor grid.faces (grid.faces.regulars[position.val]'position.isLt) side)
    (perimeters : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize
        i j)
      (sheet : Fin 2) :
    decision.value perimeters sheet =
      if fineMask excision position = false then neighbor.holeValue
        (Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters position sheet side) else 0 := by
  cases decision with
  | present hole matching discarded allocated =>
    rw [if_pos discarded, neighbor.holeValue_of_matches hole matching]
    rfl
  | absent certificate =>
    by_cases discarded : fineMask excision position = false
    · rw [if_pos discarded]
      cases neighbor with
      | exterior _ => rfl
      | neighbor cell member matching location =>
        cases location with
        | regular _ _ => rfl
        | hole found equal =>
          have physical : side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
              (grid.faces.holes[found.val]'found.isLt).cell.box := by
            rw [equal]
            exact matching
          exact False.elim (certificate found physical discarded)
    · rw [if_neg discarded]
      rfl

end OmittedHoleDecision
end Purelib.Riemann.RootContinuation.NewtonOmittedHoleDecisions
