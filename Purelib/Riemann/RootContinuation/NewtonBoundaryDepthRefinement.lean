module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReadingTargetRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! Refine the retained Newton surface without replacing its domains,
source bank, root geometry, or annular sewing data. -/
namespace Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece (junctionCount)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest (LocalBoundaryRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest (ExteriorBoundaryRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest (ClippedRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.RegularMeshes.TwoSheetRequest (ExteriorCaps)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Riemann.Branches.NewtonRequestedCutBudget (PaidCutRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (CrossingBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests (TotalRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests (PerimeterTraceBank)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests (FamilyFineAreaRequest)

namespace RegularMeshes
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List (RegularFace bank)}
  {domains : FaceDomainBank frames faces} {coarse :
    (sheet : Fin 2) → RegularMeshes domains sheet}
  {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {target : Fraction.Rational}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Raise the original two-sheet energy request to the retained minimum depth.

The new depth is the maximum of the original request and minimum; exact entry-depth certificates and a stage covering
the original index and all refined entries are retained. -/
@[expose] def refineEnergy (request : Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target)
  (minimum : Nat) :
    Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target :=
  let depth := max minimum request.depth
  have later (sheet : Fin 2) (position : Fin faces.length) :
      ((request.entries.get sheet).entries.get position).depth ≤ depth :=
    (request.depth_eq sheet position).trans_le (Data.Nat.Order.le_max_right _ _)
  let entries := Vector.DependentVector.ofFn fun sheet => (request.entries.get sheet).atDepth depth (later sheet)
  { request with
    entries := entries
    depth := depth
    depth_eq := fun sheet position => by
      dsimp only [entries, -eq_self, -iff_self]
      rw [Vector.DependentVector.ofFn_get]
      exact (request.entries.get sheet).atDepth_entry_depth depth (later sheet) position
    index := max request.index (entries.maximum (fun _ entry => entry.index))
    index_ge := fun sheet => (entries.get_le_maximum (fun _ entry => entry.index) sheet).trans
      (Data.Nat.Order.le_max_right _ _) }

open Purelib.Curves.Hyperelliptic
/-- The original requested perimeter mesh preserves its coarse owner's exact side-junction count. -/
theorem request_junction_count (request : Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed
  target)
    (sheet : Fin 2) (position : Fin faces.length) (side : GridSide) :
    Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount ((request.entries.get
      sheet).meshes.entries.get position) side =
      Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount ((coarse sheet).entries.get
        position) side := by
  rw [(request.entries.get sheet).mesh_eq position, ((request.entries.get sheet).entries.get position).mesh_eq]
  cases side <;> rfl

/-- Raise the original local boundary energy depth and rebuild its exact ownership request at the retained target. -/
@[expose] def refineLocal (request : Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest coarse fixed
  target) (minimum : Nat) :
    Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest coarse fixed target :=
  let energy := refineEnergy request.energy minimum
  { request with
    energy := energy
    ownership := Meshes.PuncturedGrid.RegularClippedRequest.ClippedRequest.build energy request.ownershipTarget
      request.ownership.positive }

/-- Raise the original exterior request's local depth and rebuild its matching reading caps and prepared cache.

The original pair target and positivity are retained, and the new preparation consumes those exact rebuilt energy and
cap owners. -/
@[expose] def refineExterior (request : Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest coarse fixed
  target) (minimum : Nat) :
    Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest coarse fixed target :=
  let initial := refineLocal request.initial minimum
  let caps := Meshes.PuncturedGrid.Exterior.ReadingCaps.RegularMeshes.TwoSheetRequest.ExteriorCaps.build initial.energy
    request.pairTarget request.pair_positive
  let prepared := initial.limitReadings caps.values caps.positive
  { request with
    initial := initial
    caps := caps
    prepared := prepared
    prepared_eq := rfl
    pair_bound := fun stage later sheet position first second => caps.pair_bound stage later sheet position first second
      }

end RegularMeshes

namespace BoundaryPreparation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {first second : Fin genus}
  {target radius : Fraction.Rational} {floor : Nat}

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Rat
/-- Raise the original paid cut's exterior depth and rebuild its matching crossing bank and request.

The exact original target, floor, corner and sewing owners remain retained; the combined stage covers both original and
rebuilt obligations. -/
@[expose] def refineCut {base : FramedPuncturedGrid curve branches higher}
    {lifted : LiftedPuncturedGrid base} {domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
      base.faces.regulars}
    {cutTarget : Fraction.Rational} (cut : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted domains
      first second cutTarget floor) (minimum : Nat) :
    Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted domains first second cutTarget floor :=
  let exterior := RegularMeshes.refineExterior cut.exterior minimum
  let crossings := Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.build exterior.prepared.energy
      lifted.mesh
  have quarter {value : Fraction.Rational} (positive : 0 < value) : 0 < value / 4 :=
    Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  let total := Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest.build crossings first second 0 0
    (((((cutTarget / 4) / 4) / 4) / 4) / 4)
    (quarter (quarter (quarter (quarter (quarter cut.positive))))) floor
  let index := max cut.index (max exterior.prepared.ownership.index total.allocated.index)
  { cut with
    exterior := exterior
    crossings := crossings
    total := total
    index := index
    floor_le := cut.floor_le.trans (Data.Nat.Order.le_max_left _ _)
    ownership_le := (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)
    crossing_le := (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)
    corner_le := cut.corner_le.trans (Data.Nat.Order.le_max_left _ _)
    sewing_le := cut.sewing_le.trans (Data.Nat.Order.le_max_left _ _) }

/-- Replace only the original paid request's cut by its exact minimum-depth refinement. -/
@[expose] def refinePaid {holeTarget : Fraction.Rational} {family :
  Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest preparation holeTarget radius}
    {lifted : LiftedPuncturedGrid family.single.grid.punctured}
    {domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames family.single.grid.faces.regulars}
      {paidTarget : Fraction.Rational}
    (paid : PaidCutRequest lifted domains first second paidTarget floor) (minimum : Nat) :
    PaidCutRequest lifted domains first second paidTarget floor :=
  { paid with cut := refineCut paid.cut minimum }

end

open Purelib.Curves.Hyperelliptic in
/-- Raise the original boundary preparation's paid-cut depth and rebuild matching perimeter traces and side requests.

The original fine grid, differential comparison and target remain the owners of the rebuilt retained boundary data. -/
@[expose] def atDepth (prepared : BoundaryPreparation preparation first second target radius floor) (minimum : Nat) :
    BoundaryPreparation preparation first second target radius floor :=
  let paid := refinePaid prepared.paid
    minimum
  let traces := Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank.build paid.cut.exterior.prepared.energy
  { prepared with
    paid := paid
    traces := traces
    sides := Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest.SideRequests.build prepared.comparison traces
      }

/-- The retained boundary refinement meets the requested minimum energy depth. -/
theorem atDepth_ge (prepared : BoundaryPreparation preparation first second target radius floor) (minimum : Nat) :
    minimum ≤ (atDepth prepared minimum).paid.cut.exterior.prepared.energy.depth :=
  Data.Nat.Order.le_max_left _ _

open Purelib.Curves.Hyperelliptic in
/-- Raising the original boundary depth preserves every retained sheet, face and side junction count. -/
theorem atDepth_junction_count (prepared : BoundaryPreparation preparation first second target radius floor)
    (minimum : Nat) (sheet : Fin 2) (position : Fin prepared.fine.family.single.grid.faces.regulars.length)
    (side : GridSide) :
    Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount
      (((atDepth prepared minimum).paid.cut.exterior.prepared.energy.entries.get sheet).meshes.entries.get position)
        side =
    Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount
      ((prepared.paid.cut.exterior.prepared.energy.entries.get sheet).meshes.entries.get position) side :=
  (RegularMeshes.request_junction_count (atDepth prepared minimum).paid.cut.exterior.prepared.energy sheet position
    side).trans
    (RegularMeshes.request_junction_count prepared.paid.cut.exterior.prepared.energy sheet position side).symm

end BoundaryPreparation
end Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement
