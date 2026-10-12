module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCutBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineTransport
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
public import Purelib.Riemann.Topology.NewtonSelectedSurfaceBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Branches.NewtonRequestedCutComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Polynomial.Dense.Basic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-! Requested comparison on the actual Newton-excised cut surface, with
internal allocation of all comparison errors. The retained physical residual
is still part of the result, not an assumption that it vanishes. -/
namespace Purelib.Riemann.RootContinuation.NewtonRequestedBoundary

open Purelib
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests (FamilyFineAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles (PairedComparison)
open Purelib.Riemann.Branches.NewtonRequestedCutBudget (PaidCutRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests (PerimeterTraceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Branches.NewtonRequestedCutComparison (CutAnnularReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering (CenteredPerimeters)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {first second : Fin genus} {target radius :
    Rational} {floor : Nat}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- A requested Newton boundary retaining its original fine grid, domains, excision and paid cut construction.

The selected exterior cut points remain exact, and the perimeter traces and fine-side requests consume the same retained
energy preparation and differential comparison. -/
structure BoundaryPreparation (preparation : NewtonPreparation original)
    (first second : Fin genus) (target radius : Fraction.Rational) (floor : Nat) where
  /-- The retained original fine-area request for one quarter of the boundary target. -/ fine :
    Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest preparation (target / 4) radius
  /-- The exact retained lift of the original requested punctured grid. -/ lifted : LiftedPuncturedGrid
    fine.family.single.grid.punctured
  /-- The original face-domain bank on the retained lift and regular faces. -/ domains :
    Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames fine.family.single.grid.faces.regulars
  /-- The retained original all-hole excision on the exact fine grid and lift. -/ excision :
    Meshes.Newton.AllHoles.Excision.AllHoleExcision fine.family.single.grid lifted
  /-- The retained outer preparations indexed by that exact original excision. -/ outer :
    Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations excision
  /-- The retained original paired-differential comparison on those outer preparations and domains. -/ comparison :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison outer first second
    domains
  /-- The retained original source-cut preparation for the first differential. -/ exterior :
    Meshes.PuncturedGrid.Exterior.SourceCuts.SourcePreparation domains
    (standardDifferential first)
  /-- The paid original quarter-target cut request on the retained lift and domains. -/ paid : PaidCutRequest lifted
    domains first second (target / 4) floor
  /-- The paid cut's point list equals the exact selected original exterior cut-point list. -/ cut_points_eq :
    paid.cut.cuts.points = exterior.selected.cuts.points
  /-- The retained perimeter traces of the exact original paid-cut energy preparation. -/ traces :
    Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank paid.cut.exterior.prepared.energy
  /-- The original fine-side requests on the retained comparison and exact perimeter traces. -/ sides :
    fine.SideRequests comparison traces

constructive_injectivity BoundaryPreparation

namespace BoundaryPreparation

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Construct the original quarter-target fine boundary, paid cut request and matching retained perimeter-side requests.

The exact selected exterior cut owner is passed into the paid request; its energy cache then drives the retained trace
bank and fine-side payment. -/
@[expose] def build (preparation : NewtonPreparation original) (first second : Fin genus)
    (target radius : Fraction.Rational) (positive : 0 < target) (radiusPositive : 0 < radius) (floor : Nat) :
    BoundaryPreparation preparation first second target radius floor :=
  let quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  let fine := Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest.build preparation (target / 4) radius
    quarterPositive radiusPositive
  let request := fine.family
  let lifted := LiftedPuncturedGrid.build request.single.grid.punctured
  let domains := Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank.build lifted.frames
    request.single.grid.faces.regulars
  let excision := Meshes.Newton.AllHoles.Excision.AllHoleExcision.build request.single.grid lifted
  let outer := Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations.build excision
  let comparison := Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.build
    outer first second domains
  let exterior := Meshes.PuncturedGrid.Exterior.SourceCuts.SourcePreparation.build domains
    (standardDifferential first)
  let paid := PaidCutRequest.build lifted domains exterior.selected.cuts first second (target / 4) quarterPositive floor
  let traces := Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank.build paid.cut.exterior.prepared.energy
  let sides := Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest.SideRequests.build comparison traces
  ⟨fine, lifted, domains, excision, outer, comparison, exterior, paid, rfl, traces, sides⟩

/-- The common stage meeting both original paid-cut and fine-side requests. -/
@[expose] def index (prepared : BoundaryPreparation preparation first second target radius floor) : Nat :=
  max prepared.paid.cut.index prepared.sides.index

/-- The retained common boundary stage meets the original requested floor. -/
theorem floor_le (prepared : BoundaryPreparation preparation first second target radius floor) :
    floor ≤ prepared.index := prepared.paid.cut.floor_le.trans (Data.Nat.Order.le_max_left _ _)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- The ordered sum of original fine-side areas minus their retained source-chord sums. -/
@[expose] def fineCorrection (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) :
      Basic.Canonical :=
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.comparison.entries.map (fun entry =>
    Meshes.Newton.Annulus.FineSideAreas.fineSideArea entry.source.outer readings.normalized -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (entry.source.outer.sources.map (Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord
        readings.left readings.right))))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Later retained boundary readings meet the original target for the exact annular perimeter sum. -/
theorem annular_perimeters_bound (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) (later :
      prepared.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (NewtonSelectedPerimeters.AllHoleExcision.annularPerimeters prepared.excision
      readings.normalized) ≤ target := by
  have cutLater := (Data.Nat.Order.le_max_left _ _).trans later
  have estimate := NewtonSelectedPerimeters.AllHoleExcision.annularPerimeters_bound prepared.excision
    prepared.paid.cut.exterior readings.original readings.normalized
    (prepared.paid.cut.ownership_le.trans cutLater)
  have quarterPositive {value : Fraction.Rational} (h : 0 < value) : 0 < value / 4 :=
    Fraction.Order.Field.div_pos_direct h (by decide)
  have positive := prepared.paid.positive
  have small := (Fraction.Order.Field.divide_le_self (denominator := 4)
    (quarterPositive (quarterPositive (quarterPositive positive))).le (by decide)).trans
    ((Fraction.Order.Field.divide_le_self (denominator := 4)
      (quarterPositive (quarterPositive positive)).le (by decide)).trans
      ((Fraction.Order.Field.divide_le_self (denominator := 4)
        (quarterPositive positive).le (by decide)).trans
        (Fraction.Order.Field.divide_le_self (denominator := 4) positive.le (by decide))))
  have requested : target / 4 ≤ target := by
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide : (1 : Fraction.Rational) ≤ 4) prepared.fine.positive.le
    rw [one_mul, mul_comm] at scaled
    exact scaled.trans_eq (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  exact estimate.trans (small.trans (prepared.paid.cutTarget_le.trans requested))

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Gaussian
open Purelib.Riemann.RootContinuation
/-- Later retained boundary readings meet a quarter target for the original selected boundary correction. -/
theorem annular_selected_boundary_bound (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) (later :
      prepared.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Meshes.PuncturedGrid.SelectedCutBoundary.Readings.selectedCorrection readings
      (NewtonSelectedPerimeters.AllHoleExcision.fineMask prepared.excision)) ≤ target / 4 :=
  (Meshes.PuncturedGrid.SelectedCutBoundary.Readings.selected_corrected_bound readings
    (NewtonSelectedPerimeters.AllHoleExcision.fineMask prepared.excision) ((Data.Nat.Order.le_max_left _ _).trans
    later)).trans
    ((Fraction.Order.Field.divide_le_self (prepared.paid.cut.positive).le (by decide)).trans prepared.paid.cutTarget_le)

/-- Original cut readings and cached annular readbacks with all six requested boundary estimates.

The bounds separately retain remaining area, fine correction, fine residual, annular perimeters, selected correction and
selected boundary remainder on the same original preparation. -/
@[expose] def Readings (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage) :=
  (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) ×
    { cached : CutAnnularReadings prepared.comparison readings //
      Data.Gaussian.Norm.Basic.normSq (cached.remaining.remainingArea + cached.correction) < target ∧
        Data.Gaussian.Norm.Basic.normSq (prepared.fineCorrection readings) < target / 4 ∧
        Data.Gaussian.Norm.Basic.normSq
          (Meshes.Newton.AllHoles.FineTransport.FamilyAreaRequest.PairedComparison.SewnSample.fineResidual
          cached.annuli) < target ∧
        Data.Gaussian.Norm.Basic.normSq (NewtonSelectedPerimeters.AllHoleExcision.annularPerimeters prepared.excision
          readings.normalized) ≤ target ∧
        Data.Gaussian.Norm.Basic.normSq (Meshes.PuncturedGrid.SelectedCutBoundary.Readings.selectedCorrection readings
          (NewtonSelectedPerimeters.AllHoleExcision.fineMask prepared.excision)) ≤ target / 4 ∧
        Data.Gaussian.Norm.Basic.normSq (cached.annuli.selectedArea +
          Meshes.PuncturedGrid.SelectedSideRemainders.LiftedPuncturedGrid.selectedSideRemainder readings.normalized
          readings.neighbors (NewtonSelectedPerimeters.AllHoleExcision.fineMask prepared.excision)) ≤ target }

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Cache annular readbacks and prove the requested boundary bounds from the supplied original cut readings.

The retained perimeter samples and lengths pay the original fine-side and cut budgets at the same sufficiently late
stage; the input readings are returned unchanged. -/
@[expose] def readWith (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage)
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) (later :
      prepared.index ≤ stage) :
    Readings prepared cache := by
  let cached := CutAnnularReadings.build prepared.comparison readings
  have estimate := prepared.paid.remaining_bound cached ((Data.Nat.Order.le_max_left _ _).trans later)
    (prepared.sides.comparison_le.trans ((Data.Nat.Order.le_max_right _ _).trans later))
  let centered := prepared.traces.samples cache first second
  let lengths := Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths.build centered
  have fine := prepared.sides.correction_accurate centered lengths readings.normalized readings.left readings.right
    ((Data.Nat.Order.le_max_right _ _).trans later)
  have transported := Meshes.Newton.AllHoles.FineTransport.FamilyFineAreaRequest.SideRequests.sewn_fine_accurate
    centered lengths prepared.sides cached.annuli
    ((Data.Nat.Order.le_max_right _ _).trans later) ((Data.Nat.Order.le_max_left _ _).trans later)
  have transportPaid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct prepared.paid.outer_paid (le_refl (target / 4)))
    (by decide : (0 : Fraction.Rational) ≤ 2)
  have totalEq : 2 * (target / 4 + target / 4) = target :=
    (show 2 * (target / 4 + target / 4) = target / 4 * 4 by ring1).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  have selected := (cached.selected_boundary_bound ((Data.Nat.Order.le_max_left _ _).trans later)).trans
    prepared.paid.cutTarget_le
  have selectedPaid : target / 4 ≤ target := by
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide : (1 : Fraction.Rational) ≤ 4) prepared.fine.positive.le
    rw [one_mul, mul_comm] at scaled
    exact scaled.trans_eq (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  exact ⟨readings, cached, estimate.trans_eq totalEq, fine,
    (transported.trans_le transportPaid).trans_eq totalEq, prepared.annular_perimeters_bound readings later,
    prepared.annular_selected_boundary_bound readings later, selected.trans selectedPaid⟩

section
open Purelib.Curves.Hyperelliptic
/-- The retained boundary readback returns the exact original supplied cut readings. -/
theorem readWith_cut (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage)
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) (later :
      prepared.index ≤ stage) :
    (prepared.readWith cache readings later).1 = readings := rfl

/-- Build the original cut readings at a sufficient stage and retain their full paid boundary readback. -/
@[expose] def readAt (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage)
      (later : prepared.index ≤ stage) :
    Readings prepared cache :=
  prepared.readWith cache (Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings.build prepared.paid.cut
    cache) later

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Acquire the exact original differential-bank cache at the retained common stage and its paid boundary readings. -/
@[expose] def acquire (prepared : BoundaryPreparation preparation first second target radius floor) :
    (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains prepared.index) × Readings
      prepared cache :=
  let cache := Vector.DependentVector.ofFn fun row =>
    Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.build (standardDifferential row) prepared.index
      prepared.domains
  ⟨cache, prepared.readAt cache le_rfl⟩

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Sample primitives for the exact retained original paired comparison at the requested positive error. -/
@[expose] def samplePrimitives (prepared : BoundaryPreparation preparation first second target radius floor)
    (error : Fraction.Rational) (positive : 0 < error) :=
  Meshes.Newton.AllHoles.PrimitiveSamples.PairedComparison.samplePrimitives prepared.comparison error positive

end BoundaryPreparation
end Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
