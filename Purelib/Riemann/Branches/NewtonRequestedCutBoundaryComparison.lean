module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CenteredHoleCutPairing
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Data.Vector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineTransport
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.Riemann.Branches.NewtonRequestedCutComparison
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Riemann.RootContinuation.NewtonRequestedFullHoleAggregate
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCutBoundary
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Riemann.RootContinuation.NewtonRequestedInterfaceAggregate
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Riemann.RootContinuation.NewtonOmittedHoleBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest
import Purelib.Polynomial.Dense.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-! Acquire the hole and exterior comparisons on one retained Newton surface.
The cut-word estimate retains the removed annuli and exterior polygons. -/
namespace Purelib.Riemann.Branches.NewtonRequestedCutBoundaryComparison

open Purelib
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth (ExteriorSourceRequest)
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorRemainder
  (JoiningEndpointRequest ComponentJoiningArea)
open Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation (atDepth)
open Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank (InterfaceBank)
open Purelib.Riemann.RootContinuation.NewtonOmittedHoleBank (OmittedHoleBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Integration.Path.PairedIncrementArea (area)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering (HoleCenteringRequest CenteredPerimeters)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection (physicalComponentCorrection)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {first second : Fin genus}
  {requested radius : Rational} {floor : Nat}

namespace BoundaryPreparation

variable (prepared : BoundaryPreparation preparation first second (requested / 128) radius floor)

/-- The retained exterior source request at one 128th of the original cut-boundary target. -/
@[expose] def CutBoundarySources (minimum : Nat) := ExteriorSourceRequest prepared (requested / 128) minimum

set_option genInjectivity false in
/-- Retained source, endpoint and side-bank requests for one cut-boundary comparison.

The record keeps the exact depth-refined preparation, its equality to the source refinement, both interface
classifications and a common maximum stage covering all four request owners. -/
structure CutBoundaryRequest (minimum : Nat) where
  /-- The retained exterior source request at the allocated target share. -/ sources : CutBoundarySources prepared
    minimum
  /-- The exact depth-refined original boundary preparation. -/ refined : BoundaryPreparation preparation first second
    (requested / 128) radius floor
  /-- The retained preparation equals the source request's original depth refinement. -/ refined_eq : refined = atDepth
    prepared sources.depth
  /-- The retained endpoint request paying both side and joining errors on the refined owner. -/ endpoints :
    JoiningEndpointRequest refined (requested / 128)
  /-- The original selected-interface request bank on the same refined trace owner. -/ interfaces : InterfaceBank
    refined.excision refined.traces first second
  /-- The original omitted-hole request bank on the same refined trace owner. -/ omitted : OmittedHoleBank
    refined.excision refined.traces first second
  /-- The common stage covering all retained request owners. -/ index : Nat
  /-- The common stage is exactly the maximum of the four retained request indices. -/ index_eq : index = max (max
    sources.index endpoints.val.endpoints.index) (max interfaces.index omitted.index)

constructive_injectivity CutBoundaryRequest

namespace CutBoundaryRequest

open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Prepare the original source, joining endpoints and side banks at a common retained stage.

A positive target is split into 128th shares; the exact source depth determines the refined owner reused by every
remaining request. -/
@[expose] def build (positive : 0 < requested) (minimum : Nat) : CutBoundaryRequest prepared minimum :=
  let sharePositive := Fraction.Order.Field.div_pos_direct positive (by decide +kernel : (0 : Fraction.Rational) < 128)
  let sources := NewtonRequestedExteriorDepth.prepareExteriorSources prepared (requested / 128) sharePositive minimum
  let refined := atDepth prepared sources.depth
  let endpoints := NewtonRequestedExteriorRemainder.prepareJoiningEndpoints refined (requested / 128) sharePositive
  let interfaces := refined.interfaceBank
  let omitted := refined.omittedBank
  ⟨sources, refined, rfl, endpoints, interfaces, omitted,
    max (max sources.index endpoints.val.endpoints.index) (max interfaces.index omitted.index), rfl⟩

variable {prepared} {minimum : Nat} (request : CutBoundaryRequest prepared minimum)

/-- The retained source request's stage is covered by the common request stage. -/
theorem source_le : request.sources.index ≤ request.index := by
  rw [request.index_eq]
  exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _)

/-- The retained endpoint request's stage is covered by the common request stage. -/
theorem endpoint_le : request.endpoints.val.endpoints.index ≤ request.index := by
  rw [request.index_eq]
  exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _)

/-- The retained selected-interface bank's stage is covered by the common request stage. -/
theorem interface_le : request.interfaces.index ≤ request.index := by
  rw [request.index_eq]
  exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)

/-- The retained omitted-hole bank's stage is covered by the common request stage. -/
theorem omitted_le : request.omitted.index ≤ request.index := by
  rw [request.index_eq]
  exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)

/-- The exact retained depth-refined boundary preparation is covered by the common request stage. -/
theorem refined_le : request.refined.index ≤ request.index := by
  have same : request.refined.index = request.sources.refined.index :=
    (congrArg BoundaryPreparation.index request.refined_eq).trans
      (congrArg BoundaryPreparation.index request.sources.refined_eq).symm
  rw [same, request.index_eq]
  exact ((request.sources.refined_le.trans (Data.Nat.Order.le_max_left _ _)).trans (Data.Nat.Order.le_max_left _ _))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- The retained remaining area differs from its component joining sum by less than the original target in squared norm.
-/
@[expose] def RetainedBound {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
  request.refined.domains stage}
    (readings : request.refined.Readings cache) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (readings.2.val.remaining.remainingArea -
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun i => ComponentJoiningArea request.refined i cache))) <
      requested

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Cut pairing minus the selected annuli and canonical component joining areas is within the original target. -/
@[expose] def CutBound {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
  request.refined.domains stage}
    (readings : request.refined.Readings cache) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (readings.1.paired - readings.2.val.annuli.selectedArea -
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (request.refined.exterior.prepared.components.map (fun component =>
      PairedIncrementArea.area (component.program.indexed.map (fun edge =>
        (⟨edgeValuation request.refined.lifted.mesh readings.1.left.values edge,
          Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation request.refined.lifted.mesh readings.1.right.values
            edge⟩ :
            Stokes.PrimitivePoint)))))) < requested

open Purelib.Data.Rat in
/-- A positive target's 128th share pays any strictly smaller-than-128 nonnegative or signed factor. -/
private theorem share_paid (positive : 0 < requested) {factor : Fraction.Rational} (small : factor < 128) :
    factor * (requested / 128) < requested :=
  (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct small (Fraction.Order.Field.div_pos_direct positive (by
    decide +kernel : (0 : Fraction.Rational) < 128))).trans_eq
    ((show 128 * (requested / 128) = (requested / 128) * 128 by ring1).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Both retained-area and canonical cut-area errors satisfy the original requested target.

The supplied readings use the exact retained refined preparation at a stage covering the common request index; the
separate estimates pay factors forty and eighty-two of its 128th share. -/
theorem accurate (positive : 0 < requested)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics request.refined.domains
      stage}
    (readings : request.refined.Readings cache) (later : request.index ≤ stage) :
    request.RetainedBound readings ∧ request.CutBound readings := by
  obtain ⟨sources, refined, refined_eq, endpoints, interfaces, omitted, index, index_eq⟩ := request
  cases refined_eq
  have sourceLe : sources.index ≤ index := by
    rw [index_eq]
    exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _)
  have endpointLe : endpoints.val.endpoints.index ≤ index := by
    rw [index_eq]
    exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _)
  have interfaceLe : interfaces.index ≤ index := by
    rw [index_eq]
    exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)
  have omittedLe : omitted.index ≤ index := by
    rw [index_eq]
    exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)
  have retained := NewtonRequestedExteriorRemainder.ExteriorSourceRequest.retained_area_bound
    sources endpoints.val interfaces omitted readings
    (sourceLe.trans later) (endpointLe.trans later) (interfaceLe.trans later) (omittedLe.trans later)
  have cut := NewtonRequestedExteriorRemainder.ExteriorSourceRequest.cut_pairing_bound
    sources endpoints interfaces omitted readings
    (sourceLe.trans later) (endpointLe.trans later) (interfaceLe.trans later) (omittedLe.trans later)
  have retainedPaid : 2 * (16 * (requested / 128) + 2 * (requested / 128 + requested / 128)) < requested :=
    (by ring1 : 2 * (16 * (requested / 128) + 2 * (requested / 128 + requested / 128)) =
      40 * (requested / 128)).trans_lt (share_paid positive (by decide +kernel : (40 : Fraction.Rational) < 128))
  have cutPaid : 2 * (2 * (16 * (requested / 128) + 2 * (requested / 128 + requested / 128)) + requested / 128) <
    requested :=
    (by ring1 : 2 * (2 * (16 * (requested / 128) + 2 * (requested / 128 + requested / 128)) + requested / 128) =
      82 * (requested / 128)).trans_lt (share_paid positive (by decide +kernel : (82 : Fraction.Rational) < 128))
  exact ⟨retained.trans retainedPaid, cut.trans cutPaid⟩

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- One retained numerical cache with both cut-boundary comparison certificates.

The readings consume the exact cache at the request's common stage and separately certify its retained-area and
canonical cut-area bounds. -/
structure Sample where
  /-- The retained primitive numerical cache at the original request's common stage. -/ cache :
    Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics request.refined.domains request.index
  /-- The comparison readings using that exact retained refined cache. -/ readings : request.refined.Readings cache
  /-- The retained remaining-area comparison satisfies the original target. -/ retained_bounded : request.RetainedBound
    readings
  /-- The canonical cut-area comparison satisfies the original target. -/ cut_bounded : request.CutBound readings

constructive_injectivity Sample

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Cache the original primitive banks once and certify both cut-boundary readbacks.

The builder uses the request's exact common stage and retained refined domains, then stores readings and their two paid
bounds on that same cache. -/
@[expose] def acquire (positive : 0 < requested) : request.Sample := by
  let cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics request.refined.domains request.index :=
    Vector.DependentVector.ofFn fun row =>
    Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.build (standardDifferential row) request.index
      request.refined.domains
  let readings := request.refined.readAt cache request.refined_le
  have bounded := request.accurate positive readings le_rfl
  exact ⟨cache, readings, bounded.1, bounded.2⟩

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Allocate the original refined hole-centering request at one quarter of the positive comparison target. -/
@[expose] def holeCentering (positive : 0 < requested) :
    Meshes.PuncturedGrid.RequestedHoleCentering.HoleCenteringRequest request.refined.lifted
      request.refined.paid.cut.fixed
      first second (requested / 4) :=
  Meshes.PuncturedGrid.RequestedHoleCentering.HoleCenteringRequest.build request.refined.lifted
    request.refined.paid.cut.fixed
    first second (requested / 4)
    (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4))

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Gaussian
/-- The original physical correction is within the quarter target of its exterior-plus-centered-hole decomposition. -/
theorem physical_centered (positive : 0 < requested)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics request.refined.domains
      stage}
    (readings : request.refined.Readings cache)
    (later : (request.holeCentering positive).endpoints.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (readings.1.physical -
      (Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalComponentCorrection readings.1.normalized
        readings.1.neighbors
          readings.1.left readings.1.right .exterior +
        (request.holeCentering positive).centeredTotal
          (Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters.build
            request.refined.paid.cut.exterior.prepared.energy
            cache first second))) < requested / 4 :=
  (request.holeCentering positive).physical_accurate
    (Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters.build
      request.refined.paid.cut.exterior.prepared.energy
      cache first second)
    later readings.1.normalized readings.1.neighbors readings.1.left readings.1.right

/-- The difference between the original annular and retained corrections is below one quarter of the target in squared
norm. -/
@[expose] def CorrectionBound {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
  request.refined.domains stage}
    (readings : request.refined.Readings cache) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (readings.2.val.annuli.correction - readings.2.val.correction) < requested / 4

end

open Purelib.Data.Rat in
/-- A positive target's quarter plus its 128th quarter is strictly below its half. -/
private theorem share_sum {value : Fraction.Rational} (positive : 0 < value) :
    (value / 128) / 4 + value / 4 < value / 2 := by
  have coefficient : (128 : Fraction.Rational)⁻¹ * (4 : Fraction.Rational)⁻¹ + (4 : Fraction.Rational)⁻¹ <
      (2 : Fraction.Rational)⁻¹ := by decide +kernel
  rw [Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.mul_assoc, ← mul_add]
  exact Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct positive coefficient

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A paid correction difference bounds the original cut pairing by the requested target.

The original cut estimate and the separate quarter-target correction bound are combined at a stage covering the retained
comparison request. -/
theorem pairing_small (positive : 0 < requested)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics request.refined.domains
      stage}
    (readings : request.refined.Readings cache) (later : request.index ≤ stage)
    (corrections : request.CorrectionBound readings) :
    Data.Gaussian.Norm.Basic.normSq readings.1.paired < requested := by
  have cutLater : request.refined.paid.cut.index ≤ stage :=
    (Data.Nat.Order.le_max_left _ _).trans (request.refined_le.trans later)
  have relative := readings.2.val.pairing_bound cutLater
  have relativePaid : Data.Gaussian.Norm.Basic.normSq (readings.1.paired - readings.2.val.annuli.correction +
      readings.2.val.correction) ≤ (requested / 128) / 4 :=
    relative.trans request.refined.paid.paid
  have decomposition : readings.1.paired =
      (readings.1.paired - readings.2.val.annuli.correction + readings.2.val.correction) +
      (readings.2.val.annuli.correction - readings.2.val.correction) := by ring1
  rw [decomposition]
  have sumBound : Data.Gaussian.Norm.Basic.normSq (readings.1.paired - readings.2.val.annuli.correction +
        readings.2.val.correction) +
        Data.Gaussian.Norm.Basic.normSq (readings.2.val.annuli.correction - readings.2.val.correction) ≤
      (requested / 128) / 4 + requested / 4 :=
    Fraction.Order.Arithmetic.add_le_add_direct relativePaid corrections.le
  have scaledBound : 2 * (Data.Gaussian.Norm.Basic.normSq (readings.1.paired - readings.2.val.annuli.correction +
        readings.2.val.correction) +
        Data.Gaussian.Norm.Basic.normSq (readings.2.val.annuli.correction - readings.2.val.correction)) ≤
      2 * ((requested / 128) / 4 + requested / 4) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound
      (by decide : (0 : Fraction.Rational) ≤ 2)
  have doubledSmall : 2 * ((requested / 128) / 4 + requested / 4) < requested := by
    have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (by decide : (0 : Fraction.Rational) < 2) (share_sum positive)
    have cancel : 2 * (requested / 2) = requested := by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne requested 2 (by decide)
    exact scaled.trans_eq cancel
  exact (Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (scaledBound.trans_lt doubledSmall)

end CutBoundaryRequest
end BoundaryPreparation

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- A boundary preparation, its exact request and one certified cached comparison sample.

All retained owners share the original Newton preparation, differential pair, positive-scale target, radius and
requested floor and minimum stages. -/
structure CutBoundaryComparison (preparation : NewtonPreparation original) (first second : Fin genus)
    (requested radius : Fraction.Rational) (floor minimum : Nat) where
  /-- The retained original boundary preparation at the allocated 128th target share. -/ prepared : BoundaryPreparation
    preparation first second (requested / 128) radius floor
  /-- The cut-boundary request on that exact preparation and original minimum stage. -/ request :
    BoundaryPreparation.CutBoundaryRequest prepared minimum
  /-- The certified numerical sample owned by that exact retained request. -/ sample : request.Sample

constructive_injectivity CutBoundaryComparison

open Purelib.Data.Rat in
/-- Prepare and sample a certified cut-boundary comparison from the original Newton owner.

The supplied positive target and radius build the boundary once; the resulting request and sample retain that exact
preparation and its cache identities. -/
@[expose] def acquireCutBoundaryComparison (preparation : NewtonPreparation original) (first second : Fin genus)
    (requested radius : Fraction.Rational) (positive : 0 < requested) (radiusPositive : 0 < radius)
    (floor minimum : Nat) : CutBoundaryComparison preparation first second requested radius floor minimum :=
  let prepared := BoundaryPreparation.build preparation first second (requested / 128) radius
    (Fraction.Order.Field.div_pos_direct positive (by decide +kernel : (0 : Fraction.Rational) < 128)) radiusPositive
      floor
  let request := BoundaryPreparation.CutBoundaryRequest.build prepared positive minimum
  ⟨prepared, request, request.acquire positive⟩

end Purelib.Riemann.Branches.NewtonRequestedCutBoundaryComparison
