module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.LocalPairedPeriodComparison
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedExteriorReduction
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalExteriorLapRequest
public import Purelib.Riemann.RootContinuation.NewtonExteriorCanonicalRemainder
import Purelib.Tactic.Ring
import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth
import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorRemainder

public section

open Purelib.Data

/-! Cancel the actual exterior polygons in the ordered period comparison.
Only the terminal factor times the original exterior total remains. -/
namespace Purelib.Riemann.RootContinuation.NewtonOrderedExteriorCancellation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation (atDepth)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Riemann.Branches.NewtonRequestedCutComparison (CutAnnularReadings)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth (ExteriorSourceRequest)
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorRemainder (JoiningEndpointRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedExteriorReduction (exteriorPeriodRequest exteriorPeriodResidual)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalExteriorLapRequest (originalExteriorLapRequest
  atDepth_exterior_components)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.LocalPairedPeriodComparison (resplitWordDeterminant)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal (resplitPhysicalExteriorCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection (physicalComponentCorrection)
open Purelib.Integration.Path.PairedIncrementArea (area)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    (prepared : Prepared paired)
  {preparation : NewtonPreparation base.bank.toBranchCellBank}
  {target radius : Rational} {i j : Fin genus} {floor : Nat}

open Purelib.Curves.Hyperelliptic.Meshes.Newton in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing in
/-- The retained resplit determinant with its terminal exterior factor subtracted.

The exact original ordered pairing determines that factor: it vanishes for an odd ending and retains the original
exterior total for an even ending. -/
@[expose] def exteriorAdjustedDeterminant (newSheet : Fin 2)
    (boundary : BoundaryPreparation preparation i j target radius floor)
    {stage : Nat} {cache : RegularMeshes.Numerics boundary.domains stage}
    (readings : CutPairingRequest.Readings boundary.paid.cut cache) : Gaussian :=
  LocalPairedPeriodComparison.resplitWordDeterminant prepared (current := boundary.lifted) newSheet
    (CanonicalEdgeValues.edgeValuation boundary.lifted.mesh readings.left.values) (CanonicalEdgeValues.edgeValuation
      boundary.lifted.mesh readings.right.values) -
      BilinearPolarization.extract (fun coefficient => ExteriorTotal.resplitPhysicalExteriorCorrection (paired :=
        paired)
        boundary.fine.family.single.grid.shrunk.included boundary.lifted.edges boundary.lifted.vertices newSheet
        (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation boundary.lifted.mesh readings.left.values)
          (CanonicalEdgeValues.edgeValuation boundary.lifted.mesh readings.right.values) coefficient))

open Purelib.Curves.Hyperelliptic.Meshes.Newton in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing in
open Purelib.Data in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Gaussian.Norm.Sum.Basic in
open Purelib.Data.Rat in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Integration in
open Purelib.Riemann.RootContinuation.NewtonExteriorCanonicalRemainder in
/-- Select a stage paying the actual exterior polygons and endpoint errors of the corrected determinant.

The same refined cache combines ordered-period reduction, original exterior laps and canonical remainder bounds for
either degree shape. The selected threshold preserves the minimum and every retained request index. -/
@[expose] def exteriorAdjustedRequest (newSheet : Fin 2)
    (boundary : BoundaryPreparation preparation i j target radius floor)
    (canonical : boundary.exterior.prepared.components.map (fun component => component.program.indexed) =
      boundary.lifted.exteriorBoundaries)
    {requested : Rat.Fraction.Rational} {referenceFloor : Nat} (result : ExteriorSourceRequest boundary requested
      referenceFloor)
    {endpointTarget : Rat.Fraction.Rational} (endpoints : JoiningEndpointRequest (atDepth boundary result.depth)
      endpointTarget)
    (minimum : Nat) :
    let refined := atDepth boundary result.depth
    {threshold : Nat // minimum ≤ threshold ∧
      ∀ stage (cache : RegularMeshes.Numerics boundary.domains stage)
        (readings : CutPairingRequest.Readings refined.paid.cut cache)
        (_cached : CutAnnularReadings refined.comparison readings), threshold ≤ stage →
        let determinant := exteriorAdjustedDeterminant prepared newSheet refined readings
        Data.Gaussian.Norm.Basic.normSq (determinant + determinant) <
          2 * (180 * target + 2 * (target + 2 * (2 * (endpointTarget + requested) + endpointTarget)))} := by
  intro refined
  have positive : 0 < target := (Arithmetic.mul_pos_direct boundary.fine.positive (by
      decide : (0 : Rat.Fraction.Rational) < 4)).trans_eq
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  let reduction := OrderedExteriorReduction.exteriorPeriodRequest prepared newSheet refined minimum
  let laps := OriginalExteriorLapRequest.originalExteriorLapRequest refined
    (OriginalExteriorLapRequest.atDepth_exterior_components boundary canonical result.depth) target positive minimum
  let threshold := max (max reduction.val laps.val) (max result.index endpoints.val.endpoints.index)
  refine ⟨threshold, reduction.property.1.trans ((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_left _ _)), ?_⟩
  intro stage cache readings cached later determinant
  have localLater := (Nat.Order.le_max_left _ _).trans later
  have sourceLater := (Nat.Order.le_max_right _ _).trans later
  have reductionBound := reduction.property.2 stage cache readings cached ((Nat.Order.le_max_left _ _).trans localLater)
  have lapBound := laps.property.2 stage cache readings ((Nat.Order.le_max_right _ _).trans localLater) newSheet
  have sourceBound := ExteriorSourceRequest.canonical_remainder_bound result endpoints readings ((Nat.Order.le_max_left
    _ _).trans sourceLater)
    ((Nat.Order.le_max_right _ _).trans sourceLater)
  let lap := BilinearPolarization.extract (fun coefficient => refined.lifted.edges.chainArea refined.lifted.vertices
    (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.left.values)
      (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.right.values) coefficient)
    (refined.fine.family.single.grid.shrunk.included.resplit base.bank.exterior (FramedBranchCellBank.baseMember
      base.bank)) newSheet)
  let componentArea := Data.Gaussian.Norm.Sum.Basic.gaussianSum (refined.exterior.prepared.components.map (fun
    component =>
    Path.PairedIncrementArea.area (component.program.indexed.map (fun edge =>
      (⟨edgeValuation refined.lifted.mesh readings.left.values edge,
        CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.right.values edge⟩ : PrimitivePoint)))))
  let exterior := PhysicalComponentCorrection.physicalComponentCorrection readings.normalized readings.neighbors
    readings.left readings.right .exterior
  change Data.Gaussian.Norm.Basic.normSq (lap + lap - componentArea) ≤ target at lapBound
  change Data.Gaussian.Norm.Basic.normSq (exterior + componentArea) <
      2 * (2 * (endpointTarget + requested) + endpointTarget) at sourceBound
  have exteriorBound := (Bounds.normSq_add_le_two (lap + lap - componentArea) (exterior + componentArea)).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rat.Fraction.Rational) < 2)
      ((Arithmetic.add_le_add_direct lapBound (le_refl _)).trans_lt (Arithmetic.add_lt_add_left_direct sourceBound
        target)))
  rw [show lap + lap - componentArea + (exterior + componentArea) = lap + lap + exterior by ring1] at exteriorBound
  have estimate := (Bounds.normSq_sub_le_two (OrderedExteriorReduction.exteriorPeriodResidual prepared newSheet refined
    readings) (lap + lap + exterior)).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rat.Fraction.Rational) < 2)
      (Arithmetic.add_lt_add_direct reductionBound exteriorBound))
  have equal : OrderedExteriorReduction.exteriorPeriodResidual prepared newSheet refined readings - (lap + lap +
    exterior) = determinant + determinant := by
    have scalar (a b : Gaussian.Basic.Canonical → Gaussian.Basic.Canonical) (d e : Gaussian.Basic.Canonical) :
        (BilinearPolarization.extract (fun c => a c - b c) + d) + (BilinearPolarization.extract (fun c => a c - b c) +
          d) + e -
          (BilinearPolarization.extract a + BilinearPolarization.extract a + e) = (d - BilinearPolarization.extract b) +
            (d - BilinearPolarization.extract b) := by
      unfold BilinearPolarization.extract
      ring1
    exact scalar
      (fun coefficient => refined.lifted.edges.chainArea refined.lifted.vertices
        (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.left.values)
          (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.right.values) coefficient)
        (refined.fine.family.single.grid.shrunk.included.resplit base.bank.exterior (FramedBranchCellBank.baseMember
          base.bank)) newSheet)
      (fun coefficient => ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
        refined.fine.family.single.grid.shrunk.included refined.lifted.edges refined.lifted.vertices newSheet
        (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.left.values)
          (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.right.values) coefficient))
      (LocalPairedPeriodComparison.resplitWordDeterminant prepared (current := refined.lifted) newSheet
        (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.left.values) (CanonicalEdgeValues.edgeValuation
          refined.lifted.mesh readings.right.values)) exterior
  exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).symm.trans_lt estimate

end Purelib.Riemann.RootContinuation.NewtonOrderedExteriorCancellation
