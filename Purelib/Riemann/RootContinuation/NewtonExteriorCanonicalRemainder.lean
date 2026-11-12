module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
public import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorRemainder
import Purelib.Tactic.Ring

@[expose] public section

/-! Transport the paid exterior remainder to the canonical component
polygons on the same edge readings, paying the endpoint comparison. -/
namespace Purelib.Riemann.RootContinuation.NewtonExteriorCanonicalRemainder

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth (ExteriorSourceRequest)
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorRemainder
  (JoiningEndpointRequest ComponentJoiningArea ComponentBoundaryJoiningArea boundary_joining_valuation
   joining_boundary_bound)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest (Readings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection (physicalComponentCorrection)
open Purelib.Integration.Path.PairedIncrementArea (area)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {first second : Fin genus} {target radius :
    Rational} {floor : Nat}

open Purelib.Integration.Path.PairedIncrementArea (area) in
open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
/-- Transport the paid exterior remainder to the actual canonical component polygons.

The original source and endpoint requests use the same refined geometry and edge readings. The bound pays their endpoint
comparison while retaining each complete component area. -/
theorem ExteriorSourceRequest.canonical_remainder_bound
    {prepared : BoundaryPreparation preparation first second target radius floor}
    {requested : Rational} {minimum : Nat}
    (result : ExteriorSourceRequest prepared requested minimum)
    {endpointTarget : Rational}
    (endpoints : JoiningEndpointRequest (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth
      prepared result.depth) endpointTarget)
    {stage : Nat} {cache : Numerics
      prepared.domains stage}
    (readings : Readings
      (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).paid.cut cache)
    (later : result.index ≤ stage) (endpointLater : endpoints.val.endpoints.index ≤ stage) :
    normSq
      (physicalComponentCorrection readings.normalized
      readings.neighbors readings.left readings.right .exterior +
      gaussianSum
        ((NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
        result.depth).exterior.prepared.components.map (fun component =>
        area (component.program.indexed.map (fun edge =>
          (⟨edgeValuation (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
            result.depth).lifted.mesh readings.left.values edge,
            edgeValuation
              (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
              result.depth).lifted.mesh readings.right.values edge⟩ : PrimitivePoint)))))) <
      2 * (2 * (endpointTarget + requested) + endpointTarget) := by
  have source := NewtonRequestedExteriorRemainder.ExteriorSourceRequest.remainder_accurate
    result endpoints.val readings later endpointLater
  have joining := (joining_boundary_bound
    (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth)
    endpoints.val.endpoints readings endpointLater).trans endpoints.property
  let physical := physicalComponentCorrection
    readings.normalized readings.neighbors readings.left readings.right .exterior
  let fine := gaussianSum (List.ofFn (fun i => ComponentJoiningArea
    (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth) i cache))
  let canonical := gaussianSum (List.ofFn (fun i => ComponentBoundaryJoiningArea
    (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth) i readings))
  change normSq (physical + fine) < 2 * (endpointTarget + requested) at source
  change normSq (fine - canonical) ≤ endpointTarget at joining
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_two (physical + fine) (fine - canonical)).trans_lt
    (Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rational) < 2)
      ((Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct source _).trans_le
        (Rat.Fraction.Order.Arithmetic.add_le_add_direct (le_refl _) joining)))
  rw [show physical + fine - (fine - canonical) = physical + canonical by ring1] at estimate
  exact (congrArg (fun area => normSq (physical + area))
    (boundary_joining_valuation (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
      result.depth) readings)).symm.trans_lt estimate

end Purelib.Riemann.RootContinuation.NewtonExteriorCanonicalRemainder
