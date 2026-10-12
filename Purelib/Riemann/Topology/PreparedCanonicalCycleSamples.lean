module
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Execution
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Topology.PreparedCycleModels

public import Purelib.Riemann.Integration.PreparedSwitchedRefinements

open Purelib.Data

public section

/-!
# Canonical samples of cached prepared cycles

Finite bank decomposition and recasting equations, proved before concrete
certificate data is substituted. This module is separate from the refinement
implementation to keep sample-proof iteration local.
-/

namespace Purelib.Riemann.Topology.PreparedCanonicalCycleSamples

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Riemann.Topology.PreparedCycleModels (Owner)

section
open Purelib.Riemann
open Purelib.Curves
open Purelib.Data
open Purelib.Polynomial
open Purelib.Geometry
/-- Every actual parent of a canonical prepared path has the canonical center state of its original edge. -/
private theorem ofPreparedPath_parent_center {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (sheet : Fin 2)
    {ambient : Rational.Box} :
    forall {start finish : Gaussian.Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared :
        Paths.PreparedClearPathModels.PreparedPath path owner)
      (centered : Integration.PreparedSubdivisionModelCore.CenteredEdge
        curve differential),
      centered ∈
          (Integration.PreparedDirectDyadicRefinements.CenteredPathChain.ofPreparedPath
            curve differential sheet prepared).parents →
        centered.center =
          Integration.PreparedConstantModels.PreparedEdge.CenterState.canonical
            centered.edge
  | _, _, .nil _point, _, .nil _ _owner, centered, membership => by
      change centered ∈ [] at membership
      cases membership
  | _, _, .cons _head _tail, _,
      .cons _ _ _owner _headWithin preparedHead preparedTail,
      centered, membership => by
      rcases List.Membership.mem_append.mp membership with
        headMembership | tailMembership
      · rw [Integration.PreparedDirectDyadicRefinements.CenteredPathChain.dataOfCompleteSegment_parents]
          at headMembership
        unfold Paths.PreparedClearPathModels.CompleteSegment.centeredEdges
          at headMembership
        exact
          Integration.PreparedSubdivisionAutomaticModels.centeredEdges_canonical_center
            curve differential sheet preparedHead.subdivision centered
              headMembership
      · exact ofPreparedPath_parent_center curve differential sheet
          preparedTail centered tailMembership

/-- Every parent from any retained dyadic-bank realization has its original edge's canonical center state. -/
private theorem ofDyadicBank_parent_center {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (sheet : Fin 2)
    {depth : Nat} {rootDiameter : Rat.Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : Paths.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner)
    (centered : Integration.PreparedSubdivisionModelCore.CenteredEdge
      curve differential)
    (membership : centered ∈
      (Integration.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
        curve differential sheet bank).parents) :
    centered.center =
      Integration.PreparedConstantModels.PreparedEdge.CenterState.canonical
        centered.edge := by
  cases bank with
  | safe checked =>
      exact ofPreparedPath_parent_center curve differential sheet
        checked.prepared centered membership
  | executed _within prepared _success =>
      exact ofPreparedPath_parent_center curve differential sheet
        prepared centered membership
  | executedCertified checked =>
      change centered ∈
        (Integration.PreparedDirectDyadicRefinements.CenteredPathChain.ofExecutedCheckedDyadic
          curve differential sheet checked).parents at membership
      rw
        [Integration.PreparedDirectDyadicRefinements.CenteredPathChain.ofExecutedCheckedDyadic_parents_eq_ofPreparedPath
        curve differential sheet checked] at membership
      exact ofPreparedPath_parent_center curve differential sheet
        checked.prepared centered membership
  | certified certificate =>
      exact ofPreparedPath_parent_center curve differential sheet
        certificate.prepared centered membership

end

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- Recasting a canonical prepared bank to its own differential preserves its actual integral sample.

The original parent-center equations identify each recast model before the finite tail accumulation. -/
theorem ofDyadicBank_tailMappedIntegralSample_recast_self {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (sheet : Fin 2)
    {depth : Nat} {rootDiameter : Rat.Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : Paths.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    Polynomial.Gaussian.Path.Basic.PathModel.tailMappedIntegralSample
        (Integration.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
          curve differential sheet bank).parents
        (fun centered =>
          (Integration.PreparedEdgeRecasting.recastCenteredEdge
            differential centered).model) =
      Polynomial.Gaussian.Path.Basic.PathModel.tailMappedIntegralSample
        (Integration.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
          curve differential sheet bank).parents
        Integration.PreparedSubdivisionModelCore.CenteredEdge.model := by
  apply Integration.Polynomial.Gaussian.Path.Basic.PathModel.tailMappedIntegralSample_congr
  intro centered membership
  have canonical := ofDyadicBank_parent_center curve differential sheet
    bank centered membership
  cases centered with
  | mk edge center =>
      dsimp only at canonical ⊢
      cases canonical
      rfl

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
/-- Read the canonical cycle integral as the sum of its exact cached bank samples.

Bridge cycles retain the forward and backward banks; finite-cut cycles retain forward, right boundary, backward and left
boundary in their original order, with self-recasts eliminated by canonical-center readback. -/
theorem cycleState_tailMappedCanonicalIntegralSample {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (source : Hyperelliptic.Differentials.Basic.Differential
      genus) :
    forall (data : Topology.PreparedCycleModels.PreparedCycleData curve),
    Polynomial.Gaussian.Path.Basic.PathModel.tailMappedIntegralSample
        (Integration.PreparedSwitchedRefinements.cycleState curve source data).parents
        (fun centered =>
          (Integration.PreparedEdgeRecasting.recastCenteredEdge
            source centered).model) =
      match data with
      | .bridge bridge =>
          let forward :=
            Integration.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 0 bridge.forwardChecked
          let backward :=
            Integration.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 bridge.backwardChecked
          Polynomial.Gaussian.Path.Basic.PathModel.tailMappedIntegralSample
              forward.parents
              Integration.PreparedSubdivisionModelCore.CenteredEdge.model +
            Polynomial.Gaussian.Path.Basic.PathModel.tailMappedIntegralSample
              backward.parents
              Integration.PreparedSubdivisionModelCore.CenteredEdge.model
      | .finiteCut boundary =>
          let forward :=
            Integration.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 0 boundary.forwardChecked
          let rightBoundary :=
            Integration.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 0 boundary.rightBoundaryChecked
          let backward :=
            Integration.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 boundary.backwardChecked
          let leftBoundary :=
            Integration.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 boundary.leftBoundaryChecked
          Polynomial.Gaussian.Path.Basic.PathModel.tailMappedIntegralSample
              forward.parents
              Integration.PreparedSubdivisionModelCore.CenteredEdge.model +
            Polynomial.Gaussian.Path.Basic.PathModel.tailMappedIntegralSample
                rightBoundary.parents
                Integration.PreparedSubdivisionModelCore.CenteredEdge.model +
              Polynomial.Gaussian.Path.Basic.PathModel.tailMappedIntegralSample
                  backward.parents
                  Integration.PreparedSubdivisionModelCore.CenteredEdge.model +
                Polynomial.Gaussian.Path.Basic.PathModel.tailMappedIntegralSample
                  leftBoundary.parents
                  Integration.PreparedSubdivisionModelCore.CenteredEdge.model
  | .bridge bridge => by
      rw [Integration.PreparedSwitchedRefinements.cycleState_tailMappedIntegralSample]
      simp only
      rw [ofDyadicBank_tailMappedIntegralSample_recast_self,
        ofDyadicBank_tailMappedIntegralSample_recast_self]
  | .finiteCut boundary => by
      rw [Integration.PreparedSwitchedRefinements.cycleState_tailMappedIntegralSample]
      simp only
      rw [ofDyadicBank_tailMappedIntegralSample_recast_self,
        ofDyadicBank_tailMappedIntegralSample_recast_self,
        ofDyadicBank_tailMappedIntegralSample_recast_self,
        ofDyadicBank_tailMappedIntegralSample_recast_self]

end Purelib.Riemann.Topology.PreparedCanonicalCycleSamples
