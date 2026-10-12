module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedDirectMeshEquality
import Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements

public section

namespace Purelib.Riemann.Transport.PreparedUniformRefinementReplay

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedDirectMeshEquality

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data in
set_option genInjectivity false in
/-- The exact diameter and depth of a uniform differential refinement request.

The retained positive diameter equals the original common accuracy choice, and the depth equals the maximum required for
sufficiency and accuracy. -/
structure Plan (parents : List (CenteredEdge curve source))
    (targets : List (Basic.Differential genus)) (target : Rat.Fraction.Rational) where
  /-- The cached common positive root diameter. -/ diameter : Rat.Fraction.Rational
  /-- The cached diameter is strictly positive. -/ positive : 0 < diameter
  /-- The cached common dyadic refinement depth. -/ depth : Nat
  /-- The diameter is the original accuracy selected for these parents and targets. -/ diameter_eq : diameter =
    differentialRefinementAccuracy parents targets target
  /-- The depth is the original maximum of the sufficiency and accuracy requirements. -/ depth_eq : depth = max
    (commonSufficientDepth (differentialRefinementAccuracy parents targets target) parents)
    (commonAccuracyDepth (differentialRefinementAccuracy parents targets target) parents)

constructive_injectivity Plan

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data in
/-- Compute and retain the exact common diameter and depth for a positive target. -/
@[expose] def Plan.build (parents : List (CenteredEdge curve source))
    (targets : List (Basic.Differential genus)) (target : Rat.Fraction.Rational) (positive : 0 < target) :
    Plan parents targets target :=
  let diameter := differentialRefinementAccuracy parents targets target
  let depth := max (commonSufficientDepth diameter parents) (commonAccuracyDepth diameter parents)
  ⟨diameter, differentialRefinementAccuracy_positive parents targets positive, depth, rfl, rfl⟩

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Curves.Hyperelliptic.Integration.Observation in
open Purelib.Data in
/-- Checked meshes at the retained uniform plan satisfy every requested differential allowance.

Proper original parents identify these meshes with the original uniform selection, whose doubled aggregate allowance is
at most the target. -/
theorem bounds (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Basic.Differential genus)) (target : Rat.Fraction.Rational) (positive : 0 < target)
    (plan : Plan parents targets target) (meshes : CheckedDirectMeshes plan.depth plan.diameter parents) :
    ∀ differential ∈ targets, 2 * meshes.aggregateAllowanceFor differential ≤ target := by
  cases plan with
  | mk diameter diameterPositive depth diameterEq depthEq =>
      dsimp only at meshes
      cases diameterEq
      cases depthEq
      have same := PreparedDirectMeshEquality.meshes_eq proper meshes
        (uniformSelection parents proper targets target positive).meshes
      intro differential member
      rw [same]
      exact (uniformSelection parents proper targets target positive).allowances.bound differential member

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data in
/-- Package the actual checked meshes with their uniform allowance certificates.

The retained plan supplies the exact diameter and depth, and the original target differential list indexes all allowance
checks. -/
@[expose] def selected (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Basic.Differential genus)) (target : Rat.Fraction.Rational) (positive : 0 < target)
    (plan : Plan parents targets target) (meshes : CheckedDirectMeshes plan.depth plan.diameter parents) :
    CheckedSelection parents targets target :=
  ⟨plan.diameter, plan.positive, plan.depth, meshes,
    MeshAllowanceChecks.ofBounds meshes target targets (bounds parents proper targets target positive plan meshes)⟩

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Curves.Hyperelliptic.Integration.Observation in
open Purelib.Data in
/-- The reconstructed selection equals the original uniform refinement selection. -/
theorem selected_eq (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Basic.Differential genus)) (target : Rat.Fraction.Rational) (positive : 0 < target)
    (plan : Plan parents targets target) (meshes : CheckedDirectMeshes plan.depth plan.diameter parents) :
    selected parents proper targets target positive plan meshes = uniformSelection parents proper targets target
      positive :=
  PreparedDirectMeshEquality.selection_eq proper _ _ plan.diameter_eq plan.depth_eq

end Purelib.Riemann.Transport.PreparedUniformRefinementReplay

end
