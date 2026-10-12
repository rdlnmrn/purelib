module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Riemann.Transport.PreparedUniformRefinementReplay
public import Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedMeshReplay
public import Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace

import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Init.Prelude
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

section

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay

open Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay

open Purelib.Riemann.Integration

section
@[expose] public section

/-!
Disk-backed centring of the original prepared bank spines.  Each callback
receives the complete original-source equation, not just matching numbers.
The explicit stored-spine eliminators retain the owners already computed by
preparation instead of rebuilding their canonical indices during execution.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Preparation.Roots.PreparedRootSafeReplay.Selection

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CheckedDirectMeshes)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Coordinate)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CheckedSelection MeshAllowanceChecks)

/-- The replayed first success is the exact choice of the root-safe selector, including its geometric movement floor and
original finite proposal order. -/
theorem selected_eq (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target)
    (trace : Trace.Search parents proper targets target 8
      (PreparedDirectDyadicRefinements.commonAccuracyDepth target parents)
      (PreparedDirectDyadicRefinements.proposedRootBits parents.length
        (PreparedDirectDyadicRefinements.familyForecast parents targets) target))
    (selected : CheckedSelection parents targets target) (found : trace.value = some selected) :
    selected = (_root_.Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy.RootSafeAccuracy.select parents proper
      targets target positive).selected := by
  have observed := trace.equation.trans found
  unfold Riemann.RootContinuation.PreparedRootSafeAccuracy.RootSafeAccuracy.select
  dsimp only
  split
  · rename_i choice reported
    exact (Option.some.inj (reported.symm.trans observed)).symm
  · rename_i reported
    cases reported.symm.trans observed

/-- Exhaustion identifies the original total fallback; it does not certify failure of that fallback or of the requested
period. -/
theorem fallback_eq (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target)
    (trace : Trace.Search parents proper targets target 8
      (PreparedDirectDyadicRefinements.commonAccuracyDepth target parents)
      (PreparedDirectDyadicRefinements.proposedRootBits parents.length
        (PreparedDirectDyadicRefinements.familyForecast parents targets) target))
    (found : trace.value = none) :
    (_root_.Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy.RootSafeAccuracy.select parents proper targets
      target positive).selected =
      PreparedDirectDyadicRefinements.uniformSelection parents proper targets target positive := by
  have observed := trace.equation.trans found
  unfold Riemann.RootContinuation.PreparedRootSafeAccuracy.RootSafeAccuracy.select
  dsimp only
  split
  · rename_i choice reported
    cases reported.symm.trans observed
  · rfl

open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint)

/-- The original root-safe eight-attempt search retaining its movement depth floor and forecast-derived root precision.
-/
abbrev OriginalSearch (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) :=
  Trace.Search parents proper targets target 8
    (PreparedDirectDyadicRefinements.commonAccuracyDepth target parents)
    (PreparedDirectDyadicRefinements.proposedRootBits parents.length
      (PreparedDirectDyadicRefinements.familyForecast parents targets) target)

set_option genInjectivity false in
/-- A retained unfinished root-safe selection with its original search and fallback evidence.

The geometric movement floor, precision proposal, exhaustion trace and exact uniform mesh requests remain unchanged. -/
inductive PendingSelection (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) : Type 2
  /-- The root-safe bounded search is pending with its original movement floor and root precision. -/ | search (pending
    : Trace.PendingSearch parents proper targets target 8
      (PreparedDirectDyadicRefinements.commonAccuracyDepth target parents)
      (PreparedDirectDyadicRefinements.proposedRootBits parents.length
        (PreparedDirectDyadicRefinements.familyForecast parents targets) target))
  /-- The root-safe bounded search was exhausted and its original uniform fallback mesh preparation is pending. -/ |
    uniformPreparation (trace :
    OriginalSearch parents proper
    targets target) (exhausted : trace.value = none)
      (plan : _root_.Purelib.Riemann.Transport.PreparedUniformRefinementReplay.Plan parents targets target)
      (pending : PreparedMeshReplay.Pending plan.depth plan.diameter plan.positive parents proper)
  /-- The root-safe bounded search was exhausted and its uniform fallback retains the exact geometric failure. -/ |
    uniformGeometry (trace :
    OriginalSearch parents proper
    targets target) (exhausted : trace.value = none)
      (plan : _root_.Purelib.Riemann.Transport.PreparedUniformRefinementReplay.Plan parents targets target)
      (failure : CheckedDirectMeshes.Inconclusive plan.depth plan.diameter plan.positive parents proper)

constructive_injectivity PendingSelection

end Purelib.Curves.Hyperelliptic.Integration.Preparation.Roots.PreparedRootSafeReplay.Selection

end

end
