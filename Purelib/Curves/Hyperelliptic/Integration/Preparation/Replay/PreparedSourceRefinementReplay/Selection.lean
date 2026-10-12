module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Riemann.Transport.PreparedUniformRefinementReplay
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedMeshReplay
public import Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace

import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay

open Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay

open Purelib.Riemann.Integration

section
public section

/-!
Disk-backed centring of the original prepared bank spines.  Each callback
receives the complete original-source equation, not just matching numbers.
The explicit stored-spine eliminators retain the owners already computed by
preparation instead of rebuilding their canonical indices during execution.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSourceRefinementReplay.Selection

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CheckedDirectMeshes)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Coordinate)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CheckedSelection MeshAllowanceChecks)

open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint)
section Source

open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (proposedRootBits familyForecast checkedDirectSelection
  uniformSelection accurateDirectRefinement)

/-- A retained successful search trace identifies exactly the original checked direct selection. -/
theorem
  selected_eq
  (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target)
    (trace : Trace.Search parents proper targets target 8 0
      (proposedRootBits parents.length (familyForecast parents targets) target))
    (selected : CheckedSelection parents targets target) (found : trace.value = some selected) :
    selected = checkedDirectSelection parents proper targets target positive := by
  unfold checkedDirectSelection
  dsimp only
  rw [trace.equation, found]

/-- Exhaustion of the retained bounded search identifies the original uniform fallback selection. -/
theorem
  fallback_eq
  (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target)
    (trace : Trace.Search parents proper targets target 8 0
      (proposedRootBits parents.length (familyForecast parents targets) target))
    (found : trace.value = none) :
    checkedDirectSelection parents proper targets target positive =
      uniformSelection parents proper targets target positive := by
  unfold checkedDirectSelection
  dsimp only
  rw [trace.equation, found]

/-- The original eight-attempt selection search with its initial depth and forecast-derived root precision. -/
abbrev
  OriginalSearch
  (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) :=
  Trace.Search parents proper targets target 8
    0
    (PreparedDirectDyadicRefinements.proposedRootBits parents.length
      (PreparedDirectDyadicRefinements.familyForecast parents targets) target)

set_option genInjectivity false in
/-- A retained unfinished selection with its exact bounded-search or uniform-fallback state.

Prior search exhaustion, original fallback plan and incomplete or failed mesh checks remain attached to the same parent
family and targets. -/
inductive
  PendingSelection
  (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) : Type 2
  /-- The original bounded selection search is pending at its retained request. -/ | search (pending :
    Trace.PendingSearch parents proper targets target 8
      0
      (PreparedDirectDyadicRefinements.proposedRootBits parents.length
        (PreparedDirectDyadicRefinements.familyForecast parents targets) target))
  /-- The bounded search was exhausted and the original uniform fallback mesh preparation is still pending. -/ |
    uniformPreparation (trace :
    OriginalSearch parents
    proper targets target) (exhausted : trace.value = none)
      (plan : _root_.Purelib.Riemann.Transport.PreparedUniformRefinementReplay.Plan parents targets target)
      (pending : PreparedMeshReplay.Pending plan.depth plan.diameter plan.positive parents proper)
  /-- The bounded search was exhausted and the original uniform fallback retains its exact geometric failure. -/ |
    uniformGeometry (trace :
    OriginalSearch parents
    proper targets target) (exhausted : trace.value = none)
      (plan : _root_.Purelib.Riemann.Transport.PreparedUniformRefinementReplay.Plan parents targets target)
      (failure : CheckedDirectMeshes.Inconclusive plan.depth plan.diameter plan.positive parents proper)

constructive_injectivity PendingSelection

end Source

end Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSourceRefinementReplay.Selection

end
