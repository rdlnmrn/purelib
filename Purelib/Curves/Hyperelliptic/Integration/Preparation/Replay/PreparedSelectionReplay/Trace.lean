module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
public import Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedMeshReplay
import Init.Prelude
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting

section

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay

open Purelib.Riemann.Integration

section
@[expose] public section

/-!
Disk-backed centring of the original prepared bank spines.  Each callback
receives the complete original-source equation, not just matching numbers.
The explicit stored-spine eliminators retain the owners already computed by
preparation instead of rebuilding their canonical indices during execution.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CheckedDirectMeshes)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Coordinate)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CheckedSelection MeshAllowanceChecks)

/-- The positive quarter-radius schedule at the retained precision-bit index. -/
abbrev diameterAt (bits : Nat) : Coordinate := Geometric.Basic.quarterRadius 1 bits

/-- Every scheduled quarter-radius diameter is strictly positive. -/
theorem diameterAt_positive (bits : Nat) : 0 <
  Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt bits :=
  Geometric.Basic.quarterRadius_pos (by decide) bits

set_option genInjectivity false in
/-- The complete first-success search trace, including actual cached allowances and every preceding finite geometric or
allowance miss. -/
inductive Search (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) : Nat → Nat → Nat → Type 2
  /-- The finite search stopped with no remaining fuel. -/ | exhausted {depth bits : Nat} :
    Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.Search parents proper
    targets target 0 depth bits
  /-- Retain the actual geometric failure before continuing at greater subdivision depth. -/ | geometry {fuel depth bits
    : Nat}
      (failure : CheckedDirectMeshes.Inconclusive depth
        (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt bits)
        (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt_positive bits)
        parents proper)
      (next : Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.Search parents
        proper targets target fuel (depth + 1) bits) :
      Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.Search parents proper
        targets target (fuel + 1) depth bits
  /-- Retain accepted meshes and their failed allowance check before increasing depth and precision. -/ | allowance
    {fuel depth bits : Nat}
      (meshes : CheckedDirectMeshes depth
        (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt bits) parents)
      (observed : CheckedDirectMeshes.attempt depth
        (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt bits)
        (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt_positive bits)
        parents proper = .ok meshes)
      (failure : MeshAllowanceChecks.Inconclusive meshes target targets)
      (next : Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.Search parents
        proper targets target fuel (depth + 1) (bits + 1)) :
      Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.Search parents proper
        targets target (fuel + 1) depth bits
  /-- Retain the first accepted meshes and allowance certificates with both original checker equalities. -/ | accepted
    {fuel depth bits : Nat}
      (meshes : CheckedDirectMeshes depth
        (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt bits) parents)
      (observed : CheckedDirectMeshes.attempt depth
        (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt bits)
        (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt_positive bits)
        parents proper = .ok meshes)
      (allowances : MeshAllowanceChecks meshes target targets)
      (checked : MeshAllowanceChecks.attempt meshes target targets = .ok allowances) :
      Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.Search parents proper
        targets target (fuel + 1) depth bits

constructive_injectivity Search

namespace Search

variable {parents : List (CenteredEdge curve source)} {proper : AllParentsProper parents}
    {targets : List (Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus)} {target : Coordinate}

/-- Read the retained first successful selection from the finite trace, or none after exhaustion. -/
def value : {fuel depth bits : Nat} →
  Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.Search parents proper targets target
  fuel depth bits →
    Option (CheckedSelection parents targets target)
  | _, _, _, .exhausted => none
  | _, _, _, .geometry _ next => next.value
  | _, _, _, .allowance _ _ _ next => next.value
  | _, depth, bits, .accepted meshes _ allowances _ =>
      some ⟨diameterAt bits,
        Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt_positive bits,
        depth, meshes, allowances⟩

/-- The retained search trace reads back to the exact original finite selection procedure. -/
theorem equation : ∀ {fuel depth bits : Nat} (trace :
  Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.Search parents proper targets target
  fuel depth bits),
    Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.searchSelection parents proper targets target fuel depth
      bits = trace.value
  | _, _, _, .exhausted => rfl
  | _, _, _, .geometry failure next => by
      unfold Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.searchSelection
      dsimp only
      rw [failure.attempt_error]
      exact next.equation
  | _, _, _, .allowance meshes observed failure next => by
      unfold Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.searchSelection
      dsimp only
      rw [observed]
      dsimp only
      rw [failure.attempt_error]
      exact next.equation
  | _, _, _, .accepted meshes observed allowances checked => by
      unfold Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.searchSelection
      dsimp only
      rw [observed]
      dsimp only
      rw [checked]
      rfl

end Search

set_option genInjectivity false in
/-- A suspended finite selection search retaining its preceding failed requests.

The current pending mesh work and every prior geometry or allowance failure keep their original owners, depth and
precision indices. -/
inductive PendingSearch (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) : Nat → Nat → Nat → Type 2
  /-- Retain the incomplete current mesh-check spine at the exact search request. -/ | current {fuel depth bits : Nat}
      (pending : PreparedMeshReplay.Pending depth
        (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt bits)
        (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt_positive bits)
        parents proper) :
      Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.PendingSearch parents
        proper targets target (fuel + 1) depth bits
  /-- Retain the actual geometric failure before continuing at greater subdivision depth. -/ | geometry {fuel depth bits
    : Nat}
      (failure : CheckedDirectMeshes.Inconclusive depth
        (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt bits)
        (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt_positive bits)
        parents proper)
      (next : Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.PendingSearch
        parents proper targets target fuel (depth + 1) bits) :
      Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.PendingSearch parents
        proper targets target (fuel + 1) depth bits
  /-- Retain accepted meshes and their failed allowance check before increasing depth and precision. -/ | allowance
    {fuel depth bits : Nat}
      (meshes : CheckedDirectMeshes depth
        (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt bits) parents)
      (observed : CheckedDirectMeshes.attempt depth
        (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt bits)
        (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt_positive bits)
        parents proper = .ok meshes)
      (failure : MeshAllowanceChecks.Inconclusive meshes target targets)
      (next : Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.PendingSearch
        parents proper targets target fuel (depth + 1) (bits + 1)) :
      Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace.PendingSearch parents
        proper targets target (fuel + 1) depth bits

constructive_injectivity PendingSearch

end Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace

end

end
