module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Riemann.Integration.CheckedDirectGeometry
public import Purelib.Riemann.Transport.CheckedDirectGeometryReplay
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Transport.PreparedDeferredRecipeReplay
import Purelib.Riemann.Transport.PreparedDirectRefinementReplay
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Init.Core
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting

section

open Purelib

open Purelib.Data.Rat

open Purelib.Riemann.Integration

open Purelib.Riemann.Transport

section
@[expose] public section

/-!
Disk-backed centring of the original prepared bank spines.  Each callback
receives the complete original-source equation, not just matching numbers.
The explicit stored-spine eliminators retain the owners already computed by
preparation instead of rebuilding their canonical indices during execution.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedMeshReplay

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CheckedDirectMeshes)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Coordinate)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- A retained finite mesh-check result with equality to the sequential checker on the exact parent list.

Both successful meshes and explanatory failures remain tied to the prescribed depth, positive diameter and
parent-properness evidence. -/
abbrev Checked (depth : Nat) (diameter : Fraction.Rational) (positive : 0 < diameter)
    (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents) :=
  {value : Except (CheckedDirectMeshes.Failure depth diameter positive parents)
      (CheckedDirectMeshes depth diameter parents) //
    CheckedDirectMeshes.sequentialAttempt depth diameter positive parents proper = value}

/-- Record an observed head-mesh failure as the exact failure of the whole sequential parent check. -/
def failedHead (depth : Nat) (diameter : Fraction.Rational) (positive : 0 < diameter)
    {parent : CenteredEdge curve source} {remaining : List (CenteredEdge curve source)}
    (proper : AllParentsProper (parent :: remaining))
    (failure : CheckedDirectGeometry.MeshInconclusive parent.edge proper.1 diameter positive depth
      parent.edge.left parent.edge.request.endpoint le_rfl le_rfl proper.1)
    (found : CheckedDirectGeometry.attemptMesh parent.edge proper.1 diameter positive depth
      parent.edge.left parent.edge.request.endpoint le_rfl le_rfl proper.1 = .error failure) :
    Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedMeshReplay.Checked depth diameter positive (parent ::
      remaining) proper := by
  refine ⟨.error (.head proper.1 failure), ?_⟩
  unfold CheckedDirectMeshes.sequentialAttempt
  rw [found]
  rfl

/-- Prepend an observed accepted head mesh to a retained checked tail result.

A failed tail keeps that accepted head in its failure spine; a successful tail extends the complete dependent mesh
family. -/
def acceptedHead (depth : Nat) (diameter : Fraction.Rational) (positive : 0 < diameter)
    {parent : CenteredEdge curve source} {remaining : List (CenteredEdge curve source)}
    (proper : AllParentsProper (parent :: remaining))
    (mesh : CheckedDirectGeometry.Mesh parent.edge diameter depth parent.edge.left parent.edge.request.endpoint)
    (found : CheckedDirectGeometry.attemptMesh parent.edge proper.1 diameter positive depth
      parent.edge.left parent.edge.request.endpoint le_rfl le_rfl proper.1 = .ok mesh)
    (tail : Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedMeshReplay.Checked depth diameter positive
      remaining proper.2) :
    Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedMeshReplay.Checked depth diameter positive (parent ::
      remaining) proper := by
  rcases tail with ⟨value, equal⟩
  cases value with
  | error failure =>
      refine ⟨.error (.tail mesh failure), ?_⟩
      unfold CheckedDirectMeshes.sequentialAttempt
      rw [found]
      unfold CheckedDirectMeshes.prependAttempt
      dsimp only
      rw [equal]
  | ok meshes =>
      refine ⟨.ok (.cons mesh meshes), ?_⟩
      unfold CheckedDirectMeshes.sequentialAttempt
      rw [found]
      unfold CheckedDirectMeshes.prependAttempt
      dsimp only
      rw [equal]

/-- Return the same public accepted meshes or explanatory finite miss as the original four-worker checker, without
rerunning that checker. -/
def finish (depth : Nat) (diameter : Fraction.Rational) (positive : 0 < diameter)
    (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (checked : Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedMeshReplay.Checked depth diameter positive
      parents proper) :
    {value : Except (CheckedDirectMeshes.Inconclusive depth diameter positive parents proper)
      (CheckedDirectMeshes depth diameter parents) //
      CheckedDirectMeshes.attempt depth diameter positive parents proper = value} := by
  rcases checked with ⟨value, equal⟩
  have originalEq := (CheckedDirectMeshes.attemptRaw_eq_sequential depth diameter positive parents proper).trans equal
  cases value with
  | error failure =>
      let report : CheckedDirectMeshes.Inconclusive depth diameter positive parents proper :=
        ⟨depth, rfl, diameter, rfl, parents.length, rfl, failure, failure.completedParents, rfl, originalEq⟩
      exact ⟨.error report, report.attempt_error⟩
  | ok meshes =>
      refine ⟨.ok meshes, ?_⟩
      unfold CheckedDirectMeshes.attempt
      split
      · rename_i other found
        have same := Except.ok.inj (found.symm.trans originalEq)
        cases same
        rfl
      · rename_i failure found
        cases found.symm.trans originalEq

set_option genInjectivity false in
/-- A suspended sequential mesh-check spine retaining every completed head.

The unresolved request is indexed by the exact parent geometry, depth and positive diameter; accepted prefixes keep
their observed checker equalities. -/
inductive Pending (depth : Nat) (diameter : Fraction.Rational) (positive : 0 < diameter) :
    (parents : List (CenteredEdge curve source)) → AllParentsProper parents → Type 2
  /-- The head parent mesh check remains pending at its exact request. -/ | head {parent : CenteredEdge curve source}
    {remaining : List (CenteredEdge curve source)}
      {proper : AllParentsProper (parent :: remaining)}
      (pending : CheckedDirectGeometryReplay.Pending parent.edge proper.1 diameter positive depth
        parent.edge.left parent.edge.request.endpoint le_rfl le_rfl proper.1) :
      Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedMeshReplay.Pending depth diameter positive
        (parent :: remaining) proper
  /-- An accepted head and its observed checker equality precede the retained pending tail. -/ | tail {parent :
    CenteredEdge curve source} {remaining : List (CenteredEdge curve source)}
      {proper : AllParentsProper (parent :: remaining)}
      (accepted : CheckedDirectGeometry.Mesh parent.edge diameter depth parent.edge.left parent.edge.request.endpoint)
      (observed : CheckedDirectGeometry.attemptMesh parent.edge proper.1 diameter positive depth
        parent.edge.left parent.edge.request.endpoint le_rfl le_rfl proper.1 = .ok accepted)
      (pending : Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedMeshReplay.Pending depth diameter
        positive remaining proper.2) :
      Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedMeshReplay.Pending depth diameter positive
        (parent :: remaining) proper

constructive_injectivity Pending

end Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedMeshReplay

end

end
