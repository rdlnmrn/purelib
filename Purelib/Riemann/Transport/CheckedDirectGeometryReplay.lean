module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Replay.PreparedRootStateReplay
public import Purelib.Riemann.Integration.CheckedDirectGeometry
public import Purelib.RootIsolation.SquareRoot.Replay.BoundedPreparedSourceReplay
public import Purelib.RootIsolation.SquareRoot.Replay.PreparedOwnerTransportReplay

@[expose] public section

/-!
Reconstruct the original direct-mesh checker from saved diameter attempts.
Every leaf retains its original parent query owner. Accepted left subtrees
and the first unresolved right subtree identify the exact traversal; a
missing transport or source checkpoint is kept separate from a mesh miss.
-/

namespace Purelib.Riemann.Transport.CheckedDirectGeometryReplay

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (PreparedEdge ParentPosition Coordinate Endpoint Owner)
open Purelib.Riemann.Branches
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.CheckedDirectGeometry (Mesh MeshFailure MeshInconclusive midpoint)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (directRequest)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  (parent : PreparedEdge curve differential)

open Purelib.Data in
/-- Casting a prepared owner along coordinate equality agrees with dependent substitution. -/
public theorem cast_owner {source target : Gaussian.Basic.Canonical}
    (equal : source = target) (owner : Owner source) :
    cast (congrArg Owner equal) owner = equal ▸ owner := by
  cases equal
  rfl

/-- Locate a local interval's left endpoint within the original proper parent segment. -/
def position (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (left right : Endpoint) (lower : parent.left.parameter ≤ left.parameter)
    (upper : right.parameter ≤ parent.request.endpoint.parameter)
    (localProper : left.parameter < right.parameter) : ParentPosition parent left :=
  ParentPosition.ofBetween proper ⟨lower, localProper.le.trans upper⟩

open Purelib.RootIsolation.SquareRoot.Clearance in
open Purelib.RootIsolation.SquareRoot.Replay in
/-- Replay the exact owner query at a retained parent position.

A stationary query preserves the original prepared owner and history. A moving query uses the full finite-state
transport checker and returns either its actual failure or an owner with equality to the original query. -/
def queryOwner (current : Endpoint) (position : ParentPosition parent current) :
    Except (PreparedOwnerTransportReplay.Failure parent.cached.preparedOwner.track.initial
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))
      (PreparedSheetContinuation.transportReserve parent.segment parent.left parent.request))
      {value : Owner (curve.polynomial.eval (parent.segment.pointAt current.parameter)) //
        value = CheckedDirectGeometry.queryOwnerAt parent current position} := by
  cases current with
  | mk parameter inside =>
    cases position with
    | mk fraction fractionInside equal =>
      dsimp only at equal
      subst parameter
      let original := parent.cached.preparedOwner
      let target := curve.polynomial.eval (parent.segment.pointAt
        (PreparedSheetContinuation.parameterAt parent.left parent.request fraction))
      if same : curve.polynomial.eval (parent.segment.pointAt parent.left.parameter) = target then
        refine .ok ⟨cast (congrArg Owner same) original, ?_⟩
        unfold CheckedDirectGeometry.queryOwnerAt PreparedConstantModels.PreparedEdge.directQueryOwner
          ExactQuadraticOwnerClearance.reservedTransport
        rw [dif_pos same]
        exact cast_owner same original
      else
        let restored : PreparedRootStateReplay.Checked _ original.ambient
            (PreparedRootStateReplay.capture original.track.initial) := ⟨original.track.initial, rfl⟩
        match PreparedOwnerTransportReplay.check restored.state target
            (PreparedSheetContinuation.transportReserve parent.segment parent.left parent.request) with
        | .error failure => exact .error failure
        | .ok transport =>
          refine .ok ⟨transport.value, ?_⟩
          unfold CheckedDirectGeometry.queryOwnerAt PreparedConstantModels.PreparedEdge.directQueryOwner
          exact transport.eq_original original restored

/-- The original exact direct-mesh check for a bounded subinterval at the specified depth. -/
def raw (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (diameter : Coordinate) (positive : 0 < diameter) (depth : Nat)
    (left right : Endpoint) (lower : parent.left.parameter ≤ left.parameter)
    (upper : right.parameter ≤ parent.request.endpoint.parameter)
    (localProper : left.parameter < right.parameter) :=
  CheckedDirectGeometry.checkMeshRawExact parent proper diameter positive depth left right lower upper localProper

/-- A retained direct-mesh outcome with its exact original checker equation. -/
abbrev Checked (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (diameter : Coordinate) (positive : 0 < diameter) (depth : Nat)
    (left right : Endpoint) (lower : parent.left.parameter ≤ left.parameter)
    (upper : right.parameter ≤ parent.request.endpoint.parameter)
    (localProper : left.parameter < right.parameter) :=
  {value : Except (MeshFailure parent diameter positive depth left right)
      (Mesh parent diameter depth left right) //
    raw parent proper diameter positive depth left right lower upper localProper = value}

open Purelib.RootIsolation.SquareRoot.Replay in
/-- Reconstruct a checked leaf from its actual query owner and bounded source outcome.

Owner equality ties both accepted leaves and unresolved-source failures to the original parent query, preserving the
selected source certificate. -/
def leaf (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (diameter : Coordinate) (positive : 0 < diameter)
    (left right : Endpoint) (lower : parent.left.parameter ≤ left.parameter)
    (upper : right.parameter ≤ parent.request.endpoint.parameter)
    (localProper : left.parameter < right.parameter)
    (owner : Owner (curve.polynomial.eval (parent.segment.pointAt left.parameter)))
    (ownerEq : owner = CheckedDirectGeometry.queryOwnerAt parent left
      (position parent proper left right lower upper localProper))
    (prepared : BoundedPreparedSourceReplay.Checked parent.segment left owner (directRequest right diameter positive)) :
    Checked parent proper diameter positive 0 left right lower upper localProper := by
  let point := position parent proper left right lower upper localProper
  refine ⟨match prepared.value with
    | .error failure => .error (.unresolved point owner ownerEq failure)
    | .ok accepted => .ok (.leaf ⟨point, owner, ownerEq, positive, localProper.le, accepted⟩ localProper), ?_⟩
  cases ownerEq
  unfold raw
  unfold CheckedDirectGeometry.checkMeshRawExact
  dsimp only [position] at prepared ⊢
  rw [prepared.equation]
  cases prepared.value <;> rfl

/-- Reconstruct the first-subtree failure of the exact ordered mesh traversal. -/
def firstFailed (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (diameter : Coordinate) (positive : 0 < diameter) (depth : Nat)
    (left right : Endpoint) (lower : parent.left.parameter ≤ left.parameter)
    (upper : right.parameter ≤ parent.request.endpoint.parameter)
    (localProper : left.parameter < right.parameter)
    (failure : MeshFailure parent diameter positive depth left (midpoint left right))
    (found : raw parent proper diameter positive depth left (midpoint left right)
      lower ((CheckedDirectGeometry.midpoint_lt_right localProper).le.trans upper)
      (CheckedDirectGeometry.left_lt_midpoint localProper) = .error failure) :
    Checked parent proper diameter positive (depth + 1) left right lower upper localProper := by
  refine ⟨.error (.first failure), ?_⟩
  unfold raw
  unfold CheckedDirectGeometry.checkMeshRawExact
  dsimp only [raw] at found
  dsimp only
  rw [found]

/-- Attach a checked right subtree after an actual accepted left subtree.

The retained left mesh and checker equation preserve the original traversal. A right failure records that mesh; success
joins the two original submeshes. -/
def second (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (diameter : Coordinate) (positive : 0 < diameter) (depth : Nat)
    (left right : Endpoint) (lower : parent.left.parameter ≤ left.parameter)
    (upper : right.parameter ≤ parent.request.endpoint.parameter)
    (localProper : left.parameter < right.parameter)
    (first : Mesh parent diameter depth left (midpoint left right))
    (found : raw parent proper diameter positive depth left (midpoint left right)
      lower ((CheckedDirectGeometry.midpoint_lt_right localProper).le.trans upper)
      (CheckedDirectGeometry.left_lt_midpoint localProper) = .ok first)
    (tail : Checked parent proper diameter positive depth (midpoint left right) right
      (lower.trans (CheckedDirectGeometry.left_lt_midpoint localProper).le) upper
      (CheckedDirectGeometry.midpoint_lt_right localProper)) :
    Checked parent proper diameter positive (depth + 1) left right lower upper localProper := by
  rcases tail with ⟨tail, tailEq⟩
  cases tail with
  | error failed =>
      refine ⟨.error (.second first failed), ?_⟩
      unfold raw
      unfold CheckedDirectGeometry.checkMeshRawExact
      dsimp only [raw] at found tailEq
      dsimp only
      rw [found, tailEq]
  | ok last =>
      refine ⟨.ok (.split first last), ?_⟩
      unfold raw
      unfold CheckedDirectGeometry.checkMeshRawExact
      dsimp only [raw] at found tailEq
      dsimp only
      rw [found, tailEq]

/-- Wrap a checked raw mesh outcome as the original finite geometry attempt.

An inconclusive result retains the requested depth, diameter, endpoints and actual failure with their defining
equations; success returns the retained mesh. -/
def finish (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (diameter : Coordinate) (positive : 0 < diameter) (depth : Nat)
    (left right : Endpoint) (lower : parent.left.parameter ≤ left.parameter)
    (upper : right.parameter ≤ parent.request.endpoint.parameter)
    (localProper : left.parameter < right.parameter)
    (checked : Checked parent proper diameter positive depth left right lower upper localProper) :
    {value : Except (MeshInconclusive parent proper diameter positive depth left right lower upper localProper)
        (Mesh parent diameter depth left right) //
      CheckedDirectGeometry.attemptMesh parent proper diameter positive depth left right lower upper localProper =
        value} := by
  rcases checked with ⟨value, equal⟩
  cases value with
  | error failure =>
      let report : MeshInconclusive parent proper diameter positive depth left right lower upper localProper :=
        ⟨depth, rfl, diameter, rfl, left, rfl, right, rfl, failure, equal⟩
      exact ⟨.error report, report.attempt_error⟩
  | ok mesh =>
      refine ⟨.ok mesh, ?_⟩
      unfold CheckedDirectGeometry.attemptMesh
      dsimp only [raw] at equal
      split
      · rename_i other found
        have same : other = mesh := Except.ok.inj (found.symm.trans equal)
        cases same
        rfl
      · rename_i failure found
        cases found.symm.trans equal

open Purelib.RootIsolation.SquareRoot.Replay in
set_option genInjectivity false in
/-- An unfinished direct-mesh replay retaining the exact unresolved traversal position.

A transport checkpoint or a pending child remains distinct from a certified failure of the original mesh checker.
Accepted left subtrees are retained before unresolved right work. -/
inductive Pending (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (diameter : Coordinate) (positive : 0 < diameter) :
    (depth : Nat) → (left right : Endpoint) →
    parent.left.parameter ≤ left.parameter →
    right.parameter ≤ parent.request.endpoint.parameter →
    left.parameter < right.parameter → Type
  /-- A leaf whose original owner-query replay returned the retained transport failure. -/ | transport {left right :
    Endpoint} {lower upper localProper}
      (failure : PreparedOwnerTransportReplay.Failure parent.cached.preparedOwner.track.initial
        (curve.polynomial.eval (parent.segment.pointAt left.parameter))
        (PreparedSheetContinuation.transportReserve parent.segment parent.left parent.request))
      (observed : queryOwner parent left (position parent proper left right lower upper localProper) =
        .error failure) : Pending proper diameter positive 0 left right lower upper localProper
  /-- An unresolved first subtree of the original ordered mesh traversal. -/ | first {depth : Nat} {left right :
    Endpoint} {lower upper localProper}
      (pending : Pending proper diameter positive depth left (midpoint left right)
        lower ((CheckedDirectGeometry.midpoint_lt_right localProper).le.trans upper)
        (CheckedDirectGeometry.left_lt_midpoint localProper)) :
      Pending proper diameter positive (depth + 1) left right lower upper localProper
  /-- An unresolved second subtree following an actual accepted first mesh and its checker equation. -/ | second {depth
    : Nat} {left right : Endpoint} {lower upper localProper}
      (accepted : Mesh parent diameter depth left (midpoint left right))
      (observed : raw parent proper diameter positive depth left (midpoint left right)
        lower ((CheckedDirectGeometry.midpoint_lt_right localProper).le.trans upper)
        (CheckedDirectGeometry.left_lt_midpoint localProper) = .ok accepted)
      (pending : Pending proper diameter positive depth (midpoint left right) right
        (lower.trans (CheckedDirectGeometry.left_lt_midpoint localProper).le) upper
        (CheckedDirectGeometry.midpoint_lt_right localProper)) :
      Pending proper diameter positive (depth + 1) left right lower upper localProper

constructive_injectivity Pending

end Purelib.Riemann.Transport.CheckedDirectGeometryReplay
