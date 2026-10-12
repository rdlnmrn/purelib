module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
public import Purelib.Riemann.Integration.PreparedEdgeRecasting
public import Purelib.Riemann.Readings.BoundedPreparedSource
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.Track.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Checked cached geometry for direct dyadic refinements

Only a complete certified mesh is returned.  Preparation, owner occurrence,
coverage and actual allowance are checked before coefficient centres are
requested; finite differential families reuse the same accepted geometry.
-/

namespace Purelib.Riemann.Integration.CheckedDirectGeometry

open Purelib.Data.List

open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation
open Purelib.Riemann.Readings
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (PreparedEdge CenteredEdge ParentPosition)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (directRequest)

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- Transport the parent's actual direct query owner to the retained endpoint's exact radicand.

The parent-position equation identifies the affine query parameter with the original endpoint, preserving the query
fraction and its bounds. -/
@[expose, irreducible] def queryOwnerAt {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : PreparedEdge curve differential)
    (current : Endpoint) (position : ParentPosition parent current) :
    Owner (curve.polynomial.eval (parent.segment.pointAt current.parameter)) := by
  rw [← position.parameter_eq]
  exact parent.directQueryOwner position.fraction position.inside

set_option genInjectivity false in
open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- A certified direct child interval retaining its actual parent query owner and prepared source cache.

The record keeps the exact parent position and owner equation, positive diameter target, ordered endpoints and
bounded-preparation success certificate. -/
structure Leaf {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : PreparedEdge curve differential)
    (left right : Endpoint) (diameter : Coordinate) where
  /-- The exact parent query fraction representing the original left endpoint. -/ position : ParentPosition parent left
  /-- The actual parent query owner at the original left endpoint's radicand. -/ owner : Owner (curve.polynomial.eval
    (parent.segment.pointAt left.parameter))
  /-- The retained owner is exactly the transported parent query owner at the retained position. -/ owner_eq : owner =
    queryOwnerAt parent left position
  /-- The retained root-diameter target is strictly positive. -/ positive : 0 < diameter
  /-- The original leaf endpoints are ordered. -/ ordered : left.parameter ≤ right.parameter
  /-- Bounded preparation succeeded for the exact retained owner and direct endpoint request. -/ prepared :
    BoundedPreparedSource.Accepted parent.segment left owner
    (directRequest right diameter positive)

constructive_injectivity Leaf

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- Construct the child edge from the leaf's original query owner and accepted prepared cache.

The parent's segment and sheet are retained, and the accepted cache equality transports the existing clearance bound to
canonical preparation. -/
@[expose] def Leaf.edge {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {parent : PreparedEdge curve differential}
    {left right : Endpoint} {diameter : Coordinate}
    (leaf : Leaf parent left right diameter) : PreparedEdge curve differential where
  ambient := parent.ambient
  start := parent.start
  finish := parent.finish
  segment := parent.segment
  within := parent.within
  left := left
  owner := leaf.owner
  request := directRequest right diameter leaf.positive
  cached := leaf.prepared.cached
  ordered := leaf.ordered
  small := by
    have small := leaf.prepared.small
    rw [leaf.prepared.cached.preparedOwner_eq] at small
    exact small
  sheet := parent.sheet

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Integration in
/-- Equip the leaf's exact prepared child edge with its canonical center state. -/
@[expose] def Leaf.centered {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {parent : PreparedEdge curve differential}
    {left right : Endpoint} {diameter : Coordinate}
    (leaf : Leaf parent left right diameter) : CenteredEdge curve differential :=
  { edge := leaf.edge
    center := PreparedConstantModels.PreparedEdge.CenterState.canonical leaf.edge }

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.RootContinuation in
/-- The transported query owner's root name is exactly the original parent's name at the retained fraction. -/
theorem queryOwnerAt_rootName {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : PreparedEdge curve differential)
    (current : Endpoint) (position : ParentPosition parent current) :
    SquareRootTrackEquivalence.ownerRootName
      (parent.segment.pointAt_eval_ne_zero current.parameter current.inside)
      (queryOwnerAt parent current position) =
        parent.rootName position.fraction position.inside := by
  rw [parent.rootName_eq_directQueryOwnerRootName]
  cases current with
  | mk parameter inside =>
      cases position with
      | mk fraction fractionInside equal =>
          dsimp only at equal
          subst parameter
          unfold queryOwnerAt
          rfl

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Integration in
/-- Relate the leaf's actual centered child to the retained centered parent.

The original parent-position equation identifies the coordinates; the exact query-owner equation and the child's
base-root comparison preserve root identity. -/
@[expose] def Leaf.rootChildAt {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : CenteredEdge curve differential)
    {left right : Endpoint} {diameter : Coordinate}
    (leaf : Leaf parent.edge left right diameter) :
    PreparedSubdivisionModelCore.RootChildAt parent leaf.centered := by
  refine
    { fraction := leaf.position.fraction
      inside := leaf.position.inside
      point_eq := ?_
      rootEquivalent := ?_ }
  · have parentPoint := pointAt_parameterAt parent.edge.segment parent.edge.within
        parent.edge.left parent.edge.request leaf.position.fraction
    have childPoint := pointAt_parameterAt parent.edge.segment parent.edge.within
        left (directRequest right diameter leaf.positive) 0
    have coordinate := congrArg parent.edge.segment.pointAt leaf.position.parameter_eq
    exact parentPoint.symm.trans (coordinate.trans (by
      change parent.edge.segment.pointAt left.parameter =
        (PreparedModels.edge curve parent.edge.segment
          parent.edge.within left (directRequest right diameter leaf.positive)).pointAt 0
      unfold PreparedModels.edge
      simpa only [parameterAt_zero] using childPoint))
  · have equivalent := leaf.edge.ownerRootEquivalent_baseQuery
    change NamedEquivalent
      (parent.edge.rootName leaf.position.fraction leaf.position.inside)
      (leaf.edge.rootName 0 leaf.edge.baseInside)
    rw [← queryOwnerAt_rootName parent.edge left leaf.position]
    rw [← leaf.owner_eq]
    exact equivalent

open Purelib.Riemann.Branches in
/-- The rational midpoint of the original bounded endpoint parameters, with its unit-interval certificate. -/
@[expose] def midpoint (left right : Endpoint) : Endpoint :=
  ⟨ClearSheetContinuation.midpoint left.parameter right.parameter,
    ClearSheetContinuation.midpoint_inside left.inside right.inside⟩

section
open Purelib.Data.Rat
open Purelib.Riemann.Branches
/-- A strictly ordered rational interval has its midpoint strictly above its left endpoint. -/
theorem left_lt_midpoint {left right : Coordinate} (proper : left < right) :
    left < ClearSheetContinuation.midpoint left right := by
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := (2 : Coordinate))
  · calc
      left * 2 = left + left := by ring1
      _ < left + right := Fraction.Order.Arithmetic.add_lt_add_left_direct proper left
      _ = ClearSheetContinuation.midpoint left right * 2 := by
        rw [ClearSheetContinuation.midpoint,
          Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
  · decide

/-- A strictly ordered rational interval has its midpoint strictly below its right endpoint. -/
theorem midpoint_lt_right {left right : Coordinate} (proper : left < right) :
    ClearSheetContinuation.midpoint left right < right := by
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := (2 : Coordinate))
  · calc
      ClearSheetContinuation.midpoint left right * 2 = left + right := by
        rw [ClearSheetContinuation.midpoint,
          Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
      _ < right + right := Fraction.Order.Arithmetic.add_lt_add_right_direct proper right
      _ = right * 2 := by ring1
  · decide

end

set_option genInjectivity false in
open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- A complete dyadic mesh of certified direct child leaves at the retained depth and endpoints.

Each split retains its actual left and right midpoint submeshes; each leaf retains a successful bounded preparation and
strict endpoint order. -/
inductive Mesh {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : PreparedEdge curve differential)
    (diameter : Coordinate) : Nat → Endpoint → Endpoint → Type
  /-- Retain a certified direct leaf and its strict endpoint ordering at depth zero. -/ | leaf {left right : Endpoint}
    (data : Leaf parent left right diameter)
      (proper : left.parameter < right.parameter) :
      Mesh parent diameter 0 left right
  /-- Retain the exact left and right midpoint submeshes of the preceding depth. -/ | split {depth : Nat} {left right :
    Endpoint}
      (first : Mesh parent diameter depth left (midpoint left right))
      (second : Mesh parent diameter depth (midpoint left right) right) :
      Mesh parent diameter (depth + 1) left right

constructive_injectivity Mesh

set_option genInjectivity false in
open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- The precise unresolved branch of the finite direct mesh check.

A leaf retains its actual query owner and inconclusive preparation report. A right-branch failure also retains the
already accepted left submesh. -/
inductive MeshFailure {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : PreparedEdge curve differential)
    (diameter : Coordinate) (positive : 0 < diameter) : Nat → Endpoint → Endpoint → Type
  /-- Retain the actual leaf query position and owner together with its inconclusive bounded-preparation report. -/ |
    unresolved {left right : Endpoint}
      (position : ParentPosition parent left)
      (owner : Owner (curve.polynomial.eval (parent.segment.pointAt left.parameter)))
      (owner_eq : owner = queryOwnerAt parent left position)
      (report : BoundedPreparedSource.Inconclusive parent.segment left owner
        (directRequest right diameter positive)) :
      MeshFailure parent diameter positive 0 left right
  /-- Retain the unresolved first midpoint submesh. -/ | first {depth : Nat} {left right : Endpoint}
      (failure : MeshFailure parent diameter positive depth left (midpoint left right)) :
      MeshFailure parent diameter positive (depth + 1) left right
  /-- Retain the accepted first submesh and the unresolved second midpoint submesh. -/ | second {depth : Nat} {left
    right : Endpoint}
      (accepted : Mesh parent diameter depth left (midpoint left right))
      (failure : MeshFailure parent diameter positive depth (midpoint left right) right) :
      MeshFailure parent diameter positive (depth + 1) left right

constructive_injectivity MeshFailure

section
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
/-- Check the exact finite dyadic mesh from left to right using bounded source preparation at each leaf.

The recursion preserves the original endpoints and parent query owners. An unresolved branch returns its actual
preparation report and any accepted left submesh. -/
private def checkMeshRaw {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : PreparedEdge curve differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (diameter : Coordinate) (positive : 0 < diameter) :
    (depth : Nat) → (left right : Endpoint) →
    parent.left.parameter ≤ left.parameter →
    right.parameter ≤ parent.request.endpoint.parameter →
    left.parameter < right.parameter →
      Except (MeshFailure parent diameter positive depth left right)
        (Mesh parent diameter depth left right)
  | 0, left, right, lower, upper, localProper =>
      let position := ParentPosition.ofBetween proper ⟨lower, localProper.le.trans upper⟩
      let owner := queryOwnerAt parent left position
      match BoundedPreparedSource.check parent.segment left owner
          (directRequest right diameter positive) with
      | .error report => .error (.unresolved position owner rfl report)
      | .ok prepared => .ok (.leaf
          { position := position
            owner := owner
            owner_eq := rfl
            positive := positive
            ordered := localProper.le
            prepared := prepared } localProper)
  | depth + 1, left, right, lower, upper, localProper =>
      let middle := midpoint left right
      have firstProper : left.parameter < middle.parameter := left_lt_midpoint localProper
      have secondProper : middle.parameter < right.parameter := midpoint_lt_right localProper
      match checkMeshRaw parent proper diameter positive depth left middle
          lower (secondProper.le.trans upper) firstProper with
      | .error failure => .error (.first failure)
      | .ok first =>
          match checkMeshRaw parent proper diameter positive depth middle right
              (lower.trans firstProper.le) upper secondProper with
          | .error failure => .error (.second first failure)
          | .ok second => .ok (.split first second)

/-- Check the exact finite dyadic mesh from left to right with branch-specific retained results.

Every leaf uses its original parent position and query owner; a second-branch miss retains the successful first submesh
along with the unresolved branch. -/
@[expose] def checkMeshRawExact {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : PreparedEdge curve differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (diameter : Coordinate) (positive : 0 < diameter) :
    (depth : Nat) → (left right : Endpoint) →
    parent.left.parameter ≤ left.parameter →
    right.parameter ≤ parent.request.endpoint.parameter →
    left.parameter < right.parameter →
      Except (MeshFailure parent diameter positive depth left right)
        (Mesh parent diameter depth left right)
  | 0, left, right, lower, upper, localProper =>
      let position := ParentPosition.ofBetween proper ⟨lower, localProper.le.trans upper⟩
      let owner := queryOwnerAt parent left position
      match BoundedPreparedSource.check parent.segment left owner
          (directRequest right diameter positive) with
      | .error report => .error (.unresolved position owner rfl report)
      | .ok prepared => .ok (.leaf
          { position := position
            owner := owner
            owner_eq := rfl
            positive := positive
            ordered := localProper.le
            prepared := prepared } localProper)
  | depth + 1, left, right, lower, upper, localProper =>
      let middle := midpoint left right
      have firstProper : left.parameter < middle.parameter := left_lt_midpoint localProper
      have secondProper : middle.parameter < right.parameter := midpoint_lt_right localProper
      match checkMeshRawExact parent proper diameter positive depth left middle
          lower (secondProper.le.trans upper) firstProper with
      | .error failure => .error (.first failure)
      | .ok first =>
          match checkMeshRawExact parent proper diameter positive depth middle right
              (lower.trans firstProper.le) upper secondProper with
          | .error failure => .error (.second first failure)
          | .ok second => .ok (.split first second)

end

set_option genInjectivity false in
open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- An unresolved mesh attempt bound to its exact depth, diameter and endpoint inputs.

The retained failure includes partial successes, and the observed equation identifies it with the actual raw checker
result. -/
structure MeshInconclusive {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : PreparedEdge curve differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (diameter : Coordinate) (positive : 0 < diameter) (depth : Nat)
    (left right : Endpoint) (lower : parent.left.parameter ≤ left.parameter)
    (upper : right.parameter ≤ parent.request.endpoint.parameter)
    (localProper : left.parameter < right.parameter) where
  /-- The actual depth tested by this finite mesh attempt. -/ attemptedDepth : Nat
  /-- The retained depth is exactly the input depth. -/ attemptedDepth_eq : attemptedDepth = depth
  /-- The actual root-diameter target tested by this attempt. -/ requestedDiameter : Coordinate
  /-- The retained diameter is exactly the input target. -/ requestedDiameter_eq : requestedDiameter = diameter
  /-- The original left endpoint retained by the attempt. -/ start : Endpoint
  /-- The retained start is exactly the original left endpoint. -/ start_eq : start = left
  /-- The original right endpoint retained by the attempt. -/ finish : Endpoint
  /-- The retained finish is exactly the original right endpoint. -/ finish_eq : finish = right
  /-- The exact unresolved branch, including any already accepted left submeshes. -/ failure : MeshFailure parent
    diameter positive depth left right
  /-- The original raw checker returned this exact retained failure at the input depth, diameter and endpoints. -/
    observed : checkMeshRawExact parent proper diameter positive depth left right
    lower upper localProper = .error failure

constructive_injectivity MeshInconclusive

section
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
/-- Run the finite mesh checker and retain either the exact mesh or its authenticated inconclusive report.

The report records the attempted depth, diameter and endpoints together with the actual error equation and partial mesh
results. -/
@[expose] def attemptMesh {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : PreparedEdge curve differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (diameter : Coordinate) (positive : 0 < diameter) (depth : Nat)
    (left right : Endpoint) (lower : parent.left.parameter ≤ left.parameter)
    (upper : right.parameter ≤ parent.request.endpoint.parameter)
    (localProper : left.parameter < right.parameter) :
    Except (MeshInconclusive parent proper diameter positive depth left right lower upper localProper)
      (Mesh parent diameter depth left right) :=
  match observed : checkMeshRawExact parent proper diameter positive depth left right
      lower upper localProper with
  | .ok mesh => .ok mesh
  | .error failure => .error
      { attemptedDepth := depth, attemptedDepth_eq := rfl
        requestedDiameter := diameter, requestedDiameter_eq := rfl
        start := left, start_eq := rfl, finish := right, finish_eq := rfl
        failure := failure, observed := observed }

/-- The retained inconclusive report is exactly the result returned by the original mesh attempt. -/
theorem MeshInconclusive.attempt_error
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Basic.Differential
      genus}
    {parent : PreparedEdge curve differential}
    {proper : parent.left.parameter < parent.request.endpoint.parameter}
    {diameter : Coordinate} {positive : 0 < diameter} {depth : Nat}
    {left right : Endpoint} {lower : parent.left.parameter ≤ left.parameter}
    {upper : right.parameter ≤ parent.request.endpoint.parameter}
    {localProper : left.parameter < right.parameter}
    (report : MeshInconclusive parent proper diameter positive depth left right lower upper localProper) :
    attemptMesh parent proper diameter positive depth left right lower upper localProper = .error report := by
  cases report with
  | mk attemptedDepth depthEq requestedDiameter diameterEq start startEq finish finishEq failure observed =>
      cases depthEq
      cases diameterEq
      cases startEq
      cases finishEq
      unfold attemptMesh
      split
      · rename_i mesh found
        have impossible := found.symm.trans observed
        cases impossible
      · rename_i other found
        have equal : other = failure := Except.error.inj (found.symm.trans observed)
        cases equal
        rfl

/-- Read the original prepared leaf edges in left-to-right mesh order. -/
@[expose] def Mesh.edges {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {parent : PreparedEdge curve differential}
    {diameter : Coordinate} : {depth : Nat} → {left right : Endpoint} →
    Mesh parent diameter depth left right → List (PreparedEdge curve differential)
  | _, _, _, .leaf data _ => [data.edge]
  | _, _, _, .split first second => first.edges ++ second.edges

/-- Read the canonical centered leaf edges in left-to-right mesh order. -/
@[expose] def Mesh.children {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {parent : PreparedEdge curve differential}
    {diameter : Coordinate} : {depth : Nat} → {left right : Endpoint} →
    Mesh parent diameter depth left right → List (CenteredEdge curve differential)
  | _, _, _, .leaf data _ => [data.centered]
  | _, _, _, .split first second => first.children ++ second.children

/-- A complete checked mesh at depth `depth` contains exactly `2 ^ depth` centered children.

Each split concatenates the children of its two preceding-depth submeshes.
The two counts add to the next dyadic power, with each leaf contributing one. -/
theorem Mesh.childCount {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {parent : PreparedEdge curve differential}
    {diameter : Coordinate} {depth : Nat} {left right : Endpoint}
    (mesh : Mesh parent diameter depth left right) : mesh.children.length = 2 ^ depth := by
  induction mesh with
  | leaf => rfl
  | @split depth left right first second ihFirst ihSecond =>
      simp only [children, Append.length_append, ihFirst, ihSecond, pow_succ]
      omega

/-- Forgetting the centers recovers the exact original prepared leaf-edge list.

A centered leaf contains its original prepared edge. Mapping the edge
projection distributes over the retained left-to-right split concatenation. -/
theorem Mesh.children_edges {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {parent : PreparedEdge curve differential}
    {diameter : Coordinate} {depth : Nat} {left right : Endpoint}
    (mesh : Mesh parent diameter depth left right) :
    mesh.children.map (·.edge) = mesh.edges := by
  induction mesh with
  | leaf => rfl
  | split first second ihFirst ihSecond =>
      rw [children, edges, Map.map_append, ihFirst, ihSecond]

open Purelib.Data.Rat in
/-- Sum each original leaf's point-movement weight times sixteen model-error allowances.

The sum uses the actual ordered prepared leaf edges without changing their cached owners or geometry. -/
@[expose] def Mesh.weightedAllowance {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {parent : PreparedEdge curve differential}
    {diameter : Coordinate} {depth : Nat} {left right : Endpoint}
    (mesh : Mesh parent diameter depth left right) : Fraction.Rational :=
  mesh.edges.foldr (fun edge total =>
    edge.pointMovement * (16 * edge.modelErrorAllowance) + total) 0

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
/-- The direct leaf allowance sum equals the centered child path's total weighted allowance. -/
theorem Mesh.weightedAllowance_eq {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {parent : PreparedEdge curve differential}
    {diameter : Coordinate} {depth : Nat} {left right : Endpoint}
    (mesh : Mesh parent diameter depth left right) :
    mesh.weightedAllowance =
      (Basic.PathModel.mk
        (mesh.children.map PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance := by
  rw [weightedAllowance, ← mesh.children_edges]
  generalize mesh.children = children
  induction children with
  | nil => rfl
  | cons child rest ih =>
      have head : child.model.weightedAllowance =
          child.edge.pointMovement * (16 * child.edge.modelErrorAllowance) := by
        unfold PreparedSubdivisionModelCore.CenteredEdge.model
          Basic.CellModel.weightedAllowance
          Basic.CellModel.displacement
          PreparedConstantModels.PreparedEdge.centeredModel
          PreparedConstantModels.PreparedEdge.pointMovement
        rw [Norm.Basic.normSq_eq_canonical]
      simpa only [List.map_cons, List.foldr_cons,
        Basic.PathModel.totalWeightedAllowance, head] using
        congrArg (fun total => child.edge.pointMovement *
          (16 * child.edge.modelErrorAllowance) + total) ih

section
open Purelib.Riemann.Integration
/-- Recast the certified leaf to a target differential, retaining its original query position, owner and accepted
preparation.

The owner equality is transported along the unchanged parent geometry; diameter, endpoint order and cached preparation
remain the original data. -/
@[expose] def Leaf.recast {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {parent : PreparedEdge curve source}
    {left right : Endpoint} {diameter : Coordinate}
    (target : Basic.Differential genus) (leaf : Leaf parent left right diameter) :
    Leaf (PreparedEdgeRecasting.recastPreparedEdge target parent)
      left right diameter where
  position :=
    { fraction := leaf.position.fraction
      inside := leaf.position.inside
      parameter_eq := leaf.position.parameter_eq }
  owner := leaf.owner
  owner_eq := by
    rw [leaf.owner_eq]
    unfold queryOwnerAt
    rfl
  positive := leaf.positive
  ordered := leaf.ordered
  prepared := leaf.prepared

/-- Reading a recast leaf edge is exactly recasting its original prepared edge. -/
theorem Leaf.recast_edge {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {parent : PreparedEdge curve source}
    {left right : Endpoint} {diameter : Coordinate}
    (target : Basic.Differential genus) (leaf : Leaf parent left right diameter) :
    (leaf.recast target).edge =
      PreparedEdgeRecasting.recastPreparedEdge target leaf.edge := rfl

end

section
open Purelib.Riemann.Integration
/-- Recast every retained leaf to the target differential while preserving the exact dyadic tree and endpoint indices.

The recursion retains both original midpoint submeshes and each original leaf preparation certificate. -/
@[expose] def Mesh.recast {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {parent : PreparedEdge curve source}
    {diameter : Coordinate} (target : Basic.Differential genus) :
    {depth : Nat} → {left right : Endpoint} → Mesh parent diameter depth left right →
      Mesh (PreparedEdgeRecasting.recastPreparedEdge target parent)
        diameter depth left right
  | _, _, _, .leaf data proper => .leaf (data.recast target) proper
  | _, _, _, .split first second => .split (first.recast target) (second.recast target)

/-- Reading recast mesh children equals recasting the original ordered centered child list.

Recasting retains the original split tree. Mapping the recast operation over
each concatenated child list gives the same left-to-right centered leaves. -/
theorem Mesh.recast_children {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {parent : PreparedEdge curve source}
    {diameter : Coordinate} {depth : Nat} {left right : Endpoint}
    (target : Basic.Differential genus) (mesh : Mesh parent diameter depth left right) :
    (mesh.recast target).children = mesh.children.map
      (PreparedEdgeRecasting.recastCenteredEdge target) := by
  induction mesh with
  | leaf => rfl
  | split first second ihFirst ihSecond =>
      change (first.recast target).children ++ (second.recast target).children =
        (first.children ++ second.children).map _
      rw [Map.map_append, ihFirst, ihSecond]

end

open Purelib.Data.Rat in
/-- The actual weighted allowance of the mesh recast to the target differential. -/
@[expose] def Mesh.weightedAllowanceFor {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {parent : PreparedEdge curve source}
    {diameter : Coordinate} {depth : Nat} {left right : Endpoint}
    (target : Basic.Differential genus) (mesh : Mesh parent diameter depth left right) : Fraction.Rational :=
  (mesh.recast target).weightedAllowance

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
/-- The target allowance equals the total weighted allowance of the exact recast centered child models. -/
theorem Mesh.weightedAllowanceFor_eq {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {parent : PreparedEdge curve source}
    {diameter : Coordinate} {depth : Nat} {left right : Endpoint}
    (target : Basic.Differential genus) (mesh : Mesh parent diameter depth left right) :
    mesh.weightedAllowanceFor target =
      (Basic.PathModel.mk
        ((mesh.children.map
          (PreparedEdgeRecasting.recastCenteredEdge target)).map
            PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance := by
  rw [weightedAllowanceFor, (mesh.recast target).weightedAllowance_eq,
    mesh.recast_children target]

end

end Purelib.Riemann.Integration.CheckedDirectGeometry
