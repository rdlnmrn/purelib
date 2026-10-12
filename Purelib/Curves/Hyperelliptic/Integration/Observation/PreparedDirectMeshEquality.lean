module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.CheckedDirectGeometry
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Readings.BoundedPreparedSource
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedDirectMeshEquality
open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Branches.PreparedSheetContinuation
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (PreparedEdge ParentPosition)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Coordinate Endpoint)
open Purelib.Riemann.Integration.CheckedDirectGeometry (Leaf Mesh)
open Purelib.Riemann.Branches
open Purelib.Riemann.Readings
open Purelib.Riemann.Integration
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- A proper prepared parent edge has a unique retained position at a fixed endpoint.

Strict increase of the parent parameter makes its affine position fraction unique; the endpoint indices then identify
the full position record. -/
theorem position_eq {parent : PreparedSubdivisionModelCore.PreparedEdge curve differential} {current :
  PreparedSheetContinuation.Endpoint}
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (first second : PreparedSubdivisionModelCore.ParentPosition parent current) : first = second := by
  have parameters := first.parameter_eq.trans second.parameter_eq.symm
  rw [PreparedSheetContinuation.parameterAt_eq_affine,
    PreparedSheetContinuation.parameterAt_eq_affine] at parameters
  have products : first.fraction * (parent.request.endpoint.parameter - parent.left.parameter) =
      second.fraction * (parent.request.endpoint.parameter - parent.left.parameter) := by
    calc
      _ = (parent.left.parameter + first.fraction *
          (parent.request.endpoint.parameter - parent.left.parameter)) - parent.left.parameter := by ring1
      _ = (parent.left.parameter + second.fraction *
          (parent.request.endpoint.parameter - parent.left.parameter)) - parent.left.parameter :=
        congrArg (fun value => value - parent.left.parameter) parameters
      _ = _ := by ring1
  have fractions : first.fraction = second.fraction :=
    Fraction.Field.mul_right_cancel_of_ne (Fraction.Order.Arithmetic.sub_pos_direct proper).ne' products
  cases first
  cases second
  cases fractions
  rfl

/-- Accepted prepared-source certificates for the same exact request are equal.

Their retained cached owners agree with the same canonical owner, which identifies the complete dependent records. -/
theorem accepted_eq {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient
  : Rational.Box}
    {start finish : Data.Gaussian.Basic.Canonical}
    {segment : ClearPath.ClearSegment polynomial ambient start finish}
    {current : PreparedSheetContinuation.Endpoint} {owner : PreparedSheetContinuation.Owner (polynomial.eval
      (segment.pointAt current.parameter))}
    {request : PreparedSheetContinuation.StepRequest}
    (first second : BoundedPreparedSource.Accepted segment current owner request) : first = second := by
  have same := first.cached.eq_canonical.trans second.cached.eq_canonical.symm
  cases first
  cases second
  cases same
  rfl

/-- A proper parent edge has a unique checked direct leaf at the fixed endpoints and diameter. -/
theorem leaf_eq {parent : PreparedSubdivisionModelCore.PreparedEdge curve differential} {left right :
  PreparedSheetContinuation.Endpoint} {diameter : PreparedSheetContinuation.Coordinate}
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (first second : CheckedDirectGeometry.Leaf parent left right diameter) : first = second := by
  cases first with
  | mk firstPosition firstOwner firstEq firstPositive firstOrdered firstPrepared =>
    cases second with
    | mk secondPosition secondOwner secondEq secondPositive secondOrdered secondPrepared =>
      have positions := Curves.Hyperelliptic.Integration.Observation.PreparedDirectMeshEquality.position_eq proper
        firstPosition secondPosition
      cases positions
      cases firstEq
      cases secondEq
      have prepared := Curves.Hyperelliptic.Integration.Observation.PreparedDirectMeshEquality.accepted_eq firstPrepared
        secondPrepared
      cases prepared
      rfl

/-- Equal-depth checked direct meshes retain the same full dependent records.

The comparison eliminates each mesh at its original depth. Unequal depths
are rejected directly by natural-constructor disjointness, while equal split
depths compare their actual midpoint submeshes recursively. -/
private theorem mesh_heq {parent : PreparedSubdivisionModelCore.PreparedEdge curve differential}
    {diameter : PreparedSheetContinuation.Coordinate} {firstDepth secondDepth : Nat}
    {left right : PreparedSheetContinuation.Endpoint}
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (first : CheckedDirectGeometry.Mesh parent diameter firstDepth left right)
    (second : CheckedDirectGeometry.Mesh parent diameter secondDepth left right)
    (depths : firstDepth = secondDepth) : HEq first second := by
  induction first generalizing secondDepth with
  | leaf data localProper =>
      cases second with
      | leaf other _ =>
          have equal := leaf_eq proper data other
          cases equal
          exact HEq.rfl
      | split otherFirst otherLast => exact Nat.noConfusion depths
  | split first last firstIH lastIH =>
      cases second with
      | leaf other _ => exact Nat.noConfusion depths
      | split otherFirst otherLast =>
          have sameDepth := Nat.noConfusion depths (fun same => same)
          cases sameDepth
          have sameFirst := eq_of_heq (firstIH otherFirst rfl)
          have sameLast := eq_of_heq (lastIH otherLast rfl)
          cases sameFirst
          cases sameLast
          exact HEq.rfl

/-- Checked direct meshes of the same depth, diameter and endpoints are equal for a proper parent edge.

Each leaf has the unique retained parent position and preparation certificate;
each split compares the original left and right midpoint submeshes. -/
theorem mesh_eq {parent : PreparedSubdivisionModelCore.PreparedEdge curve differential} {left right :
  PreparedSheetContinuation.Endpoint} {diameter : PreparedSheetContinuation.Coordinate}
    {depth : Nat} (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (first second : CheckedDirectGeometry.Mesh parent diameter depth left right) : first = second :=
  eq_of_heq (mesh_heq proper first second rfl)

/-- Every checked direct mesh with the prescribed depth and diameter equals the computed uniform mesh. -/
theorem uniform_eq {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential}
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    {diameter : PreparedSheetContinuation.Coordinate} (positive : 0 < diameter) {depth : Nat}
    (enough : Subdivision.sufficientDyadicDepth
      parent.edge.segment parent.edge.left parent.edge.request.endpoint diameter ≤ depth)
    (mesh : CheckedDirectGeometry.Mesh parent.edge diameter depth parent.edge.left parent.edge.request.endpoint) :
    mesh = PreparedDirectDyadicRefinements.uniformParentMesh parent proper diameter positive depth enough :=
  Curves.Hyperelliptic.Integration.Observation.PreparedDirectMeshEquality.mesh_eq proper _ _

open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements

/-- For proper parent edges, a checked mesh family is uniquely determined by its common depth and diameter. -/
theorem meshes_eq {diameter : PreparedSheetContinuation.Coordinate} {depth : Nat}
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (proper : PreparedDyadicRefinements.AllParentsProper parents)
    (first second : PreparedDirectDyadicRefinements.CheckedDirectMeshes depth diameter parents) : first = second := by
  induction first with
  | nil => cases second; rfl
  | cons mesh tail ih =>
      cases second with
      | cons other rest =>
          have same := Curves.Hyperelliptic.Integration.Observation.PreparedDirectMeshEquality.mesh_eq proper.1 mesh
            other
          cases same
          have remaining := ih proper.2 rest
          cases remaining
          rfl

/-- Allowance-check records for the same meshes, target and differential list are equal. -/
theorem allowances_eq {diameter : PreparedSheetContinuation.Coordinate} {depth : Nat}
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    {meshes : PreparedDirectDyadicRefinements.CheckedDirectMeshes depth diameter parents} {target :
      PreparedSheetContinuation.Coordinate}
    {targets : List (Differentials.Basic.Differential genus)}
    (first second : PreparedDirectDyadicRefinements.MeshAllowanceChecks meshes target targets) : first = second := by
  induction first with
  | nil => cases second; rfl
  | cons value valueEq enough tail ih =>
      cases second with
      | cons other otherEq otherEnough rest =>
          have same := valueEq.trans otherEq.symm
          cases same
          have remaining := ih rest
          cases remaining
          rfl

/-- Two checked direct selections coincide when their root diameters and depths agree.

Proper parent edges determine the same mesh family, and the retained allowance checks are then equal at the exact same
targets. -/
theorem selection_eq {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (proper : PreparedDyadicRefinements.AllParentsProper parents)
    {targets : List (Differentials.Basic.Differential genus)} {target : PreparedSheetContinuation.Coordinate}
    (first second : PreparedDirectDyadicRefinements.CheckedSelection parents targets target)
    (diameter : first.rootDiameter = second.rootDiameter) (depth : first.depth = second.depth) : first = second := by
  cases first with
  | mk firstDiameter firstPositive firstDepth firstMeshes firstAllowances =>
      cases second with
      | mk secondDiameter secondPositive secondDepth secondMeshes secondAllowances =>
          dsimp only at diameter depth
          cases diameter
          cases depth
          have meshes := Curves.Hyperelliptic.Integration.Observation.PreparedDirectMeshEquality.meshes_eq proper
            firstMeshes secondMeshes
          cases meshes
          have allowances := Curves.Hyperelliptic.Integration.Observation.PreparedDirectMeshEquality.allowances_eq
            firstAllowances secondAllowances
          cases allowances
          rfl

end Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedDirectMeshEquality
