module
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

@[expose] public section

/-!
Regression coverage for evidence-bearing mesh and allowance attempts.
No generated coefficient banks or global root isolation are imported here.
The generic tests retain exact procedure identities, not just error tags.
-/

namespace Test.Riemann.CheckedPreparationReportsTests

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (PreparedEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
open Purelib.Riemann.Integration.PreparedEdgeRecasting (Coordinate Endpoint CenteredEdge)
open Purelib.Riemann.Integration

/-- An inconclusive single-edge mesh attempt retains its exact depth, requested diameter, endpoints and returned error
certificate. -/
example {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    {parent : PreparedEdge curve differential}
    {proper : parent.left.parameter < parent.request.endpoint.parameter}
    {diameter : Coordinate} {positive : 0 < diameter} {depth : Nat}
    {left right : Endpoint} {lower : parent.left.parameter ≤ left.parameter}
    {upper : right.parameter ≤ parent.request.endpoint.parameter}
    {localProper : left.parameter < right.parameter}
    (report : CheckedDirectGeometry.MeshInconclusive parent proper diameter positive
      depth left right lower upper localProper) :
    report.attemptedDepth = depth ∧ report.requestedDiameter = diameter ∧
      report.start = left ∧ report.finish = right ∧
      CheckedDirectGeometry.attemptMesh parent proper diameter positive depth left right
        lower upper localProper = .error report :=
  ⟨report.attemptedDepth_eq, report.requestedDiameter_eq,
    report.start_eq, report.finish_eq, report.attempt_error⟩

/-- An inconclusive complete mesh attempt retains an unresolved original parent and its exact attempted depth and
diameter. -/
example {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    {parents : List (CenteredEdge curve differential)}
    {proper : PreparedDyadicRefinements.AllParentsProper parents}
    {diameter : Coordinate} {positive : 0 < diameter} {depth : Nat}
    (report : CheckedDirectMeshes.Inconclusive depth diameter positive parents proper) :
    report.completedParents < report.parentCount ∧
      report.attemptedDepth = depth ∧ report.requestedDiameter = diameter ∧
      CheckedDirectMeshes.attempt depth diameter positive parents proper = .error report :=
  ⟨report.unresolvedIndex_lt_count, report.attemptedDepth_eq,
    report.requestedDiameter_eq, report.attempt_error⟩

/-- An empty original parent list produces a successful empty mesh bank directly. -/
example {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter) :
    CheckedDirectMeshes.attempt depth diameter positive
        ([] : List (CenteredEdge curve differential)) True.intro = .ok .nil := rfl

/-- An inconclusive allowance check retains its exact mesh bank, requested target and returned error certificate. -/
example {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {source : Differentials.Basic.Differential
  genus}
    {parents : List (CenteredEdge curve source)} {diameter : Coordinate} {depth : Nat}
    {meshes : CheckedDirectMeshes depth diameter parents} {target : Coordinate}
    {targets : List (Differentials.Basic.Differential genus)}
    (report : MeshAllowanceChecks.Inconclusive meshes target targets) :
    report.geometry = meshes ∧ report.requestedTarget = target ∧
      MeshAllowanceChecks.attempt meshes target targets = .error report :=
  ⟨report.geometry_eq, report.requestedTarget_eq, report.attempt_error⟩

/-- An empty differential request list succeeds without allocating any additional allowance. -/
example {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {source : Differentials.Basic.Differential
  genus}
    {parents : List (CenteredEdge curve source)} {diameter : Coordinate} {depth : Nat}
    (meshes : CheckedDirectMeshes depth diameter parents) (target : Coordinate) :
    MeshAllowanceChecks.attempt meshes target [] = .ok .nil := rfl

-- Even the zero allowance of an empty geometry cannot meet a negative
-- requested bound.  The returned report retains that actual target and depth.
/-- A negative allowance target on an empty geometry is inconclusive and retains the exact target and depth.

The executable report rules out success because its certified nonnegative aggregate allowance cannot fit the negative
requested bound. -/
example {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {source : Differentials.Basic.Differential
  genus}
    (differential : Differentials.Basic.Differential genus) :
    match MeshAllowanceChecks.attempt
        (CheckedDirectMeshes.nil : CheckedDirectMeshes (curve := curve)
          (differential := source) 0 1 []) (-1) [differential] with
    | .ok _ => False
    | .error report => report.attemptedDepth = 0 ∧ report.requestedTarget = -1 := by
  generalize MeshAllowanceChecks.attempt
    (CheckedDirectMeshes.nil : CheckedDirectMeshes (curve := curve)
      (differential := source) 0 1 []) (-1) [differential] = result
  cases result with
  | error report => exact ⟨report.attemptedDepth_eq, report.requestedTarget_eq⟩
  | ok checks =>
      have bound := checks.bound differential List.mem_cons_self
      simp only [CheckedDirectMeshes.aggregateAllowanceFor,
        CheckedDirectMeshes.weightedAllowanceFor, mul_zero] at bound
      exact (by decide : ¬ (0 : Coordinate) ≤ -1) bound

end Test.Riemann.CheckedPreparationReportsTests
