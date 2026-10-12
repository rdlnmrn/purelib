module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Fin.Cases
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Dyadic.Bounds.Small
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
public import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.RootIsolation.SquareRoot.Replay.Eight.Configuration
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

/-!
# Retained depth-three dyadic endpoint tables

Two finite endpoint tables and their bounded source/target indices determine
exact eight-edge step requests. Boundary-aligned presentations keep the same
rational parameters, and the retained request lists agree with the complete
depth-three subdivision construction.
-/

namespace Purelib.RootIsolation.SquareRoot.Subdivision.Dyadic.Eight

open Purelib
open Purelib.Data Purelib.Data.Rat
open Purelib.Geometry.Rational Purelib.Polynomial
open Purelib.Riemann.Branches Purelib.Riemann.Paths Purelib.Riemann.Topology
open Purelib.RootIsolation.SquareRoot.Replay.Eight

public section

/-- A subdivision with the depth-three dyadic edge list has eight steps.

The equality uses the cached edge list and its exact correspondence with the
standard dyadic edges. -/
theorem subdivisionStepCount_eq_eight
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box}
    {start finish : Gaussian.Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : SquareRootContinuationChain.Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (data : PreparedSheetContinuation.Subdivision segment within
      left owner)
    (equal : data.parameterEdges =
      ClearSheetContinuation.Subdivision.dyadicEdges 3
        PreparedClearPathModels.zeroEndpoint PreparedClearPathModels.oneEndpoint) :
    data.stepCount = 2 ^ 3 := by
  calc
    data.stepCount = data.parameterEdges.length :=
      (PreparedSheetContinuation.Subdivision.parameterEdges_length
        data).symm
    _ = (ClearSheetContinuation.Subdivision.dyadicEdges 3
        PreparedClearPathModels.zeroEndpoint PreparedClearPathModels.oneEndpoint).length := congrArg List.length equal
    _ = 2 ^ 3 :=
      ClearSheetContinuation.Subdivision.dyadicEdges_length 3
        PreparedClearPathModels.zeroEndpoint PreparedClearPathModels.oneEndpoint

/-- The canonical endpoint data for the depth-three mesh of `firstConnectorSegment`.

The original bounded index supplies the natural coordinate. Successive natural constructor patterns select the same
ordered literal entries with a constant result type; the original input bound excludes every unused default case. -/
@[expose] def firstConnectorGridEndpoint : Fin 9 →
    ClearSheetContinuation.Subdivision.Endpoint :=
  fun index => match index.val with
  | Nat.zero => ⟨0 / 8, by decide⟩
  | (Nat.succ Nat.zero) => ⟨1 / 8, by decide⟩
  | (Nat.succ (Nat.succ Nat.zero)) => ⟨2 / 8, by decide⟩
  | (Nat.succ (Nat.succ (Nat.succ Nat.zero))) => ⟨3 / 8, by decide⟩
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) => ⟨4 / 8, by decide⟩
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) => ⟨5 / 8, by decide⟩
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) => ⟨6 / 8, by decide⟩
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))) => ⟨7 / 8, by decide⟩
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ _)))))))) => ⟨8 / 8, by decide⟩

/-- The same nine endpoints, with the two boundary entries definitionally aligned to the standard complete-segment
endpoints.

The original bounded index supplies the natural coordinate. Successive natural constructor patterns select the same
ordered literal entries with a constant result type; the original input bound excludes every unused default case. -/
@[expose] def firstConnectorMeshEndpoint : Fin 9 →
    ClearSheetContinuation.Subdivision.Endpoint :=
  fun index => match index.val with
  | Nat.zero => PreparedClearPathModels.zeroEndpoint
  | (Nat.succ Nat.zero) => firstConnectorGridEndpoint 1
  | (Nat.succ (Nat.succ Nat.zero)) => firstConnectorGridEndpoint 2
  | (Nat.succ (Nat.succ (Nat.succ Nat.zero))) => firstConnectorGridEndpoint 3
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) => firstConnectorGridEndpoint 4
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) => firstConnectorGridEndpoint 5
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) => firstConnectorGridEndpoint 6
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))) => firstConnectorGridEndpoint
    7
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ _)))))))) =>
    PreparedClearPathModels.oneEndpoint

/-- `firstConnectorMeshEndpoint` changes only proof-level boundary
presentations; its rational parameters are the exact cached grid parameters.

Boundary presentations preserve the same rational parameter as the retained grid entry. The equality covers every
original bounded mesh coordinate. -/
theorem firstConnectorMeshEndpoint_parameter (index : Fin 9) :
    (firstConnectorMeshEndpoint index).parameter =
      (firstConnectorGridEndpoint index).parameter := by
  rcases Data.Fin.Cases.finNineCases index with h | h | h | h | h | h | h | h | h
  all_goals (subst index; rfl)

/-- Source endpoint of each of the eight local dyadic edges.

The original bounded index supplies the natural coordinate. Successive natural constructor patterns select the same
ordered literal entries with a constant result type; the original input bound excludes every unused default case. -/
@[expose] def firstConnectorEdgeSource : Fin 8 → Fin 9 :=
  fun index => match index.val with
  | Nat.zero => 0
  | (Nat.succ Nat.zero) => 1
  | (Nat.succ (Nat.succ Nat.zero)) => 2
  | (Nat.succ (Nat.succ (Nat.succ Nat.zero))) => 3
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) => 4
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) => 5
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) => 6
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ _))))))) => 7

/-- Target endpoint of each of the eight local dyadic edges.

The original bounded index supplies the natural coordinate. Successive natural constructor patterns select the same
ordered literal entries with a constant result type; the original input bound excludes every unused default case. -/
@[expose] def firstConnectorEdgeTarget : Fin 8 → Fin 9 :=
  fun index => match index.val with
  | Nat.zero => 1
  | (Nat.succ Nat.zero) => 2
  | (Nat.succ (Nat.succ Nat.zero)) => 3
  | (Nat.succ (Nat.succ (Nat.succ Nat.zero))) => 4
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) => 5
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) => 6
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) => 7
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ _))))))) => 8

/-- Diameter request for each edge of the first connector-cell mesh.

The retained target endpoint and common positive root-diameter request define each mesh step. The request uses the same
ordered endpoint table as its parameter edge. -/
@[expose] def firstConnectorEdgeRequest (edge : Fin 8) :
    PreparedSheetContinuation.StepRequest :=
  { endpoint := firstConnectorMeshEndpoint (firstConnectorEdgeTarget edge)
    rootDiameter := Configuration.workingRootDiameter
    rootDiameterPositive := Configuration.workingRootDiameter_positive }

/-- Adjacent retained eighth-grid parameters have squared distance exactly one sixty-fourth. -/
public theorem firstConnectorGridEndpoint_adjacentSquare (edge : Fin 8) :
    ((firstConnectorGridEndpoint (firstConnectorEdgeSource edge)).parameter -
      (firstConnectorGridEndpoint (firstConnectorEdgeTarget edge)).parameter) ^
        2 = (1 / 64 : Fraction.Rational) := by
  rcases Data.Fin.Cases.finEightCases edge with h | h | h | h | h | h | h | h
  all_goals subst edge
  all_goals simp only [firstConnectorEdgeSource, firstConnectorEdgeTarget,
    firstConnectorGridEndpoint]
  all_goals apply Data.Rat.Dyadic.Bounds.Small.adjacentEighthParameters

/-- Every displayed eighth-grid source parameter precedes its retained request endpoint.

The retained source and requested target belong to consecutive entries of the ordered mesh. Their rational parameters
provide the original weak order certificate. -/
theorem firstConnectorEdgeOrdered (edge : Fin 8) :
    (firstConnectorMeshEndpoint
        (firstConnectorEdgeSource edge)).parameter ≤
      (firstConnectorEdgeRequest edge).endpoint.parameter := by
  rcases Data.Fin.Cases.finEightCases edge with h | h | h | h | h | h | h | h
  all_goals subst edge
  all_goals with_unfolding_all decide

/-- The retained parameter edge corresponding to one cached mesh request.

Both endpoints are taken from the same retained mesh table and step request. The edge preserves the original bounded
source and target indices. -/
@[expose] def firstConnectorParameterEdge (edge : Fin 8) :
    ClearSheetContinuation.Subdivision.ParameterEdge :=
  ⟨firstConnectorMeshEndpoint (firstConnectorEdgeSource edge),
    (firstConnectorEdgeRequest edge).endpoint⟩

/-- The eight displayed requests are exactly the standard depth-three
dyadic request list, including the common root-diameter request.

All eight cached step requests use the original ordered mesh targets and common positive root-diameter value. The finite
list agrees with the complete depth-three request construction. -/
theorem ExplicitQuarticPreparedCertificates.firstConnectorDyadicRequests :
    PreparedSheetContinuation.Subdivision.dyadicRequests 3
      PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint Configuration.workingRootDiameter
          Configuration.workingRootDiameter_positive =
      [firstConnectorEdgeRequest 0, firstConnectorEdgeRequest 1,
        firstConnectorEdgeRequest 2, firstConnectorEdgeRequest 3,
        firstConnectorEdgeRequest 4, firstConnectorEdgeRequest 5,
        firstConnectorEdgeRequest 6, firstConnectorEdgeRequest 7] := by
  with_unfolding_all rfl

/-- The nine rational endpoints `0/8` through `8/8`, each retained with its unit-interval bounds.

The original bounded index supplies the natural coordinate. Successive natural constructor patterns select the same
ordered literal entries with a constant result type; the original input bound excludes every unused default case. -/
@[expose] def secondGridEndpoint : Fin 9 →
    ClearSheetContinuation.Subdivision.Endpoint :=
  fun index => match index.val with
  | Nat.zero => ⟨0 / 8, by decide⟩
  | (Nat.succ Nat.zero) => ⟨1 / 8, by decide⟩
  | (Nat.succ (Nat.succ Nat.zero)) => ⟨2 / 8, by decide⟩
  | (Nat.succ (Nat.succ (Nat.succ Nat.zero))) => ⟨3 / 8, by decide⟩
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) => ⟨4 / 8, by decide⟩
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) => ⟨5 / 8, by decide⟩
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) => ⟨6 / 8, by decide⟩
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))) => ⟨7 / 8, by decide⟩
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ _)))))))) => ⟨8 / 8, by decide⟩

/-- Boundary-aligned presentations of the same nine mesh endpoints.

The original bounded index supplies the natural coordinate. Successive natural constructor patterns select the same
ordered literal entries with a constant result type; the original input bound excludes every unused default case. -/
@[expose] def secondMeshEndpoint : Fin 9 →
    ClearSheetContinuation.Subdivision.Endpoint :=
  fun index => match index.val with
  | Nat.zero => PreparedClearPathModels.zeroEndpoint
  | (Nat.succ Nat.zero) => secondGridEndpoint 1
  | (Nat.succ (Nat.succ Nat.zero)) => secondGridEndpoint 2
  | (Nat.succ (Nat.succ (Nat.succ Nat.zero))) => secondGridEndpoint 3
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) => secondGridEndpoint 4
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) => secondGridEndpoint 5
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) => secondGridEndpoint 6
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))) => secondGridEndpoint 7
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ _)))))))) =>
    PreparedClearPathModels.oneEndpoint

/-- Boundary-aligned second-mesh endpoints preserve the original cached rational parameters.

The boundary-aligned endpoint presentation has the same rational parameter as the retained grid entry. The equality
preserves every original bounded coordinate. -/
theorem secondMeshEndpoint_parameter (index : Fin 9) :
    (secondMeshEndpoint index).parameter =
      (secondGridEndpoint index).parameter := by
  rcases Data.Fin.Cases.finNineCasesSecond index with h | h | h | h | h | h | h | h | h
  all_goals subst index
  all_goals rfl

/-- Read the source vertex index of each of the eight consecutive second-mesh edges.

The original bounded index supplies the natural coordinate. Successive natural constructor patterns select the same
ordered literal entries with a constant result type; the original input bound excludes every unused default case. -/
@[expose] def secondEdgeSource : Fin 8 → Fin 9 :=
  fun index => match index.val with
  | Nat.zero => 0
  | (Nat.succ Nat.zero) => 1
  | (Nat.succ (Nat.succ Nat.zero)) => 2
  | (Nat.succ (Nat.succ (Nat.succ Nat.zero))) => 3
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) => 4
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) => 5
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) => 6
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ _))))))) => 7

/-- Read the successor vertex index of each of the eight consecutive second-mesh edges.

The original bounded index supplies the natural coordinate. Successive natural constructor patterns select the same
ordered literal entries with a constant result type; the original input bound excludes every unused default case. -/
@[expose] def secondEdgeTarget : Fin 8 → Fin 9 :=
  fun index => match index.val with
  | Nat.zero => 1
  | (Nat.succ Nat.zero) => 2
  | (Nat.succ (Nat.succ Nat.zero)) => 3
  | (Nat.succ (Nat.succ (Nat.succ Nat.zero))) => 4
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) => 5
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) => 6
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) => 7
  | (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ _))))))) => 8

/-- Pair a retained second-mesh target endpoint with the original positive root-diameter request.

The endpoint is the retained target of the corresponding ordered mesh edge. Each request carries the same common
positive root-diameter value. -/
@[expose] def secondEdgeRequest (edge : Fin 8) :
    PreparedSheetContinuation.StepRequest :=
  { endpoint := secondMeshEndpoint (secondEdgeTarget edge)
    rootDiameter := Configuration.workingRootDiameter
    rootDiameterPositive := Configuration.workingRootDiameter_positive }

/-- The eight retained second-mesh requests are exactly the standard depth-three dyadic request list.

The complete finite list retains all eight ordered mesh targets with the common positive root-diameter request. It is
the exact depth-three dyadic request list. -/
theorem ExplicitQuarticPreparedSecondCellCertificate.secondDyadicRequests :
    PreparedSheetContinuation.Subdivision.dyadicRequests 3
      PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint Configuration.workingRootDiameter
          Configuration.workingRootDiameter_positive =
      [secondEdgeRequest 0, secondEdgeRequest 1, secondEdgeRequest 2,
        secondEdgeRequest 3, secondEdgeRequest 4, secondEdgeRequest 5,
        secondEdgeRequest 6, secondEdgeRequest 7] := by
  with_unfolding_all rfl

end

end Purelib.RootIsolation.SquareRoot.Subdivision.Dyadic.Eight
