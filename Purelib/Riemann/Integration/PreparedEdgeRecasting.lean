module
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
public import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Recasting prepared geometry across finite differential families

The numerical owners and prepared geometry do not depend on the chosen
algebraic differential.  Keep this shared interface below both the checked
mesh builder and the total direct dyadic refinement constructor.  Public
names are retained for existing callers.
-/

namespace Purelib.Riemann.Integration.PreparedEdgeRecasting

open Purelib.Riemann.Curves.AlgebraicDifferentials

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
abbrev Gaussian := Basic.Canonical
/-- The original square-root continuation owner at its retained radicand. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- The original subdivision parameter with its unit-interval bounds. -/
abbrev Endpoint := Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint
/-- The retained continuation endpoint and positive root-diameter target. -/
abbrev StepRequest := Purelib.Riemann.Branches.PreparedSheetContinuation.StepRequest
open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- A prepared differential edge with its exact retained center state. -/
abbrev CenteredEdge {genus : Nat} (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus) :=
  Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential
/-- Compatible refinement of the original ordered constant path models. -/
abbrev CompatibleConstantPathRefinement :=
  Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel.CompatibleConstantPathRefinement

section
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
section
open Purelib.Riemann.Integration
/-- Retain the prepared edge's geometry, root owner and cache for a new differential.

The target differential changes the coefficient interpretation. The original segment, endpoint request, sheet and
clearance certificates remain the constructor's actual retained fields. -/
def recastPreparedEdge {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (edge : PreparedSubdivisionModelCore.PreparedEdge curve source) :
    PreparedSubdivisionModelCore.PreparedEdge curve target where
  ambient := edge.ambient
  start := edge.start
  finish := edge.finish
  segment := edge.segment
  within := edge.within
  left := edge.left
  owner := edge.owner
  request := edge.request
  cached := edge.cached
  ordered := edge.ordered
  small := edge.small
  sheet := edge.sheet

/-- Recasting a prepared edge to its original differential returns that exact edge. -/
@[simp] theorem recastPreparedEdge_self {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (edge : PreparedSubdivisionModelCore.PreparedEdge curve
      differential) :
    recastPreparedEdge differential edge = edge := by
  cases edge
  rfl

/-- Recast the original prepared edge and use the target differential's canonical center state.

The edge retains its original geometry, owner and cache, while the returned center is the canonical state for the recast
coefficient process. -/
def recastCenteredEdge {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (centered : CenteredEdge curve source) : CenteredEdge curve target :=
  let edge := recastPreparedEdge target centered.edge
  { edge := edge
    center :=
      PreparedConstantModels.PreparedEdge.CenterState.canonical edge }

end

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Riemann.Integration in
/-- Recasting to the same differential preserves the model's weighted allowance, including when its center is
recanonicalized. -/
@[simp] theorem recastCenteredEdge_self_weightedAllowance {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential) :
    (PreparedSubdivisionModelCore.CenteredEdge.model
      (recastCenteredEdge differential centered)).weightedAllowance =
        centered.model.weightedAllowance := by
  unfold PreparedSubdivisionModelCore.CenteredEdge.model
    Basic.CellModel.weightedAllowance
    Basic.CellModel.displacement
    PreparedConstantModels.PreparedEdge.centeredModel
    recastCenteredEdge
  rw [recastPreparedEdge_self]

/-- The recast centered edge retains the exact original segment. -/
@[simp] theorem recastCenteredEdge_segment {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (centered : CenteredEdge curve source) :
    (recastCenteredEdge target centered).edge.segment = centered.edge.segment :=
  rfl

/-- The recast centered edge retains the exact original request. -/
@[simp] theorem recastCenteredEdge_request {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (centered : CenteredEdge curve source) :
    (recastCenteredEdge target centered).edge.request = centered.edge.request :=
  rfl

/-- The recast centered edge retains the original left endpoint. -/
@[simp] theorem recastCenteredEdge_left {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (centered : CenteredEdge curve source) :
    (recastCenteredEdge target centered).edge.left = centered.edge.left :=
  rfl

/-- The recast centered edge retains the original sheet. -/
@[simp] theorem recastCenteredEdge_sheet {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (centered : CenteredEdge curve source) :
    (recastCenteredEdge target centered).edge.sheet = centered.edge.sheet :=
  rfl

/-- The recast centered edge has the exact original local segment. -/
@[simp] theorem recastCenteredEdge_localSegment {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (centered : CenteredEdge curve source) :
    (recastCenteredEdge target centered).edge.localSegment =
      centered.edge.localSegment :=
  rfl

end

/-- Construct a continuation request from the supplied endpoint and positive root-diameter target. -/
def directRequest (right : Endpoint) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) : StepRequest where
  endpoint := right
  rootDiameter := rootDiameter
  rootDiameterPositive := rootDiameterPositive

end Purelib.Riemann.Integration.PreparedEdgeRecasting

