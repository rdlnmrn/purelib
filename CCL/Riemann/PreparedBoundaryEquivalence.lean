import CCL.Riemann.PreparedConstantModels

/-!
# Operational coefficient transport across prepared cell boundaries

Prepared integration cells query their sheet root through a pointwise
continuation, while the recursive continuation checker resets each accepted
endpoint to a fresh global owner.  This module proves, using only the stored
finite winding-one bridges, that the coefficient at the right end of one cell
is operationally equal to the coefficient at the left end of its successor.
-/

namespace CCL.Riemann.PreparedBoundaryEquivalence

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchCuts

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner
abbrev Endpoint := CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint
abbrev StepRequest := CCL.Riemann.PreparedSheetContinuation.StepRequest
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev PreparedEdge {genus : Nat} (curve : HyperellipticCurve genus)
    (differential : Differential genus) :=
  CCL.Riemann.PreparedConstantModels.PreparedEdge curve differential

private theorem zeroInside :
    (0 : Coordinate) <= 0 ∧ (0 : Coordinate) <= 1 := by decide

private theorem oneInside :
    (0 : Coordinate) <= 1 ∧ (1 : Coordinate) <= 1 := by decide

/-- Two productive names together with their finite operational comparison.
Keeping the names as fields prevents dependent edge expressions from being
expanded while a boundary-construction type elaborates. -/
private structure NamedBridge where
  first : Named
  second : Named
  equivalent : NamedEquivalent first second

/-- The point-query presentation at local parameter one is the transported
endpoint owner already stored by the accepted move. -/
private def endpointQueryEquivalentToTransported {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (edge : PreparedEdge curve differential) : NamedBridge where
  first := edge.rootName 1 oneInside
  second := edge.transportedRootName
  equivalent := by
    unfold CCL.Riemann.PreparedConstantModels.PreparedEdge.rootName
      CCL.Riemann.PreparedConstantModels.PreparedEdge.transportedRootName
    rw [CCL.Riemann.PreparedDifferentialModels.rootAtCached_one_name_eq_transportedRootName]
    exact CCL.OperationalEquivalence.NamedEquivalent.refl _

/-- The point-query presentation at local parameter zero retains the prepared
source root by finite winding-one uniqueness. -/
private def preparedEquivalentToBaseQuery {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (edge : PreparedEdge curve differential) : NamedBridge where
  first := edge.preparedRootName
  second := edge.rootName 0 zeroInside
  equivalent := by
    let prepared := CCL.Riemann.PreparedSheetContinuation.prepared edge.segment
      edge.left edge.owner edge.request
    have sameSmall :
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (curve.polynomial.eval (edge.segment.pointAt edge.left.parameter) -
              curve.polynomial.eval
                (edge.segment.pointAt edge.left.parameter)) <
          prepared.track.initial.clearance.bound := by
      rw [RFAP.ConstructiveGaussian.Gaussian.sub_self,
        RFAP.ConstructiveGaussian.Gaussian.normSq_zero]
      exact prepared.track.initial.clearance.positive
    have preparedToGeneric :=
      CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_advance_same
        (edge.segment.pointAt_eval_ne_zero edge.left.parameter edge.left.inside)
          prepared sameSmall
    have genericToDirect :=
      CCL.Riemann.PreparedSheetContinuation.reservedTransportRootEquivalentGeneric
        prepared
          (edge.segment.pointAt_eval_ne_zero edge.left.parameter
            edge.left.inside)
          sameSmall
        (CCL.Riemann.PreparedSheetContinuation.transportReserve edge.segment
          edge.left edge.request)
    have equivalent := CCL.OperationalEquivalence.NamedEquivalent.trans
      preparedToGeneric genericToDirect
    unfold CCL.Riemann.PreparedConstantModels.PreparedEdge.preparedRootName
      CCL.Riemann.PreparedConstantModels.PreparedEdge.rootName
    rw [CCL.Riemann.PreparedDifferentialModels.rootAtCached_zero_name_eq_zeroMoveRootName]
    unfold CCL.Riemann.PreparedSheetContinuation.preparedRootName
      CCL.Riemann.PreparedSheetContinuation.zeroMoveRootName
    exact equivalent

/-- Consecutive prepared moves use operationally equal differential
coefficients at their common endpoint.  The proof follows four finite root
presentations: the first cell's endpoint query, its transported endpoint owner,
the freshly reconditioned next owner, and the next cell's zero query. -/
def adjacentCoefficientEquivalent {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CCL.Riemann.PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (nextRequest : StepRequest)
    (nextCached : CCL.Riemann.PreparedSheetContinuation.CachedSource segment
      request.endpoint
        (CCL.Riemann.PreparedSheetContinuation.advance segment within left
          owner request small) nextRequest)
    (nextOrdered : request.endpoint.parameter <=
      nextRequest.endpoint.parameter)
    (nextSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      request.endpoint.parameter nextRequest.endpoint.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared
          segment request.endpoint
          (CCL.Riemann.PreparedSheetContinuation.advance segment within left
            owner request small) nextRequest).track.initial.clearance.bound)
    (sheet : Fin 2) :
    NamedEquivalent
      (CCL.Riemann.PreparedDifferentialModels.coefficientAtCached curve
        differential segment within left owner request cached ordered small
          sheet 1 oneInside).name
      (CCL.Riemann.PreparedDifferentialModels.coefficientAtCached curve differential
        segment within request.endpoint
          (CCL.Riemann.PreparedSheetContinuation.advance segment within left
            owner request small)
          nextRequest nextCached nextOrdered nextSmall sheet 0 zeroInside).name := by
  let endpointNonzero : curve.polynomial.eval
      (segment.pointAt request.endpoint.parameter) ≠ 0 :=
    segment.pointAt_eval_ne_zero request.endpoint.parameter
      request.endpoint.inside
  let transported := CCL.Riemann.PreparedSheetContinuation.transported segment
    within left owner request small
  let nextOwner := CCL.Riemann.PreparedSheetContinuation.advance segment within
    left owner request small
  have resetEquivalent : NamedEquivalent
      (transported.certificate endpointNonzero).value.name
      (nextOwner.certificate endpointNonzero).value.name := by
    simpa only [nextOwner, CCL.Riemann.PreparedSheetContinuation.advance,
      CCL.Riemann.SquareRootTrackEquivalence.ownerRootName] using
      (CCL.Riemann.PreparedSheetContinuation.retainedAtReserveRootEquivalent
        transported
        (CCL.Riemann.PreparedSheetContinuation.preparedClearanceLower
          segment left request))
  have preparationEquivalent :=
    CCL.Riemann.PreparedSheetContinuation.sourceRootEquivalent segment
      request.endpoint nextOwner nextRequest
  let parent : PreparedEdge curve differential :=
    { ambient := ambient
      start := start
      finish := finish
      segment := segment
      within := within
      left := left
      owner := owner
      request := request
      cached := cached
      ordered := ordered
      small := small
      sheet := sheet }
  let child : PreparedEdge curve differential :=
    { ambient := ambient
      start := start
      finish := finish
      segment := segment
      within := within
      left := request.endpoint
      owner := nextOwner
      request := nextRequest
      cached := nextCached
      ordered := nextOrdered
      small := nextSmall
      sheet := sheet }
  have endpointEquivalent :=
    (endpointQueryEquivalentToTransported parent).equivalent
  change NamedEquivalent (parent.rootName 1 oneInside)
    parent.transportedRootName at endpointEquivalent
  have baseEquivalent := (preparedEquivalentToBaseQuery child).equivalent
  change NamedEquivalent child.preparedRootName
    (child.rootName 0 zeroInside) at baseEquivalent
  let nextOwnerRoot := (nextOwner.certificate endpointNonzero).value.name
  have resetWrapped : NamedEquivalent parent.transportedRootName
      nextOwnerRoot := by
    simpa only [parent,
      CCL.Riemann.PreparedConstantModels.PreparedEdge.transportedRootName,
      CCL.Riemann.PreparedSheetContinuation.transportedRootName,
      CCL.Riemann.PreparedSheetContinuation.advance,
      transported, nextOwner, nextOwnerRoot] using resetEquivalent
  have preparationWrapped : NamedEquivalent nextOwnerRoot
      child.preparedRootName := by
    simpa only [child,
      CCL.Riemann.PreparedConstantModels.PreparedEdge.preparedRootName,
      CCL.Riemann.PreparedSheetContinuation.preparedRootName,
      nextOwnerRoot, nextOwner] using preparationEquivalent
  have edgeRootEquivalent :=
    CCL.OperationalEquivalence.NamedEquivalent.trans endpointEquivalent
      (CCL.OperationalEquivalence.NamedEquivalent.trans resetWrapped
        (CCL.OperationalEquivalence.NamedEquivalent.trans preparationWrapped
          baseEquivalent))
  have point_eq : parent.point 1 = child.point 0 := by
    simp only [parent, child,
      CCL.Riemann.PreparedConstantModels.PreparedEdge.point,
      CCL.Riemann.PreparedConstantModels.PreparedEdge.localSegment,
      CCL.Riemann.PreparedDifferentialModels.edge,
      CCL.Riemann.BranchCuts.ClearSegment.pointAt_one,
      CCL.Riemann.BranchCuts.ClearSegment.pointAt_zero]
  exact
    CCL.Riemann.PreparedConstantModels.PreparedEdge.coefficientEquivalent_of_rootEquivalent
      parent child 1 oneInside point_eq edgeRootEquivalent

end CCL.Riemann.PreparedBoundaryEquivalence
