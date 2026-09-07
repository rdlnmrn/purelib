import CCL.Riemann.PreparedSubdivisionModels

/-!
# Checked dyadic refinements of prepared edge lists

This module lifts the constructive one-parent dyadic congruence checker to a
finite list of centered prepared edges.  Every child block retains its exact
dependent owner walk, canonical parent positions, and computed seven-way root
congruence chain.
-/

namespace CCL.Riemann.PreparedDyadicRefinements

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchCuts

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner
abbrev Endpoint := CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint
abbrev StepRequest := CCL.Riemann.PreparedSheetContinuation.StepRequest
abbrev CenteredEdge {genus : Nat} (curve : HyperellipticCurve genus)
    (differential : Differential genus) :=
  CCL.Riemann.PreparedSubdivisionModels.CenteredEdge curve differential
abbrev CompatibleConstantPathRefinement :=
  CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement

/-- Positive minimum of the seven exact target-distance clearances used by
one parent/fine continuation congruence check. -/
def directStepClearanceFloor {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (current : Endpoint)
    (position : CCL.Riemann.PreparedSubdivisionModels.ParentPosition parent
      current)
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
    (request : StepRequest) : Coordinate :=
  let source := CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
    parent.left parent.owner parent.request
  let first :=
    CCL.Riemann.PreparedSheetContinuation.Subdivision.directOwnerAt
      parent.left source current position.directMoveSmall
  let second := CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
    current owner request
  let nonzero := parent.segment.pointAt_eval_ne_zero current.parameter
    current.inside
  min first.track.initial.clearance.bound
    (min second.track.initial.clearance.bound
      (min (CCL.Riemann.SquareRootTrackEquivalence.freshSourceClearance
          nonzero first)
        (min (CCL.Riemann.SquareRootTrackEquivalence.freshSourceClearance
            nonzero second)
          (min (CCL.Riemann.SquareRootTrackEquivalence.bridgeTailClearance
              nonzero first)
            (min (CCL.Riemann.SquareRootTrackEquivalence.bridgeTailClearance
                nonzero second)
              (CCL.Riemann.SquareRootTrackEquivalence.freshCommonClearance
                nonzero first))))))

theorem directStepClearanceFloor_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (current : Endpoint)
    (position : CCL.Riemann.PreparedSubdivisionModels.ParentPosition parent
      current)
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
    (request : StepRequest) :
    0 < directStepClearanceFloor parent current position owner request := by
  let source := CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
    parent.left parent.owner parent.request
  let first :=
    CCL.Riemann.PreparedSheetContinuation.Subdivision.directOwnerAt
      parent.left source current position.directMoveSmall
  let second := CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
    current owner request
  let nonzero := parent.segment.pointAt_eval_ne_zero current.parameter
    current.inside
  change 0 < min first.track.initial.clearance.bound
    (min second.track.initial.clearance.bound
      (min (CCL.Riemann.SquareRootTrackEquivalence.freshSourceClearance
          nonzero first)
        (min (CCL.Riemann.SquareRootTrackEquivalence.freshSourceClearance
            nonzero second)
          (min (CCL.Riemann.SquareRootTrackEquivalence.bridgeTailClearance
              nonzero first)
            (min (CCL.Riemann.SquareRootTrackEquivalence.bridgeTailClearance
                nonzero second)
              (CCL.Riemann.SquareRootTrackEquivalence.freshCommonClearance
                nonzero first))))))
  apply lt_min
  · exact first.track.initial.clearance.positive
  · apply lt_min
    · exact second.track.initial.clearance.positive
    · apply lt_min
      · exact (CCL.Riemann.SquareRootReconditioning.freshOwner nonzero
          first).track.initial.clearance.positive
      · apply lt_min
        · exact (CCL.Riemann.SquareRootReconditioning.freshOwner nonzero
            second).track.initial.clearance.positive
        · apply lt_min
          · exact (CCL.Riemann.SquareRootTrackEquivalence.commonTailOfBridge
              (CCL.Riemann.SquareRootReconditioning.bridge nonzero first)).initial
                |>.clearance.positive
          · apply lt_min
            · exact (CCL.Riemann.SquareRootTrackEquivalence.commonTailOfBridge
                (CCL.Riemann.SquareRootReconditioning.bridge nonzero second)).initial
                  |>.clearance.positive
            · exact ((CCL.Riemann.SquareRootReconditioning.freshOwner
                nonzero first).refineAt 1).track.initial.clearance.positive

/-- One variation comparison below the displayed seven-way minimum constructs
the exact direct-step congruence record. -/
theorem directStepSmall_of_variation_lt_floor {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (current : Endpoint)
    (position : CCL.Riemann.PreparedSubdivisionModels.ParentPosition parent
      current)
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
    (request : StepRequest)
    (below : CCL.Riemann.ClearSheetContinuation.variationBound parent.segment
      current.parameter request.endpoint.parameter <
        directStepClearanceFloor parent current position owner request) :
    CCL.Riemann.PreparedSheetContinuation.Subdivision.DirectStepSmall
      parent.segment parent.left
        (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
          parent.left parent.owner parent.request)
        current position.directMoveSmall owner request := by
  let source := CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
    parent.left parent.owner parent.request
  let first :=
    CCL.Riemann.PreparedSheetContinuation.Subdivision.directOwnerAt
      parent.left source current position.directMoveSmall
  let second := CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
    current owner request
  let nonzero := parent.segment.pointAt_eval_ne_zero current.parameter
    current.inside
  let firstFresh :=
    CCL.Riemann.SquareRootTrackEquivalence.freshSourceClearance nonzero first
  let secondFresh :=
    CCL.Riemann.SquareRootTrackEquivalence.freshSourceClearance nonzero second
  let firstBridge :=
    CCL.Riemann.SquareRootTrackEquivalence.bridgeTailClearance nonzero first
  let secondBridge :=
    CCL.Riemann.SquareRootTrackEquivalence.bridgeTailClearance nonzero second
  let freshCommon :=
    CCL.Riemann.SquareRootTrackEquivalence.freshCommonClearance nonzero first
  let sixth := min secondBridge freshCommon
  let fifth := min firstBridge sixth
  let fourth := min secondFresh fifth
  let third := min firstFresh fourth
  let secondTail := min second.track.initial.clearance.bound third
  let floor := min first.track.initial.clearance.bound secondTail
  have floor_eq : directStepClearanceFloor parent current position owner
      request = floor := rfl
  have distance : RFAP.ConstructiveGaussian.Gaussian.normSq
      (curve.polynomial.eval (parent.segment.pointAt current.parameter) -
        curve.polynomial.eval
          (parent.segment.pointAt request.endpoint.parameter)) < floor := by
    rw [← floor_eq]
    exact (CCL.Riemann.ClearSheetContinuation.evaluation_variation_le
      parent.segment parent.within current.parameter
        request.endpoint.parameter current.inside
          request.endpoint.inside).trans_lt below
  have firstLe : floor <= first.track.initial.clearance.bound :=
    min_le_left _ _
  have secondLe : floor <= second.track.initial.clearance.bound :=
    (min_le_right _ _).trans (min_le_left _ _)
  have firstFreshLe : floor <= firstFresh :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have secondFreshLe : floor <= secondFresh :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have firstBridgeLe : floor <= firstBridge :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))))
  have secondBridgeLe : floor <= secondBridge :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))))
  have freshCommonLe : floor <= freshCommon :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))))
  exact
    ⟨{ firstSmall := distance.trans_le firstLe
       secondSmall := distance.trans_le secondLe
       firstFresh := distance.trans_le firstFreshLe
       secondFresh := distance.trans_le secondFreshLe
       firstBridge := distance.trans_le firstBridgeLe
       secondBridge := distance.trans_le secondBridgeLe
       freshCommon := distance.trans_le freshCommonLe }⟩

/-- One rational variation-below-floor comparison for every edge of a fine
parent block. -/
inductive ParentCongruenceSafe {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential) :
    (current : Endpoint) ->
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))) ->
    (subdivision : CCL.Riemann.PreparedSubdivisionModels.PreparedSubdivision
      parent.segment parent.within current owner) ->
    CCL.Riemann.PreparedSubdivisionModels.ParentPositions parent subdivision ->
      Prop
  | stop
      (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (position : CCL.Riemann.PreparedSubdivisionModels.ParentPosition parent
        current) :
      ParentCongruenceSafe parent current owner (.stop current owner)
        (.stop current owner position)
  | next
      (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (request : StepRequest)
      (cached : CCL.Riemann.PreparedSheetContinuation.CachedSource
        parent.segment current owner request)
      (ordered : current.parameter <= request.endpoint.parameter)
      (small : CCL.Riemann.ClearSheetContinuation.variationBound
        parent.segment current.parameter request.endpoint.parameter <
          (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
            current owner request).track.initial.clearance.bound)
      (remaining : CCL.Riemann.PreparedSubdivisionModels.PreparedSubdivision
        parent.segment parent.within request.endpoint
          (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
            parent.within current owner request small))
      (position : CCL.Riemann.PreparedSubdivisionModels.ParentPosition parent
        current)
      (remainingPositions :
        CCL.Riemann.PreparedSubdivisionModels.ParentPositions parent remaining)
      (below : CCL.Riemann.ClearSheetContinuation.variationBound parent.segment
        current.parameter request.endpoint.parameter <
          directStepClearanceFloor parent current position owner request)
      (tail : ParentCongruenceSafe parent request.endpoint
        (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
          parent.within current owner request small)
        remaining remainingPositions) :
      ParentCongruenceSafe parent current owner
        (.next current owner request cached ordered small remaining)
        (.next current owner request cached ordered small remaining position
          remainingPositions)

/-- Minimum of all direct-congruence clearances occurring in one displayed
fine parent block.  The terminal value `1` keeps the empty block positive. -/
def parentCongruenceFloor {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential) :
    (current : Endpoint) ->
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))) ->
    (subdivision : CCL.Riemann.PreparedSubdivisionModels.PreparedSubdivision
      parent.segment parent.within current owner) ->
    CCL.Riemann.PreparedSubdivisionModels.ParentPositions parent subdivision ->
      Coordinate
  | _current, _owner, .stop _ _, .stop _ _ _position => 1
  | current, owner, .next _ _ request _cached _ordered _small remaining,
      .next _ _ _ _ _ _ _ position remainingPositions =>
      min (directStepClearanceFloor parent current position owner request)
        (parentCongruenceFloor parent request.endpoint
          (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
            parent.within current owner request _small)
          remaining remainingPositions)

theorem parentCongruenceFloor_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential) :
    forall (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (subdivision : CCL.Riemann.PreparedSubdivisionModels.PreparedSubdivision
        parent.segment parent.within current owner)
      (positions : CCL.Riemann.PreparedSubdivisionModels.ParentPositions parent
        subdivision),
      0 < parentCongruenceFloor parent current owner subdivision positions
  | _current, _owner, .stop _ _, .stop _ _ _position => by
      change (0 : Coordinate) < 1
      decide
  | current, owner, .next _ _ request _cached _ordered small remaining,
      .next _ _ _ _ _ _ _ position remainingPositions =>
      lt_min (directStepClearanceFloor_positive parent current position owner
        request)
        (parentCongruenceFloor_positive parent request.endpoint
          (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
            parent.within current owner request small)
          remaining remainingPositions)

/-- One common upper variation bound for every step in a displayed fine
parent block. -/
inductive ParentSubdivisionVariationBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential) (bound : Coordinate) :
    (current : Endpoint) ->
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))) ->
    CCL.Riemann.PreparedSubdivisionModels.PreparedSubdivision parent.segment
      parent.within current owner -> Prop
  | stop
      (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter))) :
      ParentSubdivisionVariationBound parent bound current owner
        (.stop current owner)
  | next
      (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (request : StepRequest)
      (cached : CCL.Riemann.PreparedSheetContinuation.CachedSource
        parent.segment current owner request)
      (ordered : current.parameter <= request.endpoint.parameter)
      (small : CCL.Riemann.ClearSheetContinuation.variationBound
        parent.segment current.parameter request.endpoint.parameter <
          (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
            current owner request).track.initial.clearance.bound)
      (remaining : CCL.Riemann.PreparedSubdivisionModels.PreparedSubdivision
        parent.segment parent.within request.endpoint
          (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
            parent.within current owner request small))
      (head : CCL.Riemann.ClearSheetContinuation.variationBound parent.segment
        current.parameter request.endpoint.parameter <= bound)
      (tail : ParentSubdivisionVariationBound parent bound request.endpoint
        (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
          parent.within current owner request small) remaining) :
      ParentSubdivisionVariationBound parent bound current owner
        (.next current owner request cached ordered small remaining)

/-- A common variation bound below the block minimum discharges every local
congruence comparison. -/
theorem parentCongruenceSafe_of_bound_lt_floor {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential) (bound : Coordinate) :
    forall (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (subdivision : CCL.Riemann.PreparedSubdivisionModels.PreparedSubdivision
        parent.segment parent.within current owner)
      (positions : CCL.Riemann.PreparedSubdivisionModels.ParentPositions parent
        subdivision),
      ParentSubdivisionVariationBound parent bound current owner subdivision ->
      bound < parentCongruenceFloor parent current owner subdivision positions ->
        ParentCongruenceSafe parent current owner subdivision positions
  | current, owner, .stop _ _, .stop _ _ position, .stop _ _, _below =>
      .stop current owner position
  | current, owner, .next _ _ request cached ordered small remaining,
      .next _ _ _ _ _ _ _ position remainingPositions,
      .next _ _ _ _ _ _ _ head tail, below => by
      apply ParentCongruenceSafe.next current owner request cached ordered small
        remaining position remainingPositions
      · exact head.trans_lt (below.trans_le (min_le_left _ _))
      · exact parentCongruenceSafe_of_bound_lt_floor parent bound
          request.endpoint
          (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
            parent.within current owner request small)
          remaining remainingPositions tail
            (below.trans_le (min_le_right _ _))

/-- The owner-independent endpoint variation scan is retained by the
dependent tail constructed from `FreshMeshSafe`. -/
theorem parentSubdivisionVariationBound_ofFreshMeshSafe {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential) (bound : Coordinate) :
    forall (current : Endpoint)
      (prior : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (requests : List StepRequest)
      (safe : CCL.Riemann.PreparedSheetContinuation.FreshMeshSafe
        parent.segment current requests),
      CCL.Riemann.ClearSheetContinuation.Subdivision.EdgeVariationBound
        parent.segment bound current
          (CCL.Riemann.PreparedSheetContinuation.Subdivision.requestEndpoints
            requests) ->
      ParentSubdivisionVariationBound parent bound current
        prior
        (CCL.Riemann.PreparedSheetContinuation.Subdivision.ofFreshMeshSafe
          parent.segment parent.within current prior requests safe)
  | current, prior, [], _safe, _edges => .stop current prior
  | current, prior, request :: remaining, safe, edges => by
      let small : CCL.Riemann.ClearSheetContinuation.variationBound
          parent.segment current.parameter request.endpoint.parameter <
          (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
            current prior request).track.initial.clearance.bound :=
        safe.2.1.trans_le
          (CCL.Riemann.PreparedSheetContinuation.canonicalPredictedClearanceFloor_le_prepared
            parent.segment current prior request)
      apply ParentSubdivisionVariationBound.next current prior request
        (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
          parent.segment current prior request) safe.1 small
      · exact edges.2.1
      · exact parentSubdivisionVariationBound_ofFreshMeshSafe parent bound
          request.endpoint
          (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
            parent.within current prior request small)
          remaining safe.2.2 edges.2.2

/-- The same endpoint scan is retained by the complete first-owner mesh
constructor. -/
theorem parentSubdivisionVariationBound_ofMeshSafe {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential) (bound : Coordinate)
    (current : Endpoint)
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))) :
    forall (requests : List StepRequest)
      (safe : CCL.Riemann.PreparedSheetContinuation.MeshSafe parent.segment
        current owner requests),
      CCL.Riemann.ClearSheetContinuation.Subdivision.EdgeVariationBound
        parent.segment bound current
          (CCL.Riemann.PreparedSheetContinuation.Subdivision.requestEndpoints
            requests) ->
      ParentSubdivisionVariationBound parent bound current owner
        (CCL.Riemann.PreparedSheetContinuation.Subdivision.ofMeshSafe
          parent.segment parent.within current owner requests safe)
  | [], _safe, _edges => .stop current owner
  | request :: remaining, safe, edges => by
      apply ParentSubdivisionVariationBound.next current owner request
        (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
          parent.segment current owner request) safe.1 safe.2.1
      · exact edges.2.1
      · exact parentSubdivisionVariationBound_ofFreshMeshSafe parent bound
          request.endpoint
          (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
            parent.within current owner request safe.2.1)
          remaining safe.2.2 edges.2.2

/-- Exact common variation bound for the depth-`n` dyadic children of one
coarse parent. -/
def parentDyadicVariationBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential) (depth : Nat) : Coordinate :=
  CCL.FiniteGeometric.quarterRadius
    (CCL.Riemann.ClearSheetContinuation.variationBound parent.segment
      parent.left.parameter parent.request.endpoint.parameter) depth

/-- The finite congruence-clearance minimum computed on one concrete dyadic
parent block. -/
def parentDyadicCongruenceFloor {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive) : Coordinate :=
  parentCongruenceFloor parent parent.left parent.owner
    (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision parent depth
      rootDiameter rootDiameterPositive safe)
    (CCL.Riemann.PreparedSubdivisionModels.parentDyadicPositions parent proper
      depth rootDiameter rootDiameterPositive safe)

theorem parentDyadicCongruenceFloor_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive) :
    0 < parentDyadicCongruenceFloor parent proper depth rootDiameter
      rootDiameterPositive safe :=
  parentCongruenceFloor_positive parent parent.left parent.owner
    (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision parent depth
      rootDiameter rootDiameterPositive safe)
    (CCL.Riemann.PreparedSubdivisionModels.parentDyadicPositions parent proper
      depth rootDiameter rootDiameterPositive safe)

/-- Every accepted prepared dyadic child step satisfies its exact common
`4^-depth` variation estimate. -/
theorem parentDyadicSubdivisionVariationBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive) :
    ParentSubdivisionVariationBound parent
      (parentDyadicVariationBound parent depth) parent.left parent.owner
      (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision parent
        depth rootDiameter rootDiameterPositive safe) := by
  apply parentSubdivisionVariationBound_ofMeshSafe parent
    (parentDyadicVariationBound parent depth) parent.left parent.owner
    (CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
      parent.left parent.request.endpoint rootDiameter rootDiameterPositive)
    safe
  simpa only [
    CCL.Riemann.PreparedSheetContinuation.Subdivision.requestEndpoints_dyadicRequests,
    parentDyadicVariationBound]
    using
      (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets_edgeVariationBound
        parent.segment depth parent.left parent.request.endpoint parent.ordered)

/-- One displayed rational comparison between the dyadic variation modulus
and the computed block floor proves every congruence check in that block. -/
theorem parentDyadicCongruenceSafe_of_bound_lt_floor {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive)
    (below : parentDyadicVariationBound parent depth <
      parentDyadicCongruenceFloor parent proper depth rootDiameter
        rootDiameterPositive safe) :
    ParentCongruenceSafe parent parent.left parent.owner
      (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision parent
        depth rootDiameter rootDiameterPositive safe)
      (CCL.Riemann.PreparedSubdivisionModels.parentDyadicPositions parent proper
        depth rootDiameter rootDiameterPositive safe) :=
  parentCongruenceSafe_of_bound_lt_floor parent
    (parentDyadicVariationBound parent depth) parent.left parent.owner
      (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision parent
        depth rootDiameter rootDiameterPositive safe)
      (CCL.Riemann.PreparedSubdivisionModels.parentDyadicPositions parent proper
        depth rootDiameter rootDiameterPositive safe)
      (parentDyadicSubdivisionVariationBound parent depth rootDiameter
        rootDiameterPositive safe) below

/-- Executable Boolean form of the single block-level congruence comparison. -/
def parentDyadicCongruenceBoundAccepted {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive) : Bool :=
  decide (parentDyadicVariationBound parent depth <
    parentDyadicCongruenceFloor parent proper depth rootDiameter
      rootDiameterPositive safe)

theorem parentDyadicCongruenceSafe_of_accepted {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive)
    (accepted : parentDyadicCongruenceBoundAccepted parent proper depth
      rootDiameter rootDiameterPositive safe = true) :
    ParentCongruenceSafe parent parent.left parent.owner
      (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision parent
        depth rootDiameter rootDiameterPositive safe)
      (CCL.Riemann.PreparedSubdivisionModels.parentDyadicPositions parent proper
        depth rootDiameter rootDiameterPositive safe) :=
  parentDyadicCongruenceSafe_of_bound_lt_floor parent proper depth rootDiameter
    rootDiameterPositive safe (of_decide_eq_true accepted)

/-- Search depths are measured from the already sufficient prepared-mesh
depth, so every candidate automatically exists as a dependent subdivision. -/
def parentCandidateDepth {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential) (rootDiameter : Coordinate) (offset : Nat) : Nat :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
    parent.segment parent.left parent.request.endpoint rootDiameter + offset

/-- Prepared-mesh safety for every searched candidate depth. -/
theorem parentCandidateMeshSafe {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (offset : Nat) :
    CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner
        (parentCandidateDepth parent rootDiameter offset) rootDiameter
          rootDiameterPositive :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicMeshSafe_of_sufficientDepth_le
    parent.segment parent.left parent.request.endpoint parent.owner
      (parentCandidateDepth parent rootDiameter offset) rootDiameter
        rootDiameterPositive parent.ordered
          (Nat.le_add_right _ offset)

/-- One fully executable candidate test at a depth where the underlying
prepared dyadic mesh is already known to be safe. -/
def parentCandidateAccepted {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (offset : Nat) : Bool :=
  parentDyadicCongruenceBoundAccepted parent proper
    (parentCandidateDepth parent rootDiameter offset) rootDiameter
      rootDiameterPositive
        (parentCandidateMeshSafe parent rootDiameter rootDiameterPositive
          offset)

/-- The finite variation criterion proves that the executable seven-way
checker succeeds. -/
theorem tryParentStepSmalls_isSome_of_congruenceSafe {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential) :
    forall (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (subdivision : CCL.Riemann.PreparedSubdivisionModels.PreparedSubdivision
        parent.segment parent.within current owner)
      (positions : CCL.Riemann.PreparedSubdivisionModels.ParentPositions parent
        subdivision),
      ParentCongruenceSafe parent current owner subdivision positions ->
        (CCL.Riemann.PreparedSubdivisionModels.tryParentStepSmalls parent
          current owner subdivision positions).isSome = true
  | current, owner, .stop _ _, .stop _ _ position, .stop _ _ _ => rfl
  | current, owner, .next _ _ request cached ordered small remaining,
      .next _ _ _ _ _ _ _ position remainingPositions,
      .next _ _ _ _ _ _ _ _ _ below tail => by
      let stepSmall := directStepSmall_of_variation_lt_floor parent current
        position owner request below
      have tailAccepted := tryParentStepSmalls_isSome_of_congruenceSafe parent
        request.endpoint
        (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
          parent.within current owner request small)
        remaining remainingPositions tail
      cases checkedTail :
          CCL.Riemann.PreparedSubdivisionModels.tryParentStepSmalls parent
            request.endpoint
            (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
              parent.within current owner request small)
            remaining remainingPositions with
      | none =>
          simp only [checkedTail, Option.isSome] at tailAccepted
          cases tailAccepted
      | some checked =>
          simp only [CCL.Riemann.PreparedSubdivisionModels.tryParentStepSmalls,
            dif_pos stepSmall, checkedTail, Option.isSome]

/-- The same finite criterion proves success of the packaged dyadic-parent
checker. -/
theorem tryCheckedParentDyadic_isSome_of_congruenceSafe {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive)
    (congruenceSafe : ParentCongruenceSafe parent parent.left parent.owner
      (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision parent
        depth rootDiameter rootDiameterPositive safe)
      (CCL.Riemann.PreparedSubdivisionModels.parentDyadicPositions parent
        proper depth rootDiameter rootDiameterPositive safe)) :
    (CCL.Riemann.PreparedSubdivisionModels.tryCheckedParentDyadic parent proper
      depth rootDiameter rootDiameterPositive safe).isSome = true := by
  have accepted := tryParentStepSmalls_isSome_of_congruenceSafe parent
    parent.left parent.owner
    (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision parent
      depth rootDiameter rootDiameterPositive safe)
    (CCL.Riemann.PreparedSubdivisionModels.parentDyadicPositions parent
      proper depth rootDiameter rootDiameterPositive safe) congruenceSafe
  cases checkedSteps :
      CCL.Riemann.PreparedSubdivisionModels.tryParentStepSmalls parent
        parent.left parent.owner
        (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision parent
          depth rootDiameter rootDiameterPositive safe)
        (CCL.Riemann.PreparedSubdivisionModels.parentDyadicPositions parent
          proper depth rootDiameter rootDiameterPositive safe) with
  | none =>
      simp only [checkedSteps, Option.isSome] at accepted
      cases accepted
  | some stepSmalls =>
      simp only [CCL.Riemann.PreparedSubdivisionModels.tryCheckedParentDyadic,
        checkedSteps, Option.isSome]

/-- Constructively extract the exact checked dyadic witness whose finite
checker has been proved successful. -/
def checkedParentDyadicOfCongruenceSafe {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive)
    (congruenceSafe : ParentCongruenceSafe parent parent.left parent.owner
      (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision parent
        depth rootDiameter rootDiameterPositive safe)
      (CCL.Riemann.PreparedSubdivisionModels.parentDyadicPositions parent
        proper depth rootDiameter rootDiameterPositive safe)) :
    CCL.Riemann.PreparedSubdivisionModels.CheckedParentDyadic parent proper
      depth rootDiameter rootDiameterPositive safe :=
  let checked :=
    CCL.Riemann.PreparedSubdivisionModels.tryCheckedParentDyadic parent proper
      depth rootDiameter rootDiameterPositive safe
  checked.get (tryCheckedParentDyadic_isSome_of_congruenceSafe parent proper
    depth rootDiameter rootDiameterPositive safe congruenceSafe)

/-- Extract the checked dyadic parent block directly from the one executable
block-level comparison. -/
def checkedParentDyadicOfBoundAccepted {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive)
    (accepted : parentDyadicCongruenceBoundAccepted parent proper depth
      rootDiameter rootDiameterPositive safe = true) :
    CCL.Riemann.PreparedSubdivisionModels.CheckedParentDyadic parent proper
      depth rootDiameter rootDiameterPositive safe :=
  checkedParentDyadicOfCongruenceSafe parent proper depth rootDiameter
    rootDiameterPositive safe
      (parentDyadicCongruenceSafe_of_accepted parent proper depth rootDiameter
        rootDiameterPositive safe accepted)

/-- Successful result of the bounded candidate-depth search for one parent.
Only the offset and its verified Boolean comparison are stored; the dependent
mesh and coherence witnesses are reconstructed by computation. -/
structure CheckedParentCandidate {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) where
  offset : Nat
  accepted : parentCandidateAccepted parent proper rootDiameter
    rootDiameterPositive offset = true

namespace CheckedParentCandidate

/-- Concrete depth selected by a successful candidate. -/
def depth {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential}
    {proper : parent.left.parameter < parent.request.endpoint.parameter}
    {rootDiameter : Coordinate} {rootDiameterPositive : 0 < rootDiameter}
    (candidate : CheckedParentCandidate parent proper rootDiameter
      rootDiameterPositive) : Nat :=
  parentCandidateDepth parent rootDiameter candidate.offset

/-- Prepared-mesh safety reconstructed at the selected depth. -/
theorem meshSafe {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential}
    {proper : parent.left.parameter < parent.request.endpoint.parameter}
    {rootDiameter : Coordinate} {rootDiameterPositive : 0 < rootDiameter}
    (candidate : CheckedParentCandidate parent proper rootDiameter
      rootDiameterPositive) :
    CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner
        candidate.depth rootDiameter rootDiameterPositive :=
  parentCandidateMeshSafe parent rootDiameter rootDiameterPositive
    candidate.offset

/-- The exact dependent checked block reconstructed from a successful search
candidate. -/
def toCheckedParentDyadic {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential}
    {proper : parent.left.parameter < parent.request.endpoint.parameter}
    {rootDiameter : Coordinate} {rootDiameterPositive : 0 < rootDiameter}
    (candidate : CheckedParentCandidate parent proper rootDiameter
      rootDiameterPositive) :
    CCL.Riemann.PreparedSubdivisionModels.CheckedParentDyadic parent proper
      candidate.depth rootDiameter rootDiameterPositive candidate.meshSafe :=
  checkedParentDyadicOfBoundAccepted parent proper candidate.depth rootDiameter
    rootDiameterPositive candidate.meshSafe candidate.accepted

end CheckedParentCandidate

/-- Search offsets `0, ..., fuel` for the first accepted checked-parent
candidate.  The search is finite and executable. -/
def tryCheckedParentCandidateUpTo {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (fuel : Nat) -> Option
      (CheckedParentCandidate parent proper rootDiameter rootDiameterPositive)
  | 0 =>
      if accepted : parentCandidateAccepted parent proper rootDiameter
          rootDiameterPositive 0 = true then
        some ⟨0, accepted⟩
      else none
  | fuel + 1 =>
      match tryCheckedParentCandidateUpTo parent proper rootDiameter
          rootDiameterPositive fuel with
      | some candidate => some candidate
      | none =>
          if accepted : parentCandidateAccepted parent proper rootDiameter
              rootDiameterPositive (fuel + 1) = true then
            some ⟨fuel + 1, accepted⟩
          else none

/-- Acceptance at the final displayed offset proves that the bounded search
returns a candidate (possibly an earlier one). -/
theorem tryCheckedParentCandidateUpTo_isSome_of_lastAccepted {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    forall fuel : Nat,
      parentCandidateAccepted parent proper rootDiameter rootDiameterPositive
          fuel = true ->
        (tryCheckedParentCandidateUpTo parent proper rootDiameter
          rootDiameterPositive fuel).isSome = true
  | 0, accepted => by
      simp only [tryCheckedParentCandidateUpTo, dif_pos accepted,
        Option.isSome]
  | fuel + 1, accepted => by
      cases earlier : tryCheckedParentCandidateUpTo parent proper rootDiameter
          rootDiameterPositive fuel with
      | none =>
          simp only [tryCheckedParentCandidateUpTo, earlier,
            dif_pos accepted, Option.isSome]
      | some candidate =>
          simp only [tryCheckedParentCandidateUpTo, earlier, Option.isSome]

/-- The ordinary child-edge list computed by one checked dyadic parent mesh. -/
def childEdges {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.edge.segment parent.edge.left parent.edge.request.endpoint
          parent.edge.owner depth rootDiameter rootDiameterPositive)
    (centers : CCL.Riemann.PreparedSubdivisionModels.CenterStates curve
      differential parent.edge.sheet
      (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision
        parent.edge depth rootDiameter rootDiameterPositive safe)) :
    List (CenteredEdge curve differential) :=
  CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
    parent.edge.sheet
      (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision
        parent.edge depth rootDiameter rootDiameterPositive safe) centers

/-- A checked dyadic refinement of every edge in a finite centered path.
The child list is definitionally grouped parent by parent. -/
inductive CheckedRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    List (CenteredEdge curve differential) ->
      List (CenteredEdge curve differential) -> Type
  | nil : CheckedRefinement [] []
  | cons
      (parent : CenteredEdge curve differential)
      (proper : parent.edge.left.parameter <
        parent.edge.request.endpoint.parameter)
      (depth : Nat) (rootDiameter : Coordinate)
      (rootDiameterPositive : 0 < rootDiameter)
      (safe :
        CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
          parent.edge.segment parent.edge.left parent.edge.request.endpoint
            parent.edge.owner depth rootDiameter rootDiameterPositive)
      (checked : CCL.Riemann.PreparedSubdivisionModels.CheckedParentDyadic
        parent.edge proper depth rootDiameter rootDiameterPositive safe)
      (centers : CCL.Riemann.PreparedSubdivisionModels.CenterStates curve
        differential parent.edge.sheet
        (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision
          parent.edge depth rootDiameter rootDiameterPositive safe))
      {parents children : List (CenteredEdge curve differential)}
      (remaining : CheckedRefinement parents children) :
      CheckedRefinement (parent :: parents)
        (childEdges parent depth rootDiameter rootDiameterPositive safe centers ++
          children)

namespace CheckedRefinement

/-- Forget the dyadic construction after deriving the exact root-coherent
centered-edge refinement. -/
def toCenteredEdgeRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents children : List (CenteredEdge curve differential)},
      CheckedRefinement parents children ->
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdgeRefinement
          parents children
  | [], [], .nil => .nil
  | _, _, .cons parent proper depth rootDiameter rootDiameterPositive safe
      checked centers remaining =>
      .cons parent
        (CCL.Riemann.PreparedSubdivisionModels.rootChildBlockOfParentStepSmalls
          parent
          (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision
            parent.edge depth rootDiameter rootDiameterPositive safe)
          (CCL.Riemann.PreparedSubdivisionModels.parentDyadicPositions
            parent.edge proper depth rootDiameter rootDiameterPositive safe)
          checked.stepSmalls centers)
        (CCL.Riemann.PreparedSubdivisionModels.centeredEdges_displacement_eq_parent
          parent
          (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision
            parent.edge depth rootDiameter rootDiameterPositive safe)
          centers
          (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision_endpoint_eq
            parent.edge depth rootDiameter rootDiameterPositive safe))
        (toCenteredEdgeRefinement remaining)

/-- Every finite list of successful dyadic parent checks constructs the
integration kernel's compatible constant path refinement. -/
def toCompatible {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parents children : List (CenteredEdge curve differential)}
    (refinement : CheckedRefinement parents children) :
    CompatibleConstantPathRefinement
      (parents.map CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      (children.map CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model) :=
  refinement.toCenteredEdgeRefinement.toCompatible

end CheckedRefinement

/-- Every nonstationary parent edge in a finite centered path has positive
parameter width. -/
def AllParentsProper {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    List (CenteredEdge curve differential) -> Prop
  | [] => True
  | parent :: remaining =>
      parent.edge.left.parameter < parent.edge.request.endpoint.parameter /\
        AllParentsProper remaining

/-- Canonically centered child list reconstructed from one successful parent
candidate. -/
def candidateChildEdges {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential)
    (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (candidate : CheckedParentCandidate parent.edge proper rootDiameter
      rootDiameterPositive) : List (CenteredEdge curve differential) :=
  childEdges parent candidate.depth rootDiameter rootDiameterPositive
    candidate.meshSafe
    (CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates curve
      differential parent.edge.sheet
      (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision
        parent.edge candidate.depth rootDiameter rootDiameterPositive
          candidate.meshSafe))

/-- Existential result of refining a displayed finite parent list.  The child
list is stored as ordinary finite data and indexed by its complete compatible
refinement witness. -/
structure CheckedRefinementResult {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parents : List (CenteredEdge curve differential)) where
  children : List (CenteredEdge curve differential)
  refinement : CheckedRefinement parents children

namespace CheckedRefinementResult

/-- Integration-kernel compatibility carried by a successful whole-path
search. -/
def toCompatible {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parents : List (CenteredEdge curve differential)}
    (result : CheckedRefinementResult parents) :
    CompatibleConstantPathRefinement
      (parents.map CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      (result.children.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model) :=
  result.refinement.toCompatible

end CheckedRefinementResult

/-- Run the bounded congruence-depth search independently over every parent
edge of a finite centered path.  Success returns the computed child path and
its exact compatible refinement witness. -/
def tryCheckedRefinementUpTo {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (fuel : Nat) :
    (parents : List (CenteredEdge curve differential)) ->
    AllParentsProper parents -> Option (CheckedRefinementResult parents)
  | [], _proper => some ⟨[], .nil⟩
  | parent :: remaining, proper =>
      match tryCheckedParentCandidateUpTo parent.edge proper.1 rootDiameter
          rootDiameterPositive fuel with
      | none => none
      | some candidate =>
          match tryCheckedRefinementUpTo rootDiameter rootDiameterPositive fuel
              remaining proper.2 with
          | none => none
          | some tail =>
              let centers :=
                CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates
                  curve differential parent.edge.sheet
                  (CCL.Riemann.PreparedSubdivisionModels.parentDyadicSubdivision
                    parent.edge candidate.depth rootDiameter
                      rootDiameterPositive candidate.meshSafe)
              some
                { children := candidateChildEdges parent proper.1 rootDiameter
                    rootDiameterPositive candidate ++ tail.children
                  refinement :=
                    .cons parent proper.1 candidate.depth rootDiameter
                      rootDiameterPositive candidate.meshSafe
                      candidate.toCheckedParentDyadic centers tail.refinement }

end CCL.Riemann.PreparedDyadicRefinements
