import CCL.Riemann.PreparedSubdivisionModelCore

/-!
# Parent-refinement models for prepared subdivisions

Finite position, smallness, and direct-coherence certificates for refining one
prepared parent edge.  This layer is independent of automatic centre and
boundary-witness synthesis, allowing the two elaboration-heavy developments to
compile in parallel.
-/

namespace CCL.Riemann.PreparedSubdivisionModels

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchCuts
open CCL.Riemann.BranchCutLifts
open CCL.Riemann.LiftedPaths

/-- A finite position witness for every nonterminal edge in a fine prepared
subdivision lying inside one coarse parent. -/
inductive ParentPositions {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential) :
    {current : Endpoint} ->
      {owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter))} ->
      PreparedSubdivision parent.segment parent.within current owner -> Type
  | stop
      (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (position : ParentPosition parent current) :
      ParentPositions parent (.stop current owner)
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
      (remaining : PreparedSubdivision parent.segment parent.within
        request.endpoint
          (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
            parent.within current owner request small))
      (head : ParentPosition parent current)
      (tail : ParentPositions parent remaining) :
      ParentPositions parent
        (.next current owner request cached ordered small remaining)

namespace ParentPositions

/-- Position of the current endpoint, including the terminal endpoint of a
fine block. -/
def currentPosition {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : PreparedEdge curve differential}
    {current : Endpoint}
    {owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))}
    {subdivision : PreparedSubdivision parent.segment parent.within current
      owner} (positions : ParentPositions parent subdivision) :
    ParentPosition parent current :=
  match positions with
  | .stop _ _ position => position
  | .next _ _ _ _ _ _ _ head _ => head

end ParentPositions

/-- Every accepted prepared subdivision is parameter-monotone from its
current endpoint to its terminal endpoint. -/
theorem subdivision_start_le_endpoint
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))} :
    forall (subdivision : PreparedSubdivision segment within current owner),
      current.parameter <= subdivision.endpoint.parameter
  | .stop _ _ => le_refl _
  | .next _current _owner _request _cached ordered _small remaining =>
      ordered.trans (subdivision_start_le_endpoint remaining)

/-- Canonically position every endpoint of a monotone fine subdivision inside
a nondegenerate parent from bounds on its first and terminal parameters. -/
def parentPositionsOfBounds {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter) :
    (current : Endpoint) ->
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))) ->
    (subdivision : PreparedSubdivision parent.segment parent.within current
      owner) ->
    parent.left.parameter <= current.parameter ->
    subdivision.endpoint.parameter <= parent.request.endpoint.parameter ->
      ParentPositions parent subdivision
  | current, owner, .stop _ _, lower, upper =>
      .stop current owner (ParentPosition.ofBetween proper ⟨lower, upper⟩)
  | current, owner, .next _ _ request cached ordered small remaining, lower,
      upper =>
      let currentUpper :=
        (ordered.trans (subdivision_start_le_endpoint remaining)).trans upper
      .next current owner request cached ordered small remaining
        (ParentPosition.ofBetween proper ⟨lower, currentUpper⟩)
        (parentPositionsOfBounds parent proper request.endpoint
          (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
            parent.within current owner request small)
          remaining (lower.trans ordered) upper)

/-- A complete monotone subdivision with the same terminal parameter as its
parent obtains all local fractions automatically. -/
def parentPositionsOfEndpointEq {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (subdivision : PreparedSubdivision parent.segment parent.within
      parent.left parent.owner)
    (endpoint_eq : subdivision.endpoint.parameter =
      parent.request.endpoint.parameter) : ParentPositions parent subdivision :=
  parentPositionsOfBounds parent proper parent.left parent.owner subdivision
    (le_refl _) (by rw [endpoint_eq])

/-- The seven finite continuation-congruence comparisons for every edge in a
fine block, indexed by the canonical direct move supplied by its parent
position. -/
inductive ParentStepSmalls {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential) :
    {current : Endpoint} ->
      {owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter))} ->
      {subdivision : PreparedSubdivision parent.segment parent.within current
        owner} -> ParentPositions parent subdivision -> Type
  | stop
      (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (position : ParentPosition parent current) :
      ParentStepSmalls parent (.stop current owner position)
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
      (remaining : PreparedSubdivision parent.segment parent.within
        request.endpoint
          (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
            parent.within current owner request small))
      (position : ParentPosition parent current)
      (remainingPositions : ParentPositions parent remaining)
      (stepSmall :
        CCL.Riemann.PreparedSheetContinuation.Subdivision.DirectStepSmall
          parent.segment parent.left
            (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
              parent.left parent.owner parent.request)
            current position.directMoveSmall owner request)
      (tail : ParentStepSmalls parent remainingPositions) :
      ParentStepSmalls parent
        (.next current owner request cached ordered small remaining position
          remainingPositions)

/-- Executable checker for all seven-way congruence comparisons in one fine
parent block.  Success returns the exact dependent chain consumed by the
coherence constructor. -/
def tryParentStepSmalls {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential) :
    (current : Endpoint) ->
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))) ->
    (subdivision : PreparedSubdivision parent.segment parent.within current
      owner) ->
    (positions : ParentPositions parent subdivision) ->
      Option (ParentStepSmalls parent positions)
  | current, owner, .stop _ _, .stop _ _ position =>
      some (.stop current owner position)
  | current, owner, .next _ _ request cached ordered small remaining,
      .next _ _ _ _ _ _ _ position remainingPositions =>
      if stepSmall :
          CCL.Riemann.PreparedSheetContinuation.Subdivision.DirectStepSmall
            parent.segment parent.left
              (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
                parent.left parent.owner parent.request)
              current position.directMoveSmall owner request then
        match tryParentStepSmalls parent request.endpoint
            (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
              parent.within current owner request small)
            remaining remainingPositions with
        | none => none
        | some tail =>
            some (.next current owner request cached ordered small remaining
              position remainingPositions stepSmall tail)
      else none

/-- Boolean acceptance form of the complete finite parent-block congruence
check. -/
def parentStepSmallsAccepted {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential)
    {current : Endpoint}
    {owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))}
  (subdivision : PreparedSubdivision parent.segment parent.within current
      owner) (positions : ParentPositions parent subdivision) : Bool :=
  (tryParentStepSmalls parent current owner subdivision positions).isSome

/-- The prepared dyadic child subdivision of one coarse parent edge. -/
def parentDyadicSubdivision {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner depth
        rootDiameter rootDiameterPositive) :
    PreparedSubdivision parent.segment parent.within parent.left parent.owner :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.checkedDyadic
    parent.segment parent.within parent.left parent.request.endpoint
      parent.owner depth rootDiameter rootDiameterPositive safe

/-- The locally checked dyadic subdivision ends at the coarse parent's exact
right endpoint. -/
theorem parentDyadicSubdivision_endpoint_eq {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner depth
        rootDiameter rootDiameterPositive) :
    (parentDyadicSubdivision parent depth rootDiameter rootDiameterPositive
      safe).endpoint.parameter = parent.request.endpoint.parameter := by
  apply congrArg (fun endpoint : Endpoint => endpoint.parameter)
  exact CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic_endpoint
    parent.segment parent.within parent.left parent.request.endpoint
      parent.owner depth rootDiameter rootDiameterPositive
        (CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic_eq_some_checkedDyadic
          parent.segment parent.within parent.left parent.request.endpoint
            parent.owner depth rootDiameter rootDiameterPositive safe)

/-- Canonical local fractions for every endpoint of the parent's prepared
dyadic child mesh. -/
def parentDyadicPositions {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner depth
        rootDiameter rootDiameterPositive) :
    ParentPositions parent
      (parentDyadicSubdivision parent depth rootDiameter rootDiameterPositive
        safe) :=
  parentPositionsOfEndpointEq parent proper
    (parentDyadicSubdivision parent depth rootDiameter rootDiameterPositive
      safe)
    (parentDyadicSubdivision_endpoint_eq parent depth rootDiameter
      rootDiameterPositive safe)

/-- Successful result of the executable congruence checker on one prepared
dyadic child block. -/
structure CheckedParentDyadic {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner depth
        rootDiameter rootDiameterPositive) where
  stepSmalls : ParentStepSmalls parent
    (parentDyadicPositions parent proper depth rootDiameter
      rootDiameterPositive safe)

/-- Run the complete finite congruence checker on a prepared dyadic child
mesh. -/
def tryCheckedParentDyadic {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner depth
        rootDiameter rootDiameterPositive) :
    Option (CheckedParentDyadic parent proper depth rootDiameter
      rootDiameterPositive safe) :=
  match tryParentStepSmalls parent parent.left parent.owner
      (parentDyadicSubdivision parent depth rootDiameter rootDiameterPositive
        safe)
      (parentDyadicPositions parent proper depth rootDiameter
        rootDiameterPositive safe) with
  | none => none
  | some stepSmalls => some ⟨stepSmalls⟩

/-- Initial direct zero move from the parent's prepared source is equivalent
to the inherited owner with which the fine block starts. -/
def parentInitialRootEquivalent {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential)
    (sourceSmall :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DirectMoveSmall
        parent.segment parent.left
          (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
            parent.left parent.owner parent.request) parent.left) :
    CCL.Riemann.PreparedSheetContinuation.Subdivision.RootEquivalentAt
      parent.segment parent.left
        (CCL.Riemann.PreparedSheetContinuation.Subdivision.directOwnerAt
          parent.left
          (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
            parent.left parent.owner parent.request)
          parent.left sourceSmall)
        parent.owner :=
  { firstName := CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
      (parent.segment.pointAt_eval_ne_zero parent.left.parameter
        parent.left.inside)
      (CCL.Riemann.PreparedSheetContinuation.Subdivision.directOwnerAt
        parent.left
        (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
          parent.left parent.owner parent.request)
        parent.left sourceSmall)
    secondName := CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
      (parent.segment.pointAt_eval_ne_zero parent.left.parameter
        parent.left.inside) parent.owner
    equivalent := CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_advance_same
        (parent.segment.pointAt_eval_ne_zero parent.left.parameter
          parent.left.inside)
        (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
          parent.left parent.owner parent.request) sourceSmall.proof).symm
      (CCL.Riemann.PreparedSheetContinuation.sourceRootEquivalent
        parent.segment parent.left parent.owner parent.request).symm
    first_eq := rfl
    second_eq := rfl }

/-- Compute the complete direct-coherence chain from the finite seven-way
smallness record.  Each next endpoint relation is derived by the continuation
composition theorem rather than supplied as certificate data. -/
def directlyCoherentOfParentStepSmalls {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential) :
    (current : Endpoint) ->
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))) ->
    (subdivision : PreparedSubdivision parent.segment parent.within current
      owner) ->
    (positions : ParentPositions parent subdivision) ->
    (currentEquivalent :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.RootEquivalentAt
        parent.segment current
          (CCL.Riemann.PreparedSheetContinuation.Subdivision.directOwnerAt
            parent.left
            (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
              parent.left parent.owner parent.request)
            current positions.currentPosition.directMoveSmall)
          owner) ->
    (stepSmalls : ParentStepSmalls parent positions) ->
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DirectlyCoherent
        parent.segment parent.within parent.left
          (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
            parent.left parent.owner parent.request)
          positions.currentPosition.directMoveSmall owner currentEquivalent
            subdivision
  | current, owner, .stop _ _, .stop _ _ position, currentEquivalent,
      .stop _ _ _ =>
      .stop current position.directMoveSmall owner currentEquivalent
  | current, owner, .next _ _ request cached ordered small remaining,
      .next _ _ _ _ _ _ _ position remainingPositions, currentEquivalent,
      .next _ _ _ _ _ _ _ _ _ stepSmall tail =>
      let sourceNextSmall :=
        remainingPositions.currentPosition.directMoveSmall
      let nextEquivalent :=
        CCL.Riemann.PreparedSheetContinuation.Subdivision.directNextRootEquivalent
          parent.segment parent.within parent.left
            (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
              parent.left parent.owner parent.request)
            current position.directMoveSmall owner currentEquivalent request
              small sourceNextSmall stepSmall
      .next current position.directMoveSmall owner currentEquivalent request
        cached ordered small remaining sourceNextSmall stepSmall
          (directlyCoherentOfParentStepSmalls parent request.endpoint
            (CCL.Riemann.PreparedSheetContinuation.advance parent.segment
              parent.within current owner request small)
            remaining remainingPositions nextEquivalent tail)

/-- Specialize the recursive constructor to a fine block beginning at the
coarse parent's own inherited owner. -/
def directlyCoherentParentBlock {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential)
    (subdivision : PreparedSubdivision parent.segment parent.within
      parent.left parent.owner)
    (positions : ParentPositions parent subdivision)
    (stepSmalls : ParentStepSmalls parent positions) :
    CCL.Riemann.PreparedSheetContinuation.Subdivision.DirectlyCoherent
      parent.segment parent.within parent.left
        (CCL.Riemann.PreparedSheetContinuation.prepared parent.segment
          parent.left parent.owner parent.request)
        positions.currentPosition.directMoveSmall parent.owner
          (parentInitialRootEquivalent parent
            positions.currentPosition.directMoveSmall)
          subdivision :=
  directlyCoherentOfParentStepSmalls parent parent.left parent.owner
    subdivision positions
    (parentInitialRootEquivalent parent
      positions.currentPosition.directMoveSmall) stepSmalls

/-- Fold direct root coherence and finite parent positions into the exact
`RootChildBlock` consumed by comparison-aware constant integration. -/
def rootChildBlockOfDirectlyCoherent {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential)
    {current : Endpoint}
    (sourceCurrentSmall :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DirectMoveSmall
        parent.edge.segment parent.edge.left
          (CCL.Riemann.PreparedSheetContinuation.prepared parent.edge.segment
            parent.edge.left parent.edge.owner parent.edge.request) current)
    (owner : Owner
      (curve.polynomial.eval (parent.edge.segment.pointAt current.parameter)))
    (currentEquivalent :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.RootEquivalentAt
        parent.edge.segment current
          (CCL.Riemann.PreparedSheetContinuation.Subdivision.directOwnerAt
            parent.edge.left
            (CCL.Riemann.PreparedSheetContinuation.prepared parent.edge.segment
              parent.edge.left parent.edge.owner parent.edge.request)
            current sourceCurrentSmall)
          owner)
    (subdivision : PreparedSubdivision parent.edge.segment parent.edge.within
      current owner)
    (coherent :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DirectlyCoherent
        parent.edge.segment parent.edge.within parent.edge.left
          (CCL.Riemann.PreparedSheetContinuation.prepared parent.edge.segment
            parent.edge.left parent.edge.owner parent.edge.request)
          sourceCurrentSmall owner currentEquivalent subdivision)
    (positions : ParentPositions parent.edge subdivision)
    (centers : CenterStates curve differential parent.edge.sheet subdivision) :
    RootChildBlock parent
      (centeredEdges curve differential parent.edge.sheet subdivision centers) :=
  match coherent, positions, centers with
  | .stop _ _ _ _, .stop _ _ _, _ => .nil
  | .next current sourceSmall owner equivalent request cached ordered
        childSmall remaining sourceNextSmall stepSmall tail,
      .next _ _ _ _ _ _ _ position remainingPositions, centers =>
      .cons
        (rootChildAtOfDirectStep parent current owner request cached ordered
          childSmall centers.1 sourceSmall equivalent position)
        (rootChildBlockOfDirectlyCoherent parent sourceNextSmall
          (CCL.Riemann.PreparedSheetContinuation.advance parent.edge.segment
            parent.edge.within current owner request childSmall)
          (CCL.Riemann.PreparedSheetContinuation.Subdivision.directNextRootEquivalent
            parent.edge.segment parent.edge.within parent.edge.left
              (CCL.Riemann.PreparedSheetContinuation.prepared
                parent.edge.segment parent.edge.left parent.edge.owner
                  parent.edge.request)
              current sourceSmall owner equivalent request childSmall
                sourceNextSmall stepSmall)
          remaining tail remainingPositions centers.2)

/-- Finite positions plus the seven-way edge checks construct the complete
root-coherent child block; callers no longer supply any root equivalence. -/
def rootChildBlockOfParentStepSmalls {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential)
    (subdivision : PreparedSubdivision parent.edge.segment parent.edge.within
      parent.edge.left parent.edge.owner)
    (positions : ParentPositions parent.edge subdivision)
    (stepSmalls : ParentStepSmalls parent.edge positions)
    (centers : CenterStates curve differential parent.edge.sheet subdivision) :
    RootChildBlock parent
      (centeredEdges curve differential parent.edge.sheet subdivision centers) :=
  rootChildBlockOfDirectlyCoherent parent
    positions.currentPosition.directMoveSmall parent.edge.owner
      (parentInitialRootEquivalent parent.edge
        positions.currentPosition.directMoveSmall)
      subdivision
      (directlyCoherentParentBlock parent.edge subdivision positions stepSmalls)
      positions centers

/-- One coarse edge and one complete fine block form a centered-edge
refinement once their terminal parameters agree. -/
def singleParentRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential)
    (subdivision : PreparedSubdivision parent.edge.segment parent.edge.within
      parent.edge.left parent.edge.owner)
    (positions : ParentPositions parent.edge subdivision)
    (stepSmalls : ParentStepSmalls parent.edge positions)
    (centers : CenterStates curve differential parent.edge.sheet subdivision)
    (endpoint_eq : subdivision.endpoint.parameter =
      parent.edge.request.endpoint.parameter) :
    CenteredEdgeRefinement [parent]
      (centeredEdges curve differential parent.edge.sheet subdivision centers) := by
  let block := rootChildBlockOfParentStepSmalls parent subdivision positions
    stepSmalls centers
  have displacement := centeredEdges_displacement_eq_parent parent subdivision
    centers endpoint_eq
  simpa only [List.append_nil] using
    CenteredEdgeRefinement.cons parent block displacement
      (CenteredEdgeRefinement.nil (curve := curve)
        (differential := differential))

/-- The integration kernel's compatible constant refinement constructed from
one fully checked parent block. -/
def compatibleSingleParentRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential)
    (subdivision : PreparedSubdivision parent.edge.segment parent.edge.within
      parent.edge.left parent.edge.owner)
    (positions : ParentPositions parent.edge subdivision)
    (stepSmalls : ParentStepSmalls parent.edge positions)
    (centers : CenterStates curve differential parent.edge.sheet subdivision)
    (endpoint_eq : subdivision.endpoint.parameter =
      parent.edge.request.endpoint.parameter) :
    CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement
      [parent.model]
      ((centeredEdges curve differential parent.edge.sheet subdivision
        centers).map CenteredEdge.model) := by
  simpa only [List.map_cons, List.map_nil] using
    (singleParentRefinement parent subdivision positions stepSmalls centers
      endpoint_eq).toCompatible

namespace CheckedParentDyadic

/-- A successful dyadic parent check constructs the integration kernel's
compatible refinement for any displayed centre choices. -/
def compatible {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : PreparedEdge curve differential}
    {proper : parent.left.parameter < parent.request.endpoint.parameter}
    {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {safe : CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner depth
        rootDiameter rootDiameterPositive}
    (checked : CheckedParentDyadic parent proper depth rootDiameter
      rootDiameterPositive safe)
    (parentCenter :
      CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState parent)
    (centers : CenterStates curve differential parent.sheet
      (parentDyadicSubdivision parent depth rootDiameter rootDiameterPositive
        safe)) :
    CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement
      [CenteredEdge.model { edge := parent, center := parentCenter }]
      ((centeredEdges curve differential parent.sheet
        (parentDyadicSubdivision parent depth rootDiameter rootDiameterPositive
          safe) centers).map CenteredEdge.model) :=
  compatibleSingleParentRefinement
    { edge := parent, center := parentCenter }
    (parentDyadicSubdivision parent depth rootDiameter rootDiameterPositive safe)
    (parentDyadicPositions parent proper depth rootDiameter
      rootDiameterPositive safe)
    checked.stepSmalls centers
    (parentDyadicSubdivision_endpoint_eq parent depth rootDiameter
      rootDiameterPositive safe)

end CheckedParentDyadic

end CCL.Riemann.PreparedSubdivisionModels
