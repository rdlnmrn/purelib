import CCL.Riemann.PreparedSubdivisionModelCore

/-!
# Automatic models for prepared subdivisions

Executable canonical centres, boundary witnesses, and certification wrappers
for a complete prepared subdivision.  This layer depends only on the shared
model core, not on the separate parent-refinement proof layer.
-/

namespace CCL.Riemann.PreparedSubdivisionModels

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchCuts
open CCL.Riemann.BranchCutLifts
open CCL.Riemann.LiftedPaths

/-- The canonical centre family obtained from each edge's cached rational
root-box anchor, with the prepared base reading as a total fallback. -/
def canonicalCenterStates {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision : PreparedSubdivision segment within left owner) ->
      CenterStates curve differential sheet subdivision
  | .stop _ _ => ()
  | .next left owner request cached ordered small remaining =>
      let head := edgeOfStep curve differential segment within left owner
        request cached ordered small sheet
      (CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState.canonical
          head,
        canonicalCenterStates curve differential sheet remaining)

/-- Evaluate the sharp canonical process-ball lower endpoint directly over
the dependent subdivision spine.  The direct fold avoids first materializing
the large intermediate centre and edge lists used by the proof-facing model
presentation. -/
def canonicalBallIntegralRealLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    PreparedSubdivision segment within left owner -> Coordinate
  | .stop _ _ => 0
  | .next current owner request cached ordered small remaining =>
      let edge := edgeOfStep curve differential segment within current owner
        request cached ordered small sheet
      let center :=
        CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState.canonical
          edge
      edge.centeredBallIntegralRealDyadicLower center +
        canonicalBallIntegralRealLower curve differential sheet remaining

/-- Direct sharp lower endpoint for the negative real projection. -/
def canonicalBallNegatedIntegralRealLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    PreparedSubdivision segment within left owner -> Coordinate
  | .stop _ _ => 0
  | .next current owner request cached ordered small remaining =>
      let edge := edgeOfStep curve differential segment within current owner
        request cached ordered small sheet
      let center :=
        CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState.canonical
          edge
      edge.centeredBallNegatedIntegralRealDyadicLower center +
        canonicalBallNegatedIntegralRealLower curve differential sheet remaining

theorem canonicalBallIntegralRealLower_eq_centeredEdges {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall subdivision : PreparedSubdivision segment within left owner,
      canonicalBallIntegralRealLower curve differential sheet subdivision =
        centeredEdgesBallIntegralRealLower
          (centeredEdges curve differential sheet subdivision
            (canonicalCenterStates curve differential sheet subdivision))
  | .stop _ _ => rfl
  | .next current owner request cached ordered small remaining => by
      simp only [canonicalBallIntegralRealLower, centeredEdges,
        canonicalCenterStates, centeredEdgesBallIntegralRealLower,
        List.foldr_cons, CenteredEdge.ballIntegralRealLower]
      rw [canonicalBallIntegralRealLower_eq_centeredEdges curve differential
        sheet remaining]
      rfl

theorem canonicalBallNegatedIntegralRealLower_eq_centeredEdges {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall subdivision : PreparedSubdivision segment within left owner,
      canonicalBallNegatedIntegralRealLower curve differential sheet subdivision =
        centeredEdgesBallNegatedIntegralRealLower
          (centeredEdges curve differential sheet subdivision
            (canonicalCenterStates curve differential sheet subdivision))
  | .stop _ _ => rfl
  | .next current owner request cached ordered small remaining => by
      simp only [canonicalBallNegatedIntegralRealLower, centeredEdges,
        canonicalCenterStates, centeredEdgesBallNegatedIntegralRealLower,
        List.foldr_cons, CenteredEdge.ballNegatedIntegralRealLower]
      rw [canonicalBallNegatedIntegralRealLower_eq_centeredEdges curve
        differential sheet remaining]
      rfl

theorem canonicalBallIntegralRealLower_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner)
    (exponentZero : differential.exponent = 0) :
    canonicalBallIntegralRealLower curve differential sheet subdivision <=
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((centeredEdges curve differential sheet subdivision
          (canonicalCenterStates curve differential sheet subdivision)).map
            CenteredEdge.model)).integralSample.re := by
  rw [canonicalBallIntegralRealLower_eq_centeredEdges curve differential sheet
    subdivision]
  exact centeredEdgesBallIntegralRealLower_le exponentZero _

theorem canonicalBallNegatedIntegralRealLower_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner)
    (exponentZero : differential.exponent = 0) :
    canonicalBallNegatedIntegralRealLower curve differential sheet subdivision <=
      -(CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((centeredEdges curve differential sheet subdivision
          (canonicalCenterStates curve differential sheet subdivision)).map
            CenteredEdge.model)).integralSample.re := by
  rw [canonicalBallNegatedIntegralRealLower_eq_centeredEdges curve differential
    sheet subdivision]
  exact centeredEdgesBallNegatedIntegralRealLower_le exponentZero _

private def boundaryWitness {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    (left : Endpoint)
    (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter)))
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
    (sheet : Fin 2) : BoundaryWitness :=
  let parent := edgeOfStep curve differential segment within left owner request
    cached ordered small sheet
  let child := edgeOfStep curve differential segment within request.endpoint
    (CCL.Riemann.PreparedSheetContinuation.advance segment within left owner
      request small) nextRequest nextCached nextOrdered nextSmall sheet
  { parentName := (parent.coefficient 1 endpointInside).name
    childName := (child.coefficient 0 child.baseInside).name
    equivalent :=
      CCL.Riemann.PreparedBoundaryEquivalence.adjacentCoefficientEquivalent
        curve differential segment within left owner request cached ordered small
          nextRequest nextCached nextOrdered nextSmall sheet }

/-- A typed continuation from the edge immediately preceding the current
dependent subdivision.  Its argument indices are exactly the computed current
endpoint and owner, so applying it to the current edge requires no equality
transport. -/
private abbrev BoundaryBuilder {genus : Nat}
    (curve : HyperellipticCurve genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (left : Endpoint)
    (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))) :=
  (request : StepRequest) ->
    (cached : CCL.Riemann.PreparedSheetContinuation.CachedSource segment left
      owner request) ->
      (ordered : left.parameter <= request.endpoint.parameter) ->
      (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
            request).track.initial.clearance.bound) -> BoundaryWitness

private def automaticBoundaryWitnessesFrom {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (previous : Option
      (BoundaryBuilder curve segment left owner)) :
    PreparedSubdivision segment within left owner -> List BoundaryWitness
  | .stop _ _ => []
  | .next left owner request cached ordered small remaining =>
      let current : BoundaryBuilder curve segment request.endpoint
          (CCL.Riemann.PreparedSheetContinuation.advance segment within left
            owner request small) :=
        fun nextRequest nextCached nextOrdered nextSmall =>
          boundaryWitness curve differential left owner request cached ordered
            small nextRequest nextCached nextOrdered nextSmall sheet
      let tail := automaticBoundaryWitnessesFrom curve differential sheet
        (some current) remaining
      match previous with
      | none => tail
      | some build => build request cached ordered small :: tail

/-- Every successful dependent subdivision therefore computes the complete
finite list of its adjacent boundary equivalences without external matching
hypotheses. -/
def automaticBoundaryWitnesses {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    List BoundaryWitness :=
  automaticBoundaryWitnessesFrom curve differential sheet
    none subdivision

private theorem automaticBoundaryWitnessesFrom_some_length {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner)
    (builder : BoundaryBuilder curve segment left owner) :
    (automaticBoundaryWitnessesFrom curve differential sheet (some builder)
      subdivision).length = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left owner request cached ordered small remaining
      inductionHypothesis =>
      simp only [automaticBoundaryWitnessesFrom,
        CCL.Riemann.PreparedSheetContinuation.Subdivision.stepCount,
        List.length_cons]
      exact congrArg Nat.succ (inductionHypothesis _)

/-- There is one automatically proved boundary equivalence between each pair
of consecutive edges, hence exactly one fewer witness than nonempty edges. -/
@[simp] theorem automaticBoundaryWitnesses_length {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    (automaticBoundaryWitnesses curve differential sheet subdivision).length =
      subdivision.stepCount.pred := by
  cases subdivision with
  | stop => rfl
  | next left owner request cached ordered small remaining =>
      simp only [automaticBoundaryWitnesses,
        automaticBoundaryWitnessesFrom,
        CCL.Riemann.PreparedSheetContinuation.Subdivision.stepCount]
      exact automaticBoundaryWitnessesFrom_some_length curve differential sheet
        remaining _

/-- A typed continuation that chooses the current edge's coefficient centre
from the immediately preceding edge. -/
private abbrev CenterBuilder {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter)))
    (sheet : Fin 2) :=
  (request : StepRequest) ->
    (cached : CCL.Riemann.PreparedSheetContinuation.CachedSource segment left
      owner request) ->
      (ordered : left.parameter <= request.endpoint.parameter) ->
      (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
            request).track.initial.clearance.bound) ->
        CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState
          (edgeOfStep curve differential segment within left owner request
            cached ordered small sheet)

private def automaticAlignedCenterStatesFrom {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (previous : Option
      (CenterBuilder curve differential segment within left owner sheet)) :
    (subdivision : PreparedSubdivision segment within left owner) ->
      CenterStates curve differential sheet subdivision
  | .stop _ _ => ()
  | .next left owner request cached ordered small remaining =>
      let parent := edgeOfStep curve differential segment within left owner
        request cached ordered small sheet
      let center :
          CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState parent :=
        match previous with
        | none =>
            CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState.canonical
              parent
        | some build => build request cached ordered small
      let current : CenterBuilder curve differential segment within
          request.endpoint
          (CCL.Riemann.PreparedSheetContinuation.advance segment within left
            owner request small) sheet :=
        fun nextRequest nextCached nextOrdered nextSmall =>
          let child := edgeOfStep curve differential segment within
            request.endpoint
            (CCL.Riemann.PreparedSheetContinuation.advance segment within left
              owner request small) nextRequest nextCached nextOrdered nextSmall
                sheet
          let query :=
            CCL.Riemann.PreparedConstantModels.PreparedEdge.QueryState.canonical
              parent 1 endpointInside
          CCL.Riemann.PreparedConstantModels.PreparedEdge.alignedChildAt parent
            child query
              (CCL.Riemann.PreparedBoundaryEquivalence.adjacentCoefficientEquivalent
                curve differential segment within left owner request cached
                  ordered small nextRequest nextCached nextOrdered nextSmall sheet)
      (center, automaticAlignedCenterStatesFrom curve differential sheet
        (some current) remaining)

/-- Choose the first edge centre canonically and every later edge centre by a
finite operational comparison with its predecessor's right-end coefficient.
All comparisons are generated from the accepted subdivision itself. -/
def automaticAlignedCenterStates {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    CenterStates curve differential sheet subdivision :=
  automaticAlignedCenterStatesFrom curve differential sheet none subdivision

def certifySubdivision {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision : PreparedSubdivision segment within left owner) ->
      CertifiedSubdivision curve differential sheet subdivision
  | .stop endpoint owner =>
      { cells := []
        certificates := .nil _ }
  | .next left owner request cached ordered small remaining => by
      let head : CCL.Riemann.PreparedConstantModels.PreparedEdge curve
          differential :=
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
      let tail := certifySubdivision curve differential sheet remaining
      exact
        { cells := head.model :: tail.cells
          certificates := .cons
            (by
              change head.model.start = segment.pointAt left.parameter
              change head.localSegment.pointAt 0 = segment.pointAt left.parameter
              rw [head.localSegment.pointAt_zero])
            (by
              change head.model.finish =
                segment.pointAt request.endpoint.parameter
              change head.localSegment.pointAt 1 =
                segment.pointAt request.endpoint.parameter
              rw [head.localSegment.pointAt_one])
            head.validCertificate tail.certificates }

/-- Fold a chosen certified centre family into a uniformly certified
constant path model.  This is the comparison-aware counterpart of
`certifySubdivision`: every cell keeps the same geometry and inherited sheet,
but its rational constant may be selected at a later finite coefficient
state. -/
def certifyCenteredSubdivision {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision : PreparedSubdivision segment within left owner) ->
      CenterStates curve differential sheet subdivision ->
        CertifiedSubdivision curve differential sheet subdivision
  | .stop endpoint owner, _ =>
      { cells := []
        certificates := .nil _ }
  | .next left owner request cached ordered small remaining, centers => by
      let head : CCL.Riemann.PreparedConstantModels.PreparedEdge curve
          differential :=
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
      let tail := certifyCenteredSubdivision curve differential sheet
        remaining centers.2
      exact
        { cells := head.centeredModel centers.1 :: tail.cells
          certificates := .cons
            (by
              change (head.centeredModel centers.1).start =
                segment.pointAt left.parameter
              change head.localSegment.pointAt 0 =
                segment.pointAt left.parameter
              rw [head.localSegment.pointAt_zero])
            (by
              change (head.centeredModel centers.1).finish =
                segment.pointAt request.endpoint.parameter
              change head.localSegment.pointAt 1 =
                segment.pointAt request.endpoint.parameter
              rw [head.localSegment.pointAt_one])
            (head.centeredValidCertificate curve differential centers.1)
            tail.certificates }

/-- The ordinary centred-edge list exposes exactly the cells folded by the
uniform subdivision certifier. -/
theorem centeredEdges_models {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision : PreparedSubdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      (centeredEdges curve differential sheet subdivision centers).map
          CenteredEdge.model =
        (certifyCenteredSubdivision curve differential sheet subdivision
          centers).cells
  | .stop _ _, _ => rfl
  | .next left owner request cached ordered small remaining, centers => by
      simp only [centeredEdges, List.map_cons, certifyCenteredSubdivision,
        CenteredEdge.model]
      rw [centeredEdges_models curve differential sheet remaining centers.2]
      rfl

/-- The automatically boundary-aligned finite model, with uniform algebraic
semantics retained cell by cell. -/
def certifyAutomaticallyAlignedSubdivision {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    CertifiedSubdivision curve differential sheet subdivision :=
  certifyCenteredSubdivision curve differential sheet subdivision
    (automaticAlignedCenterStates curve differential sheet subdivision)

/-- Every comparison-aware prepared subdivision is cellwise Gaussian
constant.  The displayed coefficient is exactly the certified centre selected
for that edge. -/
def certifyCenteredSubdivision_constantCells {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision : PreparedSubdivision segment within left owner) ->
      (centers : CenterStates curve differential sheet subdivision) ->
        CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells
          (certifyCenteredSubdivision curve differential sheet subdivision
            centers).cells
  | .stop _ _, _ => .nil
  | .next left owner _request _cached _ordered _small remaining, centers =>
      .cons
        { coefficient := centers.1.value
          polynomial_eq := rfl }
        (certifyCenteredSubdivision_constantCells curve differential sheet
          remaining centers.2)

/-- Automatic centre alignment therefore produces a constant-cell model
without an additional certificate field. -/
def certifyAutomaticallyAlignedSubdivision_constantCells {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells
      (certifyAutomaticallyAlignedSubdivision curve differential sheet
        subdivision).cells :=
  certifyCenteredSubdivision_constantCells curve differential sheet
    subdivision
      (automaticAlignedCenterStates curve differential sheet subdivision)

/-- The comparison-aware fold remains cell-for-cell with the accepted finite
subdivision. -/
@[simp] theorem certifyCenteredSubdivision_cellCount {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner)
    (centers : CenterStates curve differential sheet subdivision) :
    (certifyCenteredSubdivision curve differential sheet subdivision
      centers).cells.length = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left owner request cached ordered small remaining
      inductionHypothesis =>
      exact congrArg Nat.succ (inductionHypothesis centers.2)

/-- Automatic alignment changes coefficient states, not the accepted finite
mesh or its cell count. -/
@[simp] theorem certifyAutomaticallyAlignedSubdivision_cellCount {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    (certifyAutomaticallyAlignedSubdivision curve differential sheet
      subdivision).cells.length = subdivision.stepCount :=
  certifyCenteredSubdivision_cellCount curve differential sheet subdivision
    (automaticAlignedCenterStates curve differential sheet subdivision)

@[simp] theorem certifySubdivision_cellCount {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    (certifySubdivision curve differential sheet subdivision).cells.length =
      subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left owner request cached ordered small remaining
      inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

def pathModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    {sheet : Fin 2}
    {subdivision : PreparedSubdivision segment within left owner}
    (certified : CertifiedSubdivision curve differential sheet subdivision) :
    PathModel :=
  ⟨certified.cells⟩

end CCL.Riemann.PreparedSubdivisionModels
