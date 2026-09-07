import CCL.Riemann.PreparedDyadicRefinements
import CCL.Riemann.PreparedClearPathModels

/-!
# Direct dyadic refinements of prepared edges

Every child in this module is anchored directly to its coarse parent's fixed
prepared occurrence.  Consequently no staged child-owner congruence search is
needed: the accepted coarse move supplies every direct point query, while the
uniform preparation floor supplies every sufficiently fine child move.
-/

namespace CCL.Riemann.PreparedDirectDyadicRefinements

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchCuts
open CCL.Riemann.LiftedPaths

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

/-- Reinterpret the differential-independent prepared geometry of one edge
for another algebraic differential. -/
def recastPreparedEdge {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (edge : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve source) :
    CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve target where
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

@[simp] theorem recastPreparedEdge_self {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (edge : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential) :
    recastPreparedEdge differential edge = edge := by
  cases edge
  rfl

/-- Canonically recenter the same prepared geometric edge for another
differential. -/
def recastCenteredEdge {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (centered : CenteredEdge curve source) : CenteredEdge curve target :=
  let edge := recastPreparedEdge target centered.edge
  { edge := edge
    center :=
      CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState.canonical edge }

/-- Recasting an edge to its existing differential may replace its persisted
coefficient centre by the canonical one, but weighted allowance depends only
on the unchanged geometry and prepared local-error budget. -/
@[simp] theorem recastCenteredEdge_self_weightedAllowance {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (centered : CenteredEdge curve differential) :
    (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model
      (recastCenteredEdge differential centered)).weightedAllowance =
        centered.model.weightedAllowance := by
  unfold CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model
    CCL.ProgressiveGaussianIntegration.CellModel.weightedAllowance
    CCL.ProgressiveGaussianIntegration.CellModel.displacement
    CCL.Riemann.PreparedConstantModels.PreparedEdge.centeredModel
    recastCenteredEdge
  rw [recastPreparedEdge_self]

@[simp] theorem recastCenteredEdge_segment {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (centered : CenteredEdge curve source) :
    (recastCenteredEdge target centered).edge.segment = centered.edge.segment :=
  rfl

@[simp] theorem recastCenteredEdge_request {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (centered : CenteredEdge curve source) :
    (recastCenteredEdge target centered).edge.request = centered.edge.request :=
  rfl

@[simp] theorem recastCenteredEdge_left {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (centered : CenteredEdge curve source) :
    (recastCenteredEdge target centered).edge.left = centered.edge.left :=
  rfl

@[simp] theorem recastCenteredEdge_sheet {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (centered : CenteredEdge curve source) :
    (recastCenteredEdge target centered).edge.sheet = centered.edge.sheet :=
  rfl

@[simp] theorem recastCenteredEdge_localSegment {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (centered : CenteredEdge curve source) :
    (recastCenteredEdge target centered).edge.localSegment =
      centered.edge.localSegment :=
  rfl

/-- The parent's fixed prepared occurrence transported directly to one
displayed interior endpoint. -/
def directOwner {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) (current : Endpoint)
    (position : CCL.Riemann.PreparedSubdivisionModels.ParentPosition
      parent.edge current) :
    Owner
      (curve.polynomial.eval
        (parent.edge.segment.pointAt current.parameter)) :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.directOwnerAt
    parent.edge.left
    parent.edge.cached.preparedOwner current position.cachedDirectMoveSmall

/-- Common-diameter request ending at the displayed child endpoint. -/
def directRequest (right : Endpoint) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) : StepRequest where
  endpoint := right
  rootDiameter := rootDiameter
  rootDiameterPositive := rootDiameterPositive

/-- One independently anchored child prepared edge. -/
def directChildEdge {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) (current right : Endpoint)
    (position : CCL.Riemann.PreparedSubdivisionModels.ParentPosition
      parent.edge current)
    (ordered : current.parameter <= right.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound
      parent.edge.segment current.parameter right.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared parent.edge.segment
          current (directOwner parent current position)
          (directRequest right rootDiameter
            rootDiameterPositive)).track.initial.clearance.bound) :
    CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve differential where
  ambient := parent.edge.ambient
  start := parent.edge.start
  finish := parent.edge.finish
  segment := parent.edge.segment
  within := parent.edge.within
  left := current
  owner := directOwner parent current position
  request := directRequest right rootDiameter rootDiameterPositive
  cached := CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
    parent.edge.segment current (directOwner parent current position)
      (directRequest right rootDiameter rootDiameterPositive)
  ordered := ordered
  small := small
  sheet := parent.edge.sheet

/-- Canonically centered form of one independently anchored child edge. -/
def directChild {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) (current right : Endpoint)
    (position : CCL.Riemann.PreparedSubdivisionModels.ParentPosition
      parent.edge current)
    (ordered : current.parameter <= right.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound
      parent.edge.segment current.parameter right.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared parent.edge.segment
          current (directOwner parent current position)
          (directRequest right rootDiameter
            rootDiameterPositive)).track.initial.clearance.bound) :
    CenteredEdge curve differential :=
  let edge := directChildEdge parent current right position ordered rootDiameter
    rootDiameterPositive small
  { edge := edge
    center :=
      CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState.canonical edge }

/-- The direct child starts in exactly the coarse parent's point-query
occurrence; preparation at parameter zero preserves that occurrence. -/
def directChildAt {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) (current right : Endpoint)
    (position : CCL.Riemann.PreparedSubdivisionModels.ParentPosition
      parent.edge current)
    (ordered : current.parameter <= right.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound
      parent.edge.segment current.parameter right.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared parent.edge.segment
          current (directOwner parent current position)
          (directRequest right rootDiameter
            rootDiameterPositive)).track.initial.clearance.bound) :
    CCL.Riemann.PreparedSubdivisionModels.RootChildAt parent
      (directChild parent current right position ordered rootDiameter
        rootDiameterPositive small) := by
  let childEdge := directChildEdge parent current right position ordered
    rootDiameter rootDiameterPositive small
  let child := directChild parent current right position ordered rootDiameter
    rootDiameterPositive small
  have parentPoint : parent.edge.point position.fraction =
      parent.edge.segment.pointAt
        (CCL.Riemann.PreparedSheetContinuation.parameterAt parent.edge.left
          parent.edge.request position.fraction) :=
    (CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
      parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.request position.fraction).symm
  have childPoint : parent.edge.segment.pointAt current.parameter =
      childEdge.point 0 := by
    change parent.edge.segment.pointAt current.parameter =
      (CCL.Riemann.PreparedDifferentialModels.edge curve parent.edge.segment
        parent.edge.within current
          (directRequest right rootDiameter rootDiameterPositive)).pointAt 0
    unfold CCL.Riemann.PreparedDifferentialModels.edge
    simpa only [CCL.Riemann.PreparedSheetContinuation.parameterAt_zero] using
      CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
        parent.edge.segment parent.edge.within current
          (directRequest right rootDiameter rootDiameterPositive) 0
  have pointEqual : parent.edge.point position.fraction = childEdge.point 0 :=
    parentPoint.trans ((congrArg parent.edge.segment.pointAt
      position.parameter_eq).trans childPoint)
  have queryToDirect := position.cachedDirectRootEquivalent
  have directToChild := childEdge.ownerRootEquivalent_baseQuery
  exact
    { fraction := position.fraction
      inside := position.inside
      point_eq := pointEqual
      rootEquivalent := by
        rw [parent.edge.rootName_eq_directQueryOwnerRootName position.fraction
          position.inside]
        exact CCL.OperationalEquivalence.NamedEquivalent.trans queryToDirect
          directToChild }

/-- The path-wide uniform preparation floor bounds the actual prepared
clearance of every independently selected child owner. -/
theorem directChildSmall_of_variation_lt_uniform {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) (current right : Endpoint)
    (position : CCL.Riemann.PreparedSubdivisionModels.ParentPosition
      parent.edge current)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (below : CCL.Riemann.ClearSheetContinuation.variationBound
      parent.edge.segment current.parameter right.parameter <
        CCL.Riemann.PreparedSheetContinuation.uniformPreparedClearanceFloor
          parent.edge.segment rootDiameter) :
    CCL.Riemann.ClearSheetContinuation.variationBound parent.edge.segment
      current.parameter right.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared parent.edge.segment
          current (directOwner parent current position)
          (directRequest right rootDiameter
            rootDiameterPositive)).track.initial.clearance.bound := by
  exact below.trans_le (by
    calc
      CCL.Riemann.PreparedSheetContinuation.uniformPreparedClearanceFloor
          parent.edge.segment rootDiameter <=
        CCL.Riemann.PreparedSheetContinuation.preparedClearanceLower
          parent.edge.segment current
            (directRequest right rootDiameter rootDiameterPositive) :=
        CCL.Riemann.PreparedSheetContinuation.uniformPreparedClearanceFloor_le_predicted
          parent.edge.segment rootDiameter
      _ <=
          (CCL.Riemann.PreparedSheetContinuation.prepared parent.edge.segment
            current (directOwner parent current position)
            (directRequest right rootDiameter
              rootDiameterPositive)).track.initial.clearance.bound :=
        CCL.Riemann.PreparedSheetContinuation.preparedClearanceLower_le
          parent.edge.segment current (directOwner parent current position)
            (directRequest right rootDiameter rootDiameterPositive))

private theorem quarterRadius_div_four (scale : Coordinate) (index : Nat) :
    CCL.FiniteGeometric.quarterRadius (scale / 4) index =
      CCL.FiniteGeometric.quarterRadius scale (index + 1) := by
  have scaleDiv : scale / 4 = scale * (1 / 4 : Coordinate) := by
    rw [RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ConstructiveFraction.one_mul]
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow, scaleDiv, pow_succ]
  ring1

private theorem displacementSum_append
    (first second : List CCL.ProgressiveGaussianIntegration.CellModel) :
    CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
        (first ++ second) =
      CCL.ProgressiveGaussianIntegration.PathModel.displacementSum first +
        CCL.ProgressiveGaussianIntegration.PathModel.displacementSum second := by
  induction first with
  | nil =>
      simp only [List.nil_append,
        CCL.ProgressiveGaussianIntegration.PathModel.displacementSum_nil]
      exact (zero_add _).symm
  | cons cell remaining inductionHypothesis =>
      simp only [List.cons_append,
        CCL.ProgressiveGaussianIntegration.PathModel.displacementSum_cons]
      rw [inductionHypothesis]
      ring1

/-- Squared affine movement of one displayed parameter interval. -/
def geometricMovement
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Coordinate) : Coordinate :=
  RFAP.ConstructiveGaussian.Gaussian.normSq
    (segment.pointAt right - segment.pointAt left)

private theorem midpoint_sub_left (left right : Coordinate) :
    CCL.Riemann.ClearSheetContinuation.midpoint left right - left =
      (right - left) / 2 := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show (2 : Coordinate) ≠ 0 by decide)
  calc
    (CCL.Riemann.ClearSheetContinuation.midpoint left right - left) * 2 =
        CCL.Riemann.ClearSheetContinuation.midpoint left right * 2 -
          left * 2 := by ring1
    _ = (left + right) - left * 2 := by
      rw [CCL.Riemann.ClearSheetContinuation.midpoint,
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2 (by decide)]
    _ = right - left := by ring1
    _ = ((right - left) / 2) * 2 :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2 (by decide)).symm

private theorem right_sub_midpoint (left right : Coordinate) :
    right - CCL.Riemann.ClearSheetContinuation.midpoint left right =
      (right - left) / 2 := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show (2 : Coordinate) ≠ 0 by decide)
  calc
    (right - CCL.Riemann.ClearSheetContinuation.midpoint left right) * 2 =
        right * 2 -
          CCL.Riemann.ClearSheetContinuation.midpoint left right * 2 := by
      ring1
    _ = right * 2 - (left + right) := by
      rw [CCL.Riemann.ClearSheetContinuation.midpoint,
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2 (by decide)]
    _ = right - left := by ring1
    _ = ((right - left) / 2) * 2 :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2 (by decide)).symm

private theorem left_lt_midpoint {left right : Coordinate}
    (proper : left < right) :
    left < CCL.Riemann.ClearSheetContinuation.midpoint left right := by
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := (2 : Coordinate))
  · calc
      left * 2 = left + left := by ring1
      _ < left + right :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct proper left
      _ = CCL.Riemann.ClearSheetContinuation.midpoint left right * 2 := by
        rw [CCL.Riemann.ClearSheetContinuation.midpoint,
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2 (by decide)]
  · decide

private theorem midpoint_lt_right {left right : Coordinate}
    (proper : left < right) :
    CCL.Riemann.ClearSheetContinuation.midpoint left right < right := by
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := (2 : Coordinate))
  · calc
      CCL.Riemann.ClearSheetContinuation.midpoint left right * 2 =
          left + right := by
        rw [CCL.Riemann.ClearSheetContinuation.midpoint,
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2 (by decide)]
      _ < right + right :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct proper right
      _ = right * 2 := by ring1
  · decide

private theorem geometricMovement_left_midpoint
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Coordinate) :
    geometricMovement segment left
        (CCL.Riemann.ClearSheetContinuation.midpoint left right) =
      geometricMovement segment left right / 4 := by
  unfold geometricMovement
  rw [segment.normSq_pointAt_sub_pointAt,
    segment.normSq_pointAt_sub_pointAt, midpoint_sub_left, pow_two,
    RFAP.ConstructiveFraction.div_mul_div_direct,
    show (2 : Coordinate) * 2 = 4 by decide]
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct
      ((right - left) * (right - left)) 4]
  simp only [pow_two]
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct
      ((right - left) * (right - left) *
        RFAP.ConstructiveGaussian.Gaussian.normSq (finish - start)) 4]
  ring1

private theorem geometricMovement_midpoint_right
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Coordinate) :
    geometricMovement segment
        (CCL.Riemann.ClearSheetContinuation.midpoint left right) right =
      geometricMovement segment left right / 4 := by
  unfold geometricMovement
  rw [segment.normSq_pointAt_sub_pointAt,
    segment.normSq_pointAt_sub_pointAt, right_sub_midpoint, pow_two,
    RFAP.ConstructiveFraction.div_mul_div_direct,
    show (2 : Coordinate) * 2 = 4 by decide]
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct
      ((right - left) * (right - left)) 4]
  simp only [pow_two]
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct
      ((right - left) * (right - left) *
        RFAP.ConstructiveGaussian.Gaussian.normSq (finish - start)) 4]
  ring1

/-- Point-movement evidence for every child in a finite centered block. -/
private inductive ChildMovementBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (bound : Coordinate) :
    List (CenteredEdge curve differential) -> Prop
  | nil : ChildMovementBound bound []
  | cons {child : CenteredEdge curve differential}
      {children : List (CenteredEdge curve differential)}
      (head : child.edge.pointMovement <= bound)
      (tail : ChildMovementBound bound children) :
      ChildMovementBound bound (child :: children)

private theorem appendChildMovementBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {bound : Coordinate} :
    forall {first second : List (CenteredEdge curve differential)},
      ChildMovementBound bound first -> ChildMovementBound bound second ->
        ChildMovementBound bound (first ++ second)
  | [], _second, .nil, secondBound => secondBound
  | _ :: _, _second, .cons head tail, secondBound =>
      .cons head (appendChildMovementBound tail secondBound)

private theorem castChildMovementBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {first second : Coordinate}
    {children : List (CenteredEdge curve differential)}
    (equal : first = second) :
    ChildMovementBound first children -> ChildMovementBound second children := by
  subst second
  exact fun bounded => bounded

/-- Uniform model-error evidence for every child in a finite block. -/
private inductive ChildModelErrorBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (bound : Coordinate) :
    List (CenteredEdge curve differential) -> Prop
  | nil : ChildModelErrorBound bound []
  | cons {child : CenteredEdge curve differential}
      {children : List (CenteredEdge curve differential)}
      (head : child.edge.modelErrorAllowance <= bound)
      (tail : ChildModelErrorBound bound children) :
      ChildModelErrorBound bound (child :: children)

private theorem appendChildModelErrorBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {bound : Coordinate} :
    forall {first second : List (CenteredEdge curve differential)},
      ChildModelErrorBound bound first -> ChildModelErrorBound bound second ->
        ChildModelErrorBound bound (first ++ second)
  | [], _second, .nil, secondBound => secondBound
  | _ :: _, _second, .cons head tail, secondBound =>
      .cons head (appendChildModelErrorBound tail secondBound)

private theorem castChildModelErrorBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {first second : Coordinate}
    {children : List (CenteredEdge curve differential)}
    (equal : first = second) :
    ChildModelErrorBound first children ->
      ChildModelErrorBound second children := by
  subst second
  exact fun bounded => bounded

private theorem ChildModelErrorBound.mono {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {first second : Coordinate}
    {children : List (CenteredEdge curve differential)}
    (bounded : ChildModelErrorBound first children)
    (less : first <= second) : ChildModelErrorBound second children := by
  induction bounded with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons (head.trans less) inductionHypothesis

/-! ### Compact bounds for already accepted dyadic segments

The executable prepared-path checker transports a genuinely dependent root
owner from one edge to the next.  Its retained integration cells therefore
must not be replaced by the owner-independent direct-refinement cells above.
For scheduling, however, only a numerical upper bound is required.  The
following finite predicates recover that bound from the displayed dyadic
request geometry without folding the expensive coefficient model of every
accepted leaf.
-/

/-- Uniform squared movement of consecutive endpoints in one finite list. -/
private inductive EndpointMovementBound
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (bound : Coordinate) : Endpoint -> List Endpoint -> Prop
  | nil (current : Endpoint) : EndpointMovementBound segment bound current []
  | cons {current endpoint : Endpoint} {remaining : List Endpoint}
      (head : geometricMovement segment current.parameter endpoint.parameter <=
        bound)
      (tail : EndpointMovementBound segment bound endpoint remaining) :
      EndpointMovementBound segment bound current (endpoint :: remaining)

private theorem endpointMovementBound_append
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (bound : Coordinate) :
    forall (current : Endpoint) (first second : List Endpoint),
      EndpointMovementBound segment bound current first ->
      EndpointMovementBound segment bound
        (CCL.Riemann.ClearSheetContinuation.Subdivision.finalTarget current
          first) second ->
      EndpointMovementBound segment bound current (first ++ second)
  | _current, [], _second, .nil _, secondBound => secondBound
  | _current, _endpoint :: _remaining, _second, .cons head tail,
      secondBound =>
    .cons head
      (endpointMovementBound_append segment bound _ _ _ tail secondBound)

/-- The exact depth-`n` dyadic endpoint list has the common squared movement
obtained by dividing the original squared movement by `4^n`. -/
private theorem dyadicTargets_endpointMovementBound
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    forall (depth : Nat) (left right : Endpoint),
      EndpointMovementBound segment
        (CCL.FiniteGeometric.quarterRadius
          (geometricMovement segment left.parameter right.parameter) depth)
        left
        (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets depth
          left right)
  | 0, left, right => by
      apply EndpointMovementBound.cons
      · simpa only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_zero,
          RFAP.ConstructiveFraction.mul_one_direct] using
            (le_refl (geometricMovement segment left.parameter
              right.parameter))
      · exact .nil right
  | depth + 1, left, right => by
      let middle : Endpoint :=
        ⟨CCL.Riemann.ClearSheetContinuation.midpoint left.parameter
            right.parameter,
          CCL.Riemann.ClearSheetContinuation.midpoint_inside
            left.inside right.inside⟩
      have first := dyadicTargets_endpointMovementBound segment depth left
        middle
      have second := dyadicTargets_endpointMovementBound segment depth middle
        right
      have firstScale :
          CCL.FiniteGeometric.quarterRadius
              (geometricMovement segment left.parameter middle.parameter)
                depth =
            CCL.FiniteGeometric.quarterRadius
              (geometricMovement segment left.parameter right.parameter)
                (depth + 1) := by
        change CCL.FiniteGeometric.quarterRadius
            (geometricMovement segment left.parameter
              (CCL.Riemann.ClearSheetContinuation.midpoint left.parameter
                right.parameter)) depth = _
        rw [geometricMovement_left_midpoint]
        exact quarterRadius_div_four _ _
      have secondScale :
          CCL.FiniteGeometric.quarterRadius
              (geometricMovement segment middle.parameter right.parameter)
                depth =
            CCL.FiniteGeometric.quarterRadius
              (geometricMovement segment left.parameter right.parameter)
                (depth + 1) := by
        change CCL.FiniteGeometric.quarterRadius
            (geometricMovement segment
              (CCL.Riemann.ClearSheetContinuation.midpoint left.parameter
                right.parameter) right.parameter) depth = _
        rw [geometricMovement_midpoint_right]
        exact quarterRadius_div_four _ _
      rw [firstScale] at first
      rw [secondScale] at second
      change EndpointMovementBound segment _ left
        (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets depth
            left middle ++
          CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets depth
            middle right)
      apply endpointMovementBound_append segment _ left _ _ first
      simpa only
        [CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets_finalTarget]
        using second

/-- Movement and root-diameter targets attached to the actual displayed
prepared requests. -/
private inductive RequestTargets
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (movementBound rootDiameter : Coordinate) :
    Endpoint -> List StepRequest -> Prop
  | nil (current : Endpoint) :
      RequestTargets segment movementBound rootDiameter current []
  | cons {current : Endpoint} {request : StepRequest}
      {remaining : List StepRequest}
      (movement : geometricMovement segment current.parameter
        request.endpoint.parameter <= movementBound)
      (diameter : request.rootDiameter <= rootDiameter)
      (tail : RequestTargets segment movementBound rootDiameter
        request.endpoint remaining) :
      RequestTargets segment movementBound rootDiameter current
        (request :: remaining)

private theorem requestsAtDiameter_targets
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (movementBound rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall (current : Endpoint) (endpoints : List Endpoint),
      EndpointMovementBound segment movementBound current endpoints ->
      RequestTargets segment movementBound rootDiameter current
        (CCL.Riemann.PreparedSheetContinuation.Subdivision.requestsAtDiameter
          rootDiameter rootDiameterPositive endpoints)
  | _current, [], .nil _ => .nil _
  | _current, _endpoint :: _remaining, .cons head tail =>
      .cons head le_rfl
        (requestsAtDiameter_targets segment movementBound rootDiameter
          rootDiameterPositive _ _ tail)

private theorem dyadicRequests_targets
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (depth : Nat) (left right : Endpoint)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    RequestTargets segment
      (CCL.FiniteGeometric.quarterRadius
        (geometricMovement segment left.parameter right.parameter) depth)
      rootDiameter left
      (CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
        left right rootDiameter rootDiameterPositive) := by
  unfold CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests
  exact requestsAtDiameter_targets segment _ rootDiameter
    rootDiameterPositive left _
      (dyadicTargets_endpointMovementBound segment depth left right)

/-- Segment-wide error target shared by every leaf of a direct dyadic block. -/
def localModelErrorBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Coordinate) (depth : Nat) (left right : Coordinate) :
    Coordinate :=
  CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
      differential segment *
      CCL.FiniteGeometric.quarterRadius
        (geometricMovement segment left right) depth +
    CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
      differential segment * rootDiameter

/-- Exact local-error summary with the expensive segment denominator retained
once for both quotient coefficients. -/
structure PreparedSegmentLocalErrorBounds where
  pointCoefficient : Coordinate
  rootCoefficient : Coordinate
  error : Coordinate

def preparedSegmentLocalErrorBounds {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Coordinate) (depth : Nat) (left right : Coordinate) :
    PreparedSegmentLocalErrorBounds :=
  let denominator :=
    CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower segment
  let denominatorSq := denominator * denominator
  let pointCoefficient :=
    (2 *
        (CCL.Riemann.FiniteQuotientVariation.powerSlope ambient.normSqBound
            differential.exponent *
          (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
            segment).normSqBound)) /
      denominatorSq
  let rootCoefficient :=
    (2 * ambient.normSqBound ^ differential.exponent) / denominatorSq + 1
  { pointCoefficient := pointCoefficient
    rootCoefficient := rootCoefficient
    error := pointCoefficient *
        CCL.FiniteGeometric.quarterRadius
          (geometricMovement segment left right) depth +
      rootCoefficient * rootDiameter }

@[simp] theorem preparedSegmentLocalErrorBounds_pointCoefficient
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Coordinate) (depth : Nat) (left right : Coordinate) :
    (preparedSegmentLocalErrorBounds differential segment rootDiameter depth
      left right).pointCoefficient =
        CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
          differential segment := rfl

@[simp] theorem preparedSegmentLocalErrorBounds_rootCoefficient
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Coordinate) (depth : Nat) (left right : Coordinate) :
    (preparedSegmentLocalErrorBounds differential segment rootDiameter depth
      left right).rootCoefficient =
        CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
          differential segment := rfl

@[simp] theorem preparedSegmentLocalErrorBounds_error
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Coordinate) (depth : Nat) (left right : Coordinate) :
    (preparedSegmentLocalErrorBounds differential segment rootDiameter depth
      left right).error =
        localModelErrorBound differential segment rootDiameter depth left
          right := rfl

theorem localModelErrorBound_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    {rootDiameter : Coordinate} (rootDiameterNonnegative : 0 <= rootDiameter)
    (depth : Nat) (left right : Coordinate) :
    0 <= localModelErrorBound differential segment rootDiameter depth
      left right := by
  unfold localModelErrorBound
  exact add_nonneg
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient_nonnegative
        differential segment)
      (CCL.FiniteGeometric.quarterRadius_nonneg
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _) depth))
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient_nonnegative
        differential segment) rootDiameterNonnegative)

/-- Largest squared root-box diameter actually cached by an accepted
subdivision.  This finite summary reads only the persisted source boxes; it
does not construct coefficient centres or integration models. -/
def subdivisionPreparedRootDiameterMaximum
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))} :
    CCL.Riemann.PreparedSheetContinuation.Subdivision segment within left
        owner -> Coordinate
  | .stop _ _ => 0
  | .next _ _ _ cached _ _ remaining =>
      max cached.preparedOwner.track.initial.box.diagonalSq
        (subdivisionPreparedRootDiameterMaximum remaining)

theorem subdivisionPreparedRootDiameterMaximum_nonnegative
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))} :
    forall subdivision :
        CCL.Riemann.PreparedSheetContinuation.Subdivision segment within left
          owner,
      0 <= subdivisionPreparedRootDiameterMaximum subdivision
  | .stop _ _ => le_rfl
  | .next _ _ _ _ _ _ remaining =>
      (subdivisionPreparedRootDiameterMaximum_nonnegative remaining).trans
        (le_max_right _ _)

private theorem preparedEdge_pointMovement_eq_geometric {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (edge : CCL.Riemann.PreparedSubdivisionModels.PreparedEdge curve
      differential) :
    edge.pointMovement = geometricMovement edge.segment edge.left.parameter
      edge.request.endpoint.parameter := by
  unfold CCL.Riemann.PreparedConstantModels.PreparedEdge.pointMovement
    geometricMovement
  change RFAP.ConstructiveGaussian.Gaussian.normSq
      (edge.localSegment.pointAt 1 - edge.localSegment.pointAt 0) = _
  rw [edge.localSegment.pointAt_one, edge.localSegment.pointAt_zero]

/-- Actual cached root diameters give a uniform model-error bound for every
centred edge of an accepted subdivision.  The proof follows the dependent
subdivision spine, while the executable bound retains only its finite
maximum. -/
private theorem centeredEdges_childModelErrorBound_at_actualMaximum
    {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2)
    (movementBound : Coordinate) :
    forall {left : Endpoint}
      {owner : Owner (curve.polynomial.eval
        (segment.pointAt left.parameter))}
      (subdivision : CCL.Riemann.PreparedSheetContinuation.Subdivision segment
        within left owner)
      (centers : CCL.Riemann.PreparedSubdivisionModels.CenterStates curve
        differential sheet subdivision),
      ChildMovementBound movementBound
          (CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve
            differential sheet subdivision centers) ->
        ChildModelErrorBound
          (CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                differential segment * movementBound +
            CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                differential segment *
              subdivisionPreparedRootDiameterMaximum subdivision)
          (CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve
            differential sheet subdivision centers)
  | _, _, .stop _ _, _, bounded => by
      simp only [CCL.Riemann.PreparedSubdivisionModels.centeredEdges] at bounded
      cases bounded
      exact .nil
  | _, _, .next left owner request cached ordered small remaining, centers,
      .cons headMovement tailMovement => by
      let edge := CCL.Riemann.PreparedSubdivisionModels.edgeOfStep curve
        differential segment within left owner request cached ordered small
          sheet
      have headRoot : edge.preparedRootDiameter <=
          subdivisionPreparedRootDiameterMaximum
            (.next left owner request cached ordered small remaining) := by
        exact le_max_left _ _
      have headError : edge.modelErrorAllowance <=
          CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                differential segment * movementBound +
            CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                differential segment *
              subdivisionPreparedRootDiameterMaximum
                (.next left owner request cached ordered small remaining) :=
        edge.modelErrorAllowance_le_of_separate_targets movementBound _
          headMovement headRoot
      have tailBound :=
        centeredEdges_childModelErrorBound_at_actualMaximum curve differential
          segment within sheet movementBound remaining centers.2 tailMovement
      have tailMaximumLe :
          subdivisionPreparedRootDiameterMaximum remaining <=
            subdivisionPreparedRootDiameterMaximum
              (.next left owner request cached ordered small remaining) :=
        le_max_right _ _
      have scaledTailMaximumLe :
          CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                differential segment *
              subdivisionPreparedRootDiameterMaximum remaining <=
            CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                differential segment *
              subdivisionPreparedRootDiameterMaximum
                (.next left owner request cached ordered small remaining) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          tailMaximumLe
          (CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient_nonnegative
            differential segment)
      exact .cons headError
        (tailBound.mono (add_le_add le_rfl scaledTailMaximumLe))

/-- The request targets followed by a successful prepared checker bound the
actual owner-transported centred cells returned by that checker. -/
private theorem trySteps_childBounds {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2)
    (movementBound rootDiameter : Coordinate) :
    forall (requests : List StepRequest) (left : Endpoint)
      (owner : Owner (curve.polynomial.eval
        (segment.pointAt left.parameter)))
      {subdivision : CCL.Riemann.PreparedSheetContinuation.Subdivision segment
        within left owner},
      RequestTargets segment movementBound rootDiameter left requests ->
      CCL.Riemann.PreparedSheetContinuation.Subdivision.trySteps segment
          within left owner requests = some subdivision ->
      forall centers : CCL.Riemann.PreparedSubdivisionModels.CenterStates curve
        differential sheet subdivision,
        ChildMovementBound movementBound
            (CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve
              differential sheet subdivision centers) /\
          ChildModelErrorBound
            (CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                differential segment * movementBound +
              CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                differential segment * rootDiameter)
            (CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve
              differential sheet subdivision centers)
  | [], left, owner, _subdivision, .nil _, success, centers => by
      simp only
        [CCL.Riemann.PreparedSheetContinuation.Subdivision.trySteps] at success
      cases success
      exact ⟨ChildMovementBound.nil, ChildModelErrorBound.nil⟩
  | request :: remaining, left, owner, _subdivision,
      .cons movement diameter tailTargets, success, centers => by
      simp only
        [CCL.Riemann.PreparedSheetContinuation.Subdivision.trySteps] at success
      split at success
      next ordered =>
        split at success
        next cachedSmall =>
          split at success
          next => contradiction
          next tail tailSuccess =>
            cases success
            let edge :=
              CCL.Riemann.PreparedSubdivisionModels.edgeOfStep curve
                differential segment within left owner request
                  (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
                    segment left owner request) ordered cachedSmall sheet
            have edgeMovement : edge.pointMovement <= movementBound := by
              rw [preparedEdge_pointMovement_eq_geometric]
              exact movement
            have edgeError : edge.modelErrorAllowance <=
                CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                    differential segment * movementBound +
                  CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                    differential segment * rootDiameter := by
              exact edge.modelErrorAllowance_le_of_separate_targets
                movementBound rootDiameter edgeMovement
                  (edge.preparedRootDiameter_lt_requested.le.trans diameter)
            have tailBounds := trySteps_childBounds curve differential segment
              within sheet movementBound rootDiameter remaining request.endpoint
                (CCL.Riemann.PreparedSheetContinuation.advanceCached segment
                  within left owner request
                    (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
                      segment left owner request) cachedSmall)
                tailTargets tailSuccess centers.2
            exact ⟨ChildMovementBound.cons edgeMovement tailBounds.1,
              ChildModelErrorBound.cons edgeError tailBounds.2⟩
        next => contradiction
      next => contradiction

/-- Request bounds apply directly to any retained prepared subdivision whose
accepted endpoint-and-diameter request list is known.  This avoids rebuilding
an owner-dependent checker result merely to recover bounds already justified
by the stored continuation edges. -/
private theorem subdivision_childBounds {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2)
    (movementBound rootDiameter : Coordinate) :
    forall {left : Endpoint}
      {owner : Owner (curve.polynomial.eval
        (segment.pointAt left.parameter))}
      (subdivision : CCL.Riemann.PreparedSheetContinuation.Subdivision segment
        within left owner),
      RequestTargets segment movementBound rootDiameter left
          subdivision.requests ->
      forall centers : CCL.Riemann.PreparedSubdivisionModels.CenterStates curve
        differential sheet subdivision,
        ChildMovementBound movementBound
            (CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve
              differential sheet subdivision centers) /\
          ChildModelErrorBound
            (CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                differential segment * movementBound +
              CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                differential segment * rootDiameter)
            (CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve
              differential sheet subdivision centers)
  | _, _, .stop left owner, .nil _, centers =>
      ⟨ChildMovementBound.nil, ChildModelErrorBound.nil⟩
  | _, _, .next left owner request cached ordered small remaining,
      .cons movement diameter tailTargets, centers => by
      let edge := CCL.Riemann.PreparedSubdivisionModels.edgeOfStep curve
        differential segment within left owner request cached ordered small
          sheet
      have edgeMovement : edge.pointMovement <= movementBound := by
        rw [preparedEdge_pointMovement_eq_geometric]
        exact movement
      have edgeError : edge.modelErrorAllowance <=
          CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                differential segment * movementBound +
            CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                differential segment * rootDiameter :=
        edge.modelErrorAllowance_le_of_separate_targets movementBound
          rootDiameter edgeMovement
            (edge.preparedRootDiameter_lt_requested.le.trans diameter)
      have tailBounds := subdivision_childBounds curve differential segment
        within sheet movementBound rootDiameter remaining tailTargets centers.2
      exact ⟨ChildMovementBound.cons edgeMovement tailBounds.1,
        ChildModelErrorBound.cons edgeError tailBounds.2⟩

private theorem directChild_pointMovement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) (current right : Endpoint)
    (position : CCL.Riemann.PreparedSubdivisionModels.ParentPosition
      parent.edge current)
    (ordered : current.parameter <= right.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound
      parent.edge.segment current.parameter right.parameter <
        (CCL.Riemann.PreparedSheetContinuation.prepared parent.edge.segment
          current (directOwner parent current position)
          (directRequest right rootDiameter
            rootDiameterPositive)).track.initial.clearance.bound) :
    (directChild parent current right position ordered rootDiameter
      rootDiameterPositive small).edge.pointMovement =
        geometricMovement parent.edge.segment current.parameter
          right.parameter := by
  unfold CCL.Riemann.PreparedConstantModels.PreparedEdge.pointMovement
    geometricMovement directChild directChildEdge
  change RFAP.ConstructiveGaussian.Gaussian.normSq
      ((CCL.Riemann.PreparedDifferentialModels.edge curve parent.edge.segment
        parent.edge.within current
          (directRequest right rootDiameter rootDiameterPositive)).pointAt 1 -
       (CCL.Riemann.PreparedDifferentialModels.edge curve parent.edge.segment
        parent.edge.within current
          (directRequest right rootDiameter rootDiameterPositive)).pointAt 0) = _
  unfold CCL.Riemann.PreparedDifferentialModels.edge
  rw [CCL.Riemann.BranchCuts.ClearSegment.pointAt_one,
    CCL.Riemann.BranchCuts.ClearSegment.pointAt_zero]
  simp only [directRequest]

private def appendRootChildBlock {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : CenteredEdge curve differential} :
    forall {first second : List (CenteredEdge curve differential)},
      CCL.Riemann.PreparedSubdivisionModels.RootChildBlock parent first ->
      CCL.Riemann.PreparedSubdivisionModels.RootChildBlock parent second ->
        CCL.Riemann.PreparedSubdivisionModels.RootChildBlock parent
          (first ++ second)
  | [], _second, .nil, secondBlock => secondBlock
  | _ :: _, _second, .cons head tail, secondBlock =>
      .cons head (appendRootChildBlock tail secondBlock)

private theorem allParentsProper_append {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {first second : List (CenteredEdge curve differential)},
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper first ->
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper second ->
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper (first ++ second)
  | [], _second, _firstProper, secondProper => secondProper
  | _ :: _, _second, firstProper, secondProper =>
      ⟨firstProper.1,
        allParentsProper_append firstProper.2 secondProper⟩

theorem allParentsProper_map_recast {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source target : Differential genus} :
    forall {parents : List (CenteredEdge curve source)},
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents ->
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper
        (parents.map (recastCenteredEdge target))
  | [], _proper => trivial
  | _ :: _, proper =>
      ⟨proper.1, allParentsProper_map_recast proper.2⟩

set_option linter.unusedVariables false in
/-- A consecutive centered-edge path retained directly by the refinement
blocks.  Unlike a bare lifted path, this keeps the prepared edge list in its
dependent endpoint order and can therefore be refined repeatedly. -/
inductive DirectPathChain {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    (parents : List (CenteredEdge curve differential)) ->
      {start finish : LiftedPoint 2} -> Type 2
  | nil (point : LiftedPoint 2) : DirectPathChain [] (start := point)
      (finish := point)
  | cons (parent : CenteredEdge curve differential)
      {remaining : List (CenteredEdge curve differential)}
      {finish : LiftedPoint 2}
      (tail : DirectPathChain remaining
        (start :=
          { coordinate := parent.edge.segment.pointAt
              parent.edge.request.endpoint.parameter
            sheet := parent.edge.sheet })
        (finish := finish)) :
      DirectPathChain (parent :: remaining)
        (start :=
          { coordinate := parent.edge.segment.pointAt parent.edge.left.parameter
            sheet := parent.edge.sheet })
        (finish := finish)

namespace DirectPathChain

def append {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {first second : List (CenteredEdge curve differential)}
      {start middle finish : LiftedPoint 2},
      DirectPathChain first (start := start) (finish := middle) ->
      DirectPathChain second (start := middle) (finish := finish) ->
        DirectPathChain (first ++ second) (start := start) (finish := finish)
  | [], _, _, _, _, .nil _, second => second
  | _ :: _, _, _, _, _, .cons parent tail, second =>
      .cons parent (append tail second)

private theorem model_start {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) :
    parent.model.start =
      parent.edge.segment.pointAt parent.edge.left.parameter := by
  change parent.edge.point 0 = _
  change
    (CCL.Riemann.PreparedDifferentialModels.edge curve parent.edge.segment
      parent.edge.within parent.edge.left parent.edge.request).pointAt 0 = _
  unfold CCL.Riemann.PreparedDifferentialModels.edge
  simpa only [CCL.Riemann.PreparedSheetContinuation.parameterAt_zero] using
    (CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
      parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.request 0).symm

private theorem model_finish {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) :
    parent.model.finish =
      parent.edge.segment.pointAt
        parent.edge.request.endpoint.parameter := by
  change parent.edge.point 1 = _
  change
    (CCL.Riemann.PreparedDifferentialModels.edge curve parent.edge.segment
      parent.edge.within parent.edge.left parent.edge.request).pointAt 1 = _
  unfold CCL.Riemann.PreparedDifferentialModels.edge
  simpa only [CCL.Riemann.PreparedSheetContinuation.parameterAt_one] using
    (CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
      parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.request 1).symm

def path {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2},
      DirectPathChain parents (start := start) (finish := finish) ->
        LiftedPath 2 start finish
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .cons
        (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet parent.edge.sheet
          parent.edge.localSegment)
        tail.path

def certificates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2}
      (chain : DirectPathChain parents (start := start) (finish := finish)),
      UniformPathCertificates curve differential
        (parents.map CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
        chain.path
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .cons (model_start parent) (model_finish parent)
        (parent.edge.centeredValidCertificate curve differential parent.center)
        tail.certificates

/-- Recenter every edge for another differential without changing the
dependent lifted geometry. -/
def recast {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : LiftedPoint 2},
      DirectPathChain parents (start := start) (finish := finish) ->
        DirectPathChain (parents.map (recastCenteredEdge target))
          (start := start) (finish := finish)
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .cons (recastCenteredEdge target parent) (recast target tail)

theorem path_recast {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : LiftedPoint 2}
      (chain : DirectPathChain parents (start := start) (finish := finish)),
      (chain.recast target).path = chain.path
  | [], _, _, .nil _ => rfl
  | _ :: _, _, _, .cons parent tail => by
      change
        LiftedPath.cons
            (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet
              parent.edge.sheet parent.edge.localSegment)
            (recast target tail).path =
          LiftedPath.cons
            (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet
              parent.edge.sheet parent.edge.localSegment)
            tail.path
      rw [path_recast target tail]

end DirectPathChain

/-- Direct child block over one local subinterval of the coarse parent. -/
private structure LocalBlock {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) (left right : Endpoint)
    (depth : Nat) (rootDiameter : Coordinate) where
  children : List (CenteredEdge curve differential)
  childCount : children.length = 2 ^ depth
  proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper children
  chain : DirectPathChain children
    (start :=
      { coordinate := parent.edge.segment.pointAt left.parameter
        sheet := parent.edge.sheet })
    (finish :=
      { coordinate := parent.edge.segment.pointAt right.parameter
        sheet := parent.edge.sheet })
  roots : CCL.Riemann.PreparedSubdivisionModels.RootChildBlock parent children
  lifted : LiftedPath 2
    ({ coordinate := parent.edge.segment.pointAt left.parameter
       sheet := parent.edge.sheet } : LiftedPoint 2)
    ({ coordinate := parent.edge.segment.pointAt right.parameter
       sheet := parent.edge.sheet } : LiftedPoint 2)
  certificates : UniformPathCertificates curve differential
    (children.map CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      lifted
  movements : ChildMovementBound
    (CCL.FiniteGeometric.quarterRadius
      (geometricMovement parent.edge.segment left.parameter right.parameter)
      depth) children
  errors : ChildModelErrorBound
    (localModelErrorBound differential parent.edge.segment rootDiameter depth
      left.parameter right.parameter) children
  displacement_eq :
    CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
        (children.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model) =
      parent.edge.segment.pointAt right.parameter -
        parent.edge.segment.pointAt left.parameter

/-- Recursively split a local interval, anchoring every leaf directly in the
same coarse parent occurrence. -/
private def localDyadicBlock {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential)
    (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (depth : Nat) -> (left right : Endpoint) ->
    parent.edge.left.parameter <= left.parameter ->
    right.parameter <= parent.edge.request.endpoint.parameter ->
    left.parameter <= right.parameter ->
    left.parameter < right.parameter ->
    CCL.FiniteGeometric.quarterRadius
        (CCL.Riemann.ClearSheetContinuation.variationBound parent.edge.segment
          left.parameter right.parameter) depth <
      CCL.Riemann.PreparedSheetContinuation.uniformPreparedClearanceFloor
        parent.edge.segment rootDiameter ->
          LocalBlock parent left right depth rootDiameter
  | 0, left, right, lower, upper, ordered, localProper, below => by
      let position := CCL.Riemann.PreparedSubdivisionModels.ParentPosition.ofBetween
        proper ⟨lower, ordered.trans upper⟩
      have variationBelow :
          CCL.Riemann.ClearSheetContinuation.variationBound parent.edge.segment
              left.parameter right.parameter <
            CCL.Riemann.PreparedSheetContinuation.uniformPreparedClearanceFloor
              parent.edge.segment rootDiameter := by
        simpa only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_zero,
          RFAP.ConstructiveFraction.mul_one_direct] using below
      let small := directChildSmall_of_variation_lt_uniform parent left right
        position rootDiameter rootDiameterPositive variationBelow
      let child := directChild parent left right position ordered rootDiameter
        rootDiameterPositive small
      have startEqual : child.model.start =
          parent.edge.segment.pointAt left.parameter := by
        change
          (CCL.Riemann.PreparedDifferentialModels.edge curve
            parent.edge.segment parent.edge.within left
              (directRequest right rootDiameter rootDiameterPositive)).pointAt
              0 = parent.edge.segment.pointAt left.parameter
        unfold CCL.Riemann.PreparedDifferentialModels.edge
        simpa only [CCL.Riemann.PreparedSheetContinuation.parameterAt_zero]
          using
            (CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
              parent.edge.segment parent.edge.within left
                (directRequest right rootDiameter rootDiameterPositive) 0).symm
      have finishEqual : child.model.finish =
          parent.edge.segment.pointAt right.parameter := by
        change
          (CCL.Riemann.PreparedDifferentialModels.edge curve
            parent.edge.segment parent.edge.within left
              (directRequest right rootDiameter rootDiameterPositive)).pointAt
              1 = parent.edge.segment.pointAt right.parameter
        unfold CCL.Riemann.PreparedDifferentialModels.edge
        simpa only [directRequest,
          CCL.Riemann.PreparedSheetContinuation.parameterAt_one]
          using
            (CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
              parent.edge.segment parent.edge.within left
                (directRequest right rootDiameter rootDiameterPositive) 1).symm
      let lifted : LiftedPath 2
          ({ coordinate := parent.edge.segment.pointAt left.parameter,
             sheet := parent.edge.sheet } : LiftedPoint 2)
          ({ coordinate := parent.edge.segment.pointAt right.parameter,
             sheet := parent.edge.sheet } : LiftedPoint 2) :=
        .cons
          (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet child.edge.sheet
            child.edge.localSegment)
          (.nil _)
      have childError : child.edge.modelErrorAllowance <=
          localModelErrorBound differential parent.edge.segment rootDiameter 0
            left.parameter right.parameter := by
        unfold localModelErrorBound
        apply child.edge.modelErrorAllowance_le_of_separate_targets
        · calc
            child.edge.pointMovement =
                geometricMovement parent.edge.segment left.parameter
                  right.parameter :=
              directChild_pointMovement parent left right position ordered
                rootDiameter rootDiameterPositive small
            _ = CCL.FiniteGeometric.quarterRadius
                (geometricMovement parent.edge.segment left.parameter
                  right.parameter) 0 := by
              simp only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_zero,
                RFAP.ConstructiveFraction.mul_one_direct]
            _ <= CCL.FiniteGeometric.quarterRadius
                (geometricMovement parent.edge.segment left.parameter
                  right.parameter) 0 := le_rfl
        · exact child.edge.preparedRootDiameter_lt_requested.le
      exact
        { children := [child]
          childCount := rfl
          proper := ⟨localProper, trivial⟩
          chain := .cons child (.nil _)
          roots := .cons
            (directChildAt parent left right position ordered rootDiameter
              rootDiameterPositive small) .nil
          lifted := lifted
          certificates := .cons startEqual finishEqual
            (child.edge.centeredValidCertificate curve differential child.center)
            (.nil _)
          movements := .cons (by
            rw [directChild_pointMovement]
            simpa only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_zero,
              RFAP.ConstructiveFraction.mul_one_direct] using
                (le_refl
                  (geometricMovement parent.edge.segment left.parameter
                    right.parameter))) .nil
          errors := .cons childError .nil
          displacement_eq := by
            simp only [List.map_cons, List.map_nil,
              CCL.ProgressiveGaussianIntegration.PathModel.displacementSum_cons,
              CCL.ProgressiveGaussianIntegration.PathModel.displacementSum_nil,
              add_zero]
            exact
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model_displacement
                child }
  | depth + 1, left, right, lower, upper, ordered, localProper, below => by
      let middle : Endpoint :=
        ⟨CCL.Riemann.ClearSheetContinuation.midpoint left.parameter
            right.parameter,
          CCL.Riemann.ClearSheetContinuation.midpoint_inside
            left.inside right.inside⟩
      have leftOrdered : left.parameter <= middle.parameter :=
        CCL.Riemann.ClearSheetContinuation.left_le_midpoint ordered
      have rightOrdered : middle.parameter <= right.parameter :=
        CCL.Riemann.ClearSheetContinuation.midpoint_le_right ordered
      have leftProper : left.parameter < middle.parameter :=
        left_lt_midpoint localProper
      have rightProper : middle.parameter < right.parameter :=
        midpoint_lt_right localProper
      have leftBelow :
          CCL.FiniteGeometric.quarterRadius
              (CCL.Riemann.ClearSheetContinuation.variationBound
                parent.edge.segment left.parameter middle.parameter) depth <
            CCL.Riemann.PreparedSheetContinuation.uniformPreparedClearanceFloor
              parent.edge.segment rootDiameter := by
        change CCL.FiniteGeometric.quarterRadius
            (CCL.Riemann.ClearSheetContinuation.variationBound
              parent.edge.segment left.parameter
                (CCL.Riemann.ClearSheetContinuation.midpoint
                  left.parameter right.parameter)) depth < _
        rw [CCL.Riemann.ClearSheetContinuation.variationBound_left_midpoint,
          quarterRadius_div_four]
        exact below
      have rightBelow :
          CCL.FiniteGeometric.quarterRadius
              (CCL.Riemann.ClearSheetContinuation.variationBound
                parent.edge.segment middle.parameter right.parameter) depth <
            CCL.Riemann.PreparedSheetContinuation.uniformPreparedClearanceFloor
              parent.edge.segment rootDiameter := by
        change CCL.FiniteGeometric.quarterRadius
            (CCL.Riemann.ClearSheetContinuation.variationBound
              parent.edge.segment
                (CCL.Riemann.ClearSheetContinuation.midpoint
                  left.parameter right.parameter) right.parameter) depth < _
        rw [CCL.Riemann.ClearSheetContinuation.variationBound_midpoint_right,
          quarterRadius_div_four]
        exact below
      let first := localDyadicBlock parent proper rootDiameter
        rootDiameterPositive depth left middle lower
          (rightOrdered.trans upper) leftOrdered leftProper leftBelow
      let second := localDyadicBlock parent proper rootDiameter
        rootDiameterPositive depth middle right (lower.trans leftOrdered) upper
          rightOrdered rightProper rightBelow
      have firstMovements : ChildMovementBound
          (CCL.FiniteGeometric.quarterRadius
            (geometricMovement parent.edge.segment left.parameter
              right.parameter) (depth + 1)) first.children := by
        apply castChildMovementBound _ first.movements
        rw [geometricMovement_left_midpoint, quarterRadius_div_four]
      have secondMovements : ChildMovementBound
          (CCL.FiniteGeometric.quarterRadius
            (geometricMovement parent.edge.segment left.parameter
              right.parameter) (depth + 1)) second.children := by
        apply castChildMovementBound _ second.movements
        rw [geometricMovement_midpoint_right, quarterRadius_div_four]
      have firstErrors : ChildModelErrorBound
          (localModelErrorBound differential parent.edge.segment rootDiameter
            (depth + 1) left.parameter right.parameter) first.children := by
        apply castChildModelErrorBound _ first.errors
        unfold localModelErrorBound
        rw [geometricMovement_left_midpoint, quarterRadius_div_four]
      have secondErrors : ChildModelErrorBound
          (localModelErrorBound differential parent.edge.segment rootDiameter
            (depth + 1) left.parameter right.parameter) second.children := by
        apply castChildModelErrorBound _ second.errors
        unfold localModelErrorBound
        rw [geometricMovement_midpoint_right, quarterRadius_div_four]
      exact
        { children := first.children ++ second.children
          childCount := by
            rw [List.length_append, first.childCount, second.childCount,
              pow_succ]
            omega
          proper := allParentsProper_append first.proper second.proper
          chain := first.chain.append second.chain
          roots := appendRootChildBlock first.roots second.roots
          lifted := first.lifted.append second.lifted
          certificates := by
            simpa only [List.map_append] using
              UniformPathCertificates.append first.lifted first.certificates
                second.certificates
          movements := appendChildMovementBound firstMovements secondMovements
          errors := appendChildModelErrorBound firstErrors secondErrors
          displacement_eq := by
            rw [List.map_append, displacementSum_append,
              first.displacement_eq, second.displacement_eq]
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
                RFAP.ConstructiveGaussian.Gaussian.add_im,
                RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im] <;> ring1 }

/-- The leaf geometry computed by the local dyadic recursion commutes with
recasting its parent differential. -/
private theorem localDyadicBlock_children_recast {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (parent : CenteredEdge curve source)
    (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    forall (depth : Nat) (left right : Endpoint)
      (lower : parent.edge.left.parameter <= left.parameter)
      (upper : right.parameter <= parent.edge.request.endpoint.parameter)
      (ordered : left.parameter <= right.parameter)
      (localProper : left.parameter < right.parameter)
      (below :
        CCL.FiniteGeometric.quarterRadius
            (CCL.Riemann.ClearSheetContinuation.variationBound
              parent.edge.segment left.parameter right.parameter) depth <
          CCL.Riemann.PreparedSheetContinuation.uniformPreparedClearanceFloor
            parent.edge.segment rootDiameter),
      (localDyadicBlock (recastCenteredEdge target parent) proper rootDiameter
          rootDiameterPositive depth left right lower upper ordered localProper
            below).children =
        (localDyadicBlock parent proper rootDiameter rootDiameterPositive depth
          left right lower upper ordered localProper below).children.map
            (recastCenteredEdge target)
  | 0, _left, _right, _lower, _upper, _ordered, _localProper, _below => rfl
  | depth + 1, left, right, lower, upper, ordered, localProper, below => by
      simp only [localDyadicBlock, List.map_append]
      rw [localDyadicBlock_children_recast target parent proper rootDiameter
          rootDiameterPositive depth,
        localDyadicBlock_children_recast target parent proper rootDiameter
          rootDiameterPositive depth]

/-- Total direct dyadic refinement of one nondegenerate coarse parent. -/
structure DirectParentBlock {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) where
  depth : Nat
  rootDiameter : Coordinate
  children : List (CenteredEdge curve differential)
  childCount : children.length = 2 ^ depth
  proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper children
  chain : DirectPathChain children
    (start :=
      { coordinate := parent.edge.segment.pointAt parent.edge.left.parameter
        sheet := parent.edge.sheet })
    (finish :=
      { coordinate := parent.edge.segment.pointAt
          parent.edge.request.endpoint.parameter
        sheet := parent.edge.sheet })
  roots : CCL.Riemann.PreparedSubdivisionModels.RootChildBlock parent children
  lifted : LiftedPath 2
    ({ coordinate := parent.edge.segment.pointAt parent.edge.left.parameter
       sheet := parent.edge.sheet } : LiftedPoint 2)
    ({ coordinate := parent.edge.segment.pointAt
        parent.edge.request.endpoint.parameter
       sheet := parent.edge.sheet } : LiftedPoint 2)
  certificates : UniformPathCertificates curve differential
    (children.map CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      lifted
  movements : ChildMovementBound
    (CCL.FiniteGeometric.quarterRadius
      (geometricMovement parent.edge.segment parent.edge.left.parameter
        parent.edge.request.endpoint.parameter) depth) children
  errors : ChildModelErrorBound
    (localModelErrorBound differential parent.edge.segment rootDiameter depth
      parent.edge.left.parameter parent.edge.request.endpoint.parameter)
    children
  displacement_eq :
    CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
        (children.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model) =
      parent.model.displacement

/-- Construct a complete direct child block at any displayed depth beyond
the parent's computed clearance threshold. -/
def directParentBlockAtDepth {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential)
    (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (depth : Nat)
    (enough :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
        parent.edge.segment parent.edge.left parent.edge.request.endpoint
          rootDiameter <= depth) :
    DirectParentBlock parent := by
  have laterLe := CCL.FiniteGeometric.quarterRadius_antitone
    (CCL.Riemann.ClearSheetContinuation.variationBound_nonneg
      parent.edge.segment parent.edge.left.parameter
        parent.edge.request.endpoint.parameter) enough
  have below := laterLe.trans_lt
    (CCL.Riemann.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth_variation_lt
      parent.edge.segment parent.edge.left parent.edge.request.endpoint
        rootDiameterPositive)
  let localBlock := localDyadicBlock parent proper rootDiameter
    rootDiameterPositive depth parent.edge.left parent.edge.request.endpoint
      (le_refl _) (le_refl _) parent.edge.ordered proper below
  exact
    { depth := depth
      rootDiameter := rootDiameter
      children := localBlock.children
      childCount := localBlock.childCount
      proper := localBlock.proper
      chain := localBlock.chain
      roots := localBlock.roots
      lifted := localBlock.lifted
      certificates := localBlock.certificates
      movements := localBlock.movements
      errors := localBlock.errors
      displacement_eq := localBlock.displacement_eq.trans
        (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model_displacement
          parent).symm }

/-- Direct dyadic child geometry is independent of the algebraic
differential.  Recomputing the same numerical block after recentering its
parent therefore produces exactly the recentered source children. -/
theorem directParentBlockAtDepth_children_recast {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (parent : CenteredEdge curve source)
    (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (depth : Nat)
    (enough :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
        parent.edge.segment parent.edge.left parent.edge.request.endpoint
          rootDiameter <= depth) :
    (directParentBlockAtDepth (recastCenteredEdge target parent) proper
        rootDiameter rootDiameterPositive depth enough).children =
      (directParentBlockAtDepth parent proper rootDiameter
        rootDiameterPositive depth enough).children.map
          (recastCenteredEdge target) := by
  unfold directParentBlockAtDepth
  apply localDyadicBlock_children_recast

/-- Compute the sufficient depth and the complete direct child block. -/
def directParentBlock {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential)
    (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    DirectParentBlock parent := by
  let depth :=
    CCL.Riemann.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
      parent.edge.segment parent.edge.left parent.edge.request.endpoint
        rootDiameter
  exact directParentBlockAtDepth parent proper rootDiameter
    rootDiameterPositive depth (le_refl _)

private theorem centeredEdge_weightedAllowance_eq {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (child : CenteredEdge curve differential) :
    child.model.weightedAllowance =
      child.edge.pointMovement * (16 * child.edge.modelErrorAllowance) := by
  unfold CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model
    CCL.ProgressiveGaussianIntegration.CellModel.weightedAllowance
    CCL.ProgressiveGaussianIntegration.CellModel.displacement
    CCL.Riemann.PreparedConstantModels.PreparedEdge.centeredModel
    CCL.Riemann.PreparedConstantModels.PreparedEdge.pointMovement
  rfl

private theorem centeredEdge_weightedAllowance_eq_geometric {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) :
    parent.model.weightedAllowance =
      geometricMovement parent.edge.segment parent.edge.left.parameter
        parent.edge.request.endpoint.parameter *
          parent.model.localAllowance := by
  unfold CCL.ProgressiveGaussianIntegration.CellModel.weightedAllowance
    geometricMovement
  rw [CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model_displacement]

private theorem comparisonCenteredEdge_weightedAllowance_eq {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent child : CenteredEdge curve differential) :
    (CCL.ProgressiveGaussianIntegration.PathModel.comparisonCell
      parent.model child.model).weightedAllowance =
      child.edge.pointMovement *
        (2 * (parent.model.localAllowance +
          16 * child.edge.modelErrorAllowance)) := by
  unfold CCL.ProgressiveGaussianIntegration.PathModel.comparisonCell
    CCL.ProgressiveGaussianIntegration.PathModel.parentChildAllowance
    CCL.ProgressiveGaussianIntegration.CellModel.withAllowance
    CCL.ProgressiveGaussianIntegration.CellModel.weightedAllowance
    CCL.ProgressiveGaussianIntegration.CellModel.displacement
    CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model
    CCL.Riemann.PreparedConstantModels.PreparedEdge.centeredModel
    CCL.Riemann.PreparedConstantModels.PreparedEdge.pointMovement
  rfl

private theorem comparisonCenteredEdge_weightedAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent child : CenteredEdge curve differential)
    (movementBound errorBound : Coordinate)
    (movementLe : child.edge.pointMovement <= movementBound)
    (errorLe : child.edge.modelErrorAllowance <= errorBound) :
    (CCL.ProgressiveGaussianIntegration.PathModel.comparisonCell
      parent.model child.model).weightedAllowance <=
      movementBound *
        (2 * (parent.model.localAllowance + 16 * errorBound)) := by
  have movementNonnegative : 0 <= child.edge.pointMovement :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
  have movementBoundNonnegative : 0 <= movementBound :=
    movementNonnegative.trans movementLe
  have scaledErrorLe :
      16 * child.edge.modelErrorAllowance <= 16 * errorBound :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct errorLe
      (by decide)
  have allowanceLe :
      2 * (parent.model.localAllowance +
          16 * child.edge.modelErrorAllowance) <=
        2 * (parent.model.localAllowance + 16 * errorBound) :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (add_le_add le_rfl scaledErrorLe) (by decide)
  have allowanceNonnegative :
      0 <= 2 * (parent.model.localAllowance +
        16 * child.edge.modelErrorAllowance) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg parent.model.localAllowance_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          child.edge.modelErrorAllowance_positive.le))
  rw [comparisonCenteredEdge_weightedAllowance_eq]
  exact RFAP.ConstructiveFraction.mul_le_mul_direct movementLe allowanceLe
    allowanceNonnegative movementBoundNonnegative

private theorem totalWeightedAllowance_le_of_childBounds {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (movementBound errorBound : Coordinate) :
    forall (children : List (CenteredEdge curve differential)),
      ChildMovementBound movementBound children ->
      ChildModelErrorBound errorBound children ->
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (children.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
        (children.length : Coordinate) *
          (movementBound * (16 * errorBound))
  | [], .nil, .nil => by
      simp only [List.map_nil,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_nil, List.length_nil, Nat.cast_zero,
        RFAP.ConstructiveFraction.zero_mul_direct]
      exact le_rfl
  | child :: children, .cons movementHead movementTail,
      .cons errorHead errorTail => by
      have movementNonnegative : 0 <= child.edge.pointMovement :=
        RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
      have movementBoundNonnegative : 0 <= movementBound :=
        movementNonnegative.trans movementHead
      have errorNonnegative : 0 <= child.edge.modelErrorAllowance :=
        child.edge.modelErrorAllowance_positive.le
      have scaledError :
          16 * child.edge.modelErrorAllowance <= 16 * errorBound :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct errorHead
          (by decide)
      have scaledErrorNonnegative :
          0 <= 16 * child.edge.modelErrorAllowance :=
        RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          errorNonnegative
      have headBound : child.model.weightedAllowance <=
          movementBound * (16 * errorBound) := by
        rw [centeredEdge_weightedAllowance_eq]
        exact RFAP.ConstructiveFraction.mul_le_mul_direct movementHead
          scaledError scaledErrorNonnegative movementBoundNonnegative
      have tailBound := totalWeightedAllowance_le_of_childBounds
        movementBound errorBound children movementTail errorTail
      simp only [List.map_cons,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_cons, List.length_cons, Nat.cast_succ]
      calc
        child.model.weightedAllowance +
            (children.map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model).foldr
                (fun cell total => cell.weightedAllowance + total) 0 <=
          movementBound * (16 * errorBound) +
            (children.length : Coordinate) *
              (movementBound * (16 * errorBound)) :=
          add_le_add headBound tailBound
        _ = ((children.length : Coordinate) + 1) *
            (movementBound * (16 * errorBound)) := by ring1

private theorem centeredEdge_integralSample_normSq_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (child : CenteredEdge curve differential)
    (movementBound errorBound : Coordinate)
    (movementLe : child.edge.pointMovement <= movementBound)
    (errorLe : child.edge.modelErrorAllowance <= errorBound)
    (movementBoundNonnegative : 0 <= movementBound) :
    RFAP.ConstructiveGaussian.Gaussian.normSq child.model.integralSample <=
      movementBound *
        CCL.Riemann.PreparedConstantModels.PreparedEdge.centerValueNormSqBound
          differential child.edge.segment errorBound := by
  have centerLe := child.center.value_normSq_le errorBound errorLe
  have centerNonnegative :
      0 <= RFAP.ConstructiveGaussian.Gaussian.normSq child.center.value :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
  rw [CCL.ProgressiveGaussianIntegration.PathModel.CellModel.integralSample_constant
      child.model child.center.value (by rfl),
    RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
  have displacementNorm :
      RFAP.ConstructiveGaussian.Gaussian.normSq child.model.displacement =
        child.edge.pointMovement := by
    rfl
  rw [displacementNorm]
  exact RFAP.ConstructiveFraction.mul_le_mul_direct movementLe centerLe
    centerNonnegative movementBoundNonnegative

/-- Sum of squared initial cell samples under uniform movement and model-error
targets.  This is the additive quantity consumed by finite Gaussian
Cauchy--Schwarz; it avoids constructing the total sample while scheduling. -/
private theorem centeredEdges_integralNormSqSum_le_of_childBounds
    {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2)
    (movementBound errorBound : Coordinate)
    (movementBoundNonnegative : 0 <= movementBound) :
    forall {left : Endpoint}
      {owner : Owner (curve.polynomial.eval
        (segment.pointAt left.parameter))}
      (subdivision : CCL.Riemann.PreparedSheetContinuation.Subdivision segment
        within left owner)
      (centers : CCL.Riemann.PreparedSubdivisionModels.CenterStates curve
        differential sheet subdivision),
      ChildMovementBound movementBound
          (CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve
            differential sheet subdivision centers) ->
      ChildModelErrorBound errorBound
          (CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve
            differential sheet subdivision centers) ->
      RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
          ((CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve
            differential sheet subdivision centers).map
              fun child => child.model.integralSample) <=
        (subdivision.stepCount : Coordinate) *
          (movementBound *
            CCL.Riemann.PreparedConstantModels.PreparedEdge.centerValueNormSqBound
              differential segment errorBound)
  | _, _, .stop _ _, _, movementBounds, errorBounds => by
      simp only [CCL.Riemann.PreparedSubdivisionModels.centeredEdges]
        at movementBounds errorBounds ⊢
      cases movementBounds
      cases errorBounds
      simp only [List.map_nil,
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum,
        CCL.Riemann.PreparedSheetContinuation.Subdivision.stepCount,
        Nat.cast_zero, RFAP.ConstructiveFraction.zero_mul_direct]
      exact le_rfl
  | _, _, .next left owner request cached ordered small remaining, centers,
      .cons movementHead movementTail, .cons errorHead errorTail => by
      let child : CenteredEdge curve differential :=
        { edge := CCL.Riemann.PreparedSubdivisionModels.edgeOfStep curve
            differential segment within left owner request cached ordered small
              sheet
          center := centers.1 }
      have headBound := centeredEdge_integralSample_normSq_le child
        movementBound errorBound movementHead errorHead
          movementBoundNonnegative
      have tailBound :=
        centeredEdges_integralNormSqSum_le_of_childBounds curve differential
          segment within sheet movementBound errorBound
            movementBoundNonnegative remaining centers.2 movementTail errorTail
      simp only [CCL.Riemann.PreparedSubdivisionModels.centeredEdges,
        List.map_cons, RFAP.ConstructiveFiniteNorm.gaussianNormSqSum,
        CCL.Riemann.PreparedSheetContinuation.Subdivision.stepCount,
        Nat.cast_succ]
      calc
        RFAP.ConstructiveGaussian.Gaussian.normSq child.model.integralSample +
            RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
              ((CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve
                differential sheet remaining centers.2).map
                  fun child => child.model.integralSample) <=
          movementBound *
              CCL.Riemann.PreparedConstantModels.PreparedEdge.centerValueNormSqBound
                differential segment errorBound +
            (remaining.stepCount : Coordinate) *
              (movementBound *
                CCL.Riemann.PreparedConstantModels.PreparedEdge.centerValueNormSqBound
                  differential segment errorBound) :=
          add_le_add headBound tailBound
        _ = ((remaining.stepCount : Coordinate) + 1) *
            (movementBound *
              CCL.Riemann.PreparedConstantModels.PreparedEdge.centerValueNormSqBound
                differential segment errorBound) := by ring1

private theorem centeredEdges_length_eq_stepCount {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision :
        CCL.Riemann.PreparedSheetContinuation.Subdivision segment within left
          owner)
      (centers : CCL.Riemann.PreparedSubdivisionModels.CenterStates curve
        differential sheet subdivision),
      (CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
        sheet subdivision centers).length = subdivision.stepCount
  | .stop _ _, _ => rfl
  | .next _ _ _ _ _ _ remaining, centers => by
      simp only [CCL.Riemann.PreparedSubdivisionModels.centeredEdges,
        List.length_cons,
        CCL.Riemann.PreparedSheetContinuation.Subdivision.stepCount]
      exact congrArg Nat.succ
        (centeredEdges_length_eq_stepCount curve differential sheet remaining
          centers.2)

private theorem acceptedCoordinateNatCast_nonnegative (value : Nat) :
    (0 : Coordinate) <= (value : Coordinate) := by
  induction value with
  | zero => exact le_rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ]
      exact add_nonneg inductionHypothesis (by decide)

/-- Compact total weighted allowance bound for one successful depth-`n`
prepared segment. -/
def completeDyadicTotalWeightedBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Coordinate) (depth : Nat) : Coordinate :=
  ((2 ^ depth : Nat) : Coordinate) *
    (CCL.FiniteGeometric.quarterRadius
        (geometricMovement segment
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth *
      (16 * localModelErrorBound differential segment rootDiameter depth
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
        CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter))

/-- Fixed denominator exponent for executable preflight sums.  Segmentwise
rounding at this grid changes a bound by less than `2^-32` while ensuring all
path additions have a common dyadic denominator. -/
def preflightDyadicPrecision : Nat := 32

def preflightDyadicScale : Coordinate :=
  (2 : Coordinate) ^ preflightDyadicPrecision

def dyadicPreflightUpper (source : Coordinate) : Coordinate :=
  RFAP.CanonicalFraction.fromInt
      (Int.ofNat
        (RFAP.ConstructiveFraction.ceilNat
          (source * preflightDyadicScale))) /
    preflightDyadicScale

private theorem preflightDyadicScale_positive :
    (0 : Coordinate) < preflightDyadicScale := by
  unfold preflightDyadicScale
  exact RFAP.ConstructiveFraction.pow_pos_direct (by decide)
    preflightDyadicPrecision

theorem le_dyadicPreflightUpper {source : Coordinate}
    (nonnegative : 0 <= source) : source <= dyadicPreflightUpper source := by
  unfold dyadicPreflightUpper
  apply (RFAP.ConstructiveFraction.le_div_iff_pos
    preflightDyadicScale_positive).2
  have ceilingBound :=
    RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg
    (RFAP.ConstructiveFraction.mul_nonneg_direct nonnegative
      preflightDyadicScale_positive.le)
  rw [RFAP.CanonicalFraction.natCast_eq_fromInt] at ceilingBound
  exact ceilingBound

theorem dyadicPreflightUpper_nonnegative {source : Coordinate}
    (nonnegative : 0 <= source) : 0 <= dyadicPreflightUpper source :=
  nonnegative.trans (le_dyadicPreflightUpper nonnegative)

theorem completeDyadicTotalWeightedBound_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    {rootDiameter : Coordinate} (rootDiameterNonnegative : 0 <= rootDiameter)
    (depth : Nat) :
    0 <= completeDyadicTotalWeightedBound differential segment rootDiameter
      depth := by
  unfold completeDyadicTotalWeightedBound
  exact RFAP.ConstructiveFraction.mul_nonneg_direct
    (acceptedCoordinateNatCast_nonnegative _)
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (CCL.FiniteGeometric.quarterRadius_nonneg
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _) depth)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (localModelErrorBound_nonnegative differential segment
          rootDiameterNonnegative depth
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter)))

/-- Common-denominator upper envelope of the owner-independent total-weight
bound for one original clear segment. -/
def completeDyadicTotalWeightedDyadicBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Coordinate) (depth : Nat) : Coordinate :=
  dyadicPreflightUpper
    (completeDyadicTotalWeightedBound differential segment rootDiameter depth)

theorem completeDyadicTotalWeightedBound_le_dyadicBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    {rootDiameter : Coordinate} (rootDiameterNonnegative : 0 <= rootDiameter)
    (depth : Nat) :
    completeDyadicTotalWeightedBound differential segment rootDiameter depth <=
      completeDyadicTotalWeightedDyadicBound differential segment rootDiameter
        depth :=
  le_dyadicPreflightUpper
    (completeDyadicTotalWeightedBound_nonnegative differential segment
      rootDiameterNonnegative depth)

/-- The corresponding compact segment bound using the largest root-box
diameter actually retained by the accepted subdivision.  Its coefficient
terms are evaluated once for the original segment, while its only leaf-level
work is a maximum over cached rational box diagonals. -/
def completePreparedDyadicTotalWeightedBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) : Coordinate :=
  ((2 ^ depth : Nat) : Coordinate) *
    (CCL.FiniteGeometric.quarterRadius
        (geometricMovement segment
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth *
      (16 * localModelErrorBound differential segment
        (subdivisionPreparedRootDiameterMaximum prepared.subdivision) depth
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter))

theorem completePreparedDyadicTotalWeightedBound_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    0 <= completePreparedDyadicTotalWeightedBound differential segment within
      owner prepared depth := by
  unfold completePreparedDyadicTotalWeightedBound
  exact RFAP.ConstructiveFraction.mul_nonneg_direct
    (acceptedCoordinateNatCast_nonnegative _)
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (CCL.FiniteGeometric.quarterRadius_nonneg
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _) depth)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (localModelErrorBound_nonnegative differential segment
          (subdivisionPreparedRootDiameterMaximum_nonnegative
            prepared.subdivision) depth
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter)))

/-- Common-denominator upper envelope of one exact segment allowance. -/
def completePreparedDyadicTotalWeightedDyadicBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) : Coordinate :=
  dyadicPreflightUpper
    (completePreparedDyadicTotalWeightedBound differential segment within owner
      prepared depth)

theorem completePreparedDyadicTotalWeightedBound_le_dyadicBound
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    completePreparedDyadicTotalWeightedBound differential segment within owner
        prepared depth <=
      completePreparedDyadicTotalWeightedDyadicBound differential segment
        within owner prepared depth :=
  le_dyadicPreflightUpper
    (completePreparedDyadicTotalWeightedBound_nonnegative differential segment
      within owner prepared depth)

/-- Conservative squared-sample bound for one successful depth-`n` segment.
Unlike the sharper prepared bound below, this uses the common requested root
diameter and therefore never traverses the accepted subdivision. -/
def completeDyadicIntegralNormSqSumBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Coordinate) (depth : Nat) : Coordinate :=
  ((2 ^ depth : Nat) : Coordinate) *
    (CCL.FiniteGeometric.quarterRadius
        (geometricMovement segment
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth *
      CCL.Riemann.PreparedConstantModels.PreparedEdge.centerValueNormSqBound
        differential segment
          (localModelErrorBound differential segment rootDiameter depth
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
            CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter))

/-- Cheaper residual-floor envelope for the same owner-independent segment
bound. -/
def completeDyadicIntegralNormSqResidualBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Coordinate) (depth : Nat) : Coordinate :=
  ((2 ^ depth : Nat) : Coordinate) *
    (CCL.FiniteGeometric.quarterRadius
        (geometricMovement segment
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth *
      CCL.Riemann.PreparedConstantModels.PreparedEdge.centerValueNormSqResidualBound
        differential segment
          (localModelErrorBound differential segment rootDiameter depth
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
            CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter))

theorem completeDyadicIntegralNormSqSumBound_le_residual {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Coordinate) (depth : Nat) :
    completeDyadicIntegralNormSqSumBound differential segment rootDiameter
        depth <=
      completeDyadicIntegralNormSqResidualBound differential segment
        rootDiameter depth := by
  unfold completeDyadicIntegralNormSqSumBound
    completeDyadicIntegralNormSqResidualBound
  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
  · apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (CCL.Riemann.PreparedConstantModels.PreparedEdge.centerValueNormSqBound_le_residual
        differential segment _)
    exact CCL.FiniteGeometric.quarterRadius_nonneg
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _) depth
  · exact acceptedCoordinateNatCast_nonnegative _

theorem completeDyadicIntegralNormSqResidualBound_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    {rootDiameter : Coordinate} (rootDiameterNonnegative : 0 <= rootDiameter)
    (depth : Nat) :
    0 <= completeDyadicIntegralNormSqResidualBound differential segment
      rootDiameter depth := by
  unfold completeDyadicIntegralNormSqResidualBound
  exact RFAP.ConstructiveFraction.mul_nonneg_direct
    (acceptedCoordinateNatCast_nonnegative _)
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (CCL.FiniteGeometric.quarterRadius_nonneg
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _) depth)
      (CCL.Riemann.PreparedConstantModels.PreparedEdge.centerValueNormSqResidualBound_nonnegative
        differential segment
        (localModelErrorBound_nonnegative differential segment
          rootDiameterNonnegative depth
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter)))

/-- Integral-valued owner-independent segment envelope, so long path sums
remain denominator-one rational arithmetic. -/
def completeDyadicIntegralNormSqCeilBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Coordinate) (depth : Nat) : Coordinate :=
  RFAP.CanonicalFraction.fromInt
    (Int.ofNat
      (RFAP.ConstructiveFraction.ceilNat
        (completeDyadicIntegralNormSqResidualBound differential segment
          rootDiameter depth)))

theorem completeDyadicIntegralNormSqSumBound_le_ceilBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    {rootDiameter : Coordinate} (rootDiameterNonnegative : 0 <= rootDiameter)
    (depth : Nat) :
    completeDyadicIntegralNormSqSumBound differential segment rootDiameter
        depth <=
      completeDyadicIntegralNormSqCeilBound differential segment rootDiameter
        depth := by
  unfold completeDyadicIntegralNormSqCeilBound
  have ceilingBound :=
    RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg
      (completeDyadicIntegralNormSqResidualBound_nonnegative differential
        segment rootDiameterNonnegative depth)
  rw [RFAP.CanonicalFraction.natCast_eq_fromInt] at ceilingBound
  exact (completeDyadicIntegralNormSqSumBound_le_residual differential segment
    rootDiameter depth).trans ceilingBound

/-- Compact sum-of-squared-samples bound for one accepted depth-`n` segment.
It evaluates the ambient coefficient bound once and traverses the subdivision
only for its cached maximum root-box diameter. -/
def completePreparedDyadicIntegralNormSqSumBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) : Coordinate :=
  ((2 ^ depth : Nat) : Coordinate) *
    (CCL.FiniteGeometric.quarterRadius
        (geometricMovement segment
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth *
      CCL.Riemann.PreparedConstantModels.PreparedEdge.centerValueNormSqBound
        differential segment
          (localModelErrorBound differential segment
            (subdivisionPreparedRootDiameterMaximum prepared.subdivision) depth
              CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
              CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter))

theorem completePreparedDyadicIntegralNormSqSumBound_nonnegative
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    0 <= completePreparedDyadicIntegralNormSqSumBound differential segment
      within owner prepared depth := by
  unfold completePreparedDyadicIntegralNormSqSumBound
  exact RFAP.ConstructiveFraction.mul_nonneg_direct
    (acceptedCoordinateNatCast_nonnegative _)
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (CCL.FiniteGeometric.quarterRadius_nonneg
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _) depth)
      (CCL.Riemann.PreparedConstantModels.PreparedEdge.centerValueNormSqBound_nonnegative
        differential segment
        (localModelErrorBound_nonnegative differential segment
          (subdivisionPreparedRootDiameterMaximum_nonnegative
            prepared.subdivision) depth
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter)))

/-- The same segment expression with the cheaper residual-floor coefficient
bound.  This quantity is used only as a sample envelope; the sharper local
error and total-weight calculations remain unchanged. -/
def completePreparedDyadicIntegralNormSqResidualBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) : Coordinate :=
  ((2 ^ depth : Nat) : Coordinate) *
    (CCL.FiniteGeometric.quarterRadius
        (geometricMovement segment
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth *
      CCL.Riemann.PreparedConstantModels.PreparedEdge.centerValueNormSqResidualBound
        differential segment
          (localModelErrorBound differential segment
            (subdivisionPreparedRootDiameterMaximum prepared.subdivision) depth
              CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
              CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter))

theorem completePreparedDyadicIntegralNormSqSumBound_le_residual
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    completePreparedDyadicIntegralNormSqSumBound differential segment within
        owner prepared depth <=
      completePreparedDyadicIntegralNormSqResidualBound differential segment
        within owner prepared depth := by
  unfold completePreparedDyadicIntegralNormSqSumBound
    completePreparedDyadicIntegralNormSqResidualBound
  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
  · apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (CCL.Riemann.PreparedConstantModels.PreparedEdge.centerValueNormSqBound_le_residual
        differential segment _)
    exact CCL.FiniteGeometric.quarterRadius_nonneg
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _) depth
  · exact acceptedCoordinateNatCast_nonnegative _

theorem completePreparedDyadicIntegralNormSqResidualBound_nonnegative
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    0 <= completePreparedDyadicIntegralNormSqResidualBound differential segment
      within owner prepared depth := by
  unfold completePreparedDyadicIntegralNormSqResidualBound
  exact RFAP.ConstructiveFraction.mul_nonneg_direct
    (acceptedCoordinateNatCast_nonnegative _)
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (CCL.FiniteGeometric.quarterRadius_nonneg
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _) depth)
      (CCL.Riemann.PreparedConstantModels.PreparedEdge.centerValueNormSqResidualBound_nonnegative
        differential segment
        (localModelErrorBound_nonnegative differential segment
          (subdivisionPreparedRootDiameterMaximum_nonnegative
            prepared.subdivision) depth
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter)))

/-- Integral-valued upper envelope of one segment's compact squared-sample
bound.  Rounding before path accumulation keeps all subsequent additions at
denominator one while retaining a proved upper bound on the exact rational
quantity. -/
def completePreparedDyadicIntegralNormSqCeilBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) : Coordinate :=
  RFAP.CanonicalFraction.fromInt
    (Int.ofNat
      (RFAP.ConstructiveFraction.ceilNat
        (completePreparedDyadicIntegralNormSqResidualBound differential segment
          within owner prepared depth)))

theorem completePreparedDyadicIntegralNormSqSumBound_le_ceilBound
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    completePreparedDyadicIntegralNormSqSumBound differential segment within
        owner prepared depth <=
      completePreparedDyadicIntegralNormSqCeilBound differential segment
        within owner prepared depth := by
  unfold completePreparedDyadicIntegralNormSqCeilBound
  have ceilingBound :=
    RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg
      (completePreparedDyadicIntegralNormSqResidualBound_nonnegative
        differential segment within owner prepared depth)
  rw [RFAP.CanonicalFraction.natCast_eq_fromInt] at ceilingBound
  exact (completePreparedDyadicIntegralNormSqSumBound_le_residual differential
    segment within owner prepared depth).trans ceilingBound

/-- Paired compact segment summary.  Both consumers share the cached-root
maximum and local error computation instead of traversing the accepted
subdivision twice. -/
structure PreparedSegmentPreflightBounds where
  totalWeighted : Coordinate
  integralNormSqSum : Coordinate

def completePreparedDyadicPreflightBounds {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) : PreparedSegmentPreflightBounds :=
  let count : Coordinate := ((2 ^ depth : Nat) : Coordinate)
  let movement := CCL.FiniteGeometric.quarterRadius
    (geometricMovement segment
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth
  let rootMaximum :=
    subdivisionPreparedRootDiameterMaximum prepared.subdivision
  let localBounds := preparedSegmentLocalErrorBounds differential segment rootMaximum
    depth CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter
  let error := localBounds.error
  { totalWeighted :=
      dyadicPreflightUpper (count * (movement * (16 * error)))
    integralNormSqSum :=
      RFAP.CanonicalFraction.fromInt
        (Int.ofNat
          (RFAP.ConstructiveFraction.ceilNat
            (count *
              (movement *
                CCL.Riemann.PreparedConstantModels.PreparedEdge.centerValueNormSqResidualBound
                  differential segment error)))) }

@[simp] theorem completePreparedDyadicPreflightBounds_totalWeighted
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    (completePreparedDyadicPreflightBounds differential segment within owner
      prepared depth).totalWeighted =
        completePreparedDyadicTotalWeightedDyadicBound differential segment within
          owner prepared depth := rfl

@[simp] theorem completePreparedDyadicPreflightBounds_integralNormSqSum
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    (completePreparedDyadicPreflightBounds differential segment within owner
      prepared depth).integralNormSqSum =
        completePreparedDyadicIntegralNormSqCeilBound differential segment
          within owner prepared depth := rfl

/-- Compact aggregate allowance bound for one successful depth-`n` prepared
segment.  Its value depends only on the original affine segment,
differential, common root diameter, and depth; evaluating it never
reconstructs the accepted owner chain or any coefficient centre. -/
def completeDyadicAggregateBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Coordinate) (depth : Nat) : Coordinate :=
  ((2 ^ depth : Nat) : Coordinate) *
    completeDyadicTotalWeightedBound differential segment rootDiameter depth

/-- Total weighted allowance of the actual accepted segment cells is bounded
without evaluating those cells. -/
theorem completeSegmentOfTryDyadic_totalWeightedAllowance_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : CCL.Riemann.PreparedSheetContinuation.Subdivision segment
      within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)}
    (success :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic segment
          within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
            CCL.Riemann.PreparedClearPathModels.oneEndpoint
              (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
                depth rootDiameter rootDiameterPositive = some subdivision) :
    let prepared :=
      CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic segment
        within owner depth rootDiameter rootDiameterPositive success
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((prepared.centeredEdges curve differential sheet).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
      completeDyadicTotalWeightedBound differential segment rootDiameter
        depth := by
  let movementBound := CCL.FiniteGeometric.quarterRadius
    (geometricMovement segment
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment rootDiameter
    depth CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter
  let centers :=
    CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates curve
      differential sheet subdivision
  have bounds := trySteps_childBounds curve differential segment within sheet
    movementBound rootDiameter
      (CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
      (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
      (dyadicRequests_targets segment depth
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      success centers
  change
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
        sheet subdivision centers).map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <= _
  have totalBound := totalWeightedAllowance_le_of_childBounds movementBound
    errorBound _ bounds.1 bounds.2
  rw [centeredEdges_length_eq_stepCount curve differential sheet subdivision
      centers,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic_stepCount
      segment within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint
          (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
            depth rootDiameter rootDiameterPositive success] at totalBound
  simpa only [completeDyadicTotalWeightedBound, movementBound, errorBound]
    using totalBound

/-- The same accepted cells satisfy the sharper compact bound obtained from
the maximum of their cached prepared root boxes. -/
theorem completeSegmentOfTryDyadic_preparedTotalWeightedAllowance_le
    {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : CCL.Riemann.PreparedSheetContinuation.Subdivision segment
      within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)}
    (success :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic segment
          within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
            CCL.Riemann.PreparedClearPathModels.oneEndpoint
              (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
                depth rootDiameter rootDiameterPositive = some subdivision) :
    let prepared :=
      CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic segment
        within owner depth rootDiameter rootDiameterPositive success
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((prepared.centeredEdges curve differential sheet).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
      completePreparedDyadicTotalWeightedBound differential segment within
        owner prepared depth := by
  let movementBound := CCL.FiniteGeometric.quarterRadius
    (geometricMovement segment
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment
    (subdivisionPreparedRootDiameterMaximum subdivision) depth
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter
  let centers :=
    CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates curve
      differential sheet subdivision
  have requestBounds := trySteps_childBounds curve differential segment within
    sheet movementBound rootDiameter
      (CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
      (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
      (dyadicRequests_targets segment depth
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      success centers
  have actualErrorBound :=
    centeredEdges_childModelErrorBound_at_actualMaximum curve differential
      segment within sheet movementBound subdivision centers requestBounds.1
  change
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
        sheet subdivision centers).map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <= _
  have totalBound := totalWeightedAllowance_le_of_childBounds movementBound
    errorBound _ requestBounds.1 actualErrorBound
  rw [centeredEdges_length_eq_stepCount curve differential sheet subdivision
      centers,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic_stepCount
      segment within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint
          (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
            depth rootDiameter rootDiameterPositive success] at totalBound
  simpa only [completePreparedDyadicTotalWeightedBound, movementBound,
    errorBound, CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic]
    using totalBound

/-- The squared norms of a successful segment's initial samples are bounded
by the common requested root diameter.  This is the owner-independent proof
used by the shortest executable preflight path. -/
theorem completeSegmentOfTryDyadic_integralNormSqSum_le
    {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : CCL.Riemann.PreparedSheetContinuation.Subdivision segment
      within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)}
    (success :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic segment
          within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
            CCL.Riemann.PreparedClearPathModels.oneEndpoint
              (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
                depth rootDiameter rootDiameterPositive = some subdivision) :
    let prepared :=
      CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic segment
        within owner depth rootDiameter rootDiameterPositive success
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
      ((prepared.centeredEdges curve differential sheet).map
        fun child => child.model.integralSample) <=
      completeDyadicIntegralNormSqSumBound differential segment rootDiameter
        depth := by
  let movementBound := CCL.FiniteGeometric.quarterRadius
    (geometricMovement segment
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment rootDiameter
    depth CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter
  let centers :=
    CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates curve
      differential sheet subdivision
  have requestBounds := trySteps_childBounds curve differential segment within
    sheet movementBound rootDiameter
      (CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
      (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
      (dyadicRequests_targets segment depth
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      success centers
  have movementBoundNonnegative : 0 <= movementBound :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _) depth
  change
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
      ((CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
        sheet subdivision centers).map
          fun child => child.model.integralSample) <= _
  have sampleBound :=
    centeredEdges_integralNormSqSum_le_of_childBounds curve differential
      segment within sheet movementBound errorBound movementBoundNonnegative
        subdivision centers requestBounds.1 requestBounds.2
  rw [CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic_stepCount
      segment within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint
          (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
            depth rootDiameter rootDiameterPositive success] at sampleBound
  simpa only [completeDyadicIntegralNormSqSumBound, movementBound, errorBound,
    CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic]
    using sampleBound

/-- The squared norms of the accepted segment's initial cell samples admit a
compact bound which never evaluates a persisted coefficient centre. -/
theorem completeSegmentOfTryDyadic_preparedIntegralNormSqSum_le
    {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : CCL.Riemann.PreparedSheetContinuation.Subdivision segment
      within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)}
    (success :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic segment
          within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
            CCL.Riemann.PreparedClearPathModels.oneEndpoint
              (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
                depth rootDiameter rootDiameterPositive = some subdivision) :
    let prepared :=
      CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic segment
        within owner depth rootDiameter rootDiameterPositive success
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
      ((prepared.centeredEdges curve differential sheet).map
        fun child => child.model.integralSample) <=
      completePreparedDyadicIntegralNormSqSumBound differential segment within
        owner prepared depth := by
  let movementBound := CCL.FiniteGeometric.quarterRadius
    (geometricMovement segment
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment
    (subdivisionPreparedRootDiameterMaximum subdivision) depth
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter
  let centers :=
    CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates curve
      differential sheet subdivision
  have requestBounds := trySteps_childBounds curve differential segment within
    sheet movementBound rootDiameter
      (CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
      (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
      (dyadicRequests_targets segment depth
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      success centers
  have actualErrorBound :=
    centeredEdges_childModelErrorBound_at_actualMaximum curve differential
      segment within sheet movementBound subdivision centers requestBounds.1
  have movementBoundNonnegative : 0 <= movementBound :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _) depth
  change
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
      ((CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
        sheet subdivision centers).map
          fun child => child.model.integralSample) <= _
  have sampleBound :=
    centeredEdges_integralNormSqSum_le_of_childBounds curve differential
      segment within sheet movementBound errorBound movementBoundNonnegative
        subdivision centers requestBounds.1 actualErrorBound
  rw [CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic_stepCount
      segment within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint
          (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
            depth rootDiameter rootDiameterPositive success] at sampleBound
  simpa only [completePreparedDyadicIntegralNormSqSumBound, movementBound,
    errorBound, CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic]
    using sampleBound

/-- Owner-dependent prepared subdivisions inherit the same compact total-
weight bound whenever their retained requests are exactly the canonical
depth-`n` dyadic requests. -/
theorem completePreparedSegment_totalWeightedAllowance_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (requests_eq : prepared.subdivision.requests =
      CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((prepared.centeredEdges curve differential sheet).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
      completeDyadicTotalWeightedBound differential segment rootDiameter
        depth := by
  let movementBound := CCL.FiniteGeometric.quarterRadius
    (geometricMovement segment
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment rootDiameter
    depth CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter
  let subdivision := prepared.subdivision
  let centers := CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates
    curve differential sheet subdivision
  have targets : RequestTargets segment movementBound rootDiameter
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint subdivision.requests := by
    rw [requests_eq]
    exact dyadicRequests_targets segment depth
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
          rootDiameterPositive
  have bounds := subdivision_childBounds curve differential segment within
    sheet movementBound rootDiameter subdivision targets centers
  change
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
        sheet subdivision centers).map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <= _
  have totalBound := totalWeightedAllowance_le_of_childBounds movementBound
    errorBound _ bounds.1 bounds.2
  have stepCount : subdivision.stepCount = 2 ^ depth := by
    rw [← CCL.Riemann.PreparedSheetContinuation.Subdivision.requests_length,
      requests_eq]
    simp only [CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests,
      CCL.Riemann.PreparedSheetContinuation.Subdivision.requestsAtDiameter_length,
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets_length]
  rw [centeredEdges_length_eq_stepCount curve differential sheet subdivision
      centers, stepCount] at totalBound
  simpa only [completeDyadicTotalWeightedBound, movementBound, errorBound]
    using totalBound

/-- The same request provenance supplies the sharper retained-owner total-
weight bound. -/
theorem completePreparedSegment_preparedTotalWeightedAllowance_le
    {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (requests_eq : prepared.subdivision.requests =
      CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((prepared.centeredEdges curve differential sheet).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
      completePreparedDyadicTotalWeightedBound differential segment within
        owner prepared depth := by
  let movementBound := CCL.FiniteGeometric.quarterRadius
    (geometricMovement segment
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment
    (subdivisionPreparedRootDiameterMaximum prepared.subdivision) depth
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter
  let subdivision := prepared.subdivision
  let centers := CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates
    curve differential sheet subdivision
  have targets : RequestTargets segment movementBound rootDiameter
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint subdivision.requests := by
    rw [requests_eq]
    exact dyadicRequests_targets segment depth
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
          rootDiameterPositive
  have requestBounds := subdivision_childBounds curve differential segment
    within sheet movementBound rootDiameter subdivision targets centers
  have actualErrorBound :=
    centeredEdges_childModelErrorBound_at_actualMaximum curve differential
      segment within sheet movementBound subdivision centers requestBounds.1
  change
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
        sheet subdivision centers).map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <= _
  have totalBound := totalWeightedAllowance_le_of_childBounds movementBound
    errorBound _ requestBounds.1 actualErrorBound
  have stepCount : subdivision.stepCount = 2 ^ depth := by
    rw [← CCL.Riemann.PreparedSheetContinuation.Subdivision.requests_length,
      requests_eq]
    simp only [CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests,
      CCL.Riemann.PreparedSheetContinuation.Subdivision.requestsAtDiameter_length,
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets_length]
  rw [centeredEdges_length_eq_stepCount curve differential sheet subdivision
      centers, stepCount] at totalBound
  simpa only [completePreparedDyadicTotalWeightedBound, movementBound,
    errorBound, subdivision] using totalBound

/-- Canonical request provenance bounds the sum of initial cell-sample norms
without reconstructing a checker result. -/
theorem completePreparedSegment_integralNormSqSum_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (requests_eq : prepared.subdivision.requests =
      CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive) :
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
      ((prepared.centeredEdges curve differential sheet).map
        fun child => child.model.integralSample) <=
      completeDyadicIntegralNormSqSumBound differential segment rootDiameter
        depth := by
  let movementBound := CCL.FiniteGeometric.quarterRadius
    (geometricMovement segment
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment rootDiameter
    depth CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter
  let subdivision := prepared.subdivision
  let centers := CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates
    curve differential sheet subdivision
  have targets : RequestTargets segment movementBound rootDiameter
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint subdivision.requests := by
    rw [requests_eq]
    exact dyadicRequests_targets segment depth
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
          rootDiameterPositive
  have requestBounds := subdivision_childBounds curve differential segment
    within sheet movementBound rootDiameter subdivision targets centers
  have movementBoundNonnegative : 0 <= movementBound :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _) depth
  change
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
      ((CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
        sheet subdivision centers).map
          fun child => child.model.integralSample) <= _
  have sampleBound :=
    centeredEdges_integralNormSqSum_le_of_childBounds curve differential
      segment within sheet movementBound errorBound movementBoundNonnegative
        subdivision centers requestBounds.1 requestBounds.2
  have stepCount : subdivision.stepCount = 2 ^ depth := by
    rw [← CCL.Riemann.PreparedSheetContinuation.Subdivision.requests_length,
      requests_eq]
    simp only [CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests,
      CCL.Riemann.PreparedSheetContinuation.Subdivision.requestsAtDiameter_length,
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets_length]
  rw [stepCount] at sampleBound
  simpa only [completeDyadicIntegralNormSqSumBound, movementBound, errorBound]
    using sampleBound

/-- Retained-owner counterpart of the preceding initial-sample bound. -/
theorem completePreparedSegment_preparedIntegralNormSqSum_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (prepared : CCL.Riemann.PreparedClearPathModels.CompleteSegment segment
      within owner)
    (requests_eq : prepared.subdivision.requests =
      CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive) :
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
      ((prepared.centeredEdges curve differential sheet).map
        fun child => child.model.integralSample) <=
      completePreparedDyadicIntegralNormSqSumBound differential segment within
        owner prepared depth := by
  let movementBound := CCL.FiniteGeometric.quarterRadius
    (geometricMovement segment
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment
    (subdivisionPreparedRootDiameterMaximum prepared.subdivision) depth
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter
  let subdivision := prepared.subdivision
  let centers := CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates
    curve differential sheet subdivision
  have targets : RequestTargets segment movementBound rootDiameter
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint subdivision.requests := by
    rw [requests_eq]
    exact dyadicRequests_targets segment depth
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
          rootDiameterPositive
  have requestBounds := subdivision_childBounds curve differential segment
    within sheet movementBound rootDiameter subdivision targets centers
  have actualErrorBound :=
    centeredEdges_childModelErrorBound_at_actualMaximum curve differential
      segment within sheet movementBound subdivision centers requestBounds.1
  have movementBoundNonnegative : 0 <= movementBound :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _) depth
  change
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
      ((CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
        sheet subdivision centers).map
          fun child => child.model.integralSample) <= _
  have sampleBound :=
    centeredEdges_integralNormSqSum_le_of_childBounds curve differential
      segment within sheet movementBound errorBound movementBoundNonnegative
        subdivision centers requestBounds.1 actualErrorBound
  have stepCount : subdivision.stepCount = 2 ^ depth := by
    rw [← CCL.Riemann.PreparedSheetContinuation.Subdivision.requests_length,
      requests_eq]
    simp only [CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests,
      CCL.Riemann.PreparedSheetContinuation.Subdivision.requestsAtDiameter_length,
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets_length]
  rw [stepCount] at sampleBound
  simpa only [completePreparedDyadicIntegralNormSqSumBound, movementBound,
    errorBound, subdivision] using sampleBound

/-- The actual centred model returned by a successful complete-segment
checker is bounded by the compact segment expression above. -/
theorem completeSegmentOfTryDyadic_aggregateAllowance_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : CCL.Riemann.PreparedSheetContinuation.Subdivision segment
      within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)}
    (success :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic segment
          within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
            CCL.Riemann.PreparedClearPathModels.oneEndpoint
              (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
                depth rootDiameter rootDiameterPositive = some subdivision) :
    let prepared :=
      CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic segment
        within owner depth rootDiameter rootDiameterPositive success
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((prepared.centeredEdges curve differential sheet).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
      completeDyadicAggregateBound differential segment rootDiameter depth := by
  let movementBound := CCL.FiniteGeometric.quarterRadius
    (geometricMovement segment
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment rootDiameter
    depth CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
      CCL.Riemann.PreparedClearPathModels.oneEndpoint.parameter
  let prepared :=
    CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic segment
      within owner depth rootDiameter rootDiameterPositive success
  let centers :=
    CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates curve
      differential sheet subdivision
  have bounds := trySteps_childBounds curve differential segment within sheet
    movementBound rootDiameter
      (CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
      (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
      (dyadicRequests_targets segment depth
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      success centers
  change
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
        sheet subdivision centers).map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <= _
  unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
  rw [List.length_map]
  have totalBound := totalWeightedAllowance_le_of_childBounds movementBound
    errorBound _ bounds.1 bounds.2
  have countNonnegative : (0 : Coordinate) <=
      ((CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
        sheet subdivision centers).length : Coordinate) :=
    acceptedCoordinateNatCast_nonnegative _
  have scaled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct totalBound
      countNonnegative
  rw [centeredEdges_length_eq_stepCount curve differential sheet subdivision
      centers,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic_stepCount
      segment within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint
          (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
            depth rootDiameter rootDiameterPositive success] at scaled
  rw [centeredEdges_length_eq_stepCount curve differential sheet subdivision
      centers,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic_stepCount
      segment within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint
          (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
            depth rootDiameter rootDiameterPositive success]
  simpa only [completeDyadicAggregateBound,
    completeDyadicTotalWeightedBound, movementBound, errorBound] using scaled

private theorem totalComparisonAllowance_le_of_childBounds {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential)
    (movementBound errorBound : Coordinate) :
    forall (children : List (CenteredEdge curve differential)),
      ChildMovementBound movementBound children ->
      ChildModelErrorBound errorBound children ->
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (children.map (fun child =>
          CCL.ProgressiveGaussianIntegration.PathModel.comparisonCell
            parent.model child.model))).totalWeightedAllowance <=
        (children.length : Coordinate) *
          (movementBound *
            (2 * (parent.model.localAllowance + 16 * errorBound)))
  | [], .nil, .nil => by
      simp only [List.map_nil,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_nil, List.length_nil, Nat.cast_zero,
        RFAP.ConstructiveFraction.zero_mul_direct]
      exact le_rfl
  | child :: children, .cons movementHead movementTail,
      .cons errorHead errorTail => by
      have headBound := comparisonCenteredEdge_weightedAllowance_le
        parent child movementBound errorBound movementHead errorHead
      have tailBound := totalComparisonAllowance_le_of_childBounds
        parent movementBound errorBound children movementTail errorTail
      simp only [List.map_cons,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_cons, List.length_cons, Nat.cast_succ]
      calc
        (CCL.ProgressiveGaussianIntegration.PathModel.comparisonCell
            parent.model child.model).weightedAllowance +
            (children.map (fun remaining =>
              CCL.ProgressiveGaussianIntegration.PathModel.comparisonCell
                parent.model remaining.model)).foldr
                (fun cell total => cell.weightedAllowance + total) 0 <=
          movementBound *
              (2 * (parent.model.localAllowance + 16 * errorBound)) +
            (children.length : Coordinate) *
              (movementBound *
                (2 * (parent.model.localAllowance + 16 * errorBound))) :=
          add_le_add headBound tailBound
        _ = ((children.length : Coordinate) + 1) *
            (movementBound *
              (2 * (parent.model.localAllowance + 16 * errorBound))) := by
          ring1

private theorem totalWeightedAllowance_append
    (first second :
      List CCL.ProgressiveGaussianIntegration.CellModel) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (first ++ second)).totalWeightedAllowance =
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        first).totalWeightedAllowance +
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        second).totalWeightedAllowance := by
  induction first with
  | nil =>
      simp only [List.nil_append,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_nil]
      rw [zero_add]
  | cons cell remaining inductionHypothesis =>
      simp only [List.cons_append,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_cons]
      change
        (remaining ++ second).foldr
            (fun model total => model.weightedAllowance + total) 0 =
          remaining.foldr
              (fun model total => model.weightedAllowance + total) 0 +
            second.foldr
              (fun model total => model.weightedAllowance + total) 0 at inductionHypothesis
      rw [inductionHypothesis]
      ring1

private theorem gaussianNormSqSum_append (first second : List Gaussian) :
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum (first ++ second) =
      RFAP.ConstructiveFiniteNorm.gaussianNormSqSum first +
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum second := by
  induction first with
  | nil =>
      simp only [List.nil_append,
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum]
      rw [zero_add]
  | cons value remaining inductionHypothesis =>
      simp only [List.cons_append,
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum]
      rw [inductionHypothesis]
      ring1

private def castCompatibleChildren
    {parents first second :
      List CCL.ProgressiveGaussianIntegration.CellModel}
    (refinement : CompatibleConstantPathRefinement parents first)
    (equal : first = second) :
    CompatibleConstantPathRefinement parents second :=
  equal ▸ refinement

private theorem castCompatibleChildren_comparisonAllowance_eq
    {parents first second :
      List CCL.ProgressiveGaussianIntegration.CellModel}
    (refinement : CompatibleConstantPathRefinement parents first)
    (equal : first = second) :
    (castCompatibleChildren refinement equal).comparisonAllowance =
      refinement.comparisonAllowance := by
  cases equal
  rfl

namespace DirectParentBlock

private theorem coordinateNatCast_nonnegative (value : Nat) :
    (0 : Coordinate) <= (value : Coordinate) := by
  induction value with
  | zero => exact le_rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ]
      exact add_nonneg inductionHypothesis (by decide)

private theorem coordinatePow_ne_zero (value : Coordinate)
    (nonzero : value ≠ 0) : forall exponent : Nat, value ^ exponent ≠ 0
  | 0 => by
      change (1 : Coordinate) ≠ 0
      decide
  | exponent + 1 => by
      rw [pow_succ]
      exact RFAP.ConstructiveFraction.mul_ne_zero_direct
        (coordinatePow_ne_zero value nonzero exponent) nonzero

private theorem dyadicCountSquare_mul_quarterRadius
    (scale : Coordinate) (depth : Nat) :
    ((2 ^ depth : Nat) : Coordinate) *
        (((2 ^ depth : Nat) : Coordinate) *
          CCL.FiniteGeometric.quarterRadius scale depth) =
      scale := by
  unfold CCL.FiniteGeometric.quarterRadius
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have countSquare :
      (2 : Coordinate) ^ depth * (2 : Coordinate) ^ depth =
        (4 : Coordinate) ^ depth := by
    rw [<- mul_pow]
    congr 1
  calc
    (2 : Coordinate) ^ depth *
        ((2 : Coordinate) ^ depth *
          (scale / (4 : Coordinate) ^ depth)) =
      (scale / (4 : Coordinate) ^ depth) *
        ((2 : Coordinate) ^ depth * (2 : Coordinate) ^ depth) := by
      ring1
    _ = (scale / (4 : Coordinate) ^ depth) *
        (4 : Coordinate) ^ depth := by
      rw [countSquare]
    _ = scale :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne scale
        ((4 : Coordinate) ^ depth)
        (coordinatePow_ne_zero (4 : Coordinate) (by decide) depth)

/-- View every child in a direct block with one caller-supplied comparison
allowance.  Geometry, polynomial, and integral samples are unchanged. -/
def constantAllowanceCells {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : CenteredEdge curve differential}
    (block : DirectParentBlock parent) (allowance : Coordinate)
    (allowanceNonnegative : 0 <= allowance) :
    List CCL.ProgressiveGaussianIntegration.CellModel :=
  block.children.map fun child =>
    child.model.withAllowance allowance allowanceNonnegative

private theorem totalConstantAllowance_le_of_movements {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (movementBound allowance : Coordinate)
    (allowanceNonnegative : 0 <= allowance) :
    forall (children : List (CenteredEdge curve differential)),
      ChildMovementBound movementBound children ->
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (children.map fun child =>
          child.model.withAllowance allowance
            allowanceNonnegative)).totalWeightedAllowance <=
        (children.length : Coordinate) * (movementBound * allowance)
  | [], .nil => by
      simp only [List.map_nil,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_nil, List.length_nil, Nat.cast_zero,
        RFAP.ConstructiveFraction.zero_mul_direct]
      exact le_rfl
  | child :: children, .cons head tail => by
      have headBound :
          (child.model.withAllowance allowance
            allowanceNonnegative).weightedAllowance <=
            movementBound * allowance := by
        unfold CCL.ProgressiveGaussianIntegration.CellModel.weightedAllowance
        rw [CCL.ProgressiveGaussianIntegration.CellModel.withAllowance_displacement]
        change child.edge.pointMovement * allowance <=
          movementBound * allowance
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct head
          allowanceNonnegative
      have tailBound := totalConstantAllowance_le_of_movements movementBound
        allowance allowanceNonnegative children tail
      simp only [List.map_cons,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_cons, List.length_cons, Nat.cast_succ]
      calc
        (child.model.withAllowance allowance
              allowanceNonnegative).weightedAllowance +
            (children.map fun remaining =>
              remaining.model.withAllowance allowance
                allowanceNonnegative).foldr
              (fun model total => model.weightedAllowance + total) 0 <=
          movementBound * allowance +
            (children.length : Coordinate) *
              (movementBound * allowance) :=
          add_le_add headBound tailBound
        _ = ((children.length : Coordinate) + 1) *
            (movementBound * allowance) := by ring1

/-- With a uniform local comparison allowance, exact dyadic child-count
cancellation leaves only the coarse parent's squared movement. -/
theorem constantAllowanceCells_aggregateAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : CenteredEdge curve differential}
    (block : DirectParentBlock parent) (allowance : Coordinate)
    (allowanceNonnegative : 0 <= allowance) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (block.constantAllowanceCells allowance
        allowanceNonnegative)).aggregateAllowance <=
      geometricMovement parent.edge.segment parent.edge.left.parameter
        parent.edge.request.endpoint.parameter * allowance := by
  let movementBound := CCL.FiniteGeometric.quarterRadius
    (geometricMovement parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter) block.depth
  have totalBound := totalConstantAllowance_le_of_movements movementBound
    allowance allowanceNonnegative block.children block.movements
  unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
  unfold constantAllowanceCells
  rw [List.length_map, block.childCount]
  have countNonnegative :
      (0 : Coordinate) <= ((2 ^ block.depth : Nat) : Coordinate) :=
    coordinateNatCast_nonnegative _
  have scaled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct totalBound
      countNonnegative
  rw [block.childCount] at scaled
  calc
    ((2 ^ block.depth : Nat) : Coordinate) *
        (block.children.map fun child =>
          child.model.withAllowance allowance
            allowanceNonnegative).foldr
          (fun cell total => cell.weightedAllowance + total) 0 <=
      ((2 ^ block.depth : Nat) : Coordinate) *
        (((2 ^ block.depth : Nat) : Coordinate) *
          (movementBound * allowance)) := scaled
    _ = (((2 ^ block.depth : Nat) : Coordinate) *
          (((2 ^ block.depth : Nat) : Coordinate) * movementBound)) *
        allowance := by ring1
    _ = geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter * allowance := by
      rw [dyadicCountSquare_mul_quarterRadius]

/-- Explicit aggregate semantic allowance of a complete direct dyadic parent
block.  The bound exposes the exact finite child count, common squared
movement, and common owner-independent model error. -/
theorem aggregateAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : CenteredEdge curve differential}
    (block : DirectParentBlock parent) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (block.children.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
      ((2 ^ block.depth : Nat) : Coordinate) *
        (((2 ^ block.depth : Nat) : Coordinate) *
          (CCL.FiniteGeometric.quarterRadius
            (geometricMovement parent.edge.segment parent.edge.left.parameter
              parent.edge.request.endpoint.parameter) block.depth *
            (16 * localModelErrorBound differential parent.edge.segment
              block.rootDiameter block.depth parent.edge.left.parameter
                parent.edge.request.endpoint.parameter))) := by
  unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
  rw [List.length_map, block.childCount]
  let movementBound := CCL.FiniteGeometric.quarterRadius
    (geometricMovement parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter) block.depth
  let errorBound := localModelErrorBound differential parent.edge.segment
    block.rootDiameter block.depth parent.edge.left.parameter
      parent.edge.request.endpoint.parameter
  have totalBound := totalWeightedAllowance_le_of_childBounds
    movementBound errorBound block.children block.movements block.errors
  have lengthNonnegative :
      (0 : Coordinate) <= (block.children.length : Coordinate) := by
    exact coordinateNatCast_nonnegative block.children.length
  have scaled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct totalBound
      lengthNonnegative
  rw [block.childCount] at scaled
  simpa only [movementBound, errorBound] using scaled

/-- The exact dyadic child count cancels the squared-movement decay.  Thus a
complete direct block has a bound depending only on its coarse movement and
the common leaf-model error target, not on the chosen finite depth. -/
theorem aggregateAllowance_le_local {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : CenteredEdge curve differential}
    (block : DirectParentBlock parent) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (block.children.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
      geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter *
        (16 * localModelErrorBound differential parent.edge.segment
          block.rootDiameter block.depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) := by
  calc
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (block.children.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
      ((2 ^ block.depth : Nat) : Coordinate) *
        (((2 ^ block.depth : Nat) : Coordinate) *
          (CCL.FiniteGeometric.quarterRadius
            (geometricMovement parent.edge.segment parent.edge.left.parameter
              parent.edge.request.endpoint.parameter) block.depth *
            (16 * localModelErrorBound differential parent.edge.segment
              block.rootDiameter block.depth parent.edge.left.parameter
                parent.edge.request.endpoint.parameter))) :=
      block.aggregateAllowance_le
    _ = (((2 ^ block.depth : Nat) : Coordinate) *
          (((2 ^ block.depth : Nat) : Coordinate) *
            CCL.FiniteGeometric.quarterRadius
              (geometricMovement parent.edge.segment parent.edge.left.parameter
                parent.edge.request.endpoint.parameter) block.depth)) *
        (16 * localModelErrorBound differential parent.edge.segment
          block.rootDiameter block.depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) := by
      ring1
    _ = geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter *
        (16 * localModelErrorBound differential parent.edge.segment
          block.rootDiameter block.depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) := by
      rw [dyadicCountSquare_mul_quarterRadius]

/-- One direct parent block is already the integration kernel's compatible
constant refinement. -/
def toCompatible {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : CenteredEdge curve differential}
    (block : DirectParentBlock parent) :
    CompatibleConstantPathRefinement [parent.model]
      (block.children.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model) := by
  let refinement :=
    CCL.Riemann.PreparedSubdivisionModels.CenteredEdgeRefinement.cons parent
      block.roots block.displacement_eq
      (CCL.Riemann.PreparedSubdivisionModels.CenteredEdgeRefinement.nil
        (curve := curve) (differential := differential))
  simpa only [List.map_cons, List.map_nil, List.append_nil] using
    refinement.toCompatible

end DirectParentBlock

/-- Whole-path direct refinement retaining every certified parent block.
Unlike the flattened compatibility witness, this representation keeps the
lifted child path and its uniform algebraic certificates available for later
cycle assembly. -/
inductive DirectBlockRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    List (CenteredEdge curve differential) -> Type 2
  | nil : DirectBlockRefinement []
  | cons {parent : CenteredEdge curve differential}
      {remaining : List (CenteredEdge curve differential)}
      (block : DirectParentBlock parent)
      (tail : DirectBlockRefinement remaining) :
      DirectBlockRefinement (parent :: remaining)

namespace DirectBlockRefinement

/-- Flatten the certified child blocks in parent order. -/
def children {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    {parents : List (CenteredEdge curve differential)} ->
      DirectBlockRefinement parents ->
        List (CenteredEdge curve differential)
  | [], .nil => []
  | _ :: _, .cons block tail => block.children ++ tail.children

/-- The retained block tree reconstructs the exact centered-edge refinement. -/
def toCenteredEdgeRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      (blocks : DirectBlockRefinement parents),
      CCL.Riemann.PreparedSubdivisionModels.CenteredEdgeRefinement parents
        blocks.children
  | [], .nil => .nil
  | _ :: _, .cons block tail =>
      .cons _ block.roots block.displacement_eq
        tail.toCenteredEdgeRefinement

/-- Integration compatibility while retaining the stronger certified block
decomposition for geometry-facing consumers. -/
def toCompatible {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parents : List (CenteredEdge curve differential)}
    (blocks : DirectBlockRefinement parents) :
    CompatibleConstantPathRefinement
      (parents.map CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      (blocks.children.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model) :=
  blocks.toCenteredEdgeRefinement.toCompatible

/-- Every child of a direct block refinement is again nonstationary, so the
finite construction can be iterated without an additional geometric input. -/
theorem childrenProper {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      (blocks : DirectBlockRefinement parents),
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper blocks.children
  | [], .nil => trivial
  | _ :: _, .cons block tail =>
      allParentsProper_append block.proper tail.childrenProper

/-- Refine a retained consecutive parent chain block by block. -/
def refinedChain {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2}
      (blocks : DirectBlockRefinement parents),
      DirectPathChain parents (start := start) (finish := finish) ->
        DirectPathChain blocks.children (start := start) (finish := finish)
  | [], _, _, .nil, .nil point => .nil point
  | _ :: _, _, _, .cons block tailBlocks, .cons _ tailChain =>
      block.chain.append (refinedChain tailBlocks tailChain)

end DirectBlockRefinement

/-! ## Common-depth direct refinements -/

/-- Maximum of the finitely many parent clearance depths at one common root
diameter. -/
def commonSufficientDepth {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (rootDiameter : Coordinate) :
    List (CenteredEdge curve differential) -> Nat
  | [] => 0
  | parent :: remaining =>
      max
        (CCL.Riemann.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
          parent.edge.segment parent.edge.left parent.edge.request.endpoint
            rootDiameter)
        (commonSufficientDepth rootDiameter remaining)

/-- The common clearance depth depends only on the prepared geometry. -/
@[simp] theorem commonSufficientDepth_map_recast {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus) (rootDiameter : Coordinate) :
    forall (parents : List (CenteredEdge curve source)),
      commonSufficientDepth rootDiameter
          (parents.map (recastCenteredEdge target)) =
        commonSufficientDepth rootDiameter parents
  | [] => rfl
  | _ :: remaining => by
      simp only [List.map, commonSufficientDepth,
        commonSufficientDepth_map_recast target rootDiameter remaining,
        recastCenteredEdge_segment, recastCenteredEdge_request,
        recastCenteredEdge_left]
      rfl

private theorem headSufficientDepth_le_common {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential)
    (remaining : List (CenteredEdge curve differential))
    (rootDiameter : Coordinate) :
    CCL.Riemann.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
        parent.edge.segment parent.edge.left parent.edge.request.endpoint
          rootDiameter <=
      commonSufficientDepth rootDiameter (parent :: remaining) :=
  Nat.le_max_left _ _

private theorem tailSufficientDepth_le_common {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential)
    (remaining : List (CenteredEdge curve differential))
    (rootDiameter : Coordinate) :
    commonSufficientDepth rootDiameter remaining <=
      commonSufficientDepth rootDiameter (parent :: remaining) :=
  Nat.le_max_right _ _

/-- A whole direct refinement whose every parent block uses the same depth
and root diameter.  These indices retain precisely the synchronization needed
for exact finite child-count cancellation. -/
inductive SynchronizedDirectBlockRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (depth : Nat) (rootDiameter : Coordinate) :
    List (CenteredEdge curve differential) -> Type 2
  | nil : SynchronizedDirectBlockRefinement depth rootDiameter []
  | cons {parent : CenteredEdge curve differential}
      {remaining : List (CenteredEdge curve differential)}
      (block : DirectParentBlock parent)
      (depth_eq : block.depth = depth)
      (rootDiameter_eq : block.rootDiameter = rootDiameter)
      (tail : SynchronizedDirectBlockRefinement depth rootDiameter remaining) :
      SynchronizedDirectBlockRefinement depth rootDiameter
        (parent :: remaining)

namespace SynchronizedDirectBlockRefinement

/-- Forget only the common numerical indices, retaining all certified direct
blocks. -/
def toDirect {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {depth : Nat} {rootDiameter : Coordinate} :
    {parents : List (CenteredEdge curve differential)} ->
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        DirectBlockRefinement parents
  | [], .nil => .nil
  | _ :: _, .cons block _ _ tail => .cons block tail.toDirect

/-- Flatten all synchronized child blocks in parent order. -/
def children {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {depth : Nat} {rootDiameter : Coordinate} :
    {parents : List (CenteredEdge curve differential)} ->
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        List (CenteredEdge curve differential)
  | [], .nil => []
  | _ :: _, .cons block _ _ tail => block.children ++ tail.children

theorem toDirect_children {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      blocks.toDirect.children = blocks.children
  | _, _, [], .nil => rfl
  | _, _, _ :: _, .cons _ _ _ tail => by
      simp only [toDirect, DirectBlockRefinement.children, children,
        toDirect_children tail]

/-- A path with `p` parents has exactly `p * 2^depth` synchronized children. -/
theorem children_length {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      blocks.children.length = parents.length * 2 ^ depth
  | _, _, [], .nil => by
      simp only [children, List.length_nil, Nat.zero_mul]
  | depth, _, _ :: remaining,
      .cons block depth_eq _ tail => by
      simp only [children]
      rw [List.length_append, block.childCount, depth_eq,
        children_length tail]
      simp only [List.length_cons, Nat.succ_mul]
      omega

/-- Synchronized children remain nonstationary. -/
theorem childrenProper {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {depth : Nat} {rootDiameter : Coordinate}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) :
    CCL.Riemann.PreparedDyadicRefinements.AllParentsProper blocks.children := by
  induction blocks with
  | nil => trivial
  | cons block _ _ tail inductionHypothesis =>
      exact allParentsProper_append block.proper inductionHypothesis

/-- Refine a retained consecutive parent chain at the common block depth. -/
def refinedChain {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {depth : Nat} {rootDiameter : Coordinate}
    {parents : List (CenteredEdge curve differential)}
    {start finish : LiftedPoint 2}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents)
    (chain : DirectPathChain parents (start := start) (finish := finish)) :
    DirectPathChain blocks.children (start := start) (finish := finish) := by
  rw [<- blocks.toDirect_children]
  exact blocks.toDirect.refinedChain chain

/-- Integration models flattened blockwise.  Keeping this recursion explicit
avoids any transport through `List.map_append` in the dependent compatible
refinement certificate. -/
def models {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)},
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        List CCL.ProgressiveGaussianIntegration.CellModel
  | _, _, [], .nil => []
  | _, _, _ :: _, .cons block _ _ tail =>
      block.children.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model ++
        tail.models

theorem models_eq_children_map {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      blocks.models =
        blocks.children.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model
  | _, _, [], .nil => rfl
  | _, _, _ :: _, .cons _ _ _ tail => by
      simp only [models, children, List.map_append,
        models_eq_children_map tail]

/-- The synchronized refinement is compatible with the integration kernel. -/
def toCompatible {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {depth : Nat} {rootDiameter : Coordinate} :
    {parents : List (CenteredEdge curve differential)} ->
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) ->
      CompatibleConstantPathRefinement
        (parents.map CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
        blocks.models
  | [], .nil => .nil
  | _ :: _, .cons block _ _ tail =>
      .cons (block.roots.partitionCertificate block.displacement_eq)
        tail.toCompatible

/-- The same compatible refinement with the child index rewritten to the
ordinary flattened centered-edge model list. -/
def toCompatibleChildren {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {depth : Nat} {rootDiameter : Coordinate}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) :
    CompatibleConstantPathRefinement
      (parents.map CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      (blocks.children.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model) :=
  castCompatibleChildren blocks.toCompatible blocks.models_eq_children_map

theorem toCompatibleChildren_comparisonAllowance_eq {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {depth : Nat} {rootDiameter : Coordinate}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) :
    blocks.toCompatibleChildren.comparisonAllowance =
      blocks.toCompatible.comparisonAllowance :=
  castCompatibleChildren_comparisonAllowance_eq _ _

/-- Comparison-only models grouped in exactly the same synchronized parent
blocks. -/
def comparisonCells {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)},
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        List CCL.ProgressiveGaussianIntegration.CellModel
  | _, _, [], .nil => []
  | _, _, parent :: _, .cons block _ _ tail =>
      block.children.map
          (CCL.ProgressiveGaussianIntegration.PathModel.comparisonCell
            parent.model ∘
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model) ++
        tail.comparisonCells

theorem toCompatible_comparisonCells {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      blocks.toCompatible.comparisonCells = blocks.comparisonCells
  | _, _, [], .nil => rfl
  | _, _, _ :: _, .cons _ _ _ tail => by
      simp only [toCompatible,
        CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement.comparisonCells,
        CCL.ProgressiveGaussianIntegration.PathModel.comparisonBlock,
        comparisonCells, List.map_map,
        toCompatible_comparisonCells tail]

/-- Sum of the uniform leafwise comparison targets before multiplying by the
common dyadic child count. -/
def leafComparisonSum {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)},
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        Coordinate
  | _, _, [], .nil => 0
  | depth, rootDiameter, parent :: _, .cons _ _ _ tail =>
      CCL.FiniteGeometric.quarterRadius
          (geometricMovement parent.edge.segment parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) depth *
        (2 * (parent.model.localAllowance +
          16 * localModelErrorBound differential parent.edge.segment
            rootDiameter depth parent.edge.left.parameter
              parent.edge.request.endpoint.parameter)) +
        tail.leafComparisonSum

/-- The same finite comparison sum after cancelling the common squared
dyadic child count against every leaf movement. -/
def baseComparisonSum {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)},
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        Coordinate
  | _, _, [], .nil => 0
  | depth, rootDiameter, parent :: _, .cons _ _ _ tail =>
      geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter *
        (2 * (parent.model.localAllowance +
          16 * localModelErrorBound differential parent.edge.segment
            rootDiameter depth parent.edge.left.parameter
              parent.edge.request.endpoint.parameter)) +
        tail.baseComparisonSum

/-- New child-model contribution to a synchronized comparison, separated
from the already-displayed parent allowances. -/
def refinementErrorSum {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)},
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        Coordinate
  | _, _, [], .nil => 0
  | depth, rootDiameter, parent :: _, .cons _ _ _ tail =>
      geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter *
        (32 * localModelErrorBound differential parent.edge.segment
          rootDiameter depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) +
        tail.refinementErrorSum

/-- The coarse comparison sum is exactly the old parent weighted allowance
plus the newly requested child-model contribution. -/
theorem baseComparisonSum_eq {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      blocks.baseComparisonSum =
        2 * (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (parents.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance +
          blocks.refinementErrorSum
  | _, _, [], .nil => by
      simp only [baseComparisonSum, refinementErrorSum, List.map_nil,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_nil, RFAP.ConstructiveFraction.mul_zero_direct]
      ring1
  | _, _, parent :: _, .cons _ _ _ tail => by
      simp only [baseComparisonSum, refinementErrorSum, List.map_cons,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_cons]
      rw [baseComparisonSum_eq tail,
        centeredEdge_weightedAllowance_eq_geometric]
      unfold CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance
      ring1

/-- Common dyadic synchronization cancels exactly in the complete finite
comparison sum, parent by parent. -/
theorem scaledLeafComparisonSum_eq {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      ((2 ^ depth : Nat) : Coordinate) *
          (((2 ^ depth : Nat) : Coordinate) * blocks.leafComparisonSum) =
        blocks.baseComparisonSum
  | _, _, [], .nil => by
      simp only [leafComparisonSum, baseComparisonSum,
        RFAP.ConstructiveFraction.mul_zero_direct]
  | depth, rootDiameter, parent :: _, .cons _ _ _ tail => by
      simp only [leafComparisonSum, baseComparisonSum]
      calc
        ((2 ^ depth : Nat) : Coordinate) *
            (((2 ^ depth : Nat) : Coordinate) *
              (CCL.FiniteGeometric.quarterRadius
                    (geometricMovement parent.edge.segment
                      parent.edge.left.parameter
                      parent.edge.request.endpoint.parameter) depth *
                  (2 * (parent.model.localAllowance +
                    16 * localModelErrorBound differential parent.edge.segment
                      rootDiameter depth parent.edge.left.parameter
                        parent.edge.request.endpoint.parameter)) +
                tail.leafComparisonSum)) =
          (((2 ^ depth : Nat) : Coordinate) *
              (((2 ^ depth : Nat) : Coordinate) *
                CCL.FiniteGeometric.quarterRadius
                  (geometricMovement parent.edge.segment
                    parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter) depth)) *
              (2 * (parent.model.localAllowance +
                16 * localModelErrorBound differential parent.edge.segment
                  rootDiameter depth parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter)) +
            ((2 ^ depth : Nat) : Coordinate) *
              (((2 ^ depth : Nat) : Coordinate) *
                tail.leafComparisonSum) := by
          ring1
        _ = geometricMovement parent.edge.segment parent.edge.left.parameter
              parent.edge.request.endpoint.parameter *
              (2 * (parent.model.localAllowance +
                16 * localModelErrorBound differential parent.edge.segment
                  rootDiameter depth parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter)) +
            tail.baseComparisonSum := by
          rw [DirectParentBlock.dyadicCountSquare_mul_quarterRadius,
            scaledLeafComparisonSum_eq tail]

/-- The comparison-only cell count is the synchronized child count. -/
theorem comparisonCells_length {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      blocks.comparisonCells.length = parents.length * 2 ^ depth
  | _, _, [], .nil => by
      simp only [comparisonCells, List.length_nil, Nat.zero_mul]
  | depth, _, _ :: _, .cons block depth_eq _ tail => by
      simp only [comparisonCells, List.length_append, List.length_map,
        block.childCount, depth_eq, comparisonCells_length tail,
        List.length_cons, Nat.succ_mul]
      omega

/-- Total weighted comparison allowance before the final finite path-count
factor. -/
theorem totalComparisonWeightedAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        blocks.comparisonCells).totalWeightedAllowance <=
        ((2 ^ depth : Nat) : Coordinate) * blocks.leafComparisonSum
  | _, _, [], .nil => by
      simp only [comparisonCells, leafComparisonSum,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_nil, RFAP.ConstructiveFraction.mul_zero_direct]
      exact le_rfl
  | depth, rootDiameter, parent :: _,
      .cons block depth_eq rootDiameter_eq tail => by
      have headBound := totalComparisonAllowance_le_of_childBounds parent
        (CCL.FiniteGeometric.quarterRadius
          (geometricMovement parent.edge.segment parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) block.depth)
        (localModelErrorBound differential parent.edge.segment
          block.rootDiameter block.depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter)
        block.children block.movements block.errors
      rw [block.childCount, depth_eq, rootDiameter_eq] at headBound
      have normalizedHead :
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (block.children.map
              (CCL.ProgressiveGaussianIntegration.PathModel.comparisonCell
                parent.model ∘
                CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model))).totalWeightedAllowance <=
            ((2 ^ depth : Nat) : Coordinate) *
              (CCL.FiniteGeometric.quarterRadius
                (geometricMovement parent.edge.segment
                  parent.edge.left.parameter
                  parent.edge.request.endpoint.parameter) depth *
                (2 * (parent.model.localAllowance +
                  16 * localModelErrorBound differential parent.edge.segment
                    rootDiameter depth parent.edge.left.parameter
                      parent.edge.request.endpoint.parameter))) := by
        simpa only [Function.comp_def] using headBound
      have tailBound := totalComparisonWeightedAllowance_le tail
      simp only [comparisonCells, leafComparisonSum]
      rw [totalWeightedAllowance_append]
      calc
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
              (block.children.map
                (CCL.ProgressiveGaussianIntegration.PathModel.comparisonCell
                  parent.model ∘
                  CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model))).totalWeightedAllowance +
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              tail.comparisonCells).totalWeightedAllowance <=
          ((2 ^ depth : Nat) : Coordinate) *
                (CCL.FiniteGeometric.quarterRadius
                  (geometricMovement parent.edge.segment
                    parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter) depth *
                  (2 * (parent.model.localAllowance +
                    16 * localModelErrorBound differential parent.edge.segment
                      rootDiameter depth parent.edge.left.parameter
                        parent.edge.request.endpoint.parameter))) +
            ((2 ^ depth : Nat) : Coordinate) * tail.leafComparisonSum :=
          add_le_add normalizedHead tailBound
        _ = ((2 ^ depth : Nat) : Coordinate) *
            (CCL.FiniteGeometric.quarterRadius
                (geometricMovement parent.edge.segment
                  parent.edge.left.parameter
                  parent.edge.request.endpoint.parameter) depth *
                (2 * (parent.model.localAllowance +
                  16 * localModelErrorBound differential parent.edge.segment
                    rootDiameter depth parent.edge.left.parameter
                      parent.edge.request.endpoint.parameter)) +
              tail.leafComparisonSum) := by
          ring1

private theorem coordinateNatCast_nonnegative (value : Nat) :
    (0 : Coordinate) <= (value : Coordinate) := by
  induction value with
  | zero => exact le_rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ]
      exact add_nonneg inductionHypothesis (by decide)

/-- The complete compatible comparison allowance has a coarse-scale finite
bound in which the common dyadic child count has disappeared exactly. -/
theorem comparisonAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {depth : Nat} {rootDiameter : Coordinate}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) :
    blocks.toCompatible.comparisonAllowance <=
      (parents.length : Coordinate) * blocks.baseComparisonSum := by
  unfold CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement.comparisonAllowance
    CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
  rw [blocks.toCompatible_comparisonCells, blocks.comparisonCells_length]
  have totalBound := blocks.totalComparisonWeightedAllowance_le
  have countNonnegative :
      (0 : Coordinate) <=
        ((parents.length * 2 ^ depth : Nat) : Coordinate) :=
    coordinateNatCast_nonnegative _
  have scaled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct totalBound
      countNonnegative
  calc
    ((parents.length * 2 ^ depth : Nat) : Coordinate) *
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            blocks.comparisonCells).totalWeightedAllowance <=
        ((parents.length * 2 ^ depth : Nat) : Coordinate) *
          (((2 ^ depth : Nat) : Coordinate) *
            blocks.leafComparisonSum) := scaled
    _ = (parents.length : Coordinate) *
        (((2 ^ depth : Nat) : Coordinate) *
          (((2 ^ depth : Nat) : Coordinate) * blocks.leafComparisonSum)) := by
      rw [Nat.cast_mul]
      ring1
    _ = (parents.length : Coordinate) * blocks.baseComparisonSum := by
      rw [blocks.scaledLeafComparisonSum_eq]

/-- Comparison decomposes into twice the old model allowance and one
explicitly shrinkable child-error contribution. -/
theorem comparisonAllowance_le_parent_add_error {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {depth : Nat} {rootDiameter : Coordinate}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) :
    blocks.toCompatible.comparisonAllowance <=
      2 * (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (parents.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance +
        (parents.length : Coordinate) * blocks.refinementErrorSum := by
  calc
    blocks.toCompatible.comparisonAllowance <=
        (parents.length : Coordinate) * blocks.baseComparisonSum :=
      blocks.comparisonAllowance_le
    _ = (parents.length : Coordinate) *
        (2 * (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (parents.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance +
          blocks.refinementErrorSum) := by
      rw [blocks.baseComparisonSum_eq]
    _ = 2 * (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (parents.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance +
        (parents.length : Coordinate) * blocks.refinementErrorSum := by
      unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
      rw [List.length_map]
      ring1

/-- Uniform leafwise child allowance before common-count cancellation. -/
def leafChildAllowanceSum {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)},
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        Coordinate
  | _, _, [], .nil => 0
  | depth, rootDiameter, parent :: _, .cons _ _ _ tail =>
      CCL.FiniteGeometric.quarterRadius
          (geometricMovement parent.edge.segment parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) depth *
        (16 * localModelErrorBound differential parent.edge.segment
          rootDiameter depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) +
        tail.leafChildAllowanceSum

/-- Coarse-scale child allowance after exact common-count cancellation. -/
def baseChildAllowanceSum {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)},
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        Coordinate
  | _, _, [], .nil => 0
  | depth, rootDiameter, parent :: _, .cons _ _ _ tail =>
      geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter *
        (16 * localModelErrorBound differential parent.edge.segment
          rootDiameter depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) +
        tail.baseChildAllowanceSum

theorem scaledLeafChildAllowanceSum_eq {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      ((2 ^ depth : Nat) : Coordinate) *
          (((2 ^ depth : Nat) : Coordinate) * blocks.leafChildAllowanceSum) =
        blocks.baseChildAllowanceSum
  | _, _, [], .nil => by
      simp only [leafChildAllowanceSum, baseChildAllowanceSum,
        RFAP.ConstructiveFraction.mul_zero_direct]
  | depth, rootDiameter, parent :: _, .cons _ _ _ tail => by
      simp only [leafChildAllowanceSum, baseChildAllowanceSum]
      calc
        ((2 ^ depth : Nat) : Coordinate) *
            (((2 ^ depth : Nat) : Coordinate) *
              (CCL.FiniteGeometric.quarterRadius
                    (geometricMovement parent.edge.segment
                      parent.edge.left.parameter
                        parent.edge.request.endpoint.parameter) depth *
                  (16 * localModelErrorBound differential parent.edge.segment
                    rootDiameter depth parent.edge.left.parameter
                      parent.edge.request.endpoint.parameter) +
                tail.leafChildAllowanceSum)) =
          (((2 ^ depth : Nat) : Coordinate) *
              (((2 ^ depth : Nat) : Coordinate) *
                CCL.FiniteGeometric.quarterRadius
                  (geometricMovement parent.edge.segment
                    parent.edge.left.parameter
                      parent.edge.request.endpoint.parameter) depth)) *
              (16 * localModelErrorBound differential parent.edge.segment
                rootDiameter depth parent.edge.left.parameter
                  parent.edge.request.endpoint.parameter) +
            ((2 ^ depth : Nat) : Coordinate) *
              (((2 ^ depth : Nat) : Coordinate) *
                tail.leafChildAllowanceSum) := by
          ring1
        _ = geometricMovement parent.edge.segment parent.edge.left.parameter
              parent.edge.request.endpoint.parameter *
              (16 * localModelErrorBound differential parent.edge.segment
                rootDiameter depth parent.edge.left.parameter
                  parent.edge.request.endpoint.parameter) +
            tail.baseChildAllowanceSum := by
          rw [DirectParentBlock.dyadicCountSquare_mul_quarterRadius,
            scaledLeafChildAllowanceSum_eq tail]

theorem models_length {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {depth : Nat} {rootDiameter : Coordinate}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) :
    blocks.models.length = parents.length * 2 ^ depth := by
  rw [blocks.models_eq_children_map, List.length_map,
    blocks.children_length]

theorem totalModelWeightedAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        blocks.models).totalWeightedAllowance <=
        ((2 ^ depth : Nat) : Coordinate) * blocks.leafChildAllowanceSum
  | _, _, [], .nil => by
      simp only [models, leafChildAllowanceSum,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_nil, RFAP.ConstructiveFraction.mul_zero_direct]
      exact le_rfl
  | depth, rootDiameter, parent :: _,
      .cons block depth_eq rootDiameter_eq tail => by
      have headBound := totalWeightedAllowance_le_of_childBounds
        (CCL.FiniteGeometric.quarterRadius
          (geometricMovement parent.edge.segment parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) block.depth)
        (localModelErrorBound differential parent.edge.segment
          block.rootDiameter block.depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter)
        block.children block.movements block.errors
      rw [block.childCount, depth_eq, rootDiameter_eq] at headBound
      have tailBound := totalModelWeightedAllowance_le tail
      simp only [models, leafChildAllowanceSum]
      rw [totalWeightedAllowance_append]
      calc
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
              (block.children.map
                CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance +
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              tail.models).totalWeightedAllowance <=
          ((2 ^ depth : Nat) : Coordinate) *
                (CCL.FiniteGeometric.quarterRadius
                  (geometricMovement parent.edge.segment
                    parent.edge.left.parameter
                      parent.edge.request.endpoint.parameter) depth *
                  (16 * localModelErrorBound differential parent.edge.segment
                    rootDiameter depth parent.edge.left.parameter
                      parent.edge.request.endpoint.parameter)) +
            ((2 ^ depth : Nat) : Coordinate) *
              tail.leafChildAllowanceSum :=
          add_le_add headBound tailBound
        _ = ((2 ^ depth : Nat) : Coordinate) *
            (CCL.FiniteGeometric.quarterRadius
                (geometricMovement parent.edge.segment
                  parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter) depth *
                (16 * localModelErrorBound differential parent.edge.segment
                  rootDiameter depth parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter) +
              tail.leafChildAllowanceSum) := by
          ring1

/-- Aggregate semantic allowance of the synchronized child path. -/
theorem modelAllowance_le_baseChildAllowance {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {depth : Nat} {rootDiameter : Coordinate}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      blocks.models).aggregateAllowance <=
      (parents.length : Coordinate) * blocks.baseChildAllowanceSum := by
  unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
  rw [blocks.models_length]
  have totalBound := blocks.totalModelWeightedAllowance_le
  have countNonnegative :
      (0 : Coordinate) <=
        ((parents.length * 2 ^ depth : Nat) : Coordinate) :=
    coordinateNatCast_nonnegative _
  have scaled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct totalBound
      countNonnegative
  calc
    ((parents.length * 2 ^ depth : Nat) : Coordinate) *
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            blocks.models).totalWeightedAllowance <=
        ((parents.length * 2 ^ depth : Nat) : Coordinate) *
          (((2 ^ depth : Nat) : Coordinate) *
            blocks.leafChildAllowanceSum) := scaled
    _ = (parents.length : Coordinate) *
        (((2 ^ depth : Nat) : Coordinate) *
          (((2 ^ depth : Nat) : Coordinate) *
            blocks.leafChildAllowanceSum)) := by
      rw [Nat.cast_mul]
      ring1
    _ = (parents.length : Coordinate) * blocks.baseChildAllowanceSum := by
      rw [blocks.scaledLeafChildAllowanceSum_eq]

theorem baseChildAllowanceSum_le_refinementErrorSum {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      0 <= rootDiameter ->
      blocks.baseChildAllowanceSum <= blocks.refinementErrorSum
  | _, _, [], .nil, _rootDiameterNonnegative => le_rfl
  | depth, rootDiameter, parent :: _, .cons _ _ _ tail,
      rootDiameterNonnegative => by
      have errorNonnegative := localModelErrorBound_nonnegative differential
        parent.edge.segment rootDiameterNonnegative depth
          parent.edge.left.parameter parent.edge.request.endpoint.parameter
      have sixteenErrorNonnegative :
          0 <= 16 * localModelErrorBound differential parent.edge.segment
            rootDiameter depth parent.edge.left.parameter
              parent.edge.request.endpoint.parameter :=
        RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          errorNonnegative
      have errorLe :
          16 * localModelErrorBound differential parent.edge.segment
              rootDiameter depth parent.edge.left.parameter
                parent.edge.request.endpoint.parameter <=
            32 * localModelErrorBound differential parent.edge.segment
              rootDiameter depth parent.edge.left.parameter
                parent.edge.request.endpoint.parameter := by
        calc
          16 * localModelErrorBound differential parent.edge.segment
                rootDiameter depth parent.edge.left.parameter
                  parent.edge.request.endpoint.parameter <=
              16 * localModelErrorBound differential parent.edge.segment
                  rootDiameter depth parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter +
                16 * localModelErrorBound differential parent.edge.segment
                  rootDiameter depth parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter :=
            le_add_of_nonneg_right sixteenErrorNonnegative
          _ = 32 * localModelErrorBound differential parent.edge.segment
              rootDiameter depth parent.edge.left.parameter
                parent.edge.request.endpoint.parameter := by
            ring1
      have movementNonnegative :
          0 <= geometricMovement parent.edge.segment
            parent.edge.left.parameter
              parent.edge.request.endpoint.parameter := by
        unfold geometricMovement
        exact RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
      have headBound :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct errorLe
          movementNonnegative
      have tailBound := baseChildAllowanceSum_le_refinementErrorSum tail
        rootDiameterNonnegative
      simp only [baseChildAllowanceSum, refinementErrorSum]
      exact add_le_add headBound tailBound

/-- The synchronized child path's own semantic allowance is paid entirely by
the new-error term. -/
theorem modelAllowance_le_refinementError {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {depth : Nat} {rootDiameter : Coordinate}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents)
    (rootDiameterNonnegative : 0 <= rootDiameter) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      blocks.models).aggregateAllowance <=
      (parents.length : Coordinate) * blocks.refinementErrorSum :=
  blocks.modelAllowance_le_baseChildAllowance.trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (blocks.baseChildAllowanceSum_le_refinementErrorSum
        rootDiameterNonnegative)
      (coordinateNatCast_nonnegative parents.length))


end SynchronizedDirectBlockRefinement

/-! ## Accuracy-selected synchronized refinements -/

/-- Finite coefficient multiplying a common point/root accuracy in the new
child-model part of a whole-path comparison. -/
def refinementCoefficientSum {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus) :
    List (CenteredEdge curve differential) -> Coordinate
  | [] => 0
  | parent :: remaining =>
      geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter *
        (64 *
          (CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
              differential parent.edge.segment +
            CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
              differential parent.edge.segment)) +
        refinementCoefficientSum differential remaining

theorem refinementCoefficientSum_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus) :
    forall (parents : List (CenteredEdge curve differential)),
      0 <= refinementCoefficientSum differential parents
  | [] => le_rfl
  | parent :: remaining => by
      unfold refinementCoefficientSum
      have movementNonnegative :
          0 <= geometricMovement parent.edge.segment
            parent.edge.left.parameter
              parent.edge.request.endpoint.parameter := by
        unfold geometricMovement
        exact RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
      have pointCoefficientNonnegative :=
        CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient_nonnegative
          differential parent.edge.segment
      have rootCoefficientNonnegative :=
        CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient_nonnegative
          differential parent.edge.segment
      have coefficientNonnegative := add_nonneg pointCoefficientNonnegative
        rootCoefficientNonnegative
      have sixtyFourNonnegative : (0 : Coordinate) <= 64 := by
        calc
          (0 : Coordinate) <= 8 * 8 :=
            RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide)
          _ = 64 := by ring1
      have scaledCoefficientNonnegative :=
        RFAP.ConstructiveFraction.mul_nonneg_direct
          sixtyFourNonnegative coefficientNonnegative
      have headNonnegative :=
        RFAP.ConstructiveFraction.mul_nonneg_direct movementNonnegative
          scaledCoefficientNonnegative
      exact add_nonneg headNonnegative
        (refinementCoefficientSum_nonnegative differential remaining)

private theorem coordinateNatCast_nonnegative (value : Nat) :
    (0 : Coordinate) <= (value : Coordinate) := by
  induction value with
  | zero => exact le_rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ]
      exact add_nonneg inductionHypothesis (by decide)

/-- Path-count-scaled coefficient appearing in the aggregate comparison
allowance. -/
def aggregateRefinementCoefficient {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    (parents : List (CenteredEdge curve differential)) : Coordinate :=
  (parents.length : Coordinate) *
    refinementCoefficientSum differential parents

theorem aggregateRefinementCoefficient_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    (parents : List (CenteredEdge curve differential)) :
    0 <= aggregateRefinementCoefficient differential parents := by
  unfold aggregateRefinementCoefficient
  exact RFAP.ConstructiveFraction.mul_nonneg_direct
    (coordinateNatCast_nonnegative parents.length)
    (refinementCoefficientSum_nonnegative differential parents)

/-- Positive common point/root accuracy selected from a requested aggregate
new-error target. -/
def refinementAccuracy {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    (parents : List (CenteredEdge curve differential))
    (target : Coordinate) : Coordinate :=
  target / (aggregateRefinementCoefficient differential parents + 1)

theorem refinementAccuracy_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    (parents : List (CenteredEdge curve differential))
    {target : Coordinate} (targetPositive : 0 < target) :
    0 < refinementAccuracy differential parents target := by
  unfold refinementAccuracy
  exact RFAP.ConstructiveFraction.div_pos_direct targetPositive
    (add_pos_of_nonneg_of_pos
      (aggregateRefinementCoefficient_nonnegative differential parents)
      (by decide))

theorem refinementAccuracy_mul_coefficient_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    (parents : List (CenteredEdge curve differential))
    {target : Coordinate} (targetPositive : 0 < target) :
    refinementAccuracy differential parents target *
        aggregateRefinementCoefficient differential parents <=
      target := by
  let coefficient := aggregateRefinementCoefficient differential parents
  have coefficientNonnegative : 0 <= coefficient :=
    aggregateRefinementCoefficient_nonnegative differential parents
  have denominatorPositive : 0 < coefficient + 1 :=
    add_pos_of_nonneg_of_pos coefficientNonnegative (by decide)
  have coefficientLe : coefficient <= coefficient + 1 :=
    le_add_of_nonneg_right (by decide)
  have accuracyNonnegative :
      0 <= refinementAccuracy differential parents target :=
    (refinementAccuracy_positive differential parents targetPositive).le
  calc
    refinementAccuracy differential parents target * coefficient <=
        refinementAccuracy differential parents target * (coefficient + 1) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct coefficientLe
        accuracyNonnegative
    _ = target := by
      unfold refinementAccuracy
      change (target / (coefficient + 1)) * (coefficient + 1) = target
      exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne target
        (coefficient + 1) (ne_of_gt denominatorPositive)

/-- Maximum of the finitely many depths needed to push every squared parent
movement below one common positive accuracy. -/
def commonAccuracyDepth {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (accuracy : Coordinate) :
    List (CenteredEdge curve differential) -> Nat
  | [] => 0
  | parent :: remaining =>
      max
        (CCL.FiniteGeometric.firstQuarterBelow
          (geometricMovement parent.edge.segment parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) 0 accuracy)
        (commonAccuracyDepth accuracy remaining)

/-- The finite accuracy depth is likewise invariant under recentering for a
different differential. -/
@[simp] theorem commonAccuracyDepth_map_recast {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus) (accuracy : Coordinate) :
    forall (parents : List (CenteredEdge curve source)),
      commonAccuracyDepth accuracy
          (parents.map (recastCenteredEdge target)) =
        commonAccuracyDepth accuracy parents
  | [] => rfl
  | _ :: remaining => by
      simp only [List.map, commonAccuracyDepth,
        commonAccuracyDepth_map_recast target accuracy remaining,
        recastCenteredEdge_segment, recastCenteredEdge_request,
        recastCenteredEdge_left]
      rfl

/-- Sum of the aggregate error coefficients for a displayed finite family of
differentials, all evaluated on the same recentered geometry. -/
def finiteDifferentialRefinementCoefficient {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (parents : List (CenteredEdge curve source)) :
    List (Differential genus) -> Coordinate
  | [] => 0
  | target :: remaining =>
      aggregateRefinementCoefficient target
          (parents.map (recastCenteredEdge target)) +
        finiteDifferentialRefinementCoefficient parents remaining

theorem finiteDifferentialRefinementCoefficient_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (parents : List (CenteredEdge curve source)) :
    forall (targets : List (Differential genus)),
      0 <= finiteDifferentialRefinementCoefficient parents targets
  | [] => le_rfl
  | target :: remaining =>
      add_nonneg
        (aggregateRefinementCoefficient_nonnegative target
          (parents.map (recastCenteredEdge target)))
        (finiteDifferentialRefinementCoefficient_nonnegative parents remaining)

/-- Every displayed member coefficient is bounded by the finite family sum. -/
theorem aggregateRefinementCoefficient_le_finiteDifferential {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (parents : List (CenteredEdge curve source))
    (target : Differential genus) :
    forall (targets : List (Differential genus)), target ∈ targets ->
      aggregateRefinementCoefficient target
          (parents.map (recastCenteredEdge target)) <=
        finiteDifferentialRefinementCoefficient parents targets
  | [], member => by simp only [List.not_mem_nil] at member
  | head :: remaining, member => by
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst head
        exact le_add_of_nonneg_right
          (finiteDifferentialRefinementCoefficient_nonnegative parents remaining)
      · exact
          (aggregateRefinementCoefficient_le_finiteDifferential parents target
              remaining member).trans
            (le_add_of_nonneg_left
              (aggregateRefinementCoefficient_nonnegative head
                (parents.map (recastCenteredEdge head))))

/-- One positive point/root accuracy simultaneously small enough for every
member of a finite differential family. -/
def finiteDifferentialRefinementAccuracy {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (parents : List (CenteredEdge curve source))
    (targets : List (Differential genus)) (target : Coordinate) : Coordinate :=
  target / (finiteDifferentialRefinementCoefficient parents targets + 1)

theorem finiteDifferentialRefinementAccuracy_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (parents : List (CenteredEdge curve source))
    (targets : List (Differential genus))
    {target : Coordinate} (targetPositive : 0 < target) :
    0 < finiteDifferentialRefinementAccuracy parents targets target := by
  unfold finiteDifferentialRefinementAccuracy
  exact RFAP.ConstructiveFraction.div_pos_direct targetPositive
    (add_pos_of_nonneg_of_pos
      (finiteDifferentialRefinementCoefficient_nonnegative parents targets)
      (by decide))

/-- The common accuracy pays the aggregate new-error coefficient of every
member differential. -/
theorem finiteDifferentialRefinementAccuracy_mul_coefficient_le
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (parents : List (CenteredEdge curve source))
    (targets : List (Differential genus))
    (differential : Differential genus) (member : differential ∈ targets)
    {target : Coordinate} (targetPositive : 0 < target) :
    finiteDifferentialRefinementAccuracy parents targets target *
        aggregateRefinementCoefficient differential
          (parents.map (recastCenteredEdge differential)) <= target := by
  let coefficient := finiteDifferentialRefinementCoefficient parents targets
  have coefficientNonnegative : 0 <= coefficient :=
    finiteDifferentialRefinementCoefficient_nonnegative parents targets
  have denominatorPositive : 0 < coefficient + 1 :=
    add_pos_of_nonneg_of_pos coefficientNonnegative (by decide)
  have memberCoefficientLe :
      aggregateRefinementCoefficient differential
          (parents.map (recastCenteredEdge differential)) <= coefficient :=
    aggregateRefinementCoefficient_le_finiteDifferential parents differential
      targets member
  have coefficientLe : coefficient <= coefficient + 1 :=
    le_add_of_nonneg_right (by decide)
  have accuracyNonnegative :
      0 <= finiteDifferentialRefinementAccuracy parents targets target :=
    (finiteDifferentialRefinementAccuracy_positive parents targets
      targetPositive).le
  calc
    finiteDifferentialRefinementAccuracy parents targets target *
          aggregateRefinementCoefficient differential
            (parents.map (recastCenteredEdge differential)) <=
        finiteDifferentialRefinementAccuracy parents targets target *
          coefficient :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        memberCoefficientLe accuracyNonnegative
    _ <= finiteDifferentialRefinementAccuracy parents targets target *
          (coefficient + 1) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct coefficientLe
        accuracyNonnegative
    _ = target := by
      unfold finiteDifferentialRefinementAccuracy
      change (target / (coefficient + 1)) * (coefficient + 1) = target
      exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne target
        (coefficient + 1) (ne_of_gt denominatorPositive)

private theorem headAccuracyDepth_le_common {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (accuracy : Coordinate) (parent : CenteredEdge curve differential)
    (remaining : List (CenteredEdge curve differential)) :
    CCL.FiniteGeometric.firstQuarterBelow
        (geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter) 0 accuracy <=
      commonAccuracyDepth accuracy (parent :: remaining) :=
  Nat.le_max_left _ _

private theorem tailAccuracyDepth_le_common {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (accuracy : Coordinate) (parent : CenteredEdge curve differential)
    (remaining : List (CenteredEdge curve differential)) :
    commonAccuracyDepth accuracy remaining <=
      commonAccuracyDepth accuracy (parent :: remaining) :=
  Nat.le_max_right _ _

private theorem quarterRadius_le_accuracy_of_commonDepth {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (accuracy : Coordinate) (accuracyPositive : 0 < accuracy)
    (parent : CenteredEdge curve differential)
    (remaining : List (CenteredEdge curve differential))
    (depth : Nat)
    (enough : commonAccuracyDepth accuracy (parent :: remaining) <= depth) :
    CCL.FiniteGeometric.quarterRadius
        (geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter) depth <= accuracy := by
  let first := CCL.FiniteGeometric.firstQuarterBelow
    (geometricMovement parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter) 0 accuracy
  have firstEnough : first <= depth :=
    (headAccuracyDepth_le_common accuracy parent remaining).trans enough
  have movementNonnegative :
      0 <= geometricMovement parent.edge.segment parent.edge.left.parameter
        parent.edge.request.endpoint.parameter := by
    unfold geometricMovement
    exact RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
  have laterLe := CCL.FiniteGeometric.quarterRadius_antitone
    movementNonnegative firstEnough
  have firstBelow := CCL.FiniteGeometric.firstQuarterBelow_accurate
    (geometricMovement parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter)
    movementNonnegative 0 accuracy accuracyPositive
  exact (laterLe.trans_lt firstBelow).le

/-- Construct synchronized direct blocks at any common depth beyond the
finite maximum clearance depth. -/
def synchronizedDirectBlockRefinementAtDepth {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (depth : Nat) :
    (parents : List (CenteredEdge curve differential)) ->
    CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents ->
    commonSufficientDepth rootDiameter parents <= depth ->
      SynchronizedDirectBlockRefinement depth rootDiameter parents
  | [], _proper, _enough => .nil
  | parent :: remaining, proper, enough => by
      have headEnough :=
        (headSufficientDepth_le_common parent remaining rootDiameter).trans
          enough
      have tailEnough :=
        (tailSufficientDepth_le_common parent remaining rootDiameter).trans
          enough
      let block := directParentBlockAtDepth parent proper.1 rootDiameter
        rootDiameterPositive depth headEnough
      exact .cons block rfl rfl
        (synchronizedDirectBlockRefinementAtDepth rootDiameter
          rootDiameterPositive depth remaining proper.2 tailEnough)

/-- At fixed numerical depth and diameter, synchronized child geometry
commutes with recasting the whole parent list. -/
theorem synchronizedDirectBlockRefinementAtDepth_children_recast
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (depth : Nat) :
    forall (parents : List (CenteredEdge curve source))
      (proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents)
      (sourceEnough : commonSufficientDepth rootDiameter parents <= depth)
      (targetEnough : commonSufficientDepth rootDiameter
        (parents.map (recastCenteredEdge target)) <= depth),
      (synchronizedDirectBlockRefinementAtDepth rootDiameter
          rootDiameterPositive depth
          (parents.map (recastCenteredEdge target))
          (allParentsProper_map_recast proper) targetEnough).children =
        (synchronizedDirectBlockRefinementAtDepth rootDiameter
          rootDiameterPositive depth parents proper sourceEnough).children.map
            (recastCenteredEdge target)
  | [], _proper, _sourceEnough, _targetEnough => rfl
  | parent :: remaining, proper, sourceEnough, targetEnough => by
      simp only [synchronizedDirectBlockRefinementAtDepth,
        SynchronizedDirectBlockRefinement.children, List.map,
        List.map_append]
      rw [directParentBlockAtDepth_children_recast target]
      rw [synchronizedDirectBlockRefinementAtDepth_children_recast target
        rootDiameter rootDiameterPositive depth remaining]

/-- Recompute the canonical synchronized blocks on the recentered parent
list, using the same numerical geometry as the source blocks. -/
def recastSynchronizedDirectBlockRefinementAtDepth {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (depth : Nat) (parents : List (CenteredEdge curve source))
    (proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents)
    (enough : commonSufficientDepth rootDiameter parents <= depth) :
    SynchronizedDirectBlockRefinement depth rootDiameter
      (parents.map (recastCenteredEdge target)) :=
  synchronizedDirectBlockRefinementAtDepth rootDiameter rootDiameterPositive
    depth (parents.map (recastCenteredEdge target))
      (allParentsProper_map_recast proper) (by
        simpa only [commonSufficientDepth_map_recast] using enough)

@[simp] theorem recastSynchronizedDirectBlockRefinementAtDepth_children
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (depth : Nat) (parents : List (CenteredEdge curve source))
    (proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents)
    (enough : commonSufficientDepth rootDiameter parents <= depth) :
    (recastSynchronizedDirectBlockRefinementAtDepth target rootDiameter
      rootDiameterPositive depth parents proper enough).children =
        (synchronizedDirectBlockRefinementAtDepth rootDiameter
          rootDiameterPositive depth parents proper enough).children.map
            (recastCenteredEdge target) := by
  apply synchronizedDirectBlockRefinementAtDepth_children_recast

/-- Differential-specific compatible models on exactly the recentered source
child geometry. -/
def recastCompatibleAtDepth {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (depth : Nat) (parents : List (CenteredEdge curve source))
    (proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents)
    (enough : commonSufficientDepth rootDiameter parents <= depth) :
    CompatibleConstantPathRefinement
      ((parents.map (recastCenteredEdge target)).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      (((synchronizedDirectBlockRefinementAtDepth rootDiameter
        rootDiameterPositive depth parents proper enough).children.map
          (recastCenteredEdge target)).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model) := by
  let targetBlocks := recastSynchronizedDirectBlockRefinementAtDepth target
    rootDiameter rootDiameterPositive depth parents proper enough
  apply castCompatibleChildren targetBlocks.toCompatibleChildren
  exact congrArg
    (List.map CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
    (recastSynchronizedDirectBlockRefinementAtDepth_children target
      rootDiameter rootDiameterPositive depth parents proper enough)

theorem recastCompatibleAtDepth_comparisonAllowance_eq {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (depth : Nat) (parents : List (CenteredEdge curve source))
    (proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents)
    (enough : commonSufficientDepth rootDiameter parents <= depth) :
    (recastCompatibleAtDepth target rootDiameter rootDiameterPositive depth
        parents proper enough).comparisonAllowance =
      CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement.comparisonAllowance
        (SynchronizedDirectBlockRefinement.toCompatibleChildren
          (recastSynchronizedDirectBlockRefinementAtDepth target rootDiameter
            rootDiameterPositive depth parents proper enough)) := by
  unfold recastCompatibleAtDepth
  rw [castCompatibleChildren_comparisonAllowance_eq]

/-- Canonical synchronized direct refinement at the least computed common
clearance depth. -/
def synchronizedDirectBlockRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (parents : List (CenteredEdge curve differential))
    (proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents) :
    SynchronizedDirectBlockRefinement
      (commonSufficientDepth rootDiameter parents) rootDiameter parents :=
  synchronizedDirectBlockRefinementAtDepth rootDiameter rootDiameterPositive
    (commonSufficientDepth rootDiameter parents) parents proper (le_refl _)

private theorem localModelErrorBound_le_accuracy {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (accuracy : Coordinate)
    (depth : Nat) (left right : Coordinate)
    (movementLe :
      CCL.FiniteGeometric.quarterRadius
        (geometricMovement segment left right) depth <= accuracy) :
    localModelErrorBound differential segment accuracy depth left right <=
      (CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
          differential segment +
        CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
          differential segment) * (2 * accuracy) := by
  unfold localModelErrorBound
  have pointCoefficientNonnegative :=
    CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient_nonnegative
      differential segment
  have rootCoefficientNonnegative :=
    CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient_nonnegative
      differential segment
  have accuracyNonnegative : 0 <= accuracy :=
    (CCL.FiniteGeometric.quarterRadius_nonneg
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _) depth).trans
        movementLe
  have accuracyLeDouble : accuracy <= 2 * accuracy := by
    calc
      accuracy = 1 * accuracy := by ring1
      _ <= 2 * accuracy :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (by decide) accuracyNonnegative
  calc
    CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
          differential segment *
          CCL.FiniteGeometric.quarterRadius
            (geometricMovement segment left right) depth +
        CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
          differential segment * accuracy <=
      CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
          differential segment * accuracy +
        CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
          differential segment * accuracy :=
      add_le_add
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct movementLe
          pointCoefficientNonnegative) le_rfl
    _ = (CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
          differential segment +
        CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
          differential segment) * accuracy := by
      ring1
    _ <= (CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
          differential segment +
        CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
          differential segment) * (2 * accuracy) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        accuracyLeDouble (add_nonneg pointCoefficientNonnegative
          rootCoefficientNonnegative)

namespace SynchronizedDirectBlockRefinement

/-- The explicitly new child-model error is at most the common accuracy times
the finite path coefficient. -/
theorem refinementErrorSum_le_accuracy {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {accuracy : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth accuracy parents),
      0 < accuracy -> commonAccuracyDepth accuracy parents <= depth ->
      blocks.refinementErrorSum <=
        accuracy * refinementCoefficientSum differential parents
  | _, _, [], .nil, _accuracyPositive, _enough => by
      simp only [refinementErrorSum, refinementCoefficientSum,
        RFAP.ConstructiveFraction.mul_zero_direct]
      exact le_rfl
  | depth, accuracy, parent :: remaining,
      .cons _ _ _ tail, accuracyPositive, enough => by
      have movementLe := quarterRadius_le_accuracy_of_commonDepth accuracy
        accuracyPositive parent remaining depth enough
      have localBound := localModelErrorBound_le_accuracy differential
        parent.edge.segment accuracy depth
          parent.edge.left.parameter parent.edge.request.endpoint.parameter
            movementLe
      have thirtyTwoNonnegative : (0 : Coordinate) <= 32 := by
        calc
          (0 : Coordinate) <= 8 * 4 :=
            RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide)
          _ = 32 := by ring1
      have scaledLocal :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct localBound
          thirtyTwoNonnegative
      have movementNonnegative :
          0 <= geometricMovement parent.edge.segment
            parent.edge.left.parameter
              parent.edge.request.endpoint.parameter := by
        unfold geometricMovement
        exact RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
      have headBound :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct scaledLocal
          movementNonnegative
      have normalizedHead :
          geometricMovement parent.edge.segment parent.edge.left.parameter
              parent.edge.request.endpoint.parameter *
            (32 * localModelErrorBound differential parent.edge.segment
              accuracy depth parent.edge.left.parameter
                parent.edge.request.endpoint.parameter) <=
          accuracy *
            (geometricMovement parent.edge.segment parent.edge.left.parameter
                parent.edge.request.endpoint.parameter *
              (64 *
                (CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                    differential parent.edge.segment +
                  CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                    differential parent.edge.segment))) := by
        calc
          geometricMovement parent.edge.segment parent.edge.left.parameter
                parent.edge.request.endpoint.parameter *
              (32 * localModelErrorBound differential parent.edge.segment
                accuracy depth parent.edge.left.parameter
                  parent.edge.request.endpoint.parameter) <=
            geometricMovement parent.edge.segment parent.edge.left.parameter
                parent.edge.request.endpoint.parameter *
              (32 *
                ((CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                    differential parent.edge.segment +
                  CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                    differential parent.edge.segment) *
                  (2 * accuracy))) := headBound
          _ = accuracy *
              (geometricMovement parent.edge.segment parent.edge.left.parameter
                  parent.edge.request.endpoint.parameter *
                (64 *
                  (CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                      differential parent.edge.segment +
                    CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                      differential parent.edge.segment))) := by
            ring1
      have tailEnough : commonAccuracyDepth accuracy remaining <= depth :=
        (tailAccuracyDepth_le_common accuracy parent remaining).trans enough
      have tailBound := refinementErrorSum_le_accuracy tail accuracyPositive
        tailEnough
      simp only [refinementErrorSum, refinementCoefficientSum]
      calc
        geometricMovement parent.edge.segment parent.edge.left.parameter
              parent.edge.request.endpoint.parameter *
            (32 * localModelErrorBound differential parent.edge.segment
              accuracy depth parent.edge.left.parameter
                parent.edge.request.endpoint.parameter) +
            tail.refinementErrorSum <=
          accuracy *
              (geometricMovement parent.edge.segment
                  parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter *
                (64 *
                  (CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                      differential parent.edge.segment +
                    CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                      differential parent.edge.segment))) +
            accuracy * refinementCoefficientSum differential remaining :=
          add_le_add normalizedHead tailBound
        _ = accuracy *
            (geometricMovement parent.edge.segment parent.edge.left.parameter
                parent.edge.request.endpoint.parameter *
              (64 *
                (CCL.Riemann.PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                    differential parent.edge.segment +
                  CCL.Riemann.PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                    differential parent.edge.segment)) +
              refinementCoefficientSum differential remaining) := by
          ring1

/-- Aggregate version of the accuracy estimate, including the finite parent
path-count factor. -/
theorem aggregateRefinementError_le_accuracy {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {depth : Nat} {accuracy : Coordinate}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth accuracy parents)
    (accuracyPositive : 0 < accuracy)
    (enough : commonAccuracyDepth accuracy parents <= depth) :
    (parents.length : Coordinate) * blocks.refinementErrorSum <=
      accuracy * aggregateRefinementCoefficient differential parents := by
  have errorBound := blocks.refinementErrorSum_le_accuracy accuracyPositive
    enough
  have countNonnegative : (0 : Coordinate) <= (parents.length : Coordinate) :=
    coordinateNatCast_nonnegative parents.length
  have scaled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct errorBound
      countNonnegative
  unfold aggregateRefinementCoefficient
  calc
    (parents.length : Coordinate) * blocks.refinementErrorSum <=
        (parents.length : Coordinate) *
          (accuracy * refinementCoefficientSum differential parents) := scaled
    _ = accuracy *
        ((parents.length : Coordinate) *
          refinementCoefficientSum differential parents) := by
      ring1

end SynchronizedDirectBlockRefinement

/-- One canonical dyadic refinement whose numerical geometry is accurate for
every member of a displayed finite differential family. -/
structure FiniteDifferentialAccurateDirectRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (parents : List (CenteredEdge curve source))
    (targets : List (Differential genus))
    (target : Coordinate) where
  proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents
  rootDiameter : Coordinate
  rootDiameterPositive : 0 < rootDiameter
  depth : Nat
  clearanceEnough : commonSufficientDepth rootDiameter parents <= depth
  accuracyEnough : commonAccuracyDepth rootDiameter parents <= depth
  aggregateRefinementError_le : forall (differential : Differential genus),
    differential ∈ targets ->
    ((parents.map (recastCenteredEdge differential)).length : Coordinate) *
        (recastSynchronizedDirectBlockRefinementAtDepth differential
          rootDiameter rootDiameterPositive depth parents proper
            clearanceEnough).refinementErrorSum <= target

/-- Compute the common positive diameter and common finite depth for a whole
displayed differential family. -/
def finiteDifferentialAccurateDirectRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (parents : List (CenteredEdge curve source))
    (proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents)
    (targets : List (Differential genus))
    (target : Coordinate) (targetPositive : 0 < target) :
    FiniteDifferentialAccurateDirectRefinement parents targets target := by
  let accuracy := finiteDifferentialRefinementAccuracy parents targets target
  let depth := max (commonSufficientDepth accuracy parents)
    (commonAccuracyDepth accuracy parents)
  have accuracyPositive : 0 < accuracy :=
    finiteDifferentialRefinementAccuracy_positive parents targets
      targetPositive
  have clearanceEnough : commonSufficientDepth accuracy parents <= depth :=
    Nat.le_max_left _ _
  have accuracyEnough : commonAccuracyDepth accuracy parents <= depth :=
    Nat.le_max_right _ _
  refine
    { proper := proper
      rootDiameter := accuracy
      rootDiameterPositive := accuracyPositive
      depth := depth
      clearanceEnough := clearanceEnough
      accuracyEnough := accuracyEnough
      aggregateRefinementError_le := ?_ }
  intro differential member
  let targetBlocks := recastSynchronizedDirectBlockRefinementAtDepth
    differential accuracy accuracyPositive depth parents proper clearanceEnough
  have targetAccuracyEnough :
      commonAccuracyDepth accuracy
          (parents.map (recastCenteredEdge differential)) <= depth := by
    simpa only [commonAccuracyDepth_map_recast] using accuracyEnough
  exact
    (targetBlocks.aggregateRefinementError_le_accuracy accuracyPositive
      targetAccuracyEnough).trans
        (finiteDifferentialRefinementAccuracy_mul_coefficient_le parents targets
          differential member targetPositive)

namespace FiniteDifferentialAccurateDirectRefinement

/-- The one source-geometric child block retained for the next common state. -/
def blocks {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {parents : List (CenteredEdge curve source)}
    {targets : List (Differential genus)} {target : Coordinate}
    (result :
      FiniteDifferentialAccurateDirectRefinement parents targets target) :
    SynchronizedDirectBlockRefinement result.depth result.rootDiameter parents :=
  synchronizedDirectBlockRefinementAtDepth result.rootDiameter
    result.rootDiameterPositive result.depth parents result.proper
      result.clearanceEnough

/-- The same child partition, canonically recentered for one differential. -/
def recastBlocks {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {parents : List (CenteredEdge curve source)}
    {targets : List (Differential genus)} {target : Coordinate}
    (result :
      FiniteDifferentialAccurateDirectRefinement parents targets target)
    (differential : Differential genus) :
    SynchronizedDirectBlockRefinement result.depth result.rootDiameter
      (parents.map (recastCenteredEdge differential)) :=
  recastSynchronizedDirectBlockRefinementAtDepth differential
    result.rootDiameter result.rootDiameterPositive result.depth parents
      result.proper result.clearanceEnough

@[simp] theorem recastBlocks_children {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {parents : List (CenteredEdge curve source)}
    {targets : List (Differential genus)} {target : Coordinate}
    (result :
      FiniteDifferentialAccurateDirectRefinement parents targets target)
    (differential : Differential genus) :
    (result.recastBlocks differential).children =
      result.blocks.children.map (recastCenteredEdge differential) := by
  apply recastSynchronizedDirectBlockRefinementAtDepth_children

/-- Compatible parent--child integration models on the common recast child
geometry. -/
def compatible {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {parents : List (CenteredEdge curve source)}
    {targets : List (Differential genus)} {target : Coordinate}
    (result :
      FiniteDifferentialAccurateDirectRefinement parents targets target)
    (differential : Differential genus) :
    CompatibleConstantPathRefinement
      ((parents.map (recastCenteredEdge differential)).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      ((result.blocks.children.map (recastCenteredEdge differential)).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model) :=
  recastCompatibleAtDepth differential result.rootDiameter
    result.rootDiameterPositive result.depth parents result.proper
      result.clearanceEnough

/-- Every member's common child model meets the requested aggregate semantic
allowance. -/
theorem modelAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {parents : List (CenteredEdge curve source)}
    {targets : List (Differential genus)} {target : Coordinate}
    (result :
      FiniteDifferentialAccurateDirectRefinement parents targets target)
    (differential : Differential genus) (member : differential ∈ targets) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((result.blocks.children.map (recastCenteredEdge differential)).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
      target := by
  let targetBlocks := result.recastBlocks differential
  have modelBound := targetBlocks.modelAllowance_le_refinementError
    result.rootDiameterPositive.le
  rw [targetBlocks.models_eq_children_map,
    result.recastBlocks_children differential] at modelBound
  exact modelBound.trans
    (result.aggregateRefinementError_le differential member)

/-- The common member refinement has the honest parent-plus-child comparison
bound needed by a consecutive refinement program. -/
theorem comparisonAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {parents : List (CenteredEdge curve source)}
    {targets : List (Differential genus)} {target : Coordinate}
    (result :
      FiniteDifferentialAccurateDirectRefinement parents targets target)
    (differential : Differential genus) (member : differential ∈ targets) :
    (result.compatible differential).comparisonAllowance <=
      2 * (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((parents.map (recastCenteredEdge differential)).map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance +
        target := by
  let targetBlocks := result.recastBlocks differential
  have comparisonBound :=
    targetBlocks.comparisonAllowance_le_parent_add_error
  change
    (recastCompatibleAtDepth differential result.rootDiameter
      result.rootDiameterPositive result.depth parents result.proper
        result.clearanceEnough).comparisonAllowance <= _
  rw [recastCompatibleAtDepth_comparisonAllowance_eq]
  change targetBlocks.toCompatibleChildren.comparisonAllowance <= _
  rw [targetBlocks.toCompatibleChildren_comparisonAllowance_eq]
  exact comparisonBound.trans
    (add_le_add le_rfl
      (result.aggregateRefinementError_le differential member))

end FiniteDifferentialAccurateDirectRefinement

/-- A total synchronized refinement whose newly introduced aggregate model
error meets the requested positive rational target. -/
structure AccurateDirectRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parents : List (CenteredEdge curve differential))
    (target : Coordinate) where
  rootDiameter : Coordinate
  rootDiameterPositive : 0 < rootDiameter
  depth : Nat
  blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents
  aggregateRefinementError_le :
    (parents.length : Coordinate) * blocks.refinementErrorSum <= target

/-- Compute a positive root diameter and one common finite depth meeting both
clearance and aggregate new-error requirements. -/
def accurateDirectRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parents : List (CenteredEdge curve differential))
    (proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents)
    (target : Coordinate) (targetPositive : 0 < target) :
    AccurateDirectRefinement parents target := by
  let accuracy := refinementAccuracy differential parents target
  let depth := max (commonSufficientDepth accuracy parents)
    (commonAccuracyDepth accuracy parents)
  have accuracyPositive : 0 < accuracy :=
    refinementAccuracy_positive differential parents targetPositive
  have clearanceEnough : commonSufficientDepth accuracy parents <= depth :=
    Nat.le_max_left _ _
  have accuracyEnough : commonAccuracyDepth accuracy parents <= depth :=
    Nat.le_max_right _ _
  let blocks := synchronizedDirectBlockRefinementAtDepth accuracy
    accuracyPositive depth parents proper clearanceEnough
  have aggregateError := blocks.aggregateRefinementError_le_accuracy
    accuracyPositive accuracyEnough
  have requested := refinementAccuracy_mul_coefficient_le differential parents
    targetPositive
  exact
    { rootDiameter := accuracy
      rootDiameterPositive := accuracyPositive
      depth := depth
      blocks := blocks
      aggregateRefinementError_le := aggregateError.trans requested }

namespace AccurateDirectRefinement

/-- The refined child model itself meets the requested aggregate semantic
allowance. -/
theorem modelAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parents : List (CenteredEdge curve differential)}
    {target : Coordinate}
    (result : AccurateDirectRefinement parents target) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (result.blocks.children.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
      target := by
  rw [<- result.blocks.models_eq_children_map]
  exact (result.blocks.modelAllowance_le_refinementError
    result.rootDiameterPositive.le).trans
      result.aggregateRefinementError_le

/-- The requested new-error target gives a complete parent--child comparison
bound, with the old model allowance kept explicit. -/
theorem comparisonAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parents : List (CenteredEdge curve differential)}
    {target : Coordinate}
    (result : AccurateDirectRefinement parents target) :
    result.blocks.toCompatible.comparisonAllowance <=
      2 * (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (parents.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance +
        target :=
  result.blocks.comparisonAllowance_le_parent_add_error.trans
    (add_le_add le_rfl result.aggregateRefinementError_le)

/-- Reindexing the child cells to the ordinary centered-edge model list does
not change the quantitative comparison bound. -/
theorem comparisonAllowanceChildren_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parents : List (CenteredEdge curve differential)}
    {target : Coordinate}
    (result : AccurateDirectRefinement parents target) :
    result.blocks.toCompatibleChildren.comparisonAllowance <=
      2 * (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (parents.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance +
        target := by
  rw [result.blocks.toCompatibleChildren_comparisonAllowance_eq]
  exact result.comparisonAllowance_le

end AccurateDirectRefinement

/-! ## Total consecutive direct-refinement programs -/

/-- One finite centered path together with the nonstationarity evidence needed
to refine it again. -/
structure DirectRefinementState {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus) where
  start : LiftedPoint 2
  finish : LiftedPoint 2
  parents : List (CenteredEdge curve differential)
  proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents
  chain : DirectPathChain parents (start := start) (finish := finish)

namespace DirectRefinementState

/-- Recenter one retained geometric state for another differential.  The
prepared occurrences, endpoints, sheet labels, and dependent path are kept
unchanged; only the canonical coefficient centers are recomputed. -/
def recast {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (state : DirectRefinementState curve source) :
    DirectRefinementState curve target where
  start := state.start
  finish := state.finish
  parents := state.parents.map (recastCenteredEdge target)
  proper := allParentsProper_map_recast state.proper
  chain := state.chain.recast target

@[simp] theorem recast_start {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (state : DirectRefinementState curve source) :
    (state.recast target).start = state.start := rfl

@[simp] theorem recast_finish {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (state : DirectRefinementState curve source) :
    (state.recast target).finish = state.finish := rfl

/-- Apply one accuracy-selected refinement and retain its child path as the
next executable state. -/
def refine {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (state : DirectRefinementState curve differential)
    (target : Coordinate) (targetPositive : 0 < target) :
    DirectRefinementState curve differential :=
  let result := accurateDirectRefinement state.parents state.proper target
    targetPositive
  { start := state.start
    finish := state.finish
    parents := result.blocks.children
    proper := result.blocks.childrenProper
    chain := result.blocks.refinedChain state.chain }

/-- Lifted geometry retained by one finite refinement state. -/
def path {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (state : DirectRefinementState curve differential) :
    LiftedPath 2 state.start state.finish :=
  state.chain.path

/-- Recasting a state changes its algebraic differential model but not its
finite lifted path. -/
theorem path_recast {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    (state : DirectRefinementState curve source) :
    (state.recast target).path = state.path :=
  DirectPathChain.path_recast target state.chain

/-- Uniform algebraic certificates retained by one finite refinement state. -/
def certificates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (state : DirectRefinementState curve differential) :
    UniformPathCertificates curve differential
      (state.parents.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      state.path :=
  state.chain.certificates

end DirectRefinementState

/-- Positive base scale dominating the initial finite path allowance. -/
def directScheduleBase {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (initial : DirectRefinementState curve differential) : Coordinate :=
  (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (initial.parents.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance +
    1

theorem directScheduleBase_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (initial : DirectRefinementState curve differential) :
    0 < directScheduleBase initial := by
  unfold directScheduleBase
  exact add_pos_of_nonneg_of_pos
    (CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance_nonneg _)
    (by decide)

/-- Child semantic target used at step `index`; it is one quarter-radius later
than the allowance target for the displayed parent state. -/
def directScheduleTarget {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (initial : DirectRefinementState curve differential)
    (index : Nat) : Coordinate :=
  CCL.FiniteGeometric.quarterRadius (directScheduleBase initial) (index + 1)

theorem directScheduleTarget_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (initial : DirectRefinementState curve differential)
    (index : Nat) :
    0 < directScheduleTarget initial index :=
  CCL.FiniteGeometric.quarterRadius_pos
    (directScheduleBase_positive initial) (index + 1)

/-- Recursively computed centered paths.  Every natural index executes only
the finite refinement needed to reach that displayed state. -/
def directRefinementStates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (initial : DirectRefinementState curve differential) :
    Nat -> DirectRefinementState curve differential
  | 0 => initial
  | index + 1 =>
      (directRefinementStates initial index).refine
        (directScheduleTarget initial index)
          (directScheduleTarget_positive initial index)

theorem directRefinementStates_closed {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (initial : DirectRefinementState curve differential)
    (closed : initial.finish = initial.start) :
    forall index,
      (directRefinementStates initial index).finish =
        (directRefinementStates initial index).start
  | 0 => closed
  | index + 1 => directRefinementStates_closed initial closed index

private def closeLiftedPath
    {start finish : LiftedPoint 2}
    (path : LiftedPath 2 start finish)
    (closed : finish = start) : LiftedPath 2 start start :=
  closed ▸ path

private def closeUniformPathCertificates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {cells : List CCL.ProgressiveGaussianIntegration.CellModel}
    {start finish : LiftedPoint 2}
    {path : LiftedPath 2 start finish}
    (certificates : UniformPathCertificates curve differential cells path)
    (closed : finish = start) :
    UniformPathCertificates curve differential cells
      (closeLiftedPath path closed) := by
  cases closed
  exact certificates

/-- Closed lifted path at one requested finite refinement index. -/
def directRefinementClosedLift {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (initial : DirectRefinementState curve differential)
    (closed : initial.finish = initial.start)
    (index : Nat) : ClosedLiftedPath 2 := by
  let state := directRefinementStates initial index
  have stateClosed : state.finish = state.start :=
    directRefinementStates_closed initial closed index
  exact
    { basepoint := state.start
      path := closeLiftedPath state.path stateClosed }

/-- Cell-for-cell certificates on the closed lifted state at one requested
index. -/
def directRefinementClosedCertificates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (initial : DirectRefinementState curve differential)
    (closed : initial.finish = initial.start)
    (index : Nat) :
    UniformPathCertificates curve differential
      ((directRefinementStates initial index).parents.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      (directRefinementClosedLift initial closed index).path := by
  let state := directRefinementStates initial index
  have stateClosed : state.finish = state.start :=
    directRefinementStates_closed initial closed index
  exact closeUniformPathCertificates state.certificates stateClosed

/-- The complete certified transition used to compute one successor state. -/
def directScheduledRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (initial : DirectRefinementState curve differential)
    (index : Nat) :
    AccurateDirectRefinement
      (directRefinementStates initial index).parents
        (directScheduleTarget initial index) :=
  accurateDirectRefinement
    (directRefinementStates initial index).parents
    (directRefinementStates initial index).proper
    (directScheduleTarget initial index)
    (directScheduleTarget_positive initial index)

/-- Rational constant-cell model of one displayed recursively refined path. -/
def directRefinementModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (initial : DirectRefinementState curve differential)
    (index : Nat) : CCL.ProgressiveGaussianIntegration.PathModel :=
  CCL.ProgressiveGaussianIntegration.PathModel.mk
    ((directRefinementStates initial index).parents.map
      CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)

/-- One immediate compatible partition in the recursively computed path
program. -/
def directRefinementStep {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (initial : DirectRefinementState curve differential)
    (index : Nat) :
    CompatibleConstantPathRefinement
      (directRefinementModel initial index).cells
      (directRefinementModel initial (index + 1)).cells := by
  change CompatibleConstantPathRefinement
    ((directRefinementStates initial index).parents.map
      CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
    ((directScheduledRefinement initial index).blocks.children.map
      CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
  exact (directScheduledRefinement initial index).blocks.toCompatibleChildren

/-- Every displayed model meets its base quarter-radius semantic target. -/
theorem directRefinementModel_allowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (initial : DirectRefinementState curve differential) :
    forall (index : Nat),
      (directRefinementModel initial index).aggregateAllowance <=
        CCL.FiniteGeometric.quarterRadius
          (directScheduleBase initial) index
  | 0 => by
      unfold directRefinementModel directRefinementStates directScheduleBase
      simp only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_zero,
        RFAP.ConstructiveFraction.mul_one_direct]
      exact le_add_of_nonneg_right (by decide)
  | index + 1 => by
      change
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((directScheduledRefinement initial index).blocks.children.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
          directScheduleTarget initial index
      exact (directScheduledRefinement initial index).modelAllowance_le

/-- Consecutive parent--child comparison decays geometrically at three times
the base path scale. -/
theorem directRefinementStep_comparisonAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (initial : DirectRefinementState curve differential)
    (index : Nat) :
    (directRefinementStep initial index).comparisonAllowance <=
      CCL.FiniteGeometric.quarterRadius
        (3 * directScheduleBase initial) index := by
  have comparisonBound :=
    (directScheduledRefinement initial index).comparisonAllowanceChildren_le
  have parentBound := directRefinementModel_allowance_le initial index
  have doubledParent :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct parentBound
      (show (0 : Coordinate) <= 2 by decide)
  have targetLeParent : directScheduleTarget initial index <=
      CCL.FiniteGeometric.quarterRadius (directScheduleBase initial) index :=
    CCL.FiniteGeometric.quarterRadius_antitone
      (directScheduleBase_positive initial).le (Nat.le_succ index)
  change
    (directScheduledRefinement initial index).blocks.toCompatibleChildren.comparisonAllowance <=
      CCL.FiniteGeometric.quarterRadius
        (3 * directScheduleBase initial) index
  calc
    (directScheduledRefinement initial index).blocks.toCompatibleChildren.comparisonAllowance <=
        2 * (directRefinementModel initial index).aggregateAllowance +
          directScheduleTarget initial index := comparisonBound
    _ <= 2 * CCL.FiniteGeometric.quarterRadius
            (directScheduleBase initial) index +
          CCL.FiniteGeometric.quarterRadius
            (directScheduleBase initial) index :=
      add_le_add doubledParent targetLeParent
    _ = CCL.FiniteGeometric.quarterRadius
        (3 * directScheduleBase initial) index := by
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
      ring1

/-- Total consecutive compatible refinement program generated from any
finite nonstationary centered prepared path. -/
def directSequentialProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (initial : DirectRefinementState curve differential) :
    CCL.ProgressiveGaussianIntegration.SequentialCompatibleConstantRefinementProgram where
  model := directRefinementModel initial
  steps := directRefinementStep initial
  stepScale := 3 * directScheduleBase initial
  stepScale_nonneg := RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (directScheduleBase_positive initial).le
  initialAllowance_le := by
    have initialBound := directRefinementModel_allowance_le initial 0
    have baseNonnegative := (directScheduleBase_positive initial).le
    calc
      (directRefinementModel initial 0).aggregateAllowance <=
          directScheduleBase initial := by
        simpa only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_zero,
          RFAP.ConstructiveFraction.mul_one_direct] using initialBound
      _ = 1 * directScheduleBase initial := by ring1
      _ <= 12 * directScheduleBase initial :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (show (1 : Coordinate) <= 12 by decide) baseNonnegative
      _ = 4 * (3 * directScheduleBase initial) := by ring1
  comparisonAllowance_le := directRefinementStep_comparisonAllowance_le initial

/-! ## Common-geometry finite-differential programs -/

/-- Sum of the initial model allowances of a displayed finite differential
family on one common recentered parent geometry. -/
def finiteDifferentialModelAllowanceSum {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (parents : List (CenteredEdge curve source)) :
    List (Differential genus) -> Coordinate
  | [] => 0
  | differential :: remaining =>
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((parents.map (recastCenteredEdge differential)).map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance +
        finiteDifferentialModelAllowanceSum parents remaining

theorem finiteDifferentialModelAllowanceSum_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (parents : List (CenteredEdge curve source)) :
    forall (targets : List (Differential genus)),
      0 <= finiteDifferentialModelAllowanceSum parents targets
  | [] => le_rfl
  | differential :: remaining =>
      add_nonneg
        (CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance_nonneg
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            ((parents.map (recastCenteredEdge differential)).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)))
        (finiteDifferentialModelAllowanceSum_nonnegative parents remaining)

theorem memberModelAllowance_le_finiteDifferentialSum {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (parents : List (CenteredEdge curve source))
    (differential : Differential genus) :
    forall (targets : List (Differential genus)), differential ∈ targets ->
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((parents.map (recastCenteredEdge differential)).map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
        finiteDifferentialModelAllowanceSum parents targets
  | [], member => by simp only [List.not_mem_nil] at member
  | head :: remaining, member => by
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst head
        exact le_add_of_nonneg_right
          (finiteDifferentialModelAllowanceSum_nonnegative parents remaining)
      · exact
          (memberModelAllowance_le_finiteDifferentialSum parents differential
            remaining member).trans
              (le_add_of_nonneg_left
                (CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance_nonneg
                  (CCL.ProgressiveGaussianIntegration.PathModel.mk
                    ((parents.map (recastCenteredEdge head)).map
                      CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model))))

/-- Positive family scale dominating every listed differential's initial
model allowance. -/
def finiteDifferentialScheduleBase {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus)) : Coordinate :=
  finiteDifferentialModelAllowanceSum initial.parents targets + 1

theorem finiteDifferentialScheduleBase_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus)) :
    0 < finiteDifferentialScheduleBase initial targets := by
  unfold finiteDifferentialScheduleBase
  exact add_pos_of_nonneg_of_pos
    (finiteDifferentialModelAllowanceSum_nonnegative initial.parents targets)
    (by decide)

/-- The common new-error target for step `index`. -/
def finiteDifferentialScheduleTarget {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus)) (index : Nat) : Coordinate :=
  CCL.FiniteGeometric.quarterRadius
    (finiteDifferentialScheduleBase initial targets) (index + 1)

theorem finiteDifferentialScheduleTarget_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus)) (index : Nat) :
    0 < finiteDifferentialScheduleTarget initial targets index :=
  CCL.FiniteGeometric.quarterRadius_pos
    (finiteDifferentialScheduleBase_positive initial targets) (index + 1)

/-- Recursively computed source states.  Every successor uses one numerical
refinement accurate for the entire displayed differential family. -/
def finiteDifferentialRefinementStates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus)) :
    Nat -> DirectRefinementState curve source
  | 0 => initial
  | index + 1 =>
      let current := finiteDifferentialRefinementStates initial targets index
      let result := finiteDifferentialAccurateDirectRefinement current.parents
        current.proper targets
          (finiteDifferentialScheduleTarget initial targets index)
          (finiteDifferentialScheduleTarget_positive initial targets index)
      { start := current.start
        finish := current.finish
        parents := result.blocks.children
        proper := result.blocks.childrenProper
        chain := result.blocks.refinedChain current.chain }

/-- The complete common refinement used at one successor step. -/
def finiteDifferentialScheduledRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus)) (index : Nat) :
    FiniteDifferentialAccurateDirectRefinement
      (finiteDifferentialRefinementStates initial targets index).parents targets
        (finiteDifferentialScheduleTarget initial targets index) :=
  finiteDifferentialAccurateDirectRefinement
    (finiteDifferentialRefinementStates initial targets index).parents
    (finiteDifferentialRefinementStates initial targets index).proper targets
    (finiteDifferentialScheduleTarget initial targets index)
    (finiteDifferentialScheduleTarget_positive initial targets index)

/-- Differential-specific constant model on the recast common state. -/
def finiteDifferentialRefinementModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (index : Nat) :
    CCL.ProgressiveGaussianIntegration.PathModel :=
  CCL.ProgressiveGaussianIntegration.PathModel.mk
    (((finiteDifferentialRefinementStates initial targets index).parents.map
      (recastCenteredEdge differential)).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)

/-- One compatible member refinement on the source schedule's exact recast
child geometry. -/
def finiteDifferentialRefinementStep {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (index : Nat) :
    CompatibleConstantPathRefinement
      (finiteDifferentialRefinementModel initial targets differential index).cells
      (finiteDifferentialRefinementModel initial targets differential
        (index + 1)).cells := by
  change CompatibleConstantPathRefinement
    ((((finiteDifferentialRefinementStates initial targets index).parents.map
      (recastCenteredEdge differential)).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model))
    (((finiteDifferentialScheduledRefinement initial targets index).blocks.children.map
      (recastCenteredEdge differential)).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
  exact (finiteDifferentialScheduledRefinement initial targets index).compatible
    differential

/-- Every listed initial model is dominated by the common family base. -/
theorem finiteDifferentialInitialModelAllowance_le_base {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (member : differential ∈ targets) :
    (finiteDifferentialRefinementModel initial targets differential 0).aggregateAllowance <=
      finiteDifferentialScheduleBase initial targets := by
  unfold finiteDifferentialRefinementModel finiteDifferentialRefinementStates
    finiteDifferentialScheduleBase
  exact
    (memberModelAllowance_le_finiteDifferentialSum initial.parents differential
      targets member).trans (le_add_of_nonneg_right (by decide))

/-- Every common-geometry member model meets the family quarter-radius
semantic target. -/
theorem finiteDifferentialRefinementModel_allowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (member : differential ∈ targets) :
    forall (index : Nat),
      (finiteDifferentialRefinementModel initial targets differential index).aggregateAllowance <=
        CCL.FiniteGeometric.quarterRadius
          (finiteDifferentialScheduleBase initial targets) index
  | 0 => by
      simpa only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_zero,
        RFAP.ConstructiveFraction.mul_one_direct] using
          finiteDifferentialInitialModelAllowance_le_base initial targets
            differential member
  | index + 1 => by
      change
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (((finiteDifferentialScheduledRefinement initial targets index).blocks.children.map
            (recastCenteredEdge differential)).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
          finiteDifferentialScheduleTarget initial targets index
      exact (finiteDifferentialScheduledRefinement initial targets index).modelAllowance_le
        differential member

/-- Consecutive comparison allowance for every listed member decays on the
same three-times-family scale. -/
theorem finiteDifferentialRefinementStep_comparisonAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (member : differential ∈ targets)
    (index : Nat) :
    (finiteDifferentialRefinementStep initial targets differential index).comparisonAllowance <=
      CCL.FiniteGeometric.quarterRadius
        (3 * finiteDifferentialScheduleBase initial targets) index := by
  let result := finiteDifferentialScheduledRefinement initial targets index
  have comparisonBound := result.comparisonAllowance_le differential member
  have parentBound := finiteDifferentialRefinementModel_allowance_le initial
    targets differential member index
  have doubledParent :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct parentBound
      (show (0 : Coordinate) <= 2 by decide)
  have targetLeParent :
      finiteDifferentialScheduleTarget initial targets index <=
        CCL.FiniteGeometric.quarterRadius
          (finiteDifferentialScheduleBase initial targets) index :=
    CCL.FiniteGeometric.quarterRadius_antitone
      (finiteDifferentialScheduleBase_positive initial targets).le
      (Nat.le_succ index)
  change
    (result.compatible differential).comparisonAllowance <=
      CCL.FiniteGeometric.quarterRadius
        (3 * finiteDifferentialScheduleBase initial targets) index
  calc
    (result.compatible differential).comparisonAllowance <=
        2 * (finiteDifferentialRefinementModel initial targets differential
          index).aggregateAllowance +
            finiteDifferentialScheduleTarget initial targets index :=
      comparisonBound
    _ <= 2 * CCL.FiniteGeometric.quarterRadius
            (finiteDifferentialScheduleBase initial targets) index +
          CCL.FiniteGeometric.quarterRadius
            (finiteDifferentialScheduleBase initial targets) index :=
      add_le_add doubledParent targetLeParent
    _ = CCL.FiniteGeometric.quarterRadius
        (3 * finiteDifferentialScheduleBase initial targets) index := by
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
      ring1

/-- Total consecutive program for one listed differential, with its models
following the one recursively computed common geometry. -/
def finiteDifferentialSequentialProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (member : differential ∈ targets) :
    CCL.ProgressiveGaussianIntegration.SequentialCompatibleConstantRefinementProgram
    where
  model := finiteDifferentialRefinementModel initial targets differential
  steps := finiteDifferentialRefinementStep initial targets differential
  stepScale := 3 * finiteDifferentialScheduleBase initial targets
  stepScale_nonneg := RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (finiteDifferentialScheduleBase_positive initial targets).le
  initialAllowance_le := by
    have initialBound :=
      finiteDifferentialInitialModelAllowance_le_base initial targets
        differential member
    have baseNonnegative :=
      (finiteDifferentialScheduleBase_positive initial targets).le
    calc
      (finiteDifferentialRefinementModel initial targets differential 0).aggregateAllowance <=
        finiteDifferentialScheduleBase initial targets := initialBound
      _ = 1 * finiteDifferentialScheduleBase initial targets := by ring1
      _ <= 12 * finiteDifferentialScheduleBase initial targets :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (show (1 : Coordinate) <= 12 by decide) baseNonnegative
      _ = 4 * (3 * finiteDifferentialScheduleBase initial targets) := by ring1
  comparisonAllowance_le :=
    finiteDifferentialRefinementStep_comparisonAllowance_le initial targets
      differential member

theorem finiteDifferentialRefinementStates_start {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus)) :
    forall index,
      (finiteDifferentialRefinementStates initial targets index).start =
        initial.start
  | 0 => rfl
  | index + 1 => finiteDifferentialRefinementStates_start initial targets index

theorem finiteDifferentialRefinementStates_finish {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus)) :
    forall index,
      (finiteDifferentialRefinementStates initial targets index).finish =
        initial.finish
  | 0 => rfl
  | index + 1 => finiteDifferentialRefinementStates_finish initial targets index

theorem finiteDifferentialRefinementStates_closed {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus))
    (closed : initial.finish = initial.start) :
    forall index,
      (finiteDifferentialRefinementStates initial targets index).finish =
        (finiteDifferentialRefinementStates initial targets index).start
  | index => by
      rw [finiteDifferentialRefinementStates_finish initial targets index,
        finiteDifferentialRefinementStates_start initial targets index]
      exact closed

/-- The common source path with its recursively preserved endpoints cast back
to the fixed initial endpoint indices. -/
def finiteDifferentialRefinementPath {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus)) (index : Nat) :
    LiftedPath 2 initial.start initial.finish :=
  let state := finiteDifferentialRefinementStates initial targets index
  (state.path.castStart
    (finiteDifferentialRefinementStates_start initial targets index)).castFinish
      (finiteDifferentialRefinementStates_finish initial targets index)

/-- Closed lifted path of the one common source state at a requested index. -/
def finiteDifferentialRefinementClosedLift {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus))
    (closed : initial.finish = initial.start)
    (index : Nat) : ClosedLiftedPath 2 := by
  let state := finiteDifferentialRefinementStates initial targets index
  have stateClosed : state.finish = state.start :=
    finiteDifferentialRefinementStates_closed initial targets closed index
  exact
    { basepoint := state.start
      path := closeLiftedPath state.path stateClosed }

/-- Transport a uniform certificate family across equality of its complete
dependent lifted path index. -/
private def castUniformPathCertificatesPath {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {cells : List CCL.ProgressiveGaussianIntegration.CellModel}
    {start finish : LiftedPoint 2}
    {left right : LiftedPath 2 start finish}
    (equal : left = right)
    (certificates : UniformPathCertificates curve differential cells left) :
    UniformPathCertificates curve differential cells right :=
  equal ▸ certificates

/-- Every target differential is certified on the common open source path
with the fixed initial endpoint indices. -/
def finiteDifferentialRefinementPathCertificates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (index : Nat) :
    UniformPathCertificates curve differential
      (finiteDifferentialRefinementModel initial targets differential index).cells
      (finiteDifferentialRefinementPath initial targets index) := by
  let state := finiteDifferentialRefinementStates initial targets index
  have onStatePath : UniformPathCertificates curve differential
      ((state.parents.map (recastCenteredEdge differential)).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      state.path :=
    castUniformPathCertificatesPath (state.path_recast differential)
      (state.recast differential).certificates
  exact UniformPathCertificates.castFinish
    (finiteDifferentialRefinementStates_finish initial targets index)
      (UniformPathCertificates.castStart
        (finiteDifferentialRefinementStates_start initial targets index)
          onStatePath)

/-- Every listed differential is certified cell-for-cell on exactly the
common closed lifted source path. -/
def finiteDifferentialRefinementClosedCertificates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus)
    (closed : initial.finish = initial.start)
    (index : Nat) :
    UniformPathCertificates curve differential
      (finiteDifferentialRefinementModel initial targets differential index).cells
      (finiteDifferentialRefinementClosedLift initial targets closed index).path := by
  let state := finiteDifferentialRefinementStates initial targets index
  have stateClosed : state.finish = state.start :=
    finiteDifferentialRefinementStates_closed initial targets closed index
  have onCommonPath : UniformPathCertificates curve differential
      ((state.parents.map (recastCenteredEdge differential)).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      state.path :=
    castUniformPathCertificatesPath (state.path_recast differential)
      (state.recast differential).certificates
  exact closeUniformPathCertificates onCommonPath stateClosed

/-! ## Certified centered paths -/

set_option linter.unusedVariables false in
/-- A geometrically consecutive centered-edge list on fixed sheet labels.
The dependent endpoints enforce adjacency without storing an additional
propositional continuity field. -/
inductive CenteredPathChain {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    (parents : List (CenteredEdge curve differential)) ->
      {start finish : LiftedPoint 2} -> Type 2
  | nil (point : LiftedPoint 2) : CenteredPathChain [] (start := point)
      (finish := point)
  | cons (parent : CenteredEdge curve differential)
      {remaining : List (CenteredEdge curve differential)}
      {finish : LiftedPoint 2}
      (tail : CenteredPathChain remaining
        (start :=
          { coordinate := parent.edge.segment.pointAt
              parent.edge.request.endpoint.parameter
            sheet := parent.edge.sheet })
        (finish := finish)) :
      CenteredPathChain (parent :: remaining)
        (start :=
          { coordinate := parent.edge.segment.pointAt parent.edge.left.parameter
            sheet := parent.edge.sheet })
        (finish := finish)

namespace CenteredPathChain

/-- Concatenate two canonical centered chains at their exact shared lifted
endpoint. -/
def append {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {first second : List (CenteredEdge curve differential)}
      {start middle finish : LiftedPoint 2},
      CenteredPathChain first (start := start) (finish := middle) ->
      CenteredPathChain second (start := middle) (finish := finish) ->
        CenteredPathChain (first ++ second) (start := start) (finish := finish)
  | [], _, _, _, _, .nil _, second => second
  | _ :: _, _, _, _, _, .cons parent tail, second =>
      .cons parent (append tail second)

/-- Change only the propositionally equal starting endpoint index. -/
def castStart {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parents : List (CenteredEdge curve differential)}
    {left right finish : LiftedPoint 2} (equal : left = right)
    (chain : CenteredPathChain parents (start := left) (finish := finish)) :
    CenteredPathChain parents (start := right) (finish := finish) := by
  subst right
  exact chain

/-- Change only the propositionally equal finishing endpoint index. -/
def castFinish {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parents : List (CenteredEdge curve differential)}
    {start left right : LiftedPoint 2} (equal : left = right)
    (chain : CenteredPathChain parents (start := start) (finish := left)) :
    CenteredPathChain parents (start := start) (finish := right) := by
  subst right
  exact chain

private theorem model_start {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) :
    parent.model.start =
      parent.edge.segment.pointAt parent.edge.left.parameter := by
  change parent.edge.point 0 = _
  change
    (CCL.Riemann.PreparedDifferentialModels.edge curve parent.edge.segment
      parent.edge.within parent.edge.left parent.edge.request).pointAt 0 = _
  unfold CCL.Riemann.PreparedDifferentialModels.edge
  simpa only [CCL.Riemann.PreparedSheetContinuation.parameterAt_zero] using
    (CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
      parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.request 0).symm

private theorem model_finish {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) :
    parent.model.finish =
      parent.edge.segment.pointAt
        parent.edge.request.endpoint.parameter := by
  change parent.edge.point 1 = _
  change
    (CCL.Riemann.PreparedDifferentialModels.edge curve parent.edge.segment
      parent.edge.within parent.edge.left parent.edge.request).pointAt 1 = _
  unfold CCL.Riemann.PreparedDifferentialModels.edge
  simpa only [CCL.Riemann.PreparedSheetContinuation.parameterAt_one] using
    (CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
      parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.request 1).symm

/-- Canonical lifted path carried by the centered edge chain. -/
def path {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2},
      CenteredPathChain parents (start := start) (finish := finish) ->
        LiftedPath 2 start finish
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .cons
        (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet parent.edge.sheet
          parent.edge.localSegment)
        tail.path

/-- Every centered edge in the canonical chain retains its uniform algebraic
semantics. -/
def certificates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2}
      (chain : CenteredPathChain parents (start := start) (finish := finish)),
      UniformPathCertificates curve differential
        (parents.map CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
        chain.path
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .cons (model_start parent) (model_finish parent)
        (parent.edge.centeredValidCertificate curve differential parent.center)
        tail.certificates

/-- Forget the provenance of an existing canonical centered chain while
retaining exactly the dependent edge order needed by the direct refiner. -/
def toDirectPathChain {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2},
      CenteredPathChain parents (start := start) (finish := finish) ->
        DirectPathChain parents (start := start) (finish := finish)
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .cons parent tail.toDirectPathChain

/-- Package a canonical centered chain as the initial executable direct
refinement state. -/
def toDirectRefinementState {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parents : List (CenteredEdge curve differential)}
    {start finish : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := start) (finish := finish))
    (proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents) :
    DirectRefinementState curve differential where
  start := start
  finish := finish
  parents := parents
  proper := proper
  chain := chain.toDirectPathChain

/-- The centered edges exposed by an ordinary prepared subdivision form the
canonical consecutive chain definitionally.  This is the bridge from the
existing dependent continuation representation to direct certified blocks. -/
def ofCenteredSubdivision {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision :
      CCL.Riemann.PreparedSubdivisionModels.PreparedSubdivision segment within
        left owner) ->
    (centers : CCL.Riemann.PreparedSubdivisionModels.CenterStates curve
      differential sheet subdivision) ->
    CenteredPathChain
      (CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
        sheet subdivision centers)
      (start :=
        { coordinate := segment.pointAt left.parameter, sheet := sheet })
      (finish :=
        { coordinate := segment.pointAt subdivision.endpoint.parameter,
          sheet := sheet })
  | .stop endpoint owner, _centers => .nil _
  | .next current owner request cached ordered small remaining, centers =>
      .cons
        { edge :=
            { ambient := ambient
              start := start
              finish := finish
              segment := segment
              within := within
              left := current
              owner := owner
              request := request
              cached := cached
              ordered := ordered
              small := small
              sheet := sheet }
          center := centers.1 }
        (ofCenteredSubdivision curve differential sheet remaining centers.2)

/-- Canonically centered data for one complete prepared segment.  Packaging
the ordinary parent list together with its dependent endpoint chain lets both
views share the same evaluated family of differential center states. -/
structure PreparedSegmentCenteredData {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus) (sheet : Fin 2)
    (start finish : Gaussian) where
  parents : List (CenteredEdge curve differential)
  chain : CenteredPathChain parents
    (start := { coordinate := start, sheet := sheet })
    (finish := { coordinate := finish, sheet := sheet })

/-- Fold a prepared subdivision once, constructing each canonical centred edge
and retaining both its ordinary-list and dependent-chain views.  Keeping the
views in one recursive package avoids replaying the dependent subdivision for
centres, parents, and endpoint adjacency separately. -/
def dataOfCanonicalSubdivision {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision :
      CCL.Riemann.PreparedSubdivisionModels.PreparedSubdivision segment within
        left owner) ->
      PreparedSegmentCenteredData curve differential sheet
        (segment.pointAt left.parameter)
        (segment.pointAt subdivision.endpoint.parameter)
  | .stop endpoint _owner =>
      { parents := []
        chain := .nil _ }
  | .next current owner request cached ordered small remaining =>
      let edge :=
        CCL.Riemann.PreparedSubdivisionModels.edgeOfStep curve differential
          segment within current owner request cached ordered small sheet
      let centered : CenteredEdge curve differential :=
        { edge := edge
          center :=
            CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState.canonical
              edge }
      let tail := dataOfCanonicalSubdivision curve differential segment within
        sheet remaining
      { parents := centered :: tail.parents
        chain := .cons centered tail.chain }

/-- The single-pass package exposes the same canonical parent list as the
ordinary subdivision-model interface. -/
theorem dataOfCanonicalSubdivision_parents {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision :
      CCL.Riemann.PreparedSubdivisionModels.PreparedSubdivision segment within
        left owner),
      (dataOfCanonicalSubdivision curve differential segment within sheet
        subdivision).parents =
        CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
          sheet subdivision
            (CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates curve
              differential sheet subdivision)
  | .stop _endpoint _owner => rfl
  | .next current owner request cached ordered small remaining => by
      simp only [dataOfCanonicalSubdivision,
        CCL.Riemann.PreparedSubdivisionModels.centeredEdges,
        CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates]
      rw [dataOfCanonicalSubdivision_parents curve differential segment within
        sheet remaining]

/-- Compute every canonical centred edge of one complete segment once and
retain both its list and dependent-chain projections. -/
def dataOfCompleteSegment {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2)
    (prepared :
      CCL.Riemann.PreparedClearPathModels.CompleteSegment segment within owner) :
    PreparedSegmentCenteredData curve differential sheet start finish := by
  let data := dataOfCanonicalSubdivision curve differential segment within
    sheet prepared.subdivision
  let startEqual := congrArg
    (fun coordinate : Gaussian =>
      ({ coordinate := coordinate, sheet := sheet } : LiftedPoint 2))
    prepared.start_eq
  let finishEqual := congrArg
    (fun coordinate : Gaussian =>
      ({ coordinate := coordinate, sheet := sheet } : LiftedPoint 2))
    prepared.finish_eq
  exact
    { parents := data.parents
      chain := (data.chain.castStart startEqual).castFinish finishEqual }

@[simp] theorem dataOfCompleteSegment_parents {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2)
    (prepared :
      CCL.Riemann.PreparedClearPathModels.CompleteSegment segment within owner) :
    (dataOfCompleteSegment curve differential sheet prepared).parents =
      prepared.centeredEdges curve differential sheet := by
  exact dataOfCanonicalSubdivision_parents curve differential segment within
    sheet prepared.subdivision

@[simp] theorem dataOfCompleteSegment_parents_length {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2)
    (prepared :
      CCL.Riemann.PreparedClearPathModels.CompleteSegment segment within owner) :
    (dataOfCompleteSegment curve differential sheet prepared).parents.length =
      prepared.subdivision.stepCount := by
  rw [dataOfCompleteSegment_parents]
  exact CCL.Riemann.PreparedSubdivisionModels.centeredEdges_length
    curve differential sheet prepared.subdivision _

/-- Canonical centered chain of one completely prepared clear segment, with
its dependent endpoints transported back to the original segment endpoints. -/
def ofCompleteSegment {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2)
    (prepared :
      CCL.Riemann.PreparedClearPathModels.CompleteSegment segment within owner) :
    CenteredPathChain
      (prepared.centeredEdges curve differential sheet)
      (start := { coordinate := start, sheet := sheet })
      (finish := { coordinate := finish, sheet := sheet }) := by
  let centers :=
    CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates curve
      differential sheet prepared.subdivision
  let chain := ofCenteredSubdivision curve differential sheet
    prepared.subdivision centers
  let startEqual := congrArg
    (fun coordinate : Gaussian =>
      ({ coordinate := coordinate, sheet := sheet } : LiftedPoint 2))
    prepared.start_eq
  let finishEqual := congrArg
    (fun coordinate : Gaussian =>
      ({ coordinate := coordinate, sheet := sheet } : LiftedPoint 2))
    prepared.finish_eq
  exact (chain.castStart startEqual).castFinish finishEqual

private def AllParameterEdgesProper :
    List CCL.Riemann.ClearSheetContinuation.Subdivision.ParameterEdge -> Prop
  | [] => True
  | edge :: remaining =>
      edge.left.parameter < edge.right.parameter /\
        AllParameterEdgesProper remaining

private theorem allParameterEdgesProper_append : forall
    (first second :
      List CCL.Riemann.ClearSheetContinuation.Subdivision.ParameterEdge),
    AllParameterEdgesProper first -> AllParameterEdgesProper second ->
      AllParameterEdgesProper (first ++ second)
  | [], _second, _firstProper, secondProper => secondProper
  | _ :: _, _second, firstProper, secondProper =>
      ⟨firstProper.1,
        allParameterEdgesProper_append _ _ firstProper.2 secondProper⟩

private theorem allParameterEdgesProper_of_strictParameterEdges : forall
    (edges :
      List CCL.Riemann.ClearSheetContinuation.Subdivision.ParameterEdge),
    CCL.Riemann.PreparedClearPathModels.PreparedPath.StrictParameterEdges
        edges ->
      AllParameterEdgesProper edges
  | [], _proper => trivial
  | _edge :: remaining, proper =>
      ⟨proper.1,
        allParameterEdgesProper_of_strictParameterEdges remaining proper.2⟩

private theorem dyadicEdges_allParameterEdgesProper : forall
    (depth : Nat) (left right : Endpoint),
    left.parameter < right.parameter ->
      AllParameterEdgesProper
        (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges depth
          left right)
  | 0, _left, _right, proper => ⟨proper, trivial⟩
  | depth + 1, left, right, proper => by
      let middle : Endpoint :=
        ⟨CCL.Riemann.ClearSheetContinuation.midpoint left.parameter
            right.parameter,
          CCL.Riemann.ClearSheetContinuation.midpoint_inside
            left.inside right.inside⟩
      apply allParameterEdgesProper_append
      · exact dyadicEdges_allParameterEdgesProper depth left middle
          (left_lt_midpoint proper)
      · exact dyadicEdges_allParameterEdgesProper depth middle right
          (midpoint_lt_right proper)

private theorem allParentsProper_of_parameterEdgesProper {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall (parents : List (CenteredEdge curve differential)),
      AllParameterEdgesProper
        (parents.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.parameterEdge) ->
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents
  | [], _proper => trivial
  | _ :: remaining, proper =>
      ⟨proper.1,
        allParentsProper_of_parameterEdgesProper remaining proper.2⟩

/-- Every centered edge of one successfully checked dyadic segment has
strictly positive parameter width. -/
theorem ofSafeDyadic_allParentsProper {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.DyadicMeshSafe segment
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint
        (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive) :
    CCL.Riemann.PreparedDyadicRefinements.AllParentsProper
      ((CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofSafeDyadic
        segment within owner depth rootDiameter rootDiameterPositive safe).centeredEdges
          curve differential sheet) := by
  apply allParentsProper_of_parameterEdgesProper
  rw [CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofSafeDyadic_centeredEdges_parameterEdges]
  exact dyadicEdges_allParameterEdgesProper depth
    CCL.Riemann.PreparedClearPathModels.zeroEndpoint
    CCL.Riemann.PreparedClearPathModels.oneEndpoint (by decide)

/-- Every centered edge returned by an executable successful dyadic check has
strictly positive parameter width. -/
theorem ofTryDyadic_allParentsProper {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision :
      CCL.Riemann.PreparedSubdivisionModels.PreparedSubdivision segment within
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)}
    (success :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.tryDyadic segment
        within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint
        (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive = some subdivision) :
    CCL.Riemann.PreparedDyadicRefinements.AllParentsProper
      ((CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic
        segment within owner depth rootDiameter rootDiameterPositive
          success).centeredEdges curve differential sheet) := by
  apply allParentsProper_of_parameterEdgesProper
  rw [CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic_centeredEdges_parameterEdges
    curve differential segment within owner sheet depth rootDiameter
      rootDiameterPositive success]
  exact dyadicEdges_allParameterEdgesProper depth
    CCL.Riemann.PreparedClearPathModels.zeroEndpoint
    CCL.Riemann.PreparedClearPathModels.oneEndpoint (by decide)

/-- The centered edges, their dependent endpoint order, and their positive
parameter widths extracted from one checked common-depth path.  Packaging the
three pieces together avoids a choice of an independently supplied flattened
edge list. -/
structure CheckedDyadicCenteredState {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus) (sheet : Fin 2)
    (start finish : Gaussian) where
  parents : List (CenteredEdge curve differential)
  proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents
  chain : CenteredPathChain parents
    (start := { coordinate := start, sheet := sheet })
    (finish := { coordinate := finish, sheet := sheet })

/-- The executable centered data extracted from a prepared path, before
attaching the proof that every parent has positive parameter width.  Keeping
the data separate from that proof lets an executed bank consume the prepared
path it already stores instead of replaying its successful checker. -/
structure PreparedPathCenteredData {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus) (sheet : Fin 2)
    (start finish : Gaussian) where
  parents : List (CenteredEdge curve differential)
  chain : CenteredPathChain parents
    (start := { coordinate := start, sheet := sheet })
    (finish := { coordinate := finish, sheet := sheet })

/-- Extract the centered parents and their dependent endpoint chain directly
from stored prepared-path data. -/
def ofPreparedPath {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {ambient : RFAP.Boxes.Box} :
    forall {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)},
      CCL.Riemann.PreparedClearPathModels.PreparedPath path owner ->
        PreparedPathCenteredData curve differential sheet start finish
  | _, _, .nil point, _, .nil _ _owner =>
      { parents := []
        chain := .nil _ }
  | _, _, .cons _head _tail, _,
      .cons _ _ _owner _headWithin preparedHead preparedTail =>
      let headData :=
        dataOfCompleteSegment curve differential sheet preparedHead
      let tailData := ofPreparedPath curve differential sheet preparedTail
      { parents :=
          headData.parents ++ tailData.parents
        chain :=
          headData.chain.append tailData.chain }
termination_by structural _ _ path _ _ => path

/-- The centre-free path endpoint is exactly the fold over the canonical
centred parent list retained by the direct-refinement presentation. -/
theorem ofPreparedPath_integralRealLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {ambient : RFAP.Boxes.Box} :
    forall {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner),
      prepared.integralRealLower curve differential sheet =
        CCL.Riemann.PreparedSubdivisionModels.centeredEdgesIntegralRealLower
          (ofPreparedPath curve differential sheet prepared).parents
  | _, _, .nil _point, _, .nil _ _owner => rfl
  | _, _, .cons _head _tail, _,
      .cons _ _ _owner _headWithin preparedHead preparedTail => by
      simp only [CCL.Riemann.PreparedClearPathModels.PreparedPath.integralRealLower,
        ofPreparedPath,
        CCL.Riemann.PreparedSubdivisionModels.centeredEdgesIntegralRealLower_append,
        dataOfCompleteSegment_parents]
      have headEqual :
          preparedHead.integralRealLower curve differential sheet =
            CCL.Riemann.PreparedSubdivisionModels.centeredEdgesIntegralRealLower
              (preparedHead.centeredEdges curve differential sheet) := by
        unfold CCL.Riemann.PreparedClearPathModels.CompleteSegment.integralRealLower
          CCL.Riemann.PreparedClearPathModels.CompleteSegment.centeredEdges
        exact
          CCL.Riemann.PreparedSubdivisionModels.preparedSubdivisionIntegralRealLower_eq_centeredEdges
            curve differential sheet preparedHead.subdivision
              (CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates curve
                differential sheet preparedHead.subdivision)
      rw [headEqual,
        ofPreparedPath_integralRealLower curve differential sheet preparedTail]

/-- The centre-free directional endpoint is exactly the same fold over the
canonical centred parents retained by the direct-refinement presentation. -/
theorem ofPreparedPath_directionalIntegralLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) (direction : Gaussian)
    {ambient : RFAP.Boxes.Box} :
    forall {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner),
      prepared.directionalIntegralLower curve differential sheet direction =
        CCL.Riemann.PreparedSubdivisionModels.centeredEdgesDirectionalIntegralLower
          direction (ofPreparedPath curve differential sheet prepared).parents
  | _, _, .nil _point, _, .nil _ _owner => rfl
  | _, _, .cons _head _tail, _,
      .cons _ _ _owner _headWithin preparedHead preparedTail => by
      simp only [
        CCL.Riemann.PreparedClearPathModels.PreparedPath.directionalIntegralLower,
        ofPreparedPath,
        CCL.Riemann.PreparedSubdivisionModels.centeredEdgesDirectionalIntegralLower_append,
        dataOfCompleteSegment_parents]
      have headEqual :
          preparedHead.directionalIntegralLower curve differential sheet
              direction =
            CCL.Riemann.PreparedSubdivisionModels.centeredEdgesDirectionalIntegralLower
              direction
                (preparedHead.centeredEdges curve differential sheet) := by
        unfold
          CCL.Riemann.PreparedClearPathModels.CompleteSegment.directionalIntegralLower
          CCL.Riemann.PreparedClearPathModels.CompleteSegment.centeredEdges
        exact
          CCL.Riemann.PreparedSubdivisionModels.preparedSubdivisionDirectionalIntegralLower_eq_centeredEdges
            curve differential sheet direction preparedHead.subdivision
              (CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates curve
                differential sheet preparedHead.subdivision)
      rw [headEqual,
        ofPreparedPath_directionalIntegralLower curve differential sheet
          direction preparedTail]

/-- The single-pass centred path cache retains exactly the accepted prepared
edge count. -/
@[simp] theorem ofPreparedPath_parents_length {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {ambient : RFAP.Boxes.Box} :
    forall {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner),
      (ofPreparedPath curve differential sheet prepared).parents.length =
        prepared.stepCount
  | _, _, .nil point, _, .nil _ _owner => rfl
  | _, _, .cons _head _tail, _,
      .cons _ _ _owner _headWithin preparedHead preparedTail => by
      simp only [ofPreparedPath, List.length_append,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.stepCount,
        dataOfCompleteSegment_parents_length,
        ofPreparedPath_parents_length curve differential sheet preparedTail]

/-- Strict parameter orientation cached on a prepared path supplies exactly
the positive-width invariant required by the centred parent list. -/
theorem ofPreparedPath_allParentsProper_of_allEdgesProper {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {ambient : RFAP.Boxes.Box} :
    forall {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner),
      CCL.Riemann.PreparedClearPathModels.PreparedPath.AllEdgesProper
          prepared ->
        CCL.Riemann.PreparedDyadicRefinements.AllParentsProper
          ((ofPreparedPath curve differential sheet prepared).parents)
  | _, _, .nil _point, _, .nil _ _owner, _proper => trivial
  | _, _, .cons _head _tail, _,
      .cons _ _ _owner _headWithin preparedHead preparedTail, proper => by
      apply allParentsProper_append
      · apply allParentsProper_of_parameterEdgesProper
        rw [dataOfCompleteSegment_parents,
          CCL.Riemann.PreparedClearPathModels.CompleteSegment.centeredEdges_parameterEdges]
        exact allParameterEdgesProper_of_strictParameterEdges _ proper.1
      · exact ofPreparedPath_allParentsProper_of_allEdgesProper curve
          differential sheet preparedTail proper.2

/-- Successful common-depth preparation proves that the parents extracted
from the stored result all have positive parameter width.  This theorem is
proof-only; executable consumers retain and traverse the stored result rather
than recomputing it from the success equality. -/
theorem ofPreparedPath_allParentsProper_of_tryDyadic {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      (path : ClearPath curve.polynomial ambient start finish)
      (within : path.WithinAmbient)
      (owner : Owner (curve.polynomial.eval start))
      (prepared :
        CCL.Riemann.PreparedClearPathModels.PreparedPath path owner),
      CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic path within
          owner depth rootDiameter rootDiameterPositive = some prepared ->
        CCL.Riemann.PreparedDyadicRefinements.AllParentsProper
          ((ofPreparedPath curve differential sheet prepared).parents) := by
  intro ambient start finish path
  induction path with
  | nil point =>
      intro _within _owner _prepared success
      simp only
        [CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic] at success
      cases success
      simpa only [ofPreparedPath] using
        (show CCL.Riemann.PreparedDyadicRefinements.AllParentsProper [] from
          trivial)
  | cons head tail inductionHypothesis =>
      intro within owner _prepared success
      rw [CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic] at success
      split at success
      next => contradiction
      next subdivision headSuccess =>
        simp only at success
        split at success
        next => contradiction
        next preparedTail tailSuccess =>
          cases success
          let preparedHead :=
            CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic
              head within.head owner depth rootDiameter rootDiameterPositive
                headSuccess
          simpa only [ofPreparedPath, dataOfCompleteSegment_parents] using
            allParentsProper_append
              (ofTryDyadic_allParentsProper curve differential head
                within.head owner sheet depth rootDiameter
                  rootDiameterPositive headSuccess)
              (inductionHypothesis within.tail preparedHead.finishOwner
                preparedTail tailSuccess)

/-- The prepared-path cache underlying a checked common-depth path has
positive-width parents.  Keeping this proof separate lets the executable
centred state reuse `ofPreparedPath` instead of maintaining a second
dependent recursion over the same checked data. -/
theorem ofCheckedDyadic_prepared_allParentsProper {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (checked :
      CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic depth
        rootDiameter rootDiameterPositive path owner) :
    CCL.Riemann.PreparedDyadicRefinements.AllParentsProper
      ((ofPreparedPath curve differential sheet checked.prepared).parents) := by
  induction checked with
  | nil =>
      simp only [CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath]
      trivial
  | cons head tail owner headWithin headSafe remaining inductionHypothesis =>
      simp only [CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath]
      simpa only [dataOfCompleteSegment_parents] using
        (allParentsProper_append
          (ofSafeDyadic_allParentsProper curve differential head headWithin
            owner sheet depth rootDiameter rootDiameterPositive headSafe)
          inductionHypothesis)

/-- Construct the centered state of every segment in one checked common-depth
path from the single prepared-path cache, attaching its independently proved
positive-width invariant. -/
def ofCheckedDyadic {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (checked :
      CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic depth
        rootDiameter rootDiameterPositive path owner) :
    CheckedDyadicCenteredState curve differential sheet start finish :=
  let data := ofPreparedPath curve differential sheet checked.prepared
  { parents := data.parents
    proper := ofCheckedDyadic_prepared_allParentsProper curve differential
      sheet checked
    chain := data.chain }

@[simp] theorem ofCheckedDyadic_parents_length {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (checked :
      CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic depth
        rootDiameter rootDiameterPositive path owner) :
    (ofCheckedDyadic curve differential sheet checked).parents.length =
      checked.prepared.stepCount := by
  unfold ofCheckedDyadic
  exact ofPreparedPath_parents_length curve differential sheet checked.prepared

/-- Every centred edge rebuilt from an exact executed segment certificate has
strictly positive parameter width. -/
theorem ofExecutedDyadic_allParentsProper {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      CCL.Riemann.PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
        segment within CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint
            (CCL.Riemann.PreparedClearPathModels.ownerAtStart segment owner)
              depth rootDiameter rootDiameterPositive) :
    CCL.Riemann.PreparedDyadicRefinements.AllParentsProper
      ((CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofExecutedDyadic
        segment within owner depth rootDiameter rootDiameterPositive
          safe).centeredEdges curve differential sheet) := by
  apply allParentsProper_of_parameterEdgesProper
  rw [CCL.Riemann.PreparedClearPathModels.CompleteSegment.centeredEdges_parameterEdges,
    CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofExecutedDyadic_parameterEdges]
  exact dyadicEdges_allParameterEdgesProper depth
    CCL.Riemann.PreparedClearPathModels.zeroEndpoint
    CCL.Riemann.PreparedClearPathModels.oneEndpoint (by decide)

/-- Construct the centred integration state from a compact exact executed
path certificate. -/
def ofExecutedCheckedDyadic {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (checked :
      CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic
        depth rootDiameter rootDiameterPositive path owner) :
    CheckedDyadicCenteredState curve differential sheet start finish :=
  match checked with
  | .nil point _owner =>
      { parents := []
        proper := trivial
        chain := .nil _ }
  | .cons head _tail owner headWithin headSafe remaining =>
      let preparedHead :=
        CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofExecutedDyadic
          head headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofExecutedCheckedDyadic curve differential sheet
        remaining
      { parents :=
          preparedHead.centeredEdges curve differential sheet ++
            tailState.parents
        proper :=
          allParentsProper_append
            (ofExecutedDyadic_allParentsProper curve differential head
              headWithin owner sheet depth rootDiameter rootDiameterPositive
                headSafe)
            tailState.proper
        chain :=
          (ofCompleteSegment curve differential sheet preparedHead).append
            tailState.chain }
  termination_by structural checked

/-- The compact executed-certificate presentation extracts exactly the same
centred parents as its retained prepared path.  This equality keeps later
theorem-facing folds independent of which successful bank representation was
used at runtime. -/
theorem ofExecutedCheckedDyadic_parents_eq_ofPreparedPath {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic
          depth rootDiameter rootDiameterPositive path owner),
      (ofExecutedCheckedDyadic curve differential sheet checked).parents =
        (ofPreparedPath curve differential sheet checked.prepared).parents
  | _, _, _, _, _, .nil point owner => rfl
  | _, _, _, _, _, .cons head tail owner headWithin headSafe remaining => by
      simp only [ofExecutedCheckedDyadic,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared,
        ofPreparedPath]
      rw [dataOfCompleteSegment_parents,
        ofExecutedCheckedDyadic_parents_eq_ofPreparedPath curve differential
          sheet remaining]

private theorem completeSegment_centeredEdges_length {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2)
    (prepared :
      CCL.Riemann.PreparedClearPathModels.CompleteSegment segment within owner) :
    (prepared.centeredEdges curve differential sheet).length =
      prepared.subdivision.stepCount := by
  unfold CCL.Riemann.PreparedClearPathModels.CompleteSegment.centeredEdges
  exact centeredEdges_length_eq_stepCount curve differential sheet
    prepared.subdivision _

private theorem canonicalCenteredEdges_recast_self {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision :
      CCL.Riemann.PreparedSheetContinuation.Subdivision segment within left
        owner),
      (CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
          sheet subdivision
            (CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates curve
              differential sheet subdivision)).map
          (recastCenteredEdge differential) =
        CCL.Riemann.PreparedSubdivisionModels.centeredEdges curve differential
          sheet subdivision
            (CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates curve
              differential sheet subdivision)
  | .stop _ _ => rfl
  | .next _ _ _ _ _ _ remaining => by
      simp only [CCL.Riemann.PreparedSubdivisionModels.centeredEdges,
        CCL.Riemann.PreparedSubdivisionModels.canonicalCenterStates,
        List.map_cons, recastCenteredEdge]
      rw [recastPreparedEdge_self]
      rw [canonicalCenteredEdges_recast_self curve differential sheet
        remaining]

private theorem completeSegment_centeredEdges_recast_self {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2)
    (prepared :
      CCL.Riemann.PreparedClearPathModels.CompleteSegment segment within owner) :
    (prepared.centeredEdges curve differential sheet).map
        (recastCenteredEdge differential) =
      prepared.centeredEdges curve differential sheet := by
  unfold CCL.Riemann.PreparedClearPathModels.CompleteSegment.centeredEdges
  exact canonicalCenteredEdges_recast_self curve differential sheet
    prepared.subdivision

theorem ofPreparedPath_recast_self {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner),
      (ofPreparedPath curve differential sheet prepared).parents.map
          (recastCenteredEdge differential) =
        (ofPreparedPath curve differential sheet prepared).parents
  | _, _, _, _, _, .nil point owner => by
      simp only [ofPreparedPath, List.map_nil]
  | _, _, _, _, _, .cons head tail owner headWithin preparedHead
      preparedTail => by
      simp only [ofPreparedPath, List.map_append]
      rw [dataOfCompleteSegment_parents,
        completeSegment_centeredEdges_recast_self curve differential sheet
          preparedHead,
        ofPreparedPath_recast_self curve differential sheet preparedTail]

/-- A successful common-depth checker proves that every edge of the already
centred prepared path has positive width. -/
theorem ofPreparedPath_allParentsProper_ofTryDyadic {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      (path : ClearPath curve.polynomial ambient start finish)
      (within : path.WithinAmbient)
      (owner : Owner (curve.polynomial.eval start))
      {prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner},
      CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic path within
          owner depth rootDiameter rootDiameterPositive = some prepared ->
        CCL.Riemann.PreparedDyadicRefinements.AllParentsProper
          (ofPreparedPath curve differential sheet prepared).parents := by
  intro ambient start finish path within owner prepared success
  exact ofPreparedPath_allParentsProper_of_tryDyadic curve differential sheet
    depth rootDiameter rootDiameterPositive path within owner prepared success

/-- Construct the centred state directly from one successful executable
whole-path check.  The retained parents and chain depend only on the returned
prepared path; the success proof supplies strict dyadic widths. -/
def ofTryDyadic {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (path : ClearPath curve.polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    {prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner}
    (success : CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic path
      within owner depth rootDiameter rootDiameterPositive = some prepared) :
    CheckedDyadicCenteredState curve differential sheet start finish :=
  let centered := ofPreparedPath curve differential sheet prepared
  { parents := centered.parents
    proper := ofPreparedPath_allParentsProper_ofTryDyadic curve differential
      sheet depth rootDiameter rootDiameterPositive path within owner success
    chain := centered.chain }

/-- Sum of compact segment-level total-weight bounds for a common-depth
prepared path.  This expression traverses only the original clear path, not
its accepted dyadic leaves. -/
def dyadicPathTotalWeightedBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    (rootDiameter : Coordinate) (depth : Nat)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (path : ClearPath curve.polynomial ambient start finish) : Coordinate :=
  match path with
  | .nil _point => 0
  | .cons head tail =>
      completeDyadicTotalWeightedBound differential head rootDiameter depth +
        dyadicPathTotalWeightedBound differential rootDiameter depth tail
  termination_by structural path

/-- Owner-independent total-weight preflight bound with one fixed dyadic
denominator for every original clear segment. -/
def dyadicPathTotalWeightedDyadicBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    (rootDiameter : Coordinate) (depth : Nat)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (path : ClearPath curve.polynomial ambient start finish) : Coordinate :=
  match path with
  | .nil _point => 0
  | .cons head tail =>
      completeDyadicTotalWeightedDyadicBound differential head rootDiameter
          depth +
        dyadicPathTotalWeightedDyadicBound differential rootDiameter depth tail
  termination_by structural path

theorem dyadicPathTotalWeightedBound_le_dyadicBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {rootDiameter : Coordinate} (rootDiameterNonnegative : 0 <= rootDiameter)
    (depth : Nat) {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (path : ClearPath curve.polynomial ambient start finish) :
    dyadicPathTotalWeightedBound differential rootDiameter depth path <=
      dyadicPathTotalWeightedDyadicBound differential rootDiameter depth
        path := by
  induction path with
  | nil point => exact le_rfl
  | cons head tail inductionHypothesis =>
      unfold dyadicPathTotalWeightedBound
        dyadicPathTotalWeightedDyadicBound
      exact add_le_add
        (completeDyadicTotalWeightedBound_le_dyadicBound differential head
          rootDiameterNonnegative depth)
        inductionHypothesis

/-- Owner-independent, segmentwise-rounded initial-sample bound for a
common-depth path.  It folds only the original clear segments. -/
def dyadicPathIntegralNormSqCeilBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    (rootDiameter : Coordinate) (depth : Nat)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (path : ClearPath curve.polynomial ambient start finish) : Coordinate :=
  match path with
  | .nil _point => 0
  | .cons head tail =>
      completeDyadicIntegralNormSqCeilBound differential head rootDiameter
          depth +
        dyadicPathIntegralNormSqCeilBound differential rootDiameter depth tail
  termination_by structural path

/-- Sum of actual-root compact bounds over a retained prepared path.  Unlike
`dyadicPathTotalWeightedBound`, this traverses the accepted subdivisions, but
only to take maxima of their cached root-box diagonals. -/
def preparedPathTotalWeightedBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus) (depth : Nat)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner) :
    Coordinate :=
  match prepared with
  | .nil _point _owner => 0
  | .cons head _tail owner headWithin preparedHead preparedTail =>
      completePreparedDyadicTotalWeightedBound differential head headWithin
          owner preparedHead depth +
        preparedPathTotalWeightedBound differential depth preparedTail

/-- Segmentwise dyadic upper sum used by executable preflight. -/
def preparedPathTotalWeightedDyadicBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus) (depth : Nat)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner) :
    Coordinate :=
  match prepared with
  | .nil _point _owner => 0
  | .cons head _tail owner headWithin preparedHead preparedTail =>
      completePreparedDyadicTotalWeightedDyadicBound differential head
          headWithin owner preparedHead depth +
        preparedPathTotalWeightedDyadicBound differential depth preparedTail

theorem preparedPathTotalWeightedBound_le_dyadicBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus) (depth : Nat)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner) :
    preparedPathTotalWeightedBound differential depth prepared <=
      preparedPathTotalWeightedDyadicBound differential depth prepared := by
  induction prepared with
  | nil point owner => exact le_rfl
  | cons head tail owner headWithin preparedHead preparedTail
      inductionHypothesis =>
      unfold preparedPathTotalWeightedBound
        preparedPathTotalWeightedDyadicBound
      exact add_le_add
        (completePreparedDyadicTotalWeightedBound_le_dyadicBound differential
          head headWithin owner preparedHead depth)
        inductionHypothesis

/-- Additive squared-sample bound over a retained prepared path.  Each
segment contributes one compact coefficient bound and one cached root-box
maximum, without evaluating any persisted centre. -/
def preparedPathIntegralNormSqSumBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus) (depth : Nat)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner) :
    Coordinate :=
  match prepared with
  | .nil _point _owner => 0
  | .cons head _tail owner headWithin preparedHead preparedTail =>
      completePreparedDyadicIntegralNormSqSumBound differential head headWithin
          owner preparedHead depth +
        preparedPathIntegralNormSqSumBound differential depth preparedTail

/-- Segmentwise-rounded squared-sample bound.  Every recursive addition is
between denominator-one canonical fractions, avoiding denominator growth
across a long prepared path. -/
def preparedPathIntegralNormSqCeilBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus) (depth : Nat)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner) :
    Coordinate :=
  match prepared with
  | .nil _point _owner => 0
  | .cons head _tail owner headWithin preparedHead preparedTail =>
      completePreparedDyadicIntegralNormSqCeilBound differential head
          headWithin owner preparedHead depth +
        preparedPathIntegralNormSqCeilBound differential depth preparedTail

theorem preparedPathIntegralNormSqSumBound_le_ceilBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus) (depth : Nat)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner) :
    preparedPathIntegralNormSqSumBound differential depth prepared <=
      preparedPathIntegralNormSqCeilBound differential depth prepared := by
  induction prepared with
  | nil point owner => exact le_rfl
  | cons head tail owner headWithin preparedHead preparedTail
      inductionHypothesis =>
      unfold preparedPathIntegralNormSqSumBound
        preparedPathIntegralNormSqCeilBound
      exact add_le_add
        (completePreparedDyadicIntegralNormSqSumBound_le_ceilBound differential
          head headWithin owner preparedHead depth)
        inductionHypothesis

/-- One structural fold computing both compact prepared-path summaries. -/
structure PreparedPathPreflightBounds where
  totalWeighted : Coordinate
  integralNormSqSum : Coordinate

def preparedPathPreflightBounds {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus) (depth : Nat)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner) :
    PreparedPathPreflightBounds :=
  match prepared with
  | .nil _point _owner =>
      { totalWeighted := 0
        integralNormSqSum := 0 }
  | .cons head _tail owner headWithin preparedHead preparedTail =>
      let headBounds := completePreparedDyadicPreflightBounds differential head
        headWithin owner preparedHead depth
      let tailBounds := preparedPathPreflightBounds differential depth
        preparedTail
      { totalWeighted :=
          headBounds.totalWeighted + tailBounds.totalWeighted
        integralNormSqSum :=
          headBounds.integralNormSqSum + tailBounds.integralNormSqSum }

@[simp] theorem preparedPathPreflightBounds_totalWeighted {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus) (depth : Nat)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner) :
    (preparedPathPreflightBounds differential depth prepared).totalWeighted =
      preparedPathTotalWeightedDyadicBound differential depth prepared := by
  induction prepared with
  | nil point owner => rfl
  | cons head tail owner headWithin preparedHead preparedTail
      inductionHypothesis =>
      unfold preparedPathPreflightBounds preparedPathTotalWeightedDyadicBound
      change
        (completePreparedDyadicPreflightBounds differential head headWithin
            owner preparedHead depth).totalWeighted +
          (preparedPathPreflightBounds differential depth
            preparedTail).totalWeighted = _
      rw [completePreparedDyadicPreflightBounds_totalWeighted,
        inductionHypothesis]

@[simp] theorem preparedPathPreflightBounds_integralNormSqSum {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus) (depth : Nat)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner) :
    (preparedPathPreflightBounds differential depth prepared).integralNormSqSum =
      preparedPathIntegralNormSqCeilBound differential depth prepared := by
  induction prepared with
  | nil point owner => rfl
  | cons head tail owner headWithin preparedHead preparedTail
      inductionHypothesis =>
      unfold preparedPathPreflightBounds preparedPathIntegralNormSqCeilBound
      change
        (completePreparedDyadicPreflightBounds differential head headWithin
            owner preparedHead depth).integralNormSqSum +
          (preparedPathPreflightBounds differential depth
            preparedTail).integralNormSqSum = _
      rw [completePreparedDyadicPreflightBounds_integralNormSqSum,
        inductionHypothesis]

/-- A successful whole-path checker inherits the compact additive bound for
the squared norms of its actual initial cell samples. -/
theorem ofTryDyadic_preparedIntegralNormSqSum_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      (path : ClearPath curve.polynomial ambient start finish)
      (within : path.WithinAmbient)
      (owner : Owner (curve.polynomial.eval start))
      {prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner}
      (success :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic path within
            owner depth rootDiameter rootDiameterPositive = some prepared),
      RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
          ((ofTryDyadic curve differential sheet depth rootDiameter
            rootDiameterPositive path within owner success).parents.map
              fun parent => parent.model.integralSample) <=
        preparedPathIntegralNormSqSumBound differential depth prepared
  | _, _, _, .nil point, _within, owner, _prepared, success => by
      simp only
        [CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic] at success
      have preparedEqual := Option.some.inj success
      subst _prepared
      simp only [ofTryDyadic, ofPreparedPath,
        preparedPathIntegralNormSqSumBound, List.map_nil,
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum]
      exact le_rfl
  | _, _, _, .cons head tail, within, owner, _prepared, success => by
      rw [CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic] at success
      split at success
      next => contradiction
      next subdivision headSuccess =>
        simp only at success
        split at success
        next => contradiction
        next preparedTail tailSuccess =>
          have preparedEqual := Option.some.inj success
          subst _prepared
          let preparedHead :=
            CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic
              head within.head owner depth rootDiameter rootDiameterPositive
                headSuccess
          let tailCentered := ofPreparedPath curve differential sheet
            preparedTail
          simp only [ofTryDyadic, ofPreparedPath,
            preparedPathIntegralNormSqSumBound]
          rw [dataOfCompleteSegment_parents]
          change
            RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
                ((preparedHead.centeredEdges curve differential sheet ++
                  tailCentered.parents).map
                    fun parent => parent.model.integralSample) <=
              completePreparedDyadicIntegralNormSqSumBound differential head
                  within.head owner preparedHead depth +
                preparedPathIntegralNormSqSumBound differential depth
                  preparedTail
          rw [List.map_append, gaussianNormSqSum_append]
          exact add_le_add
            (completeSegmentOfTryDyadic_preparedIntegralNormSqSum_le curve
              differential head within.head owner sheet depth rootDiameter
                rootDiameterPositive headSuccess)
            (ofTryDyadic_preparedIntegralNormSqSum_le curve differential sheet
              depth rootDiameter rootDiameterPositive tail within.tail
                preparedHead.finishOwner tailSuccess)

/-- A successful whole-path checker inherits the sharper compact sum carried
by its returned prepared path. -/
theorem ofTryDyadic_preparedTotalWeightedAllowance_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      (path : ClearPath curve.polynomial ambient start finish)
      (within : path.WithinAmbient)
      (owner : Owner (curve.polynomial.eval start))
      {prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner}
      (success :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic path within
            owner depth rootDiameter rootDiameterPositive = some prepared),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((ofTryDyadic curve differential sheet depth rootDiameter
          rootDiameterPositive path within owner success).parents.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
        preparedPathTotalWeightedBound differential depth prepared
  | _, _, _, .nil point, _within, owner, _prepared, success => by
      simp only
        [CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic] at success
      have preparedEqual := Option.some.inj success
      subst _prepared
      simp only [ofTryDyadic, ofPreparedPath,
        preparedPathTotalWeightedBound,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.map_nil, List.foldr_nil]
      exact le_rfl
  | _, _, _, .cons head tail, within, owner, _prepared, success => by
      rw [CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic] at success
      split at success
      next => contradiction
      next subdivision headSuccess =>
        simp only at success
        split at success
        next => contradiction
        next preparedTail tailSuccess =>
          have preparedEqual := Option.some.inj success
          subst _prepared
          let preparedHead :=
            CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic
              head within.head owner depth rootDiameter rootDiameterPositive
                headSuccess
          let tailCentered := ofPreparedPath curve differential sheet
            preparedTail
          simp only [ofTryDyadic, ofPreparedPath,
            preparedPathTotalWeightedBound]
          rw [dataOfCompleteSegment_parents]
          change
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              ((preparedHead.centeredEdges curve differential sheet ++
                tailCentered.parents).map
                  CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
              completePreparedDyadicTotalWeightedBound differential head
                  within.head owner preparedHead depth +
                preparedPathTotalWeightedBound differential depth preparedTail
          rw [List.map_append, totalWeightedAllowance_append]
          exact add_le_add
            (completeSegmentOfTryDyadic_preparedTotalWeightedAllowance_le curve
              differential head within.head owner sheet depth rootDiameter
                rootDiameterPositive headSuccess)
            (ofTryDyadic_preparedTotalWeightedAllowance_le curve differential
              sheet depth rootDiameter rootDiameterPositive tail within.tail
                preparedHead.finishOwner tailSuccess)

/-- A successful whole-path checker inherits the compact sum of its original
segments' bounds. -/
theorem ofTryDyadic_totalWeightedAllowance_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      (path : ClearPath curve.polynomial ambient start finish)
      (within : path.WithinAmbient)
      (owner : Owner (curve.polynomial.eval start))
      {prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner}
      (success :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic path within
            owner depth rootDiameter rootDiameterPositive = some prepared),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((ofTryDyadic curve differential sheet depth rootDiameter
          rootDiameterPositive path within owner success).parents.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
        dyadicPathTotalWeightedBound differential rootDiameter depth path
  | _, _, _, .nil point, _within, owner, _prepared, success => by
      simp only
        [CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic] at success
      have preparedEqual := Option.some.inj success
      subst _prepared
      simp only [ofTryDyadic, ofPreparedPath, dyadicPathTotalWeightedBound,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.map_nil, List.foldr_nil]
      exact le_rfl
  | _, _, _, .cons head tail, within, owner, _prepared, success => by
      rw [CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic] at success
      split at success
      next => contradiction
      next subdivision headSuccess =>
        simp only at success
        split at success
        next => contradiction
        next preparedTail tailSuccess =>
          have preparedEqual := Option.some.inj success
          subst _prepared
          let preparedHead :=
            CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic
              head within.head owner depth rootDiameter rootDiameterPositive
                headSuccess
          let tailCentered := ofPreparedPath curve differential sheet
            preparedTail
          simp only [ofTryDyadic, ofPreparedPath,
            dyadicPathTotalWeightedBound]
          rw [dataOfCompleteSegment_parents]
          change
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              ((preparedHead.centeredEdges curve differential sheet ++
                tailCentered.parents).map
                  CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
              completeDyadicTotalWeightedBound differential head rootDiameter
                  depth +
                dyadicPathTotalWeightedBound differential rootDiameter depth
                  tail
          rw [List.map_append, totalWeightedAllowance_append]
          exact add_le_add
            (completeSegmentOfTryDyadic_totalWeightedAllowance_le curve
              differential head within.head owner sheet depth rootDiameter
                rootDiameterPositive headSuccess)
            (ofTryDyadic_totalWeightedAllowance_le curve differential sheet
              depth rootDiameter rootDiameterPositive tail within.tail
                preparedHead.finishOwner tailSuccess)

theorem ofCheckedDyadic_totalWeightedAllowance_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic depth
          rootDiameter rootDiameterPositive path owner),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((ofCheckedDyadic curve differential sheet checked).parents.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
        dyadicPathTotalWeightedBound differential rootDiameter depth path
  | _, _, _, _, _, .nil point owner => by
      simp only [ofCheckedDyadic,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath, dyadicPathTotalWeightedBound, List.map_nil,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_nil]
      exact le_rfl
  | _, _, _, _, _, .cons head tail owner headWithin headSafe remaining => by
      let preparedHead :=
        CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofSafeDyadic head
          headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofCheckedDyadic curve differential sheet remaining
      simp only [ofCheckedDyadic,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath, dataOfCompleteSegment_parents,
        dyadicPathTotalWeightedBound]
      change
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((preparedHead.centeredEdges curve differential sheet ++
            tailState.parents).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
          completeDyadicTotalWeightedBound differential head rootDiameter
              depth +
            dyadicPathTotalWeightedBound differential rootDiameter depth tail
      rw [List.map_append, totalWeightedAllowance_append]
      exact add_le_add
        (completeSegmentOfTryDyadic_totalWeightedAllowance_le curve
          differential head headWithin owner sheet depth rootDiameter
            rootDiameterPositive _)
        (ofCheckedDyadic_totalWeightedAllowance_le curve differential sheet
          remaining)

theorem ofExecutedCheckedDyadic_totalWeightedAllowance_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic
          depth rootDiameter rootDiameterPositive path owner),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((ofExecutedCheckedDyadic curve differential sheet checked).parents.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
        dyadicPathTotalWeightedBound differential rootDiameter depth path
  | _, _, _, _, _, .nil point owner => by
      simp only [ofExecutedCheckedDyadic, dyadicPathTotalWeightedBound,
        List.map_nil,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_nil]
      exact le_rfl
  | _, _, _, _, _, .cons head tail owner headWithin headSafe remaining => by
      let preparedHead :=
        CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofExecutedDyadic
          head headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofExecutedCheckedDyadic curve differential sheet
        remaining
      simp only [ofExecutedCheckedDyadic, dyadicPathTotalWeightedBound]
      change
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((preparedHead.centeredEdges curve differential sheet ++
            tailState.parents).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
          completeDyadicTotalWeightedBound differential head rootDiameter
              depth +
            dyadicPathTotalWeightedBound differential rootDiameter depth tail
      rw [List.map_append, totalWeightedAllowance_append]
      exact add_le_add
        (completeSegmentOfTryDyadic_totalWeightedAllowance_le curve
          differential head headWithin owner sheet depth rootDiameter
            rootDiameterPositive _)
        (ofExecutedCheckedDyadic_totalWeightedAllowance_le curve differential
          sheet remaining)

/-- A successful whole-path checker inherits the owner-independent rounded
sample bound of its original segments. -/
theorem ofTryDyadic_integralNormSqSum_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      (path : ClearPath curve.polynomial ambient start finish)
      (within : path.WithinAmbient)
      (owner : Owner (curve.polynomial.eval start))
      {prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner}
      (success :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic path within
            owner depth rootDiameter rootDiameterPositive = some prepared),
      RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
          ((ofTryDyadic curve differential sheet depth rootDiameter
            rootDiameterPositive path within owner success).parents.map
              fun parent => parent.model.integralSample) <=
        dyadicPathIntegralNormSqCeilBound differential rootDiameter depth path
  | _, _, _, .nil point, _within, owner, _prepared, success => by
      simp only
        [CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic] at success
      have preparedEqual := Option.some.inj success
      subst _prepared
      simp only [ofTryDyadic, ofPreparedPath,
        dyadicPathIntegralNormSqCeilBound, List.map_nil,
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum]
      exact le_rfl
  | _, _, _, .cons head tail, within, owner, _prepared, success => by
      rw [CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic] at success
      split at success
      next => contradiction
      next subdivision headSuccess =>
        simp only at success
        split at success
        next => contradiction
        next preparedTail tailSuccess =>
          have preparedEqual := Option.some.inj success
          subst _prepared
          let preparedHead :=
            CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofTryDyadic
              head within.head owner depth rootDiameter rootDiameterPositive
                headSuccess
          let tailCentered := ofPreparedPath curve differential sheet
            preparedTail
          simp only [ofTryDyadic, ofPreparedPath,
            dyadicPathIntegralNormSqCeilBound]
          rw [dataOfCompleteSegment_parents]
          change
            RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
                ((preparedHead.centeredEdges curve differential sheet ++
                  tailCentered.parents).map
                    fun parent => parent.model.integralSample) <=
              completeDyadicIntegralNormSqCeilBound differential head
                  rootDiameter depth +
                dyadicPathIntegralNormSqCeilBound differential rootDiameter
                  depth tail
          rw [List.map_append, gaussianNormSqSum_append]
          exact add_le_add
            ((completeSegmentOfTryDyadic_integralNormSqSum_le curve
              differential head within.head owner sheet depth rootDiameter
                rootDiameterPositive headSuccess).trans
              (completeDyadicIntegralNormSqSumBound_le_ceilBound differential
                head rootDiameterPositive.le depth))
            (ofTryDyadic_integralNormSqSum_le curve differential sheet depth
              rootDiameter rootDiameterPositive tail within.tail
                preparedHead.finishOwner tailSuccess)

theorem ofCheckedDyadic_integralNormSqSum_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic depth
          rootDiameter rootDiameterPositive path owner),
      RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
          ((ofCheckedDyadic curve differential sheet checked).parents.map
            fun parent => parent.model.integralSample) <=
        dyadicPathIntegralNormSqCeilBound differential rootDiameter depth path
  | _, _, _, _, _, .nil point owner => by
      simp only [ofCheckedDyadic,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath, dyadicPathIntegralNormSqCeilBound, List.map_nil,
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum]
      exact le_rfl
  | _, _, _, _, _, .cons head tail owner headWithin headSafe remaining => by
      let preparedHead :=
        CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofSafeDyadic head
          headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofCheckedDyadic curve differential sheet remaining
      simp only [ofCheckedDyadic,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath, dataOfCompleteSegment_parents,
        dyadicPathIntegralNormSqCeilBound]
      change
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
            ((preparedHead.centeredEdges curve differential sheet ++
              tailState.parents).map
                fun parent => parent.model.integralSample) <=
          completeDyadicIntegralNormSqCeilBound differential head rootDiameter
              depth +
            dyadicPathIntegralNormSqCeilBound differential rootDiameter depth
              tail
      rw [List.map_append, gaussianNormSqSum_append]
      exact add_le_add
        ((completeSegmentOfTryDyadic_integralNormSqSum_le curve differential
          head headWithin owner sheet depth rootDiameter rootDiameterPositive
            _).trans
          (completeDyadicIntegralNormSqSumBound_le_ceilBound differential head
            rootDiameterPositive.le depth))
        (ofCheckedDyadic_integralNormSqSum_le curve differential sheet
          remaining)

theorem ofExecutedCheckedDyadic_integralNormSqSum_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic
          depth rootDiameter rootDiameterPositive path owner),
      RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
          ((ofExecutedCheckedDyadic curve differential sheet checked).parents.map
            fun parent => parent.model.integralSample) <=
        dyadicPathIntegralNormSqCeilBound differential rootDiameter depth path
  | _, _, _, _, _, .nil point owner => by
      simp only [ofExecutedCheckedDyadic, dyadicPathIntegralNormSqCeilBound,
        List.map_nil, RFAP.ConstructiveFiniteNorm.gaussianNormSqSum]
      exact le_rfl
  | _, _, _, _, _, .cons head tail owner headWithin headSafe remaining => by
      let preparedHead :=
        CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofExecutedDyadic
          head headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofExecutedCheckedDyadic curve differential sheet
        remaining
      simp only [ofExecutedCheckedDyadic, dyadicPathIntegralNormSqCeilBound]
      change
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
            ((preparedHead.centeredEdges curve differential sheet ++
              tailState.parents).map
                fun parent => parent.model.integralSample) <=
          completeDyadicIntegralNormSqCeilBound differential head rootDiameter
              depth +
            dyadicPathIntegralNormSqCeilBound differential rootDiameter depth
              tail
      rw [List.map_append, gaussianNormSqSum_append]
      exact add_le_add
        ((completeSegmentOfTryDyadic_integralNormSqSum_le curve differential
          head headWithin owner sheet depth rootDiameter rootDiameterPositive
            _).trans
          (completeDyadicIntegralNormSqSumBound_le_ceilBound differential head
            rootDiameterPositive.le depth))
        (ofExecutedCheckedDyadic_integralNormSqSum_le curve differential sheet
          remaining)

theorem ofCheckedDyadic_preparedTotalWeightedAllowance_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic depth
          rootDiameter rootDiameterPositive path owner),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((ofCheckedDyadic curve differential sheet checked).parents.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
        preparedPathTotalWeightedBound differential depth checked.prepared
  | _, _, _, _, _, .nil point owner => by
      simp only [ofCheckedDyadic,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath, preparedPathTotalWeightedBound, List.map_nil,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_nil]
      exact le_rfl
  | _, _, _, _, _, .cons head tail owner headWithin headSafe remaining => by
      let preparedHead :=
        CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofSafeDyadic head
          headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofCheckedDyadic curve differential sheet remaining
      simp only [ofCheckedDyadic,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath, dataOfCompleteSegment_parents,
        preparedPathTotalWeightedBound]
      change
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((preparedHead.centeredEdges curve differential sheet ++
            tailState.parents).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
          completePreparedDyadicTotalWeightedBound differential head headWithin
              owner preparedHead depth +
            preparedPathTotalWeightedBound differential depth
              remaining.prepared
      rw [List.map_append, totalWeightedAllowance_append]
      exact add_le_add
        (completeSegmentOfTryDyadic_preparedTotalWeightedAllowance_le curve
          differential head headWithin owner sheet depth rootDiameter
            rootDiameterPositive _)
        (ofCheckedDyadic_preparedTotalWeightedAllowance_le curve differential
          sheet remaining)

theorem ofExecutedCheckedDyadic_preparedTotalWeightedAllowance_le
    {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic
          depth rootDiameter rootDiameterPositive path owner),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((ofExecutedCheckedDyadic curve differential sheet checked).parents.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
        preparedPathTotalWeightedBound differential depth checked.prepared
  | _, _, _, _, _, .nil point owner => by
      simp only [ofExecutedCheckedDyadic,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared,
        preparedPathTotalWeightedBound, List.map_nil,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_nil]
      exact le_rfl
  | _, _, _, _, _, .cons head tail owner headWithin headSafe remaining => by
      let preparedHead :=
        CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofExecutedDyadic
          head headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofExecutedCheckedDyadic curve differential sheet
        remaining
      simp only [ofExecutedCheckedDyadic,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared,
        preparedPathTotalWeightedBound]
      change
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((preparedHead.centeredEdges curve differential sheet ++
            tailState.parents).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
          completePreparedDyadicTotalWeightedBound differential head headWithin
              owner preparedHead depth +
            preparedPathTotalWeightedBound differential depth
              remaining.prepared
      rw [List.map_append, totalWeightedAllowance_append]
      exact add_le_add
        (completeSegmentOfTryDyadic_preparedTotalWeightedAllowance_le curve
          differential head headWithin owner sheet depth rootDiameter
            rootDiameterPositive _)
        (ofExecutedCheckedDyadic_preparedTotalWeightedAllowance_le curve
          differential sheet remaining)

theorem ofCheckedDyadic_preparedIntegralNormSqSum_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic depth
          rootDiameter rootDiameterPositive path owner),
      RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
          ((ofCheckedDyadic curve differential sheet checked).parents.map
            fun parent => parent.model.integralSample) <=
        preparedPathIntegralNormSqSumBound differential depth checked.prepared
  | _, _, _, _, _, .nil point owner => by
      simp only [ofCheckedDyadic,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath, preparedPathIntegralNormSqSumBound, List.map_nil,
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum]
      exact le_rfl
  | _, _, _, _, _, .cons head tail owner headWithin headSafe remaining => by
      let preparedHead :=
        CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofSafeDyadic head
          headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofCheckedDyadic curve differential sheet remaining
      simp only [ofCheckedDyadic,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath, dataOfCompleteSegment_parents,
        preparedPathIntegralNormSqSumBound]
      change
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
            ((preparedHead.centeredEdges curve differential sheet ++
              tailState.parents).map
                fun parent => parent.model.integralSample) <=
          completePreparedDyadicIntegralNormSqSumBound differential head
              headWithin owner preparedHead depth +
            preparedPathIntegralNormSqSumBound differential depth
              remaining.prepared
      rw [List.map_append, gaussianNormSqSum_append]
      exact add_le_add
        (completeSegmentOfTryDyadic_preparedIntegralNormSqSum_le curve
          differential head headWithin owner sheet depth rootDiameter
            rootDiameterPositive _)
        (ofCheckedDyadic_preparedIntegralNormSqSum_le curve differential sheet
          remaining)

theorem ofExecutedCheckedDyadic_preparedIntegralNormSqSum_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic
          depth rootDiameter rootDiameterPositive path owner),
      RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
          ((ofExecutedCheckedDyadic curve differential sheet checked).parents.map
            fun parent => parent.model.integralSample) <=
        preparedPathIntegralNormSqSumBound differential depth checked.prepared
  | _, _, _, _, _, .nil point owner => by
      simp only [ofExecutedCheckedDyadic,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared,
        preparedPathIntegralNormSqSumBound, List.map_nil,
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum]
      exact le_rfl
  | _, _, _, _, _, .cons head tail owner headWithin headSafe remaining => by
      let preparedHead :=
        CCL.Riemann.PreparedClearPathModels.CompleteSegment.ofExecutedDyadic
          head headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofExecutedCheckedDyadic curve differential sheet
        remaining
      simp only [ofExecutedCheckedDyadic,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared,
        preparedPathIntegralNormSqSumBound]
      change
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
            ((preparedHead.centeredEdges curve differential sheet ++
              tailState.parents).map
                fun parent => parent.model.integralSample) <=
          completePreparedDyadicIntegralNormSqSumBound differential head
              headWithin owner preparedHead depth +
            preparedPathIntegralNormSqSumBound differential depth
              remaining.prepared
      rw [List.map_append, gaussianNormSqSum_append]
      exact add_le_add
        (completeSegmentOfTryDyadic_preparedIntegralNormSqSum_le curve
          differential head headWithin owner sheet depth rootDiameter
            rootDiameterPositive _)
        (ofExecutedCheckedDyadic_preparedIntegralNormSqSum_le curve differential
          sheet remaining)

/-- A retained prepared path with exact canonical request lists satisfies the
same owner-independent total-weight bound as a freshly checked dyadic path. -/
theorem ofPreparedPath_totalWeightedAllowance_le_of_allRequestsDyadic
    {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner),
      CCL.Riemann.PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive prepared ->
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((ofPreparedPath curve differential sheet prepared).parents.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
          dyadicPathTotalWeightedBound differential rootDiameter depth path
  | _, _, _, _, _, .nil point owner, _generated => by
      simp only [ofPreparedPath, dyadicPathTotalWeightedBound, List.map_nil,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_nil]
      exact le_rfl
  | _, _, _, _, _, .cons head tail owner headWithin preparedHead preparedTail,
      generated => by
      change preparedHead.subdivision.requests =
          CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint
              CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
                rootDiameterPositive ∧
        CCL.Riemann.PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive preparedTail at generated
      let tailState := ofPreparedPath curve differential sheet preparedTail
      simp only [ofPreparedPath, dataOfCompleteSegment_parents,
        dyadicPathTotalWeightedBound]
      change
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((preparedHead.centeredEdges curve differential sheet ++
            tailState.parents).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
          completeDyadicTotalWeightedBound differential head rootDiameter
              depth +
            dyadicPathTotalWeightedBound differential rootDiameter depth tail
      rw [List.map_append, totalWeightedAllowance_append]
      exact add_le_add
        (completePreparedSegment_totalWeightedAllowance_le curve differential
          head headWithin owner sheet depth rootDiameter rootDiameterPositive
            preparedHead generated.1)
        (ofPreparedPath_totalWeightedAllowance_le_of_allRequestsDyadic curve
          differential sheet depth rootDiameter rootDiameterPositive
            preparedTail generated.2)

/-- Exact retained request provenance also supplies the owner-independent
rounded initial-sample bound. -/
theorem ofPreparedPath_integralNormSqSum_le_of_allRequestsDyadic
    {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner),
      CCL.Riemann.PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive prepared ->
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
            ((ofPreparedPath curve differential sheet prepared).parents.map
              fun parent => parent.model.integralSample) <=
          dyadicPathIntegralNormSqCeilBound differential rootDiameter depth path
  | _, _, _, _, _, .nil point owner, _generated => by
      simp only [ofPreparedPath, dyadicPathIntegralNormSqCeilBound,
        List.map_nil, RFAP.ConstructiveFiniteNorm.gaussianNormSqSum]
      exact le_rfl
  | _, _, _, _, _, .cons head tail owner headWithin preparedHead preparedTail,
      generated => by
      change preparedHead.subdivision.requests =
          CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint
              CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
                rootDiameterPositive ∧
        CCL.Riemann.PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive preparedTail at generated
      let tailState := ofPreparedPath curve differential sheet preparedTail
      simp only [ofPreparedPath, dataOfCompleteSegment_parents,
        dyadicPathIntegralNormSqCeilBound]
      change
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
            ((preparedHead.centeredEdges curve differential sheet ++
              tailState.parents).map
                fun parent => parent.model.integralSample) <=
          completeDyadicIntegralNormSqCeilBound differential head rootDiameter
              depth +
            dyadicPathIntegralNormSqCeilBound differential rootDiameter depth
              tail
      rw [List.map_append, gaussianNormSqSum_append]
      exact add_le_add
        ((completePreparedSegment_integralNormSqSum_le curve differential head
          headWithin owner sheet depth rootDiameter rootDiameterPositive
            preparedHead generated.1).trans
          (completeDyadicIntegralNormSqSumBound_le_ceilBound differential head
            rootDiameterPositive.le depth))
        (ofPreparedPath_integralNormSqSum_le_of_allRequestsDyadic curve
          differential sheet depth rootDiameter rootDiameterPositive
            preparedTail generated.2)

/-- Exact retained request provenance supplies the sharper cached-root
total-weight bound without reconstructing the checker term. -/
theorem ofPreparedPath_preparedTotalWeightedAllowance_le_of_allRequestsDyadic
    {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner),
      CCL.Riemann.PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive prepared ->
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((ofPreparedPath curve differential sheet prepared).parents.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
          preparedPathTotalWeightedBound differential depth prepared
  | _, _, _, _, _, .nil point owner, _generated => by
      simp only [ofPreparedPath, preparedPathTotalWeightedBound, List.map_nil,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_nil]
      exact le_rfl
  | _, _, _, _, _, .cons head tail owner headWithin preparedHead preparedTail,
      generated => by
      change preparedHead.subdivision.requests =
          CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint
              CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
                rootDiameterPositive ∧
        CCL.Riemann.PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive preparedTail at generated
      let tailState := ofPreparedPath curve differential sheet preparedTail
      simp only [ofPreparedPath, dataOfCompleteSegment_parents,
        preparedPathTotalWeightedBound]
      change
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((preparedHead.centeredEdges curve differential sheet ++
            tailState.parents).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
          completePreparedDyadicTotalWeightedBound differential head headWithin
              owner preparedHead depth +
            preparedPathTotalWeightedBound differential depth preparedTail
      rw [List.map_append, totalWeightedAllowance_append]
      exact add_le_add
        (completePreparedSegment_preparedTotalWeightedAllowance_le curve
          differential head headWithin owner sheet depth rootDiameter
            rootDiameterPositive preparedHead generated.1)
        (ofPreparedPath_preparedTotalWeightedAllowance_le_of_allRequestsDyadic
          curve differential sheet depth rootDiameter rootDiameterPositive
            preparedTail generated.2)

/-- Exact retained request provenance supplies the sharper cached-root
initial-sample bound without reconstructing the checker term. -/
theorem ofPreparedPath_preparedIntegralNormSqSum_le_of_allRequestsDyadic
    {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : CCL.Riemann.PreparedClearPathModels.PreparedPath path owner),
      CCL.Riemann.PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive prepared ->
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
            ((ofPreparedPath curve differential sheet prepared).parents.map
              fun parent => parent.model.integralSample) <=
          preparedPathIntegralNormSqSumBound differential depth prepared
  | _, _, _, _, _, .nil point owner, _generated => by
      simp only [ofPreparedPath, preparedPathIntegralNormSqSumBound,
        List.map_nil, RFAP.ConstructiveFiniteNorm.gaussianNormSqSum]
      exact le_rfl
  | _, _, _, _, _, .cons head tail owner headWithin preparedHead preparedTail,
      generated => by
      change preparedHead.subdivision.requests =
          CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests depth
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint
              CCL.Riemann.PreparedClearPathModels.oneEndpoint rootDiameter
                rootDiameterPositive ∧
        CCL.Riemann.PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive preparedTail at generated
      let tailState := ofPreparedPath curve differential sheet preparedTail
      simp only [ofPreparedPath, dataOfCompleteSegment_parents,
        preparedPathIntegralNormSqSumBound]
      change
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
            ((preparedHead.centeredEdges curve differential sheet ++
              tailState.parents).map
                fun parent => parent.model.integralSample) <=
          completePreparedDyadicIntegralNormSqSumBound differential head
              headWithin owner preparedHead depth +
            preparedPathIntegralNormSqSumBound differential depth preparedTail
      rw [List.map_append, gaussianNormSqSum_append]
      exact add_le_add
        (completePreparedSegment_preparedIntegralNormSqSum_le curve
          differential head headWithin owner sheet depth rootDiameter
            rootDiameterPositive preparedHead generated.1)
        (ofPreparedPath_preparedIntegralNormSqSum_le_of_allRequestsDyadic curve
          differential sheet depth rootDiameter rootDiameterPositive
            preparedTail generated.2)

@[simp] theorem ofExecutedCheckedDyadic_parents_length {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic
          depth rootDiameter rootDiameterPositive path owner),
      (ofExecutedCheckedDyadic curve differential sheet checked).parents.length =
        checked.prepared.stepCount
  | _, _, _, _, _, .nil point owner => by
      simp only [ofExecutedCheckedDyadic,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.stepCount]
      rfl
  | _, _, _, _, _, .cons head tail owner headWithin headSafe remaining => by
      simp only [ofExecutedCheckedDyadic, List.length_append,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.stepCount]
      rw [completeSegment_centeredEdges_length curve differential sheet _,
        ofExecutedCheckedDyadic_parents_length curve differential sheet
          remaining]

theorem ofCheckedDyadic_recast_self {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic depth
          rootDiameter rootDiameterPositive path owner),
      (ofCheckedDyadic curve differential sheet checked).parents.map
          (recastCenteredEdge differential) =
        (ofCheckedDyadic curve differential sheet checked).parents := by
  intro ambient start finish path owner checked
  unfold ofCheckedDyadic
  exact ofPreparedPath_recast_self curve differential sheet checked.prepared

theorem ofExecutedCheckedDyadic_recast_self {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
      {path : ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic
          depth rootDiameter rootDiameterPositive path owner),
      (ofExecutedCheckedDyadic curve differential sheet checked).parents.map
          (recastCenteredEdge differential) =
        (ofExecutedCheckedDyadic curve differential sheet checked).parents
  | _, _, _, _, _, .nil point owner => by
      simp only [ofExecutedCheckedDyadic, List.map_nil]
  | _, _, _, _, _, .cons head tail owner headWithin headSafe remaining => by
      simp only [ofExecutedCheckedDyadic, List.map_append]
      rw [completeSegment_centeredEdges_recast_self curve differential sheet _,
        ofExecutedCheckedDyadic_recast_self curve differential sheet remaining]

/-- Extract the canonical centered state from either a conservative safe bank
or an explicitly executed bank. -/
def ofDyadicBank {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    CheckedDyadicCenteredState curve differential sheet start finish := by
  cases bank with
  | safe checked => exact ofCheckedDyadic curve differential sheet checked
  | executed within prepared success =>
      exact ofTryDyadic curve differential sheet depth rootDiameter
        rootDiameterPositive path within owner success
  | executedCertified checked =>
      exact ofExecutedCheckedDyadic curve differential sheet checked
  | certified certificate =>
      let data := ofPreparedPath curve differential sheet certificate.prepared
      exact
        { parents := data.parents
          proper := ofPreparedPath_allParentsProper_of_allEdgesProper curve
            differential sheet certificate.prepared
              certificate.prepared_allEdgesProper
          chain := data.chain }

/-- The centre-free lower endpoint retained by every bank presentation is
exactly the fold over the canonical parents used by direct refinements. -/
theorem ofDyadicBank_integralRealLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    bank.integralRealLower curve differential sheet =
      CCL.Riemann.PreparedSubdivisionModels.centeredEdgesIntegralRealLower
        (ofDyadicBank curve differential sheet bank).parents := by
  cases bank with
  | safe checked =>
      exact ofPreparedPath_integralRealLower curve differential sheet
        checked.prepared
  | executed within prepared success =>
      exact ofPreparedPath_integralRealLower curve differential sheet prepared
  | executedCertified checked =>
      change checked.prepared.integralRealLower curve differential sheet =
        CCL.Riemann.PreparedSubdivisionModels.centeredEdgesIntegralRealLower
          (ofExecutedCheckedDyadic curve differential sheet checked).parents
      rw [ofExecutedCheckedDyadic_parents_eq_ofPreparedPath curve differential
        sheet checked]
      exact ofPreparedPath_integralRealLower curve differential sheet
        checked.prepared
  | certified certificate =>
      exact ofPreparedPath_integralRealLower curve differential sheet
        certificate.prepared

/-- Every bank presentation retains the same arbitrary rational projection
endpoint on its canonical direct-refinement parents. -/
theorem ofDyadicBank_directionalIntegralLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) (direction : Gaussian)
    {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    bank.prepared.directionalIntegralLower curve differential sheet direction =
      CCL.Riemann.PreparedSubdivisionModels.centeredEdgesDirectionalIntegralLower
        direction (ofDyadicBank curve differential sheet bank).parents := by
  cases bank with
  | safe checked =>
      exact ofPreparedPath_directionalIntegralLower curve differential sheet
        direction checked.prepared
  | executed within prepared success =>
      exact ofPreparedPath_directionalIntegralLower curve differential sheet
        direction prepared
  | executedCertified checked =>
      change checked.prepared.directionalIntegralLower curve differential sheet
          direction =
        CCL.Riemann.PreparedSubdivisionModels.centeredEdgesDirectionalIntegralLower
          direction
            (ofExecutedCheckedDyadic curve differential sheet checked).parents
      rw [ofExecutedCheckedDyadic_parents_eq_ofPreparedPath curve differential
        sheet checked]
      exact ofPreparedPath_directionalIntegralLower curve differential sheet
        direction checked.prepared
  | certified certificate =>
      exact ofPreparedPath_directionalIntegralLower curve differential sheet
        direction certificate.prepared

/-- Either bank representation is bounded by the same compact expression on
its original path. -/
theorem ofDyadicBank_totalWeightedAllowance_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((ofDyadicBank curve differential sheet bank).parents.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
      dyadicPathTotalWeightedBound differential rootDiameter depth path := by
  cases bank with
  | safe checked =>
      exact ofCheckedDyadic_totalWeightedAllowance_le curve differential sheet
        checked
  | executed within prepared success =>
      exact ofTryDyadic_totalWeightedAllowance_le curve differential sheet
        depth rootDiameter rootDiameterPositive path within owner success
  | executedCertified checked =>
      exact ofExecutedCheckedDyadic_totalWeightedAllowance_le curve
        differential sheet checked
  | certified certificate =>
      simp only [ofDyadicBank]
      exact
        ofPreparedPath_totalWeightedAllowance_le_of_allRequestsDyadic curve
          differential sheet depth rootDiameter rootDiameterPositive
            certificate.prepared certificate.generated

/-- Every bank representation inherits the owner-independent rounded sample
bound of its original clear path. -/
theorem ofDyadicBank_integralNormSqSum_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
        ((ofDyadicBank curve differential sheet bank).parents.map
          fun parent => parent.model.integralSample) <=
      dyadicPathIntegralNormSqCeilBound differential rootDiameter depth path := by
  cases bank with
  | safe checked =>
      exact ofCheckedDyadic_integralNormSqSum_le curve differential sheet
        checked
  | executed within prepared success =>
      exact ofTryDyadic_integralNormSqSum_le curve differential sheet depth
        rootDiameter rootDiameterPositive path within owner success
  | executedCertified checked =>
      exact ofExecutedCheckedDyadic_integralNormSqSum_le curve differential
        sheet checked
  | certified certificate =>
      simp only [ofDyadicBank]
      exact
        ofPreparedPath_integralNormSqSum_le_of_allRequestsDyadic curve
          differential sheet depth rootDiameter rootDiameterPositive
            certificate.prepared certificate.generated

/-- Actual-root compact total-weight bound carried by any prepared-bank
representation.  Evaluation follows only the retained prepared path and its
cached root-box maxima. -/
def dyadicBankPreparedTotalWeightedBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) : Coordinate :=
  match bank with
  | .safe checked =>
      preparedPathTotalWeightedBound differential depth checked.prepared
  | .executed _within prepared _success =>
      preparedPathTotalWeightedBound differential depth prepared
  | .executedCertified checked =>
      preparedPathTotalWeightedBound differential depth checked.prepared
  | .certified certificate =>
      preparedPathTotalWeightedBound differential depth certificate.prepared

def dyadicBankPreparedTotalWeightedDyadicBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) : Coordinate :=
  match bank with
  | .safe checked =>
      preparedPathTotalWeightedDyadicBound differential depth checked.prepared
  | .executed _within prepared _success =>
      preparedPathTotalWeightedDyadicBound differential depth prepared
  | .executedCertified checked =>
      preparedPathTotalWeightedDyadicBound differential depth checked.prepared
  | .certified certificate =>
      preparedPathTotalWeightedDyadicBound differential depth
        certificate.prepared

theorem dyadicBankPreparedTotalWeightedBound_le_dyadicBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    dyadicBankPreparedTotalWeightedBound differential bank <=
      dyadicBankPreparedTotalWeightedDyadicBound differential bank := by
  cases bank <;>
    exact preparedPathTotalWeightedBound_le_dyadicBound differential depth _

/-- Actual-root compact squared-sample bound carried by any prepared-bank
representation. -/
def dyadicBankPreparedIntegralNormSqSumBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) : Coordinate :=
  match bank with
  | .safe checked =>
      preparedPathIntegralNormSqSumBound differential depth checked.prepared
  | .executed _within prepared _success =>
      preparedPathIntegralNormSqSumBound differential depth prepared
  | .executedCertified checked =>
      preparedPathIntegralNormSqSumBound differential depth checked.prepared
  | .certified certificate =>
      preparedPathIntegralNormSqSumBound differential depth
        certificate.prepared

/-- Segmentwise-rounded bank bound used by executable preflight. -/
def dyadicBankPreparedIntegralNormSqCeilBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) : Coordinate :=
  match bank with
  | .safe checked =>
      preparedPathIntegralNormSqCeilBound differential depth checked.prepared
  | .executed _within prepared _success =>
      preparedPathIntegralNormSqCeilBound differential depth prepared
  | .executedCertified checked =>
      preparedPathIntegralNormSqCeilBound differential depth checked.prepared
  | .certified certificate =>
      preparedPathIntegralNormSqCeilBound differential depth
        certificate.prepared

theorem dyadicBankPreparedIntegralNormSqSumBound_le_ceilBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    dyadicBankPreparedIntegralNormSqSumBound differential bank <=
      dyadicBankPreparedIntegralNormSqCeilBound differential bank := by
  cases bank <;>
    exact preparedPathIntegralNormSqSumBound_le_ceilBound differential depth _

/-- Paired bank summary which preserves the shared prepared-path traversal. -/
def dyadicBankPreparedPreflightBounds {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    PreparedPathPreflightBounds :=
  match bank with
  | .safe checked =>
      preparedPathPreflightBounds differential depth checked.prepared
  | .executed _within prepared _success =>
      preparedPathPreflightBounds differential depth prepared
  | .executedCertified checked =>
      preparedPathPreflightBounds differential depth checked.prepared
  | .certified certificate =>
      preparedPathPreflightBounds differential depth certificate.prepared

@[simp] theorem dyadicBankPreparedPreflightBounds_totalWeighted {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    (dyadicBankPreparedPreflightBounds differential bank).totalWeighted =
      dyadicBankPreparedTotalWeightedDyadicBound differential bank := by
  cases bank <;>
    simp only [dyadicBankPreparedPreflightBounds,
      dyadicBankPreparedTotalWeightedDyadicBound,
      preparedPathPreflightBounds_totalWeighted]

theorem dyadicBankPreparedTotalWeightedBound_le_preflight {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    dyadicBankPreparedTotalWeightedBound differential bank <=
      (dyadicBankPreparedPreflightBounds differential bank).totalWeighted := by
  rw [dyadicBankPreparedPreflightBounds_totalWeighted]
  exact dyadicBankPreparedTotalWeightedBound_le_dyadicBound differential bank

@[simp] theorem dyadicBankPreparedPreflightBounds_integralNormSqSum
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    (dyadicBankPreparedPreflightBounds differential bank).integralNormSqSum =
      dyadicBankPreparedIntegralNormSqCeilBound differential bank := by
  cases bank <;>
    simp only [dyadicBankPreparedPreflightBounds,
      dyadicBankPreparedIntegralNormSqCeilBound,
      preparedPathPreflightBounds_integralNormSqSum]

theorem dyadicBankPreparedIntegralNormSqSumBound_le_preflight
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    dyadicBankPreparedIntegralNormSqSumBound differential bank <=
      (dyadicBankPreparedPreflightBounds differential bank).integralNormSqSum := by
  rw [dyadicBankPreparedPreflightBounds_integralNormSqSum]
  exact dyadicBankPreparedIntegralNormSqSumBound_le_ceilBound differential bank

/-- Every bank's actual centred cells satisfy its cached-root compact bound. -/
theorem ofDyadicBank_preparedTotalWeightedAllowance_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((ofDyadicBank curve differential sheet bank).parents.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
      dyadicBankPreparedTotalWeightedBound differential bank := by
  cases bank with
  | safe checked =>
      exact ofCheckedDyadic_preparedTotalWeightedAllowance_le curve
        differential sheet checked
  | executed within prepared success =>
      exact ofTryDyadic_preparedTotalWeightedAllowance_le curve differential
        sheet depth rootDiameter rootDiameterPositive path within owner success
  | executedCertified checked =>
      exact ofExecutedCheckedDyadic_preparedTotalWeightedAllowance_le curve
        differential sheet checked
  | certified certificate =>
      simp only [ofDyadicBank, dyadicBankPreparedTotalWeightedBound]
      exact
        ofPreparedPath_preparedTotalWeightedAllowance_le_of_allRequestsDyadic
          curve differential sheet depth rootDiameter rootDiameterPositive
            certificate.prepared certificate.generated

/-- Every bank's actual initial cell samples satisfy its compact additive
squared-norm bound. -/
theorem ofDyadicBank_preparedIntegralNormSqSum_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
        ((ofDyadicBank curve differential sheet bank).parents.map
          fun parent => parent.model.integralSample) <=
      dyadicBankPreparedIntegralNormSqSumBound differential bank := by
  cases bank with
  | safe checked =>
      exact ofCheckedDyadic_preparedIntegralNormSqSum_le curve differential
        sheet checked
  | executed within prepared success =>
      exact ofTryDyadic_preparedIntegralNormSqSum_le curve differential sheet
        depth rootDiameter rootDiameterPositive path within owner success
  | executedCertified checked =>
      exact ofExecutedCheckedDyadic_preparedIntegralNormSqSum_le curve
        differential sheet checked
  | certified certificate =>
      simp only [ofDyadicBank, dyadicBankPreparedIntegralNormSqSumBound]
      exact
        ofPreparedPath_preparedIntegralNormSqSum_le_of_allRequestsDyadic curve
          differential sheet depth rootDiameter rootDiameterPositive
            certificate.prepared certificate.generated

/-- The centred parent list of every bank has the checker-certified common
dyadic edge count. -/
@[simp] theorem ofDyadicBank_parents_length {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    (ofDyadicBank curve differential sheet bank).parents.length =
      2 ^ depth * path.segmentCount := by
  cases bank with
  | safe checked =>
      simp only [ofDyadicBank]
      rw [ofCheckedDyadic_parents_length,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared_stepCount]
  | executed within prepared success =>
      change (ofPreparedPath curve differential sheet prepared).parents.length =
        2 ^ depth * path.segmentCount
      rw [ofPreparedPath_parents_length,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.tryDyadic_stepCount
          path within owner depth rootDiameter rootDiameterPositive success]
  | executedCertified checked =>
      simp only [ofDyadicBank]
      rw [ofExecutedCheckedDyadic_parents_length,
        CCL.Riemann.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared_stepCount]
  | certified certificate =>
      change
        (ofPreparedPath curve differential sheet
          certificate.prepared).parents.length = _
      rw [ofPreparedPath_parents_length, certificate.prepared_stepCount]

/-- Compact aggregate allowance bound for a complete common-depth bank. -/
def dyadicPathAggregateBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    (rootDiameter : Coordinate) (depth : Nat)
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    (path : ClearPath curve.polynomial ambient start finish) : Coordinate :=
  ((2 ^ depth * path.segmentCount : Nat) : Coordinate) *
    dyadicPathTotalWeightedBound differential rootDiameter depth path

/-- Aggregate allowance of a bank's actual centred cells is bounded by an
expression which traverses only its original clear path. -/
theorem ofDyadicBank_aggregateAllowance_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((ofDyadicBank curve differential sheet bank).parents.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
      dyadicPathAggregateBound differential rootDiameter depth path := by
  unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
    dyadicPathAggregateBound
  rw [List.length_map, ofDyadicBank_parents_length]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    (ofDyadicBank_totalWeightedAllowance_le curve differential sheet bank)
    (acceptedCoordinateNatCast_nonnegative _)

/-- Recasting a bank to the same differential preserves its canonical centred
parent list exactly. -/
theorem ofDyadicBank_recast_self {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    (ofDyadicBank curve differential sheet bank).parents.map
        (recastCenteredEdge differential) =
      (ofDyadicBank curve differential sheet bank).parents := by
  cases bank with
  | safe checked =>
      simp only [ofDyadicBank]
      exact ofCheckedDyadic_recast_self curve differential sheet checked
  | executed within prepared success =>
      change (ofPreparedPath curve differential sheet prepared).parents.map
          (recastCenteredEdge differential) =
        (ofPreparedPath curve differential sheet prepared).parents
      exact ofPreparedPath_recast_self curve differential sheet prepared
  | executedCertified checked =>
      simp only [ofDyadicBank]
      exact ofExecutedCheckedDyadic_recast_self curve differential sheet
        checked
  | certified certificate =>
      change
        (ofPreparedPath curve differential sheet certificate.prepared).parents.map
            (recastCenteredEdge differential) =
          (ofPreparedPath curve differential sheet certificate.prepared).parents
      exact ofPreparedPath_recast_self curve differential sheet
        certificate.prepared

/-- Initial executable open state extracted from one checked prepared bank. -/
def stateOfCheckedDyadic {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : RFAP.Boxes.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (checked :
      CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic depth
        rootDiameter rootDiameterPositive path owner) :
    DirectRefinementState curve differential :=
  let state := ofCheckedDyadic curve differential sheet checked
  state.chain.toDirectRefinementState state.proper

end CenteredPathChain

namespace DirectBlockRefinement

/-- Replace every canonical parent cell by its certified direct dyadic path,
preserving the endpoints of the complete finite chain. -/
def refinedPath {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2}
      (_blocks : DirectBlockRefinement parents)
      (_chain : CenteredPathChain parents (start := start) (finish := finish)),
      LiftedPath 2 start finish
  | [], _, _, .nil, .nil point => .nil point
  | _ :: _, _, _, .cons block tailBlocks, .cons _ tailChain =>
      block.lifted.append (refinedPath tailBlocks tailChain)

/-- Cell-for-cell algebraic certification of the refined complete path. -/
def refinedCertificates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2}
      (blocks : DirectBlockRefinement parents)
      (chain : CenteredPathChain parents (start := start) (finish := finish)),
      UniformPathCertificates curve differential
        (blocks.children.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
        (blocks.refinedPath chain)
  | [], _, _, .nil, .nil point => .nil point
  | _ :: _, _, _, .cons block tailBlocks, .cons _ tailChain => by
      simpa only [children, List.map_append, refinedPath] using
        UniformPathCertificates.append block.lifted block.certificates
          (refinedCertificates tailBlocks tailChain)

end DirectBlockRefinement

/-- Total certified block decomposition of every nonstationary parent in one
finite centered path. -/
def directBlockRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (parents : List (CenteredEdge curve differential)) ->
    CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents ->
      DirectBlockRefinement parents
  | [], _proper => .nil
  | parent :: remaining, proper =>
      .cons
        (directParentBlock parent proper.1 rootDiameter rootDiameterPositive)
        (directBlockRefinement rootDiameter rootDiameterPositive remaining
          proper.2)

/-- Total direct refinement result for a finite centered parent path. -/
structure DirectRefinementResult {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parents : List (CenteredEdge curve differential)) where
  children : List (CenteredEdge curve differential)
  refinement : CCL.Riemann.PreparedSubdivisionModels.CenteredEdgeRefinement
    parents children

namespace DirectRefinementResult

def toCompatible {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parents : List (CenteredEdge curve differential)}
    (result : DirectRefinementResult parents) :
    CompatibleConstantPathRefinement
      (parents.map CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      (result.children.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model) :=
  result.refinement.toCompatible

end DirectRefinementResult

/-- Refine every nonstationary parent in a finite centered path, with no
congruence-search or acceptance input. -/
def directRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (parents : List (CenteredEdge curve differential)) ->
    CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents ->
      DirectRefinementResult parents
  | parents, proper =>
      let blocks := directBlockRefinement rootDiameter rootDiameterPositive
        parents proper
      { children := blocks.children
        refinement := blocks.toCenteredEdgeRefinement }

end CCL.Riemann.PreparedDirectDyadicRefinements
